/*
 * Copyright (c) David Benedeki.  All rights reserved.  http://www.github.com/benedeki
 * The software in this package is published under the terms of the MIT License,
 *  a copy of which has been included with this distribution in the LICENSE.md file.
 */
package scala.Aho_Corasick

import scala.Aho_Corasick.Search.{FallbackQueue, QueueItem, SearchHit, TrieNode}
import scala.collection.immutable.Queue


/** Implementation of the Aho Corasick text search algorithm (searching for multiple strings at once within text)
  *
  * @param searchStrings the strings to search for; the search structure is build based on these and cannot be changed later
  * @param ignoreCase flag whether searches will be or not case sensitive
  */
class Search(searchStrings: Set[String], ignoreCase: Boolean = false) {
  private val start = new TrieNode()  //TODO

  private val charTransponder: Char => Char = if (ignoreCase) {
    _.toLower
  } else {
    _
  }

  private def addWord(word: String): Int = {
    val wordLength: Int = word.length
    if (wordLength > 0) {
      word.toIterator.foldLeft((start, wordLength)) { (acc, current) => (acc , current) match {
       case((node, 1), char) => //reached last letter
         (node.forceChild(char, word), -1)
       case ((node, charsLeft), char) =>
         (node.forceChild(char), charsLeft - 1)
      }}
    } // else not adding empty string
    wordLength
  }

  //build Trie while finding the longest word length
  private val maxWordLength: Int = searchStrings.foldLeft(0) ((currentMax, word) => currentMax.max(addWord(word)))

  addFallbacks()

  private def addFallbacks(): Unit = {
    var nodes: FallbackQueue = FallbackQueue(start.children.map{case (k, v) => QueueItem(v, k, start)}.toSeq)
    while (nodes.nonEmpty) {
      val (node, nodesRest) = nodes.dequeue
      nodes = processFallback(node, nodesRest)
    }
  }

  private def processFallback(item: QueueItem, nodes: FallbackQueue):FallbackQueue = {
    val fallback: TrieNode = item.parentFallback.getChildOrElse(item.letter, start) match {
      case item.node => start
      case x: TrieNode => x
    }
    //enqueue item.node children
    val result: FallbackQueue = nodes ++ fallback.children.map {case (k, v) => QueueItem(v, k, fallback)}
    item.node.adoptChildren(fallback)
    result
  }

  /** Searches the provided text using the search strings defined on creation of the object
    * By the nature of the search if overlaps are off, the earlier starting longest substring is reported,
    * In that case (overalaps = false) the result hit are byt the nature of the algorithm guaranteed to be returned
    * by the order how they appear in in searched text.
    * E.g. in case of search for strings (hit, hitman, man, sun) in "hitmansunxxxxhit"
    * the result will be (hitman, sun, hit)
    * In case overlaps = true the result would be (hit, hitman, man, sun, hit) order not guaranteed
    *
    * @param text text to search through
    * @param overlaps flag indicating if overlapped search hits to be reported
    * @return a list of found hits (what was found, start and end index of the find)
    */
  def search(text: String, overlaps: Boolean = true): Seq[SearchHit] = {
    searchWithCost(text, overlaps)._1
  }

  /** Searches the provided text using the search strings defined on creation of the object
    * Regarding overlaps, same applies as for the above simple "search" version of the function above
    * The "costs" map must use for keys the same strings as the strings used fro creation of this object
    *  including case, even in case of case-insensitive search.
    *  Missing keys in the costs map are OK (default to cost 0), so as extra pairs (those are ignored)
    *
    * @param text text to search through
    * @param overlaps flag indicating if overlapped search hits to be reported
    * @param costs map of costs each found substring would mean (if missing, defaults to 0), where substrings used at
    *              creation of the o
    *              NB! the searched substring
    * @return a list of found hits (what was found, start and end index of the find) and the sum of the costs of these
    *         finds based on the costs map
    */
  def searchWithCost(text: String, overlaps: Boolean = true, costs: Map[String, Int] = Map.empty): (Seq[SearchHit], Int) = {
    if (overlaps) {
      val (result, cost, _, _): (List[SearchHit], Int, Int, TrieNode) = text.toIterable.foldLeft(List.empty[SearchHit], 0, 0, start) {
        case ((accResult: List[SearchHit], costAcc, index, state), char) =>
          val newState = state.getChildOrElse(charTransponder(char), start)
          val hitsCollection: (List[SearchHit], Int) = newState.fullWords.foldLeft(accResult, costAcc) {
            case ((accResultInner: List[SearchHit], costAccInner), word) => (SearchHit(word, index - word.length, index) :: accResultInner , costAccInner + costs.getOrElse(word, 0))
          }
          (hitsCollection._1, hitsCollection._2, index + 1, newState)
      }
      (result, cost)
    } else {
      val buffer: Buffer[SearchHit] = new Buffer[SearchHit](maxWordLength)
      val (resultPreBuff, costPreBuff, _, _): (List[SearchHit], Int, Int, TrieNode) = text.toIterable.foldLeft(List.empty[SearchHit], 0, 0, start) {
        case ((accResult, accCost, index, state), char) =>
          val newState = state.getChildOrElse(charTransponder(char), start)
          newState.fullWords.foreach(word => buffer.put(SearchHit(word, index - word.length, index)))
          buffer.pop match {
            case Some(hit) => (hit :: accResult, accCost + costs.getOrElse(hit.word, 0) , index + 1, newState)
            case None => (accResult, accCost, index + 1, newState)
          }
      }
      //add what's remaining in the buffer
      buffer.flush.foldLeft((resultPreBuff, costPreBuff)) {(acc, hit) => (hit::acc._1, acc._2 + costs.getOrElse(hit.word, 0))}
    }
  }
}

object Search {
  private case class QueueItem(node: TrieNode, letter: Char, parentFallback: TrieNode)
  private type FallbackQueue = Queue[QueueItem]
  private def FallbackQueue(seq: Seq[QueueItem]): FallbackQueue = {
    Queue(seq: _*)
  }

  private class TrieNode(private var fFullWords: List[String]) {
    def this() = this(List.empty)

    private var fChildren: Map[Char, TrieNode] = Map.empty

    def fullWords: List[String] = {
      fFullWords
    }

    def children: Map[Char, TrieNode] = {
      fChildren
    }

    def assignWords(newWords: List[String]): List[String] = {
      fFullWords = newWords:::fFullWords
      fFullWords
    }

    def forceChild(char: Char): TrieNode = {
      getChild(char) match {
        case Some(ownChild) => ownChild
        case None =>
          val newChild = new TrieNode()
          fChildren += (char->newChild)
          newChild
      }
    }

    def forceChild(char: Char, fullWord: String): TrieNode= {
      getChild(char) match {
        case Some(ownChild) =>
          if (!ownChild.hasWord) {
            ownChild.fFullWords = List(fullWord)
          }
          ownChild
        case None =>
          val newChild = new TrieNode(List(fullWord))
          fChildren += (char->newChild)
          newChild
      }
    }

    def adoptChildren(fromNode: TrieNode): Unit = {
      fromNode.fChildren.foreach {
        case (k, v) => getChild(k) match {
          case Some(ownChild) => ownChild.fFullWords = v.fFullWords ++ ownChild.fFullWords //no need to check oneness if words coming from different part of tree
          case None => fChildren += (k->v)
        }
      }
    }

    def getChildOrElse(letter: Char, default: TrieNode): TrieNode = {
      fChildren.getOrElse(letter, default)
    }

    def getChild(letter: Char): Option[TrieNode] = {
      fChildren.get(letter)
    }

    def hasWord: Boolean = {
      fFullWords.nonEmpty
    }
  }

  /** Represents the successful find of a substring in the text
    *
    * @param word the word (substring) found
    * @param start the index of ths start of the word in the searched text
    * @param end the index of the last letter of the word within the searched text
    */
  case class SearchHit(word: String, start: Int, end: Int) extends BufferItem {
    override def length: Int = {
      end - start + 1
    }
  }
}


/** Serves to effectively search and replace a set of substrings in text
  *
  * In case of substring overlaps in the searched text the earlier and longer ones takes precedence.
  *
  * @param replacementPairs the substrings to search for (keys) and the corresponding texts they are to be replaced with
  * @param ignoreCase flag whether searches will be or not case sensitive
  */
class Replace(replacementPairs: Map[String, String], ignoreCase: Boolean = false) {
  private val searchEngine = new Search(replacementPairs.keys.toSet, ignoreCase)

  private val costs: Map[String, Int] = replacementPairs.map {case (k ,v) => (k, v.length - k.length)}

  /** In the provided text finds all the substrings specified in the creation of the class and replaces them with
    * their respective replacements
    *
    * @param text text to search through and make replacements on
    * @param emptyToNoHit flag if in case of no hits the result should be empty
    * @return the newly created string with all found substring replaced by their respective replacements
    *         None in case of emptyToNoHit flag set and no substrings to replace found
    */
  def replaceStructured(text: String, emptyToNoHit: Boolean = true): Option[Replace.ReplacementResult] = {
    val (found, cost) = searchEngine.searchWithCost(text, overlaps = false, costs = costs)

    if (found.nonEmpty || (!emptyToNoHit)) {
      val result = Replace.ReplacementResult(text)
      val resultText = new StringBuilder(text.length + cost, "")
      found.foldLeft(0) { case (afterLastHit, hit) if afterLastHit <= hit.start =>
          resultText.append(text.substring(afterLastHit, hit.start))
          resultText.append(replacementPairs(hit.word))
          hit.end + 1
      }
      result.setResult(resultText.toString)
      Some(result)
    } else if (emptyToNoHit) {
      None
    } else {
      Some(Replace.ReplacementResult(text))
    }
  }

  /**
    *
    * @param text text to search through and make replacements on
    * @param emptyToNoHit flag if in case of no hits the result should be empty
    * @return structure with extended info regarding the replacements done
    *         None in case of emptyToNoHit flag set and no substrings to replace found
    */
  def replace(text: String, emptyToNoHit: Boolean = true): Option[String] = {
    replaceStructured(text, emptyToNoHit).map(_.result)
  }
}

object Replace {

  /**  Class representing the result of replacement executed on a text
    * Includes information on total number of replacements and which substrings were found and how many times replaced
    *
    * @param original the original text the replacement was executed upon
    */
  class ReplacementResult(original: String) {
    private var fTotalReplacementCount: Int = 0
    private var fReplacements: Map[String, Int] = Map.empty
    private var fResult: String = original

    def totalReplacementCount: Int = fTotalReplacementCount
    def replacements: Map[String, Int] = fReplacements
    def result: String = fResult

    private [Replace] def addHit(key: String): Unit = {
      fReplacements ++= Map(key -> (fReplacements.getOrElse(key, 0) + 1))
    }

    private [Replace] def setResult(text: String): Unit = {
      fResult = text
    }
  }

  object ReplacementResult {
    def apply(original: String): ReplacementResult = new ReplacementResult(original)
  }
}