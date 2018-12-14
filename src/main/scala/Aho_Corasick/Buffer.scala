/*
 * Copyright (c) David Benedeki.  All rights reserved.  http://www.github.com/benedeki
 * The software in this package is published under the terms of the MIT License,
 *  a copy of which has been included with this distribution in the LICENSE.md file.
 */
package scala.Aho_Corasick


class BufferException(msg: String = "") extends Exception(msg)


object BufferException {
  case class NegativeItemLength() extends BufferException("Item length cannot be negative")
  case class IndexOutOfBoundsException(index: Int) extends BufferException(s"Index $index is out of bounds")
  case class ItemTooBigException(itemSize: Int, bufferSize: Int) extends BufferException(s"Item if size $bufferSize is too big for Buffer($bufferSize)")
}


/** Base trait that all items in the buffer have implement
  */
trait BufferItem {
  /** The "size" of the item in the buffer.
    * The number of positions in the buffer that the item occupies,
    * therefore any item on these positions is considered as not being there (can be bigger the the buffer size)
    * If it's 0 or 1 no effective "shadowing" of the buffer happens
    *
    * @return the "size" of the item
    */
  def length: Int = 0
}


object Buffer {
  object OverwriteStrategy extends Enumeration {
    type OverwriteStrategy = Value
    val biggerWins, smallerWins, newWins, oldWins = Value
  }

}

import Aho_Corasick.Buffer.OverwriteStrategy._


/** A constant size buffer that allows insertions into any position of the buffer
  * Output from the buffer is executed via the pop method, which also removes the item from the buffer
  * The idea is that it's a stream of objects that allows skipping the line within the size of the buffer.
  * At the same time, an object inserted "shadows" the positions behind it according to its size,
  * so no output is given from them
  *
  * @param bufferSize the number of position in the buffer, also any item inserted length cannot exceed this value
  * @param defaultOverwriteStrategy the strategy to use when on insertion there's a collision with an earlier inserted item
  * @tparam A class of the items in the buffer
  */
class Buffer[A <: BufferItem](bufferSize: Int, defaultOverwriteStrategy: OverwriteStrategy = biggerWins) { //TODO make iterable
  private val buffer: Array[Option[A]] = Array.fill[Option[A]](bufferSize)(None)
  private var head: Int = 0
  private var invalidTill: Int = 0

  private def trimIndex(index: Int): Int = {
    if (index >= bufferSize) {
      index - bufferSize
    } else {
      index
    }
  }

  private def toRelIndex(index: Int): Int = {
    if ((index >= bufferSize) || (index < 0)) {
      throw BufferException.IndexOutOfBoundsException(index)
    }
    trimIndex(index + head)
  }

  private val putFunctions: Map[OverwriteStrategy, (A, Int) => A] = Map (
    biggerWins -> putBiggerWins,
    smallerWins -> putSmallerWins,
    newWins -> putNewWins,
    oldWins -> putOldWins
  )

  private def putBiggerWins(item: A, index: Int): A = {
    if (buffer(index).map(_.length).getOrElse(Int.MinValue) < item.length) {
      buffer(index) = Some(item)
    }
    buffer(index)()
  }

  private def putSmallerWins(item: A, index: Int): A = {
    if (buffer(index).map(_.length).getOrElse(Int.MaxValue) > item.length) {
      buffer(index) = Some(item)
    }
    buffer(index)()
  }

  private def putNewWins(item: A, index: Int): A = {
    buffer(index) = Some(item)
    item
  }

  private def putOldWins(item: A, index: Int): A = {
    if (buffer(index).isEmpty) {
      buffer(index) = Some(item)
      item
    } else {
      buffer(index)()
    }
  }

  /** Inserts an item into the buffer.
    * The position within the buffer is decided based on the size of the item. The position is computed so that the item
    * "shadows" the rest of the buffer till it's end
    * E.g. an item of size 2 is inserted to position 3 (zero based) in a buffer of size 5
    *
    *
    * @param item the item to be inserted into the buffer
    * @param overwriteStrategy the behavior in case the position in the buffer already contains an item
    * @return the item at the destination position - either the newly inserted item or the one that was there before.
    */
  def put(item: A, overwriteStrategy: Option[OverwriteStrategy] = None): A = {
    put(item, bufferSize - item.length, overwriteStrategy)
  }

  /** Inserts an item into the buffer to a particular position
    *
    * @param item the item to be inserted into the buffer
    * @param index the position in the buffer - it has to be between 0 and bufferSize - 1
    * @param overwriteStrategy the behavior in case the position in the buffer already contains an item
    * @return the item at the destination position - either the newly inserted item or the one that was there before.
    */
  def put(item: A, index: Int, overwriteStrategy: Option[OverwriteStrategy] = None): A = {
    val relIndex = relIndex(index)
    val length = item.length
    if (length > bufferSize) {
      throw BufferException.ItemTooBigException(length, bufferSize)
    } else if (length < 0) {
      throw  BufferException.NegativeItemLength()
    }
    putFunctions(overwriteStrategy.getOrElse(defaultOverwriteStrategy))(item, relIndex)
  }

  /** pops the buffer and inserts the new item at the end of the buffer
    *
    * @param item the item to be inserted into the buffer
    * @param overwriteStrategy  the behavior in case the position in the buffer already contains an item
    * @return the item, if any, at the head of the buffer
    */
  def push(item: A, overwriteStrategy: Option[OverwriteStrategy] = None): Option[A] = {
    val result: Option[A] = pop
    put(item, bufferSize-1, overwriteStrategy)
    result
  }

  /** Shifts the buffer by 1 position, returning the item that was at the head of the buffer
    *
    * @return the item that was at the head of the buffer
    */
  def pop: Option[A] = {
    val result: Option[A] = buffer(head) match {
      case Some(x) if invalidTill == 0 =>
        invalidTill = x.length
        buffer(head) = None
        Some(x)
      case None =>
        if (invalidTill > 0) {
          invalidTill -= 1
        }
        None
      case _ =>
        invalidTill -= 1
        buffer(head) = None
        None
    }
    head = trimIndex(head + 1) //TODO wrong
    result
  }

  /** Returns a sequence of all items that are currently in the buffer. It is equivalent to flat mapping the call
    * of pop bufferSize times.
    * With the call, the whole buffer is emptied
    *
    * @return sequence of items in the buffer.
    */
  def flush: Seq[A] = {
    for {
      _ <- 0 until bufferSize
      item <- pop
    } yield item
  }

  /** Removes the buffer item from the specified position (if present)
    *
    * @param index the position in the buffer to clear
    * @return the item, if present, from the cleared position
    */
  def clear(index: Int): Option[A] = {
    val relIndex = toRelIndex(index)
    val result = if (invalidTill > index) {
      None
    } else {
      buffer(relIndex)
    }
    if (buffer(relIndex).nonEmpty) {
      buffer(relIndex) = None
    }
    result
  }

  /** Returns the item at the specified position (if present)
    *
    * @param index the position in the buffer to request from
    * @return the content of the buffer at the given position
    */
  def get(index: Int): Option[A] = {
    val relIndex = toRelIndex(index) //part of the relative index computation is also check for boundaries, doing this first ensures that  get(-1) fails as it should
    if (invalidTill > index) {
      None
    } else {
      buffer(relIndex)
    }
  }

  def apply(index: Int): Option[A] = get(index)

}
