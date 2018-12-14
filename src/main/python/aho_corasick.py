from typing import Optional

import six


class TrieNode:
    def __init__(self):
        # type: () -> None
        self.children = dict()
        self.full_words = None

    def _assign_full_word(self, full_word):
        # type: (str) -> None
        if self.full_words:
            self.full_words.append(full_word)
        else:
            self.full_words = [full_word, ]

    def add_suffix(self, full_word, index):
        # type: (str, int) -> TrieNode
        till_end = len(full_word) - index
        if till_end:
            child = self.get_child(full_word[index])
            if not child:
                child = TrieNode()
                self.children[full_word[index]] = child
            child.add_suffix(full_word, index + 1)
            return child
        else:
            self._assign_full_word(full_word)
            return self

    def get_child(self, char, default=None):
        # type: (str, TrieNode) -> TrieNode
        return self.children.get(char, default)


class Search:
    def __init__(self, search_strings, ignore_case=False):
        # type: (list, bool) -> None
        self._ignore_case = ignore_case
        if ignore_case:
            self._case_mapping = dict() # needed for report correct case back
            for s in search_strings:
                if s:
                    self._case_mapping[s.lower()] = s
        self._start = self._build_trie(search_strings)
        self._add_fallbacks()

    def _build_trie(self, search_strings):
        # type: (list) -> TrieNode
        result = TrieNode()
        for s in search_strings:
            if s:  # not to add empty string
                result.add_suffix(s.lower() if self._ignore_case else s, 0)
        return result

    def _add_fallbacks(self):
        # type: () -> None
        nodes = list()  # list of all nodes breadth-first (with some additional info)
        # init the list
        for char, child in self._start.children.items():
            nodes.append((child, char, self._start))
        pos = 0
        while pos < len(nodes):
            node, char, parent_fallback = nodes[pos]
            self._process_fallback(node, char, parent_fallback, nodes)
            pos += 1

    def _process_fallback(self, node, node_char, parent_fallback, nodes):
        # type: (TrieNode, str, TrieNode, list) -> None
        fallback = parent_fallback.get_child(node_char, self._start)
        if fallback == node:
            fallback = self._start
        for char, child in node.children.items():
            nodes.append((child, char, fallback))
        for char, child in fallback.children.items():  # add items from fallback
            #if child == node:
            #    continue  # don't need self reference, this can happen with _start children only anyway
            own_child = node.get_child(char)
            if not own_child:
                # node doesn't have a child of the given characters, adding it
                node.children[char] = child
            elif child.full_words:
                if own_child.full_words:
                    own_child.full_words = own_child.full_words + child.full_words
                else:
                    own_child.full_words = child.full_words

    @staticmethod
    def _add_full_words(hits, full_words, index):
        # type: (list, list, int) -> list
        for word in full_words:
            hit = (word, index - len(word) + 1, index)
            hits.append(hit)
        return hits

    def search(self, text):
        # type: (str) -> list
        """
        Within the given text find all occurrences of strings from the constructor
        Args:
            :text: The text to search within
        Returns:
            List of tuples where each item is a trio
                :0: the string found
                :1: index of start of the string within the text
                :2:  index of end of the string within the text
            List is ordered by 1 ascending and 2 descending
            (e.g. earlier founds are placed first, if staring same longer strings before shorter ones)
        """
        hits = list()
        state = self._start
        index = 0
        if self._ignore_case:
            for c in text:
                c = c.lower()
                state = state.get_child(c, self._start)
                if state.full_words:
                    for word in state.full_words:
                        hit = (self._case_mapping[word], index - len(word) + 1, index)
                        hits.append(hit)
                index += 1
        else:
            for c in text:
                state = state.get_child(c, self._start)
                if state.full_words:
                    hits = self._add_full_words(hits, state.full_words, index)
                index += 1
        return sorted(hits, key=lambda h: (h[1], -h[2]))  # TODO avoid sorting


class Replace:
    def __init__(self, replacement_pairs, ignore_case=False):
        # type: (dict, bool) -> None
        self._replacement_pairs = replacement_pairs
        self._search_engine = Search(list(replacement_pairs.keys()), ignore_case)

    def replace(self, text, empty_on_no_hit=True):
        # type: (str, bool) -> Optional[ReplacementResult]
        """
        Within the given text replace all keys from the constructor with their values
        Args:
            :text: The text to make the replacements in
            :empty_on_no_hit: if true in case of no hit the result text is an empty string
        Returns:
            Dictionary of following components:
                :original_text: the original text
                :result: the text after replacements (empty if no hit and the empty_on_no_hit is true)
                :total_replacement_count: the number of replacements
                :replacements: dictionary where the number of replacements per key are recorded
        """
        found = self._search_engine.search(text)
        if len(found) or not empty_on_no_hit:
            result = ReplacementResult(text)
            after_last_find = 0
            result_text = ''
            for (key, start, end) in found:
                if after_last_find <= start:
                    # finds don't overlap
                    if after_last_find < start:
                        # there is a gap between the two finds
                        result_text += text[after_last_find:start]
                    result_text += self._replacement_pairs[key]
                    after_last_find = end + 1
                    result.add_hit(key)
            if after_last_find < len(text):
                result_text += text[after_last_find:]
            result.result = result_text
            return result
        elif empty_on_no_hit:
            return None
        else:
            return ReplacementResult(text)


class ReplacementResult:
    def __init__(self, original):
        # type: (str) -> None
        self.total_replacement_count = 0
        self.replacements = dict()
        self.original = original
        self.result = original

    def add_hit(self, key):
        # type (str) -> None
        self.total_replacement_count += 1

        if key in self.replacements:
            self.replacements[key] += 1
        else:
            self.replacements[key] = 1