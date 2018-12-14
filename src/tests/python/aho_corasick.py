from python.aho_corasick import Search, Replace
import sys

def test():
    test_search()
    print('')
    test_replace()
    print('')
    print("aho_corasick tests OK")


def test_search():
    # Simple test
    s = Search(['One', 'Two', 'Three'])
    check(s.search('One, Two, Three.'), [('One', 0, 2), ('Two', 5, 7), ('Three', 10, 14)])
    # Repeated letters and not present word
    s = Search(['zoom', 'bebel', 'zzz', 'lamb'])
    check(s.search('zzzzzoom bebebel'), [('zzz', 0, 2), ('zzz', 1, 3), ('zzz', 2, 4), ('zoom', 4, 7), ('bebel', 11, 15)])
    # Prefix, suffix, overlap, successive hit
    s = Search(['hell', 'hello', 'low', 'sun', 'slow', 'lo', 'shine', 'any', 'more', 'anymore'])
    check(s.search('helloworld, no sunshine anymore!'), [('hello', 0, 4), ('hell', 0, 3), ('low', 3, 5), ('lo', 3, 4), ('sun', 15, 17), ('shine', 18, 22), ('anymore', 24, 30), ('any', 24, 26), ('more', 27, 30)])
    # case sensitivity testing
    s = Search(['sIt', 'sEnS'], False)
    check(s.search('CaSe SeNsItIvE, sEnSiTiVe!'), [('sIt', 8, 10), ('sEnS', 16, 19)])
    # case sensitivity testing
    s = Search(['sIt', 'sEnS'], True)
    check(s.search('CaSe InSeNsItIvE, iNsEnSiTiVe!'), [('sEnS', 7, 10), ('sIt', 10, 12), ('sEnS', 20, 23), ('sIt', 23, 25)])


def test_replace():
    # Case sensitive
    r = Replace({"Hello": 'Hi', 'world': 'universe', 'stars': 'universe'}, False)
    text = 'Hello world, hello stars. Hello people.'
    result = r.replace(text)
    check(result.replacements, {'world': 1, 'Hello': 2, 'stars': 1}, 'replacement: ')
    check(result.total_replacement_count, 4, 'total_replacement_count: ')
    check(result.original, text, 'original: ')
    check(result.result, 'Hi universe, hello universe. Hi people.', 'result: ')
    # Case insensitive
    r = Replace({"Hello": 'Hi', 'world': 'universe', 'stars': 'universe'}, True)
    text = 'Hello world, hello stars. Hello people.'
    result = r.replace(text)
    check(result.replacements, {'world': 1, 'Hello': 3, 'stars': 1}, 'replacement: ')
    check(result.total_replacement_count, 5, 'total_replacement_count: ')
    check(result.original, text, 'original: ')
    check(result.result, 'Hi universe, Hi universe. Hi people.', 'result: ')
    # Overlapping
    r = Replace({"hello": 'alo', 'hell': 'b', 'lo': 'c', 'el': 'd'}, True)
    text = 'hello world, hell low.'
    result = r.replace(text)
    check(result.replacements, {'hello': 1, 'hell': 1, 'lo': 1}, 'replacement: ')
    check(result.total_replacement_count, 3, 'total_replacement_count: ')
    check(result.original, text, 'original: ')
    check(result.result, 'alo world, b cw.', 'result: ')
    # empty_on_no_hit testing
    r = Replace({'x': '???'}, True)
    check(r.replace('Lorem Ipsum'), None)
    r = Replace({'x': '???'}, False)
    text = 'Lorem Ipsum'
    result = r.replace(text, False)
    check(result.replacements, {}, 'replacement: ')
    check(result.total_replacement_count, 0, 'total_replacement_count: ')
    check(result.original, text, 'original: ')
    check(result.result, text, 'result: ')


def check(a, b, prefix=''):
    assert (a == b), '%s"%s" differs from "%s"' % (prefix, a, b)
    print('.', end='')
    sys.stdout.flush()


if __name__ == '__main__':
    test()
