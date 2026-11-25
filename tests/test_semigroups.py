import pytest
from semigroups import bitset, closed_prefixes, from_generators, reference


def test_exhaustive_small_independent_of_enumerator():
    for c in range(1, 13):
        expected = []
        for b in range(1, 1 << c, 2):
            prefix = {i for i in range(c) if b >> i & 1}
            try:
                a = reference(prefix, c)
            except ValueError:
                with pytest.raises(ValueError):
                    bitset(b, c)
                continue
            assert a == bitset(b, c)
            expected.append(b)
        actual = list(closed_prefixes(c))
        assert len(actual) == len(set(actual))
        assert sorted(actual) == expected


@pytest.mark.parametrize('gens,c,expected', [([14,22,23],56,-1),([19,26,27],90,-1)])
def test_known_negative_examples(gens, c, expected):
    prefix = from_generators(gens, c)
    a = reference(prefix,c)
    assert a == bitset(sum(1 << x for x in prefix),c)
    assert a.E == expected and a.canonical


def test_normalization_and_noncanonical():
    assert from_generators([3,3,6,100],10) == from_generators([3],10)
    a = reference(from_generators([3,4],10),10)
    assert a.conductor == 6 and not a.canonical
    assert reference({0},1).primitives == (1,)


@pytest.mark.parametrize('prefix,c', [({1},3),({0,-1},3),({0,3},3),({0,2},5),({0},0)])
def test_invalid_prefixes(prefix,c):
    with pytest.raises(ValueError):
        reference(prefix,c)


def test_invalid_generators():
    for gens in [[0],[-1],[1.5],[True]]:
        with pytest.raises(ValueError):
            from_generators(gens,10)
