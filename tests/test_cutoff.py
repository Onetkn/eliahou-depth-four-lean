"""Regression checks for the independently written symbolic cutoff argument."""
from semigroups import bitset, closed_prefixes, from_generators


def test_fixed_semigroup_cutoff_transition():
    for c in range(1,19):
        for bits in closed_prefixes(c):
            a = bitset(bits,c)
            b = bitset(bits | (1 << c),c+1)
            delta = b.q-a.q
            assert delta == int(c % a.multiplicity == 0)
            assert b.k == a.k+1
            if c in a.primitives:
                assert (b.ell,b.r) == (a.ell+1,a.r-1)
                expected = a.k+a.ell-a.q+delta*(a.r-1)
            else:
                assert (b.ell,b.r) == (a.ell,a.r)
                expected = a.ell-1+delta*a.r
            assert b.E-a.E == expected >= 0
            if a.ell == 0:
                assert a.E == 0
            if a.ell == 1:
                assert a.k == a.q and a.r == a.multiplicity-1
                assert a.E == a.q*a.multiplicity-c


def test_consecutive_generator_formula():
    for m in range(2,20):
        for c in range(m+2,m*(m-1)+20):
            prefix = from_generators([m,m+1],c)
            a = bitset(sum(1 << n for n in prefix),c)
            if c >= m*(m-1):
                expected = c-m*(m-1)
            else:
                q = (c+m-1)//m
                u = c-(q-1)*m
                expected = m+u-q if u <= q else m-u
            assert a.E == expected
