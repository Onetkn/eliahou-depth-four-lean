"""Exact finite-prefix numerical-semigroup calculations (no floating point)."""
from dataclasses import asdict, dataclass
from typing import Iterator


@dataclass(frozen=True)
class Invariants:
    cutoff: int
    conductor: int
    multiplicity: int
    left: tuple[int, ...]
    primitives: tuple[int, ...]
    k: int
    ell: int
    r: int
    q: int
    E: int
    W: int
    canonical: bool
    gap: int | None

    def record(self):
        return asdict(self)


def validate_prefix(prefix: set[int], cutoff: int) -> None:
    if type(cutoff) is not int or cutoff < 1:
        raise ValueError("cutoff must be a positive integer")
    if 0 not in prefix or any(type(x) is not int or x < 0 or x >= cutoff for x in prefix):
        raise ValueError("prefix must contain zero and only integers in [0, cutoff)")
    if any(a + b < cutoff and a + b not in prefix for a in prefix for b in prefix):
        raise ValueError("prefix is not additively closed below cutoff")


def from_generators(generators: list[int], cutoff: int) -> set[int]:
    if type(cutoff) is not int or cutoff < 1:
        raise ValueError("cutoff must be a positive integer")
    if any(type(g) is not int or g <= 0 for g in generators):
        raise ValueError("generators must be positive integers")
    reachable = {0}
    for n in range(1, cutoff):
        if any(n - g in reachable for g in generators):
            reachable.add(n)
    return reachable


def reference(prefix: set[int], cutoff: int) -> Invariants:
    """Independent set implementation, explicitly checks each decomposition."""
    validate_prefix(prefix, cutoff)
    m = min(prefix - {0}, default=cutoff)
    elements = prefix | set(range(cutoff, cutoff + m))
    primitives = tuple(n for n in sorted(elements - {0})
                       if not any(a in elements and n-a in elements for a in range(1, n)))
    left = tuple(sorted(prefix))
    left_primitives = [p for p in primitives if p < cutoff]
    ell = len(left_primitives)
    r = len(primitives) - ell
    k = len(left)
    q = (cutoff + m - 1) // m
    conductor = max(set(range(cutoff)) - prefix, default=-1) + 1
    return Invariants(cutoff, conductor, m, left, primitives, k, ell, r, q,
                      k*ell + q*r - cutoff, k*(ell+r)-cutoff,
                      cutoff == conductor,
                      left_primitives[1]-m if ell >= 2 else None)


def bitset(prefix_bits: int, cutoff: int) -> Invariants:
    """Bit-parallel implementation using the positive sumset."""
    if type(cutoff) is not int or cutoff < 1:
        raise ValueError("cutoff must be a positive integer")
    if type(prefix_bits) is not int or prefix_bits < 1 or not prefix_bits & 1 or prefix_bits >> cutoff:
        raise ValueError("invalid prefix bits")
    positive = prefix_bits & ~1
    m = (positive & -positive).bit_length()-1 if positive else cutoff
    bound = cutoff + m
    elements = prefix_bits | (((1 << m)-1) << cutoff)
    positives = elements & ~1
    sums = 0
    todo = positives
    while todo:
        low = todo & -todo
        sums |= positives << (low.bit_length()-1)
        todo ^= low
    mask = (1 << cutoff)-1
    if sums & mask & ~prefix_bits:
        raise ValueError("prefix is not additively closed below cutoff")
    prim = positives & ~sums
    left = tuple(n for n in range(cutoff) if prefix_bits >> n & 1)
    primitives = tuple(n for n in range(1, bound) if prim >> n & 1)
    ell = (prim & mask).bit_count()
    r = (prim >> cutoff).bit_count()
    k = prefix_bits.bit_count()
    q = (cutoff+m-1)//m
    conductor = (mask & ~prefix_bits).bit_length()
    return Invariants(cutoff, conductor, m, left, primitives, k, ell, r, q,
                      k*ell+q*r-cutoff, k*(ell+r)-cutoff,
                      cutoff == conductor,
                      primitives[1]-m if ell >= 2 else None)


def closed_prefixes(cutoff: int) -> Iterator[int]:
    """Enumerate every closed prefix exactly once, including noncanonical ones.

    At n, previous positives force n iff n is in their sumset. Otherwise
    membership can be chosen freely. No unproved conjecture is used to prune.
    """
    if cutoff < 1:
        raise ValueError("cutoff must be positive")
    def visit(n, bits, sums):
        if n == cutoff:
            yield bits
            return
        if not (sums >> n & 1):
            yield from visit(n+1, bits, sums)
        new_sums = sums | ((bits & ~1) << n) | (1 << (2*n))
        yield from visit(n+1, bits | (1 << n), new_sums)
    yield from visit(1, 1, 0)
