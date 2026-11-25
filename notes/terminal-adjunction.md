# A terminal-layer adjunction inequality

Status: pen-and-paper derivation, independently reviewed within this project.
Not yet fully formalized; **novelty not established**. This is not a proof of
the complete small-gap conjecture. Author of the project: Zhengyi Liu;
AI-assisted derivation and internal review.

## Definitions

S is a numerical semigroup with multiplicity m. The integer c is a chosen
cutoff with every integer >=c in S. Set L=S intersect [0,c), k=|L|,
ell=number of primitive elements below c, r=number of primitive elements
in [c,c+m), q=ceil(c/m), and E_c(S)=k ell+q r-c.

The cutoff is not implicitly replaced by the actual conductor. All comparisons
below use the same cutoff and the same multiplicity.

## Lemma 1 (arbitrary cutoff at least 3m)

Suppose c>=3m. Let B be a finite set of t gaps of S, all in [c-m,c),
and put T=S union B. Write a=|S intersect [m,2m)|. Then T is a numerical
semigroup of multiplicity m and

    E_c(T)-E_c(S) >= t(k+ell-q a)+t^2.

Proof. Every b in B is >=2m, and every positive element of T is >=m.
Thus b+x>=c for positive x in T, except possibly another b; that case
also has b+b'>=2(c-m)>=c. All these sums belong to the tail of S.
Hence T is closed under addition and has the same multiplicity.

The new left elements are exactly B. None is a sum of positive old
elements because B consists of gaps of S. A sum involving a new element
is >=c, so no new left decomposition appears. Thus all old left primitives
remain primitive and all B are primitive:

    k_T=k+t, ell_T=ell+t.

The threshold interval I=[c,c+m) consists of elements in both S and T.
An element of I which becomes decomposable must involve at least one b in B.
It cannot be a sum of two new elements, since 2(c-m)>=c+m. If it is b+x
with x an old positive element, then x<2m, hence x is in S intersect [m,2m).
There are at most a*t such sums; collisions only decrease that count.
Consequently r_T>=r-a*t. Since q is nonnegative, expansion gives

    E_c(T)-E_c(S)
    >= (k+t)(ell+t)+q(r-a*t)-c - (k*ell+q*r-c)
     = t(k+ell-q*a)+t^2.

This argument is independent of the small-gap conjecture.

## Theorem 2 (cutoff a multiple of the multiplicity)

If c=q*m with integer q>=3, the preceding construction satisfies

    E_c(T) >= E_c(S)+t(t+1).

Proof. Every element of A=S intersect [m,2m) is primitive, so ell>=a.
For each x in A, the q-1 elements x,x+m,...,x+(q-2)m belong to L.
These chains are pairwise disjoint: two distinct elements of [m,2m)
cannot be congruent modulo m. None contains zero. Thus

    k >= 1+a(q-1).

It follows that k+ell-q*a >= 1+ell-a >=1. Substitute into Lemma 1.

The theorem permits arbitrary S; it does not assume two generators or
any bound on the gap between the first two primitives.

## Corollary 3 (an explicit small-gap infinite family)

Let q>=3, d>=1, m>q*d, c=q*m and

    S_0 = <m,m+d> union [c,infinity).

For any t-element set B of gaps of S_0 in [c-m,c), let T=S_0 union B.
Then the first two left primitives of T are m,m+d, and

    E_c(T) >= t^2 + t*(q^2-3q+4)/2 >=0.

Indeed the sums of exactly j generators from {m,m+d} are

    {j*m+i*d : 0<=i<=j}.

For 0<=j<=q these layers have disjoint containing intervals because q*d<m.
Exactly layers 0,...,q-1 lie below c, giving k=q(q+1)/2. There are two
left primitives; exactly the q+1 elements of layer q are decomposable
in [c,c+m), giving r=m-(q+1). Thus E_c(S_0)=0 and a=ell=2.
Lemma 1 yields the displayed lower bound. Its coefficient is positive
for q>=3, since q^2-3q+4=q(q-3)+4.

For a theorem about the actual conductor, also require c-1 not in B.
The base S_0 misses c-1, and this condition ensures T still has conductor c.
Without it the assertion concerns E at the chosen cutoff, not necessarily
E at the new actual conductor. This distinction cannot be omitted.

Setting 1<=d<=6 places these families inside the target conjecture, but
does not cover semigroups with arbitrary additional primitives in earlier
layers, or non-multiple actual conductors. q<=3 is already covered by known
results; no claim of novelty is made for that case.

## Remaining work

- Check the literature on profiles, trimming, and high primitive adjunction.
- Independently formalize the set/cardinality and arithmetic arguments.
- Determine whether this supplies a useful new ingredient for the complete
  conjecture, rather than merely another proof of a known special case.
- Do not label the project publication-ready based on this note.
