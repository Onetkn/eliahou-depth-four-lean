# Fixed-semigroup cutoff monotonicity and a consecutive-generator baseline

Status: independently derived pen-and-paper arguments; not yet Lean-checked.
Novelty is **not established**. These are auxiliary results and baselines, not a
solution of Bacher's Conjecture 2.7. Computational checks below are evidence of
implementation consistency, not proofs of the quantified statements.

## Scope and notation

Let S be a numerical semigroup, m its least positive element, and C its actual
conductor. Choose an integer cutoff c >= max(C, 1). Thus every integer >= c
belongs to S, but c need not equal C. Write P for the intrinsic set of positive
primitive elements of S, and define

- k(c) = |S intersect [0,c)|;
- ell(c) = |P intersect [0,c)|;
- r(c) = |P intersect [c,infinity)|;
- q(c) = ceil(c/m);
- E(c) = k(c) ell(c) + q(c) r(c) - c.

Every primitive is < c+m: if n >= c+m, then n = m+(n-m) decomposes into two
positive elements of S. Therefore r(c) can be computed in [c,c+m).
The multiples 0,m,...,(q(c)-1)m belong to S and are < c, so k(c) >= q(c).

Bacher explicitly uses possibly noncanonical presentations in Section 2.1:
the counts are relative to the specified cutoff, not necessarily C.
Reference: https://arxiv.org/html/2604.25051v9#S2.SS1

## Lemma 1: one-step change for a fixed S

Put delta = q(c+1)-q(c). Then delta is 1 when m divides c and 0 otherwise.
Because c belongs to S, k(c+1)=k(c)+1.

If c is not primitive, ell and r are unchanged. Expanding the definitions gives

    E(c+1)-E(c) = ell(c)-1 + delta*r(c).

Here ell(c)>=1: otherwise m>=c; if m=c then c=m is primitive, a contradiction.
Consequently this difference is nonnegative.

If c is primitive, ell(c+1)=ell(c)+1 and r(c+1)=r(c)-1. Expansion gives

    E(c+1)-E(c) = k(c)+ell(c)-q(c) + delta*(r(c)-1).

This is nonnegative because k(c)>=q(c), ell(c)>=0, r(c)>=1 and delta>=0.
Thus E(c+1)>=E(c) in both cases, and induction yields E(b)>=E(a) whenever
max(C,1)<=a<=b.

This compares two cutoffs of the **same** S. It says nothing about monotonicity
when a different semigroup is obtained by adding/removing generators or gaps.

### Boundary c=m

Here S={0} union [m,infinity), k=1, ell=0, r=m, q=1, E=0.
The element c=m is primitive, delta=1, and the primitive formula gives
E(m+1)-E(m)=m-1. In particular there is no exception at a ceiling jump.

### Boundary S=N

Then C=0,m=1. Our cutoff domain starts at c=1, where k=1,ell=0,r=1,q=1,E=0.
For c>=2, k=c,ell=1,r=0,q=c,E=0. Thus monotonicity also holds. The actual
conductor c=0 can be handled separately with k=0,ell=0,r=1,q=0,E=0.
The finite-prefix implementation deliberately uses positive cutoffs.

## Lemma 2: at most one left primitive

If ell=0, there is no positive element below c, since a smallest such element
would itself be primitive. Hence m=c and the ordinary-semigroup calculation
above gives E=0.

If ell=1, its sole left primitive must be m<c. Every element of S below c
is a sum of left primitives (repeatedly decompose a nonprimitive element;
all summands are smaller positive integers). Therefore the left elements
are exactly 0,m,...,(q-1)m, so k=q and q>=2.

Any decomposable n in [c,c+m) has both summands <c, since a summand >=c
would force n>=c+m. Both summands are thus multiples of m. The interval
[c,c+m) contains exactly one multiple of m, namely qm. It is decomposable
as m+(q-1)m, with both summands positive and <c. Hence r=m-1 and

    E(c) = q + q*(m-1) - c = qm-c >= 0.

## Corollary: reducing the small-gap assertion to canonical cutoffs

Suppose Conjecture 2.7 has been proved for actual conductors whenever there
are at least two left primitives. Take any allowed noncanonical presentation
with gamma_1-m<=6. At the actual conductor C:

- if there are at most one left primitives, Lemma 2 gives E(C)>=0;
- otherwise the first two intrinsic primitives are the same as at the larger
  cutoff, so the assumed canonical theorem applies.

Monotonicity then gives E(c)>=E(C)>=0. For S=N use the explicit boundary case.
The converse is immediate because canonical presentations are included.
This reduction does not prove the remaining canonical conjecture.

## Appendix: exactly two consecutive left primitives

Let m>=2 and c>=m+2, and set S=<m,m+1> union [c,infinity).
There are exactly two left primitives, m and m+1. This is a strict subclass
of the d=1 problem, which allows additional left primitives.

For m>=3 and m+2<=c<=m(m-1), write q=ceil(c/m) and
u=c-(q-1)m, so 2<=q<=m-1 and 1<=u<=m. Then

    E(c) = m+u-q, if u<=q;
    E(c) = m-u,   if u>q.

Proof: the sums of exactly t elements chosen from {m,m+1} form the integer
interval [tm,tm+t]. For 0<=t<=q-1 these intervals are disjoint. The layers
0,...,q-2 contribute q(q-1)/2 left elements; layer q-1 contributes min(q,u).
Thus k=q(q-1)/2+min(q,u).

All decomposable elements in [c,c+m) must be sums of the two left primitives.
Only layers q-1 and q can meet this interval. Their contributions have sizes
max(q-u,0) and min(q+1,u), respectively, and are disjoint. (At q=2, u>=2
by c>=m+2, so the first contribution is zero; no primitive is counted as a
decomposable.) Hence their total s is q if u<=q, and q+1 if u>q.
Since r=m-s, ell=2 and qm-c=m-u, substituting gives the displayed formula.
Both branches are nonnegative because q<=m-1 and u<=m.

For c>=m(m-1), the original two-generator semigroup already contains all
integers >=c. Counting the gaps between the layers gives genus m(m-1)/2;
there are no right primitives and k=c-m(m-1)/2, so

    E(c) = c-m(m-1) >= 0.

For m=2 the allowed range c>=4 lies entirely in this last case.

If c<=m(m-1) is canonical, then necessarily u>q, and E(c)=qm-c.
The explicit formula should be treated as a baseline until literature
comparison establishes whether its exact form has already appeared.

## Reproducible exploratory checks (2026-11-26)

Using the project's independent invariant functions in memory:

- All 35,563 valid closed prefixes with cutoffs 1,...,24 satisfy both one-step
  formulas and E(c+1)>=E(c) after including c in the next prefix (fixed S).
  There were 14,930 primitive and 20,633 decomposable transitions.
- All 24 ell=0 and 276 ell=1 presentations in that run satisfy Lemma 2.
- The consecutive-generator formula agrees with the bitset implementation
  for all 12,464 pairs with 3<=m<=34 and m+2<=c<=m(m-1).

These counts were produced by ephemeral Python checks, not by persisted
certificate artifacts. The mathematical arguments above stand independently
of these tests, and still require formalization and independent review.

## Literature status

The arXiv abstract page checked on 2026-11-26 still identifies v9 dated
2026-10-14 as the latest version. Section 2.2 labels the target Conjecture 2.7.
Targeted searches found no later resolution, which is not proof of novelty.

Eliahou's 2018 paper proves E>=0 for depth q<=3 and other subclasses;
these are known baselines, not possible novelty claims. Its notation W_0
equals the E used here. The familiar embedding-dimension-two theorem concerns
the total number of primitives, not merely the number of left primitives;
one must not substitute it for an assertion about ell=2.
Reference: https://ems.press/content/serial-article-files/32312

The short search did not establish a general existing theorem E>=0 for all
ell<=2. That absence is inconclusive. In particular it does not certify the
novelty of the appendix or make it a publication-ready result.

**Specific overlap found:** Eliahou 2018, Theorem 7.1 proves E>=rho for a true
grading; Corollary 7.2 verifies that grading when q>=4 and all left primitives
lie in [m, m+(m-rho)/(q-1)). For the canonical consecutive-generator subclass
in the appendix, u>q and m-rho=u, so m+1 is strictly below m+u/(q-1).
Thus the nonnegativity of that canonical subclass is already covered by the
2018 result for q>=4, and by the known depth<=3 results for smaller q.
The noncanonical extension follows from the cutoff reduction. In particular,
the appendix must not be advertised as a newly solved infinite subclass.
