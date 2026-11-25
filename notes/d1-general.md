# General gap-one problem: symbolic reduction and a concrete obstacle

Status: research notes, not a completed proof and not a novelty claim.
The goal is E>=0 for all numerical semigroups whose first two primitives are
m and m+1, allowing arbitrarily many other left primitives and arbitrary depth.
Finite experiments are only checks on proposed statements, never the final
argument for this goal.

## Exact Apéry-coordinate formulation

It suffices to treat the actual conductor by the cutoff-monotonicity reduction.
Discard the known depth q<=3 cases for purposes of finding new progress.
For each residue 0<=i<m, let w_i be the least member of S congruent to i mod m,
and write w_i=m*x_i+i. Then x_0=0 and x_i>=1 for i>0. Since m+1 belongs to S,

    x_1=1,
    x_(i+1)<=x_i+1  for 0<=i<m-1,
    x_i<=i         for 1<=i<m.

Proof: w_i+(m+1) belongs to residue i+1, so the minimal representative of that
residue is no larger. Iterating from x_0=0 proves the last bound.
The full additive-closure constraints must also be retained:

    x_(i+j) <= x_i+x_j                 if i+j<m;
    x_(i+j-m) <= x_i+x_j+1             if i+j>=m.

The slope bounds alone are not an adequate replacement for these Kunz
inequalities.

Set q=max(x_i : 1<=i<m), and let h be the largest index where x_h=q.
The largest Apéry element is q*m+h. It follows that

    c=(q-1)*m+h+1,
    rho=m-h-1,
    q<=m-1.

For i>0 define

    t_i = q-x_i                   if i<=h,
    t_i = q-1-x_i                 if i>h.

This is exactly the number of elements of residue i below c, and is
nonnegative. The zero residue contributes q elements, so

    k = q + sum_(i=1)^(m-1) t_i.

An Apéry element w_i, i>0, is decomposable if and only if some j,k>0 with
j+k congruent to i mod m attain equality in the appropriate Kunz inequality.
Indeed a decomposition of an Apéry element cannot use a positive multiple of
m; replacing either summand by the minimal representative of its residue
would otherwise give a smaller representative for residue i. Conversely an
equality supplies a decomposition.

Let A be the indices i>0 for which w_i is primitive, and let

    a = |{i in A : t_i>0}|,
    b = |{i in A : t_i=0}|,
    N = m-1-|A|.

Here ell=1+a (including m), r=b, and N counts decomposable nonzero Apéry
elements. Substitution, with no inequality, gives the useful identity

    E = (1+a)*sum_i t_i - q*N + rho.

Therefore the general d=1 problem is equivalent to proving the following
finite-dimensional, but uniformly quantified, combinatorial inequality:

    q*N <= (1+a)*sum_i t_i + rho

for every valid Kunz vector with x_1=1. This is a symbolic reformulation, not
an argument that a fixed finite set of vectors suffices.

## Why a natural chain argument stops short

If x_(i+1)=x_i+1 and i>=1, then w_(i+1)=w_i+(m+1) is decomposable.
This partitions the residue indices into consecutive rising chains. Along
each chain the counts t_i decrease by one; a chain cannot cross h because
x_h=q is maximal and a rise at h would exceed q.

The obstacle is that a chain head need not be primitive: it may be the sum
of other Apéry elements. Thus counting chain heads as generators overcounts
ell, which is precisely the coefficient multiplying sum(t_i) in the target
inequality. A valid proof needs to charge those composite chain heads to
actual left primitives, while controlling the same primitive being charged
many times. Merely observing x_(i+1)<=x_i+1 does not provide that charging
argument.

## Concrete example outside the simplest sufficient criteria

Consider S=<20,21,55>_100. Direct exact computation gives

    m=20, c=100, q=5, rho=0, k=21, ell=3, r=9, E=8.

Its Apéry coordinates, indexed 0,...,19, are

    [0,1,2,3,4,5,5,5,5,5,5,5,5,5,5,2,3,4,5,5].

The above identity reads 3*16-5*8=8. Yet ell*k-c=-37, so the crude
sufficient condition ell*k>=c fails. The left primitive 55 lies in the
second layer [40,60), so the true-grading assumption S_2=2*S_1 fails:
55 belongs to S_2 but not to {40,41,42}=2*{20,21}.

The concentration (largest distance between consecutive positive semigroup
elements) is 19, attained between 21 and 40. Thus the known concentration
criterion is not useful here either. This is not a counterexample; it shows
why these otherwise useful sufficient criteria do not settle even very
small three-left-generator d=1 examples.

## Independent audit of the last-layer extension lemma

Let S_0 be any numerical semigroup of multiplicity m, let c>=3m with
[c,infinity) contained in S_0, and let B be a t-element subset of the missing
integers in [c-m,c). Set S=S_0 union B, using the same cutoff c.

This union is closed: sums involving B and a positive old element are >=c,
as are sums of two members of B. Its multiplicity remains m. Every member
of B is a new primitive below c: a decomposition into old elements would
contradict closure of S_0, and a decomposition involving B is >=c. Old left
primitives remain primitive for the same reason. Thus

    k'=k+t, ell'=ell+t.

Let a_0=|S_0 intersect [m,2m)|. A newly decomposable element in [c,c+m)
must use one member of B and one old element in [m,2m): two members of B
sum to >=2c-2m>=c+m. The number H of new threshold decomposables satisfies
H<=a_0*t, so r'=r-H. Expanding E gives the exact identity and lower bound

    E'-E = t*(k+ell)+t^2-q*H
          >= t*(k+ell-q*a_0)+t^2.

No claim that the pair sums are distinct is required.

### Stronger uniform consequence at cutoffs divisible by m

If c=q*m with q>=3, each of the a_0 elements p in [m,2m) yields q-1 distinct
positive left elements p,p+m,...,p+(q-2)m. The residue classes for distinct p
are different, so these a_0 chains are disjoint. Including zero proves

    k>=1+a_0*(q-1).

Also ell>=a_0 because every element of [m,2m) is primitive. Consequently

    k+ell-q*a_0 >= 1+ell-a_0 >= 1,
    E(S_0 union B) >= E(S_0)+t*(t+1).

This is valid for every base S_0, not only consecutive-generator bases.
It shows that at a cutoff divisible by m, a minimal negative-E example
cannot contain a left primitive in the final multiplicity-width layer:
removing all such primitives preserves the semigroup below c and cannot
increase E. It does not remove primitives in earlier layers.

### Two-generator base with a bounded spread

For S_0=<m,m+d>_(q*m), where q>=3, d>=1 and q*d<m, the layers of sums with
t factors (0<=t<=q) are the disjoint arithmetic progressions

    {t*m+j*d : 0<=j<=t}.

Thus k=q*(q+1)/2, ell=a_0=2, the threshold has q+1 decomposable elements,
and E(S_0)=0. The general bound gives

    E(S_0 union B) >= t^2 + t*(q^2-3*q+4)/2.

This is a fully symbolic derivation. Its relation to existing results needs
further checking; the lemma's elementary form is not evidence of novelty.
In particular the base nonnegativity is already covered by known
true-grading results.

## Focused literature check

Eliahou, *Wilf's conjecture and Macaulay's theorem* (2018), Theorem 7.1,
proves E>=rho under a true-grading hypothesis. Corollary 7.2 verifies it
when all left primitives lie in a specified narrow interval above m. That
is stronger structure than merely having m+1 present.
Source: https://ems.press/content/serial-article-files/32312

Almirón and Moyano-Fernández, *Eliahou number, Wilf function and concentration
of a numerical semigroup*, arXiv:2104.03793v2, Theorem 4.4, gives a sufficient
condition in terms of the maximum consecutive-positive-element gap K:
with the paper's notation c=L*m+rho', it requires m/K^2>(L+1)/(L-1).
Having first gap 1 does not imply small K; even <m,m+1> has K=m-1.
The theorem therefore does not establish the general d=1 assertion.
Source: https://arxiv.org/html/2104.03793#S4.SS2

No source checked here establishes the complete d=1 assertion. This limited
search is not a certification of an open problem or of novelty. The remaining
proof obligation is the charging inequality stated above (or another argument
that controls later, possibly composite Apéry chain heads).
