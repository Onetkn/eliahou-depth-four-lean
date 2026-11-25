# Research artifact status

The complete main theorem is:

> For a numerical semigroup of multiplicity m containing [c,infinity),
> if 3m<c<=4m and S intersect [m,2m)={m,m+d}, with 0<d<m,
> then the cutoff-relative Eliahou number E_c(S) is nonnegative.

The usual-conductor statement follows by taking c to be the actual conductor.
The theorem does not cover arbitrary depth or more than two first-interval
elements, and does not settle the full Bacher or Wilf conjecture.

## Included result

- Complete readable proof: paper/main.tex and output/pdf/eliahou-depth-four.pdf.
- Complete formal theorem: Eliahou.DepthFour.depth_four_nonneg.
- Full semigroup-to-counting bridge, not just a conditional arithmetic lemma.
- Pinned Lean 4.36.0 and Mathlib/dependency source revisions.
- Cross-platform build and explicit main-theorem axiom audit.
- A scoped primary-source literature comparison and an explicit infinite
  family outside the directly compared sufficient hypotheses.
- Author Zhengyi Liu; no email or affiliation; AI assistance disclosed.

The main formal theorem was compiled successfully. Its transitive axioms are
only propext, Classical.choice, and Quot.sound. Neither bounded enumeration nor
an external numerical oracle supplies a premise or proof of this theorem.

## Limits of the claim

Lean proves the formal implication. It does not establish that the result is
the first of its kind, that the literature review is exhaustive, or that a
journal will accept the paper. The manuscript does not assert those claims.

The older experiments, fixed-cutoff monotonicity notes and algebra-only
CutoffStep module are exploratory supplements. They are not substitutes for
the main proof; the general semantic cutoff-monotonicity theorem is not claimed
to be formalized here. No journal or arXiv submission has been made.
