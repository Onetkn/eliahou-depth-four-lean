# Literature audit: depth four with two first-layer primitives

Audit date: 2026-11-26. This is a scoped novelty check, not a certification of novelty.

## Candidate and notation

The final candidate assumes actual conductor `3m<c<=4m`, `0<d<m`, and
`S intersect [m,2m)={m,m+d}`, with unrestricted higher primitives, and
concludes `E(S)>=0`. The proof also treats the specified-cutoff number
when the actual conductor is smaller. The earlier restricted candidate
`c=4m, d<=6, m>12d` has been superseded.

At actual conductor `4m`, the first-layer primitive count is `p1=2`, whereas
the first Apéry count is `alpha1=1`: `m` is not an Apéry element. These
notations must not be confused. Also, `W>=0` does not imply `E>=0`.

**Scoped verdict:** no inspected source explicitly states the full candidate.
The family below is outside the hypotheses of the inspected E criteria,
including the divisible-conductor divset criteria. The depth-four theorem
is selected for formalization on this evidence. This is not a proof of
absolute originality, and publication must not claim an established first
proof. The older three-left-generator subcase should not be presented as
novel on present evidence. The unshifted first-interval condition is not
identical to the shifted Apery condition alpha1=1 for rho>0.

## Explicit scope witness for the final candidate

For every integer m>=42, set

    S_m = <m,m+1,2m+10,2m+20> union [4m-1,infinity).

Its left elements are exactly

    {0} union (m+{0,1}) union (2m+{0,1,2,10,20})
        union (3m+{0,1,2,3,10,11,20,21}).

Thus 4m-2 is a gap, the true conductor is 4m-1, k=16, and ell=4.
Its threshold decomposables have offsets, relative to 4m,

    {0,1,2,3,4,10,11,12,20,21,22,30,40}.

All these values are below 5m-1 even at m=42. Therefore s=13 and E=13.
These are symbolic classifications of representations, not sampled counts.

The family fails the inspected sufficient hypotheses as follows:

* k=16>12; the at-most-12-left-elements theorem does not apply.
* Its shifted first Apery count is alpha1=1, not zero.
* S2 is not 2S1: the two higher primitives occur in S2. The true-grading
  equality of JEMS Theorem 7.1 fails (mere sumset inclusion is insufficient).
* m does not divide 4m-1. The cited Divsets propositions for special
  semigroups therefore do not apply, regardless of a model's tameness.
* Its concentration is K=m-1. In the concentration paper, Corollary 5.3
  requires ell>=2K and Corollary 5.4 requires ell>=K+1; both fail since
  ell=4 and m>=42. Theorem 4.4's sufficient condition also fails.

This proves only noncoverage by these specific sufficient conditions.
It does not prove that the family or full theorem was previously unknown,
nor exclude every possible consequence or refinement of previous work.
The rest of this note records the detailed earlier divisible-conductor
comparison; those overlaps remain important to state in related work.

## Verified coverage

| Source | Established result relevant here | Relation to candidate |
|---|---|---|
| Eliahou, *Wilf's conjecture and Macaulay's theorem*, JEMS 20 (2018), Theorem 7.1 and Corollary 7.2 | True grading through level `q-1` gives `E>=rho`. All left primitives in `[m,m+(m-rho)/(q-1))` imply that grading. | At `c=4m`, covers all-left-primitives-below-`4m/3`, including the two-generator base. Does not directly allow arbitrary middle or terminal primitives. |
| Eliahou–Marín-Aragón, *On numerical semigroups with at most 12 left elements* (2020), Theorem 4.1 | `|L|<=12 => E>=0`, genuinely E, not merely W. | Covers all candidate members with at most 12 left elements. |
| Same, Theorem 3.1 | If `alpha1=...=alpha_(ceil(q/2)-1)=0`, then `E>=0`. | At `q=4` this requires `alpha1=0`, so it does not cover our `alpha1=1`. |
| Same, Section 4.2.1 | Treats `q=4, alpha1=1` **under the standing assumption `|L|<=12`**. It uses `2 alpha2+alpha3<=5`. | This section is not an unrestricted first-layer-two theorem. |
| Eliahou, *Divsets, numerical semigroups and Wilf's conjecture*, HAL v4 / Comm. Algebra 53 (2025), Proposition 5.4 | For `m|c`, a tame divset model implies `E>=0`. | Potentially broad overlap; see below. |
| Same, Theorem 6.2 and Corollary 6.3 | Divsets of degree two are tame; the proof of the semigroup corollary gives `E>=0`. | Covers members admitting an appropriate degree-two Apéry model, not automatically the whole candidate. |
| Same, Section 7 | Divset models with vertex-maximal matching number at most five are tame, apart from one explicitly classified wild shape. | Our first-layer condition excludes that wild shape. Thus every candidate member admitting such a model is already covered. |

Primary text links: [JEMS full text](https://ems.press/content/serial-article-files/32312),
[2020 arXiv full text](https://arxiv.org/html/2006.01480),
[Divsets DOI](https://doi.org/10.1080/00927872.2024.2428807),
[HAL v4 record](https://hal.science/hal-04234167v4).
HAL direct access was blocked by Anubis and the publisher full text returned 403;
the actual author's HAL-v4 manuscript was read through its
[full-text mirror](https://www.academia.edu/123385802/Divsets_numerical_semigroups_and_Wilfs_conjecture).
The mirror is the paper itself, not an AI summary. Final-version changes
have not been compared against HAL v4.

## The divset overlap that must be settled

Write `n=|X1|` and `vm(X)` for the maximum number of vertices covered by a
matching in the graph associated with the divset `X`. Tameness means
`2|D(X)| <= (n+1)vm(X)`. The exact low-matching references are Propositions
7.2 (`vm=2`), 7.3 (`vm=3`), 7.8 (`vm=5`), and Corollary 7.6 (`vm=4`).
The exceptional `vm=4` shape is

    [x1^3, x1^2*x2, x1*x2^2, x2^3,
     x1*x3,...,x1*xn, x2*x3,...,x2*xn].

The following is our applicability check, not a quotation from the paper.
In a model at `c=4m`, every modeled Apéry element is below `5m`.
The two distinct cubes in the exceptional shape would map to `3a,3b<5m`
for distinct non-m primitive elements `a,b`. Both would be in `(m,2m)`,
contradicting the candidate's sole such element `m+d`. Therefore this
exception cannot occur. The cases `vm=0,1` are elementary degenerate cases.

This proves **conditional old coverage whenever a candidate member has a
model with `vm<=5`**. It does not prove that every candidate member has such
a model. Nor does `vm>=6` establish novelty: a high-matching model can still
be tame, and a semigroup can admit more than one model. The main theorem
`m|c, e>=m/4 => W>=0` must not be silently promoted to an E theorem.

Outstanding audit: determine whether the entire first-layer-two class admits
tame models by an existing theorem or an immediate specialization. If so,
the new counting proof is an alternative proof/formalization of a known
consequence. If not, exhibit an infinite subfamily outside **all applicable
published E criteria**, rather than merely outside `|L|<=12`.

## Other recent and nearby results

1. Bacher, *Families of Eliahou semigroups linked to Farey intervals*,
   [arXiv:2604.25051v9](https://arxiv.org/html/2604.25051v9), 14 October 2026.
   Conjecture 2.7 is `gamma1<=m+6 => E>=0`; it is explicitly a conjecture.
   The candidate would address a restricted depth-four part, not the whole
   conjecture. Conjectures 2.5 and 2.8 are also not available theorems.
   Lemma 2.3 only gives monotonicity when newly added generators start at
   `c+m-gamma1`; at our parameters this is `4m-d`, not the whole terminal
   layer. The unconditional conductor search ends at 200. Its finite search
   does not prove an infinite first-layer-two result. The later structural
   theorems impose additional split/collision-free/Farey-class hypotheses;
   no unrestricted profile `(2,t,u)` result was located there.

2. Eliahou–Fromentin, *Near-misses in Wilf's conjecture*,
   [arXiv:1710.03623](https://arxiv.org/html/1710.03623), journal 2019.
   The paper constructs depth-four negative-E families and states a proposed
   universal lower bound as **Conjecture 4.2**, with a sharper structural
   **Conjecture 4.3**. These cannot be used as proved classifications of all
   negative-E profiles. The standard smallest counterexamples have
   `alpha1=2`, not our `alpha1=1`.

3. Almirón–Moyano-Fernández, *Eliahou number, Wilf function and concentration
   of a numerical semigroup*,
   [arXiv:2104.03793](https://arxiv.org/html/2104.03793), journal 2023.
   Theorem 4.4 gives an E criterion using the maximum consecutive-element
   gap `C`, not the initial gap `d`. Here the empty interval from `m+d` to
   `2m` forces `C>=m-d`. Consequently its sufficient condition
   `m/C^2>2` (at `c=4m`) does not hold under `m>12d`.
   Corollaries 5.3 and 5.4 require additional left-generator/cardinality
   inequalities; they are not consequences of our hypotheses. A family
   member may individually satisfy them.

4. Delgado–Kumar–Marion, *On counting numerical semigroups by maximum
   primitive and Wilf's conjecture*,
   [arXiv:2501.04417v3](https://arxiv.org/html/2501.04417v3), October 2026.
   Theorem 1.5 proves Wilf when `|S intersect (m,2m)|>=sqrt(2m)`;
   the older version used `sqrt(3m)`. Our count is one. This criterion does
   not apply, and its conclusion is W.

5. *Wilf's Conjecture from the First Kunz Layer*,
   [Preprints.org 202604.0551v1](https://www.preprints.org/manuscript/202604.0551),
   8 April 2026, explicitly not peer reviewed. Theorems 1.2 and 1.3 concern
   W under population/embedding-dimension inequalities. At our `eta=1`,
   the divisible-conductor mixed condition becomes `7e>=4m`.
   It does not assert `eta=1 => E>=0`. This source was checked because its
   title is close; its correctness was not independently audited.

6. Eliahou, *A graph-theoretic approach to Wilf's conjecture*,
   [EJCombin 27(2), P2.15](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v27i2p15/pdf/),
   2020, proves the large-embedding-dimension W criterion. Its graph methods
   precede the divset work. No unconditional `q=4,alpha1=1 => E>=0`
   statement was located; this is a scoped reading conclusion, not a proof
   that no such consequence exists.

## Publication wording and remaining checks

Safe current wording is: “We give an elementary proof and a formalization
candidate for a depth-four family. Its relation to existing divset criteria
is being checked.” Do not write “first proof”, “new theorem”, “solves Bacher's
conjecture”, or claim journal publishability at this stage.

Required next novelty checks are the divset applicability test above, a
comparison with the final 2025 Divsets text, and a citation search for papers
using Proposition 5.4 / first Apéry count one after that publication.
Searches included first layer, first level, profile `(2,t,u)`, `alpha1=1`,
depth four, two left generators, Eliahou number, concentration and divsets.
No-result searches are only search records; they do not certify originality.

For noncanonical cutoff versions, separately state what is proved. Existing
actual-conductor E theorems cannot automatically be applied to that altered
quantity. Conversely, a cutoff-relative extension alone should not be
marketed as a new result on the usual E invariant without explaining its
mathematical significance.
