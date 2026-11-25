# Lean proof of the depth-four theorem

The main result is `Eliahou.DepthFour.depth_four_nonneg`. It proves a uniform
inequality for arbitrary numerical semigroups satisfying the hypotheses below;
it is not a bounded enumeration certificate or a proof of the full Bacher
conjecture.

## Statement

Let `S` be an additively closed subset of the natural numbers containing zero,
with multiplicity `m`. Assume

- `0 < d < m` and `1 <= h <= m`;
- `S` intersected with the **unshifted** interval `[m, 2m)` is exactly
  `{m, m+d}`;
- every integer at least `c = 3m+h` belongs to `S`.

Write `L = S intersect [0,c)`, let `P` be the positive elements of `S` that
cannot be written as a sum of two positive elements of `S`, and let
`D = (S \ P) intersect [c,c+m)`. Then the theorem proves

```text
|P intersect L| * |L| - 4 * |D| + (m-h) >= 0.
```

The cutoff satisfies `3m < c <= 4m`, so its depth is four. It need not be the
least conductor. When it is the conductor, the displayed expression is the
usual Eliahou number. There is no upper bound on `m`, and `d` may be any
integer between `1` and `m-1`.

The exact Lean interface is:

```lean
theorem Eliahou.DepthFour.depth_four_nonneg {S : Set ℕ} {m d h : ℕ}
    (A : Eliahou.DepthFour.Admissible S m d h) :
    0 ≤ Eliahou.DepthFour.eliahou S m h
```

## Proof structure

The modules under `Eliahou/DepthFour/` define semigroup membership and additive
indecomposability, derive structural decompositions of the relevant intervals,
bound finite sumsets and overlaps, and compute the baseline counts in all
parameter ranges. `Main.lean` combines those bounds with integer inequalities.
The semantic sets are quantified over all natural numbers. The counting case
proofs apply to symbolic parameters, not just a list of tested semigroups.

`Audit.lean` prints the transitive axiom dependencies of the main theorem and
selected supporting declarations. `verify.py` requires an axiom report for
every requested declaration, explicitly including
`Eliahou.DepthFour.depth_four_nonneg`. It rejects any axiom outside
`propext`, `Classical.choice`, and `Quot.sound`; declarations using no axioms
also pass. Thus a successful build alone does not satisfy the verification
command. The scripts do not establish mathematical novelty.

## Pinned dependencies

- Lean **4.36.0**, selected by `lean-toolchain`.
- Mathlib **4.36.0**, commit
  `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.
- `source-lock.json` records Mathlib and its eight dependency revisions.
  Official source snapshots are restored under ignored `Bootstrap/sources/`.
  Lake uses relative paths to those snapshots.

The initial foundation modules use Lean's bundled Std. The general theorem
uses Mathlib. The cache helper requests only the dependency closures of its
listed imports, including finite sets, natural-number intervals, and
`Mathlib.Tactic.Linarith`.

## Reproduce

Install Python **3.12 or newer**, elan, and the GitHub CLI. Authenticate `gh`
with `gh auth login`, or supply `GH_TOKEN` through your environment. From this
directory on Linux or macOS, with `lake` on `PATH`, run:

```sh
elan toolchain install leanprover/lean4:v4.36.0
python bootstrap_mathlib.py
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build cache
lake env python cache_mathlib.py
python verify.py --json .lake/verification.json
```

The source bootstrap uses GitHub API archives, so it does not require Git HTTPS
cloning. The cache helper invokes the official Mathlib cache tool and mirrors
cached dependency artifacts to the snapshot paths used by this project.

On Windows, after installing the same prerequisites, run:

```powershell
elan toolchain install leanprover/lean4:v4.36.0
.\fetch_mathlib_cache.ps1
.\verify.ps1 --json .lake/verification.json
```

On the original Windows machine the helpers automatically prefer the isolated
elan installation at `.tools/elan/`; otherwise they use `lake` from `PATH`.
`verify.ps1` delegates to the same Python verifier used by the Linux CI template. The
verifier runs `lake build`, then `lake env lean Audit.lean`, prints their
output, and returns a nonzero exit code on a build or audit failure. Its
optional JSON report records the stage exit codes and individual axiom lists.
The verification script may also be invoked by absolute path from another
working directory.

The optional `../ci/verify.yml` template repeats the pinned setup and verifier
on Linux with read-only repository permissions. Copy it to
`.github/workflows/verify.yml` to enable it. It is not active in this release;
the included verification report records the local Windows build.
The template has no publication step.
Toolchains, downloaded archives, and generated build files are not versioned.

## Supplementary foundations and examples

The older `Presentation` representation describes a finite prefix followed by
an infinite tail. Its validity theorem proves zero membership, additive
closure on all natural numbers, and cofiniteness. Its Boolean primitive test
is proved equivalent to positive membership and additive indecomposability.
The cutoff in this representation is not assumed to be the least conductor.

`Examples.lean` checks two known infinite prefix-plus-tail sets, their
multiplicities, counts, and negative Eliahou values. These are baseline checks,
not new counterexamples to the main theorem. Equality with the corresponding
original generator descriptions has not been formalized. Their concrete
certificates use kernel reduction, not `native_decide`.

`CutoffStep.lean` proves algebraic difference formulas and sign consequences.
It does not prove the semigroup counting transitions needed for a complete
semantic cutoff-monotonicity theorem. These supplementary limitations do not
change the statement or dependencies of `depth_four_nonneg`.
