# Eliahou nonnegativity at depth four

**Author: Zhengyi Liu.** A complete symbolic proof and Lean 4 formalization.

If a numerical semigroup has multiplicity \(m\), conductor \(3m<c\le4m\),
and exactly two elements in \([m,2m)\), its Eliahou number is nonnegative.
The proof permits every gap between the two elements and arbitrarily many
higher primitive elements. It also works at a specified cutoff containing
the entire tail, without assuming that cutoff is the least conductor.

- [Paper (PDF)](output/pdf/eliahou-depth-four.pdf)
- [LaTeX source](paper/main.tex)
- [Main Lean theorem](lean/Eliahou/DepthFour/Main.lean)
- [Build instructions](lean/README.md)
- [Literature comparison](notes/literature-review.md)

This does **not** solve the full Wilf conjecture or Bacher's general small-gap
conjecture. The result is an infinite-family theorem, not a finite enumeration
certificate. The literature comparison identifies an explicit infinite family
outside the hypotheses of the inspected sufficient conditions; it does not
certify absolute originality or guarantee publication. AI assistance is
disclosed in the paper.

## What Lean proves

The declaration is:

~~~lean
Eliahou.DepthFour.depth_four_nonneg
  (A : Admissible S m d h) : 0 ≤ eliahou S m h
~~~

Here the cutoff is \(3m+h\), with \(1\le h\le m\).
Admissible contains only the mathematical hypotheses: zero membership,
additive closure, the multiplicity condition, the exact first interval
{m, m+d}, and the full tail starting at the cutoff.
It does not assume a counting inequality, a decomposition theorem, or the
desired conclusion.

The development proves the element classifications, cardinality formulas,
sumset bounds, all parameter cases, and the final inequality. The final theorem
uses only propext, Classical.choice, and Quot.sound, the ordinary Lean
foundational axioms. It has no placeholder proof, custom axiom, or external
computation oracle in its dependency closure.

## Reproduce the proof

Lean 4.36.0 and a fixed Mathlib revision are pinned. Install elan, Python 3.12
or newer, and the GitHub CLI, then follow [lean/README.md](lean/README.md)
to restore the exact source snapshots and their official compiled caches.

On Windows:

~~~powershell
cd lean
.\fetch_mathlib_cache.ps1
python verify.py
~~~

The verifier builds the complete development and checks the axiom report,
including an explicit requirement that the main theorem was audited.
The optional [CI template](ci/verify.yml) performs the corresponding build on
Linux when installed as .github/workflows/verify.yml. It is not active in this
release; the included verification evidence is from the local Windows build.

To rebuild the paper from the repository root:

~~~sh
pdflatex -interaction=nonstopmode -halt-on-error -jobname=eliahou-depth-four -output-directory=output/pdf paper/main.tex
pdflatex -interaction=nonstopmode -halt-on-error -jobname=eliahou-depth-four -output-directory=output/pdf paper/main.tex
~~~

## Proof organization

| Module | Role |
|---|---|
| Defs | Semigroup hypotheses, primitives, finite counts, signed invariant |
| Semantics | Exact left-element classification and threshold coverage |
| Shifts | Truncated-translation cardinality estimates |
| PairSums | Unordered two-summand bound |
| BaseCounts, BaseLarge | Counts for the two-generator base in all ranges |
| Offsets | The single-collision alternatives and deficient cases |
| Arithmetic, Reduction | Integer inequalities and the semantic bridge |
| Main | The complete theorem |

## Earlier exploration

The Python experiments and older Lean examples are retained for transparency.
They helped select the problem and reproduce known negative examples; they
are not used in the proof of the main theorem.

~~~sh
python -m pip install -r requirements-dev.txt
python -m pytest -q
~~~

The older restricted notes record exploratory arguments. Only the complete
theorem above is claimed as fully formalized; the older algebra-only cutoff
lemmas are not a semantic formalization of cutoff monotonicity. The latest
readable uniform proof is in
[notes/q4-first-layer-two.md](notes/q4-first-layer-two.md).

## 中文说明

本项目证明的是一个无限族：导子位于 \(3m<c\le4m\)，且第一段
\([m,2m)\) 恰有两个元素的数值半群，其 Eliahou 数非负。这里 \(m\)
是最小正元素，导子是“从此以后所有整数都在半群里”的最小起点。

这是结构性证明，参数不设有限上限。论文给出可读推导，Lean 从半群定义
检查到最终结论。它尚不覆盖任意深度或第一段含更多元素的情形。
文献比较和数学正确性是两个不同问题；Lean 不判断论文是否首次提出结果。
