import Mathlib.Tactic.Linarith

/-! Integer inequalities used after the semantic finite-set counts.
These are intermediate lemmas, not the semigroup theorem on their own.
-/

namespace Eliahou.DepthFour

def core (k₀ s₀ ρ t v w : ℤ) : ℤ :=
  (2 + t) * (k₀ + t + v) - 4 * s₀ - 4 * w - 2 * t * (t + 1) + ρ

theorem core_expand (k₀ s₀ ρ t v w : ℤ) :
    core k₀ s₀ ρ t v w =
      (2 * k₀ - 4 * s₀ + ρ) + (k₀ + 2) * t + (t + 2) * (v - t) - 4 * w := by
  unfold core
  nlinarith

theorem terminal_core_bound {k k₀ ell s s₀ ρ t v w u : ℤ}
    (hk : k = k₀ + t + v + u) (hell : ell = 2 + t + u)
    (hs : 2 * s ≤ 2 * s₀ + 2 * w + t * (t + 1) + 4 * u)
    (hk₀ : 6 ≤ k₀) (ht : 0 ≤ t) (hv : 0 ≤ v) (hu : 0 ≤ u) :
    core k₀ s₀ ρ t v w + u ^ 2 ≤ ell * k - 4 * s + ρ := by
  have hp : 0 ≤ u * (k₀ + 2 * t + v - 6) :=
    mul_nonneg hu (by omega)
  unfold core
  nlinarith

theorem core_low {k₀ s₀ ρ t v w : ℤ}
    (hk₀ : 6 ≤ k₀) (he : 0 ≤ 2 * k₀ - 4 * s₀ + ρ)
    (ht : 0 ≤ t) (hv : t ≤ v) (hw : w ≤ 2 * t) :
    0 ≤ core k₀ s₀ ρ t v w := by
  rw [core_expand]
  have h₁ := mul_nonneg (show 0 ≤ k₀ - 6 by omega) ht
  have h₂ := mul_nonneg (show 0 ≤ t + 2 by omega) (show 0 ≤ v - t by omega)
  nlinarith

theorem core_ten_regular {s₀ ρ t v w : ℤ}
    (he : 0 ≤ 20 - 4 * s₀ + ρ) (ht : 0 ≤ t)
    (hv : t ≤ v) (hw : w ≤ 3 * t) :
    0 ≤ core 10 s₀ ρ t v w := by
  rw [core_expand]
  have hp := mul_nonneg (show 0 ≤ t + 2 by omega) (show 0 ≤ v - t by omega)
  nlinarith

theorem core_ten_deficient {s₀ ρ t v w : ℤ}
    (he : 0 ≤ 20 - 4 * s₀ + ρ) (ht : 1 ≤ t)
    (hv : v = t - 1) (hw : w ≤ 2 * t) :
    0 ≤ core 10 s₀ ρ t v w := by
  rw [core_expand]
  nlinarith

theorem core_nine {s₀ ρ t v w β : ℤ}
    (he : 2 ≤ 18 - 4 * s₀ + ρ) (ht : 0 ≤ t)
    (hβ : 0 ≤ β) (hβt : β ≤ t) (hv : v = t + β)
    (hw : w ≤ 2 * t + 2 * β) :
    0 ≤ core 9 s₀ ρ t v w := by
  rw [core_expand]
  by_cases hlarge : 6 ≤ t
  · have hp := mul_nonneg (show 0 ≤ t - 6 by omega) hβ
    nlinarith
  · have hp := mul_nonneg (show 0 ≤ 6 - t by omega) (show 0 ≤ t - β by omega)
    have hpoly : 0 ≤ (t - 1) * (t - 2) := by
      by_cases hsmall : t ≤ 1
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact mul_nonneg (by omega) (by omega)
    nlinarith

theorem core_seven_deficient {s₀ ρ t v w : ℤ}
    (he : 2 ≤ 14 - 4 * s₀ + ρ)
    (hv : v = t - 1) (hw : w ≤ 2 * t) :
    0 ≤ core 7 s₀ ρ t v w := by
  rw [core_expand, hv]
  nlinarith

theorem core_eight_deficient {s₀ ρ t v w : ℤ}
    (he : 0 ≤ 16 - 4 * s₀ + ρ) (ht : 2 ≤ t)
    (hv : v = t - 1) (hw : w ≤ 2 * t) :
    0 ≤ core 8 s₀ ρ t v w := by
  rw [core_expand]
  nlinarith

theorem core_eight_deficient_slack {s₀ ρ t v w : ℤ}
    (he : 2 ≤ 16 - 4 * s₀ + ρ) (ht : 0 ≤ t)
    (hv : v = t - 1) (hw : w ≤ 2 * t) :
    0 ≤ core 8 s₀ ρ t v w := by
  rw [core_expand]
  nlinarith

end Eliahou.DepthFour
