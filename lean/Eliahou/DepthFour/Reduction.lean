import Eliahou.DepthFour.Semantics
import Eliahou.DepthFour.Arithmetic

/-! The complete reduction from an admissible semigroup to the six-parameter
integer core.  Every numerical premise is obtained from semantic counts. -/

namespace Eliahou.DepthFour

open Finset

variable {S : Set ℕ} {m d h : ℕ}

theorem six_le_card_baseLeft (A : Admissible S m d h) :
    6 ≤ (baseLeft m d h).card := by
  classical
  have hm := A.m_pos
  have hd := A.d_pos
  have hdm := A.d_lt_m
  have hh := A.h_pos
  let F : Finset ℕ := {0, m, m + d, 2 * m, 2 * m + d, 3 * m}
  have hsub : F ⊆ baseLeft m d h := by
    intro n hn
    simp only [F, mem_insert, mem_singleton] at hn
    apply mem_filter.mpr
    constructor
    · apply mem_range.mpr
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
      · exact base_zero
      · exact base_m
      · exact base_second
      · exact ⟨2, 0, by simp⟩
      · exact ⟨1, 1, by simp; omega⟩
      · exact ⟨3, 0, by simp⟩
  have hcard : F.card = 6 := by
    simp (disch := (simp only [mem_insert, mem_singleton]; omega))
      only [F, card_insert_of_notMem, card_singleton]
  simpa only [hcard] using card_le_card hsub

/-- The unproved part of the main theorem is now solely nonnegativity of
`core`; the contribution of all final primitives is already controlled. -/
theorem core_le_eliahou (A : Admissible S m d h) :
    core ((baseLeft m d h).card : ℤ) ((baseRight m d h).card : ℤ)
      ((m : ℤ) - h) ((middleOffsets S m h).card : ℤ)
      ((thirdOffsets S m d h).card : ℤ)
      (((lowShifts (middleOffsets S m h) d h).card : ℤ) +
        ((highIndices (middleOffsets S m h) d h).card : ℤ)) +
      ((terminalPrims S m h).card : ℤ) ^ 2 ≤ eliahou S m h := by
  have hk : ((left S m h).card : ℤ) = ((baseLeft m d h).card : ℤ) +
      ((middleOffsets S m h).card : ℤ) + ((thirdOffsets S m d h).card : ℤ) +
      ((terminalPrims S m h).card : ℤ) := by
    exact_mod_cast card_left_offsets A
  have hell : ((leftPrims S m h).card : ℤ) = 2 +
      ((middleOffsets S m h).card : ℤ) + ((terminalPrims S m h).card : ℤ) := by
    exact_mod_cast card_leftPrims_offsets A
  have hs : 2 * ((rightDecomp S m h).card : ℤ) ≤
      2 * ((baseRight m d h).card : ℤ) +
      2 * (((lowShifts (middleOffsets S m h) d h).card : ℤ) +
        ((highIndices (middleOffsets S m h) d h).card : ℤ)) +
      ((middleOffsets S m h).card : ℤ) * (((middleOffsets S m h).card : ℤ) + 1) +
      4 * ((terminalPrims S m h).card : ℤ) := by
    exact_mod_cast twice_card_rightDecomp_le A
  have hk₀ : (6 : ℤ) ≤ ((baseLeft m d h).card : ℤ) := by
    exact_mod_cast six_le_card_baseLeft A
  exact terminal_core_bound hk hell hs hk₀ (Int.natCast_nonneg _)
    (Int.natCast_nonneg _) (Int.natCast_nonneg _)

theorem eliahou_nonneg_of_core (A : Admissible S m d h)
    (hc : 0 ≤ core ((baseLeft m d h).card : ℤ) ((baseRight m d h).card : ℤ)
      ((m : ℤ) - h) ((middleOffsets S m h).card : ℤ)
      ((thirdOffsets S m d h).card : ℤ)
      (((lowShifts (middleOffsets S m h) d h).card : ℤ) +
        ((highIndices (middleOffsets S m h) d h).card : ℤ))) :
    0 ≤ eliahou S m h := by
  have hb := core_le_eliahou A
  have hu := sq_nonneg (((terminalPrims S m h).card : ℤ))
  omega

end Eliahou.DepthFour
