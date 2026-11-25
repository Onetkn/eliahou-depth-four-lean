import Eliahou.DepthFour.Semantics
import Eliahou.DepthFour.BaseCounts

namespace Eliahou.DepthFour

open Finset

variable {S : Set ℕ} {m d h : ℕ}

noncomputable section
open Classical

theorem middle_shiftUnion_properties (A : Admissible S m d h) {x : ℕ}
    (hx : x ∈ shiftUnion (middleOffsets S m h) d h) :
    x < h ∧ x ≠ 0 ∧ x ≠ d ∧ x ≠ 2 * d := by
  rcases mem_union.mp hx with hx | hx
  · exact ⟨middleOffsets_lt hx, middleOffsets_exclusions A hx⟩
  · obtain ⟨j, hj, hjh, rfl⟩ := mem_shiftBelow.mp hx
    have hje := middleOffsets_exclusions A hj
    have hd := A.d_pos
    exact ⟨hjh, by omega, by omega, by omega⟩

theorem base_on_middle_shift_small (A : Admissible S m d h)
    (hdm : 2 * d < m) {x : ℕ}
    (hx : x ∈ shiftUnion (middleOffsets S m h) d h) :
    Base m d (3 * m + x) ↔ x = 3 * d := by
  have hp := middle_shiftUnion_properties A hx
  have hm := A.m_pos
  have hd := A.d_pos
  have hdm' := A.d_lt_m
  have hh := A.h_le_m
  rw [base_lt_four_iff hm (by omega)]
  simp only [baseSmall, mem_insert, mem_singleton]
  omega

theorem not_base_on_middle_shift_half (A : Admissible S m d h)
    (hdm : 2 * d = m) {x : ℕ}
    (hx : x ∈ shiftUnion (middleOffsets S m h) d h) :
    ¬ Base m d (3 * m + x) := by
  have hp := middle_shiftUnion_properties A hx
  have hm := A.m_pos
  have hd := A.d_pos
  have hh := A.h_le_m
  rw [base_lt_four_iff hm (by omega)]
  simp only [baseSmall, mem_insert, mem_singleton]
  omega

theorem base_on_middle_shift_large (A : Admissible S m d h)
    (hdm : m < 2 * d) {x : ℕ}
    (hx : x ∈ shiftUnion (middleOffsets S m h) d h) :
    Base m d (3 * m + x) ↔ x = 2 * d - m := by
  have hp := middle_shiftUnion_properties A hx
  have hm := A.m_pos
  have hd := A.d_pos
  have hdm' := A.d_lt_m
  have hh := A.h_le_m
  rw [base_lt_four_iff hm (by omega)]
  simp only [baseSmall, mem_insert, mem_singleton]
  omega

theorem thirdOffsets_eq_erase_small (A : Admissible S m d h)
    (hdm : 2 * d < m) :
    thirdOffsets S m d h =
      (shiftUnion (middleOffsets S m h) d h).erase (3 * d) := by
  ext x
  simp only [thirdOffsets, mem_filter, mem_erase]
  constructor
  · rintro ⟨hx, hnb⟩
    exact ⟨fun he => hnb ((base_on_middle_shift_small A hdm hx).mpr he), hx⟩
  · rintro ⟨hne, hx⟩
    exact ⟨hx, fun hb => hne ((base_on_middle_shift_small A hdm hx).mp hb)⟩

theorem thirdOffsets_eq_union_small (A : Admissible S m d h)
    (hdm : 2 * d < m) (hh : h ≤ 3 * d) :
    thirdOffsets S m d h = shiftUnion (middleOffsets S m h) d h := by
  rw [thirdOffsets_eq_erase_small A hdm]
  apply erase_eq_of_notMem
  intro hx
  have := (middle_shiftUnion_properties A hx).1
  omega

theorem thirdOffsets_eq_union_half (A : Admissible S m d h)
    (hdm : 2 * d = m) :
    thirdOffsets S m d h = shiftUnion (middleOffsets S m h) d h := by
  ext x
  simp only [thirdOffsets, mem_filter]
  exact ⟨And.left, fun hx => ⟨hx, not_base_on_middle_shift_half A hdm hx⟩⟩

theorem thirdOffsets_eq_erase_large (A : Admissible S m d h)
    (hdm : m < 2 * d) :
    thirdOffsets S m d h =
      (shiftUnion (middleOffsets S m h) d h).erase (2 * d - m) := by
  ext x
  simp only [thirdOffsets, mem_filter, mem_erase]
  constructor
  · rintro ⟨hx, hnb⟩
    exact ⟨fun he => hnb ((base_on_middle_shift_large A hdm hx).mpr he), hx⟩
  · rintro ⟨hne, hx⟩
    exact ⟨hx, fun hb => hne ((base_on_middle_shift_large A hdm hx).mp hb)⟩

theorem card_thirdOffsets_small (A : Admissible S m d h)
    (hdm : 2 * d < m) (hh : h ≤ 3 * d) :
    (thirdOffsets S m d h).card =
      (middleOffsets S m h).card + shiftBeta (middleOffsets S m h) d h := by
  rw [thirdOffsets_eq_union_small A hdm hh, card_shiftUnion]

theorem card_thirdOffsets_half (A : Admissible S m d h)
    (hdm : 2 * d = m) :
    (thirdOffsets S m d h).card =
      (middleOffsets S m h).card + shiftBeta (middleOffsets S m h) d h := by
  rw [thirdOffsets_eq_union_half A hdm, card_shiftUnion]

/-- A one-element deletion defect has exactly size one, and forces closure. -/
theorem shiftUnion_erase_defect_card (J : Finset ℕ) (d h collision : ℕ)
    (hdefect : ((shiftUnion J d h).erase collision).card < J.card) :
    ((shiftUnion J d h).erase collision).card + 1 = J.card ∧
      shiftBelow J d h ⊆ J ∧ collision ∈ J := by
  obtain ⟨hclosed, hmem⟩ := erased_shiftUnion_defect J d h collision hdefect
  have hU : shiftUnion J d h = J := union_eq_left.mpr hclosed
  refine ⟨?_, hclosed, hmem⟩
  rw [hU]
  exact card_erase_add_one hmem

theorem thirdOffsets_defect_small (A : Admissible S m d h)
    (hdm : 2 * d < m)
    (hdefect : (thirdOffsets S m d h).card < (middleOffsets S m h).card) :
    (thirdOffsets S m d h).card + 1 = (middleOffsets S m h).card ∧
      shiftBelow (middleOffsets S m h) d h ⊆ middleOffsets S m h ∧
      3 * d ∈ middleOffsets S m h := by
  rw [thirdOffsets_eq_erase_small A hdm] at hdefect ⊢
  exact shiftUnion_erase_defect_card _ _ _ _ hdefect

theorem thirdOffsets_defect_large (A : Admissible S m d h)
    (hdm : m < 2 * d)
    (hdefect : (thirdOffsets S m d h).card < (middleOffsets S m h).card) :
    (thirdOffsets S m d h).card + 1 = (middleOffsets S m h).card ∧
      shiftBelow (middleOffsets S m h) d h ⊆ middleOffsets S m h ∧
      2 * d - m ∈ middleOffsets S m h := by
  rw [thirdOffsets_eq_erase_large A hdm] at hdefect ⊢
  exact shiftUnion_erase_defect_card _ _ _ _ hdefect

theorem large_defect_two_le_card (A : Admissible S m d h)
    (hdm : m < 2 * d) (hrh : 3 * d - m < h)
    (hdefect : (thirdOffsets S m d h).card < (middleOffsets S m h).card) :
    2 ≤ (middleOffsets S m h).card := by
  obtain ⟨_, hclosed, hz⟩ := thirdOffsets_defect_large A hdm hdefect
  have hr : 3 * d - m ∈ middleOffsets S m h :=
    hclosed (mem_shiftBelow.mpr ⟨2 * d - m, hz, by omega, by omega⟩)
  have hne : 2 * d - m ≠ 3 * d - m := by have := A.d_pos; omega
  have hc := one_lt_card.mpr ⟨2 * d - m, hz, 3 * d - m, hr, hne⟩
  omega

end
end Eliahou.DepthFour
