import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace Eliahou.DepthFour

open Finset

/-- Translation by `d`, retaining only values strictly below `h`. -/
def shiftBelow (J : Finset ℕ) (d h : ℕ) : Finset ℕ :=
  (J.filter fun j => j + d < h).image fun j => j + d

def shiftUnion (J : Finset ℕ) (d h : ℕ) : Finset ℕ :=
  J ∪ shiftBelow J d h

def shiftBeta (J : Finset ℕ) (d h : ℕ) : ℕ :=
  (shiftBelow J d h \ J).card

def lowShifts (J : Finset ℕ) (d h : ℕ) : Finset ℕ :=
  shiftUnion J d h ∪ shiftBelow J (2 * d) h

/-- The indices whose first translate reaches the upper part. -/
def highIndices (J : Finset ℕ) (d h : ℕ) : Finset ℕ :=
  J.filter fun j => h ≤ j + d

@[simp] theorem mem_shiftBelow {J : Finset ℕ} {d h x : ℕ} :
    x ∈ shiftBelow J d h ↔ ∃ j ∈ J, j + d < h ∧ j + d = x := by
  simp only [shiftBelow, mem_image, mem_filter]
  constructor
  · rintro ⟨j, ⟨hj, hjh⟩, hjx⟩
    exact ⟨j, hj, hjh, hjx⟩
  · rintro ⟨j, hj, hjh, hjx⟩
    exact ⟨j, ⟨hj, hjh⟩, hjx⟩

theorem shiftBelow_eq_filter_image (J : Finset ℕ) (d h : ℕ) :
    shiftBelow J d h = (J.image (fun j => j + d)).filter (fun x => x < h) := by
  ext x
  simp only [mem_shiftBelow, mem_filter, mem_image]
  constructor
  · rintro ⟨j, hj, hjh, rfl⟩
    exact ⟨⟨j, hj, rfl⟩, hjh⟩
  · rintro ⟨⟨j, hj, rfl⟩, hjh⟩
    exact ⟨j, hj, hjh, rfl⟩

theorem card_shiftBelow (J : Finset ℕ) (d h : ℕ) :
    (shiftBelow J d h).card = (J.filter fun j => j + d < h).card := by
  apply card_image_of_injective
  intro x y hxy
  exact Nat.add_right_cancel hxy

theorem card_shiftBelow_le (J : Finset ℕ) (d h : ℕ) :
    (shiftBelow J d h).card ≤ J.card := by
  rw [card_shiftBelow]
  exact card_filter_le _ _

theorem card_highIndices_le (J : Finset ℕ) (d h : ℕ) :
    (highIndices J d h).card ≤ J.card :=
  card_filter_le _ _

theorem card_shiftBelow_add_high (J : Finset ℕ) (d h : ℕ) :
    (shiftBelow J d h).card + (highIndices J d h).card = J.card := by
  rw [card_shiftBelow]
  simpa only [highIndices, not_lt] using
    (card_filter_add_card_filter_not (s := J) fun j => j + d < h)

theorem card_shiftUnion (J : Finset ℕ) (d h : ℕ) :
    (shiftUnion J d h).card = J.card + shiftBeta J d h := by
  have hc := card_sdiff_add_card (shiftBelow J d h) J
  simpa only [shiftUnion, shiftBeta, union_comm, Nat.add_comm] using hc.symm

theorem shiftBeta_le (J : Finset ℕ) (d h : ℕ) :
    shiftBeta J d h ≤ J.card := by
  exact (card_le_card sdiff_subset).trans (card_shiftBelow_le J d h)

theorem card_secondShift_le (J : Finset ℕ) (d h : ℕ) :
    (shiftBelow J (2 * d) h).card ≤ (shiftBelow J d h).card := by
  rw [card_shiftBelow, card_shiftBelow]
  apply card_le_card
  intro j hj
  simp only [mem_filter] at hj ⊢
  exact ⟨hj.1, by omega⟩

/-- A second translate either is a first translate or comes from a new first translate. -/
theorem secondShift_subset (J : Finset ℕ) (d h : ℕ) :
    shiftBelow J (2 * d) h ⊆ shiftBelow J d h ∪
      (shiftBelow J d h \ J).image (fun j => j + d) := by
  intro x hx
  obtain ⟨j, hj, hjh, rfl⟩ := mem_shiftBelow.mp hx
  have hmid : j + d ∈ shiftBelow J d h :=
    mem_shiftBelow.mpr ⟨j, hj, by omega, rfl⟩
  by_cases hjd : j + d ∈ J
  · apply mem_union_left
    exact mem_shiftBelow.mpr ⟨j + d, hjd, by omega, by omega⟩
  · apply mem_union_right
    exact mem_image.mpr ⟨j + d, mem_sdiff.mpr ⟨hmid, hjd⟩, by omega⟩

theorem card_lowShifts_le_beta (J : Finset ℕ) (d h : ℕ) :
    (lowShifts J d h).card ≤ J.card + 2 * shiftBeta J d h := by
  have hs : lowShifts J d h ⊆ shiftUnion J d h ∪
      (shiftBelow J d h \ J).image (fun j => j + d) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact mem_union_left _ hx
    · rcases mem_union.mp (secondShift_subset J d h hx) with hp | hp
      · exact mem_union_left _ (mem_union_right _ hp)
      · exact mem_union_right _ hp
  have hcard := (card_le_card hs).trans (card_union_le _ _)
  have himage : ((shiftBelow J d h \ J).image (fun j => j + d)).card ≤
      shiftBeta J d h := card_image_le
  have hu := card_shiftUnion J d h
  omega

theorem card_lowShifts_add_high_le_three (J : Finset ℕ) (d h : ℕ) :
    (lowShifts J d h).card + (highIndices J d h).card ≤ 3 * J.card := by
  have hlow := card_union_le (shiftUnion J d h) (shiftBelow J (2 * d) h)
  have hu := card_union_le J (shiftBelow J d h)
  have hsecond := card_secondShift_le J d h
  have hfirst := card_shiftBelow_le J d h
  have hpartition := card_shiftBelow_add_high J d h
  change (lowShifts J d h).card ≤
    (shiftUnion J d h).card + (shiftBelow J (2 * d) h).card at hlow
  change (shiftUnion J d h).card ≤ J.card + (shiftBelow J d h).card at hu
  omega

theorem secondShift_eq_empty (J : Finset ℕ) (d h : ℕ) (hh : h ≤ 2 * d) :
    shiftBelow J (2 * d) h = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨j, _, hjh, _⟩ := mem_shiftBelow.mp hx
  omega

theorem card_lowShifts_add_high_le_two_of_small (J : Finset ℕ) (d h : ℕ)
    (hh : h ≤ 2 * d) :
    (lowShifts J d h).card + (highIndices J d h).card ≤ 2 * J.card := by
  have hlow : lowShifts J d h = shiftUnion J d h := by
    simp only [lowShifts, secondShift_eq_empty J d h hh, union_empty]
  have hu := card_union_le J (shiftBelow J d h)
  have hpartition := card_shiftBelow_add_high J d h
  change (shiftUnion J d h).card ≤ J.card + (shiftBelow J d h).card at hu
  rw [hlow]
  omega

theorem card_lowShifts_add_high_le_beta (J : Finset ℕ) (d h : ℕ) :
    (lowShifts J d h).card + (highIndices J d h).card ≤
      2 * J.card + 2 * shiftBeta J d h := by
  have hlow := card_lowShifts_le_beta J d h
  have hhigh := card_highIndices_le J d h
  omega

theorem lowShifts_eq_of_closed (J : Finset ℕ) (d h : ℕ)
    (hclosed : shiftBelow J d h ⊆ J) : lowShifts J d h = J := by
  apply Subset.antisymm
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact union_subset (Subset.refl _) hclosed hx
    · obtain ⟨j, hj, hjh, rfl⟩ := mem_shiftBelow.mp hx
      have hjd : j + d ∈ J :=
        hclosed (mem_shiftBelow.mpr ⟨j, hj, by omega, rfl⟩)
      exact hclosed (mem_shiftBelow.mpr ⟨j + d, hjd, by omega, by omega⟩)
  · intro x hx
    exact mem_union_left _ (mem_union_left _ hx)

theorem card_lowShifts_add_high_le_two_of_closed (J : Finset ℕ) (d h : ℕ)
    (hclosed : shiftBelow J d h ⊆ J) :
    (lowShifts J d h).card + (highIndices J d h).card ≤ 2 * J.card := by
  rw [lowShifts_eq_of_closed J d h hclosed]
  have hhigh := card_highIndices_le J d h
  omega

/-- The low and high parts may be translated by unrelated maps. -/
theorem card_low_high_images_le (J : Finset ℕ) (d h : ℕ) (f g : ℕ → ℕ) :
    ((lowShifts J d h).image f ∪ (highIndices J d h).image g).card ≤
      (lowShifts J d h).card + (highIndices J d h).card := by
  exact (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)

/-- Erasing one collision can decrease the union below `|J|` only if it was closed. -/
theorem erased_shiftUnion_defect (J : Finset ℕ) (d h collision : ℕ)
    (hdefect : ((shiftUnion J d h).erase collision).card < J.card) :
    shiftBelow J d h ⊆ J ∧ collision ∈ J := by
  have hJU : J ⊆ shiftUnion J d h := subset_union_left
  have hcard := card_le_card hJU
  have hmem : collision ∈ shiftUnion J d h := by
    by_contra hnot
    rw [erase_eq_of_notMem hnot] at hdefect
    omega
  have herase := card_erase_add_one hmem
  have hEq : J = shiftUnion J d h := eq_of_subset_of_card_le hJU (by omega)
  constructor
  · intro x hx
    rw [hEq]
    exact mem_union_right _ hx
  · rw [hEq]
    exact hmem

end Eliahou.DepthFour
