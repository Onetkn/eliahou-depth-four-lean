import Eliahou.DepthFour.Defs
import Eliahou.DepthFour.Shifts
import Eliahou.DepthFour.PairSums
import Lean.Elab.Tactic.Omega

/-! Intrinsic semigroup semantics for the depth-four counting argument.
No counting identities or generation hypotheses are assumed here. -/

namespace Eliahou.DepthFour

open Finset

variable {S : Set ℕ} {m d h : ℕ}

theorem Admissible.mem_m (A : Admissible S m d h) : m ∈ S :=
  (A.first m (by omega) (by have := A.m_pos; omega)).2 (Or.inl rfl)

theorem Admissible.mem_second (A : Admissible S m d h) : m + d ∈ S :=
  (A.first (m + d) (by omega) (by have := A.d_lt_m; omega)).2 (Or.inr rfl)

theorem Admissible.mul_mem (A : Admissible S m d h) {x : ℕ}
    (hx : x ∈ S) (i : ℕ) : i * x ∈ S := by
  induction i with
  | zero => simpa using A.zero_mem
  | succ i ih => simpa [Nat.succ_mul] using A.add_mem (i * x) x ih hx

theorem base_zero : Base m d 0 := ⟨0, 0, by simp⟩

theorem base_m : Base m d m := ⟨1, 0, by simp⟩

theorem base_second : Base m d (m + d) := ⟨0, 1, by simp⟩

theorem base_add {x y : ℕ} (hx : Base m d x) (hy : Base m d y) :
    Base m d (x + y) := by
  rcases hx with ⟨i, j, rfl⟩
  rcases hy with ⟨i', j', rfl⟩
  refine ⟨i + i', j + j', ?_⟩
  simp only [Nat.add_mul]
  omega

theorem Admissible.base_mem (A : Admissible S m d h) {n : ℕ}
    (hn : Base m d n) : n ∈ S := by
  rcases hn with ⟨i, j, rfl⟩
  exact A.add_mem _ _ (A.mul_mem A.mem_m i) (A.mul_mem A.mem_second j)

theorem primitive_or_decomposable {n : ℕ} (hn : n ∈ S) (hp : 0 < n) :
    Primitive S n ∨ Decomposable S n := by
  classical
  by_cases hd : Decomposable S n
  · exact Or.inr hd
  · exact Or.inl ⟨hn, hp, hd⟩

/-- Every member has a finite expression as a sum of intrinsic primitives. -/
theorem primitive_sum {n : ℕ} (hn : n ∈ S) :
    ∃ l : List ℕ, (∀ x ∈ l, Primitive S x) ∧ l.sum = n := by
  classical
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n
      exact ⟨[], by simp, rfl⟩
    · have hp : 0 < n := by omega
      rcases primitive_or_decomposable hn hp with hprim | hdec
      · exact ⟨[n], by simpa using hprim, by simp⟩
      · rcases hdec with ⟨x, hx, y, hy, hxp, hyp, hxy⟩
        obtain ⟨lx, hlx, hsx⟩ := ih x (by omega) hx
        obtain ⟨ly, hly, hsy⟩ := ih y (by omega) hy
        refine ⟨lx ++ ly, ?_, ?_⟩
        · intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hlx a ha
          · exact hly a ha
        · simp only [List.sum_append, hsx, hsy, hxy]

theorem Admissible.primitive_of_first (A : Admissible S m d h)
    {n : ℕ} (hn : n ∈ S) (hp : 0 < n) (hu : n < 2 * m) : Primitive S n := by
  refine ⟨hn, hp, ?_⟩
  rintro ⟨x, hx, y, hy, hxp, hyp, hxy⟩
  have := A.lower x hx hxp
  have := A.lower y hy hyp
  omega

theorem Admissible.primitive_m (A : Admissible S m d h) : Primitive S m :=
  A.primitive_of_first A.mem_m A.m_pos (by have := A.m_pos; omega)

theorem Admissible.primitive_second (A : Admissible S m d h) :
    Primitive S (m + d) :=
  A.primitive_of_first A.mem_second (by have := A.m_pos; omega)
    (by have := A.d_lt_m; omega)

theorem Admissible.base_decomposable (A : Admissible S m d h)
    {n : ℕ} (hb : Base m d n) (hn : 2 * m ≤ n) : Decomposable S n := by
  rcases hb with ⟨i, j, he⟩
  cases i with
  | succ i =>
    have he' : m + (i * m + j * (m + d)) = n := by
      simp only [Nat.succ_mul] at he
      omega
    exact ⟨m, A.mem_m, i * m + j * (m + d),
      A.base_mem ⟨i, j, rfl⟩, A.m_pos, by have := A.m_pos; omega, he'⟩
  | zero =>
    cases j with
    | zero => simp at he; have := A.m_pos; omega
    | succ j =>
      have he' : (m + d) + j * (m + d) = n := by
        simp only [Nat.zero_mul, Nat.zero_add, Nat.succ_mul] at he
        omega
      exact ⟨m + d, A.mem_second, j * (m + d),
        A.mul_mem A.mem_second j, by have := A.m_pos; omega,
        by have := A.d_lt_m; omega, he'⟩

theorem Admissible.base_or_primitive_of_lt_three (A : Admissible S m d h)
    {n : ℕ} (hn : n ∈ S) (hu : n < 3 * m) :
    Base m d n ∨ (Primitive S n ∧ 2 * m ≤ n) := by
  by_cases hz : n = 0
  · subst n
    exact Or.inl base_zero
  have hp : 0 < n := by omega
  rcases primitive_or_decomposable hn hp with hprim | hdec
  · by_cases hsmall : n < 2 * m
    · rcases (A.first n (A.lower n hn hp) hsmall).1 hn with rfl | rfl
      · exact Or.inl base_m
      · exact Or.inl base_second
    · exact Or.inr ⟨hprim, by omega⟩
  · rcases hdec with ⟨x, hx, y, hy, hxp, hyp, hxy⟩
    have hxm := A.lower x hx hxp
    have hym := A.lower y hy hyp
    have hxf := (A.first x hxm (by omega)).1 hx
    have hyf := (A.first y hym (by omega)).1 hy
    have hxb : Base m d x := by
      rcases hxf with rfl | rfl
      · exact base_m
      · exact base_second
    have hyb : Base m d y := by
      rcases hyf with rfl | rfl
      · exact base_m
      · exact base_second
    exact Or.inl (hxy ▸ base_add hxb hyb)

noncomputable section
open Classical

@[simp] theorem mem_middleOffsets {j : ℕ} :
    j ∈ middleOffsets S m h ↔ j < h ∧ Primitive S (2 * m + j) := by
  simp only [middleOffsets, mem_image, middlePrims, mem_filter, mem_Ico]
  constructor
  · rintro ⟨n, ⟨⟨hn, hnh⟩, hp⟩, he⟩
    have he' : n = 2 * m + j := by omega
    exact ⟨by omega, he' ▸ hp⟩
  · rintro ⟨hj, hp⟩
    exact ⟨2 * m + j, ⟨⟨by omega, by omega⟩, hp⟩, by omega⟩

theorem middleOffsets_lt {j : ℕ} (hj : j ∈ middleOffsets S m h) : j < h :=
  (mem_middleOffsets.mp hj).1

/-- Additional third-layer members, with the base monoid removed. -/
def thirdOffsets (S : Set ℕ) (m d h : ℕ) : Finset ℕ :=
  (shiftUnion (middleOffsets S m h) d h).filter
    (fun x => ¬ Base m d (3 * m + x))

def thirdExtras (S : Set ℕ) (m d h : ℕ) : Finset ℕ :=
  (thirdOffsets S m d h).image (fun x => 3 * m + x)

theorem mem_thirdOffsets {x : ℕ} :
    x ∈ thirdOffsets S m d h ↔
      (x ∈ middleOffsets S m h ∨
        ∃ j ∈ middleOffsets S m h, j + d < h ∧ j + d = x) ∧
      ¬ Base m d (3 * m + x) := by
  simp [thirdOffsets, shiftUnion]

theorem thirdExtras_properties (A : Admissible S m d h) {n : ℕ}
    (hn : n ∈ thirdExtras S m d h) :
    n ∈ S ∧ n < 3 * m + h ∧ Decomposable S n ∧ ¬ Base m d n := by
  rcases mem_image.mp hn with ⟨x, hx, rfl⟩
  rcases mem_thirdOffsets.mp hx with ⟨hx, hnb⟩
  rcases hx with hx | ⟨j, hj, hjh, rfl⟩
  · have hx' := mem_middleOffsets.mp hx
    have he : (2 * m + x) + m = 3 * m + x := by omega
    have hd : Decomposable S (3 * m + x) :=
      ⟨2 * m + x, hx'.2.1, m, A.mem_m, hx'.2.2.1, A.m_pos, he⟩
    exact ⟨he ▸ A.add_mem _ _ hx'.2.1 A.mem_m, by omega, hd, hnb⟩
  · have hj' := mem_middleOffsets.mp hj
    have he : (2 * m + j) + (m + d) = 3 * m + (j + d) := by omega
    have hd : Decomposable S (3 * m + (j + d)) :=
      ⟨2 * m + j, hj'.2.1, m + d, A.mem_second, hj'.2.2.1,
        by have := A.m_pos; omega, he⟩
    exact ⟨he ▸ A.add_mem _ _ hj'.2.1 A.mem_second, by omega, hd, hnb⟩

theorem middle_add_first_mem_third (A : Admissible S m d h)
    {b f n : ℕ} (hb : Primitive S b) (hbm : 2 * m ≤ b)
    (hf : f = m ∨ f = m + d) (he : b + f = n)
    (hn : n < 3 * m + h) (hnb : ¬ Base m d n) :
    n ∈ thirdExtras S m d h := by
  have hfpos : m ≤ f := by rcases hf with rfl | rfl <;> omega
  have hbu : b < 2 * m + h := by omega
  let j := b - 2 * m
  have hbj : b = 2 * m + j := by dsimp [j]; omega
  have hj : j ∈ middleOffsets S m h :=
    mem_middleOffsets.mpr ⟨by omega, hbj ▸ hb⟩
  rcases hf with hf | hf
  · have hne : n = 3 * m + j := by omega
    apply mem_image.mpr
    refine ⟨j, mem_thirdOffsets.mpr ⟨Or.inl hj, ?_⟩, hne.symm⟩
    simpa only [hne] using hnb
  · have hne : n = 3 * m + (j + d) := by omega
    apply mem_image.mpr
    refine ⟨j + d, mem_thirdOffsets.mpr
      ⟨Or.inr ⟨j, hj, by omega, rfl⟩, ?_⟩, hne.symm⟩
    simpa only [hne] using hnb

/-- The original left part is classified directly; no semigroup is deleted. -/
theorem left_membership (A : Admissible S m d h) {n : ℕ} :
    n ∈ left S m h ↔ n ∈ baseLeft m d h ∨
      n ∈ middlePrims S m h ∨ n ∈ terminalPrims S m h ∨
      n ∈ thirdExtras S m d h := by
  constructor
  · intro hn
    rcases mem_filter.mp hn with ⟨hnr, hns⟩
    have hnc := mem_range.mp hnr
    by_cases hnb : Base m d n
    · exact Or.inl (mem_filter.mpr ⟨mem_range.mpr hnc, hnb⟩)
    right
    have hnp : 0 < n := by
      by_contra hz
      have : n = 0 := by omega
      subst n
      exact hnb base_zero
    rcases primitive_or_decomposable hns hnp with hp | hd
    · have hnm : 2 * m ≤ n := by
        by_contra hm
        rcases (A.first n (A.lower n hns hnp) (by omega)).1 hns with rfl | rfl
        · exact hnb base_m
        · exact hnb base_second
      by_cases hu : n < 2 * m + h
      · exact Or.inl (mem_filter.mpr ⟨mem_Ico.mpr ⟨hnm, hu⟩, hp⟩)
      · exact Or.inr (Or.inl (mem_filter.mpr
          ⟨mem_Ico.mpr ⟨by omega, hnc⟩, hp⟩))
    · right; right
      rcases hd with ⟨x, hx, y, hy, hxp, hyp, hxy⟩
      have hxm := A.lower x hx hxp
      have hym := A.lower y hy hyp
      have hhm := A.h_le_m
      rcases A.base_or_primitive_of_lt_three hx (by omega) with hxb | ⟨hxp', hx2⟩
      · rcases A.base_or_primitive_of_lt_three hy (by omega) with hyb | ⟨hyp', hy2⟩
        · exact False.elim (hnb (hxy ▸ base_add hxb hyb))
        · exact middle_add_first_mem_third A hyp' hy2
            ((A.first x hxm (by omega)).1 hx) (by omega) hnc hnb
      · exact middle_add_first_mem_third A hxp' hx2
          ((A.first y hym (by omega)).1 hy) hxy hnc hnb
  · intro hn
    rcases hn with hn | hn | hn | hn
    · rcases mem_filter.mp hn with ⟨hr, hb⟩
      exact mem_filter.mpr ⟨hr, A.base_mem hb⟩
    · rcases mem_filter.mp hn with ⟨hi, hp⟩
      have hi' := mem_Ico.mp hi
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp.1⟩
    · rcases mem_filter.mp hn with ⟨hi, hp⟩
      exact mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp hi).2, hp.1⟩
    · have hn' := thirdExtras_properties A hn
      exact mem_filter.mpr ⟨mem_range.mpr hn'.2.1, hn'.1⟩

theorem left_eq_union (A : Admissible S m d h) :
    left S m h = baseLeft m d h ∪
      (middlePrims S m h ∪ (terminalPrims S m h ∪ thirdExtras S m d h)) := by
  ext n
  simpa only [mem_union] using left_membership A (n := n)

theorem baseLeft_disjoint_middle (A : Admissible S m d h) :
    Disjoint (baseLeft m d h) (middlePrims S m h) := by
  apply disjoint_left.mpr
  intro n hn hm
  have hb := (mem_filter.mp hn).2
  rcases mem_filter.mp hm with ⟨hi, hp⟩
  exact hp.2.2 (A.base_decomposable hb (mem_Ico.mp hi).1)

theorem baseLeft_disjoint_terminal (A : Admissible S m d h) :
    Disjoint (baseLeft m d h) (terminalPrims S m h) := by
  apply disjoint_left.mpr
  intro n hn hm
  have hb := (mem_filter.mp hn).2
  rcases mem_filter.mp hm with ⟨hi, hp⟩
  have hlow := (mem_Ico.mp hi).1
  exact hp.2.2 (A.base_decomposable hb (by omega))

theorem baseLeft_disjoint_third :
    Disjoint (baseLeft m d h) (thirdExtras S m d h) := by
  apply disjoint_left.mpr
  intro n hn hm
  rcases mem_image.mp hm with ⟨x, hx, rfl⟩
  exact (mem_thirdOffsets.mp hx).2 (mem_filter.mp hn).2

theorem middle_disjoint_terminal :
    Disjoint (middlePrims S m h) (terminalPrims S m h) := by
  apply disjoint_left.mpr
  intro n hn hm
  have hn' := mem_Ico.mp (mem_filter.mp hn).1
  have hm' := mem_Ico.mp (mem_filter.mp hm).1
  omega

theorem middle_disjoint_third (A : Admissible S m d h) :
    Disjoint (middlePrims S m h) (thirdExtras S m d h) := by
  apply disjoint_left.mpr
  intro n hn hm
  exact (mem_filter.mp hn).2.2.2 (thirdExtras_properties A hm).2.2.1

theorem terminal_disjoint_third (A : Admissible S m d h) :
    Disjoint (terminalPrims S m h) (thirdExtras S m d h) := by
  apply disjoint_left.mpr
  intro n hn hm
  exact (mem_filter.mp hn).2.2.2 (thirdExtras_properties A hm).2.2.1

theorem card_left (A : Admissible S m d h) :
    (left S m h).card = (baseLeft m d h).card +
      (middlePrims S m h).card + (thirdExtras S m d h).card +
      (terminalPrims S m h).card := by
  have hb : Disjoint (baseLeft m d h)
      (middlePrims S m h ∪ (terminalPrims S m h ∪ thirdExtras S m d h)) := by
    apply disjoint_left.mpr
    intro n hn hu
    rcases mem_union.mp hu with hu | hu
    · exact disjoint_left.mp (baseLeft_disjoint_middle A) hn hu
    · rcases mem_union.mp hu with hu | hu
      · exact disjoint_left.mp (baseLeft_disjoint_terminal A) hn hu
      · exact disjoint_left.mp baseLeft_disjoint_third hn hu
  have hm : Disjoint (middlePrims S m h)
      (terminalPrims S m h ∪ thirdExtras S m d h) := by
    apply disjoint_left.mpr
    intro n hn hu
    rcases mem_union.mp hu with hu | hu
    · exact disjoint_left.mp middle_disjoint_terminal hn hu
    · exact disjoint_left.mp (middle_disjoint_third A) hn hu
  rw [left_eq_union A, card_union_of_disjoint hb,
    card_union_of_disjoint hm, card_union_of_disjoint (terminal_disjoint_third A)]
  omega

theorem leftPrims_eq_union (A : Admissible S m d h) :
    leftPrims S m h = {m, m + d} ∪
      (middlePrims S m h ∪ terminalPrims S m h) := by
  ext n
  constructor
  · intro hn
    rcases mem_filter.mp hn with ⟨hnr, hp⟩
    have hnu := mem_range.mp hnr
    by_cases hn2 : n < 2 * m
    · apply mem_union.mpr; left
      have hf := (A.first n (A.lower n hp.1 hp.2.1) hn2).1 hp.1
      simpa only [mem_insert, mem_singleton] using hf
    · apply mem_union.mpr; right
      by_cases hnh : n < 2 * m + h
      · exact mem_union.mpr (Or.inl (mem_filter.mpr
          ⟨mem_Ico.mpr ⟨by omega, hnh⟩, hp⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr
          ⟨mem_Ico.mpr ⟨by omega, hnu⟩, hp⟩))
  · intro hn
    rcases mem_union.mp hn with hn | hn
    · have hn' : n = m ∨ n = m + d := by
        simpa only [mem_insert, mem_singleton] using hn
      rcases hn' with rfl | rfl
      · exact mem_filter.mpr ⟨mem_range.mpr (by have := A.m_pos; omega), A.primitive_m⟩
      · exact mem_filter.mpr ⟨mem_range.mpr (by have := A.d_lt_m; have := A.m_pos; omega),
          A.primitive_second⟩
    · rcases mem_union.mp hn with hn | hn
      · rcases mem_filter.mp hn with ⟨hi, hp⟩
        have hi' := mem_Ico.mp hi
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩
      · rcases mem_filter.mp hn with ⟨hi, hp⟩
        exact mem_filter.mpr ⟨mem_range.mpr (mem_Ico.mp hi).2, hp⟩

theorem card_leftPrims (A : Admissible S m d h) :
    (leftPrims S m h).card = 2 + (middlePrims S m h).card +
      (terminalPrims S m h).card := by
  have hd : Disjoint ({m, m + d} : Finset ℕ)
      (middlePrims S m h ∪ terminalPrims S m h) := by
    apply disjoint_left.mpr
    intro n hn hu
    have hn' : n = m ∨ n = m + d := by
      simpa only [mem_insert, mem_singleton] using hn
    have hnu : n < 2 * m := by
      have := A.m_pos
      have := A.d_lt_m
      rcases hn' with rfl | rfl <;> omega
    rcases mem_union.mp hu with hu | hu
    · have := (mem_Ico.mp (mem_filter.mp hu).1).1
      omega
    · have := (mem_Ico.mp (mem_filter.mp hu).1).1
      omega
  have hne : m ≠ m + d := by have := A.d_pos; omega
  rw [leftPrims_eq_union A, card_union_of_disjoint hd,
    card_union_of_disjoint middle_disjoint_terminal]
  rw [card_pair hne]
  omega

theorem card_middleOffsets :
    (middleOffsets S m h).card = (middlePrims S m h).card := by
  apply card_image_of_injOn
  intro x hx y hy he
  have hx' := (mem_Ico.mp (mem_filter.mp hx).1).1
  have hy' := (mem_Ico.mp (mem_filter.mp hy).1).1
  change x - 2 * m = y - 2 * m at he
  omega

theorem card_thirdExtras :
    (thirdExtras S m d h).card = (thirdOffsets S m d h).card := by
  apply card_image_of_injective
  intro x y he
  change 3 * m + x = 3 * m + y at he
  omega

theorem middleOffsets_exclusions (A : Admissible S m d h) {j : ℕ}
    (hj : j ∈ middleOffsets S m h) : j ≠ 0 ∧ j ≠ d ∧ j ≠ 2 * d := by
  have hp := (mem_middleOffsets.mp hj).2
  have hnot : ¬ Base m d (2 * m + j) := by
    intro hb
    exact hp.2.2 (A.base_decomposable hb (by omega))
  refine ⟨?_, ?_, ?_⟩
  · intro he; subst j
    exact hnot ⟨2, 0, by simp⟩
  · intro he; subst j
    exact hnot ⟨1, 1, by simp; omega⟩
  · intro he; subst j
    exact hnot ⟨0, 2, by simp [Nat.mul_add]⟩

/-- The two families of threshold expressions using one middle primitive. -/
def oneMiddle (S : Set ℕ) (m d h : ℕ) : Finset ℕ :=
  (lowShifts (middleOffsets S m h) d h).image (fun x => 4 * m + x) ∪
    (highIndices (middleOffsets S m h) d h).image (fun j => 3 * m + j + d)

def twoMiddle (S : Set ℕ) (m h : ℕ) : Finset ℕ :=
  ((middleOffsets S m h).product (middleOffsets S m h)).image
    (fun p => 4 * m + p.1 + p.2)

def terminalHits (S : Set ℕ) (m d h : ℕ) : Finset ℕ :=
  (terminalPrims S m h).image (fun b => b + m) ∪
    (terminalPrims S m h).image (fun b => b + (m + d))

theorem base_positive_lt_three (A : Admissible S m d h) {n : ℕ}
    (hb : Base m d n) (hp : 0 < n) (hu : n < 3 * m) :
    n = m ∨ n = m + d ∨ n = 2 * m ∨ n = 2 * m + d ∨ n = 2 * m + 2 * d := by
  rcases hb with ⟨i, j, he⟩
  have hsum : (i + j) * m ≤ n := by
    calc
      (i + j) * m = i * m + j * m := Nat.add_mul _ _ _
      _ ≤ i * m + j * (m + d) := Nat.add_le_add_left
        (Nat.mul_le_mul_left j (by omega)) _
      _ = n := he.symm
  have hij : i + j < 3 := (Nat.mul_lt_mul_right A.m_pos).mp (lt_of_le_of_lt hsum hu)
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp_all [Nat.mul_add]; omega

theorem oneMiddle_mem_low {j n : ℕ} (hj : j ∈ middleOffsets S m h)
    (he : n = 4 * m + j ∨ n = 4 * m + j + d ∨ n = 4 * m + j + 2 * d)
    (hu : n < 4 * m + h) : n ∈ oneMiddle S m d h := by
  apply mem_union.mpr
  left
  rcases he with he | he | he
  · refine mem_image.mpr ⟨j, ?_, by omega⟩
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hj)))
  · refine mem_image.mpr ⟨j + d, ?_, by omega⟩
    exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
      (mem_shiftBelow.mpr ⟨j, hj, by omega, rfl⟩))))
  · refine mem_image.mpr ⟨j + 2 * d, ?_, by omega⟩
    exact mem_union.mpr (Or.inr
      (mem_shiftBelow.mpr ⟨j, hj, by omega, rfl⟩))

theorem terminal_add_cover (A : Admissible S m d h) {b y n : ℕ}
    (hb : b ∈ terminalPrims S m h) (hy : y ∈ S) (hyp : 0 < y)
    (he : b + y = n) (hu : n < 4 * m + h) : n ∈ terminalHits S m d h := by
  have hbm := (mem_Ico.mp (mem_filter.mp hb).1).1
  have hym := A.lower y hy hyp
  have hf := (A.first y hym (by omega)).1 hy
  rcases hf with rfl | rfl
  · exact mem_union.mpr (Or.inl (mem_image.mpr ⟨b, hb, he⟩))
  · exact mem_union.mpr (Or.inr (mem_image.mpr ⟨b, hb, he⟩))

theorem middle_add_cover (A : Admissible S m d h) {b y n : ℕ}
    (hb : b ∈ middlePrims S m h) (hy : y ∈ S) (hyp : 0 < y)
    (he : b + y = n) (hl : 3 * m + h ≤ n) (hu : n < 4 * m + h) :
    n ∈ oneMiddle S m d h ∨ n ∈ twoMiddle S m h := by
  have hbi := mem_Ico.mp (mem_filter.mp hb).1
  have hbp := (mem_filter.mp hb).2
  let j := b - 2 * m
  have hbj : b = 2 * m + j := by dsimp [j]; omega
  have hj : j ∈ middleOffsets S m h :=
    mem_middleOffsets.mpr ⟨by omega, hbj ▸ hbp⟩
  have hyu : y < 3 * m := by have := A.h_le_m; omega
  rcases A.base_or_primitive_of_lt_three hy hyu with hyb | ⟨hyp', hy2⟩
  · left
    rcases base_positive_lt_three A hyb hyp hyu with hyf | hyf | hyf | hyf | hyf
    · have hjh := middleOffsets_lt hj
      omega
    · apply mem_union.mpr
      right
      exact mem_image.mpr ⟨j, mem_filter.mpr ⟨hj, by omega⟩, by omega⟩
    · exact oneMiddle_mem_low hj (Or.inl (by omega)) hu
    · exact oneMiddle_mem_low hj (Or.inr (Or.inl (by omega))) hu
    · exact oneMiddle_mem_low hj (Or.inr (Or.inr (by omega))) hu
  · right
    let i := y - 2 * m
    have hyi : y = 2 * m + i := by dsimp [i]; omega
    have hi : i ∈ middleOffsets S m h :=
      mem_middleOffsets.mpr ⟨by omega, hyi ▸ hyp'⟩
    exact mem_image.mpr ⟨(j, i), mem_product.mpr ⟨hj, hi⟩, by dsimp; omega⟩

theorem thirdExtras_representation {n : ℕ} (hn : n ∈ thirdExtras S m d h) :
    ∃ b ∈ middlePrims S m h, ∃ f, (f = m ∨ f = m + d) ∧ b + f = n := by
  rcases mem_image.mp hn with ⟨x, hx, rfl⟩
  rcases (mem_thirdOffsets.mp hx).1 with hx | ⟨j, hj, hjh, rfl⟩
  · have hx' := mem_middleOffsets.mp hx
    exact ⟨2 * m + x, mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hx'.2⟩,
      m, Or.inl rfl, by omega⟩
  · have hj' := mem_middleOffsets.mp hj
    exact ⟨2 * m + j, mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hj'.2⟩,
      m + d, Or.inr rfl, by omega⟩

theorem third_add_cover (A : Admissible S m d h) {x y n : ℕ}
    (hx : x ∈ thirdExtras S m d h) (hy : y ∈ S) (hyp : 0 < y)
    (he : x + y = n) (hl : 3 * m + h ≤ n) (hu : n < 4 * m + h) :
    n ∈ oneMiddle S m d h ∨ n ∈ twoMiddle S m h := by
  rcases thirdExtras_representation hx with ⟨b, hb, f, hf, hbf⟩
  have hfs : f ∈ S := by
    rcases hf with rfl | rfl
    · exact A.mem_m
    · exact A.mem_second
  exact middle_add_cover A hb (A.add_mem f y hfs hy) (by omega) (by omega) hl hu

/-- Every intrinsic right decomposition belongs to one of four explicit
finite families.  The last three families may overcount; no semantic
generation or cardinality premise is used. -/
theorem rightDecomp_subset (A : Admissible S m d h) :
    rightDecomp S m h ⊆ baseRight m d h ∪
      (oneMiddle S m d h ∪ (twoMiddle S m h ∪ terminalHits S m d h)) := by
  intro n hn
  rcases mem_filter.mp hn with ⟨hni, x, hx, y, hy, hxp, hyp, he⟩
  rcases mem_Ico.mp hni with ⟨hl, hu⟩
  have hxm := A.lower x hx hxp
  have hym := A.lower y hy hyp
  have hxl : x ∈ left S m h := mem_filter.mpr
    ⟨mem_range.mpr (by omega), hx⟩
  have hyl : y ∈ left S m h := mem_filter.mpr
    ⟨mem_range.mpr (by omega), hy⟩
  have putMid : n ∈ oneMiddle S m d h ∨ n ∈ twoMiddle S m h →
      n ∈ baseRight m d h ∪
        (oneMiddle S m d h ∪ (twoMiddle S m h ∪ terminalHits S m d h)) := by
    intro hh
    apply mem_union.mpr; right
    rcases hh with hh | hh
    · exact mem_union.mpr (Or.inl hh)
    · exact mem_union.mpr (Or.inr (mem_union.mpr (Or.inl hh)))
  have putTerm : n ∈ terminalHits S m d h →
      n ∈ baseRight m d h ∪
        (oneMiddle S m d h ∪ (twoMiddle S m h ∪ terminalHits S m d h)) := by
    intro hh
    exact mem_union.mpr (Or.inr (mem_union.mpr (Or.inr (mem_union.mpr (Or.inr hh)))))
  rcases (left_membership A).mp hxl with hxb | hxb | hxc | hxt
  · rcases (left_membership A).mp hyl with hyb | hyb | hyc | hyt
    · exact mem_union.mpr (Or.inl (mem_filter.mpr
        ⟨mem_Ico.mpr ⟨hl, hu⟩, he ▸ base_add (mem_filter.mp hxb).2 (mem_filter.mp hyb).2⟩))
    · exact putMid (middle_add_cover A hyb hx hxp (by omega) hl hu)
    · exact putTerm (terminal_add_cover A hyc hx hxp (by omega) hu)
    · exact putMid (third_add_cover A hyt hx hxp (by omega) hl hu)
  · exact putMid (middle_add_cover A hxb hy hyp he hl hu)
  · exact putTerm (terminal_add_cover A hxc hy hyp he hu)
  · exact putMid (third_add_cover A hxt hy hyp he hl hu)

theorem card_oneMiddle_le :
    (oneMiddle S m d h).card ≤
      (lowShifts (middleOffsets S m h) d h).card +
        (highIndices (middleOffsets S m h) d h).card := by
  exact card_low_high_images_le _ _ _ _ _

theorem card_terminalHits_le :
    (terminalHits S m d h).card ≤ 2 * (terminalPrims S m h).card := by
  calc
    _ ≤ ((terminalPrims S m h).image (fun b => b + m)).card +
        ((terminalPrims S m h).image (fun b => b + (m + d))).card := card_union_le _ _
    _ ≤ (terminalPrims S m h).card + (terminalPrims S m h).card :=
      Nat.add_le_add (card_image_le) (card_image_le)
    _ = _ := by omega

theorem card_rightDecomp_le (A : Admissible S m d h) :
    (rightDecomp S m h).card ≤ (baseRight m d h).card +
      (oneMiddle S m d h).card + (twoMiddle S m h).card +
      2 * (terminalPrims S m h).card := by
  have hsub := card_le_card (rightDecomp_subset A)
  have h1 := card_union_le (baseRight m d h)
    (oneMiddle S m d h ∪ (twoMiddle S m h ∪ terminalHits S m d h))
  have h2 := card_union_le (oneMiddle S m d h)
    (twoMiddle S m h ∪ terminalHits S m d h)
  have h3 := card_union_le (twoMiddle S m h) (terminalHits S m d h)
  have h4 := card_terminalHits_le (S := S) (m := m) (d := d) (h := h)
  omega

theorem card_rightDecomp_le_shifts (A : Admissible S m d h) :
    (rightDecomp S m h).card ≤ (baseRight m d h).card +
      (lowShifts (middleOffsets S m h) d h).card +
      (highIndices (middleOffsets S m h) d h).card +
      (twoMiddle S m h).card + 2 * (terminalPrims S m h).card := by
  have h1 := card_rightDecomp_le A
  have h2 := card_oneMiddle_le (S := S) (m := m) (d := d) (h := h)
  omega

theorem card_left_offsets (A : Admissible S m d h) :
    (left S m h).card = (baseLeft m d h).card +
      (middleOffsets S m h).card + (thirdOffsets S m d h).card +
      (terminalPrims S m h).card := by
  rw [card_left A, card_middleOffsets, card_thirdExtras]

theorem card_leftPrims_offsets (A : Admissible S m d h) :
    (leftPrims S m h).card = 2 + (middleOffsets S m h).card +
      (terminalPrims S m h).card := by
  rw [card_leftPrims A, card_middleOffsets]

theorem twice_card_twoMiddle_le :
    2 * (twoMiddle S m h).card ≤
      (middleOffsets S m h).card * ((middleOffsets S m h).card + 1) :=
  twice_shiftedPairSums_card_le (middleOffsets S m h) (4 * m)

/-- The complete semantic threshold estimate, with unordered pairs counted
without natural-number division. -/
theorem twice_card_rightDecomp_le (A : Admissible S m d h) :
    2 * (rightDecomp S m h).card ≤ 2 * (baseRight m d h).card +
      2 * ((lowShifts (middleOffsets S m h) d h).card +
        (highIndices (middleOffsets S m h) d h).card) +
      (middleOffsets S m h).card * ((middleOffsets S m h).card + 1) +
      4 * (terminalPrims S m h).card := by
  have h1 := card_rightDecomp_le_shifts A
  have h2 := twice_card_twoMiddle_le (S := S) (m := m) (h := h)
  omega

end
end Eliahou.DepthFour
