import Eliahou.DepthFour.Defs
import Mathlib.Tactic.Linarith

namespace Eliahou.DepthFour

open Finset

def baseCandidates (m d : ℕ) : Finset ℕ :=
  {0, m, m + d, 2*m, 2*m+d, 2*m+2*d, 3*m, 3*m+d,
    3*m+2*d, 3*m+3*d, 4*m, 4*m+d, 4*m+2*d, 4*m+3*d, 4*m+4*d}

def baseSmall (m d : ℕ) : Finset ℕ :=
  {0, m, m + d, 2*m, 2*m+d, 2*m+2*d, 3*m, 3*m+d,
    3*m+2*d, 3*m+3*d}

theorem base_of_mem_candidates {m d n : ℕ} (hn : n ∈ baseCandidates m d) :
    Base m d n := by
  simp only [baseCandidates, mem_insert, mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by omega⟩
  · exact ⟨1, 0, by omega⟩
  · exact ⟨0, 1, by omega⟩
  · exact ⟨2, 0, by omega⟩
  · exact ⟨1, 1, by omega⟩
  · exact ⟨0, 2, by omega⟩
  · exact ⟨3, 0, by omega⟩
  · exact ⟨2, 1, by omega⟩
  · exact ⟨1, 2, by omega⟩
  · exact ⟨0, 3, by omega⟩
  · exact ⟨4, 0, by omega⟩
  · exact ⟨3, 1, by omega⟩
  · exact ⟨2, 2, by omega⟩
  · exact ⟨1, 3, by omega⟩
  · exact ⟨0, 4, by omega⟩

theorem base_lt_five_iff {m d n : ℕ} (hm : 0 < m) (hn : n < 5*m) :
    Base m d n ↔ n ∈ baseCandidates m d := by
  constructor
  · rintro ⟨i,j,he⟩
    have hlen : i+j < 5 := by
      by_contra hc
      have hb : 5 ≤ i+j := by omega
      have hp := Nat.mul_le_mul_right m hb
      nlinarith
    have hi : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
    simp only [baseCandidates, mem_insert, mem_singleton]
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl | rfl | rfl <;> omega
  · exact base_of_mem_candidates

theorem base_lt_four_iff {m d n : ℕ} (hm : 0 < m) (hn : n < 4*m) :
    Base m d n ↔ n ∈ baseSmall m d := by
  rw [base_lt_five_iff hm (by omega)]
  simp only [baseCandidates, baseSmall, mem_insert, mem_singleton]
  omega

theorem mem_baseLeft_iff {m d h n : ℕ} (hm : 0 < m) (hh : h ≤ m) :
    n ∈ baseLeft m d h ↔ n < 3*m+h ∧ n ∈ baseSmall m d := by
  classical
  simp only [baseLeft, mem_filter, mem_range]
  constructor
  · rintro ⟨hn,hb⟩
    exact ⟨hn, (base_lt_four_iff hm (by omega)).mp hb⟩
  · rintro ⟨hn,hb⟩
    exact ⟨hn, (base_lt_four_iff hm (by omega)).mpr hb⟩

theorem mem_baseRight_iff {m d h n : ℕ} (hm : 0 < m) (hh : h ≤ m) :
    n ∈ baseRight m d h ↔
      3*m+h ≤ n ∧ n < 4*m+h ∧ n ∈ baseCandidates m d := by
  classical
  simp only [baseRight, mem_filter, mem_Ico]
  constructor
  · rintro ⟨⟨hl,hu⟩,hb⟩
    exact ⟨hl,hu,(base_lt_five_iff hm (by omega)).mp hb⟩
  · rintro ⟨hl,hu,hb⟩
    exact ⟨⟨hl,hu⟩,base_of_mem_candidates hb⟩

theorem baseLeft_eq_seven {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdm : 2*d < m) (hh : 0 < h) (hhd : h ≤ d) :
    baseLeft m d h = {0,m,m+d,2*m,2*m+d,2*m+2*d,3*m} := by
  ext n
  rw [mem_baseLeft_iff hm (by omega)]
  simp only [baseSmall, mem_insert, mem_singleton]
  omega

theorem baseLeft_eq_eight {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdm : 2*d < m) (hdh : d < h) (hh : h ≤ 2*d) :
    baseLeft m d h = {0,m,m+d,2*m,2*m+d,2*m+2*d,3*m,3*m+d} := by
  ext n
  rw [mem_baseLeft_iff hm (by omega)]
  simp only [baseSmall, mem_insert, mem_singleton]
  omega

theorem baseLeft_eq_nine {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdm : 2*d < m) (hdh : 2*d < h) (hh : h ≤ 3*d) (hhm : h ≤ m) :
    baseLeft m d h = {0,m,m+d,2*m,2*m+d,2*m+2*d,3*m,3*m+d,3*m+2*d} := by
  ext n
  rw [mem_baseLeft_iff hm hhm]
  simp only [baseSmall, mem_insert, mem_singleton]
  omega

theorem baseLeft_eq_ten {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdh : 3*d < h) (hhm : h ≤ m) :
    baseLeft m d h = baseSmall m d := by
  ext n
  rw [mem_baseLeft_iff hm hhm]
  simp only [baseSmall, mem_insert, mem_singleton]
  omega

theorem card_baseLeft_seven {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdm : 2*d < m) (hh : 0 < h) (hhd : h ≤ d) :
    (baseLeft m d h).card = 7 := by
  rw [baseLeft_eq_seven hm hd hdm hh hhd]
  have hn : ([0,m,m+d,2*m,2*m+d,2*m+2*d,3*m] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa using List.toFinset_card_of_nodup hn

theorem card_baseLeft_eight {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdm : 2*d < m) (hdh : d < h) (hh : h ≤ 2*d) :
    (baseLeft m d h).card = 8 := by
  rw [baseLeft_eq_eight hm hd hdm hdh hh]
  have hn : ([0,m,m+d,2*m,2*m+d,2*m+2*d,3*m,3*m+d] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa using List.toFinset_card_of_nodup hn

theorem card_baseLeft_nine {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdm : 2*d < m) (hdh : 2*d < h) (hh : h ≤ 3*d) (hhm : h ≤ m) :
    (baseLeft m d h).card = 9 := by
  rw [baseLeft_eq_nine hm hd hdm hdh hh hhm]
  have hn : ([0,m,m+d,2*m,2*m+d,2*m+2*d,3*m,3*m+d,3*m+2*d] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa using List.toFinset_card_of_nodup hn

theorem card_baseLeft_ten {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdh : 3*d < h) (hhm : h ≤ m) :
    (baseLeft m d h).card = 10 := by
  rw [baseLeft_eq_ten hm hd hdh hhm]
  have hn : ([0,m,m+d,2*m,2*m+d,2*m+2*d,3*m,3*m+d,3*m+2*d,3*m+3*d] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa [baseSmall] using List.toFinset_card_of_nodup hn

theorem card_baseRight_le_four {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdm : 2*d < m) (hh : 0 < h) (hhm : h ≤ m) (hhd : h ≤ 3*d) :
    (baseRight m d h).card ≤ 4 := by
  let x₁ := if d < h then 4*m+d else 3*m+d
  let x₂ := if 2*d < h then 4*m+2*d else 3*m+2*d
  let x₃ := if 3*d < h then 4*m+3*d else 3*m+3*d
  have hs : baseRight m d h ⊆ {4*m,x₁,x₂,x₃} := by
    intro n hn
    obtain ⟨hl,hu,hb⟩ := (mem_baseRight_iff hm hhm).mp hn
    simp only [baseCandidates, mem_insert, mem_singleton] at hb
    simp only [mem_insert, mem_singleton]
    dsimp [x₁,x₂,x₃]
    split_ifs <;> omega
  have hc : ({4*m,x₁,x₂,x₃} : Finset ℕ).card ≤ 4 := by
    simpa using (List.toFinset_card_le (l := [4*m,x₁,x₂,x₃]))
  exact (card_le_card hs).trans hc

theorem card_baseRight_le_five {m d h : ℕ} (hm : 0 < m) (hd : 0 < d)
    (hdm : 2*d < m) (hh : 0 < h) (hhm : h ≤ m) :
    (baseRight m d h).card ≤ 5 := by
  let x₁ := if d < h then 4*m+d else 3*m+d
  let x₂ := if 2*d < h then 4*m+2*d else 3*m+2*d
  let x₃ := if 3*d < h then 4*m+3*d else 3*m+3*d
  have hs : baseRight m d h ⊆ {4*m,x₁,x₂,x₃,4*m+4*d} := by
    intro n hn
    obtain ⟨hl,hu,hb⟩ := (mem_baseRight_iff hm hhm).mp hn
    simp only [baseCandidates, mem_insert, mem_singleton] at hb
    simp only [mem_insert, mem_singleton]
    dsimp [x₁,x₂,x₃]
    split_ifs <;> omega
  have hc : ({4*m,x₁,x₂,x₃,4*m+4*d} : Finset ℕ).card ≤ 5 := by
    simpa using (List.toFinset_card_le (l := [4*m,x₁,x₂,x₃,4*m+4*d]))
  exact (card_le_card hs).trans hc

end Eliahou.DepthFour
