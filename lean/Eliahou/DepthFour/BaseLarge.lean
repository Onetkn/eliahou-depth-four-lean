import Eliahou.DepthFour.BaseCounts

/-! Base counting when the gap satisfies `m ≤ 2*d`. All counts refer to
the entire finite interval, using the proved generator characterization.
-/

namespace Eliahou.DepthFour

open Finset

theorem card_baseLeft_half_low {m d h : ℕ} (hm : 0 < m) (_hd : 0 < d)
    (heq : 2*d = m) (hh : 0 < h) (hhd : h ≤ d) :
    (baseLeft m d h).card = 6 := by
  have hs : baseLeft m d h = {0,m,m+d,2*m,2*m+d,3*m} := by
    ext n
    rw [mem_baseLeft_iff hm (by omega)]
    simp only [baseSmall, mem_insert, mem_singleton]
    omega
  rw [hs]
  have hn : ([0,m,m+d,2*m,2*m+d,3*m] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa using List.toFinset_card_of_nodup hn

theorem card_baseLeft_half_high {m d h : ℕ} (hm : 0 < m) (_hd : 0 < d)
    (heq : 2*d = m) (hdh : d < h) (hhm : h ≤ m) :
    (baseLeft m d h).card = 7 := by
  have hs : baseLeft m d h = {0,m,m+d,2*m,2*m+d,3*m,3*m+d} := by
    ext n
    rw [mem_baseLeft_iff hm hhm]
    simp only [baseSmall, mem_insert, mem_singleton]
    omega
  rw [hs]
  have hn : ([0,m,m+d,2*m,2*m+d,3*m,3*m+d] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa using List.toFinset_card_of_nodup hn

theorem card_baseLeft_large_low {m d h : ℕ} (hm : 0 < m) (hdm : d < m)
    (hmd : m < 2*d) (hh : 0 < h) (hhz : h ≤ 2*d-m) :
    (baseLeft m d h).card = 6 := by
  have hs : baseLeft m d h = {0,m,m+d,2*m,2*m+d,3*m} := by
    ext n
    rw [mem_baseLeft_iff hm (by omega)]
    simp only [baseSmall, mem_insert, mem_singleton]
    omega
  rw [hs]
  have hn : ([0,m,m+d,2*m,2*m+d,3*m] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa using List.toFinset_card_of_nodup hn

theorem card_baseLeft_large_middle {m d h : ℕ} (hm : 0 < m) (hdm : d < m)
    (hmd : m < 2*d) (hzh : 2*d-m < h) (hhd : h ≤ d) :
    (baseLeft m d h).card = 7 := by
  have hs : baseLeft m d h = {0,m,m+d,2*m,2*m+d,2*m+2*d,3*m} := by
    ext n
    rw [mem_baseLeft_iff hm (by omega)]
    simp only [baseSmall, mem_insert, mem_singleton]
    omega
  rw [hs]
  have hn : ([0,m,m+d,2*m,2*m+d,2*m+2*d,3*m] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa using List.toFinset_card_of_nodup hn

theorem card_baseLeft_large_high {m d h : ℕ} (hm : 0 < m) (hdm : d < m)
    (hmd : m < 2*d) (hdh : d < h) (hhm : h ≤ m) :
    (baseLeft m d h).card = 8 := by
  have hs : baseLeft m d h = {0,m,m+d,2*m,2*m+d,2*m+2*d,3*m,3*m+d} := by
    ext n
    rw [mem_baseLeft_iff hm hhm]
    simp only [baseSmall, mem_insert, mem_singleton]
    omega
  rw [hs]
  have hn : ([0,m,m+d,2*m,2*m+d,2*m+2*d,3*m,3*m+d] : List ℕ).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      not_or, not_false_eq_true, and_true]
    repeat' constructor <;> omega
  simpa using List.toFinset_card_of_nodup hn

theorem card_baseRight_half_le_two {m d h : ℕ} (hm : 0 < m) (_hd : 0 < d)
    (heq : 2*d = m) (hh : 0 < h) (hhm : h ≤ m) :
    (baseRight m d h).card ≤ 2 := by
  have hs : baseRight m d h ⊆ {4*m, if h ≤ d then 3*m+d else 4*m+d} := by
    intro n hn
    rw [mem_baseRight_iff hm hhm] at hn
    simp only [baseCandidates, mem_insert, mem_singleton] at hn
    by_cases hc : h ≤ d
    · simp only [ite_eq_left hc, mem_insert, mem_singleton]
      omega
    · simp only [ite_eq_right hc, mem_insert, mem_singleton]
      omega
  exact (card_le_card hs).trans card_le_two

theorem card_baseRight_large_le_three {m d h : ℕ} (hm : 0 < m)
    (hdm : d < m) (hmd : m < 2*d) (hh : 0 < h) (hhm : h ≤ m)
    (hhr : h ≤ 3*d-m) : (baseRight m d h).card ≤ 3 := by
  have hs : baseRight m d h ⊆
      {4*m, if h ≤ 2*d-m then 2*m+2*d else 3*m+2*d,
        if h ≤ d then 3*m+d else 4*m+d} := by
    intro n hn
    rw [mem_baseRight_iff hm hhm] at hn
    simp only [baseCandidates, mem_insert, mem_singleton] at hn
    by_cases hz : h ≤ 2*d-m <;> by_cases hc : h ≤ d
    all_goals simp only [hz, hc, ite_true, ite_false, mem_insert, mem_singleton]
    all_goals omega
  exact (card_le_card hs).trans card_le_three

theorem card_baseRight_large_le_four {m d h : ℕ} (hm : 0 < m)
    (hdm : d < m) (hmd : m < 2*d) (hh : 0 < h) (hhm : h ≤ m) :
    (baseRight m d h).card ≤ 4 := by
  have hs : baseRight m d h ⊆
      {4*m, if h ≤ 2*d-m then 2*m+2*d else 3*m+2*d,
        if h ≤ d then 3*m+d else 4*m+d, 3*m+3*d} := by
    intro n hn
    rw [mem_baseRight_iff hm hhm] at hn
    simp only [baseCandidates, mem_insert, mem_singleton] at hn
    by_cases hz : h ≤ 2*d-m <;> by_cases hc : h ≤ d
    all_goals simp only [hz, hc, ite_true, ite_false, mem_insert, mem_singleton]
    all_goals omega
  exact (card_le_card hs).trans card_le_four

end Eliahou.DepthFour
