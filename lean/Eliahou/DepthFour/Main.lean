import Eliahou.DepthFour.Reduction
import Eliahou.DepthFour.Offsets
import Eliahou.DepthFour.BaseCounts
import Eliahou.DepthFour.BaseLarge

namespace Eliahou.DepthFour

/-- The Eliahou number at any depth-four cutoff is nonnegative when the
unshifted first layer consists of exactly two elements. -/
theorem depth_four_nonneg {S : Set ℕ} {m d h : ℕ}
    (A : Admissible S m d h) : 0 ≤ eliahou S m h := by
  apply eliahou_nonneg_of_core A
  let J := middleOffsets S m h
  let k : ℤ := (baseLeft m d h).card
  let s : ℤ := (baseRight m d h).card
  let ρ : ℤ := (m : ℤ) - h
  let t : ℤ := J.card
  let v : ℤ := (thirdOffsets S m d h).card
  let w : ℤ := ((lowShifts J d h).card : ℤ) + (highIndices J d h).card
  let β : ℤ := shiftBeta J d h
  change 0 ≤ core k s ρ t v w
  have hm := A.m_pos
  have hd := A.d_pos
  have hdm := A.d_lt_m
  have hh := A.h_pos
  have hhm := A.h_le_m
  have ht : 0 ≤ t := Int.natCast_nonneg _
  have hv0 : 0 ≤ v := Int.natCast_nonneg _
  have hβ0 : 0 ≤ β := Int.natCast_nonneg _
  have hβt : β ≤ t := by
    dsimp only [β, t]
    exact_mod_cast shiftBeta_le J d h
  have hρ : 0 ≤ ρ := by dsimp [ρ]; omega
  have hk6 : 6 ≤ k := by
    dsimp only [k]
    exact_mod_cast six_le_card_baseLeft A
  have hw3 : w ≤ 3 * t := by
    dsimp only [w, t]
    exact_mod_cast card_lowShifts_add_high_le_three J d h
  have hwβ : w ≤ 2 * t + 2 * β := by
    dsimp only [w, t, β]
    exact_mod_cast card_lowShifts_add_high_le_beta J d h
  have hw2small (hh2 : h ≤ 2 * d) : w ≤ 2 * t := by
    dsimp only [w, t]
    exact_mod_cast card_lowShifts_add_high_le_two_of_small J d h hh2
  have hw2closed (hc : shiftBelow J d h ⊆ J) : w ≤ 2 * t := by
    dsimp only [w, t]
    exact_mod_cast card_lowShifts_add_high_le_two_of_closed J d h hc
  by_cases hsmall : 2 * d < m
  · have hvβ (hh3 : h ≤ 3 * d) : v = t + β := by
      dsimp only [v, t, β, J]
      exact_mod_cast card_thirdOffsets_small A hsmall hh3
    have hs4 (hh3 : h ≤ 3 * d) : s ≤ 4 := by
      dsimp only [s]
      exact_mod_cast card_baseRight_le_four hm hd hsmall hh hhm hh3
    by_cases hh2 : h ≤ 2 * d
    · have hv : t ≤ v := by have := hvβ (by omega); omega
      have hs := hs4 (by omega)
      have he : 0 ≤ 2 * k - 4 * s + ρ := by
        by_cases hh1 : h ≤ d
        · have hk : k = 7 := by
            dsimp only [k]
            exact_mod_cast card_baseLeft_seven hm hd hsmall hh hh1
          have hr : (2 : ℤ) ≤ ρ := by dsimp [ρ]; omega
          omega
        · have hk : k = 8 := by
            dsimp only [k]
            exact_mod_cast card_baseLeft_eight hm hd hsmall (by omega) hh2
          omega
      exact core_low hk6 he ht hv (hw2small hh2)
    · by_cases hh3 : h ≤ 3 * d
      · have hk : k = 9 := by
          dsimp only [k]
          exact_mod_cast card_baseLeft_nine hm hd hsmall (by omega) hh3 hhm
        have hs := hs4 hh3
        rw [hk]
        exact core_nine (by omega) ht hβ0 hβt (hvβ hh3) hwβ
      · have hk : k = 10 := by
          dsimp only [k]
          exact_mod_cast card_baseLeft_ten hm hd (by omega) hhm
        have hs : s ≤ 5 := by
          dsimp only [s]
          exact_mod_cast card_baseRight_le_five hm hd hsmall hh hhm
        have he : 0 ≤ 20 - 4 * s + ρ := by omega
        rw [hk]
        by_cases hv : t ≤ v
        · exact core_ten_regular he ht hv hw3
        · have hdef : (thirdOffsets S m d h).card < J.card := by
            have hvi : v < t := by omega
            dsimp only [v, t] at hvi
            exact_mod_cast hvi
          obtain ⟨hcard, hc, _⟩ := thirdOffsets_defect_small A hsmall hdef
          have hvi : v + 1 = t := by
            dsimp only [v, t, J]
            exact_mod_cast hcard
          exact core_ten_deficient he (by omega) (by omega) (hw2closed hc)
  · by_cases heq : 2 * d = m
    · have hs : s ≤ 2 := by
        dsimp only [s]
        exact_mod_cast card_baseRight_half_le_two hm hd heq hh hhm
      have hvβ : v = t + β := by
        dsimp only [v, t, β, J]
        exact_mod_cast card_thirdOffsets_half A heq
      exact core_low hk6 (by omega) ht (by omega) (hw2small (by omega))
    · have hlarge : m < 2 * d := by omega
      have hw := hw2small (by omega)
      have hs4 : s ≤ 4 := by
        dsimp only [s]
        exact_mod_cast card_baseRight_large_le_four hm hdm hlarge hh hhm
      have hs3 (hhr : h ≤ 3 * d - m) : s ≤ 3 := by
        dsimp only [s]
        exact_mod_cast card_baseRight_large_le_three hm hdm hlarge hh hhm hhr
      have hk8 (hdh : d < h) : k = 8 := by
        dsimp only [k]
        exact_mod_cast card_baseLeft_large_high hm hdm hlarge hdh hhm
      have he : 0 ≤ 2 * k - 4 * s + ρ := by
        by_cases hhr : h ≤ 3 * d - m
        · have hs := hs3 hhr
          omega
        · have hk := hk8 (by omega)
          omega
      by_cases hv : t ≤ v
      · exact core_low hk6 he ht hv hw
      · have hdef : (thirdOffsets S m d h).card < J.card := by
          have hvi : v < t := by omega
          dsimp only [v, t] at hvi
          exact_mod_cast hvi
        obtain ⟨hcard, _, hz⟩ := thirdOffsets_defect_large A hlarge hdef
        have hvi : v = t - 1 := by
          have hvi' : v + 1 = t := by
            dsimp only [v, t, J]
            exact_mod_cast hcard
          omega
        have hzh : 2 * d - m < h := middleOffsets_lt hz
        by_cases hhd : h ≤ d
        · have hk : k = 7 := by
            dsimp only [k]
            exact_mod_cast card_baseLeft_large_middle hm hdm hlarge hzh hhd
          have hs := hs3 (by omega)
          rw [hk]
          exact core_seven_deficient (by omega) hvi hw
        · have hk := hk8 (by omega)
          rw [hk]
          by_cases hhr : h ≤ 3 * d - m
          · have hs := hs3 hhr
            exact core_eight_deficient_slack (by omega) ht hvi hw
          · have ht2 : 2 ≤ t := by
              dsimp only [t, J]
              exact_mod_cast large_defect_two_le_card A hlarge (by omega) hdef
            exact core_eight_deficient (by omega) ht2 hvi hw

end Eliahou.DepthFour
