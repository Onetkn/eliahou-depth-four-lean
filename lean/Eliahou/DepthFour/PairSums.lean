import Mathlib.Data.Finset.Sym

/-! Cardinality bounds for pair sums, using unordered pairs with repetition.
These generic counting facts do not assume any semigroup hypotheses.
-/

namespace Eliahou.DepthFour

private def unorderedSum : Sym2 ℕ → ℕ :=
  Sym2.lift ⟨fun a b => a + b, Nat.add_comm⟩

theorem pairSums_card_le (J : Finset ℕ) :
    ((J.product J).image (fun p => p.1 + p.2)).card ≤
      J.card * (J.card + 1) / 2 := by
  have heq : (J.product J).image (fun p => p.1 + p.2) =
      J.sym2.image unorderedSum := by
    rw [Finset.sym2_eq_image, Finset.image_image]
    rfl
  rw [heq]
  calc
    (J.sym2.image unorderedSum).card ≤ J.sym2.card := Finset.card_image_le
    _ = J.card * (J.card + 1) / 2 := by
      rw [Finset.card_sym2, Nat.choose_two_right]
      simp [Nat.mul_comm]

theorem twice_pairSums_card_le (J : Finset ℕ) :
    2 * ((J.product J).image (fun p => p.1 + p.2)).card ≤
      J.card * (J.card + 1) := by
  have h := pairSums_card_le J
  omega

theorem shiftedPairSums_card_le (J : Finset ℕ) (K : ℕ) :
    ((J.product J).image (fun p => K + p.1 + p.2)).card ≤
      J.card * (J.card + 1) / 2 := by
  have heq : (J.product J).image (fun p => K + p.1 + p.2) =
      ((J.product J).image (fun p => p.1 + p.2)).image (fun n => K + n) := by
    rw [Finset.image_image]
    simp only [Nat.add_assoc]
    rfl
  rw [heq]
  exact Finset.card_image_le.trans (pairSums_card_le J)

theorem twice_shiftedPairSums_card_le (J : Finset ℕ) (K : ℕ) :
    2 * ((J.product J).image (fun p => K + p.1 + p.2)).card ≤
      J.card * (J.card + 1) := by
  have h := shiftedPairSums_card_le J K
  omega

end Eliahou.DepthFour

#print axioms Eliahou.DepthFour.pairSums_card_le
#print axioms Eliahou.DepthFour.twice_shiftedPairSums_card_le
