import Eliahou.Basic

namespace Eliahou

/-- Intrinsic additive indecomposability, quantified over all natural summands. -/
def Presentation.IsPrimitive (p : Presentation) (n : Nat) : Prop :=
  0 < n ∧ p.Mem n ∧ ∀ a b, 0 < a → 0 < b → a + b = n →
    ¬ (p.Mem a ∧ p.Mem b)

theorem Presentation.primitive_iff_bounded (p : Presentation) (n : Nat) :
    p.primitive n = true ↔
      0 < n ∧ p.Mem n ∧ ∀ a, a < n → 0 < a → ¬ (p.Mem a ∧ p.Mem (n - a)) := by
  simp only [primitive, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range]
  simp only [Mem]
  constructor
  · rintro ⟨⟨hn, hmem⟩, h⟩
    refine ⟨hn, hmem, ?_⟩
    intro a han ha hboth
    have hx := h a han
    simp [ha, hboth.1, hboth.2] at hx
  · rintro ⟨hn, hmem, h⟩
    refine ⟨⟨hn, hmem⟩, ?_⟩
    intro a han
    by_cases ha : 0 < a
    · have hx := h a han ha
      by_cases hm : p.contains a = true
      · have hb : p.contains (n - a) = false := by
          cases hb' : p.contains (n - a)
          · rfl
          · exact False.elim (hx ⟨hm, hb'⟩)
        simp [ha, hb]
      · have hb : p.contains a = false := by
          cases hb' : p.contains a
          · rfl
          · exact False.elim (hm hb')
        simp [hb]
    · simp [ha]

theorem Presentation.primitive_iff (p : Presentation) (n : Nat) :
    p.primitive n = true ↔ p.IsPrimitive n := by
  rw [p.primitive_iff_bounded]
  constructor
  · rintro ⟨hn, hm, h⟩
    refine ⟨hn, hm, ?_⟩
    intro a b ha hb hab hboth
    have han : a < n := by omega
    have hsub : n - a = b := by omega
    exact h a han ha ⟨hboth.1, hsub ▸ hboth.2⟩
  · rintro ⟨hn, hm, h⟩
    refine ⟨hn, hm, ?_⟩
    intro a han ha hboth
    exact h a (n - a) ha (by omega) (by omega) hboth

end Eliahou

#print axioms Eliahou.Presentation.primitive_iff
