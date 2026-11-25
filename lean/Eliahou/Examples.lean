import Eliahou.Basic

/-!
Known examples, not new mathematics and not counterexamples to conjecture 2.7.
All concrete equalities below use kernel reduction (`decide`), not native_decide.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Eliahou

def example56 : Presentation :=
  ⟨56, [0, 14, 22, 23, 28, 36, 37, 42, 44, 45, 46, 50, 51]⟩

def example90 : Presentation :=
  ⟨90, [0, 19, 26, 27, 38, 45, 46, 52, 53, 54, 57, 64, 65,
    71, 72, 73, 76, 78, 79, 80, 81, 83, 84]⟩

theorem example56_valid : example56.Valid :=
  example56.valid_of_check (by decide)

theorem example90_valid : example90.Valid :=
  example90.valid_of_check (by decide)

theorem example56_semigroup : IsNumericalSemigroup example56.Mem :=
  example56.numericalSemigroup example56_valid

theorem example90_semigroup : IsNumericalSemigroup example90.Mem :=
  example90.numericalSemigroup example90_valid

theorem example56_multiplicity : example56.IsMultiplicity 14 :=
  example56.multiplicity_of_check (by decide)

theorem example90_multiplicity : example90.IsMultiplicity 19 :=
  example90.multiplicity_of_check (by decide)

theorem example56_counts :
    example56.leftCount = 13 ∧ example56.leftPrimitiveCount = 3 ∧
    example56.rightPrimitiveCount 14 = 4 := by decide

theorem example90_counts :
    example90.leftCount = 23 ∧ example90.leftPrimitiveCount = 3 ∧
    example90.rightPrimitiveCount 19 = 4 := by decide

theorem example56_eliahou : example56.eliahou 14 = -1 := by decide
theorem example90_eliahou : example90.eliahou 19 = -1 := by decide

end Eliahou

#print axioms Eliahou.example56_semigroup
#print axioms Eliahou.example90_semigroup
#print axioms Eliahou.example56_multiplicity
#print axioms Eliahou.example90_multiplicity
#print axioms Eliahou.example56_counts
#print axioms Eliahou.example90_counts
#print axioms Eliahou.example56_eliahou
#print axioms Eliahou.example90_eliahou
