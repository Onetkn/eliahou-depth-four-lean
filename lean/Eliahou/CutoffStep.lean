import Std

/-!
# Algebra for one-step cutoff changes

These are algebraic auxiliary lemmas, not a formalization of the entire
semigroup cutoff-monotonicity theorem.  The counting identities and sign
hypotheses must still be derived from semigroup semantics when applying them.
No novelty is claimed.
-/

namespace Eliahou

def invariant (k ell q r c : Int) : Int := k * ell + q * r - c

theorem decomposable_step_identity (k ell q r c delta : Int) :
    invariant (k + 1) ell (q + delta) r (c + 1) - invariant k ell q r c =
      ell - 1 + delta * r := by
  simp only [invariant, Int.add_mul, Int.one_mul]
  omega

theorem primitive_step_identity (k ell q r c delta : Int) :
    invariant (k + 1) (ell + 1) (q + delta) (r - 1) (c + 1) -
        invariant k ell q r c =
      k + ell - q + delta * (r - 1) := by
  simp only [invariant, Int.add_mul, Int.mul_add, Int.mul_sub,
    Int.one_mul, Int.mul_one]
  omega

theorem decomposable_step_nondecreasing (k ell q r c delta : Int)
    (hell : 1 ≤ ell) (hr : 0 ≤ r) (hd : 0 ≤ delta) :
    invariant k ell q r c ≤ invariant (k + 1) ell (q + delta) r (c + 1) := by
  have h := decomposable_step_identity k ell q r c delta
  have hp : 0 ≤ delta * r := Int.mul_nonneg hd hr
  omega

theorem primitive_step_nondecreasing (k ell q r c delta : Int)
    (hkq : q ≤ k) (hell : 0 ≤ ell) (hr : 1 ≤ r) (hd : 0 ≤ delta) :
    invariant k ell q r c ≤
      invariant (k + 1) (ell + 1) (q + delta) (r - 1) (c + 1) := by
  have h := primitive_step_identity k ell q r c delta
  have hr' : 0 ≤ r - 1 := by omega
  have hp : 0 ≤ delta * (r - 1) := Int.mul_nonneg hd hr'
  omega

end Eliahou

#print axioms Eliahou.decomposable_step_identity
#print axioms Eliahou.primitive_step_identity
#print axioms Eliahou.decomposable_step_nondecreasing
#print axioms Eliahou.primitive_step_nondecreasing
