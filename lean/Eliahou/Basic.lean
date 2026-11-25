import Std

/-!
# Finite presentations of cofinite additive subsets of the natural numbers

This module makes no claim to prove Bacher's conjecture.  A presentation
consists of a finite prefix and a cutoff, followed by the entire infinite
tail.  The cutoff is not required to be the least conductor.
-/

namespace Eliahou

structure Presentation where
  cutoff : Nat
  elements : List Nat
  deriving Repr

def Presentation.contains (p : Presentation) (n : Nat) : Bool :=
  p.elements.contains n || decide (p.cutoff ≤ n)

def Presentation.Mem (p : Presentation) (n : Nat) : Prop :=
  p.contains n = true

instance (p : Presentation) (n : Nat) : Decidable (p.Mem n) :=
  inferInstanceAs (Decidable (p.contains n = true))

def IsNumericalSemigroup (mem : Nat → Prop) : Prop :=
  mem 0 ∧ (∀ a b, mem a → mem b → mem (a + b)) ∧
    ∃ c, ∀ n, c ≤ n → mem n

def Presentation.Valid (p : Presentation) : Prop :=
  p.Mem 0 ∧ ∀ a b, a < p.cutoff → b < p.cutoff →
    p.Mem a → p.Mem b → a + b < p.cutoff → p.Mem (a + b)

def Presentation.CheckValid (p : Presentation) : Prop :=
  p.Mem 0 ∧ ∀ a b : Fin p.cutoff,
    p.Mem a.val → p.Mem b.val → a.val + b.val < p.cutoff → p.Mem (a.val + b.val)

instance (p : Presentation) : Decidable p.CheckValid := by
  unfold Presentation.CheckValid
  infer_instance

theorem Presentation.valid_of_check (p : Presentation) (h : p.CheckValid) : p.Valid := by
  refine ⟨h.1, ?_⟩
  intro a b ha hb hma hmb hab
  exact h.2 ⟨a, ha⟩ ⟨b, hb⟩ hma hmb hab

theorem Presentation.mem_of_cutoff_le (p : Presentation) {n : Nat}
    (hn : p.cutoff ≤ n) : p.Mem n := by
  simp [Mem, contains, hn]

theorem Presentation.numericalSemigroup (p : Presentation) (hp : p.Valid) :
    IsNumericalSemigroup p.Mem := by
  refine ⟨hp.1, ?_, p.cutoff, ?_⟩
  · intro a b ha hb
    by_cases h : p.cutoff ≤ a + b
    · exact p.mem_of_cutoff_le h
    · have hab : a + b < p.cutoff := Nat.lt_of_not_ge h
      have ha' : a < p.cutoff := Nat.lt_of_le_of_lt (Nat.le_add_right a b) hab
      have hb' : b < p.cutoff := Nat.lt_of_le_of_lt (Nat.le_add_left b a) hab
      exact hp.2 a b ha' hb' ha hb hab
  · intro n hn
    exact p.mem_of_cutoff_le hn

/-- A primitive element is positive, belongs to the set, and is not a sum
of two positive members.  This test is finite for every candidate. -/
def Presentation.primitive (p : Presentation) (n : Nat) : Bool :=
  decide (0 < n) && p.contains n &&
    (List.range n).all (fun a =>
      !(decide (0 < a) && p.contains a && p.contains (n - a)))

def Presentation.leftCount (p : Presentation) : Nat :=
  ((List.range p.cutoff).filter p.contains).length

def Presentation.leftPrimitiveCount (p : Presentation) : Nat :=
  ((List.range p.cutoff).filter p.primitive).length

def Presentation.rightPrimitiveCount (p : Presentation) (m : Nat) : Nat :=
  ((List.range m).filter (fun i => p.primitive (p.cutoff + i))).length

/-- Integer-valued: negative values must never be truncated to zero. -/
def Presentation.eliahou (p : Presentation) (m : Nat) : Int :=
  (p.leftCount : Int) * (p.leftPrimitiveCount : Int) +
    (((p.cutoff + m - 1) / m : Nat) : Int) *
      (p.rightPrimitiveCount m : Int) - (p.cutoff : Int)

/-- `m` is supplied to the executable invariant, but its mathematical
meaning must be established independently before using that invariant. -/
def Presentation.IsMultiplicity (p : Presentation) (m : Nat) : Prop :=
  0 < m ∧ p.Mem m ∧ ∀ n, 0 < n → n < m → ¬ p.Mem n

def Presentation.CheckMultiplicity (p : Presentation) (m : Nat) : Prop :=
  0 < m ∧ p.Mem m ∧ ∀ n : Fin m, 0 < n.val → ¬ p.Mem n.val

instance (p : Presentation) (m : Nat) : Decidable (p.CheckMultiplicity m) := by
  unfold Presentation.CheckMultiplicity
  infer_instance

theorem Presentation.multiplicity_of_check (p : Presentation) {m : Nat}
    (h : p.CheckMultiplicity m) : p.IsMultiplicity m := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro n hn hnm
  exact h.2.2 ⟨n, hnm⟩ hn

end Eliahou
