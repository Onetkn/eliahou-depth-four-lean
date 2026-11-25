import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Basic

/-! Semantic definitions for the uniform depth-four theorem.
The cutoff is `3 * m + h`; it need not be the least conductor.
-/

namespace Eliahou.DepthFour

structure Admissible (S : Set ℕ) (m d h : ℕ) : Prop where
  m_pos : 0 < m
  d_pos : 0 < d
  d_lt_m : d < m
  h_pos : 0 < h
  h_le_m : h ≤ m
  zero_mem : 0 ∈ S
  add_mem : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S
  lower : ∀ n, n ∈ S → 0 < n → m ≤ n
  first : ∀ n, m ≤ n → n < 2 * m → (n ∈ S ↔ n = m ∨ n = m + d)
  tail : ∀ n, 3 * m + h ≤ n → n ∈ S

def Decomposable (S : Set ℕ) (n : ℕ) : Prop :=
  ∃ x ∈ S, ∃ y ∈ S, 0 < x ∧ 0 < y ∧ x + y = n

def Primitive (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ 0 < n ∧ ¬ Decomposable S n

def Base (m d n : ℕ) : Prop :=
  ∃ i j : ℕ, n = i * m + j * (m + d)

noncomputable section

open Classical

def left (S : Set ℕ) (m h : ℕ) : Finset ℕ :=
  (Finset.range (3 * m + h)).filter (· ∈ S)

def leftPrims (S : Set ℕ) (m h : ℕ) : Finset ℕ :=
  (Finset.range (3 * m + h)).filter (Primitive S)

def rightDecomp (S : Set ℕ) (m h : ℕ) : Finset ℕ :=
  (Finset.Ico (3 * m + h) (4 * m + h)).filter (Decomposable S)

def baseLeft (m d h : ℕ) : Finset ℕ :=
  (Finset.range (3 * m + h)).filter (Base m d)

def baseRight (m d h : ℕ) : Finset ℕ :=
  (Finset.Ico (3 * m + h) (4 * m + h)).filter (Base m d)

def middlePrims (S : Set ℕ) (m h : ℕ) : Finset ℕ :=
  (Finset.Ico (2 * m) (2 * m + h)).filter (Primitive S)

def terminalPrims (S : Set ℕ) (m h : ℕ) : Finset ℕ :=
  (Finset.Ico (2 * m + h) (3 * m + h)).filter (Primitive S)

def middleOffsets (S : Set ℕ) (m h : ℕ) : Finset ℕ :=
  (middlePrims S m h).image (fun n => n - 2 * m)

def eliahou (S : Set ℕ) (m h : ℕ) : ℤ :=
  ((leftPrims S m h).card : ℤ) * ((left S m h).card : ℤ) -
    4 * ((rightDecomp S m h).card : ℤ) + ((m : ℤ) - h)

end

end Eliahou.DepthFour
