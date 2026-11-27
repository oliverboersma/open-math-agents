import Mathlib.Data.Nat.Choose.Basic

/-!
# OEIS A385736

Felix Huber asks which triangular numbers are perimeters of nondegenerate
triangles with triangular sides. The three strict triangle inequalities
ensure that the sides are positive and exclude collinear triangles.

Source: https://oeis.org/A385736
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a385736

def triangular (n : ℕ) : ℕ := (n + 1).choose 2

def fits (p i j k : ℕ) : Prop :=
  let x := triangular i
  let y := triangular j
  let z := triangular k
  x + y + z = p ∧ z < x + y ∧ y < x + z ∧ x < y + z

def perimeter (p : ℕ) : Prop := ∃ i j k : ℕ, fits p i j k

def exceptional (p : ℕ) : Prop := p = 0 ∨ p = 1 ∨ p = 6 ∨ p = 10 ∨ p = 28 ∨ p = 55

theorem main : ∀ n : ℕ, ¬ perimeter (triangular n) ↔ exceptional (triangular n) := by
  sorry

end OMA.S_oeis_a385736
