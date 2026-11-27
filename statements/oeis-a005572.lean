/-
OEIS A005572, Peter Bala's generating function and parity conjecture.
Reference: https://oeis.org/A005572
Credit: @Heart-galaxy
Text credit: OEIS Foundation, CC BY-SA 4.0.

The definitions use John W. Layman's published recurrence, including a(0) = 1.
The Catalan series is the ordinary generating series for the Catalan numbers.
The inverse in the generating function is taken over the rationals.
-/

import Mathlib

namespace OMA.S_oeis_a005572

open Finset PowerSeries

/-- Layman's recurrence, with the empty sum at index 1 evaluated separately. -/
def a : (n : ℕ) → ℕ
  | 0 => 1
  | 1 => 4
  | n + 2 => 4 * a (n + 1) +
      ∑ i ∈ (range (n + 1)).attach, a i * a (n - i)
termination_by n => n
decreasing_by
  all_goals first | omega | (have hi := mem_range.mp i.property; omega)

noncomputable def generatingSeries : PowerSeries ℚ := mk (fun n => (a n : ℚ))

noncomputable def catalanGF : PowerSeries ℚ := map (Nat.castRingHom ℚ) catalanSeries

noncomputable def denominator : PowerSeries ℚ := 1 - 2 * X

noncomputable def innerSeries : PowerSeries ℚ := X * denominator⁻¹

noncomputable def catalanComposition : PowerSeries ℚ := catalanGF.subst innerSeries

theorem main :
    generatingSeries = denominator⁻¹ * catalanComposition ^ 2 ∧
    (∀ n : ℕ, Even (a n) ↔ ¬ ∃ k : ℕ, n = 2 * (2 ^ k - 1)) := by
  sorry

end OMA.S_oeis_a005572
