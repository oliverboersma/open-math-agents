import Mathlib

/-!
# Counting words on five symbols that avoid two consecutive patterns

Source: https://oeis.org/A243513
Credit: @jatin6

R. H. Hardin defined the sequence with offset one. Colin Barker conjectured
both its closed form and its ordinary generating function.
-/

namespace OMA.S_oeis_a243513

/-- Each nonzero symbol has its predecessor somewhere to its left. After two
distinct successive symbols, the next symbol must differ from both. -/
def validWord {length : ℕ} (w : Fin length → Fin 5) : Prop :=
  (∀ i, 0 < (w i).val → ∃ j, j < i ∧ (w j).val + 1 = (w i).val) ∧
  (∀ i j k : Fin length, j.val = i.val + 1 → k.val = j.val + 1 →
    w i ≠ w j → w k ≠ w i ∧ w k ≠ w j)

noncomputable def count (n : ℕ) : ℕ :=
  Nat.card {w : Fin (n + 2) → Fin 5 // validWord w}

/-- The OEIS series starts at degree one. -/
noncomputable def series : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (count n : ℚ))

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → 4 * count n = 7 + 3 ^ n + 2 * n) ∧
    series * ((1 - X) ^ 2 * (1 - 3 * X)) = X * (3 - 10 * X + 6 * X ^ 2) := by
  sorry

end OMA.S_oeis_a243513

