import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic

/-!
# Equal counts of 000 and 001 in OEIS A164137

Source: https://oeis.org/A164137 (OEIS Foundation, CC BY-SA 4.0).
Formalization: @sturdy4days.

An occurrence is counted at its starting position, so occurrences may
contribute even when they overlap. Clearing the positive denominator in
Robert P. P. McKone's conjecture gives an equation over the integers.
-/

namespace OMA.S_oeis_a164137

def occurrences (w : List Bool) (lastBit : Bool) : ℕ :=
  (List.range w.length).countP fun i =>
    (w[i]? == some false) && (w[i + 1]? == some false) && (w[i + 2]? == some lastBit)

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun w : Fin n → Bool =>
    occurrences (List.ofFn w) false = occurrences (List.ofFn w) true).card

theorem main : ∀ n : ℕ, 10 ≤ n →
    let m : ℤ := n
    let b : ℕ → ℤ := fun k => a k
    m * b n =
      (8 * m - 72) * b (n - 10) + (20 * m - 160) * b (n - 9) +
      (6 * m - 26) * b (n - 8) + (46 - 5 * m) * b (n - 7) -
      16 * b (n - 6) + (56 - 11 * m) * b (n - 5) + (12 - m) * b (n - 4) +
      (m - 18) * b (n - 3) + m * b (n - 2) + 2 * m * b (n - 1) := by
  sorry

end OMA.S_oeis_a164137
