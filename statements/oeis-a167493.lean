import Mathlib

/-!
# Two conjectures on the differences of OEIS A167493

Source: https://oeis.org/A167493 (OEIS Foundation, CC BY-SA 4.0).
The sequence starts at index 1. A difference record is strictly greater
than every earlier difference at an index at least 2. The second conjecture
requires each record greater than 3 to be the larger member of a twin-prime pair.
-/

namespace OMA.S_oeis_a167493

def step (n prev : ℕ) : ℕ :=
  prev + if n % 2 = 1 then n.gcd prev else (n - 2).gcd prev

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 => step (n + 2) (a (n + 1))

def difference (n : ℕ) : ℕ := a n - a (n - 1)

theorem main :
    (∀ n : ℕ, 2 ≤ n → (difference n = 1 ∨ (difference n).Prime)) ∧
      ∀ n : ℕ, 2 ≤ n → 3 < difference n →
        (∀ j : ℕ, 2 ≤ j → j < n → difference j < difference n) →
        (difference n).Prime ∧ (difference n - 2).Prime := by
  sorry

end OMA.S_oeis_a167493
