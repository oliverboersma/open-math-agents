import Mathlib

/-!
# A131401: Least number dividing Fibonacci(n) but not dividing Fibonacci(m) for m < n, or 0 if there is no such number.

Source: https://oeis.org/A131401
Credit: @bnb9001

The sequence has offset 1 (1, 0, 2, 3, 5, 4, 13, ...). The smaller indices are `1 ≤ m < n`, as
in the entry (a(2) = 0 because Fibonacci(1) = Fibonacci(2) = 1); `Nat.fib 0 = 0` is not
compared. The least such number is `sInf`, which is `0` exactly when there is none.

Conjecture: only a(2) = 0. The entry notes that the conjecture is true.
-/

namespace OMA.S_oeis_a131401

/-- The least `d` dividing `fib n` but no `fib m` with `1 ≤ m < n`, or `0` if there is none. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {d : ℕ | d ∣ Nat.fib n ∧ ∀ m : ℕ, 1 ≤ m → m < n → ¬ d ∣ Nat.fib m}

/-- For `n ≥ 1`, `a n = 0` exactly when `n = 2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 2) := by
  sorry

end OMA.S_oeis_a131401
