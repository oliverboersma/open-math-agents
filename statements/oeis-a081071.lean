import Mathlib

/-!
# A081071: a(n) = Lucas(4*n+2)-2 = Lucas(2*n+1)^2.

Source: https://oeis.org/A081071
Credit: @ShoQo

Conjecture (Alex Ratushnyak, May 06 2012): a(n) = Fibonacci(4*n+3) + Sum_{k=2..2*n}
Fibonacci(2*k). (Nguyen Tuan Anh, Aug 02 2025: "The above conjecture is true for n >= 1.")

Formalization notes:
* Offset 0, with `a n = Lucas(4n+2) - 2` (data: 1, 16, 121, ...). Lucas numbers: L(0) = 2,
  L(1) = 1, L(n+2) = L(n+1) + L(n). Fibonacci numbers are Mathlib's `Nat.fib`.
* At n = 0 the right-hand side is F(3) = 2 while a(0) = 1, so the identity is stated for
  `n ≥ 1`, the range in which the entry records it as true.
-/

namespace OMA.S_oeis_a081071

/-- The Lucas numbers: L(0) = 2, L(1) = 1, L(n+2) = L(n+1) + L(n). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- a(n) = Lucas(4n+2) - 2. -/
def a (n : ℕ) : ℕ := lucas (4 * n + 2) - 2

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = Nat.fib (4 * n + 3) + ∑ k ∈ Finset.Icc 2 (2 * n), Nat.fib (2 * k) := by
  sorry

end OMA.S_oeis_a081071
