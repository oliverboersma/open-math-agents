import Mathlib

/-!
# A102395: A mod 2 related Jacobsthal sequence.

Source: https://oeis.org/A102395
Credit: @ShoQo

Conjecture: "all the terms are in A078008." (Paul Barry, Jan 07 2005: "The conjecture is true
since a(n) = A078008(A000120(n)).")

Formalization notes:
* Offset 0, a(n) = Sum_{k=0..n} [n+k ≡ 0 (mod 3)] (C(n,k) mod 2), the entry's formula
  (data: 1, 0, 0, 2, 0, 2, 2, 2, ...).
* A078008 is the expansion of (1-x)/((1+x)(1-2x)) = (1-x)/(1-x-2x^2), i.e. b(0) = 1, b(1) = 0,
  b(n+2) = b(n+1) + 2 b(n) (data: 1, 0, 2, 2, 6, 10, 22, ...).
-/

namespace OMA.S_oeis_a102395

/-- a(n) = Σ_{k ≤ n, n+k ≡ 0 (mod 3)} (C(n,k) mod 2). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if (n + k) % 3 = 0 then n.choose k % 2 else 0

/-- A078008: b(0) = 1, b(1) = 0, b(n+2) = b(n+1) + 2 b(n). -/
def A078008 : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | (n + 2) => A078008 (n + 1) + 2 * A078008 n

theorem main : ∀ n : ℕ, ∃ m : ℕ, a n = A078008 m := by
  sorry

end OMA.S_oeis_a102395
