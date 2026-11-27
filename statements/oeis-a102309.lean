import Mathlib

/-!
# A102309: a(n) = Sum_{d divides n} moebius(d) * binomial(n/d,2).

Source: https://oeis.org/A102309
Credit: @ShoQo

Conjecture: "Also apparently, the first differences of A100448 (checked up to n=2000)."
(Sela Fried, Mar 15 2026: "The conjectured relation to A100448 is true.")

Formalization notes:
* Offset 0: a(n) = Σ_{d ∣ n} μ(d) C(n/d, 2) (data: 0, 0, 1, 3, 5, 10, ...; a(0) = 0 as the
  empty sum).
* A100448(n) is the number of triples (i, j, k) with 1 ≤ i ≤ j < k ≤ n and gcd(i, j, k) = 1
  (data from n = 1: 0, 1, 4, 9, 19, ...); A100448(0) = 0.
* "First differences": a(n) = A100448(n) - A100448(n-1) for n ≥ 1, matching the data
  (1 - 0 = a(2), 4 - 1 = a(3), ..., and a(1) = 0 - 0).
-/

namespace OMA.S_oeis_a102309

/-- a(n) = Σ_{d ∣ n} μ(d) C(n/d, 2). -/
def a (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) * ((n / d).choose 2 : ℤ)

/-- A100448(n): triples 1 ≤ i ≤ j < k ≤ n with gcd(i, j, k) = 1. -/
def A100448 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t : ℕ × ℕ × ℕ => t.1 ≤ t.2.1 ∧ t.2.1 < t.2.2 ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1)).card

theorem main : ∀ n : ℕ, 1 ≤ n → a n = (A100448 n : ℤ) - A100448 (n - 1) := by
  sorry

end OMA.S_oeis_a102309
