import Mathlib

/-!
# A204988: The index j < k such that n divides 2^k - 2^j, where k is the least index (A204987) for which such j exists.

Source: https://oeis.org/A204988
Credit: @bnb9001

The sequence has offset 1. As in the entry, the indices satisfy `1 ≤ j < k`. `kmin n` is the
least `k` admitting such a `j` (A204987), and `a n` is the `j` that goes with it, taken as the
least one (it is in fact unique).

Conjecture (Velin Yanev, 2016): a(n) = A007814(n) + (1 - (-1)^n)/2, where A007814(n) is the
2-adic valuation of n; the second term is 1 for odd n and 0 for even n. Andrew Howroyd notes that
the conjecture is true.
-/

namespace OMA.S_oeis_a204988

/-- A204987: the least `k` such that `n ∣ 2 ^ k - 2 ^ j` for some `1 ≤ j < k`. -/
noncomputable def kmin (n : ℕ) : ℕ := sInf {k : ℕ | ∃ j, 1 ≤ j ∧ j < k ∧ n ∣ 2 ^ k - 2 ^ j}

/-- A204988: the index `j` with `1 ≤ j < kmin n` and `n ∣ 2 ^ kmin n - 2 ^ j`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧ j < kmin n ∧ n ∣ 2 ^ kmin n - 2 ^ j}

/-- For every `n ≥ 1`, `a n = v₂(n) + (1 if n is odd, else 0)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = padicValNat 2 n + (if n % 2 = 1 then 1 else 0) := by
  sorry

end OMA.S_oeis_a204988
