import Mathlib

/-!
# A352844: Smallest k > 1 such that sopfr(k) - tau(k) = n, or -1 if no such k exists

Source: https://oeis.org/A352844
Credit: @AkiRA-COM-FP

Formalizes the OEIS A352844 conjecture (offset 0): there is no `-1` in this sequence, i.e.
for every `n : ℕ` there exists `k > 1` with `sopfr(k) - tau(k) = n`.
-/

namespace OMA.S_oeis_a352844

/-- Sum of prime factors of `k` counted with multiplicity (OEIS A001414). -/
def sopfr (k : ℕ) : ℕ :=
  ∑ p ∈ k.primeFactors, p * k.factorization p

/-- For every `n >= 0`, there exists `k > 1` with `sopfr(k) - tau(k) = n`. -/
theorem main :
    ∀ n : ℕ, ∃ k : ℕ, 1 < k ∧ (sopfr k : ℤ) - (k.divisors.card : ℤ) = (n : ℤ) := by
  sorry

end OMA.S_oeis_a352844
