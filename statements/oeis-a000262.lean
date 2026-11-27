import Mathlib

/-!
# Congruence periodicity of OEIS A000262

Source: https://oeis.org/A000262
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A000/A000262.seq
Credit: @Heart-galaxy

Peter Bala conjectured on November 14, 2017 that, for every k >= 2,
k divides a(n+k) - a(n), where a(n) counts sets of lists on n labels.
The OEIS entry reports on January 20, 2018 that this conjecture is true,
and refers to Bala's note:
https://oeis.org/A047974/a047974_1.pdf
This submission states the known result, rather than claiming a new proof.

The sequence is defined using the exact finite-sum formula recorded by
Francesca Aicardi on November 3, 2022, with the source's initial term a(0)=1.
The index n ranges over all natural numbers, matching the OEIS offset 0.
Natural-number congruence expresses divisibility of the integer difference
without using truncated natural-number subtraction.
-/

namespace OMA.S_oeis_a000262

/-- The number of sets of nonempty lists partitioning n labels (A000262),
using the source's formula `sum_{k=0..n-1} k! * C(n-1,k) * C(n,k)` for n > 0. -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k ∈ Finset.range (n + 1),
      Nat.factorial k * Nat.choose n k * Nat.choose (n + 1) k

/-- Bala's congruence, for every index and every modulus at least two. -/
theorem main :
    ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, Nat.ModEq k (a (n + k)) (a n) := by
  sorry

end OMA.S_oeis_a000262
