import Mathlib

/-!
# Sums of prime counts at triangular numbers and squares (OEIS A262999)

Source: https://oeis.org/A262999 (Zhi-Wei Sun, OEIS Foundation, CC BY-SA 4.0).

A262999(n) is the number of ordered pairs (k, m) with k > 0 and m > 0 such that
n = pi(k(k+1)/2) + pi(m^2), where pi is the prime counting function.

Conjecture (in the entry): a(n) > 0 for all n > 1, and a(n) = 1 only for
n = 3, 5, 7, 35, 37, 217, 7439, 10381.

The entry's own example line shows a(590) = 1, while the printed list omits 590; we read the
omission as a typo and include 590 in the exceptional list, so that the statement is not
refuted by that discrepancy alone.
-/

namespace OMA.S_oeis_a262999

/-- The representations of `n` counted by A262999. The search range k, m <= 2n + 2 contains
every representation: for j >= 2 both pi(j(j+1)/2) and pi(j^2) are at least j/2, so a larger
coordinate would already make the sum exceed n. -/
def pairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (2 * n + 2)) ×ˢ (Finset.Icc 1 (2 * n + 2))).filter
    (fun km => Nat.primeCounting (km.1 * (km.1 + 1) / 2) + Nat.primeCounting (km.2 ^ 2) = n)

/-- A262999(n). -/
def a (n : ℕ) : ℕ := (pairs n).card

/-- Sun's conjecture on A262999 (with 590 included in the exceptional list). -/
theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
      ∀ n : ℕ, a n = 1 → n ∈ ({3, 5, 7, 35, 37, 217, 590, 7439, 10381} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a262999
