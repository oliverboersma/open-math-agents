import Mathlib

/-!
# OEIS A247339: some m <= n has gpf(m^2+1) equal to the least prime factor of n^2+1

Source: https://oeis.org/A247339 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A247339 (Michel Lagneau, Sep 14 2014), offset 1: a(n) is the least number k such that the
greatest prime divisor of k^2+1 is the smallest prime divisor of n^2+1. Comment: Conjecture: for
all integer n, there exists at least an integer m <= n such that the smallest prime factor of
n^2+1 is also the greatest prime factor of m^2+1. - Michel Lagneau, Sep 27 2015

Formalization notes:
* n ranges over the positive integers, the indices of the sequence (for n = 0, n^2+1 = 1 has no
  prime factor), and m over 1..n; the conjecture then says a(n) <= n.
* The smallest prime factor is `Nat.minFac`, and the greatest prime factor `gpf` is the largest
  element of `Nat.primeFactors`.
* Control from the entry's example a(34) = 5: gpf(5^2+1) = 13 = minFac(34^2+1).
-/

namespace OMA.S_oeis_a247339

/-- The greatest prime divisor of m (for m >= 2). -/
def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

/-- Lagneau's conjecture: for every n >= 1 some 1 <= m <= n has gpf(m^2+1) = minFac(n^2+1). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ m, 1 ≤ m ∧ m ≤ n ∧ gpf (m ^ 2 + 1) = Nat.minFac (n ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a247339
