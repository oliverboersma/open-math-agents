import Mathlib

/-!
# A271983: The smaller of a pair n, m such that phi(n) = phi(m) and there is no other k such that phi(n) = phi(k).

Source: https://oeis.org/A271983
Credit: @darealpandaboi

Conjecture: if phi(x) = N has exactly two solutions, x = n and x = m, say (see A007366),
then one of n and m is odd and the other even.

Translation notes.
* phi is Euler's totient, Nat.totient. Mathlib sets totient 0 = 0, and 0 is the only k with
  totient k = 0, so no pair involves 0 and quantifying over all k : ℕ changes nothing.
* phi(x) = N has exactly two solutions n and m: n /= m, both are solutions, and every
  solution is n or m.
* Checked by computer: for every N <= 400 with exactly two solutions (52 cases), one solution
  is odd and the other even; the smaller solutions start 1, 11, 23, 29, 31, 47, 53, 81, 59,
  matching the listed data.
-/

namespace OMA.S_oeis_a271983

theorem main : ∀ n m : ℕ, n ≠ m → Nat.totient n = Nat.totient m →
    (∀ k : ℕ, Nat.totient k = Nat.totient n → k = n ∨ k = m) →
    (Odd n ∧ Even m) ∨ (Even n ∧ Odd m) := by
  sorry

end OMA.S_oeis_a271983
