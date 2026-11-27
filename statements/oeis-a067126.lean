import Mathlib

/-!
# A067126: Numbers for which phi(n) >= phi(k) for all k = 1 to n-1.

Source: https://oeis.org/A067126
Credit: @darealpandaboi

Conjecture: 4 and 9 are the only composite terms.

Translation notes.
* phi is Euler's totient, Nat.totient. n is a term when totient k <= totient n for every k
  with 1 <= k <= n - 1.
* A composite number is an n > 1 that is not prime.
* This reading reproduces the listed data 1, 2, 3, 4, 5, 7, 9, 11, 13, 17, 19, 23, ..., and
  its composite terms up to 20000 are exactly 4 and 9 (checked by computer).
-/

namespace OMA.S_oeis_a067126

/-- n is in A067126: totient n >= totient k for all 1 <= k < n. -/
def IsTerm (n : ℕ) : Prop := ∀ k : ℕ, 1 ≤ k → k < n → Nat.totient k ≤ Nat.totient n

theorem main : ∀ n : ℕ, IsTerm n → 1 < n → ¬ n.Prime → n = 4 ∨ n = 9 := by
  sorry

end OMA.S_oeis_a067126
