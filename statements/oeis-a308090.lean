import Mathlib

/-!
# A308090: a(n) = gcd(2^n + n!, 3^n + n!, n + 1)

Source: https://oeis.org/A308090
Credit: @AkiRA-COM-FP

Formalizes the converse conjecture of OEIS A308090 (offset 1): for every `n >= 1`, if
`gcd(2^n + n!, 3^n + n!, n + 1) = n + 1`, then `n + 1` is prime.
-/

namespace OMA.S_oeis_a308090

/-- The OEIS sequence A308090: `a(n) = gcd(2^n + n!, 3^n + n!, n + 1)`. -/
def a (n : ℕ) : ℕ :=
  Nat.gcd (Nat.gcd (2 ^ n + n.factorial) (3 ^ n + n.factorial)) (n + 1)

/-- For every `n >= 1`, if `a(n) = n + 1` then `n + 1` is prime. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = n + 1 → (n + 1).Prime := by
  sorry

end OMA.S_oeis_a308090
