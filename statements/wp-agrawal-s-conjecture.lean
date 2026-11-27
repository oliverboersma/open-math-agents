import Mathlib

/-!
# Agrawal's conjecture

Source: https://en.wikipedia.org/wiki/Agrawal's_conjecture
Credit: @sntntHb

Agrawal's conjecture: let `n` and `r` be coprime positive integers. If
`(X - 1)^n ≡ X^n - 1 (mod n, X^r - 1)`, then either `n` is prime or `n^2 ≡ 1 (mod r)`.

Conventions:
- A congruence of integer polynomials modulo the ideal `(n, X^r - 1)` of `ℤ[X]` is the same as
  divisibility by `X^r - 1` after reducing the coefficients modulo `n`, i.e. in `(ZMod n)[X]`.
  The statement is phrased that way.
-/

namespace OMA.S_wp_agrawal_s_conjecture

open Polynomial

theorem main :
    ∀ n r : ℕ, 0 < n → 0 < r → Nat.Coprime n r →
      ((X : (ZMod n)[X]) ^ r - 1) ∣ (X - 1) ^ n - (X ^ n - 1) →
      n.Prime ∨ n ^ 2 ≡ 1 [MOD r] := by
  sorry

end OMA.S_wp_agrawal_s_conjecture
