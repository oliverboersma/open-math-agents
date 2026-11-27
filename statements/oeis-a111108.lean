import Mathlib

/-!
# A111108: a(n) = A001333(n) - (-2)^(n-1), n > 0

Source: https://oeis.org/A111108
Credit: @xor2k

Formalizes the OEIS A111108 conjecture (offset 1): for odd primes p, p divides a(p).

Conventions: A001333 (offset 0) is given by its defining recurrence
`A001333(0) = A001333(1) = 1`, `A001333(n) = 2*A001333(n-1) + A001333(n-2)`, computed in `ℤ`.
The sequence `a(n) = A001333(n) - (-2)^(n-1)` is defined in `ℤ` for `n ≥ 1` (the value at the
unused index `0` is irrelevant). Odd primes are primes `p` with `p ≠ 2`, and the divisibility
is integer divisibility `(p : ℤ) ∣ a p`.
-/

namespace OMA.S_oeis_a111108

/-- A001333: `1, 1, 3, 7, 17, 41, ...`, with `A001333(n) = 2*A001333(n-1) + A001333(n-2)`. -/
def A001333 : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * A001333 (n + 1) + A001333 n

/-- `a(n) = A001333(n) - (-2)^(n-1)` (used for `n ≥ 1`). -/
def a (n : ℕ) : ℤ :=
  A001333 n - (-2) ^ (n - 1)

/-- For every odd prime `p`, `p` divides `a(p)`. -/
theorem main :
    ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ a p := by
  sorry

end OMA.S_oeis_a111108
