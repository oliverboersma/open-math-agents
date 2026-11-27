import Mathlib

/-!
# OEIS A297402: gcd of prime-power inradii

For a positive exponent, take the gcd of the inradii `(p^n - 1)/2`
for the first `n` odd primes. The conjecture says this is already
a common divisor of those inradii for all odd primes.

Source: https://oeis.org/A297402
Formalization: @senamakel
-/

namespace OMA.S_oeis_a297402

/-- The inradius associated to the odd prime `p` and exponent `n`. -/
def term (n p : ℕ) : ℕ := (p ^ n - 1) / 2

/-- The gcd of the inradii from the first `n` odd primes. -/
noncomputable def initialGcd (n : ℕ) : ℕ :=
  (Finset.range n).gcd (fun i => term n (Nat.nth Nat.Prime (i + 1)))

-- Every common divisor over all odd primes divides the finite gcd.
-- The following reverse divisibility property therefore identifies that gcd.
theorem main : ∀ (n : ℕ), 0 < n → ∀ p : ℕ, p.Prime → p ≠ 2 →
    initialGcd n ∣ term n p := by
  sorry

end OMA.S_oeis_a297402
