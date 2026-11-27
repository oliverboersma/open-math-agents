import Mathlib

/-!
# A000657: Eventual periodicity of the median Euler numbers

Source: https://oeis.org/A000657, conjecture by Peter Bala (May 8, 2023).
The median Euler numbers are the central entries of the Entringer triangle A008280.
-/

namespace OMA.S_oeis_a000657

/-- Entringer rows, read from the zero end after the initial row. -/
def entringerRow : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => (entringerRow n).reverse.scanl (· + ·) 0

/-- The middle entry of row `2 * n` is independent of the row orientation. -/
def medianEuler (n : ℕ) : ℕ := (entringerRow (2 * n)).getD n 0

/-- From some index onward, the residues have a positive period dividing the totient. -/
theorem main :
    ∀ modulus : ℕ, 0 < modulus → ∃ start period : ℕ, 0 < period ∧ period ∣ modulus.totient ∧
      ∀ n : ℕ, start ≤ n → Nat.ModEq modulus (medianEuler (n + period)) (medianEuler n) := by
  sorry

end OMA.S_oeis_a000657
