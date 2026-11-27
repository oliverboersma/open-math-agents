import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Dist

/-!
# Fixed points of the 1089 trick

Remco Havenaar's uniqueness conjecture for OEIS A393794. Decimal reversal
drops leading zeroes in the reversed string. The source gives the proposed
term explicitly and takes the index to start at one.

Source: https://oeis.org/A393794
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a393794

def reverse10 (x : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 x).reverse

def step (x : ℕ) : ℕ :=
  let difference := Nat.dist x (reverse10 x)
  difference + reverse10 difference

def term (n : ℕ) : ℕ := 110 * (10 ^ (n + 1) - 1)

/-- The fixed points with exactly `n + 4` digits consist of the listed term alone. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ x : ℕ,
    (10 ^ (n + 3) ≤ x ∧ x < 10 ^ (n + 4) ∧ step x = x) ↔ x = term n := by
  sorry

end OMA.S_oeis_a393794
