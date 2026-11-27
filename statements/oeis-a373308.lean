import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Int.ModEq

/-!
# The cube of the signed Thue–Morse generating function

Source: https://oeis.org/A373308 (Paul D. Hanna, OEIS Foundation, CC BY-SA 4.0).
For the coefficient of x^n, all factors after the first n+1 have no effect.
A001285 gives 1 or 2 according as the sum of the binary digits is even or odd.
A000695 lists the numbers whose base-four digits are all zero or one, beginning
with zero. The equation n+1=3b automatically excludes b=0.
-/

namespace OMA.S_oeis_a373308

open Polynomial

noncomputable def truncation (d : ℕ) : Polynomial ℤ := ∏ j ∈ Finset.range d, (1-X^(2^j))^3

noncomputable def a (n : ℕ) : ℤ := (truncation (n+1)).coeff n

def thue (n : ℕ) : ℤ := (-1)^((Nat.digits 2 n).sum)

def zeroIndex (m : ℕ) : Prop := ∃ b : ℕ, m=3*b ∧ ∀ t ∈ Nat.digits 4 b, t ≤ 1

theorem main : (∀ n : ℕ, a (3*n) ≡ thue n [ZMOD 3] ∧ 3 ∣ a (3*n+1) ∧ 3 ∣ a (3*n+2)) ∧
    (∀ n : ℕ, a n = 0 ↔ zeroIndex (n+1)) := by
  sorry

end OMA.S_oeis_a373308
