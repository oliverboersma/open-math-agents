import Mathlib.Data.Nat.GCD.Basic

/-!
# OEIS A392943

A primitive Heronian triangle has positive integer side lengths with gcd one
and positive integer area K. Heron's formula is written with integer factors
to avoid truncated subtraction. Its circumradius R satisfies 4RK = abc.

Source: https://oeis.org/A392943
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a392943

def hasArea (a b c K : ℕ) : Prop :=
  let x := (a : ℤ)
  let y := (b : ℤ)
  let z := (c : ℤ)
  (4 * (K : ℤ)) ^ 2 = (x + y + z) * (-x + y + z) * (x - y + z) * (x + y - z)

theorem main : ¬ ∃ a b c K R : ℕ,
    0 < a ∧ 0 < b ∧ 0 < c ∧ a < b + c ∧ b < a + c ∧ c < a + b ∧
    Nat.gcd (Nat.gcd a b) c = 1 ∧ 0 < K ∧ hasArea a b c K ∧
    0 < R ∧ 4 * R * K = a * b * c := by
  sorry

end OMA.S_oeis_a392943
