import Mathlib

/-!
# ON cells in Wolfram's rule 3

Source: https://oeis.org/A266072 (OEIS Foundation, CC BY-SA 4.0).
The sequence was submitted by Robert Price. Its two sequence identities are
due to Colin Barker and its generating function to Michael De Vlieger.
Formalization by @anmolspace.

The array starts at time zero with a single ON cell at site zero. As in the
entry's displayed rows and Mathematica program, row `n` counts just sites
`-n` through `n`, while the update acts on the entire integer line. The
quotient of formal power series is written after clearing its denominator,
whose constant coefficient is one.
-/

namespace OMA.S_oeis_a266072

/-- Elementary rule 3, with the left, central, and right bits in Wolfram order. -/
def update (left center right : Bool) : Bool :=
  (3 : ℕ).testBit (4 * left.toNat + 2 * center.toNat + right.toNat)

/-- The state of site `i` at time `n`. -/
def cell : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => update (cell n (i - 1)) (cell n i) (cell n (i + 1))

/-- Number of ON cells in the displayed row of width `2 * n + 1`. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell n ((j : ℤ) - n) then 1 else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, a n = (n : ℤ) - (-1 : ℤ) ^ n * ((n : ℤ) - 1)) ∧
    (∀ n : ℕ, 3 < n → a n = 2 * a (n - 2) - a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (-1 + X ^ 2) ^ 2 = 1 + X - X ^ 2 + 3 * X ^ 3) := by
  sorry

end OMA.S_oeis_a266072
