import Mathlib

/-!
# OEIS A071287: Peirce numerators of order 6

The stream follows Graham, Knuth and Patashnik, Concrete Mathematics,
second edition, exercise 64 on p. 151. At each source insertion site it
adds the new fraction and a separator in the order prescribed there.

The two source conjectures give the period-21 second-difference
recurrence and an ordinary generating function. The coefficient list below
includes the initial factor x^6 in the displayed numerator polynomial.
The source sequence starts at index 0.

Source: https://oeis.org/A071287
Conjecture: Colin Barker, March 29, 2017.
Formalization: @senamakel
-/

namespace OMA.S_oeis_a071287

inductive Symbol where
  | frac (num den : ℕ)
  | sep
  deriving DecidableEq

/-- Insert the two new symbols into each block of n old symbols. -/
def expandStream (n : ℕ) (old : ℕ → Symbol) (i : ℕ) : Symbol :=
  let q := i / (n + 2)
  let r := i % (n + 2)
  let j := (q + 1) * n
  if r + 1 < n then
    old (q * n + r)
  else if r + 1 = n then
    if j % 2 = 1 then Symbol.frac q (n + 1) else old (j - 1)
  else if r = n then
    if j % 2 = 1 then Symbol.sep else Symbol.frac q (n + 1)
  else
    old (j - 1)

/-- The infinite token stream defined by the original Peirce insertion rule. -/
def peirce : ℕ → ℕ → Symbol
  | 0, _ => Symbol.sep
  | 1, i => if i % 2 = 0 then Symbol.frac (i / 2) 1 else Symbol.sep
  | n + 2, i => expandStream (n + 1) (peirce (n + 1)) i

/-- Fraction numerators at even zero-based positions. -/
def numeratorAt (n i : ℕ) : ℕ :=
  match peirce n (2 * i) with
  | Symbol.frac a _ => a
  | Symbol.sep => 0

/-- Coefficient of p(x)/(1 - x^period)^2 using the geometric-series expansion. -/
def gfCoeff (period : ℕ) (p : List ℕ) (i : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (i + 1), p[k]! *
    (if (i - k) % period = 0 then (i - k) / period + 1 else 0)

theorem main :
  (∀ i : ℕ, (numeratorAt 6 (i + 42) : ℤ) =
    2 * (numeratorAt 6 (i + 21) : ℤ) - (numeratorAt 6 i : ℤ)) ∧
  (∀ i : ℕ, numeratorAt 6 i = gfCoeff 21
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 4, 2, 3, 4, 5, 2, 4, 6, 5, 3, 1, 5, 4, 3, 4, 2, 3, 2, 3, 1, 2, 2, 1, 1, 1, 1] i) := by
  sorry

end OMA.S_oeis_a071287
