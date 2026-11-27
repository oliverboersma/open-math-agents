import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A267514: Rule 137 center-column words

Source: https://oeis.org/A267514 (OEIS Foundation, CC BY-SA 4.0).
Conjectures by Colin Barker, January 16, 2016.
R. J. Mathar identified the recurrence failure at index 62.

The sequence starts at index zero with a single ON cell. The initial
window for time n consists of n OFF cells, the ON cell, and n OFF
cells. Applying the local rule to consecutive triples shrinks that
window until only the center cell remains. The digits from time zero
through time n are read in chronological order in base ten, as in the
source's Mathematica FromDigits program and its initial terms.

Clearing the generating-function denominator states the original
quotient because its constant coefficient is one.
-/

namespace OMA.S_oeis_a267514

def rule (left middle right : Bool) : Bool :=
  (137 : ℕ).testBit (4 * left.toNat + 2 * middle.toNat + right.toNat)

def step : List Bool → List Bool
  | left :: middle :: right :: rest => rule left middle right :: step (middle :: right :: rest)
  | _ => []

def center (n : ℕ) : Bool :=
  ((step^[n]) (List.replicate n false ++ [true] ++ List.replicate n false)).headD false

def a : ℕ → ℤ
  | 0 => (center 0).toNat
  | n + 1 => 10 * a n + (center (n + 1)).toNat

noncomputable def series : PowerSeries ℤ := PowerSeries.mk a

open PowerSeries in
theorem main :
    (∀ n : ℕ, 7 < n → a n = 10 * a (n - 1) + a (n - 7) - 10 * a (n - 8)) ∧
    (series * ((1 - X) * (1 - 10 * X) * (1 + X + X^2 + X^3 + X^4 + X^5 + X^6)) =
      (1 - X + X^2) * (1 + X + X^2)) := by
  sorry

end OMA.S_oeis_a267514
