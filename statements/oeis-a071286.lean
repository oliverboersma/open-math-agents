import Mathlib

/-!
# OEIS A071286: Peirce denominators of order 5

The infinite token stream implements the insertion rule in Graham, Knuth
and Patashnik, Concrete Mathematics, second edition, exercise 64 on p. 151.
A token records a fraction's denominator or a separator. At every old
position j divisible by the previous order, the rule inserts two tokens
before the original token. For an odd one-based j it inserts a new fraction
and an equality separator. For an even j it inserts a copy of the separator
and a new fraction. Projecting to denominators therefore loses no information
used in the insertion. Fraction tokens occupy even zero-based positions.

The target compares every coefficient to the appropriate entry of the
source numerator polynomial. This expresses both the rational generating
function with denominator 1 minus x to the power 15 and the period-15 recurrence.

Source: https://oeis.org/A071286
Conjecture: Colin Barker, March 29, 2017.
Formalization: @senamakel
-/

namespace OMA.S_oeis_a071286

inductive Symbol where
  | den (d : Nat)
  | sep
  deriving DecidableEq, Repr

def expandStream (n : Nat) (old : Nat → Symbol) (i : Nat) : Symbol :=
  let q := i / (n + 2)
  let r := i % (n + 2)
  let j := (q + 1) * n
  if r + 1 < n then
    old (q * n + r)
  else if r + 1 = n then
    if j % 2 = 1 then Symbol.den (n + 1) else old (j - 1)
  else if r = n then
    if j % 2 = 1 then Symbol.sep else Symbol.den (n + 1)
  else
    old (j - 1)

def peirce : Nat → Nat → Symbol
  | 0, _ => Symbol.sep
  | 1, i => if i % 2 = 0 then Symbol.den 1 else Symbol.sep
  | n + 2, i => expandStream (n + 1) (peirce (n + 1)) i

def denominatorAt (n i : Nat) : Nat :=
  match peirce n (2 * i) with
  | Symbol.den d => d
  | Symbol.sep => 0

theorem main : ∀ i : ℕ, denominatorAt 5 i = ([2, 4, 5, 3, 1, 5, 4, 3, 5, 4, 2, 5, 3, 4, 5] : List ℕ)[i % 15]! := by
  sorry

end OMA.S_oeis_a071286
