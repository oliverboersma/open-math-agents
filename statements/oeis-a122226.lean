import Mathlib

/-!
# Equal maxima for the integer-diameter sequences A122226 and A125852

Sources: https://oeis.org/A122226 and https://oeis.org/A125852.
Credit: @shunyaekam.

The two sequences are indexed by positive integers. The conjecture compares
their terms for every index greater than one. A quantifier over all real
diameters would be a stronger statement than equality of these sequences.

The six unit directions of the hexagonal lattice in this entry join centers
of adjacent hexagons. In axial coordinates the squared norm is x^2+xy+y^2.
All lengths count segments. A self-avoiding walk may close at its starting
vertex, using a different edge to return there. Every vertex lies in the
disk if and only if the entire polygonal walk lies there, by convexity.
-/

namespace OMA.S_oeis_a122226

abbrev Site := ℤ × ℤ
abbrev Center := ℝ × ℝ

def unitStep (p q : Site) : Prop :=
  let x := p.1 - q.1
  let y := p.2 - q.2
  x^2 + x*y + y^2 = 1

def valid (m : ℕ) (p : ℕ → Site) : Prop :=
  (∀ i < m, unitStep (p i) (p (i+1))) ∧
  (∀ i j : ℕ, i < j → j ≤ m → p i = p j → i = 0 ∧ j = m) ∧
  (p 0 = p m → 3 ≤ m)


def inDisk (n : ℕ) (o : Center) (p : Site) : Prop :=
  let x := p.1 - o.1
  let y := p.2 - o.2
  4 * (x^2 + x*y + y^2) ≤ (n : ℝ)^2

def walkLengths (n : ℕ) : Set ℕ :=
  {m | ∃ (p : ℕ → Site) (o : Center), valid m p ∧ ∀ i ≤ m, inDisk n o (p i)}

/-- Count any finite collection in a common disk. Its greatest attainable
cardinality equals the greatest number of lattice points covered by a disk. -/
def siteCounts (n : ℕ) : Set ℕ :=
  {m | ∃ (s : Finset Site) (o : Center), s.card = m ∧ ∀ p ∈ s, inDisk n o p}

/-- A122226(n) and A125852(n) have the same value for every integer n > 1. -/
theorem main : ∀ n : ℕ, 1 < n →
    ∃ m : ℕ, IsGreatest (walkLengths n) m ∧ IsGreatest (siteCounts n) m := by
  sorry

end OMA.S_oeis_a122226
