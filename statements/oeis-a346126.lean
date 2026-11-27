import Mathlib

/-!
# Optimal walks on the triangular lattice of OEIS A346126

Source: https://oeis.org/A346126 and the author's illustrations at
https://www.randomwalk.de/sequences/a346126.htm. Credit: @shunyaekam.

The six unit directions of the hexagonal lattice in this entry join centers
of adjacent hexagons. In axial coordinates the squared norm is x^2+xy+y^2.
All lengths count segments. A self-avoiding walk may close at its starting
vertex, using a different edge to return there. Every vertex lies in the
disk if and only if the entire polygonal walk lies there, by convexity.
-/

namespace OMA.S_oeis_a346126

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

def fits (m : ℕ) (p : ℕ → Site) (o : Center) (s : ℝ) : Prop :=
  ∀ i ≤ m,
    let x := (p i).1 - o.1
    let y := (p i).2 - o.2
    x^2 + x*y + y^2 ≤ s

def attainable (m : ℕ) (s : ℝ) : Prop :=
  ∃ (p : ℕ → Site) (o : Center), valid m p ∧ fits m p o s

/-- At every record length other than one, every walk attaining the smallest
enclosing disk is closed. Existence at squared radius s is witnessed by p;
the final premise means no length-(m+1) walk fits at that same radius. -/
theorem main : ∀ (m : ℕ) (s : ℝ) (p : ℕ → Site) (o : Center),
    2 ≤ m → valid m p → fits m p o s →
    (∀ t : ℝ, attainable m t → s ≤ t) →
    ¬ attainable (m+1) s → p 0 = p m := by
  sorry

end OMA.S_oeis_a346126
