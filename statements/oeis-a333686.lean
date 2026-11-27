import Mathlib

/-!
Seiichi Manyama, OEIS A333686 (2020), including both conjectured formulas.
https://oeis.org/A333686
-/

namespace OMA.S_oeis_a333686

abbrev Site := ℕ × ℕ

/-- Horizontal and vertical unit steps in vertex coordinates (row, column). -/
def adjacent (u v : Site) : Prop :=
  Nat.dist u.1 v.1 + Nat.dist u.2 v.2 = 1

/-- An ordered simple walk inside the stated rectangle, including both endpoints.
A singleton list represents the length-zero walk. -/
def isWalk (height width : ℕ) (start finish : Site) (w : List Site) : Prop :=
  w.head? = some start ∧ w.getLast? = some finish ∧ w.Nodup ∧
    List.IsChain adjacent w ∧ ∀ p ∈ w, p.1 < height ∧ p.2 < width

/-- Rectangles have 2n+1 rows and three columns. The marked site is the center. -/
noncomputable def count (n : ℕ) : ℤ :=
  (Nat.card {w : List Site // isWalk (2*n+1) 3 (0,0) (2*n,2) w ∧ (n,1) ∈ w} : ℕ)

/-- The polynomial factor at the constant term of the denominator equals one. -/
theorem main :
    (let x : PowerSeries ℤ := PowerSeries.X
     PowerSeries.mk count * ((1-x)*(1+x)*(1+x+x^2)*(1-11*x+x^2)) =
       (1-3*x-x^2)*(1+3*x+x^2+x^3)) ∧
    ∀ n : ℕ, count (n+6) =
      10*count (n+5) + 10*count (n+4) - 10*count (n+2) - 10*count (n+1) + count n := by
  sorry

end OMA.S_oeis_a333686
