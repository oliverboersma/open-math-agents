import Mathlib

/-!
Toby Gottfried, OEIS A216211 (2013); generating function and recurrence
conjectured by Colin Barker (2017). https://oeis.org/A216211
-/

namespace OMA.S_oeis_a216211

abbrev Site := ℕ × ℕ

/-- Horizontal and vertical unit steps in vertex coordinates (row, column). -/
def adjacent (u v : Site) : Prop :=
  Nat.dist u.1 v.1 + Nat.dist u.2 v.2 = 1

/-- An ordered simple walk inside the stated rectangle, including both endpoints.
A singleton list represents the length-zero walk. -/
def isWalk (height width : ℕ) (start finish : Site) (w : List Site) : Prop :=
  w.head? = some start ∧ w.getLast? = some finish ∧ w.Nodup ∧
    List.IsChain adjacent w ∧ ∀ p ∈ w, p.1 < height ∧ p.2 < width

/-- At zero rows there is no path, giving the zero constant coefficient of
the ordinary generating function. At one row the two endpoints coincide. -/
noncomputable def count (n : ℕ) : ℤ :=
  (Nat.card {w : List Site // isWalk n 4 (0,0) (n-1,0) w} : ℕ)

theorem main :
    (let x : PowerSeries ℤ := PowerSeries.X
     PowerSeries.mk count *
       ((1-8*x+15*x^2-5*x^3-9*x^4+2*x^5+x^6) *
        (1-4*x+7*x^2-3*x^3-7*x^4+2*x^5+x^6)) =
       x*(1-8*x+34*x^2-66*x^3+21*x^4+85*x^5-64*x^6-45*x^7+26*x^8+11*x^9-3*x^10-x^11)) ∧
    ∀ n : ℕ, count (n+13) =
      12*count (n+12) - 54*count (n+11) + 124*count (n+10) - 133*count (n+9) -
      16*count (n+8) + 175*count (n+7) - 94*count (n+6) - 69*count (n+5) +
      40*count (n+4) + 12*count (n+3) - 4*count (n+2) - count (n+1) := by
  sorry

end OMA.S_oeis_a216211
