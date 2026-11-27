import Mathlib.Data.Int.Basic

/-!
# OEIS A390007

Janaka Rodrigo asks whether an integer square of side n has a unique
minimum-defect set of three distinct rectangular tiles, except at n=4.

We represent the sets by their cut dimensions. Every tiling by three
rectangles has one tile at two corners of the square, by pigeonhole.
Those corners must be adjacent, since opposite corners would force that
tile to be the entire square. This leaves a rectangle tiled by two
rectangles, separated by a single straight cut. The two cuts are either
parallel or perpendicular. Conversely both constructions give tilings.

Sorting the widths of three parallel strips identifies all reorderings.
For perpendicular cuts only the full strip has a side of length n.
Its width therefore determines the first cut; the shorter of the two
parts on the perpendicular cut determines the second. Thus these
parameters describe sets of shapes, with rotations treated as congruences.
The same two normal forms occur in Figure 1 and Theorem 2.1 of Dalfó,
Fiol and López, "New results for the Mondrian art problem" (2021).

Source: https://oeis.org/A390007
Formalization: @ecirak42.
-/

namespace OMA.S_oeis_a390007

inductive TileSet where
  | strips (x y z : Int)
  | tee (a b : Int)

def valid (n : Int) : TileSet → Prop
  | .strips x y z => 0 < x ∧ x < y ∧ y < z ∧ x+y+z = n
  | .tee a b => 0 < a ∧ a < n ∧ 0 < b ∧ 2*b < n

/-- If l ≤ h, these three differences have maximum equal to the largest
of x,l,h minus the smallest. -/
def spread (x l h : Int) : Int := max (h-l) (max (x-l) (h-x))

def defect (n : Int) : TileSet → Int
  | .strips x _ z => n*(z-x)
  | .tee a b => spread (n*a) (b*(n-a)) ((n-b)*(n-a))

def optimal (n : Int) (s : TileSet) : Prop :=
  valid n s ∧ ∀ t, valid n t → defect n s ≤ defect n t

theorem main : ∀ n : Int, 3 ≤ n → ((∃! s, optimal n s) ↔ n ≠ 4) := by
  sorry

end OMA.S_oeis_a390007
