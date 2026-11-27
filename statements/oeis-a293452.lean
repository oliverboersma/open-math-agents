import Mathlib

/-!
# The one-row toroidal sandpile

Sources: https://oeis.org/A293452, https://oeis.org/A249872, https://oeis.org/A023855.
Credit: @shunyaekam

Site zero is a sink. On a strip of width one, the two vertical neighbors
of each nonsink site are that site itself, so a legal toppling costs it
two grains net. Both horizontal edges are retained, even when their
endpoints coincide.
-/

namespace OMA.S_oeis_a293452

abbrev Heights (n : ℕ) := Fin n → ℕ

def initial (n : ℕ) : Heights n :=
  fun j => if j.val = 0 then 0 else 4

def topple {n : ℕ} (c : Heights n) (i : Fin n) : Heights n :=
  fun j => if j.val = 0 then 0 else
    (if j = i then c j - 2 else c j) +
    (if j.val = (i.val + 1) % n then 1 else 0) +
    (if j.val = (i.val + n - 1) % n then 1 else 0)

/-- The list records every toppling, in order, up to stabilization. -/
def completes {n : ℕ} : Heights n → List (Fin n) → Prop
  | c, [] => ∀ j, c j < 4
  | c, i :: rest => i.val ≠ 0 ∧ 4 ≤ c i ∧ completes (topple c i) rest

/-- A023855 in the OEIS offset-one convention. -/
def rectangleSum (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range ((n + 1) / 2), (j + 1) * (n - j)

/-- The formula printed in A293452, quantified over positive row indices.
The equivalence specifies existence of a completed run of the stated length
and excludes all other lengths. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ,
    (∃ moves : List (Fin n), completes (initial n) moves ∧ moves.length = m) ↔
      m = rectangleSum n := by
  sorry

end OMA.S_oeis_a293452
