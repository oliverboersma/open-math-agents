import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Maximum product of partition parts congruent to two modulo three

Source: https://oeis.org/A121451 (John W. Layman, OEIS Foundation, CC BY-SA 4.0).

The sequence starts at n = 1. The maximum is zero when no partition has
all parts congruent to two modulo three.
-/

namespace OMA.S_oeis_a121451

def a (n : ℕ) : ℕ :=
  Finset.univ.sup fun P : n.Partition =>
    if ∀ x ∈ P.parts, x % 3 = 2 then P.parts.prod else 0

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = if n = 1 ∨ n = 3 then 0 else
      if n % 2 = 0 then 2 ^ (n / 2) else 5 * 2 ^ ((n - 5) / 2) := by
  sorry

end OMA.S_oeis_a121451
