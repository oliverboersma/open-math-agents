import Mathlib

/-!
# A000001: conjectures on the number of groups of order n

Source: https://oeis.org/A000001
Credit: @caa1982

`a(n)` (the group number `gnu(n)`) is the number of groups of order `n` up to isomorphism, with
`a(0) = 0`. The entry records two conjectures:
1. (J. H. Conway, Heiko Dietrich and E. A. O'Brien, 2008) for every `n`, the sequence
   `n, a(n), a(a(n)), a(a(a(n))), ...` consists ultimately of 1s;
2. `a(i) * a(j) ≤ a(i * j)` for all nonnegative integers `i` and `j`.

`main` is the conjunction of the two. Conjecture 1 is stated for `n ≥ 1`, the range of the cited
paper (for `n = 0` the sequence is constantly `a(0) = 0`); once a 1 appears the sequence stays at
1 because `a(1) = 1`.

The number of groups of order `n` is counted as the number of isomorphism classes of group
structures on `Fin n`: every group of order `n` is isomorphic to one carried by `Fin n`, and there is
none when `n = 0`. Isomorphism is already an equivalence relation, so `Quot` by it is the set of
isomorphism classes. The type `Group (Fin n)` is finite (all its data fields are determined by the
multiplication, a function `Fin n → Fin n → Fin n`, through the group axioms), so `Nat.card` is the
actual number of classes.
-/

namespace OMA.S_oeis_a000001

/-- Two group structures on `Fin n` are isomorphic. -/
def IsoRel (n : ℕ) (G H : Group (Fin n)) : Prop :=
  Nonempty (@MulEquiv (Fin n) (Fin n) (letI := G; inferInstance) (letI := H; inferInstance))

/-- `gnu n`: the number of groups of order `n` up to isomorphism (OEIS A000001). -/
noncomputable def gnu (n : ℕ) : ℕ := Nat.card (Quot (IsoRel n))

/-- Conjectures 1 and 2 of OEIS A000001. -/
theorem main : (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, gnu^[k] n = 1) ∧
    (∀ i j : ℕ, gnu i * gnu j ≤ gnu (i * j)) := by
  sorry

end OMA.S_oeis_a000001
