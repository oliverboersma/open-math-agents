import FormalConjectures.OEIS.«262813»

/-!
# A262813: the seven indices with `a n = 1` and the open direction

`a n` counts the ordered ways to write `n` as `x^3 + y^2 + z*(z+1)/2` with `x ≥ 0`, `y ≥ 0`
and `z > 0`.  The conjecture `a n = 1 ↔ n ∈ {1, 9, 21, 35, 98, 152, 306}` says that exactly
those seven positive indices have a single such representation.

`H1` is the finite direction: at the seven listed indices the count is one.  This is a direct
computation of `a` on those values.

`H2` is the open direction: no other positive index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA262813_conjecture_2_R1

/-- The finite direction: the seven listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({1, 9, 21, 35, 98, 152, 306} : Finset ℕ) → OeisA262813.a n = 1

/-- The open direction: count one happens only at the seven listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → OeisA262813.a n = 1 → n ∈ ({1, 9, 21, 35, 98, 152, 306} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA262813.conjecture_2 := by
  intro h1 h2 n hn
  exact ⟨h2 n hn, h1 n⟩

end OMA.R_OeisA262813_conjecture_2_R1
