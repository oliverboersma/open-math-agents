import FormalConjectures.OEIS.«262446»

/-!
# A262446: the seven indices with `a n = 1` and the open direction

`a n` counts the ways to write `b(n) = b(k) + b(m)` with `0 < k < m < n`, where
`b(x) = π(T(x) + 1)` and `T(x) = x(x+1)/2`.  The conjecture
`a n = 1 ↔ n ∈ {4, 6, 11, 21, 54, 253, 325}` says that exactly those seven indices have a
single such decomposition.

`H1` is the finite direction: at the seven listed indices the count is one.  This is a direct
computation of `a` on those values.

`H2` is the open direction: no other index above three has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA262446_conjecture_2_R1

/-- The finite direction: the seven listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({4, 6, 11, 21, 54, 253, 325} : Finset ℕ) → OeisA262446.a n = 1

/-- The open direction: count one happens only at the seven listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → OeisA262446.a n = 1 → n ∈ ({4, 6, 11, 21, 54, 253, 325} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA262446.conjecture_2 := by
  intro h1 h2 n hn
  exact ⟨h2 n hn, h1 n⟩

end OMA.R_OeisA262446_conjecture_2_R1
