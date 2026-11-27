import FormalConjectures.OEIS.«262403»

/-!
# A262403: the nine indices with `a n = 1` and the open direction

`a n` counts the ways to write `π(T(n)) = π(T(k)) + π(T(m))` with `1 < k < m < n`, where
`T(x) = x(x+1)/2` and `π` is the prime counting function.  The conjecture
`a n = 1 ↔ n ∈ {5, 6, 7, 10, 12, 32, 38, 445, 727}` says that exactly those nine indices have
a single such decomposition.

`H1` is the finite direction: at the nine listed indices the count is one.  This is a direct
computation of `a` on those values.

`H2` is the open direction: no other index above four has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA262403_conjecture_2_R1

/-- The finite direction: the nine listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({5, 6, 7, 10, 12, 32, 38, 445, 727} : Finset ℕ) → OeisA262403.a n = 1

/-- The open direction: count one happens only at the nine listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 < n → OeisA262403.a n = 1 → n ∈ ({5, 6, 7, 10, 12, 32, 38, 445, 727} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA262403.conjecture_2 := by
  intro h1 h2 n hn
  exact ⟨h2 n hn, h1 n⟩

end OMA.R_OeisA262403_conjecture_2_R1
