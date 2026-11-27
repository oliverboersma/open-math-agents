import FormalConjectures.OEIS.«237720»

/-!
# A237720: the indices with `a n = 1` and the open direction

`a n` counts the primes `p ≤ ⌊(n+1)/2⌋` for which `⌊√(n-p)⌋` is prime.  The conjecture
`a n = 1 ↔ n = 6 ∨ n = 23 ∨ n = 24 ∨ (111 ≤ n ∧ n ≤ 120)` says that exactly those thirteen
indices have a single such prime.

`H1` is the finite direction: at the listed indices the count is one.  This is a direct
computation of `a` on those values.

`H2` is the open direction: no other index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA237720_conjecture_2_R1

/-- The finite direction: the thirteen listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n = 6 ∨ n = 23 ∨ n = 24 ∨ (111 ≤ n ∧ n ≤ 120) → OeisA237720.a n = 1

/-- The open direction: count one happens only at the thirteen listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA237720.a n = 1 → n = 6 ∨ n = 23 ∨ n = 24 ∨ (111 ≤ n ∧ n ≤ 120)

theorem main : H1 → H2 → type_of% @OeisA237720.conjecture_2 := by
  intro h1 h2 n
  exact ⟨h2 n, h1 n⟩

end OMA.R_OeisA237720_conjecture_2_R1
