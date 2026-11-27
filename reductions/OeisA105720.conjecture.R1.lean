import FormalConjectures.OEIS.«105720»

/-!
# A105720: the indices whose sum-of-primes value is a square, and the open direction

`a n` is the sum of the primes `p_(n-1), …, p_(2n)` (with `p_1 = 2`), and `a 0 = 0`.  The
conjecture `IsSquare (a n) ↔ n = 3 ∨ n = 6 ∨ n = 4072` says the value is a square at exactly
those three indices.

`H1` is the finite direction: at the three listed indices the value is a square.

`H2` is the open direction: no other positive index gives a square.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA105720_conjecture_R1

/-- The finite direction: the three listed indices give a square. -/
def H1 : Prop :=
  ∀ n : ℕ, n = 3 ∨ n = 6 ∨ n = 4072 → IsSquare (OeisA105720.a n)

/-- The open direction: a square happens only at the three listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → IsSquare (OeisA105720.a n) → n = 3 ∨ n = 6 ∨ n = 4072

theorem main : H1 → H2 → type_of% @OeisA105720.conjecture := by
  intro h1 h2 n hn
  exact ⟨h2 n hn, h1 n⟩

end OMA.R_OeisA105720_conjecture_R1
