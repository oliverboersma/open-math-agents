import FormalConjectures.OEIS.«78729»

/-!
# A78729: the vanishing index and the open direction

`a n` is the least `k > 0` such that `(k+1)(k+2)⋯(k+n) + 1` is prime, or `0` if none exists.
The conjecture `a n = 0 ↔ n = 4` says the value vanishes only at `n = 4`.

`H1` is the finite direction: at `n = 4` the value is zero (the product is always the square
`(k^2 + 5k + 5)^2`, hence not prime).  This is the only index in the finite direction.

`H2` is the open direction: no other positive index has value zero.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA78729_conjecture_R1

/-- The finite direction: the single listed index has value zero. -/
def H1 : Prop :=
  ∀ n : ℕ, n = 4 → OeisA78729.a n = 0

/-- The open direction: value zero happens only at the single listed index. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → OeisA78729.a n = 0 → n = 4

theorem main : H1 → H2 → type_of% @OeisA78729.conjecture := by
  intro h1 h2 n hn
  exact ⟨h2 n hn, h1 n⟩

end OMA.R_OeisA78729_conjecture_R1
