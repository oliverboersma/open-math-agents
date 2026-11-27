import FormalConjectures.OEIS.«259667»

/-!
# A259667: the exponents `k` with `a (2^k - 1) = 1` and the open direction

`a n = C_n mod 6` where `C_n` is the `n`-th Catalan number.  The conjecture
`a (2^k - 1) = 1 ↔ k = 0 ∨ k = 1 ∨ k = 5` says that exactly those three exponents give residue
one.

`H1` is the finite direction: at the three listed exponents the residue is one.  This is a
direct computation of the Catalan number modulo six.

`H2` is the open direction: no other exponent gives residue one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA259667_conjecture_1_R1

/-- The finite direction: the three listed exponents give residue one. -/
def H1 : Prop :=
  ∀ k : ℕ, k ∈ ({0, 1, 5} : Finset ℕ) → OeisA259667.a (2 ^ k - 1) = 1

/-- The open direction: residue one happens only at the three listed exponents. -/
def H2 : Prop :=
  ∀ k : ℕ, OeisA259667.a (2 ^ k - 1) = 1 → k = 0 ∨ k = 1 ∨ k = 5

theorem main : H1 → H2 → type_of% @OeisA259667.conjecture_1 := by
  intro h1 h2 k
  constructor
  · exact h2 k
  · rintro (rfl | rfl | rfl)
    · exact h1 0 (by simp)
    · exact h1 1 (by simp)
    · exact h1 5 (by simp)

end OMA.R_OeisA259667_conjecture_1_R1
