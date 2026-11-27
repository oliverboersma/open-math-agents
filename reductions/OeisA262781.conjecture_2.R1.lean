import FormalConjectures.OEIS.«262781»

/-!
# A262781: the eighteen indices with `a n = 1` and the open direction

`a n` counts the ordered ways to write `n` as `x^2 + φ(y^2) + φ(z^2)` with `x ≥ 0`, `0 < y ≤ z`
and `y` or `z` prime, where `φ` is Euler's totient function.  The conjecture
`a n = 1 ↔ n ∈ {3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649}`
says that exactly those eighteen indices have a single such representation.

`H1` is the finite direction: at the eighteen listed indices the count is one.  This is a
direct computation of `a` on those values.

`H2` is the open direction: no other index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA262781_conjecture_2_R1

/-- The finite direction: the eighteen listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ,
    n ∈ ({3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649} : Finset ℕ) →
      OeisA262781.a n = 1

/-- The open direction: count one happens only at the eighteen listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA262781.a n = 1 →
    n ∈ ({3, 5, 9, 10, 17, 20, 24, 25, 31, 36, 45, 73, 80, 101, 136, 145, 388, 649} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA262781.conjecture_2 := by
  intro h1 h2 n
  exact ⟨h2 n, h1 n⟩

end OMA.R_OeisA262781_conjecture_2_R1
