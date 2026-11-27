import FormalConjectures.OEIS.«238585»

/-!
# A238585: the twelve indices with `a n = 1` and the open direction

`a n` counts the primes `p < n` for which `prime(p)^2 + (prime(n) - 1)^2` is prime, where
`prime(i)` is the `i`-th prime.  The conjecture
`a n = 1 ↔ n ∈ {4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44}` says that exactly those twelve
indices have a single such prime.

`H1` is the finite direction: at the twelve listed indices the count is one.  This is a
direct computation of `a` on those values.

`H2` is the open direction: no other index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA238585_conjecture_2_R1

/-- The finite direction: the twelve listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44} : Set ℕ) →
    OeisA238585.a n = 1

/-- The open direction: count one happens only at the twelve listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → OeisA238585.a n = 1 →
    n ∈ ({4, 5, 7, 10, 11, 12, 19, 21, 22, 31, 42, 44} : Set ℕ)

theorem main : H1 → H2 → type_of% @OeisA238585.conjecture_2 := by
  intro h1 h2 n hn
  exact ⟨h2 n hn, h1 n⟩

end OMA.R_OeisA238585_conjecture_2_R1
