import FormalConjectures.OEIS.«261627»

/-!
# A261627: the thirteen indices with `a n = 1` and the open direction

`a n` counts the primes `p` for which `k = p * n' - 1` (with `n' = 1` for odd `n` and `n' = 2`
for even `n`) satisfies `k < n` and both `n - k` and `n + k` are prime.  The conjecture
`a n = 1 ↔ n ∈ {5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142}` says that exactly those
thirteen indices admit a single such prime.

`H1` is the finite direction: at the thirteen listed indices the count is one.  This is a
direct computation of `a` on those values.

`H2` is the open direction: no other index has count one.

`main` assembles the two directions.
-/

namespace OMA.R_OeisA261627_conjecture_2_R1

/-- The finite direction: the thirteen listed indices have count one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142} : Finset ℕ) →
    OeisA261627.a n = 1

/-- The open direction: count one happens only at the thirteen listed indices. -/
def H2 : Prop :=
  ∀ n : ℕ, OeisA261627.a n = 1 →
    n ∈ ({5, 7, 10, 11, 12, 19, 22, 30, 34, 44, 46, 72, 142} : Finset ℕ)

theorem main : H1 → H2 → type_of% @OeisA261627.conjecture_2 := by
  intro h1 h2 n
  exact ⟨h2 n, h1 n⟩

end OMA.R_OeisA261627_conjecture_2_R1
