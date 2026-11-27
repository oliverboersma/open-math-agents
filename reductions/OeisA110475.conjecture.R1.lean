import FormalConjectures.OEIS.«110475»

-- Reduction OeisA110475.conjecture.R1 of OEIS A110475.
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a biconditional under `m > 0`: membership in the exceptional set of `a` versus a
-- two-term decomposition into positions where `a` takes the value 1. The two directions are
-- independent statements, so each is its own step.

namespace OMA.R_OeisA110475_conjecture_R1

open OeisA110475

/-- Forward direction: a positive `m` outside the exceptional set decomposes as `x + y` with
`a x = 1` and `a y = 1`. -/
def H1 : Prop :=
  ∀ m : ℕ, 0 < m → m ∉ exceptionalSet → ∃ x y : ℕ, a x = 1 ∧ a y = 1 ∧ m = x + y

/-- Backward direction: any positive `m` that decomposes as such a sum is outside the exceptional
set. -/
def H2 : Prop :=
  ∀ m : ℕ, 0 < m → (∃ x y : ℕ, a x = 1 ∧ a y = 1 ∧ m = x + y) → m ∉ exceptionalSet

theorem main : H1 → H2 → type_of% @OeisA110475.conjecture := by
  intro h1 h2 m hm
  exact ⟨h1 m hm, h2 m hm⟩

end OMA.R_OeisA110475_conjecture_R1
