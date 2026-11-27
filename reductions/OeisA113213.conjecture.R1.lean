import FormalConjectures.OEIS.«113213»

-- Reduction OeisA113213.conjecture.R1 of OEIS A113213.
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is the conjunction of two independent statements about the same sequence: a
-- Golomb-type claim that every large power of two is the midpoint of a prime pair, and a growth
-- bound of order n^3 on the smallest such offset. Neither implies the other, so each is a step.

namespace OMA.R_OeisA113213_conjecture_R1

open OeisA113213

/-- Every sufficiently large power of two is the midpoint of two primes. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∃ m, (2 ^ n - m).Prime ∧ (2 ^ n + m).Prime

/-- The smallest such offset grows at most like `n ^ 3`. -/
def H2 : Prop :=
  (fun n : ℕ => (a n : ℝ)) =O[Filter.atTop] (fun n : ℕ => (n ^ 3 : ℝ))

theorem main : H1 → H2 → type_of% @OeisA113213.conjecture := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_OeisA113213_conjecture_R1
