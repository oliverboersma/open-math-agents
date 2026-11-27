import FormalConjectures.Wikipedia.Catalan

-- Reduction LebesgueNagell.lebesgue_nagell.R1 of the Lebesgue-Nagell equation x^2 - 2 = y^p.
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is an iff, so it splits into its two directions. The backward direction is already
-- proved upstream (the two [category test] lemmas that check (+-1, -1) are solutions), so it is
-- kept as its own step although it is cheap; the forward direction is the open arithmetic core.

namespace OMA.R_LebesgueNagell_lebesgue_nagell_R1

/-- Forward direction (the open core): for an odd prime `p`, any integer solution of
`x^2 - 2 = y^p` must be `x = ±1`, `y = -1`. -/
def H1 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ),
    x ^ 2 - 2 = y ^ p → (x = 1 ∨ x = -1) ∧ y = -1

/-- Backward direction: `(±1, -1)` solves `x^2 - 2 = y^p` for every odd `p`. -/
def H2 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime) (hodd : Odd p) (x y : ℤ),
    (x = 1 ∨ x = -1) ∧ y = -1 → x ^ 2 - 2 = y ^ p

theorem main : H1 → H2 → type_of% @LebesgueNagell.lebesgue_nagell := by
  intro h1 h2 p hp hodd x y
  exact ⟨h1 p hp hodd x y, h2 p hp hodd x y⟩

end OMA.R_LebesgueNagell_lebesgue_nagell_R1
