import FormalConjectures.GreensOpenProblems.«28»

-- Reduction Green28.green_28.R1 of Ben Green's Open Problem 28.
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target asks: if `X` and `Y` are finitely supported and `X + Y` is uniform on its support,
-- are `X` and `Y` uniform on their supports? The conclusion is the conjunction of the two
-- one-variable claims, so each factor of the convolution is its own step. The hypotheses are
-- spelled out separately so that neither hypothesis mentions the other.

namespace OMA.R_Green28_green_28_R1

open Green28

/-- The first factor: a finitely supported `X` whose convolution with a finitely supported `Y` is
uniform on its support is itself uniform on its support. -/
def H1 : Prop :=
  ∀ X Y : PMF ℤ, X.support.Finite → Y.support.Finite →
    IsUniformOnSupport (indepSum X Y) → IsUniformOnSupport X

/-- The second factor: a finitely supported `Y` whose convolution with a finitely supported `X` is
uniform on its support is itself uniform on its support. -/
def H2 : Prop :=
  ∀ X Y : PMF ℤ, X.support.Finite → Y.support.Finite →
    IsUniformOnSupport (indepSum X Y) → IsUniformOnSupport Y

theorem main : H1 → H2 → type_of% @Green28.green_28 := by
  intro h1 h2 X Y hXY
  obtain ⟨hX, hY, hS⟩ := hXY
  exact ⟨h1 X Y hX hY hS, h2 X Y hX hY hS⟩

end OMA.R_Green28_green_28_R1
