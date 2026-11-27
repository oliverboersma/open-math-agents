import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.ZMod.Basic

/-! Andrei Zabolotskii's population recurrences for the triangular odd-rule
cellular automaton. The two orientations have opposite neighbor offsets.
The active cells are the nonzero coefficients of the configuration.
Source: https://oeis.org/A275667/internal
-/

namespace OMA.S_oeis_a275667

noncomputable section

abbrev Point := ℤ × ℤ
abbrev Config := AddMonoidAlgebra (ZMod 2) Point

def monomial (p : Point) : Config := AddMonoidAlgebra.single p 1

/-- The three displacements from a triangle to its side neighbors, with the
sign determined by its orientation. -/
def stencil (sign : ℤ) : Config :=
  monomial (0, 0) + monomial (sign, 0) + monomial (0, sign)

/-- A single marked triangle evolves over F₂. All marked triangles at a
fixed time have the same orientation, which reverses on each step. -/
def generation : ℕ → Config
  | 0 => 1
  | n + 1 => stencil (if n % 2 = 0 then 1 else -1) * generation n

def population (n : ℕ) : ℕ := (generation n).coeff.support.card

theorem main :
    population 0 = 1 ∧
    (∀ t : ℕ, population (2 * t + 1) = 3 * population t) ∧
    (∀ t : ℕ, population (8 * t + 6) = 3 * population (4 * t + 2) + 4 * population (2 * t)) ∧
    (∀ t : ℕ, population (8 * t + 2) = 3 * population (4 * t) + 4 * population (2 * t)) ∧
    (∀ t : ℕ, population (4 * t) = population (2 * t)) := by
  sorry

end
end OMA.S_oeis_a275667
