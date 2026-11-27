import FormalConjectures.Wikipedia.BoundedBurnsideProblem
import Mathlib

/-! The bounded Burnside problem has a negative answer because the free Burnside group
B(2, 667), the quotient of the free group on two generators by the normal closure of all
667-th powers, is infinite: Adian, The Burnside problem and identities in groups (1979),
proves B(m, n) infinite for m ≥ 2 and odd n ≥ 665, after Novikov and Adian (1968). What
remains is elementary: such a quotient is finitely generated and every element has order
dividing n. -/

namespace OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1

/-- Adian: the free Burnside group B(2, 667) is infinite. -/
def H1 : Prop := Infinite (FreeGroup (Fin 2) ⧸
  Subgroup.normalClosure {y : FreeGroup (Fin 2) | ∃ x : FreeGroup (Fin 2), y = x ^ 667})

/-- The free Burnside group B(2, n) is finitely generated and every element satisfies
g^n = 1. -/
def H2 : Prop := ∀ n : ℕ,
  Group.FG (FreeGroup (Fin 2) ⧸
    Subgroup.normalClosure {y : FreeGroup (Fin 2) | ∃ x : FreeGroup (Fin 2), y = x ^ n}) ∧
  ∀ g : FreeGroup (Fin 2) ⧸
    Subgroup.normalClosure {y : FreeGroup (Fin 2) | ∃ x : FreeGroup (Fin 2), y = x ^ n},
    g ^ n = 1

theorem main : H1 → H2 → type_of% @BoundedBurnsideProblem.bounded_burnside_problem := by
  intro h1 h2 hall
  obtain ⟨hfg, hexp⟩ := h2 667
  have hfin := hall _ hfg 667 (by norm_num) hexp
  exact not_finite_iff_infinite.2 h1 hfin

end OMA.R_BoundedBurnsideProblem_bounded_burnside_problem_R1
