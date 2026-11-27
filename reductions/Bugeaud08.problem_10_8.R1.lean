import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_8

-- Reduction Bugeaud08.problem_10_8.R1 of the p-adic Littlewood conjecture (de Mathan and Teulié)
-- Credit: @marcusbuffett

/-!
# The p-adic Littlewood conjecture is only open for badly approximable numbers

The conjecture says `inf_{q ≥ 1} q * |q|_p * ‖qξ‖ = 0` for every real `ξ` and prime `p`, where
`‖x‖` is the distance to the nearest integer.

* `H1` (classical remark): if `q ‖qξ‖` takes arbitrarily small values (that is, `ξ` is rational
  or, more generally, not badly approximable), the infimum is `0`, because `|q|_p ≤ 1`.
* `H2`: the conjecture for badly approximable `ξ`, that is `q ‖qξ‖ ≥ ε` for all `q ≥ 1`. This is
  the open part (de Mathan and Teulié settle quadratic `ξ`; Einsiedler and Kleinbock show that
  the exceptions have Hausdorff dimension zero).
-/

namespace OMA.R_Bugeaud08_problem_10_8_R1

/-- The case of a `ξ` that is not badly approximable. -/
def H1 : Prop :=
  ∀ (ξ : ℝ) (p : ℕ), p.Prime →
    (∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) * distToNearestInt (q * ξ) < ε) →
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0

/-- The open part: badly approximable `ξ`. -/
def H2 : Prop :=
  ∀ (ξ : ℝ) (p : ℕ), p.Prime →
    (∃ ε : ℝ, 0 < ε ∧ ∀ q : ℕ, 1 ≤ q → ε ≤ (q : ℝ) * distToNearestInt (q * ξ)) →
    sInf {x : ℝ | ∃ q : ℕ, 1 ≤ q ∧
      x = q * padicNorm p q * distToNearestInt (q * ξ)} = 0

theorem main : H1 → H2 → type_of% @Bugeaud08.problem_10_8 := by
  intro h1 h2 ξ p hp
  by_cases h : ∀ ε : ℝ, 0 < ε → ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) * distToNearestInt (q * ξ) < ε
  · exact h1 ξ p hp h
  · apply h2 ξ p hp
    by_contra hbad
    apply h
    intro ε hε
    by_contra hq
    apply hbad
    refine ⟨ε, hε, fun q hq1 => ?_⟩
    by_contra hlt
    exact hq ⟨q, hq1, not_le.mp hlt⟩

end OMA.R_Bugeaud08_problem_10_8_R1
