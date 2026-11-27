import Mathlib

/-!
# Zero divisor conjecture for finite fields

Source: https://mathoverflow.net/questions/62548/zero-divisor-conjecture-for-finite-fields
Question by Kate Juschenko, CC BY-SA 3.0.
Credit: @my-other-github-account

The first conjunct is the first displayed question, interpreted as the universal
zero-divisor conjecture. The second conjunct is the separate, weaker question
introduced by `In particular`. Over F2 the minimum number of group elements
in a sum representing a is exactly a.coeff.support.card. Zero divisors here are
nonzero and annihilate a nonzero element on the right. The left-handed
formulation is equivalent by the group-inversion anti-automorphism.
The unspecified positive constant R is read as a real number; no optimal
bound is requested in the source.

This states the questions, not an assertion that both have positive answers.
A counterexample to the first conjunct refutes main; it does not refute the
separate support-size bound.
-/

namespace OMA.S_mo_62548

/-- The first question, for arbitrary torsion-free groups and finite fields. -/
def ZeroDivisorConjecture : Prop :=
  ∀ (G K : Type) [Group G] [Field K] [Finite K],
    (∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1) →
    ∀ a b : MonoidAlgebra K G, a * b = 0 → a = 0 ∨ b = 0

/-- The uniform positive support-size lower bound in the second question. -/
def SupportBound : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ (G : Type) [Group G],
    (∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1) →
    ∀ a b : MonoidAlgebra (ZMod 2) G,
      a ≠ 0 → b ≠ 0 → a * b = 0 → R < (a.coeff.support.card : ℝ)

theorem main : ZeroDivisorConjecture ∧ SupportBound := by
  sorry

end OMA.S_mo_62548
