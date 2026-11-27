import Mathlib

/-!
# Counts of positive and negative Möbius values (OEIS A070548)

Stefan Steinerberger's asymptotics, with explicit natural indices. The
two sign counts together count the squarefree integers. The middle statement
records the RH error bound in its eventual form for every positive epsilon.

Source: https://oeis.org/A070548 (OEIS Foundation, CC BY-SA 4.0)
Formalization: @DomTheDeveloper
-/

namespace OMA.S_oeis_a070548

noncomputable def countSign (s : ℤ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => ArithmeticFunction.moebius k = s)).card

theorem main :
    Filter.Tendsto (fun n : ℕ => ((countSign 1 n : ℝ) + countSign (-1) n) / n)
      Filter.atTop (nhds (6 / Real.pi ^ 2)) ∧
    (RiemannHypothesis → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |(countSign 1 n : ℝ) - countSign (-1) n| < (n : ℝ) ^ (1 / 2 + ε)) ∧
    Filter.Tendsto (fun n : ℕ => (countSign 1 n : ℝ) / n)
      Filter.atTop (nhds (3 / Real.pi ^ 2)) := by
  sorry

end OMA.S_oeis_a070548
