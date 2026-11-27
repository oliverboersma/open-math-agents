import Mathlib

/-!
# Hyman's conjectured persistence density (Conjecture 3.17)

Source: https://arxiv.org/abs/2603.18243
Credit: @rleshner

Corollary 3.16 specifies persistence at a given sample depth. Conjecture
3.17 sends the upper base cutoff B to infinity. We use the standard survey
depth N = 10,000 (abstract and Section 4.4). Writing n = B − 1 gives the
exact denominator in (3.17), with the bases 2 through n + 1 inclusive.
-/

namespace OMA.S_arxiv_2603_18243

open Filter
open scoped Topology

/-- The successive complete quotients of a simple continued fraction. -/
noncomputable def completeQuotient (x : ℝ) : ℕ → ℝ
  | 0 => x
  | k + 1 => (Int.fract (completeQuotient x k))⁻¹

/-- The partial quotient at index k (all quotients here are nonnegative). -/
noncomputable def digit (x : ℝ) (k : ℕ) : ℕ := ⌊completeQuotient x k⌋₊

/-- The two successive denominators (qₖ₋₁,qₖ), initialized by (0,1). -/
noncomputable def denominatorPair (x : ℝ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 =>
      let p := denominatorPair x k
      (p.2, digit x (k + 1) * p.2 + p.1)

/-- Corollary 3.16's PERS criterion. The fractional-part condition requires
that the continued fraction has not terminated before the next digit. -/
def persistent (N b : ℕ) : Prop :=
  let x := Real.logb 10 b
  ∃ k : ℕ, (∀ j ≤ k, Int.fract (completeQuotient x j) ≠ 0) ∧
    (denominatorPair x k).2 ≤ N ∧
    (N : ℝ) * Real.log N < ((digit x (k + 1) * (denominatorPair x k).2 : ℕ) : ℝ)

open scoped Classical in
/-- Counts the bases 2 through n + 1, inclusive, satisfying P. -/
noncomputable def blockCount (P : ℕ → Prop) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if P (i+2) then 1 else 0

/-- Natural density of persistent bases at the standard survey depth. -/
theorem main :
    Tendsto (fun n : ℕ => (blockCount (persistent 10000) n : ℝ) / (n : ℝ))
      atTop (𝓝 (1/12 : ℝ)) := by
  sorry

end OMA.S_arxiv_2603_18243
