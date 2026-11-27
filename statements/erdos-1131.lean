import Mathlib

/-!
# Erdős Problem 1131: the conjectured asymptotic

Source: https://www.erdosproblems.com/1131
Credit: @seanm27lol
Lean disproof of the asymptotic subquestion:
https://github.com/seanm27lol/erdos-1131-lean/blob/31574acf09ae50430c08da92288800fe7d26c7fd/Erdos1131/Main.lean

The source asks for the minimum of the integrated sum of squared Lagrange basis
polynomials, then asks whether that minimum is asymptotic to 2 with first-order
term -1/n. The theorem below states the latter question in its conjectured
direction. Determining the exact extremal value for each n is a separate question.

The embeddings encode distinct nodes. The infimum avoids assuming attainment.
Over the reals, squaring a basis value is the same as squaring its absolute value.
Indexing by n + 1 runs through the positive node counts.
-/

open scoped BigOperators Interval
open Filter Set

namespace OMA.S_erdos_1131

def Admissible {n : ℕ} (x : Fin n ↪ ℝ) : Prop :=
  ∀ k, x k ∈ Set.Icc (-1 : ℝ) 1

noncomputable def functional {n : ℕ} (x : Fin n ↪ ℝ) : ℝ :=
  ∫ t in (-1 : ℝ)..1,
    ∑ k : Fin n,
      ((Lagrange.basis Finset.univ (x : Fin n → ℝ) k).eval t) ^ 2

def values (n : ℕ) : Set ℝ :=
  {y | ∃ x : Fin n ↪ ℝ, Admissible x ∧ functional x = y}

noncomputable def M (n : ℕ) : ℝ :=
  sInf (values n)

noncomputable def scaledDefect (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * (2 - M (n + 1))

theorem main : Tendsto scaledDefect atTop (nhds 1) := by
  sorry

end OMA.S_erdos_1131
