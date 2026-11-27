import Mathlib

/-!
# Erdős Problem 928

Source: https://www.erdosproblems.com/928
Credit: @timlantin

Let $\alpha,\beta\in (0,1)$ and let $P(n)$ denote the largest prime divisor of $n$. Does the
density of integers $n$ such that $P(n)<n^{\alpha}$ and $P(n+1)<(n+1)^\beta$ exist?

Formalization notes:
* $P(n)$ is `P n`, the largest prime factor of $n$ (with $P(0) = P(1) = 0$). The values at
  $n = 0, 1$ do not affect densities.
* Natural density is defined here directly, as the limit of $|S \cap [0, N)| / N$.
* Written with Claude Code (AI-assisted).
-/

namespace OMA.S_erdos_928

open Filter Topology

/-- The largest prime factor of `n`, or `0` if `n` has none. -/
def P (n : ℕ) : ℕ := n.primeFactors.sup id

/-- The set of $n$ with $P(n) < n^{\alpha}$ and $P(n+1) < (n+1)^{\beta}$. -/
def S (α β : ℝ) : Set ℕ :=
  {n | (P n : ℝ) < (n : ℝ) ^ α ∧ (P (n + 1) : ℝ) < ((n + 1 : ℕ) : ℝ) ^ β}

/-- `A` has natural density `d`. -/
def HasNatDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ ↦ ((Set.ncard (A ∩ Set.Iio N) : ℕ) : ℝ) / N) atTop (𝓝 d)

/-- For all $\alpha, \beta \in (0, 1)$ the set `S α β` has a natural density. -/
theorem main :
    ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∃ d : ℝ, HasNatDensity (S α β) d := by
  sorry

end OMA.S_erdos_928
