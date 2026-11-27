import Mathlib

/-!
# The periodicity conjecture for the iterated sum of divisors

Source: https://arxiv.org/abs/2102.09941v2, Conjecture 3.1.
Credit: @rleshner

Theorem 2.1 defines the superscript as function iteration. In the entropy
condition we start the orbit at the conjectured input n, as in Conjecture 3.1.
Sample frequencies use the first K positive iterates; zero frequencies
contribute zero to the Shannon entropy.
-/

namespace OMA.S_arxiv_2102_09941

def divisorSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

def exponentPeriod (n : ℕ) : ℕ :=
  n.primeFactors.lcm fun p => n.factorization p + 1

noncomputable def frequency (n K r : ℕ) : ℝ :=
  (((Finset.range K).filter (fun t => (divisorSum^[t + 1]) n % n = r)).card : ℝ) / K

noncomputable def entropy (n K : ℕ) : ℝ :=
  ∑ r ∈ Finset.range n, Real.negMulLog (frequency n K r)

def conditions (n : ℕ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → Odd k → n ∣ (divisorSum^[k]) n) ∧
  (∃ T : ℕ, 0 < T ∧ T ∣ exponentPeriod n ∧
    Function.Periodic (fun k : ℕ => (divisorSum^[k + 1]) n % n) T) ∧
  Filter.Tendsto (entropy n) Filter.atTop (nhds (Real.log 2))

theorem main : ∀ n : ℕ, 2 ≤ n → (conditions n ↔ n = 6) := by
  sorry

end OMA.S_arxiv_2102_09941
