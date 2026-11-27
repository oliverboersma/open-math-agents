import FormalConjectures.ErdosProblems.«968»
import Mathlib

/-! Increasing triples of u_n = p_n / n from chains of large gaps. Ford, Maynard and Tao,
Chains of large gaps between primes (2018), Theorem 1 with k = 2: there are consecutive
gaps p_(n+1) - p_n and p_(n+2) - p_(n+1) below X that both exceed a constant times
log X log log X log log log log X / log log log X, hence any fixed multiple of log X,
for all large X. The Chebyshev lower bound for the prime counting function gives
u_n at most 2 log p_n, so both gaps beat the local thresholds u_n and u_(n+1), which is
exactly u_n < u_(n+1) < u_(n+2). -/

namespace OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1
open Filter

/-- Two consecutive prime gaps exceeding any fixed multiple of the logarithm,
a consequence of the Ford-Maynard-Tao theorem on chains of large gaps. -/
def H1 : Prop := ∀ C : ℝ, ∀ N : ℕ, ∃ n ≥ N,
  C * Real.log (Nat.nth Nat.Prime n) ≤
      (Nat.nth Nat.Prime (n + 1) : ℝ) - (Nat.nth Nat.Prime n : ℝ) ∧
  C * Real.log (Nat.nth Nat.Prime (n + 1)) ≤
      (Nat.nth Nat.Prime (n + 2) : ℝ) - (Nat.nth Nat.Prime (n + 1) : ℝ)

/-- The Chebyshev bound for the normalized n-th prime. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
  Erdos968.u n ≤ 2 * Real.log (Nat.nth Nat.Prime n)

theorem main : H1 → H2 →
    type_of% @Erdos968.erdos_968.variants.infinite_increasingTriples := by
  intro hfmt hu
  have hev2 : ∀ᶠ n in atTop, Erdos968.u n ≤ 2 * Real.log (Nat.nth Nat.Prime n) ∧
      Erdos968.u (n + 1) ≤ 2 * Real.log (Nat.nth Nat.Prime (n + 1)) :=
    hu.and ((tendsto_add_atTop_nat 1).eventually hu)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev2
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  obtain ⟨n, hn, hg1, hg2⟩ := hfmt 3 (max N0 (M + 1))
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M < n := lt_of_lt_of_le (Nat.lt_succ_self M) (le_trans (le_max_right _ _) hn)
  obtain ⟨h1, h2⟩ := hN0 n hn0
  have key : n ∈ {n : ℕ | Erdos968.u n < Erdos968.u (n + 1) ∧
      Erdos968.u (n + 1) < Erdos968.u (n + 2)} := by
    have hp1 : (2 : ℝ) ≤ Nat.nth Nat.Prime n := by
      exact_mod_cast (Nat.prime_nth_prime n).two_le
    have hp2 : (2 : ℝ) ≤ Nat.nth Nat.Prime (n + 1) := by
      exact_mod_cast (Nat.prime_nth_prime (n + 1)).two_le
    have hl1 : 0 < Real.log (Nat.nth Nat.Prime n) := Real.log_pos (by linarith)
    have hl2 : 0 < Real.log (Nat.nth Nat.Prime (n + 1)) := Real.log_pos (by linarith)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
    have hn3 : (0 : ℝ) < (n : ℝ) + 2 + 1 := by positivity
    simp only [Erdos968.u, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h1 h2 ⊢
    rw [div_le_iff₀ hn1] at h1
    rw [div_le_iff₀ hn2] at h2
    have e1 := mul_le_mul_of_nonneg_right hg1 hn1.le
    have e2 := mul_le_mul_of_nonneg_right hg2 hn2.le
    have f1 := mul_pos hl1 hn1
    have f2 := mul_pos hl2 hn2
    refine ⟨?_, ?_⟩
    · rw [div_lt_div_iff₀ hn1 hn2]
      nlinarith
    · rw [div_lt_div_iff₀ hn2 hn3]
      nlinarith
  exact absurd (hM key) (not_le.2 hnM)

end OMA.R_Erdos968_erdos_968_variants_infinite_increasingTriples_R1
