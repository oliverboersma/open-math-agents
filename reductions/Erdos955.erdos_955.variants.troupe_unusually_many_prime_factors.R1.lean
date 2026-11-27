import FormalConjectures.ErdosProblems.«955»
import Mathlib

/-! Reduction of Troupe's upper-tail statement for the number of prime factors of s(n) to the
same statement normalised by log log n instead of log log s(n), together with the elementary
bound s(n) ^ 2 >= n for composite n. A prime n has s(n) = 1 and is never in the exceptional
set; for composite n the bound gives log log s(n) >= log log n - log 2, which is absorbed by
halving epsilon once n is large. -/

namespace OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1

open Filter Topology

/-- Troupe (J. Number Theory 2015), upper half of the normal-order theorem for the number of
distinct prime factors of s(n), with the normalisation log log n. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    {n : ℕ | (1 + ε) * Real.log (Real.log (n : ℝ)) <
      (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)}.HasDensity 0

/-- A composite n has a proper divisor at least sqrt n, so s(n) ^ 2 >= n. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ¬ n.Prime → n ≤ Erdos955.s n ^ 2

lemma s_prime {p : ℕ} (hp : p.Prime) : Erdos955.s p = 1 := by
  have h : ArithmeticFunction.sigma 1 p = p + 1 := by
    rw [ArithmeticFunction.sigma_one_apply, hp.sum_divisors]
  unfold Erdos955.s
  omega

theorem main : H1 → H2 →
    type_of% @Erdos955.erdos_955.variants.troupe_unusually_many_prime_factors := by
  intro h1 h2 ε hε
  have hS := h1 (ε / 2) (by positivity)
  have hll : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp
    (hll.eventually_ge_atTop ((1 + ε) * Real.log 2 * (2 / ε)))
  have hsub : {x : ℕ | (1 + ε) * Real.log (Real.log (Erdos955.s x)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s x) : ℝ)} ⊆
      {n : ℕ | (1 + ε / 2) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∪ Set.Iio (max N0 2) := by
    intro n hn
    by_cases hlt : n < max N0 2
    · exact Or.inr hlt
    · left
      have hn1 : max N0 2 ≤ n := not_lt.mp hlt
      have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn1
      have hnN0 : N0 ≤ n := le_trans (le_max_left _ _) hn1
      have hnp : ¬ n.Prime := by
        intro hp
        have hs1 : Erdos955.s n = 1 := s_prime hp
        rw [Set.mem_ofPred_eq, hs1] at hn
        simp at hn
      have hsq := h2 n hn2 hnp
      have hLL := hN0 n hnN0
      have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hnpos : (0 : ℝ) < n := by linarith
      have hLpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
      have hsqR : (n : ℝ) ≤ (Erdos955.s n : ℝ) ^ 2 := by exact_mod_cast hsq
      have hlog1 : Real.log (n : ℝ) ≤ 2 * Real.log (Erdos955.s n : ℝ) := by
        have h := Real.log_le_log hnpos hsqR
        rw [Real.log_pow] at h
        push_cast at h
        exact h
      have hhalf : 0 < Real.log (n : ℝ) / 2 := by positivity
      have hlog2 : Real.log (Real.log (n : ℝ)) - Real.log 2 ≤
          Real.log (Real.log (Erdos955.s n : ℝ)) := by
        rw [← Real.log_div hLpos.ne' (by norm_num)]
        exact Real.log_le_log hhalf (by linarith)
      have hkey : (1 + ε) * Real.log 2 ≤ ε / 2 * Real.log (Real.log (n : ℝ)) := by
        have h := mul_le_mul_of_nonneg_left hLL (by positivity : (0 : ℝ) ≤ ε / 2)
        have he : ε / 2 * ((1 + ε) * Real.log 2 * (2 / ε)) = (1 + ε) * Real.log 2 := by
          field_simp
        linarith
      rw [Set.mem_ofPred_eq] at hn ⊢
      have hmul : (1 + ε) * (Real.log (Real.log (n : ℝ)) - Real.log 2) ≤
          (1 + ε) * Real.log (Real.log (Erdos955.s n : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
      nlinarith
  rw [Set.HasDensity] at hS ⊢
  have hN : Tendsto (fun b : ℕ => ((max N0 2 : ℕ) : ℝ) / (b : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsum := hS.add hN
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun b => ?_)
    (fun b => ?_)
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hfin : (({n : ℕ | (1 + ε / 2) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∩ Set.Iio b) ∪
        Set.Iio (max N0 2)).Finite :=
      ((Set.finite_Iio b).inter_of_right _).union (Set.finite_Iio _)
    have hle1 := Set.ncard_le_ncard (s := {x : ℕ | (1 + ε) * Real.log (Real.log (Erdos955.s x)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s x) : ℝ)} ∩ Set.Iio b)
      (fun x hx => by
        rcases hsub hx.1 with h | h
        · exact Or.inl ⟨h, hx.2⟩
        · exact Or.inr h) hfin
    have hle2 := Set.ncard_union_le ({n : ℕ | (1 + ε / 2) * Real.log (Real.log (n : ℝ)) <
        (ArithmeticFunction.cardDistinctFactors (Erdos955.s n) : ℝ)} ∩ Set.Iio b)
      (Set.Iio (max N0 2))
    have hle3 : (Set.Iio (max N0 2)).ncard = max N0 2 := Nat.ncard_Iio _
    have hle4 := hle1.trans hle2
    rw [hle3] at hle4
    exact_mod_cast hle4

end OMA.R_Erdos955_erdos_955_variants_troupe_unusually_many_prime_factors_R1
