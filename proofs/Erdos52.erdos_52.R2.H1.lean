import OMAReductions.R_Erdos52_erdos_52_R2
import Mathlib

-- Step Erdos52.erdos_52.R2.H1: hypothesis H1 of reduction Erdos52.erdos_52.R2
-- Credit: @ivillar

/-!
The divisor bound `d(n) ≤ C n ^ η`. Writing `d(n) = ∏ (e_p + 1)` and `n ^ η = ∏ (p ^ η) ^ e_p`,
each factor satisfies `e + 1 ≤ M (p ^ η) ^ e` with `M = 1 + 1 / (η log 2)`, and
`e + 1 ≤ (p ^ η) ^ e` once `p ≥ 2 ^ (1 / η)`; only boundedly many primes need the factor `M`.
-/
namespace F2E52

theorem divisor_bound : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
    (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ η := by
  intro η hη
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = η * Real.log 2 := ⟨_, rfl⟩
  have hcpos : 0 < c := hc ▸ mul_pos hη (Real.log_pos (by norm_num))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + 1 / c := ⟨_, rfl⟩
  have hinv : 0 < 1 / c := one_div_pos.mpr hcpos
  have hM1 : 1 ≤ M := by rw [hM]; linarith
  have hMpos : 0 < M := by linarith
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, N₀ = ⌈(2 : ℝ) ^ (1 / η)⌉₊ := ⟨_, rfl⟩
  refine ⟨M ^ N₀, by positivity, fun n hn => ?_⟩
  have key : ∀ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) ≤
      (if p < N₀ then M else 1) * ((p : ℝ) ^ η) ^ (n.factorization p) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hq1 : 1 + c ≤ (p : ℝ) ^ η := by
      calc 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
        _ = (2 : ℝ) ^ η := by rw [Real.rpow_def_of_pos (by norm_num), hc, mul_comm]
        _ ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by norm_num) hp2 hη.le
    have hbern : 1 + (n.factorization p : ℝ) * c ≤ ((p : ℝ) ^ η) ^ (n.factorization p) := by
      calc 1 + (n.factorization p : ℝ) * c ≤ (1 + c) ^ (n.factorization p) :=
            one_add_mul_le_pow (by linarith) _
        _ ≤ ((p : ℝ) ^ η) ^ (n.factorization p) := pow_le_pow_left₀ (by linarith) hq1 _
    have he0 : (0 : ℝ) ≤ (n.factorization p : ℝ) := Nat.cast_nonneg _
    split_ifs with h
    · have h1 : (1 + 1 / c) * (1 + (n.factorization p : ℝ) * c) =
          1 + (n.factorization p : ℝ) * c + 1 / c + (n.factorization p : ℝ) := by
        field_simp
        ring
      push_cast
      calc (n.factorization p : ℝ) + 1 ≤ (1 + 1 / c) * (1 + (n.factorization p : ℝ) * c) := by
            rw [h1]
            nlinarith [mul_nonneg he0 hcpos.le]
        _ = M * (1 + (n.factorization p : ℝ) * c) := by rw [hM]
        _ ≤ M * ((p : ℝ) ^ η) ^ (n.factorization p) := mul_le_mul_of_nonneg_left hbern hMpos.le
    · have hpN : (2 : ℝ) ^ (1 / η) ≤ p := by
        have h' : N₀ ≤ p := not_lt.mp h
        calc (2 : ℝ) ^ (1 / η) ≤ (⌈(2 : ℝ) ^ (1 / η)⌉₊ : ℝ) := Nat.le_ceil _
          _ = (N₀ : ℝ) := by rw [hN₀]
          _ ≤ p := by exact_mod_cast h'
      have hq2 : (2 : ℝ) ≤ (p : ℝ) ^ η := by
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / η)) ^ η := by
              rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one]
          _ ≤ (p : ℝ) ^ η := Real.rpow_le_rpow (by positivity) hpN hη.le
      push_cast
      rw [one_mul]
      calc (n.factorization p : ℝ) + 1 = 1 + (n.factorization p : ℝ) * 1 := by ring
        _ ≤ (1 + 1 : ℝ) ^ (n.factorization p) := one_add_mul_le_pow (by norm_num) _
        _ ≤ ((p : ℝ) ^ η) ^ (n.factorization p) :=
            pow_le_pow_left₀ (by norm_num) (by linarith) _
  have hd : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    rw [Nat.card_divisors hn, Nat.cast_prod]
  have hnprod : (n : ℝ) ^ η = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ η) ^ (n.factorization p) := by
    have h1 : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
      rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
      simp only [Nat.cast_pow]
    rw [h1, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity) η]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p), mul_comm,
      Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast]
  have hg : ∏ p ∈ n.primeFactors, (if p < N₀ then M else 1) ≤ M ^ N₀ := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hM1
    calc (n.primeFactors.filter (· < N₀)).card ≤ (Finset.range N₀).card :=
          Finset.card_le_card (fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)
      _ = N₀ := Finset.card_range N₀
  rw [hd, hnprod]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ)
      ≤ ∏ p ∈ n.primeFactors,
          ((if p < N₀ then M else 1) * ((p : ℝ) ^ η) ^ (n.factorization p)) :=
        Finset.prod_le_prod (fun p _ => by positivity) key
    _ = (∏ p ∈ n.primeFactors, (if p < N₀ then M else 1)) *
          ∏ p ∈ n.primeFactors, ((p : ℝ) ^ η) ^ (n.factorization p) := Finset.prod_mul_distrib
    _ ≤ M ^ N₀ * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ η) ^ (n.factorization p) :=
        mul_le_mul_of_nonneg_right hg (Finset.prod_nonneg fun p _ => by positivity)

end F2E52

theorem OMA.solution : OMA.R_Erdos52_erdos_52_R2.H1 :=
  F2E52.divisor_bound
