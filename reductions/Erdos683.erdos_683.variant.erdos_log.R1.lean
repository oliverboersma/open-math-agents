import FormalConjectures.ErdosProblems.«683»

-- Reduction Erdos683.erdos_683.variant.erdos_log.R1 of Erdős Problem 683 — erdos log
-- Credit: @ptc-prover-bot
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős's bound P(C(n,k)) ≫ min(n - k + 1, k log k) from prime gaps

Following Erdős [Er55d] (Nieuw Arch. Wisk. (3) 3 (1955) 124–128, proof of Theorem 1):
* `H1` (Hoheisel–Ingham): every interval (x, x + C x^θ] contains a prime, for some θ < 2/3
  (Ingham 1937 gives θ = 5/8). For n ≤ k^(3/2) it puts a prime p in (n - k, n]; such a p exceeds
  k, so it divides C(n,k), and P(C(n,k)) ≥ p ≥ n - k + 1. This is the only non-elementary input.
* `H2` (the range n > k^(3/2), equations (6)–(8) of [Er55d]): if every prime factor of C(n,k) were
  below k log k / 20 then (n/(2k))^k ≤ C(n,k) ≤ n^(π(k log k / 20)), since every prime power
  dividing C(n,k) is at most n; Chebyshev's θ(x) ≤ x log 4 makes this impossible once log k ≥ 20.
`main` handles small k (where P(C(n,k)) ≥ 2 suffices) and fixes the constant.
-/

open Finset Real

namespace OMA.R_Erdos683_erdos_683_variant_erdos_log_R1

lemma le_P {n k p : ℕ} (hp : p ∈ (n.choose k).primeFactors) : p ≤ Erdos683.P n k :=
  Finset.le_sup (f := id) hp

lemma two_le_P {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n / 2) : 2 ≤ Erdos683.P n k := by
  have hn : 2 ≤ n.choose k := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_succ_succ, Nat.succ_eq_add_one]
    have h1 := Nat.choose_pos (show j ≤ m by omega)
    have h2 := Nat.choose_pos (show j + 1 ≤ m by omega)
    omega
  obtain ⟨q, hq⟩ := Nat.exists_prime_and_dvd (show n.choose k ≠ 1 by omega)
  have hmem : q ∈ (n.choose k).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq.1, hq.2, by omega⟩
  exact hq.1.two_le.trans (le_P hmem)

/-- A prime in (n - k, n] that exceeds k divides C(n,k). -/
lemma prime_dvd_choose {n k p : ℕ} (hp : p.Prime) (hkp : k < p) (hlo : n - k < p) (hhi : p ≤ n)
    (hkn : k ≤ n) : p ∣ n.choose k := by
  have h := Nat.choose_mul_factorial_mul_factorial hkn
  have hdvd : p ∣ n.factorial := hp.dvd_factorial.mpr hhi
  rw [← h] at hdvd
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
    · exact h2
    · exact absurd (hp.dvd_factorial.mp h2) (by omega)
  · exact absurd (hp.dvd_factorial.mp h1) (by omega)

/-- Hoheisel–Ingham type prime gaps: some exponent θ < 2/3 (Ingham 1937: θ = 5/8). -/
def H1 : Prop :=
  ∃ θ : ℝ, θ < 2 / 3 ∧ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + C * (x : ℝ) ^ θ

/-- The range n > k^{3/2} (Erdős's elementary argument, equations (6)–(8) of [Er55d]). -/
def H2 : Prop :=
  ∀ n k : ℕ, Real.exp 20 ≤ k → k ≤ n / 2 → k ^ 3 < n ^ 2 →
    (k : ℝ) * Real.log k / 20 ≤ Erdos683.P n k

theorem main : H1 → H2 → type_of% @Erdos683.erdos_683.variant.erdos_log := by
  rintro ⟨θ, hθ, C, hgap⟩ h2
  set θ' := max θ 0 with hθ'
  set C' := max C 0 with hC'
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hθ'lt : θ' < 2 / 3 := max_lt hθ (by norm_num)
  set e := 1 - 3 / 2 * θ' with he
  have hepos : 0 < e := by rw [he]; linarith
  -- k^e eventually exceeds C' + 1
  obtain ⟨K1, hK1⟩ := (((tendsto_rpow_atTop hepos).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (C' + 1)).exists_forall_of_atTop
  set K : ℕ := max ⌈Real.exp 20⌉₊ (K1 + 2) with hKdef
  have hK1R : (1 : ℝ) ≤ K := by
    have : 1 ≤ K := le_trans (by omega) (le_max_right _ _)
    exact_mod_cast this
  have hKpos : (0 : ℝ) < K * Real.log K + 1 := by
    have := Real.log_nonneg hK1R; positivity
  set c : ℝ := min (1 / 20) (2 / (K * Real.log K + 1)) with hc
  have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
  have hc3 : c ≤ 1 / 20 := min_le_left _ _
  have hc4 : c ≤ 2 / (K * Real.log K + 1) := min_le_right _ _
  refine ⟨c, hcpos, fun n k ⟨hk, hkn⟩ => ?_⟩
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hB : 0 ≤ (k : ℝ) * Real.log k := mul_nonneg (by linarith) (Real.log_nonneg hkR)
  rw [ge_iff_le]
  by_cases hkK : K ≤ k
  · have hexp : Real.exp 20 ≤ k := by
      have h1 := Nat.le_ceil (Real.exp 20)
      have h2 : (⌈Real.exp 20⌉₊ : ℝ) ≤ K := by exact_mod_cast le_max_left _ _
      have h3 : (K : ℝ) ≤ k := by exact_mod_cast hkK
      linarith
    by_cases hn : k ^ 3 < n ^ 2
    · have := h2 n k hexp hkn hn
      calc min (↑(n - k + 1) : ℝ) (c * k * Real.log k) ≤ c * k * Real.log k := min_le_right _ _
        _ ≤ 1 / 20 * k * Real.log k := by rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hc3 hB
        _ = k * Real.log k / 20 := by ring
        _ ≤ _ := this
    · -- n ≤ k^{3/2}: a prime in (n - k, n]
      push Not at hn
      have hx2 : 2 ≤ n - k := by
        have : 1 ≤ K1 + 2 - 1 := by omega
        have : K1 + 2 ≤ K := le_max_right _ _
        omega
      obtain ⟨p, hp, hxp, hpC⟩ := hgap (n - k) hx2
      have hxR : (1 : ℝ) ≤ ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - k by omega)
      have hxn : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
      -- n ≤ k^{3/2}
      have hn32 : (n : ℝ) ≤ (k : ℝ) ^ ((3 : ℝ) / 2) := by
        have h1 : ((n : ℝ)) ^ 2 ≤ (k : ℝ) ^ 3 := by exact_mod_cast hn
        have h2 : (n : ℝ) = (((n : ℝ)) ^ 2) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        have h3 : (k : ℝ) ^ ((3 : ℝ) / 2) = (((k : ℝ)) ^ 3) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
        rw [h2, h3]; exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
      -- C x^θ ≤ C' k^{3θ'/2} < k
      have hpow : (((n - k : ℕ) : ℝ)) ^ θ ≤ (k : ℝ) ^ ((3 : ℝ) / 2 * θ') := by
        calc (((n - k : ℕ) : ℝ)) ^ θ ≤ (((n - k : ℕ) : ℝ)) ^ θ' :=
              Real.rpow_le_rpow_of_exponent_le hxR (le_max_left _ _)
          _ ≤ (n : ℝ) ^ θ' := Real.rpow_le_rpow (by positivity) hxn hθ'0
          _ ≤ ((k : ℝ) ^ ((3 : ℝ) / 2)) ^ θ' := Real.rpow_le_rpow (by positivity) hn32 hθ'0
          _ = (k : ℝ) ^ ((3 : ℝ) / 2 * θ') := by rw [← Real.rpow_mul (by positivity)]
      have hCx : C * (((n - k : ℕ) : ℝ)) ^ θ ≤ C' * (k : ℝ) ^ ((3 : ℝ) / 2 * θ') := by
        have hxθ : 0 ≤ (((n - k : ℕ) : ℝ)) ^ θ := by positivity
        rcases le_or_gt 0 C with hC0 | hC0
        · calc C * (((n - k : ℕ) : ℝ)) ^ θ ≤ C' * (((n - k : ℕ) : ℝ)) ^ θ :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) hxθ
            _ ≤ C' * (k : ℝ) ^ ((3 : ℝ) / 2 * θ') := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
        · have : C * (((n - k : ℕ) : ℝ)) ^ θ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hC0.le hxθ
          have : 0 ≤ C' * (k : ℝ) ^ ((3 : ℝ) / 2 * θ') := mul_nonneg (le_max_right _ _) (by positivity)
          linarith
      have hsmall : C' * (k : ℝ) ^ ((3 : ℝ) / 2 * θ') < k := by
        have hke := hK1 k (by have : K1 + 2 ≤ K := le_max_right _ _; omega)
        simp only [Function.comp] at hke
        have hsplit : (k : ℝ) = (k : ℝ) ^ e * (k : ℝ) ^ ((3 : ℝ) / 2 * θ') := by
          rw [← Real.rpow_add (by linarith), he]; norm_num
        have hpos : 0 < (k : ℝ) ^ ((3 : ℝ) / 2 * θ') := by positivity
        calc C' * (k : ℝ) ^ ((3 : ℝ) / 2 * θ') < (k : ℝ) ^ e * (k : ℝ) ^ ((3 : ℝ) / 2 * θ') :=
              mul_lt_mul_of_pos_right (by linarith) hpos
          _ = k := hsplit.symm
      have hpn : (p : ℝ) < n := by
        have : ((n - k : ℕ) : ℝ) = n - k := by rw [Nat.cast_sub (by omega)]
        linarith
      have hpn' : p ≤ n := by exact_mod_cast hpn.le
      have hdvd := prime_dvd_choose hp (by omega) hxp hpn' (by omega)
      have hmem : p ∈ (n.choose k).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, hdvd, (Nat.choose_pos (by omega)).ne'⟩
      have hPp := le_P hmem
      calc min (↑(n - k + 1) : ℝ) (c * k * Real.log k) ≤ ↑(n - k + 1) := min_le_left _ _
        _ ≤ (p : ℝ) := by exact_mod_cast hxp
        _ ≤ _ := by exact_mod_cast hPp
  · -- small k: c k log k ≤ 2 ≤ P
    push Not at hkK
    have hkK' : (k : ℝ) ≤ K := by exact_mod_cast hkK.le
    have hlogK : Real.log k ≤ Real.log K := Real.log_le_log (by linarith) hkK'
    have hBK : (k : ℝ) * Real.log k ≤ K * Real.log K :=
      mul_le_mul hkK' hlogK (Real.log_nonneg hkR) (by linarith)
    have hP : (2 : ℝ) ≤ Erdos683.P n k := by exact_mod_cast two_le_P hk hkn
    calc min (↑(n - k + 1) : ℝ) (c * k * Real.log k) ≤ c * k * Real.log k := min_le_right _ _
      _ = c * (k * Real.log k) := by ring
      _ ≤ 2 / (K * Real.log K + 1) * (K * Real.log K + 1) := by
          apply mul_le_mul hc4 (by linarith) hB (by positivity)
      _ = 2 := by field_simp
      _ ≤ _ := hP

end OMA.R_Erdos683_erdos_683_variant_erdos_log_R1
