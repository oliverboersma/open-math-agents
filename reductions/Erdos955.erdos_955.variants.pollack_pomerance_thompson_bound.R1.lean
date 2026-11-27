import FormalConjectures.ErdosProblems.«955»
import Mathlib

/-! Reduction of the Pollack--Pomerance--Thompson density statement to the uniform theorem of
their paper (Divisor-sum fibers, Mathematika 64 (2018)) and an elementary bound for the
sum-of-divisors function. Every n below x has s(n) below x (1 + log x), so only the part of A
below that bound matters, and that part has at most x ^ (1/2 + o(1)) elements. -/

namespace OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1

open Filter Topology

/-- Pollack, Pomerance and Thompson, uniformly in the set: if eps tends to 0 then the number of
n up to x whose sum of proper divisors lies in a set of at most x ^ (1/2 + eps x) positive
integers is o(x), uniformly over such sets. -/
def H1 : Prop :=
  ∀ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) → ∀ δ : ℝ, 0 < δ →
    ∀ᶠ x : ℕ in atTop, ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) →
      (A.card : ℝ) ≤ (x : ℝ) ^ ((1 / 2 : ℝ) + ε x) →
      (((Finset.Icc 1 x).filter (fun n => Erdos955.s n ∈ A)).card : ℝ) ≤ δ * x

/-- The elementary bound sigma(n) <= n (1 + log n), from sigma(n) / n = sum of 1 / d over the
divisors d of n. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → (ArithmeticFunction.sigma 1 n : ℝ) ≤ n * (1 + Real.log n)

lemma s_pos_of_two_le {n : ℕ} (hn : 2 ≤ n) : 1 ≤ Erdos955.s n := by
  have h1 : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    rw [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors_self _ (by omega)
  have h2 : ∑ d ∈ ({1, n} : Finset ℕ), d = 1 + n := Finset.sum_pair (by omega)
  have h3 : ∑ d ∈ ({1, n} : Finset ℕ), d ≤ ∑ d ∈ n.divisors, d :=
    Finset.sum_le_sum_of_subset h1
  have h4 : ArithmeticFunction.sigma 1 n = ∑ d ∈ n.divisors, d := by
    simp [ArithmeticFunction.sigma_one_apply]
  unfold Erdos955.s
  omega

lemma tendsto_log_ratio :
    Tendsto (fun b : ℕ => Real.log ((b : ℝ) * (2 + Real.log b)) / Real.log b) atTop (𝓝 1) := by
  have hL : Tendsto (fun b : ℕ => 2 + Real.log (b : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h0 : Tendsto (fun b : ℕ => Real.log (2 + Real.log (b : ℝ)) / Real.log b) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hL
    refine h.congr (fun b => ?_)
    simp only [Function.comp_apply, pow_one]
    congr 1
    ring
  have h1 : Tendsto (fun b : ℕ => 1 + Real.log (2 + Real.log (b : ℝ)) / Real.log b) atTop
      (𝓝 1) := by
    simpa using h0.const_add 1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with b hb
  have hb' : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hlog : 0 < Real.log (b : ℝ) := Real.log_pos (by linarith)
  rw [Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)), add_div,
    div_self hlog.ne']

theorem main : H1 → H2 →
    type_of% @Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound := by
  intro h1 h2 A ε hε hA
  classical
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ → ℕ, ∀ b : ℕ, M b = ⌊(b : ℝ) * (1 + Real.log b)⌋₊ + 1 :=
    ⟨_, fun _ => rfl⟩
  have hbM : ∀ b : ℕ, b ≤ M b := by
    intro b
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · exact Nat.zero_le _
    · have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      have hlog : 0 ≤ Real.log (b : ℝ) := Real.log_nonneg hb1
      have hfl : b ≤ ⌊(b : ℝ) * (1 + Real.log b)⌋₊ := Nat.le_floor (by nlinarith)
      rw [hMdef]
      omega
  have hM : Tendsto M atTop atTop := tendsto_atTop_mono hbM tendsto_id
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℕ → ℝ, ∀ b : ℕ, ε' b =
      (1 / 2 + ε (M b)) * (Real.log ((b : ℝ) * (2 + Real.log b)) / Real.log b) - 1 / 2 :=
    ⟨_, fun _ => rfl⟩
  have hεM : Tendsto (fun b => ε (M b)) atTop (𝓝 0) := hε.comp hM
  have hε' : Tendsto ε' atTop (𝓝 0) := by
    have h := ((hεM.const_add (1 / 2)).mul tendsto_log_ratio).sub_const (1 / 2)
    have hfun : ε' = fun b : ℕ => (1 / 2 + ε (M b)) *
        (Real.log ((b : ℝ) * (2 + Real.log b)) / Real.log b) - 1 / 2 := funext hε'def
    rw [hfun]
    simpa using h
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro η hη
  have hE2 := hM.eventually hA
  have hE3 : ∀ᶠ b in atTop, dist (ε (M b)) 0 < 1 / 2 :=
    Metric.tendsto_nhds.mp hεM (1 / 2) (by norm_num)
  have hE4 := h1 ε' hε' (η / 2) (by positivity)
  have hE5 : ∀ᶠ b : ℕ in atTop, 4 / η < (b : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [eventually_ge_atTop 2, hE2, hE3, hE4, hE5] with b hb2 hcount heps hppt hbig
  have hb1 : (2 : ℝ) ≤ b := by exact_mod_cast hb2
  have hbpos : (0 : ℝ) < b := by linarith
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by linarith)
  have hAbpos : ∀ a ∈ (Finset.Ico 1 (M b)).filter (· ∈ A), 0 < a := by
    intro a ha
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).1
  have he0 : 0 ≤ 1 / 2 + ε (M b) := by
    rw [Real.dist_eq, sub_zero] at heps
    have := (abs_lt.mp heps).1
    linarith
  have hRpos : 0 < (b : ℝ) * (2 + Real.log b) := mul_pos hbpos (by linarith)
  have hMR : ((M b : ℕ) : ℝ) ≤ (b : ℝ) * (2 + Real.log b) := by
    have hfl : ((⌊(b : ℝ) * (1 + Real.log b)⌋₊ : ℕ) : ℝ) ≤ (b : ℝ) * (1 + Real.log b) :=
      Nat.floor_le (mul_nonneg hbpos.le (by linarith))
    have hring : (b : ℝ) * (2 + Real.log b) = (b : ℝ) * (1 + Real.log b) + b := by ring
    rw [hMdef, hring]
    push_cast
    linarith
  have hpow : ((b : ℝ) * (2 + Real.log b)) ^ (1 / 2 + ε (M b)) =
      (b : ℝ) ^ ((1 / 2 : ℝ) + ε' b) := by
    rw [Real.rpow_def_of_pos hRpos, Real.rpow_def_of_pos hbpos, hε'def]
    congr 1
    field_simp
    ring
  have hcardAb : ((((Finset.Ico 1 (M b)).filter (· ∈ A)).card : ℕ) : ℝ) ≤
      (b : ℝ) ^ ((1 / 2 : ℝ) + ε' b) := by
    rw [← hpow]
    refine le_trans (le_trans (Nat.cast_le.mpr ?_) hcount)
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hMR he0)
    rw [Nat.count_eq_card_filter_range]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hx.1).2, hx.2⟩
  have hres := hppt _ hAbpos hcardAb
  have hsub : (Finset.range b).filter (fun n => Erdos955.s n ∈ A) ⊆
      {0, 1} ∪ (Finset.Icc 1 b).filter
        (fun n => Erdos955.s n ∈ (Finset.Ico 1 (M b)).filter (· ∈ A)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    by_cases hn1 : n ≤ 1
    · apply Finset.mem_union_left
      rw [Finset.mem_insert, Finset.mem_singleton]
      omega
    · apply Finset.mem_union_right
      have hn2 : 2 ≤ n := by omega
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Ico]
      refine ⟨⟨by omega, by omega⟩, ⟨s_pos_of_two_le hn2, ?_⟩, hn.2⟩
      have hσ := h2 n (by omega)
      have hnb : (n : ℝ) ≤ b := by exact_mod_cast hn.1.le
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hlogn : Real.log (n : ℝ) ≤ Real.log b := Real.log_le_log (by linarith) hnb
      have hlogn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1'
      have hle : (ArithmeticFunction.sigma 1 n : ℝ) ≤ (b : ℝ) * (1 + Real.log b) :=
        hσ.trans (mul_le_mul hnb (by linarith) (by linarith) (by linarith))
      have hfl : ArithmeticFunction.sigma 1 n ≤ ⌊(b : ℝ) * (1 + Real.log b)⌋₊ :=
        Nat.le_floor hle
      have hs : Erdos955.s n ≤ ArithmeticFunction.sigma 1 n := Nat.sub_le _ _
      rw [hMdef]
      omega
  have hcardC : ((((Finset.range b).filter (fun n => Erdos955.s n ∈ A)).card : ℕ) : ℝ) ≤
      2 + η / 2 * b := by
    have h1' := Finset.card_le_card hsub
    have h2' := Finset.card_union_le ({0, 1} : Finset ℕ) ((Finset.Icc 1 b).filter
      (fun n => Erdos955.s n ∈ (Finset.Ico 1 (M b)).filter (· ∈ A)))
    have h3' : ({0, 1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    have h4' : ((((Finset.range b).filter (fun n => Erdos955.s n ∈ A)).card : ℕ) : ℝ) ≤
        (2 : ℝ) + (((Finset.Icc 1 b).filter
          (fun n => Erdos955.s n ∈ (Finset.Ico 1 (M b)).filter (· ∈ A))).card : ℕ) := by
      exact_mod_cast (by omega :
        ((Finset.range b).filter (fun n => Erdos955.s n ∈ A)).card ≤
          2 + ((Finset.Icc 1 b).filter
            (fun n => Erdos955.s n ∈ (Finset.Ico 1 (M b)).filter (· ∈ A))).card)
    linarith
  have hset : (((Finset.range b).filter (fun n => Erdos955.s n ∈ A) : Finset ℕ) : Set ℕ) =
      {n | Erdos955.s n ∈ A} ∩ Set.Iio b := by
    ext n
    simp [and_comm]
  have hpd : ({n | Erdos955.s n ∈ A} : Set ℕ).partialDensity Set.univ b =
      ((((Finset.range b).filter (fun n => Erdos955.s n ∈ A)).card : ℕ) : ℝ) / b := by
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, Nat.ncard_Iio, ← hset,
      Set.ncard_coe_finset]
  rw [Real.dist_eq, hpd, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hbpos]
  have h4 : 4 < b * η := (div_lt_iff₀ hη).mp hbig
  linarith

end OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1
