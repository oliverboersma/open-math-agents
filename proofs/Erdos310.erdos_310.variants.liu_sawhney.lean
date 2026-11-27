import FormalConjectures.ErdosProblems.«310»

/-!
# Disproof of `Erdos310.erdos_310.variants.liu_sawhney`

We refute `Erdos310.erdos_310.variants.liu_sawhney`: for every `C : ℝ`, there is no
upper bound `b ≤ exp (C / α)` holding uniformly for all `α ∈ [(log N)^(-1/7+ε), 1/2]`
and `A ⊆ [1, N]` with `|A| ≥ α N`.

Given any `C : ℝ`, set `C₁ = max C 1` and pick an integer `y₀ ≥ 4` large enough in terms
of `C₁`. Let `M = ∏_{p ≤ y₀} p`, `α = 1 / (3 M)`, and `L₀ = ⌊exp (C₁ / α)⌋`.
Consider the periodic set of integers `n ∈ [⌈N/2⌉, N]` not divisible by `p^2` for any
prime `p ≤ y₀` and not divisible by `p` for any prime `p ∈ (y₀, L₀]`.
By the Chinese Remainder Theorem and Mertens' third theorem, its asymptotic density is
`(1/2) * (∏_{p ≤ y₀} (1 - 1/p^2)) * (∏_{y₀ < p ≤ L₀} (1 - 1/p)) ≫ (log y₀ / C₁) * α > 2 α`
for sufficiently large `y₀`.
Taking a subset `A` of cardinality `⌈α N⌉` gives `∑_{n ∈ S} 1/n ≤ 2 α + 2/N < 3 α = 1/M`,
whereas any reduced fraction `a'/b'` with `0 < a'` and `b' ≤ L₀` arising as a reciprocal sum
from `A` must satisfy `b' ∣ M`, forcing `a'/b' ≥ 1/M = 3 α`, a contradiction.
-/

namespace Erdos310Disproof

open Real Finset

/- Part 1: Mertens' third theorem lower bound -/

noncomputable def Sm (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log p / p
noncomputable def Lm (n : ℕ) : ℝ := ∑ p ∈ (range (n + 1)).filter Nat.Prime, -Real.log (1 - 1 / (p : ℝ))
noncomputable def Qm (n : ℕ) : ℝ := ∏ p ∈ (range (n + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))
noncomputable def cM : ℝ := 2 * Real.log 2 - 1 + 1 / 12
noncomputable def Hm (n : ℕ) : ℝ :=
  Lm n - Real.log (Real.log n) + (Real.log n + cM - Sm n) / Real.log n + 1 / n

lemma filter_succ (n : ℕ) : (range (n + 2)).filter Nat.Prime =
    if (n + 1).Prime then insert (n + 1) ((range (n + 1)).filter Nat.Prime)
    else (range (n + 1)).filter Nat.Prime := by
  rw [Finset.range_add_one, Finset.filter_insert]

lemma not_mem_filter (n : ℕ) : n + 1 ∉ (range (n + 1)).filter Nat.Prime := by simp

lemma Sm_succ (n : ℕ) : Sm (n + 1) = Sm n +
    (if (n + 1).Prime then Real.log ((n : ℝ) + 1) / ((n : ℝ) + 1) else 0) := by
  unfold Sm
  rw [filter_succ]
  split_ifs
  · rw [sum_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Lm_succ (n : ℕ) : Lm (n + 1) = Lm n +
    (if (n + 1).Prime then -Real.log (1 - 1 / ((n : ℝ) + 1)) else 0) := by
  unfold Lm
  rw [filter_succ]
  split_ifs
  · rw [sum_insert (not_mem_filter n)]; push_cast; ring
  · simp

lemma Qm_pos (n : ℕ) : 0 < Qm n := by
  unfold Qm
  apply prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 1 / (p : ℝ) < 1 := by rw [div_lt_iff₀ (by linarith)]; linarith
  linarith

lemma Qm_eq_exp (n : ℕ) : Qm n = Real.exp (-Lm n) := by
  unfold Qm Lm
  rw [← sum_neg_distrib, Real.exp_sum]
  apply prod_congr rfl
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
  have : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_iff₀ (by linarith)]; linarith
    linarith
  rw [neg_neg, Real.exp_log this]

lemma log_fact_le (t : ℕ) (ht : 1 ≤ t) :
    Real.log (t.factorial) ≤ ((t : ℝ) + 1) * Real.log t - t + 1 := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih =>
    have htp : (0 : ℝ) < t := by exact_mod_cast ht
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have h1 := Real.one_sub_inv_le_log_of_pos (x := ((t : ℝ) + 1) / t) (by positivity)
    rw [Real.log_div (by positivity) (by positivity), inv_div] at h1
    have h2 : 1 - (t : ℝ) / (t + 1) = 1 / (t + 1) := by field_simp; ring
    rw [h2] at h1
    have h3 : 1 ≤ ((t : ℝ) + 1) * (Real.log (t + 1) - Real.log t) := by
      rw [div_le_iff₀ (by positivity)] at h1; linarith
    push_cast
    nlinarith

lemma sum_div_log_le (t : ℕ) :
    ∑ p ∈ (range (t + 1)).filter Nat.Prime, ((t / p : ℕ) : ℝ) * Real.log p
      ≤ Real.log (t.factorial) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (s := (range (t + 1)).filter Nat.Prime) ?_ ?_)
  · apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpt : p ≤ t := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg p)
    rw [Nat.factorization_factorial hpp (Nat.lt_succ_of_le (Nat.log_le_self p t))]
    have h1 : 1 ∈ Ico 1 (t + 1) := by
      simp only [mem_Ico]; have := hpp.two_le; omega
    have := Finset.single_le_sum (f := fun i => t / p ^ i) (fun _ _ => Nat.zero_le _) h1
    simp only [pow_one] at this
    exact_mod_cast this
  · intro p hp
    have hpp := (mem_filter.mp hp).2
    have hpt : p ≤ t := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    rw [Nat.support_factorization, Nat.mem_primeFactors]
    exact ⟨hpp, Nat.dvd_factorial hpp.pos hpt, Nat.factorial_ne_zero t⟩
  · intro p _ _
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p)

lemma theta_le (t : ℕ) :
    ∑ p ∈ (range (t + 1)).filter Nat.Prime, Real.log p ≤ 2 * Real.log 2 * t := by
  have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg t)
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range] at h
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this] at h
  linarith

lemma log_aux (t : ℝ) (ht : 64 ≤ t) : Real.log t + 1 ≤ t / 12 := by
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have h1 := Real.log_le_sub_one_of_pos (x := t / 64) (by positivity)
  rw [Real.log_div (by positivity) (by norm_num), h64] at h1
  have := Real.log_two_lt_d9
  linarith

lemma mertens1 (t : ℕ) (ht : 64 ≤ t) : Sm t ≤ Real.log t + cM := by
  have htr : (64 : ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (t : ℝ) * Sm t ≤ ∑ p ∈ (range (t + 1)).filter Nat.Prime,
      (((t / p : ℕ) : ℝ) * Real.log p + Real.log p) := by
    unfold Sm
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp2 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hlt := Nat.lt_mul_div_succ t hpp.pos
    have hle : (t : ℝ) ≤ p * (((t / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt.le
    have : (t : ℝ) / p ≤ ((t / p : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hp2]; linarith
    have hl := Real.log_natCast_nonneg p
    calc (t : ℝ) * (Real.log p / p) = ((t : ℝ) / p) * Real.log p := by ring
      _ ≤ (((t / p : ℕ) : ℝ) + 1) * Real.log p := mul_le_mul_of_nonneg_right this hl
      _ = _ := by ring
  rw [sum_add_distrib] at h1
  have h2 := sum_div_log_le t
  have h3 := theta_le t
  have h4 := log_fact_le t (by omega)
  have h5 := log_aux t htr
  have htp : (0 : ℝ) < t := by linarith
  have key : (t : ℝ) * Sm t ≤ t * (Real.log t + cM) := by
    unfold cM; nlinarith
  exact le_of_mul_le_mul_left key htp

lemma key_ineq (a b u : ℝ) (ha : 0 < a) (hab : a < b) (hu : -a ≤ u) :
    u / b - Real.log b ≤ u / a - Real.log a := by
  have hb : 0 < b := by linarith
  have h1 := Real.one_sub_inv_le_log_of_pos (x := b / a) (by positivity)
  rw [Real.log_div hb.ne' ha.ne', inv_div] at h1
  have e1 : u / b - u / a = -(u * (b - a)) / (a * b) := by field_simp; ring
  have e2 : 1 - a / b = (b - a) / b := by field_simp
  have h2 : -(u * (b - a)) / (a * b) ≤ (b - a) / b := by
    rw [div_le_div_iff₀ (by positivity) hb]
    have : 0 < b - a := by linarith
    have : -u * (b - a) ≤ a * (b - a) := mul_le_mul_of_nonneg_right (by linarith) this.le
    nlinarith
  linarith

lemma H_step (m : ℕ) (hm : 64 ≤ m) : Hm (m + 1) ≤ Hm m := by
  have hS := mertens1 m hm
  have hmr : (64 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 0 < Real.log m := Real.log_pos (by linarith)
  have hab : Real.log m < Real.log ((m : ℝ) + 1) := Real.log_lt_log (by linarith) (by linarith)
  have hb : 0 < Real.log ((m : ℝ) + 1) := by linarith
  have K := key_ineq _ _ (cM - Sm m) ha hab (by linarith)
  have hD : -Real.log (1 - 1 / ((m : ℝ) + 1)) ≤ 1 / m := by
    have e : 1 - 1 / ((m : ℝ) + 1) = ((m : ℝ) + 1)⁻¹ * m := by field_simp; ring
    have := Real.log_le_sub_one_of_pos (x := ((m : ℝ) + 1) / m) (by positivity)
    rw [e, Real.log_mul (by positivity) (by positivity), Real.log_inv]
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e2 : ((m : ℝ) + 1) / m - 1 = 1 / m := by field_simp; ring
    linarith
  have hinv : 1 / ((m : ℝ) + 1) ≤ 1 / m := one_div_le_one_div_of_le (by linarith) (by linarith)
  have ea : (Real.log m + cM - Sm m) / Real.log m = 1 + (cM - Sm m) / Real.log m := by
    field_simp; ring
  unfold Hm
  rw [Lm_succ, Sm_succ]
  push_cast
  rw [ea]
  split_ifs
  · have eb : (Real.log ((m : ℝ) + 1) + cM - (Sm m + Real.log ((m : ℝ) + 1) / ((m : ℝ) + 1)))
        / Real.log ((m : ℝ) + 1) = 1 + (cM - Sm m) / Real.log ((m : ℝ) + 1) - 1 / ((m : ℝ) + 1) := by
      field_simp; ring
    rw [eb]; linarith
  · have eb : (Real.log ((m : ℝ) + 1) + cM - (Sm m + 0))
        / Real.log ((m : ℝ) + 1) = 1 + (cM - Sm m) / Real.log ((m : ℝ) + 1) := by
      field_simp; ring
    rw [eb]; linarith

lemma H_le (n : ℕ) (hn : 64 ≤ n) : Hm n ≤ Hm 64 := by
  induction n, hn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (H_step n hn) ih

lemma mertens_third_lower (n : ℕ) (hn : 64 ≤ n) :
    Real.exp (-Hm 64) / Real.log n ≤ Qm n := by
  have hnr : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hS := mertens1 n hn
  have hH := H_le n hn
  have hdef : Hm n = Lm n - Real.log (Real.log n) + (Real.log n + cM - Sm n) / Real.log n + 1 / n := rfl
  have h1 : 0 ≤ (Real.log n + cM - Sm n) / Real.log n := div_nonneg (by linarith) hlog.le
  have h2 : (0 : ℝ) ≤ 1 / n := by positivity
  have hL : Lm n - Real.log (Real.log n) ≤ Hm 64 := by linarith
  rw [Qm_eq_exp]
  calc Real.exp (-Hm 64) / Real.log n
      = Real.exp (-Hm 64) / Real.exp (Real.log (Real.log n)) := by rw [Real.exp_log hlog]
    _ = Real.exp (-Hm 64 - Real.log (Real.log n)) := by rw [Real.exp_sub]
    _ ≤ Real.exp (-Lm n) := Real.exp_le_exp.mpr (by linarith)

/- Part 2: Elementary upper bound on `Qm y` and lower bound on `∏ (1 - 1/p^2)` -/

lemma log_le_harmonic (y : ℕ) (hy : 1 ≤ y) :
    Real.log ((y : ℝ) + 1) ≤ ∑ n ∈ Icc 1 y, (1 / (n : ℝ)) := by
  induction y, hy using Nat.le_induction with
  | base =>
    simp only [Nat.cast_one, one_add_one_eq_two, Icc_self, sum_singleton, div_one]
    have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
    linarith
  | succ y hy ih =>
    have hy1 : (0 : ℝ) < (y : ℝ) + 1 := by positivity
    have hstep := Real.log_le_sub_one_of_pos (x := ((y : ℝ) + 2) / ((y : ℝ) + 1)) (by positivity)
    rw [Real.log_div (by positivity) hy1.ne'] at hstep
    have heq : ((y : ℝ) + 2) / ((y : ℝ) + 1) - 1 = 1 / ((y : ℝ) + 1) := by field_simp; ring
    rw [heq] at hstep
    have hIcc : Icc 1 (y + 1) = insert (y + 1) (Icc 1 y) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, sum_insert (by simp)]
    push_cast
    have h2 : (y : ℝ) + 1 + 1 = (y : ℝ) + 2 := by ring
    rw [h2]
    linarith

lemma harmonic_le_inv_Qm (y : ℕ) :
    ∑ n ∈ Icc 1 y, (1 / (n : ℝ)) ≤ (Qm y)⁻¹ := by
  set P := (range (y + 1)).filter Nat.Prime
  have hgeom : ∀ p ∈ P, ∑ j ∈ range (y + 1), (1 / (p : ℝ)) ^ j ≤ (1 - 1 / (p : ℝ))⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    have hr1 : 1 / (p : ℝ) < 1 := by rw [div_lt_iff₀ (by linarith)]; linarith
    rw [geom_sum_eq (ne_of_lt hr1)]
    have hden : 0 < 1 - 1 / (p : ℝ) := by linarith
    have hpow : 0 ≤ (1 / (p : ℝ)) ^ (y + 1) := pow_nonneg hr0 _
    have hneg : ((1 / (p : ℝ)) ^ (y + 1) - 1) / (1 / (p : ℝ) - 1) =
        (1 - (1 / (p : ℝ)) ^ (y + 1)) / (1 - 1 / (p : ℝ)) := by
      rw [← neg_div_neg_eq]; congr 1 <;> ring
    rw [hneg, inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  have hprod_le : ∏ p ∈ P, ∑ j ∈ range (y + 1), (1 / (p : ℝ)) ^ j ≤ (Qm y)⁻¹ := by
    unfold Qm
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_le_prod (fun p _ => Finset.sum_nonneg (fun j _ => by positivity)) hgeom
  refine le_trans ?_ hprod_le
  rw [Finset.prod_sum]
  let φ : ℕ → (p : ℕ) → p ∈ P → ℕ := fun n p _ => n.factorization p
  have hmem : ∀ n ∈ Icc 1 y, φ n ∈ P.pi (fun _ => range (y + 1)) := by
    intro n hn
    rw [Finset.mem_pi]
    intro p hp
    rw [Finset.mem_range]
    dsimp [φ]
    have hpp := (mem_filter.mp hp).2
    have hnle : n ≤ y := (mem_Icc.mp hn).2
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hpow : p ^ n.factorization p ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.ordProj_dvd n p)
    have h2 : n.factorization p < 2 ^ n.factorization p := Nat.lt_two_pow_self
    have h2p : 2 ^ n.factorization p ≤ p ^ n.factorization p := Nat.pow_le_pow_left hpp.two_le _
    omega
  have hfac_eq : ∀ n ∈ Icc 1 y, ∏ p ∈ P.attach, p.1 ^ φ n p.1 p.2 = n := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
    have hnle : n ≤ y := (mem_Icc.mp hn).2
    have hsub : n.primeFactors ⊆ P := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      rw [mem_filter, mem_range]
      exact ⟨Nat.lt_succ_of_le ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp.2.1).trans hnle), hp.1⟩
    rw [Finset.prod_attach P (fun p => p ^ n.factorization p)]
    rw [← Finset.prod_subset hsub]
    · exact Nat.prod_factorization_pow_eq_self hn0
    · intro p _ hpnot
      have : n.factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        by_contra h
        push Not at h
        exact hpnot (Nat.mem_primeFactors.mpr ⟨h.1, h.2.1, h.2.2⟩)
      simp [this]
  have hinj : Set.InjOn φ (Icc 1 y : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    rw [← hfac_eq n₁ hn₁, ← hfac_eq n₂ hn₂]
    apply Finset.prod_congr rfl
    intro p _
    have := congrFun (congrFun heq p.1) p.2
    simp only [this]
  calc ∑ n ∈ Icc 1 y, (1 / (n : ℝ))
      = ∑ n ∈ Icc 1 y, ∏ p ∈ P.attach, (1 / (p.1 : ℝ)) ^ φ n p.1 p.2 := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnR : (∏ p ∈ P.attach, (p.1 : ℝ) ^ φ n p.1 p.2) = (n : ℝ) := by
          exact_mod_cast hfac_eq n hn
        simp only [one_div, inv_pow, Finset.prod_inv_distrib, hnR]
    _ = ∑ f ∈ (Icc 1 y).image φ, ∏ p ∈ P.attach, (1 / (p.1 : ℝ)) ^ f p.1 p.2 := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ f ∈ P.pi (fun _ => range (y + 1)), ∏ p ∈ P.attach, (1 / (p.1 : ℝ)) ^ f p.1 p.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro f hf
          rcases Finset.mem_image.mp hf with ⟨n, hn, rfl⟩
          exact hmem n hn
        · intro f _ _
          exact Finset.prod_nonneg (fun p _ => by positivity)

lemma mertens_third_upper (y : ℕ) (hy : 2 ≤ y) : Qm y ≤ 1 / Real.log y := by
  have hlog_pos : 0 < Real.log y := Real.log_pos (by exact_mod_cast hy)
  have hlog : Real.log y ≤ (Qm y)⁻¹ := by
    calc Real.log y ≤ Real.log ((y : ℝ) + 1) :=
          Real.log_le_log (by positivity) (by linarith)
      _ ≤ ∑ n ∈ Icc 1 y, (1 / (n : ℝ)) := log_le_harmonic y (by omega)
      _ ≤ (Qm y)⁻¹ := harmonic_le_inv_Qm y
  have hQpos := Qm_pos y
  rw [le_div_iff₀ hlog_pos]
  have := mul_le_mul_of_nonneg_left hlog hQpos.le
  rw [mul_inv_cancel₀ hQpos.ne'] at this
  linarith

lemma prod_one_sub_inv_sq_Icc (y : ℕ) (hy : 2 ≤ y) :
    ∏ n ∈ Icc 2 y, (1 - 1 / (n : ℝ) ^ 2) = ((y : ℝ) + 1) / (2 * (y : ℝ)) := by
  induction y, hy using Nat.le_induction with
  | base =>
    simp only [Icc_self, prod_singleton, Nat.cast_ofNat]
    norm_num
  | succ y hy ih =>
    have hIcc : Icc 2 (y + 1) = insert (y + 1) (Icc 2 y) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, prod_insert (by simp), ih]
    have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    have hy1 : (0 : ℝ) < (y : ℝ) + 1 := by positivity
    push_cast
    field_simp
    ring

lemma prod_one_sub_inv_sq_primes_ge (y : ℕ) (hy : 2 ≤ y) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ (range (y + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ) ^ 2) := by
  set P := (range (y + 1)).filter Nat.Prime
  have hsub : P ⊆ Icc 2 y := by
    intro p hp
    rw [mem_filter, mem_range] at hp
    rw [mem_Icc]
    exact ⟨hp.2.two_le, Nat.lt_succ_iff.mp hp.1⟩
  have hterm : ∀ n ∈ Icc 2 y, 0 ≤ 1 - 1 / (n : ℝ) ^ 2 ∧ 1 - 1 / (n : ℝ) ^ 2 ≤ 1 := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hsq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h1 : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
    have h2 : 1 / (n : ℝ) ^ 2 ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
    exact ⟨by linarith, by linarith⟩
  have hsplit : ∏ n ∈ Icc 2 y, (1 - 1 / (n : ℝ) ^ 2) =
      (∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2)) * (∏ n ∈ Icc 2 y \ P, (1 - 1 / (n : ℝ) ^ 2)) := by
    rw [← Finset.prod_union disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
  have hrest_le : ∏ n ∈ Icc 2 y \ P, (1 - 1 / (n : ℝ) ^ 2) ≤ 1 :=
    Finset.prod_le_one (fun n hn => (hterm n (mem_sdiff.mp hn).1).1)
      (fun n hn => (hterm n (mem_sdiff.mp hn).1).2)
  have hP_nonneg : 0 ≤ ∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2) :=
    Finset.prod_nonneg (fun p hp => (hterm p (hsub hp)).1)
  have hhalf : (1 / 2 : ℝ) ≤ ((y : ℝ) + 1) / (2 * (y : ℝ)) := by
    have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  calc (1 / 2 : ℝ) ≤ ((y : ℝ) + 1) / (2 * (y : ℝ)) := hhalf
    _ = ∏ n ∈ Icc 2 y, (1 - 1 / (n : ℝ) ^ 2) := (prod_one_sub_inv_sq_Icc y hy).symm
    _ = (∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2)) * (∏ n ∈ Icc 2 y \ P, (1 - 1 / (n : ℝ) ^ 2)) := hsplit
    _ ≤ (∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left hrest_le hP_nonneg
    _ = ∏ p ∈ P, (1 - 1 / (p : ℝ) ^ 2) := mul_one _

/- Part 3: Periodic CRT density and interval counting -/

lemma card_filter_not_dvd_prod {S : Finset ℕ} {m : ℕ → ℕ}
    (hm_pos : ∀ p ∈ S, 0 < m p)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime (m p) (m q)) :
    ((range (∏ p ∈ S, m p)).filter (fun n => ∀ p ∈ S, ¬ m p ∣ n)).card =
      ∏ p ∈ S, (m p - 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert q S hq ih =>
    have hq_pos : 0 < m q := hm_pos q (mem_insert_self q S)
    have hS_pos : ∀ p ∈ S, 0 < m p := fun p hp => hm_pos p (mem_insert_of_mem hp)
    have hS_cop : ∀ p ∈ S, ∀ r ∈ S, p ≠ r → Nat.Coprime (m p) (m r) :=
      fun p hp r hr hne => hcop p (mem_insert_of_mem hp) r (mem_insert_of_mem hr) hne
    have hP_pos : 0 < ∏ p ∈ S, m p := Finset.prod_pos hS_pos
    have hqP_cop : Nat.Coprime (m q) (∏ p ∈ S, m p) :=
      Nat.Coprime.prod_right fun p hp =>
        hcop q (mem_insert_self q S) p (mem_insert_of_mem hp) (fun h => hq (h ▸ hp))
    have : NeZero (m q) := ⟨hq_pos.ne'⟩
    have : NeZero (∏ p ∈ S, m p) := ⟨hP_pos.ne'⟩
    have : NeZero (m q * ∏ p ∈ S, m p) := ⟨(Nat.mul_pos hq_pos hP_pos).ne'⟩
    rw [Finset.prod_insert hq, Finset.prod_insert hq, ← ih hS_pos hS_cop]
    set P := ∏ p ∈ S, m p
    let e : ZMod (m q * P) ≃+* ZMod (m q) × ZMod P := ZMod.chineseRemainder hqP_cop
    have hcard_a : ((range (m q)).filter (fun a => ¬ m q ∣ a)).card = m q - 1 := by
      have hfilt : (range (m q)).filter (fun a => ¬ m q ∣ a) = (range (m q)).erase 0 := by
        ext a
        simp only [mem_filter, mem_range, mem_erase]
        constructor
        · rintro ⟨ha, hndvd⟩
          exact ⟨fun h0 => hndvd (h0 ▸ dvd_zero _), ha⟩
        · rintro ⟨ha0, ha⟩
          exact ⟨ha, fun hd => ha0 (Nat.eq_zero_of_dvd_of_lt hd ha)⟩
      rw [hfilt, Finset.card_erase_of_mem (mem_range.mpr hq_pos), Finset.card_range]
    rw [← hcard_a, ← Finset.card_product]
    apply Finset.card_bij
      (fun (n : ℕ) _ => ((e (n : ZMod (m q * P))).1.val, (e (n : ZMod (m q * P))).2.val))
    · intro n hn
      rw [mem_filter, mem_range] at hn
      rw [mem_product, mem_filter, mem_filter, mem_range, mem_range]
      have h1 : (e (n : ZMod (m q * P))).1 = (n : ZMod (m q)) := by
        simp [e, ZMod.chineseRemainder]
      have h2 : (e (n : ZMod (m q * P))).2 = (n : ZMod P) := by
        simp [e, ZMod.chineseRemainder]
      refine ⟨⟨ZMod.val_lt _, ?_⟩, ⟨ZMod.val_lt _, ?_⟩⟩
      · rw [h1, ZMod.val_natCast]
        intro hd
        have : m q ∣ n := (Nat.dvd_mod_iff (dvd_refl (m q))).mp hd
        exact hn.2 q (mem_insert_self q S) this
      · rw [h2, ZMod.val_natCast]
        intro p hp hd
        have hpP : m p ∣ P := Finset.dvd_prod_of_mem m hp
        have : m p ∣ n := (Nat.dvd_mod_iff hpP).mp hd
        exact hn.2 p (mem_insert_of_mem hp) this
    · intro n₁ hn₁ n₂ hn₂ heq
      rw [mem_filter, mem_range] at hn₁ hn₂
      have he1 : (e (n₁ : ZMod (m q * P))).1 = (e (n₂ : ZMod (m q * P))).1 :=
        ZMod.val_injective _ (Prod.mk.inj heq).1
      have he2 : (e (n₁ : ZMod (m q * P))).2 = (e (n₂ : ZMod (m q * P))).2 :=
        ZMod.val_injective _ (Prod.mk.inj heq).2
      have hzeq : (n₁ : ZMod (m q * P)) = (n₂ : ZMod (m q * P)) :=
        e.injective (Prod.ext he1 he2)
      have hv := congrArg ZMod.val hzeq
      rwa [ZMod.val_natCast_of_lt hn₁.1, ZMod.val_natCast_of_lt hn₂.1] at hv
    · intro ⟨a, b⟩ hab
      rw [mem_product, mem_filter, mem_filter, mem_range, mem_range] at hab
      let x : ZMod (m q * P) := e.symm ((a : ZMod (m q)), (b : ZMod P))
      refine ⟨x.val, ?_, ?_⟩
      · rw [mem_filter, mem_range]
        refine ⟨ZMod.val_lt x, ?_⟩
        intro p hp hd
        have hex : e (x.val : ZMod (m q * P)) = ((a : ZMod (m q)), (b : ZMod P)) := by
          rw [ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]
        have hx1 : (x.val : ZMod (m q)) = (a : ZMod (m q)) := by
          have := congrArg Prod.fst hex
          simpa [e, ZMod.chineseRemainder] using this
        have hx2 : (x.val : ZMod P) = (b : ZMod P) := by
          have := congrArg Prod.snd hex
          simpa [e, ZMod.chineseRemainder] using this
        rcases mem_insert.mp hp with rfl | hpS
        · have hxa : x.val % m p = a := by
            have := congrArg ZMod.val hx1
            rwa [ZMod.val_natCast, ZMod.val_natCast_of_lt hab.1.1] at this
          have hda : m p ∣ a := hxa ▸ (Nat.dvd_mod_iff (dvd_refl _)).mpr hd
          exact hab.1.2 hda
        · have hxb : x.val % P = b := by
            have := congrArg ZMod.val hx2
            rwa [ZMod.val_natCast, ZMod.val_natCast_of_lt hab.2.1] at this
          have hpP : m p ∣ P := Finset.dvd_prod_of_mem m hpS
          have hdb : m p ∣ b := hxb ▸ (Nat.dvd_mod_iff hpP).mpr hd
          exact hab.2.2 p hpS hdb
      · have hex : e (x.val : ZMod (m q * P)) = ((a : ZMod (m q)), (b : ZMod P)) := by
          rw [ZMod.natCast_zmod_val, RingEquiv.apply_symm_apply]
        rw [hex, ZMod.val_natCast_of_lt hab.1.1, ZMod.val_natCast_of_lt hab.2.1]

lemma card_filter_Ico_periodic (P c : ℕ) (hP : 0 < P) (f : ℕ → Prop) [DecidablePred f]
    (hper : ∀ n, f n ↔ f (n % P)) :
    ((Ico c (c + P)).filter f).card = ((range P).filter f).card := by
  apply Finset.card_bij (fun n _ => n % P)
  · intro n hn
    rw [mem_filter] at hn ⊢
    exact ⟨mem_range.mpr (Nat.mod_lt n hP), (hper n).mp hn.2⟩
  · intro n₁ hn₁ n₂ hn₂ heq
    rw [mem_filter, mem_Ico] at hn₁ hn₂
    have h1 := Nat.div_add_mod n₁ P
    have h2 := Nat.div_add_mod n₂ P
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hqlt : n₁ / P < n₂ / P := by
        by_contra hge
        have : P * (n₂ / P) ≤ P * (n₁ / P) := Nat.mul_le_mul_left P (by omega)
        omega
      have hmul : P * (n₁ / P + 1) ≤ P * (n₂ / P) := Nat.mul_le_mul_left P hqlt
      rw [Nat.mul_add, mul_one] at hmul
      omega
    · have hqlt : n₂ / P < n₁ / P := by
        by_contra hge
        have : P * (n₁ / P) ≤ P * (n₂ / P) := Nat.mul_le_mul_left P (by omega)
        omega
      have hmul : P * (n₂ / P + 1) ≤ P * (n₁ / P) := Nat.mul_le_mul_left P hqlt
      rw [Nat.mul_add, mul_one] at hmul
      omega
  · intro r hr
    rw [mem_filter, mem_range] at hr
    let k := if c % P ≤ r then r - c % P else r + P - c % P
    have hk : k < P := by dsimp [k]; split_ifs <;> omega
    have hmod : (c + k) % P = r := by
      have hc := Nat.div_add_mod c P
      have hlt := Nat.mod_lt c hP
      dsimp [k]
      split_ifs with h
      · have hsum : c + (r - c % P) = P * (c / P) + r := by omega
        rw [hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt hr.1]
      · have hmul : P * (c / P + 1) = P * (c / P) + P := by rw [Nat.mul_add, mul_one]
        have hsum : c + (r + P - c % P) = P * (c / P + 1) + r := by omega
        rw [hsum, Nat.mul_add_mod, Nat.mod_eq_of_lt hr.1]
    refine ⟨c + k, ?_, hmod⟩
    rw [mem_filter, mem_Ico]
    exact ⟨⟨Nat.le_add_right _ _, by omega⟩, (hper (c + k)).mpr (hmod ▸ hr.2)⟩

lemma card_filter_Icc_periodic_ge (P a b : ℕ) (hP : 0 < P) (f : ℕ → Prop) [DecidablePred f]
    (hper : ∀ n, f n ↔ f (n % P)) :
    ((b + 1 - a) / P) * ((range P).filter f).card ≤ ((Icc a b).filter f).card := by
  set q := (b + 1 - a) / P
  have hsub : (range q).biUnion (fun j => (Ico (a + j * P) (a + (j + 1) * P)).filter f) ⊆
      (Icc a b).filter f := by
    intro n hn
    rw [mem_biUnion] at hn
    rcases hn with ⟨j, hj, hnj⟩
    rw [mem_range] at hj
    rw [mem_filter, mem_Ico] at hnj
    rw [mem_filter, mem_Icc]
    have hqP : (j + 1) * P ≤ q * P := Nat.mul_le_mul_right P hj
    have hqle : q * P ≤ b + 1 - a := Nat.div_mul_le_self (b + 1 - a) P
    exact ⟨⟨by omega, by omega⟩, hnj.2⟩
  have hdisj : Set.PairwiseDisjoint (range q : Set ℕ)
      (fun j => (Ico (a + j * P) (a + (j + 1) * P)).filter f) := by
    intro i _ j _ hij
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hni hnj
    rw [mem_filter, mem_Ico] at hni hnj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have : (i + 1) * P ≤ j * P := Nat.mul_le_mul_right P hlt
      omega
    · have : (j + 1) * P ≤ i * P := Nat.mul_le_mul_right P hgt
      omega
  calc q * ((range P).filter f).card
      = ∑ _j ∈ range q, ((range P).filter f).card := by simp
    _ = ∑ j ∈ range q, ((Ico (a + j * P) (a + (j + 1) * P)).filter f).card := by
        apply Finset.sum_congr rfl
        intro j _
        rw [show a + (j + 1) * P = (a + j * P) + P by ring]
        exact (card_filter_Ico_periodic P (a + j * P) hP f hper).symm
    _ = ((range q).biUnion (fun j => (Ico (a + j * P) (a + (j + 1) * P)).filter f)).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ ((Icc a b).filter f).card := Finset.card_le_card hsub

/- Part 4: Arithmetic obstruction for reduced denominators -/

lemma pow_dvd_lcm_exists {S : Finset ℕ} {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hpos : ∀ n ∈ S, n ≠ 0) (hdvd : p ^ k ∣ S.lcm id) :
    ∃ n ∈ S, p ^ k ∣ n := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.lcm_empty, Nat.dvd_one] at hdvd
    have hge : 2 ≤ p ^ k := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    omega
  | @insert x S hx ih =>
    rw [Finset.lcm_insert] at hdvd
    have hx0 : x ≠ 0 := hpos x (mem_insert_self x S)
    have hS0 : ∀ n ∈ S, n ≠ 0 := fun n hn => hpos n (mem_insert_of_mem hn)
    have hlcm0 : S.lcm id ≠ 0 := by
      intro h0
      rw [Finset.lcm_eq_zero_iff] at h0
      rcases h0 with ⟨n, hn, hn0⟩
      exact hS0 n hn hn0
    have hfac : k ≤ (Nat.lcm x (S.lcm id)).factorization p :=
      (hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero hx0 hlcm0)).mp hdvd
    rw [Nat.factorization_lcm hx0 hlcm0, Finsupp.sup_apply] at hfac
    rcases le_sup_iff.mp hfac with h1 | h2
    · exact ⟨x, mem_insert_self x S, (hp.pow_dvd_iff_le_factorization hx0).mpr h1⟩
    · rcases ih hS0 ((hp.pow_dvd_iff_le_factorization hlcm0).mpr h2) with ⟨n, hn, hdn⟩
      exact ⟨n, mem_insert_of_mem hn, hdn⟩

lemma reduced_denom_dvd_lcm {S : Finset ℕ} {a' b' : ℕ}
    (hpos : ∀ n ∈ S, n ≠ 0) (hb' : 0 < b') (hcop : Nat.Coprime a' b')
    (hsum : ∑ n ∈ S, (1 / (n : ℚ)) = (a' : ℚ) / (b' : ℚ)) :
    b' ∣ S.lcm id := by
  set D := S.lcm id
  have hD_mul : (D : ℚ) * ∑ n ∈ S, (1 / (n : ℚ)) = ((∑ n ∈ S, D / n : ℕ) : ℚ) := by
    rw [Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hpos n hn)
    have hnd : n ∣ D := Finset.dvd_lcm hn
    rw [one_div, ← div_eq_mul_inv, Nat.cast_div hnd hn0]
  have heqQ : ((D * a' : ℕ) : ℚ) = ((b' * ∑ n ∈ S, D / n : ℕ) : ℚ) := by
    have hbQ : (b' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb'.ne'
    rw [Nat.cast_mul, Nat.cast_mul, ← hD_mul, hsum]
    field_simp
  have heqN : D * a' = b' * ∑ n ∈ S, D / n := Nat.cast_injective heqQ
  have hdvd : b' ∣ D * a' := ⟨∑ n ∈ S, D / n, heqN⟩
  exact hcop.symm.dvd_of_dvd_mul_right hdvd

lemma primorial_ge (y : ℕ) (hy : 4 ≤ y) :
    y ≤ ∏ p ∈ (range (y + 1)).filter Nat.Prime, p := by
  have hm : y / 2 ≠ 0 := by omega
  rcases Nat.exists_prime_lt_and_le_two_mul (y / 2) hm with ⟨q, hq_prime, hq_gt, hq_le⟩
  have hq_le_y : q ≤ y := by omega
  have h2_mem : 2 ∈ (range (y + 1)).filter Nat.Prime := by
    rw [mem_filter, mem_range]; exact ⟨by omega, Nat.prime_two⟩
  have hq_mem : q ∈ (range (y + 1)).filter Nat.Prime := by
    rw [mem_filter, mem_range]; exact ⟨Nat.lt_succ_of_le hq_le_y, hq_prime⟩
  have h2q : 2 ≠ q := by omega
  have hsub : ({2, q} : Finset ℕ) ⊆ (range (y + 1)).filter Nat.Prime := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hprod_pos : ∀ p ∈ (range (y + 1)).filter Nat.Prime, 1 ≤ p :=
    fun p hp => (mem_filter.mp hp).2.one_le
  have hle : ∏ p ∈ ({2, q} : Finset ℕ), p ≤ ∏ p ∈ (range (y + 1)).filter Nat.Prime, p :=
    Finset.prod_le_prod_of_subset_of_one_le' hsub (fun p hp _ => hprod_pos p hp)
  rw [Finset.prod_pair h2q] at hle
  omega

/- Part 5: Decoupled contradiction lemma (opaque parameters for fast elaboration) -/

lemma no_small_denom_from_good {y₀ L₀ N : ℕ} {α C : ℝ}
    (hy₀_le_L₀ : y₀ ≤ L₀) (hN_ge4 : 4 ≤ N) (hα_pos : 0 < α)
    (hα_eq : α = 1 / (3 * ((∏ p ∈ (range (y₀ + 1)).filter Nat.Prime, p : ℕ) : ℝ)))
    (hM_pos : 0 < ∏ p ∈ (range (y₀ + 1)).filter Nat.Prime, p)
    (hL₀_ge_exp : Real.exp (C / α) < (L₀ : ℝ) + 1)
    (hN_large : 2 < α * (N : ℝ))
    {A : Finset ℕ}
    (hA_sub : A ⊆ (Icc ((N + 1) / 2) N).filter
      (fun n => ∀ p ∈ (range (L₀ + 1)).filter Nat.Prime,
        ¬ (if p ≤ y₀ then p ^ 2 else p) ∣ n))
    (hA_card : A.card = ⌈α * (N : ℝ)⌉₊)
    {S : Finset ℕ} (hSA : S ⊆ A) {a b : ℕ}
    (ha_pos : 0 < a) (hab : a ≤ b) (hb_exp : (b : ℝ) ≤ Real.exp (C / α))
    (hS_sum : ∑ n ∈ S, (1 / (n : ℚ)) = (a : ℚ) / (b : ℚ)) : False := by
  set P₁ : Finset ℕ := (range (y₀ + 1)).filter Nat.Prime
  set Pall : Finset ℕ := (range (L₀ + 1)).filter Nat.Prime
  set M : ℕ := ∏ p ∈ P₁, p
  set m : ℕ → ℕ := fun p => if p ≤ y₀ then p ^ 2 else p
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb_pos : 0 < b := lt_of_lt_of_le ha_pos hab
  have hb_le_L₀ : b ≤ L₀ := by
    have hlt : (b : ℝ) < (L₀ : ℝ) + 1 := lt_of_le_of_lt hb_exp hL₀_ge_exp
    have hnat : b < L₀ + 1 := by exact_mod_cast hlt
    omega
  let g := Nat.gcd a b
  let a' := a / g
  let b' := b / g
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left b ha_pos
  have hga : g ∣ a := Nat.gcd_dvd_left a b
  have hgb : g ∣ b := Nat.gcd_dvd_right a b
  have ha'_pos : 0 < a' := Nat.div_pos (Nat.le_of_dvd ha_pos hga) hg_pos
  have hb'_pos : 0 < b' := Nat.div_pos (Nat.le_of_dvd hb_pos hgb) hg_pos
  have hb'_le_L₀ : b' ≤ L₀ := le_trans (Nat.div_le_self b g) hb_le_L₀
  have hcop' : Nat.Coprime a' b' := Nat.coprime_div_gcd_div_gcd hg_pos
  have hS_sum' : ∑ n ∈ S, (1 / (n : ℚ)) = (a' : ℚ) / (b' : ℚ) := by
    rw [hS_sum]
    have hgQ : (g : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hg_pos.ne'
    have ha_eq : (a : ℚ) = (a' : ℚ) * (g : ℚ) := by exact_mod_cast (Nat.div_mul_cancel hga).symm
    have hb_eq : (b : ℚ) = (b' : ℚ) * (g : ℚ) := by exact_mod_cast (Nat.div_mul_cancel hgb).symm
    rw [ha_eq, hb_eq, mul_div_mul_right _ _ hgQ]
  have hS_pos : ∀ n ∈ S, n ≠ 0 := by
    intro n hn
    have h1 := mem_Icc.mp (mem_filter.mp (hA_sub (hSA hn))).1
    omega
  have hb'_dvd_lcm : b' ∣ S.lcm id := reduced_denom_dvd_lcm hS_pos hb'_pos hcop' hS_sum'
  have hb'_p_in : b'.primeFactors ⊆ P₁ := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    have hp_le_L₀ : p ≤ L₀ := le_trans (Nat.le_of_dvd hb'_pos hp.2.1) hb'_le_L₀
    have hp_Pall : p ∈ Pall := mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hp_le_L₀), hp.1⟩
    by_contra hpnot
    have hp_gt : y₀ < p := by
      by_contra hle
      exact hpnot (mem_filter.mpr ⟨mem_range.mpr (by omega), hp.1⟩)
    have hpk : p ^ 1 ∣ S.lcm id := by rw [pow_one]; exact dvd_trans hp.2.1 hb'_dvd_lcm
    rcases pow_dvd_lcm_exists hp.1 (le_refl 1) hS_pos hpk with ⟨n, hnS, hpn⟩
    rw [pow_one] at hpn
    have hngood := (mem_filter.mp (hA_sub (hSA hnS))).2 p hp_Pall
    rw [if_neg (by omega)] at hngood
    exact hngood hpn
  have hb'_sqfree : ∀ p ∈ b'.primeFactors, b'.factorization p = 1 := by
    intro p hp
    have hpp := (Nat.mem_primeFactors.mp hp).1
    have hp_P₁ : p ∈ P₁ := hb'_p_in hp
    have hp_le_y₀ : p ≤ y₀ := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp_P₁).1)
    have hp_Pall : p ∈ Pall :=
      mem_filter.mpr ⟨mem_range.mpr (by omega), hpp⟩
    have hge1 : 1 ≤ b'.factorization p :=
      (hpp.pow_dvd_iff_le_factorization hb'_pos.ne').mp
        (by rw [pow_one]; exact (Nat.mem_primeFactors.mp hp).2.1)
    have hlt2 : b'.factorization p < 2 := by
      by_contra hge2
      push Not at hge2
      have hp2 : p ^ 2 ∣ b' := (hpp.pow_dvd_iff_le_factorization hb'_pos.ne').mpr hge2
      rcases pow_dvd_lcm_exists hpp (by norm_num) hS_pos (dvd_trans hp2 hb'_dvd_lcm) with
        ⟨n, hnS, hpn⟩
      have hngood := (mem_filter.mp (hA_sub (hSA hnS))).2 p hp_Pall
      rw [if_pos hp_le_y₀] at hngood
      exact hngood hpn
    omega
  have hb'_dvd_M : b' ∣ M := by
    have hb'_eq : b' = ∏ p ∈ b'.primeFactors, p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hb'_pos.ne']
      rw [Finsupp.prod]
      apply Finset.prod_congr rfl
      intro p hp
      rw [Nat.support_factorization] at hp
      rw [hb'_sqfree p hp, pow_one]
    rw [hb'_eq]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hb'_p_in
  have hb'_le_M : b' ≤ M := Nat.le_of_dvd hM_pos hb'_dvd_M
  have hsum_R : ∑ n ∈ S, (1 / (n : ℝ)) = (a' : ℝ) / (b' : ℝ) := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) hS_sum'
    simpa [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hcast
  have hsum_ge : 3 * α ≤ ∑ n ∈ S, (1 / (n : ℝ)) := by
    rw [hsum_R]
    have ha'1 : (1 : ℝ) ≤ a' := by exact_mod_cast ha'_pos
    have hb'M : (b' : ℝ) ≤ M := by exact_mod_cast hb'_le_M
    have hb'R : (0 : ℝ) < b' := by exact_mod_cast hb'_pos
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM_pos
    calc 3 * α = 1 / (M : ℝ) := by rw [hα_eq]; field_simp
      _ ≤ 1 / (b' : ℝ) := one_div_le_one_div_of_le hb'R hb'M
      _ ≤ (a' : ℝ) / (b' : ℝ) := div_le_div_of_nonneg_right ha'1 hb'R.le
  have hsum_lt : ∑ n ∈ S, (1 / (n : ℝ)) < 3 * α := by
    have hterm : ∀ n ∈ S, (1 / (n : ℝ)) ≤ 2 / (N : ℝ) := by
      intro n hn
      have h1 := (mem_Icc.mp (mem_filter.mp (hA_sub (hSA hn))).1).1
      have hnat : N ≤ 2 * n := by omega
      have hreal : (N : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hnat
      have hn_pos : (0 : ℝ) < n := by linarith
      rw [div_le_div_iff₀ hn_pos hN_pos]
      linarith
    have hS_le : ∑ n ∈ S, (1 / (n : ℝ)) ≤ (S.card : ℝ) * (2 / (N : ℝ)) := by
      calc ∑ n ∈ S, (1 / (n : ℝ)) ≤ ∑ _n ∈ S, (2 / (N : ℝ)) := Finset.sum_le_sum hterm
        _ = (S.card : ℝ) * (2 / (N : ℝ)) := by simp
    have hSA_card : (S.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hSA
    have hA_lt : (A.card : ℝ) < α * (N : ℝ) + 1 := by
      rw [hA_card]
      exact Nat.ceil_lt_add_one (by positivity)
    have h2_lt : 2 / (N : ℝ) < α := by
      rw [div_lt_iff₀ hN_pos]; linarith
    calc ∑ n ∈ S, (1 / (n : ℝ))
        ≤ (S.card : ℝ) * (2 / (N : ℝ)) := hS_le
      _ ≤ (A.card : ℝ) * (2 / (N : ℝ)) := mul_le_mul_of_nonneg_right hSA_card (by positivity)
      _ < (α * (N : ℝ) + 1) * (2 / (N : ℝ)) :=
          mul_lt_mul_of_pos_right hA_lt (by positivity)
      _ = 2 * α + 2 / (N : ℝ) := by field_simp
      _ < 3 * α := by linarith
  linarith

lemma periodic_subset_exists {P R N : ℕ} {α : ℝ} {f : ℕ → Prop} [DecidablePred f]
    (hP_pos : 0 < P) (hN_ge4 : 4 ≤ N) (hα_pos : 0 < α)
    (hper : ∀ n, f n ↔ f (n % P))
    (hR_eq : R = ((range P).filter f).card)
    (hδ_gt : 4 * α < (R : ℝ) / (P : ℝ))
    (hP_lt : (P : ℝ) + 2 < α * (N : ℝ)) :
    ∃ A ⊆ (Icc ((N + 1) / 2) N).filter f, A.card = ⌈α * (N : ℝ)⌉₊ := by
  set low := (N + 1) / 2
  set Asf := (Icc low N).filter f
  have hP_posR : (0 : ℝ) < P := by exact_mod_cast hP_pos
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hper_card := card_filter_Icc_periodic_ge P low N hP_pos f hper
  rw [← hR_eq] at hper_card
  have hperR : (((N + 1 - low) / P : ℕ) : ℝ) * (R : ℝ) ≤ (Asf.card : ℝ) := by
    exact_mod_cast hper_card
  have hlen : (N : ℝ) / 2 ≤ ((N + 1 - low : ℕ) : ℝ) := by
    have hnat : N ≤ 2 * (N + 1 - low) := by dsimp [low]; omega
    have : (N : ℝ) ≤ 2 * ((N + 1 - low : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hdiv : ((N + 1 - low : ℕ) : ℝ) / (P : ℝ) - 1 ≤ (((N + 1 - low) / P : ℕ) : ℝ) := by
    have hnat : N + 1 - low < ((N + 1 - low) / P + 1) * P := by
      have := Nat.div_add_mod (N + 1 - low) P
      have := Nat.mod_lt (N + 1 - low) hP_pos
      nlinarith
    have hreal : ((N + 1 - low : ℕ) : ℝ) < ((((N + 1 - low) / P : ℕ) : ℝ) + 1) * (P : ℝ) := by
      exact_mod_cast hnat
    rw [sub_le_iff_le_add, div_le_iff₀ hP_posR]
    linarith
  have hR_le_P : (R : ℝ) ≤ (P : ℝ) := by
    have hnat : R ≤ P := by
      rw [hR_eq]
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range P)
    exact_mod_cast hnat
  have hAsfR : α * (N : ℝ) + 1 < (Asf.card : ℝ) := by
    have hstep1 : (((N + 1 - low : ℕ) : ℝ) / (P : ℝ) - 1) * (R : ℝ) ≤ (Asf.card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right hdiv (Nat.cast_nonneg R)) hperR
    have hstep2 : (N : ℝ) / 2 * ((R : ℝ) / (P : ℝ)) - (P : ℝ) ≤
        (((N + 1 - low : ℕ) : ℝ) / (P : ℝ) - 1) * (R : ℝ) := by
      have h1 : (N : ℝ) / 2 * ((R : ℝ) / (P : ℝ)) ≤
          ((N + 1 - low : ℕ) : ℝ) * ((R : ℝ) / (P : ℝ)) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
      have h2 : (((N + 1 - low : ℕ) : ℝ) / (P : ℝ) - 1) * (R : ℝ) =
          ((N + 1 - low : ℕ) : ℝ) * ((R : ℝ) / (P : ℝ)) - (R : ℝ) := by ring
      linarith
    have hstep3 : 2 * α * (N : ℝ) < (N : ℝ) / 2 * ((R : ℝ) / (P : ℝ)) := by
      have := mul_lt_mul_of_pos_left hδ_gt (show (0 : ℝ) < (N : ℝ) / 2 by positivity)
      linarith
    linarith
  have hceil_lt : (⌈α * (N : ℝ)⌉₊ : ℝ) < (Asf.card : ℝ) :=
    lt_of_lt_of_le (Nat.ceil_lt_add_one (by positivity)) hAsfR.le
  have hAsf_card : ⌈α * (N : ℝ)⌉₊ ≤ Asf.card := Nat.le_of_lt (by exact_mod_cast hceil_lt)
  exact Finset.exists_subset_card_eq hAsf_card

lemma exists_counterexample_params (C : ℝ) :
    ∃ (y₀ L₀ P R : ℕ) (α : ℝ),
      y₀ ≤ L₀ ∧ 0 < P ∧ 0 < α ∧ α ≤ 1 / 2 ∧
      α = 1 / (3 * ((∏ p ∈ (range (y₀ + 1)).filter Nat.Prime, p : ℕ) : ℝ)) ∧
      0 < ∏ p ∈ (range (y₀ + 1)).filter Nat.Prime, p ∧
      Real.exp (C / α) < (L₀ : ℝ) + 1 ∧
      (∀ n, (∀ p ∈ (range (L₀ + 1)).filter Nat.Prime, ¬ (if p ≤ y₀ then p ^ 2 else p) ∣ n) ↔
            (∀ p ∈ (range (L₀ + 1)).filter Nat.Prime, ¬ (if p ≤ y₀ then p ^ 2 else p) ∣ (n % P))) ∧
      R = ((range P).filter (fun n => ∀ p ∈ (range (L₀ + 1)).filter Nat.Prime,
            ¬ (if p ≤ y₀ then p ^ 2 else p) ∣ n)).card ∧
      4 * α < (R : ℝ) / (P : ℝ) := by
  let C₁ : ℝ := max C 1
  have hC_le : C ≤ C₁ := le_max_left C 1
  have hC₁_ge : (1 : ℝ) ≤ C₁ := le_max_right C 1
  have hC₁_pos : 0 < C₁ := by linarith
  let c₀ : ℝ := Real.exp (-Hm 64)
  have hc₀_pos : 0 < c₀ := Real.exp_pos _
  let y₀ : ℕ := max 4 (⌈Real.exp (9 * C₁ / c₀)⌉₊ + 1)
  have hy₀_ge4 : 4 ≤ y₀ := le_max_left _ _
  have hy₀_ge2 : 2 ≤ y₀ := by omega
  have hy₀_gt_exp : Real.exp (9 * C₁ / c₀) < (y₀ : ℝ) := by
    have h1nat : ⌈Real.exp (9 * C₁ / c₀)⌉₊ + 1 ≤ y₀ := le_max_right _ _
    have h1 : (⌈Real.exp (9 * C₁ / c₀)⌉₊ : ℝ) + 1 ≤ (y₀ : ℝ) := by exact_mod_cast h1nat
    have h2 : Real.exp (9 * C₁ / c₀) ≤ ⌈Real.exp (9 * C₁ / c₀)⌉₊ := Nat.le_ceil _
    linarith
  have hlog_y₀ : 9 * C₁ / c₀ < Real.log y₀ := by
    rw [← Real.log_exp (9 * C₁ / c₀)]
    exact Real.log_lt_log (Real.exp_pos _) hy₀_gt_exp
  let P₁ : Finset ℕ := (range (y₀ + 1)).filter Nat.Prime
  let M : ℕ := ∏ p ∈ P₁, p
  have hM_ge_y₀ : y₀ ≤ M := primorial_ge y₀ hy₀_ge4
  have hM_ge4 : 4 ≤ M := le_trans hy₀_ge4 hM_ge_y₀
  have hM_posN : 0 < M := by omega
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM_posN
  let α : ℝ := 1 / (3 * (M : ℝ))
  have hα_pos : 0 < α := by positivity
  have hα_le_half : α ≤ 1 / 2 := by
    dsimp [α]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (4 : ℝ) ≤ M := by exact_mod_cast hM_ge4
    linarith
  let L : ℝ := Real.exp (C₁ / α)
  let L₀ : ℕ := ⌊L⌋₊
  have hC₁_div_α : C₁ / α = 3 * C₁ * (M : ℝ) := by dsimp [α]; field_simp
  have hL_ge64 : (64 : ℝ) ≤ L := by
    dsimp [L]
    rw [hC₁_div_α]
    have h6 : (6 : ℝ) ≤ 3 * C₁ * (M : ℝ) := by
      have : (4 : ℝ) ≤ M := by exact_mod_cast hM_ge4
      nlinarith
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) he2 6
      _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ Real.exp (3 * C₁ * (M : ℝ)) := Real.exp_le_exp.mpr h6
  have hL₀_ge64 : 64 ≤ L₀ := Nat.le_floor hL_ge64
  have hL₀_pos : (0 : ℝ) < L₀ := by exact_mod_cast (by omega : 0 < L₀)
  have hL₀_le_L : (L₀ : ℝ) ≤ L := Nat.floor_le (Real.exp_pos _).le
  have hL_lt_L₀ : Real.exp (C / α) < (L₀ : ℝ) + 1 := by
    have h1 : Real.exp (C / α) ≤ L := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hC_le hα_pos.le)
    have h2 : L < (L₀ : ℝ) + 1 := Nat.lt_floor_add_one L
    linarith
  have hy₀_le_L₀ : y₀ ≤ L₀ := by
    apply Nat.le_floor
    dsimp [L]
    rw [hC₁_div_α]
    have hyM : (y₀ : ℝ) ≤ M := by exact_mod_cast hM_ge_y₀
    have h1 := Real.add_one_le_exp (3 * C₁ * (M : ℝ))
    nlinarith
  let P₂ : Finset ℕ := (Ioc y₀ L₀).filter Nat.Prime
  let Pall : Finset ℕ := (range (L₀ + 1)).filter Nat.Prime
  have hdisj12 : Disjoint P₁ P₂ := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [mem_filter, mem_range] at hp1
    rw [mem_filter, mem_Ioc] at hp2
    omega
  have hunion12 : P₁ ∪ P₂ = Pall := by
    ext p
    simp only [P₁, P₂, Pall, mem_union, mem_filter, mem_range, mem_Ioc]
    constructor
    · rintro (⟨h1, hp⟩ | ⟨⟨_, h2⟩, hp⟩) <;> exact ⟨by omega, hp⟩
    · rintro ⟨h1, hp⟩
      by_cases hle : p ≤ y₀
      · exact Or.inl ⟨by omega, hp⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hp⟩
  let m : ℕ → ℕ := fun p => if p ≤ y₀ then p ^ 2 else p
  have hm_pos : ∀ p ∈ Pall, 0 < m p := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    dsimp [m]; split_ifs
    · exact pow_pos hpp.pos 2
    · exact hpp.pos
  have hm_cop : ∀ p ∈ Pall, ∀ q ∈ Pall, p ≠ q → Nat.Coprime (m p) (m q) := by
    intro p hp q hq hpq
    have hpp := (mem_filter.mp hp).2
    have hqq := (mem_filter.mp hq).2
    have hbase : Nat.Coprime p q := (Nat.coprime_primes hpp hqq).mpr hpq
    dsimp [m]; split_ifs
    · exact (hbase.pow_left 2).pow_right 2
    · exact hbase.pow_left 2
    · exact hbase.pow_right 2
    · exact hbase
  let P : ℕ := ∏ p ∈ Pall, m p
  have hP_pos : 0 < P := Finset.prod_pos hm_pos
  have hgood_per : ∀ n, (∀ p ∈ Pall, ¬ m p ∣ n) ↔ (∀ p ∈ Pall, ¬ m p ∣ (n % P)) := by
    intro n
    constructor <;> intro hg p hp hd
    · exact hg p hp ((Nat.dvd_mod_iff (Finset.dvd_prod_of_mem m hp)).mp hd)
    · exact hg p hp ((Nat.dvd_mod_iff (Finset.dvd_prod_of_mem m hp)).mpr hd)
  let R : ℕ := ((range P).filter (fun n => ∀ p ∈ Pall, ¬ m p ∣ n)).card
  have hR_eq : R = ∏ p ∈ Pall, (m p - 1) := card_filter_not_dvd_prod hm_pos hm_cop
  have hδ_eq : (R : ℝ) / (P : ℝ) =
      (∏ p ∈ P₁, (1 - 1 / (p : ℝ) ^ 2)) * (∏ p ∈ P₂, (1 - 1 / (p : ℝ))) := by
    have hRP : (R : ℝ) / (P : ℝ) = ∏ p ∈ Pall, (1 - 1 / (m p : ℝ)) := by
      rw [hR_eq]
      dsimp [P]
      rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hm1 : 1 ≤ m p := hm_pos p hp
      have hmR : (0 : ℝ) < m p := by exact_mod_cast hm1
      rw [Nat.cast_sub hm1, Nat.cast_one]
      field_simp
    rw [hRP, ← hunion12, Finset.prod_union hdisj12]
    congr 1
    · apply Finset.prod_congr rfl
      intro p hp
      have hle : p ≤ y₀ := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
      simp [m, hle]
    · apply Finset.prod_congr rfl
      intro p hp
      have hgt : ¬ p ≤ y₀ := by have := (mem_Ioc.mp (mem_filter.mp hp).1).1; omega
      simp [m, hgt]
  have hQm_split : Qm L₀ = Qm y₀ * ∏ p ∈ P₂, (1 - 1 / (p : ℝ)) := by
    unfold Qm
    change ∏ p ∈ Pall, (1 - 1 / (p : ℝ)) =
      (∏ p ∈ P₁, (1 - 1 / (p : ℝ))) * ∏ p ∈ P₂, (1 - 1 / (p : ℝ))
    rw [← hunion12, Finset.prod_union hdisj12]
  have hP₂_ge : c₀ * Real.log y₀ / (3 * C₁ * (M : ℝ)) ≤ ∏ p ∈ P₂, (1 - 1 / (p : ℝ)) := by
    have hlow : c₀ / Real.log L₀ ≤ Qm L₀ := mertens_third_lower L₀ hL₀_ge64
    have hup : Qm y₀ ≤ 1 / Real.log y₀ := mertens_third_upper y₀ hy₀_ge2
    have hQpos : 0 < Qm y₀ := Qm_pos y₀
    have hlogL₀_pos : 0 < Real.log L₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < L₀))
    have hlogL₀_le : Real.log L₀ ≤ 3 * C₁ * (M : ℝ) := by
      calc Real.log L₀ ≤ Real.log L := Real.log_le_log hL₀_pos hL₀_le_L
        _ = C₁ / α := Real.log_exp _
        _ = 3 * C₁ * (M : ℝ) := hC₁_div_α
    have hlogy₀_pos : 0 < Real.log y₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < y₀))
    have hlow2 : c₀ / (3 * C₁ * (M : ℝ)) ≤ Qm L₀ :=
      le_trans (div_le_div_of_nonneg_left hc₀_pos.le hlogL₀_pos hlogL₀_le) hlow
    rw [hQm_split] at hlow2
    have hdiv : c₀ / (3 * C₁ * (M : ℝ)) / (1 / Real.log y₀) ≤
        Qm y₀ * (∏ p ∈ P₂, (1 - 1 / (p : ℝ))) / Qm y₀ := by
      have h1 : c₀ / (3 * C₁ * (M : ℝ)) / (1 / Real.log y₀) ≤
          c₀ / (3 * C₁ * (M : ℝ)) / Qm y₀ :=
        div_le_div_of_nonneg_left (by positivity) hQpos hup
      have h2 : c₀ / (3 * C₁ * (M : ℝ)) / Qm y₀ ≤
          Qm y₀ * (∏ p ∈ P₂, (1 - 1 / (p : ℝ))) / Qm y₀ :=
        div_le_div_of_nonneg_right hlow2 hQpos.le
      exact le_trans h1 h2
    rw [mul_div_cancel_left₀ _ hQpos.ne'] at hdiv
    have hsimp : c₀ / (3 * C₁ * (M : ℝ)) / (1 / Real.log y₀) =
        c₀ * Real.log y₀ / (3 * C₁ * (M : ℝ)) := by field_simp
    rwa [hsimp] at hdiv
  have hδ_gt : 4 * α < (R : ℝ) / (P : ℝ) := by
    rw [hδ_eq]
    have hsq := prod_one_sub_inv_sq_primes_ge y₀ hy₀_ge2
    have hprod_ge : (1 / 2 : ℝ) * (c₀ * Real.log y₀ / (3 * C₁ * (M : ℝ))) ≤
        (∏ p ∈ P₁, (1 - 1 / (p : ℝ) ^ 2)) * (∏ p ∈ P₂, (1 - 1 / (p : ℝ))) :=
      mul_le_mul hsq hP₂_ge (by positivity) (by positivity)
    refine lt_of_lt_of_le ?_ hprod_ge
    dsimp [α]
    have hnum : 9 * C₁ < c₀ * Real.log y₀ := by
      have h := (div_lt_iff₀ hc₀_pos).mp hlog_y₀
      linarith
    have hden : 0 < 6 * C₁ * (M : ℝ) := by positivity
    calc 4 * (1 / (3 * (M : ℝ))) = (8 * C₁) / (6 * C₁ * (M : ℝ)) := by field_simp; ring
      _ < (c₀ * Real.log y₀) / (6 * C₁ * (M : ℝ)) :=
          div_lt_div_of_pos_right (by linarith) hden
      _ = (1 / 2 : ℝ) * (c₀ * Real.log y₀ / (3 * C₁ * (M : ℝ))) := by ring
  exact ⟨y₀, L₀, P, R, α, hy₀_le_L₀, hP_pos, hα_pos, hα_le_half, rfl, hM_posN,
    hL_lt_L₀, hgood_per, rfl, hδ_gt⟩

end Erdos310Disproof

theorem OMA.disproof : ¬ (type_of% @Erdos310.erdos_310.variants.liu_sawhney) := by
  intro hMain
  rcases hMain with ⟨C, hC⟩
  rcases Erdos310Disproof.exists_counterexample_params C with
    ⟨y₀, L₀, P, R, α, hy₀_le_L₀, hP_pos, hα_pos, hα_le_half, hα_eq, hM_pos,
      hL_lt_L₀, hgood_per, hR_eq, hδ_gt⟩
  have hEv := hC (1 / 14 : ℝ) (by norm_num)
  rw [Filter.eventually_atTop] at hEv
  rcases hEv with ⟨N₁, hN₁⟩
  let N : ℕ := max N₁ (max 4 (max (⌈Real.exp ((1 / α) ^ (14 : ℕ))⌉₊ + 1)
      (⌈((P : ℝ) + 2) / α⌉₊ + 1)))
  have hN_ge_N₁ : N₁ ≤ N := le_max_left _ _
  have hN_ge4 : 4 ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hN_exp : Real.exp ((1 / α) ^ (14 : ℕ)) < (N : ℝ) := by
    have h1nat : ⌈Real.exp ((1 / α) ^ (14 : ℕ))⌉₊ + 1 ≤ N :=
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have h1 : (⌈Real.exp ((1 / α) ^ (14 : ℕ))⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h1nat
    have h2 : Real.exp ((1 / α) ^ (14 : ℕ)) ≤ ⌈Real.exp ((1 / α) ^ (14 : ℕ))⌉₊ := Nat.le_ceil _
    linarith
  have hP_lt : (P : ℝ) + 2 < α * (N : ℝ) := by
    have h1nat : ⌈((P : ℝ) + 2) / α⌉₊ + 1 ≤ N :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    have h1 : (⌈((P : ℝ) + 2) / α⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h1nat
    have h2 : ((P : ℝ) + 2) / α ≤ ⌈((P : ℝ) + 2) / α⌉₊ := Nat.le_ceil _
    have h3 : ((P : ℝ) + 2) / α < (N : ℝ) := by linarith
    have h4 := (div_lt_iff₀ hα_pos).mp h3
    linarith
  have hlogN_ge : Real.log (N : ℝ) ^ (-(1 / 7 : ℝ) + (1 / 14 : ℝ)) ≤ α := by
    have hpow_lt : (1 / α) ^ (14 : ℕ) < Real.log (N : ℝ) := by
      rw [← Real.log_exp ((1 / α) ^ (14 : ℕ))]
      exact Real.log_lt_log (Real.exp_pos _) hN_exp
    have hbase_pos : 0 < (1 / α) ^ (14 : ℝ) := by positivity
    have hpow_le : (1 / α) ^ (14 : ℝ) ≤ Real.log (N : ℝ) := by
      rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact hpow_lt.le
    rw [show -(1 / 7 : ℝ) + (1 / 14 : ℝ) = -(1 / 14 : ℝ) by norm_num]
    calc Real.log (N : ℝ) ^ (-(1 / 14 : ℝ))
        ≤ ((1 / α) ^ (14 : ℝ)) ^ (-(1 / 14 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hbase_pos hpow_le (by norm_num)
      _ = (1 / α) ^ ((14 : ℝ) * (-(1 / 14 : ℝ))) := by
          rw [← Real.rpow_mul (by positivity)]
      _ = (1 / α) ^ (-1 : ℝ) := by norm_num
      _ = α := by rw [Real.rpow_neg_one, one_div, inv_inv]
  rcases Erdos310Disproof.periodic_subset_exists hP_pos hN_ge4 hα_pos hgood_per hR_eq hδ_gt hP_lt with
    ⟨A, hA_sub, hA_card⟩
  have hA_Icc : A ⊆ Finset.Icc 1 N := by
    intro n hn
    have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp (hA_sub hn)).1
    exact Finset.mem_Icc.mpr ⟨by omega, h1.2⟩
  have hA_dense : α * (N : ℝ) ≤ (A.card : ℝ) := by
    rw [hA_card]
    exact Nat.le_ceil _
  rcases hN₁ N hN_ge_N₁ α hlogN_ge hα_le_half A hA_Icc hA_dense with
    ⟨S, hSA, a, b, ha_pos, hab, hb_exp, hS_sum⟩
  exact Erdos310Disproof.no_small_denom_from_good hy₀_le_L₀ hN_ge4 hα_pos hα_eq hM_pos
    hL_lt_L₀ (by linarith) hA_sub hA_card hSA ha_pos hab hb_exp hS_sum
