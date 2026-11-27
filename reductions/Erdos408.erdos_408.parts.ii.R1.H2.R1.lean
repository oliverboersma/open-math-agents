import OMAReductions.R_Erdos408_erdos_408_parts_ii_R1

/-!
Weighted prime moments control the mean-square error of the additive totient height.
The change from `log n` to `log x` uses the logarithmic sum estimate in the parent
reduction, adapted there from Jacob Parish's Plasma AI formalization at 4ea44bf911f8.
-/

open Filter
open scoped Topology

namespace OMA.R_Erdos408_erdos_408_parts_ii_R1_H2_R1

open Finset

theorem prime_log_pos {p : ℕ} (hp : Nat.Prime p) : 0 < Real.log (p : ℝ) :=
  Real.log_pos (by exact_mod_cast hp.one_lt)

theorem sum_log_factorization (n : ℕ) (hn : n ≠ 0) :
    (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * Real.log (p : ℝ)) =
      Real.log (n : ℝ) := by
  have hprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    simpa only [Finsupp.prod, Nat.support_factorization] using
      Nat.prod_factorization_pow_eq_self hn
  conv_rhs => rw [← hprod, Nat.cast_prod]
  rw [Real.log_prod]
  · simp only [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact_mod_cast pow_ne_zero (n.factorization p) (Nat.prime_of_mem_primeFactors hp).ne_zero

theorem primeFactors_subset {n N : ℕ} (hn : n ∈ Icc 1 N) :
    n.primeFactors ⊆ Nat.primesLE N := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hn' := mem_Icc.mp hn
  exact Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hn'.2, hpp⟩

/-- Cauchy–Schwarz on the logarithmic masses of the prime-factor occurrences. -/
theorem square_bound (w : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) (α : ℝ) :
    ((∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * w p) - α * Real.log (n : ℝ)) ^ 2 ≤
      Real.log (n : ℝ) *
        ∑ p ∈ n.primeFactors, (n.factorization p : ℝ) *
          (Real.log (p : ℝ) * (w p / Real.log (p : ℝ) - α) ^ 2) := by
  let a (p : ℕ) : ℝ := (n.factorization p : ℝ) * Real.log (p : ℝ)
  have ha : ∀ p ∈ n.primeFactors, 0 ≤ a p :=
    fun p hp => mul_nonneg (by positivity) (prime_log_pos (Nat.prime_of_mem_primeFactors hp)).le
  have h :=
    sum_sq_le_sum_mul_sum_of_sq_le_mul (r := fun p => a p * (w p / Real.log (p : ℝ) - α))
      (f := a) (g := fun p => a p * (w p / Real.log (p : ℝ) - α) ^ 2) _ ha
      (fun p hp => mul_nonneg (ha p hp) (sq_nonneg _))
      (fun p _ => le_of_eq (by ring))
  have heq : (∑ p ∈ n.primeFactors, a p * (w p / Real.log (p : ℝ) - α)) =
      (∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * w p) - α * Real.log (n : ℝ) := by
    rw [← sum_log_factorization n hn, mul_sum]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    have hl := (prime_log_pos (Nat.prime_of_mem_primeFactors hp)).ne'
    dsimp [a]
    field_simp
  rw [heq] at h
  simp only [a, sum_log_factorization n hn, mul_assoc] at h
  exact h

theorem sum_factorization (N p : ℕ) :
    (∑ n ∈ Icc 1 N, n.factorization p) = N.factorial.factorization p := by
  rw [← prod_Ico_id_eq_factorial, Nat.factorization_prod_apply]
  · congr 1
  · intro n hn
    have := (mem_Ico.mp hn).1
    omega

/-- A finite mean-square bound for any real weights on prime factors.

The multiplicity of each prime across all integers up to `N` is its valuation in `N!`.
Legendre's bound on that valuation supplies the weight `log p / (p - 1)`.
-/
theorem prime_transfer (w : ℕ → ℝ) (N : ℕ) (α : ℝ) :
    (∑ n ∈ Icc 1 N, ((∑ p ∈ n.primeFactors, (n.factorization p : ℝ) * w p) - α * Real.log (n : ℝ)) ^ 2) ≤
      (N : ℝ) * Real.log (N : ℝ) *
        ∑ p ∈ Nat.primesLE N, (Real.log (p : ℝ) / ((p : ℝ) - 1)) *
          (w p / Real.log (p : ℝ) - α) ^ 2 := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, Real.log (N : ℝ) *
        ∑ p ∈ Nat.primesLE N, (n.factorization p : ℝ) *
          (Real.log (p : ℝ) * (w p / Real.log (p : ℝ) - α) ^ 2) := by
      apply sum_le_sum
      intro n hn
      have hn' := mem_Icc.mp hn
      refine (square_bound w n (by omega) α).trans (mul_le_mul ?_ ?_ ?_ ?_)
      · exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
          (by exact_mod_cast hn'.2)
      · apply sum_le_sum_of_subset_of_nonneg (primeFactors_subset hn)
        intro p hp _
        have := prime_log_pos (Nat.prime_of_mem_primesLE hp)
        positivity
      · apply sum_nonneg
        intro p hp
        have := prime_log_pos (Nat.prime_of_mem_primeFactors hp)
        positivity
      · exact Real.log_nonneg (by exact_mod_cast hn'.1.trans hn'.2)
    _ = Real.log (N : ℝ) *
        ∑ p ∈ Nat.primesLE N, (N.factorial.factorization p : ℝ) *
          (Real.log (p : ℝ) * (w p / Real.log (p : ℝ) - α) ^ 2) := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro p hp
      rw [← sum_mul, ← Nat.cast_sum, sum_factorization]
    _ ≤ _ := by
      rw [mul_comm (N : ℝ), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg N)
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hP := Nat.prime_of_mem_primesLE hp
      have h₁ : (N.factorial.factorization p : ℝ) ≤ (N : ℝ) / ((p : ℝ) - 1) := by
        have hnat := Nat.factorization_factorial_le_div_pred hP N
        have hp1 : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr (by exact_mod_cast hP.one_lt)
        apply (le_div_iff₀ hp1).mpr
        have hmul := Nat.mul_le_of_le_div (p - 1) _ _ hnat
        simpa [Nat.cast_mul, Nat.cast_sub hP.one_lt.le] using
          (Nat.cast_le.mpr hmul : (↑(N.factorial.factorization p * (p - 1)) : ℝ) ≤ N)
      calc
        _ ≤ ((N : ℝ) / ((p : ℝ) - 1)) * (Real.log (p : ℝ) * (w p / Real.log (p : ℝ) - α) ^ 2) :=
          mul_le_mul_of_nonneg_right h₁
            (mul_nonneg (prime_log_pos hP).le (sq_nonneg _))
        _ = _ := by ring


theorem sum_factorial_log (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, (N.factorial.factorization p : ℝ) * Real.log (p : ℝ)) ≤
      (N : ℝ) * Real.log (N : ℝ) := by
  calc
    _ = ∑ p ∈ Nat.primesLE N, ∑ n ∈ Icc 1 N, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
      apply sum_congr rfl
      intro p hp
      rw [← sum_factorization, Nat.cast_sum, sum_mul]
    _ = ∑ n ∈ Icc 1 N, Real.log (n : ℝ) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro n hn
      rw [← sum_log_factorization n (by have := (mem_Icc.mp hn).1; omega)]
      symm
      apply sum_subset (primeFactors_subset hn)
      intro p hp hnot
      have hzero : n.factorization p = 0 := by
        by_contra h
        apply hnot
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr h
      simp [hzero]
    _ ≤ ∑ _n ∈ Icc 1 N, Real.log (N : ℝ) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hn₁, hnN⟩ := mem_Icc.mp hn
      exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
        (by exact_mod_cast hnN)
    _ = _ := by simp [Nat.card_Icc, nsmul_eq_mul]

theorem div_le_fact {N p : ℕ} (hp : Nat.Prime p) :
    N / p ≤ N.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (n := N) (b := Nat.log p N + 2) (by omega)]
  have h := single_le_sum (s := Ico 1 (Nat.log p N + 2))
    (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le (N / p ^ i))
    (show 1 ∈ Ico 1 (Nat.log p N + 2) by simp)
  simpa only [pow_one] using h

theorem total_bound {N : ℕ} (hN : 0 < N) :
    (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / ((p : ℝ) - 1)) ≤ 4 * Real.log (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  apply le_of_mul_le_mul_left (a := (N : ℝ)) _ hN'
  calc
    _ = ∑ p ∈ Nat.primesLE N, (N : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) - 1)) := by rw [mul_sum]
    _ ≤ ∑ p ∈ Nat.primesLE N, 4 * ((N.factorial.factorization p : ℝ) * Real.log (p : ℝ)) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN, hP⟩ := Nat.mem_primesLE.mp hp
      have hd : 1 ≤ N / p := Nat.div_pos hpN hP.pos
      have hd' : (1 : ℝ) ≤ (↑(N / p) : ℝ) := by exact_mod_cast hd
      have hmod : ((N % p : ℕ) : ℝ) ≤ p := by exact_mod_cast (Nat.mod_lt N hP.pos).le
      have hdiv : (p : ℝ) * (↑(N / p) : ℝ) + (↑(N % p) : ℝ) = N := by
        exact_mod_cast Nat.div_add_mod N p
      have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hP.two_le
      have hNp : (N : ℝ) ≤ 2 * (p : ℝ) * (↑(N / p) : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hd' (show (0 : ℝ) ≤ p by positivity)]
      have hf : (↑(N / p) : ℝ) ≤ (N.factorial.factorization p : ℝ) := by
        exact_mod_cast div_le_fact (N := N) hP
      have hfact : (N : ℝ) / ((p : ℝ) - 1) ≤ 4 * (N.factorial.factorization p : ℝ) := by
        apply (div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1)).mpr
        calc
          _ ≤ (2 * (p : ℝ)) * (↑(N / p) : ℝ) := hNp
          _ ≤ (4 * ((p : ℝ) - 1)) * (N.factorial.factorization p : ℝ) :=
            mul_le_mul (by linarith) hf (by positivity) (by linarith)
          _ = _ := by ring
      calc
        (N : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) - 1)) =
            (N : ℝ) / ((p : ℝ) - 1) * Real.log (p : ℝ) := by ring
        _ ≤ (4 * (N.factorial.factorization p : ℝ)) * Real.log (p : ℝ) :=
          mul_le_mul_of_nonneg_right hfact (prime_log_pos hP).le
        _ = _ := by ring
    _ ≤ _ := by
      rw [← mul_sum, mul_left_comm]
      exact mul_le_mul_of_nonneg_left (sum_factorial_log N) (by norm_num)


theorem total_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) / ((p : ℝ) - 1) := by
  have h₂ : 2 ∈ Nat.primesLE N := Nat.mem_primesLE.mpr ⟨hN, Nat.prime_two⟩
  have hpos {p : ℕ} (hp : p ∈ Nat.primesLE N) :
      0 < Real.log (p : ℝ) / ((p : ℝ) - 1) := by
    have hP := Nat.prime_of_mem_primesLE hp
    exact div_pos (prime_log_pos hP) (sub_pos.mpr (by exact_mod_cast hP.one_lt))
  exact (hpos h₂).trans_le (single_le_sum (fun p hp => (hpos hp).le) h₂)

theorem prime_decomposition (s : Finset ℕ) (w r : ℕ → ℝ) (α : ℝ)
    (hw : (∑ p ∈ s, w p) ≠ 0) :
    let μ := (∑ p ∈ s, w p * r p) / ∑ p ∈ s, w p
    (∑ p ∈ s, w p * (r p - α) ^ 2) =
      (∑ p ∈ s, w p * (r p - μ) ^ 2) + (∑ p ∈ s, w p) * (μ - α) ^ 2 := by
  intro μ
  have hmean : (∑ p ∈ s, w p * r p) = (∑ p ∈ s, w p) * μ := by
    dsimp only [μ]
    rw [mul_div_left_comm, div_self hw, mul_one]
  have hz : (∑ p ∈ s, w p * (r p - μ)) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hmean, sub_self]
  calc
    _ = ∑ p ∈ s, (w p * (r p - μ) ^ 2 + w p * (μ - α) ^ 2 +
          (2 * (μ - α)) * (w p * (r p - μ))) := by
      apply sum_congr rfl
      intro p hp
      ring
    _ = _ := by
      simp only [sum_add_distrib, ← sum_mul, ← mul_sum, hz, mul_zero, add_zero]

/-- The weighted mean of the normalized prime heights.
Its squared distance from a fixed center should decay as `(log log x)⁻⁵`. -/
def H1 : Prop :=
  let r := fun p : ℕ => ((if p = 2 then 1 else Erdos408.f p - 1 : ℕ) : ℝ) / Real.log p
  let w := fun p : ℕ => Real.log p / ((p : ℝ) - 1)
  ∃ α A : ℝ, 1 / Real.log 3 ≤ α ∧ α ≤ 1 / Real.log 2 ∧
    ∀ᶠ x : ℝ in atTop,
      let s := Nat.primesLE ⌊x⌋₊
      let μ := (∑ p ∈ s, w p * r p) / ∑ p ∈ s, w p
      (μ - α) ^ 2 ≤ A / Real.log (Real.log x) ^ 5

/-- The normalized prime heights should concentrate about their own weighted mean. -/
def H2 : Prop :=
  let r := fun p : ℕ => ((if p = 2 then 1 else Erdos408.f p - 1 : ℕ) : ℝ) / Real.log p
  let w := fun p : ℕ => Real.log p / ((p : ℝ) - 1)
  ∃ B : ℝ, ∀ᶠ x : ℝ in atTop,
    let s := Nat.primesLE ⌊x⌋₊
    let μ := (∑ p ∈ s, w p * r p) / ∑ p ∈ s, w p
    (∑ p ∈ s, w p * (r p - μ) ^ 2) ≤ B * Real.log x / Real.log (Real.log x) ^ 5

theorem main : H1 → H2 → OMA.R_Erdos408_erdos_408_parts_ii_R1.H2 := by
  rintro ⟨α, A, hα₃, hα₂, hA⟩ ⟨B, hB⟩
  let C := |B| + 4 * |A|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨α, 2 * C + 256, hα₃, hα₂, ?_⟩
  have hα₀ : 0 ≤ α := (by positivity : 0 ≤ 1 / Real.log 3).trans hα₃
  have hα2 : α ^ 2 ≤ 4 := by
    have h₂ : α ≤ 2 := hα₂.trans (by
      rw [div_le_iff₀ (Real.log_pos one_lt_two)]
      linarith [Real.log_two_gt_d9])
    nlinarith
  filter_upwards [hA, hB, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    OMA.R_Erdos408_erdos_408_parts_ii_R1.tendsto_log_log_atTop.eventually_gt_atTop 0] with
    x hxA hxB hx hxL hxT
  let N := ⌊x⌋₊
  let v := fun p : ℕ => if p = 2 then 1 else Erdos408.f p - 1
  let F := fun n : ℕ => ∑ p ∈ n.primeFactors, n.factorization p * v p
  let r := fun p : ℕ => (v p : ℝ) / Real.log p
  let w := fun p : ℕ => Real.log p / ((p : ℝ) - 1)
  let s := Nat.primesLE N
  let μ := (∑ p ∈ s, w p * r p) / ∑ p ∈ s, w p
  let L := Real.log x
  let T := Real.log L
  have hx₀ : 0 ≤ x := by linarith
  have hN : 2 ≤ N := (Nat.le_floor_iff hx₀).mpr (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx₀
  have hNlog : Real.log (N : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hNx
  have hT : 0 < T ^ 5 := pow_pos hxT 5
  have hL : 0 ≤ L := by exact hxL.trans' zero_le_one
  have hMass : (∑ p ∈ s, w p) ≤ 4 * L :=
    (total_bound (show 0 < N by omega)).trans (mul_le_mul_of_nonneg_left hNlog (by norm_num))
  have hBias : (μ - α) ^ 2 ≤ |A| / T ^ 5 :=
    hxA.trans (div_le_div_of_nonneg_right (le_abs_self A) hT.le)
  have hVar : (∑ p ∈ s, w p * (r p - μ) ^ 2) ≤ |B| * L / T ^ 5 :=
    hxB.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self B) hL) hT.le)
  have hprime : (∑ p ∈ s, w p * (r p - α) ^ 2) ≤ C * L / T ^ 5 := by
    rw [prime_decomposition s w r α (total_pos hN).ne']
    calc
      _ ≤ |B| * L / T ^ 5 + (4 * L) * (|A| / T ^ 5) :=
        add_le_add hVar (mul_le_mul hMass hBias (sq_nonneg _) (by positivity))
      _ = _ := by dsimp [C]; ring
  have hInt : (∑ n ∈ Icc 1 N, ((F n : ℝ) - α * Real.log (n : ℝ)) ^ 2) ≤
      C * (x * L ^ 2 / T ^ 5) := by
    calc
      _ ≤ (N : ℝ) * Real.log (N : ℝ) * ∑ p ∈ s, w p * (r p - α) ^ 2 :=
        by simpa only [F, Nat.cast_sum, Nat.cast_mul] using
          prime_transfer (fun p => (v p : ℝ)) N α
      _ ≤ (N : ℝ) * Real.log (N : ℝ) * (C * L / T ^ 5) :=
        mul_le_mul_of_nonneg_left hprime (by positivity)
      _ ≤ x * L * (C * L / T ^ 5) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hNx hNlog (Real.log_natCast_nonneg _) hx₀)
          (by positivity)
      _ = _ := by ring
  have hPoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      ((F n : ℝ) - α * L) ^ 2 ≤
        2 * ((F n : ℝ) - α * Real.log (n : ℝ)) ^ 2 + 8 * Real.log (x / n) ^ 2 := by
    have hn₀ : (0 : ℝ) < n := by
      have := (mem_Icc.mp hn).1
      exact_mod_cast (show 0 < n by omega)
    have hlog : L = Real.log (n : ℝ) + Real.log (x / n) := by
      rw [Real.log_div (by linarith : x ≠ 0) hn₀.ne']
      dsimp [L]
      ring
    rw [hlog]
    nlinarith only [sq_nonneg ((F n : ℝ) - α * Real.log (n : ℝ) + α * Real.log (x / n)),
      mul_le_mul_of_nonneg_right hα2 (sq_nonneg (Real.log (x / n)))]
  change (∑ n ∈ Icc 1 N, ((F n : ℝ) - α * L) ^ 2) ≤
    (2 * C + 256) * (x * L ^ 2 / T ^ 5 + x * L)
  calc
    _ ≤ ∑ n ∈ Icc 1 N, (2 * ((F n : ℝ) - α * Real.log (n : ℝ)) ^ 2 +
        8 * Real.log (x / n) ^ 2) := sum_le_sum hPoint
    _ ≤ 2 * (C * (x * L ^ 2 / T ^ 5)) + 8 * (32 * x) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      exact add_le_add (mul_le_mul_of_nonneg_left hInt (by norm_num))
        (mul_le_mul_of_nonneg_left
          (OMA.R_Erdos408_erdos_408_parts_ii_R1.sum_log_div_sq_le hx₀) (by norm_num))
    _ ≤ _ := by
      have hMain : 0 ≤ x * L ^ 2 / T ^ 5 := by positivity
      have hxL' : x ≤ x * L := le_mul_of_one_le_right hx₀ hxL
      nlinarith only [mul_nonneg hC (mul_nonneg hx₀ hL), hMain, hxL']

end OMA.R_Erdos408_erdos_408_parts_ii_R1_H2_R1
