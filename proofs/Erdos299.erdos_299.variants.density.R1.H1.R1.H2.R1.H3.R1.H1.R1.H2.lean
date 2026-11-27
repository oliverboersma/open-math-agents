import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1_H1_R1
import Mathlib

/-! Mertens estimates adapted from @senamakel (Erdős 851). The exponential moment generalizes @marcusbuffett’s finite product in the earlier Erdős 299 step. -/
open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith


theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr


theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp


/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring

theorem abs_mertensG_sub_le (N : ℕ) (hN : 2 ≤ N) :
    |mertensG N - mertensG 2| ≤ (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := mertensG_step n hn
    calc |mertensG (n + 1) - mertensG 2|
        = |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG 2)| := by ring_nf
      _ ≤ |mertensG (n + 1) - mertensG n| + |mertensG n - mertensG 2| := abs_add_le _ _
      _ ≤ _ := add_le_add hs ih
      _ = _ := by push_cast; ring


/-- The constant in Mertens' second theorem over the naturals. -/
noncomputable def mertens2NatConst : ℝ :=
  |mertensG 2| + (2 * mertens1Const + 1) / Real.log 2

theorem mertens1Const_nonneg : 0 ≤ mertens1Const := by
  have := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertens1Const; linarith

/-- **Mertens' second theorem** over the naturals: for `N ≥ 2`,
`|∑_{p ≤ N} 1 / p - log log N| ≤ mertens2NatConst`. -/
theorem abs_sum_inv_sub_log_log_le_nat (N : ℕ) (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N)| ≤ mertens2NatConst := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlN0 : 0 < Real.log N := by linarith
  have hG := abs_mertensG_sub_le N hN
  have hR := abs_sum_log_div_sub_log_le_nat N
  have hC := mertens1Const_nonneg
  have e : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N) =
      mertensG 2 + (mertensG N - mertensG 2) +
        ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N := by
    rw [show mertensG 2 + (mertensG N - mertensG 2) = mertensG N by ring]
    unfold mertensG; ring
  rw [e]
  have h1 : |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| ≤
      mertens1Const / Real.log 2 := by
    rw [abs_div, abs_of_pos hlN0]
    calc _ ≤ mertens1Const / Real.log N := div_le_div_of_nonneg_right hR hlN0.le
      _ ≤ mertens1Const / Real.log 2 := div_le_div_of_nonneg_left hC hl2 hlN
  have h2 : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
      (mertens1Const + 1) / Real.log 2 := by
    have : 0 ≤ 1 / Real.log N := by positivity
    have : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
        (mertens1Const + 1) * (1 / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    rw [div_eq_mul_one_div (mertens1Const + 1)]
    exact this
  have h3 : mertens2NatConst =
      |mertensG 2| + (mertens1Const + 1) / Real.log 2 + mertens1Const / Real.log 2 := by
    unfold mertens2NatConst; ring
  rw [h3]
  calc _ ≤ |mertensG 2 + (mertensG N - mertensG 2)| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := abs_add_le _ _
    _ ≤ |mertensG 2| + |mertensG N - mertensG 2| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := by
      gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem log_log_floor_le (x : ℝ) (hx : 2 ≤ x) :
    Real.log (Real.log ⌊x⌋₊) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ Real.log (Real.log ⌊x⌋₊) + 1 := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN2r : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN2
  have hlN : Real.log 2 ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by norm_num) hN2r
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN0 : 0 < Real.log ⌊x⌋₊ := by linarith
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x (by linarith)
  have hlx : 0 < Real.log x := by linarith
  constructor
  · exact Real.log_le_log hlN0 h1
  · have hq := Real.log_le_sub_one_of_pos (div_pos hlx hlN0)
    rw [Real.log_div hlx.ne' hlN0.ne'] at hq
    have : Real.log x / Real.log ⌊x⌋₊ - 1 ≤ 1 := by
      rw [div_sub_one hlN0.ne', div_le_iff₀ hlN0]; linarith
    linarith

/-- The constant in Mertens' second theorem over the reals. -/
noncomputable def mertens2Const : ℝ := mertens2NatConst + 1

/-- **Mertens' second theorem.** For real `x ≥ 2`,
`|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const`. -/
theorem abs_sum_inv_sub_log_log_le (x : ℝ) (hx : 2 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ mertens2Const := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h := abs_sum_inv_sub_log_log_le_nat ⌊x⌋₊ hN2
  obtain ⟨h1, h2⟩ := log_log_floor_le x hx
  unfold mertens2Const
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' second theorem**, existential form. -/
theorem mertens2 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ C :=
  ⟨mertens2Const, abs_sum_inv_sub_log_log_le⟩
end OMALib.Mertens

namespace OMA.FactorMass
open Finset Real
open scoped BigOperators
def factors (n : ℕ) := n.primeFactors.image (fun p => p ^ n.factorization p)
def powers (C : Finset ℕ) := C.biUnion factors
lemma distinct (n : ℕ) : Set.InjOn (fun p => p ^ n.factorization p) (↑n.primeFactors) := by
  intro p hp q hq he
  have h (p : ℕ) (hp : p ∈ n.primeFactors) :
      (p^n.factorization p).primeFactors = {p} :=
    Nat.primeFactors_prime_pow (Finsupp.mem_support_iff.mp hp) (Nat.prime_of_mem_primeFactors hp)
  have eq := congrArg Nat.primeFactors he
  exact Finset.singleton_inj.mp ((h p hp).symm.trans (eq.trans (h q hq)))
lemma recover {n : ℕ} (hn : n ≠ 0) : ∏ q ∈ factors n, q = n := by
  rw [factors,prod_image (distinct n)]
  exact (Nat.prod_primeFactors_pow_factorization hn).symm
lemma subset_powers {C : Finset ℕ} {n : ℕ} (hn : n ∈ C) (_ : n ≠ 0) :
    factors n ⊆ powers C := fun _ hq => mem_biUnion.mpr ⟨n,hn,hq⟩
lemma exponential_bound (a : ℝ) (C : Finset ℕ) (hz : 0 ∉ C) :
    (∑ n ∈ C, exp ((n.primeFactors.card : ℝ) * a) / n) ≤
      exp (exp a * ∑ q ∈ powers C, (1:ℝ)/q) := by
  classical
  let w (q : ℕ) := exp a / (q : ℝ)
  have reconstruct (n : ℕ) (hn : n ∈ C) : ∏ q ∈ factors n, w q = exp ((n.primeFactors.card : ℝ) * a) / n := by
    have hne : n ≠ 0 := fun e => hz (e ▸ hn)
    have den : (∏ q ∈ factors n, (q : ℝ)) = n := by
      change (∏ x ∈ factors n, (Nat.castRingHom ℝ) x) = (Nat.castRingHom ℝ) n
      rw [← map_prod,recover hne]
    simp only [w,prod_div_distrib,prod_const,den]
    rw [factors,card_image_of_injOn (distinct n),← exp_nat_mul]
  have inject : Set.InjOn factors (↑C) := by
    intro n hn m hm heq
    have h := congrArg (fun s : Finset ℕ => ∏ q ∈ s, q) heq
    simpa only [recover (show n≠0 from fun e => hz (e ▸ hn)),recover (show m≠0 from fun e => hz (e ▸ hm))] using h
  have included : C.image factors ⊆ (powers C).powerset := by
    intro s hs
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hs
    exact mem_powerset.mpr (subset_powers hn (fun e => hz (e ▸ hn)))
  calc
    _ = ∑ s ∈ C.image factors, ∏ q ∈ s, w q := by
      rw [sum_image inject]
      exact sum_congr rfl (fun n hn => (reconstruct n hn).symm)
    _ ≤ ∑ s ∈ (powers C).powerset, ∏ q ∈ s, w q :=
      sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => prod_nonneg fun _ _ => by dsimp [w]; positivity)
    _ = ∏ q ∈ powers C, (1+w q) := (prod_one_add _).symm
    _ ≤ ∏ q ∈ powers C, exp (w q) := prod_le_prod
      (fun q _ => by dsimp [w]; positivity) (fun q _ => by linarith [add_one_le_exp (w q)])
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro q hq; dsimp [w]; ring
end OMA.FactorMass

namespace OMA.RoughBudget
open Finset Real Filter OMA.FactorMass
open scoped Classical Topology

noncomputable def K : ℝ := (∑' p : ℕ, 1 / (p : ℝ)^2) * 2

lemma higher (S : Finset ℕ) (h : ∀ q ∈ S, IsPrimePow q ∧ ¬q.Prime) :
    ∑ q ∈ S, (1 : ℝ)/q ≤ K := by
  classical
  have rep (q : S) : ∃ v : ℕ × ℕ, v.1.Prime ∧ (q : ℕ) = v.1 ^ (v.2 + 2) := by
    obtain ⟨p,k,hp,hk,e⟩ := (isPrimePow_nat_iff _).mp (h q q.property).1
    have h2 : 2 ≤ k := by
      by_contra! hh
      have ek : k=1 := by omega
      simp [ek] at e
      exact (h q q.property).2 (e.symm ▸ hp)
    exact ⟨(p,k-2),hp,by simpa [show k-2+2=k by omega] using e.symm⟩
  choose f hf he using rep
  have inj : Function.Injective f := fun i j eq => Subtype.ext ((he i).trans (eq ▸ (he j).symm))
  let T := S.attach.image f
  let A := T.image Prod.fst
  let B := T.image Prod.snd
  let w (v : ℕ × ℕ) := (1/(v.1:ℝ)^2) * (1/2:ℝ)^v.2
  have nonneg (v) : 0 ≤ w v := by dsimp [w]; positivity
  have sub : T ⊆ A ×ˢ B := fun v hv => mem_product.mpr
    ⟨mem_image_of_mem Prod.fst hv,mem_image_of_mem Prod.snd hv⟩
  calc
    _ = ∑ q ∈ S.attach, (1 : ℝ)/(q.val : ℝ) := (sum_attach S _).symm
    _ ≤ ∑ q ∈ S.attach, w (f q) := by
      apply sum_le_sum
      intro q _
      rw [he q,Nat.cast_pow,pow_add]
      simp only [w,one_div,mul_inv_rev,inv_pow]
      have p2 : (2:ℝ) ≤ (f q).1 := by exact_mod_cast (hf q).two_le
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) p2 _)) (by positivity)
    _ = ∑ v ∈ T, w v := (sum_image inj.injOn).symm
    _ ≤ ∑ v ∈ A ×ˢ B, w v := sum_le_sum_of_subset_of_nonneg sub (fun v _ _ => nonneg v)
    _ = (∑ p ∈ A, 1/(p:ℝ)^2) * (∑ e ∈ B, (1/2:ℝ)^e) := by
      rw [sum_product, sum_mul]; apply sum_congr rfl; intro p hp; rw [mul_sum]
    _ ≤ K := by
      have hA := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).sum_le_tsum A
        (fun _ _ => by positivity)
      have hg := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
      have hB := hg.summable.sum_le_tsum B (fun _ _ => by positivity)
      rw [hg.tsum_eq] at hB
      norm_num at hB
      exact mul_le_mul hA hB (sum_nonneg fun _ _ => by positivity) (tsum_nonneg fun _ => by positivity)

lemma window {X : ℕ} {Y : ℝ} (hY : 2 ≤ Y) (hYX : Y ≤ X)
    (S : Finset ℕ) (hs : ∀ q ∈ S, IsPrimePow q ∧ Y < q ∧ q ≤ X) :
    ∑ q ∈ S, (1:ℝ)/q ≤ K + 2 * OMALib.Mertens.mertens2Const + log (log X) - log (log Y) := by
  classical
  let P := S.filter Nat.Prime
  let H := S.filter (fun n => ¬ n.Prime)
  have split : (∑ q ∈ P, (1:ℝ)/q) + (∑ q ∈ H, (1:ℝ)/q) = ∑ q ∈ S, (1:ℝ)/q :=
    sum_filter_add_sum_filter_not ..
  have hi := higher H (fun q hq => ⟨(hs q (mem_filter.mp hq).1).1,(mem_filter.mp hq).2⟩)
  let U := X.primesLE
  let L := (⌊Y⌋₊).primesLE
  have lu : L ⊆ U := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans (Nat.floor_le_of_le hYX),Nat.prime_of_mem_primesLE hp⟩
  have sub : P ⊆ U \ L := by
    intro p hp
    obtain ⟨hm,hp'⟩ := mem_filter.mp hp
    exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨(hs p hm).2.2,hp'⟩,fun h => (not_le.mpr (hs p hm).2.1)
      ((Nat.le_floor_iff (by linarith : 0 ≤ Y)).mp (Nat.le_of_mem_primesLE h))⟩
  have le := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => (1:ℝ)/p) sub (fun _ _ _ => by positivity)
  have su := sum_sdiff lu (f := fun p : ℕ => (1:ℝ)/p)
  have mx := (abs_le.mp (OMALib.Mertens.abs_sum_inv_sub_log_log_le (x := (X:ℝ)) (hY.trans hYX))).2
  have my := (abs_le.mp (OMALib.Mertens.abs_sum_inv_sub_log_log_le (x := Y) hY)).1
  rw [Nat.floor_natCast] at mx
  change (∑ q ∈ U, _) - _ ≤ _ at mx
  change _ ≤ (∑ q ∈ L, _) - _ at my
  linarith

end OMA.RoughBudget

namespace OMA.RoughBudget
open Filter Finset Real OMA.FactorMass
open scoped Classical Topology

noncomputable def w (N : ℕ) := log (log N)
noncomputable def Y (N : ℕ) := exp (log N / (2*(w N)^2))
noncomputable def R (N : ℕ) := (range N).filter (fun d => 0 < d ∧ ∀ (p : ℕ), p ∈ d.primeFactors →
    Y N < (p:ℝ)^d.factorization p)

lemma wtop : Tendsto w atTop atTop :=
  tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma budget (η : ℝ) (hη : 0 < η) : ∀ᶠ N : ℕ in atTop,
    ∑ q ∈ powers (R N), (1:ℝ)/q ≤ η*w N := by
  let C := K + 2*OMALib.Mertens.mertens2Const + log 2
  have hcore := (tendsto_exp_div_pow_atTop 2).comp wtop
  have hlog := wtop.eventually ((Real.isLittleO_log_id_atTop).bound (show 0 < η/4 by positivity))
  have hconst := (wtop.const_mul_atTop (show 0 < η/2 by positivity)).eventually_ge_atTop C
  filter_upwards [wtop.eventually_ge_atTop 1, eventually_ge_atTop 3, hcore.eventually_ge_atTop 4,
    hlog,hconst] with N hw hN he hlo hc
  have hNr : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
  have hL : 0 < log N := log_pos hNr
  have hw' : 0 < w N := by linarith
  change 4 ≤ exp (w N) / w N ^ 2 at he
  rw [w,exp_log hL] at he
  change 4 ≤ log N / w N^2 at he
  have low : 2 ≤ Y N := by
    unfold Y
    have : (2:ℝ) ≤ log N / (2*w N^2) := by linarith [show log N / (2*w N^2) = (log N / w N^2)/2 by ring]
    linarith [Real.add_one_le_exp (log N / (2*w N^2))]
  have up : Y N ≤ N := by
    rw [Y, ← le_log_iff_exp_le (by positivity : 0 < (N:ℝ))]
    apply div_le_self hL.le
    nlinarith [sq_nonneg (w N-1)]
  have hs (q) (hq : q ∈ powers (R N)) : IsPrimePow q ∧ Y N < q ∧ q ≤ N := by
    obtain ⟨d,hd,hq⟩ := mem_biUnion.mp hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    obtain ⟨hlt,hd0,hm⟩ := mem_filter.mp hd
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact ⟨hprime.isPrimePow.pow (Finsupp.mem_support_iff.mp hp),by simpa using hm p hp,
      (Nat.le_of_dvd hd0 (Nat.ordProj_dvd d p)).trans (mem_range.mp hlt).le⟩
  have mass := window low up (powers (R N)) hs
  have ey : log (log (Y N)) = w N - (log 2 + 2 * log (w N)) := by
    rw [Y,log_exp,Real.log_div hL.ne' (by positivity),Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    rfl
  rw [ey] at mass
  change ‖log (w N)‖ ≤ η / 4 * ‖w N‖ at hlo
  rw [Real.norm_of_nonneg (log_nonneg hw),Real.norm_of_nonneg hw'.le] at hlo
  change C ≤ η/2*w N at hc
  change _ ≤ K + 2 * OMALib.Mertens.mertens2Const + w N - _ at mass
  dsimp [C] at hc
  linarith

end OMA.RoughBudget

namespace OMA.RoughBudget
open Filter Finset Real OMA.FactorMass
open scoped Classical Topology

theorem finish : ∀ᶠ N : ℕ in atTop,
  ∑ d ∈ R N, (if (d.primeFactors.card : ℝ) ≤ w N/110 then (log N)^(-(1/99:ℝ))
    else 1+log N) / d < (log N)^(-(1/100:ℝ))/2 := by
  let η : ℝ := (1/40000) / exp 330
  have hη : 0 < η := by dsimp [η]; positivity
  filter_upwards [budget η hη,wtop.eventually_ge_atTop 40000,eventually_ge_atTop 3] with N hm hw hN
  have hL : 0 < log N := log_pos (by exact_mod_cast (show 1<N by omega))
  have hzero : 0 ∉ R N := by simp [R]
  have hw0 : 0 ≤ w N := by linarith
  have hlog : exp (w N) = log N := exp_log hL
  have em := exponential_bound 330 (R N) hzero
  have em' : exp 330 * ∑ q ∈ powers (R N), (1:ℝ)/q ≤ w N / 40000 := calc
    _ ≤ exp 330 * (η * w N) := mul_le_mul_of_nonneg_left hm (exp_pos _).le
    _ = _ := by dsimp [η]; field_simp
  have single (d : ℕ) :
    (if (d.primeFactors.card : ℝ) ≤ w N/110 then (log N)^(-(1/99:ℝ)) else 1+log N) ≤
      exp (-(w N)/99) * exp ((d.primeFactors.card : ℝ)*330) := by
    split_ifs with small
    · rw [rpow_def_of_pos hL]
      change exp (w N * _) ≤ _
      have e : w N * -(1/99:ℝ) = -w N /99 := by ring
      rw [e]
      exact le_mul_of_one_le_right (exp_pos _).le (one_le_exp (by positivity))
    · rw [← exp_add,← hlog]
      calc
        1+exp (w N) ≤ exp (w N)+exp (w N) := by linarith [one_le_exp hw0]
        _ ≤ exp 1 * exp (w N) := by nlinarith [mul_le_mul_of_nonneg_right (add_one_le_exp (1:ℝ)) (exp_pos (w N)).le]
        _ = exp (1+w N) := (exp_add ..).symm
        _ ≤ _ := exp_le_exp.mpr (by push Not at small; linarith)
  have final : exp (-w N/99+w N/40000) < exp (w N * -(1/100:ℝ)) / 2 := by
    rw [lt_div_iff₀ (by norm_num)]
    calc
      _ ≤ exp (-w N/99+w N/40000) * exp 1 := mul_le_mul_of_nonneg_left
        (by linarith [add_one_le_exp (1:ℝ)]) (exp_pos _).le
      _ = _ := (exp_add ..).symm
      _ < _ := exp_lt_exp.mpr (by linarith)
  conv_rhs => rw [rpow_def_of_pos hL]
  calc
    _ ≤ ∑ d ∈ R N, exp (-(w N)/99) * (exp ((d.primeFactors.card:ℝ)*330)/d) := by
      apply sum_le_sum; intro d _
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (single d) (by positivity)
    _ = _ := (mul_sum ..).symm
    _ ≤ exp (-(w N)/99) * exp (w N/40000) :=
      mul_le_mul_of_nonneg_left (em.trans (exp_le_exp.mpr em')) (exp_pos _).le
    _ < _ := by rw [←exp_add]; exact final

end OMA.RoughBudget

theorem OMA.solution : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1_H1_R1.H2 := OMA.RoughBudget.finish
