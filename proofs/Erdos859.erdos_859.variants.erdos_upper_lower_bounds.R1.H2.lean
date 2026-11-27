import OMAReductions.R_Erdos859_erdos_859_variants_erdos_upper_lower_bounds_R1
import Mathlib

/-! The dyadic divisor estimate is adapted from @marcusbuffett’s Erdős 692 proof (#3559), including the Mertens estimates credited there to @senamakel (#2394). -/
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

theorem log_one_sub_inv_bounds {p : ℕ} (hp : p.Prime) :
    -(1 / (p : ℝ)) - Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        Real.log (1 - 1 / (p : ℝ)) ∧
      Real.log (1 - 1 / (p : ℝ)) ≤ -(1 / (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 - 1 / (p : ℝ))⁻¹ = -(1 / (p : ℝ)) - 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    rw [e] at h
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    have hlp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp2
    have : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 := by
      rw [div_div, div_le_div_iff₀ hden (by positivity)]
      nlinarith
    linarith
  · have h := Real.log_le_sub_one_of_pos hpos
    linarith

/-- **Mertens' third theorem**, explicit form. For real `z ≥ 2`,
`exp (-c) / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ exp (mertens2Const) / log z`
with `c = mertens2Const + primePowerConst / log 2`. -/
theorem prod_one_sub_inv_bounds (z : ℝ) (hz : 2 ≤ z) :
    Real.exp (-(mertens2Const + primePowerConst / Real.log 2)) / Real.log z ≤
        ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ Real.exp mertens2Const / Real.log z := by
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hne : ∀ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    intro h; linarith
  have hPpos : 0 < ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hlogP := Real.log_prod (s := Nat.primesLE ⌊z⌋₊) (f := fun p => (1 - 1 / (p : ℝ))) hne
  have hup : Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) ≤
      -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p := by
    rw [hlogP, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun p hp => (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).2
  have hlo : -∑ p ∈ Nat.primesLE ⌊z⌋₊, (1 : ℝ) / p - primePowerConst / Real.log 2 ≤
      Real.log (∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ))) := by
    rw [hlogP]
    have hK := sum_log_div_mul_sub_one_le (Nat.primesLE ⌊z⌋₊)
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK' : ∑ p ∈ Nat.primesLE ⌊z⌋₊, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) / Real.log 2 ≤
        primePowerConst / Real.log 2 := by
      rw [← Finset.sum_div]; exact div_le_div_of_nonneg_right hK hl2.le
    have hs := Finset.sum_le_sum (s := Nat.primesLE ⌊z⌋₊) fun p hp =>
      (log_one_sub_inv_bounds (Nat.mem_primesLE.mp hp).2).1
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hs
    linarith
  have hM := abs_sum_inv_sub_log_log_le z hz
  rw [abs_le] at hM
  have hexp : ∀ t : ℝ, Real.exp t / Real.log z = Real.exp (t - Real.log (Real.log z)) := by
    intro t
    rw [Real.exp_sub, Real.exp_log hlz]
  rw [hexp, hexp, ← Real.exp_log hPpos]
  constructor
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]
  · apply Real.exp_le_exp.mpr; linarith [hM.1, hM.2]

/-- **Mertens' third theorem**, existential form: there are constants `0 < c₁` and `c₂` with
`c₁ / log z ≤ ∏_{p ≤ z} (1 - 1 / p) ≤ c₂ / log z` for all real `z ≥ 2`. -/
theorem mertens3 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ z : ℝ, 2 ≤ z →
    c₁ / Real.log z ≤ ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ∧
      ∏ p ∈ Nat.primesLE ⌊z⌋₊, (1 - 1 / (p : ℝ)) ≤ c₂ / Real.log z :=
  ⟨_, _, Real.exp_pos _, Real.exp_pos _, prod_one_sub_inv_bounds⟩


/-- Upper half of Mertens' second theorem for any subset of the primes, for instance the primes
in a residue class: `∑_{p ≤ x, P p} 1 / p ≤ log log x + mertens2Const` for real `x ≥ 2`. -/
theorem sum_inv_filter_le (P : ℕ → Prop) [DecidablePred P] (x : ℝ) (hx : 2 ≤ x) :
    ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      Real.log (Real.log x) + mertens2Const := by
  have h := abs_sum_inv_sub_log_log_le x hx
  rw [abs_le] at h
  have hsub : ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter P, (1 : ℝ) / p ≤
      ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun p _ _ => by positivity)
  linarith [h.2]

end OMALib.Mertens

namespace Work692
open Finset Filter
open scoped Classical BigOperators Topology

noncomputable def ind (S : Set ℕ) (x : ℕ) : ℝ := if x∈S then 1 else 0
def wgt (P : Finset ℕ) (t : ℝ) (x : ℕ) := ∏ p ∈ P, if p∣x then t else 1
def row (P : Finset ℕ) (d : ℕ) (t : ℝ) (x : ℕ) := if d∣x then wgt P t x else 0
noncomputable def factor (d p : ℕ) (t : ℝ) : ℝ := if p∣d then t else 1+(t-1)/p
def avg (f : ℕ → ℝ) (a : ℝ) := ∀ᶠ N : ℕ in atTop,
  ∑ x ∈ range (N.factorial), f x = a*N.factorial
def boundSet (S : Set ℕ) (a : ℝ) := ∀ᶠ N : ℕ in atTop,
  ∑ x ∈ range (N.factorial), ind S x ≤ a*N.factorial

lemma w_nonneg {P : Finset ℕ} {t : ℝ} (ht : 0≤t) (x : ℕ) : 0≤wgt P t x := by
  exact prod_nonneg (fun p _ => by split_ifs <;> positivity)
lemma r_nonneg {P : Finset ℕ} {t : ℝ} (ht : 0≤t) (d x : ℕ) : 0≤row P d t x := by
  dsimp [row]; split_ifs; exact w_nonneg ht x; exact le_rfl

lemma mean_dvd (d : ℕ) (hd : 0<d) : avg (fun x => if d∣x then 1 else 0) (1/d) := by
  filter_upwards [eventually_ge_atTop d] with N hN
  have hdiv : d∣N.factorial := Nat.dvd_factorial hd hN
  have hswap : (∑ x ∈ range N.factorial, (if d∣x then (1:ℝ) else 0)) =
      ∑ x ∈ range N.factorial, (if d∣x+1 then (1:ℝ) else 0) := by
    let F (x : ℕ) : ℝ := if d∣x then 1 else 0
    have h1 := sum_range_succ F N.factorial
    have h2 := sum_range_succ' F N.factorial
    change ∑ x ∈ range N.factorial, F x = ∑ x ∈ range N.factorial, F (x+1)
    have hf : F N.factorial=F 0 := by simp [F,hdiv]
    linarith
  rw [hswap,← sum_filter,sum_const,Nat.card_multiples,nsmul_eq_mul,mul_one,
    Nat.cast_div hdiv (by exact_mod_cast hd.ne')]
  ring

lemma mean_row (P : Finset ℕ) (hP : ∀ p∈P, p.Prime) (d : ℕ) (hd : 0<d) (t : ℝ) :
    avg (row P d t) ((1/d)*∏ p ∈ P, factor d p t) := by
  induction P using Finset.induction_on generalizing d with
  | empty =>
    have h : row ∅ d t = (fun x => if d∣x then 1 else 0) := by funext x; simp [row,wgt]
    rw [h]; simpa using mean_dvd d hd
  | @insert p P hp ih =>
    have hp' := hP p (mem_insert_self _ _)
    have hP' : ∀ q∈P, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have r1 := ih hP' d hd
    by_cases hpd : p∣d
    · filter_upwards [r1] with N hn
      have eq (x : ℕ) : row (insert p P) d t x=t*row P d t x := by
        by_cases h : d∣x
        · simp [row,wgt,prod_insert,hp,h,hpd.trans h]
        · simp [row,h]
      simp_rw [eq,← mul_sum,hn]
      rw [prod_insert hp,show factor d p t=t by simp [factor,hpd]]; ring
    · have hcop : d.Coprime p := (hp'.coprime_iff_not_dvd.mpr hpd).symm
      have r2 := ih hP' (d*p) (Nat.mul_pos hd hp'.pos)
      have prodEq : (∏ q ∈ P, factor (d*p) q t) = ∏ q ∈ P, factor d q t := by
        apply prod_congr rfl
        intro q hq
        have hq' := hP' q hq
        have ne : ¬q∣p := by
          intro h; have := (Nat.prime_dvd_prime_iff_eq hq' hp').mp h
          exact hp (this ▸ hq)
        simp [factor,hq'.dvd_mul,ne]
      have eq (x : ℕ) : row (insert p P) d t x=row P d t x+(t-1)*row P (d*p) t x := by
        have iff : d*p∣x ↔ d∣x ∧ p∣x := ⟨fun h => ⟨(dvd_mul_right d p).trans h,
          (dvd_mul_left p d).trans h⟩,fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
        by_cases h : d∣x <;> by_cases k : p∣x <;> simp [row,wgt,prod_insert,hp,iff,h,k] <;> ring
      filter_upwards [r1,r2] with N hn hm
      simp_rw [eq,sum_add_distrib,←mul_sum,hn,hm]
      rw [prodEq,prod_insert hp]
      simp only [factor,if_neg hpd,Nat.cast_mul]
      have hD : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
      have hT : (p:ℝ)≠0 := by exact_mod_cast hp'.ne_zero
      field_simp <;> ring

lemma bound_mono {S T : Set ℕ} {a b : ℝ} (h : S⊆T) (hab : a≤b) (bt : boundSet T a) :
    boundSet S b := by
  filter_upwards [bt] with N hn
  exact (sum_le_sum (fun x _ => by by_cases hx : x∈S; simp [ind,hx,h hx]; simp [ind,hx]; split_ifs <;> norm_num)).trans
    (hn.trans (mul_le_mul_of_nonneg_right hab (by positivity)))

lemma bound_union {S T : Set ℕ} {a b : ℝ} (hs : boundSet S a) (ht : boundSet T b) :
    boundSet (S∪T) (a+b) := by
  filter_upwards [hs,ht] with N hn hm
  calc _ ≤ ∑ x ∈ range N.factorial, (ind S x+ind T x) := by
           apply sum_le_sum; intro x _
           by_cases h : x∈S <;> by_cases k : x∈T <;> simp [ind,h,k]
       _ ≤ _ := by rw [sum_add_distrib,add_mul]; linarith

lemma bound_iUnion (s : Finset ℕ) (T : ℕ → Set ℕ) (a : ℝ)
    (h : ∀ i∈s, boundSet (T i) a) : boundSet (⋃ i∈s, T i) (s.card*a) := by
  induction s using Finset.induction_on with
  | empty => simp [boundSet,ind]
  | @insert i s hi ih =>
    have hh := bound_union (h i (mem_insert_self _ _)) (ih (fun j hj => h j (mem_insert_of_mem hj)))
    simpa [hi,add_mul,add_comm] using hh

lemma density_bound {S : Set ℕ} {δ a : ℝ} (hs : S.HasDensity δ) (hb : boundSet S a) :
    δ≤a := by
  have tend : Tendsto Nat.factorial atTop atTop := tendsto_atTop_mono Nat.self_le_factorial tendsto_id
  apply le_of_tendsto (hs.comp tend)
  filter_upwards [hb] with N hN
  change Set.partialDensity S Set.univ N.factorial ≤ a
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Set.ncard_Iio_nat]
  rw [div_le_iff₀ (by exact_mod_cast Nat.factorial_pos N)]
  have eq : (S ∩ Set.Iio N.factorial).ncard = ((range N.factorial).filter (· ∈ S)).card := by
    rw [← Set.ncard_coe_finset]; congr 1; ext x; simp [and_comm]
  rw [eq]
  simpa [ind,← sum_filter] using hN
end Work692


namespace Work692
open Finset Filter ArithmeticFunction Real
open scoped Classical BigOperators ArithmeticFunction.zeta ArithmeticFunction.vonMangoldt
noncomputable section

def fw (s : ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n=0 then 0 else s^n.primeFactors.card,by simp⟩
def frac (s : ℝ) : ArithmeticFunction ℝ := ⟨fun n => fw s n / n,by simp⟩

lemma fw_apply {s : ℝ} {n : ℕ} (hn : n≠0) : fw s n = s^n.primeFactors.card := by simp [fw,hn]
lemma frac_apply (s : ℝ) (n : ℕ) : frac s n = fw s n / n := rfl
lemma fw_pos {s : ℝ} (hs : 0 ≤ s) (n : ℕ) : 0≤fw s n := by
  by_cases h : n=0 <;> simp [fw,h]; positivity

lemma frac_mult (s : ℝ) : (frac s).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [frac,fw],?_⟩
  intro m n hm hn cop
  simp only [frac_apply,fw_apply hm,fw_apply hn,fw_apply (mul_ne_zero hm hn),Nat.cast_mul,
    Nat.primeFactors_mul hm hn,card_union_of_disjoint cop.disjoint_primeFactors,pow_add]
  ring

lemma local_geom (p k : ℕ) (hp : p.Prime) (s : ℝ) (hs : 0 ≤ s) :
    ∑ i ∈ range (k+1), frac s (p^i) ≤ 1+s/((p:ℝ)-1) := by
  have p1 : 1<(p:ℝ) := by exact_mod_cast hp.one_lt
  have p0 : (0:ℝ)<p := by linarith
  let r := (p:ℝ)⁻¹
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hr1 : r<1 := inv_lt_one_of_one_lt₀ p1
  have eq (i : ℕ) : frac s (p^(i+1))=s*r^(i+1) := by
    simp [frac_apply,fw_apply (pow_ne_zero _ hp.ne_zero),Nat.primeFactors_prime_pow (Nat.succ_ne_zero _) hp,r,div_eq_mul_inv]
  rw [sum_range_succ']
  simp_rw [eq,pow_succ',←mul_assoc,←mul_sum]
  have ub := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum (range k) (fun _ _ => pow_nonneg hr0 _)
  rw [tsum_geometric_of_lt_one hr0 hr1] at ub
  have le := mul_le_mul_of_nonneg_left ub (mul_nonneg hs hr0)
  have eq' : s*r*(1-r)⁻¹=s/((p:ℝ)-1) := by
    dsimp [r]; field_simp <;> ring
  simpa [eq',frac_apply,fw,add_comm] using add_le_add_right le 1

lemma harmonic_euler (N : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    ∑ n ∈ Ioc 0 N, frac s n ≤ ∏ p ∈ Nat.primesLE N, (1+s/((p:ℝ)-1)) := by
  let M := N.factorial
  have hm : M≠0 := Nat.factorial_ne_zero _
  have sub : Ioc 0 N ⊆ M.divisors := by
    intro n hn
    exact Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (mem_Ioc.mp hn).1 (mem_Ioc.mp hn).2,hm⟩
  have eq : M.primeFactors=Nat.primesLE N := by
    ext p
    simp only [Nat.mem_primeFactors,Nat.mem_primesLE,hm,not_false_eq_true,and_true]
    constructor
    · rintro ⟨hp,h⟩; exact ⟨hp.dvd_factorial.mp h.1,hp⟩
    · rintro ⟨h,hp⟩; exact ⟨hp,hp.dvd_factorial.mpr h,hm⟩
  have mult := (frac_mult s).mul ArithmeticFunction.isMultiplicative_zeta.natCast
  calc _ ≤ ∑ n ∈ M.divisors, frac s n := sum_le_sum_of_subset_of_nonneg sub
           (fun n _ _ => div_nonneg (fw_pos hs n) (Nat.cast_nonneg _))
       _ = (frac s * ζ) M := coe_mul_zeta_apply.symm
       _ = ∏ p ∈ M.primeFactors, (frac s * ζ) (p^(M.factorization p)) := by
           simpa [Finsupp.prod,Nat.support_factorization] using mult.multiplicative_factorization _ hm
       _ ≤ _ := by
           rw [eq]
           apply Finset.prod_le_prod
           · intro p _
             rw [coe_mul_zeta_apply]; exact sum_nonneg fun i _ => div_nonneg (fw_pos hs _) (Nat.cast_nonneg _)
           · intro p hp; have pr := Nat.prime_of_mem_primesLE hp
             rw [coe_mul_zeta_apply,Nat.sum_divisors_prime_pow pr]
             exact local_geom p _ pr _ hs

def zetaSq := ∑' n : ℕ, 1/(n:ℝ)^2

lemma harmonic_bound (s : ℝ) (hs : 0 ≤ s) : ∃ C : ℝ, 0<C ∧ ∀ N : ℕ, 2≤N →
    ∑ n ∈ Ioc 0 N, frac s n ≤ C*(Real.log N)^s := by
  refine ⟨exp (s*OMALib.Mertens.mertens2NatConst+2*s*zetaSq),exp_pos _,?_⟩
  intro N hN
  let P := Nat.primesLE N
  have hM := (abs_le.mp (OMALib.Mertens.abs_sum_inv_sub_log_log_le_nat N hN)).2
  have hsq : ∑ p ∈ P, 1/(p:ℝ)^2 ≤ zetaSq :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).sum_le_tsum _ (fun _ _ => by positivity)
  have hp (p : ℕ) (h : p∈P) : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE h).two_le
  have hloc (p : ℕ) (h : p∈P) : s/((p:ℝ)-1) ≤ s*(1/(p:ℝ))+2*s*(1/(p:ℝ)^2) := by
    have h' := hp p h; have h1 : 0<(p:ℝ)-1 := by linarith
    have h0 : (0:ℝ)<p := by linarith
    field_simp
    nlinarith [mul_nonneg hs (sub_nonneg.mpr h'),mul_nonneg (mul_nonneg hs (sub_nonneg.mpr h')) h0.le]
  have hsum : ∑ p ∈ P, s/((p:ℝ)-1) ≤ s*Real.log (Real.log N)+s*OMALib.Mertens.mertens2NatConst+2*s*zetaSq := by
    apply (sum_le_sum hloc).trans
    rw [sum_add_distrib,←mul_sum,←mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (show ∑ p ∈ P, 1/(p:ℝ) ≤ Real.log (Real.log N)+OMALib.Mertens.mertens2NatConst by dsimp [P]; linarith) hs
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0≤2*s by positivity)]
  have hl : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  apply (harmonic_euler N s hs).trans
  calc _ ≤ ∏ p ∈ P, exp (s/((p:ℝ)-1)) := by
           apply Finset.prod_le_prod
           · intro p h; have := hp p h; exact add_nonneg zero_le_one (div_nonneg hs (by linarith))
           · intro p _; linarith [Real.add_one_le_exp (s/((p:ℝ)-1))]
       _ = exp (∑ p ∈ P, s/((p:ℝ)-1)) := (Real.exp_sum ..).symm
       _ ≤ _ := by
           rw [Real.rpow_def_of_pos hl,←Real.exp_add]
           apply exp_le_exp.mpr; linarith

end
end Work692


namespace Work692
open Finset Filter ArithmeticFunction Real
open scoped Classical BigOperators ArithmeticFunction.vonMangoldt
noncomputable section

lemma log_weight (s : ℝ) (hs : 0 ≤ s) (hs' : s≤1) (N : ℕ) :
    ∑ n ∈ Ioc 0 N, fw s n*Real.log n ≤ (Real.log 4+4)*N*∑ n ∈ Ioc 0 N, frac s n := by
  calc _ ≤ ∑ n ∈ Ioc 0 N, (fw s * vonMangoldt) n := by
           apply sum_le_sum
           intro n hn
           have hn' : n≠0 := (mem_Ioc.mp hn).1.ne'
           rw [← vonMangoldt_sum,mul_sum,ArithmeticFunction.mul_apply,
             Nat.sum_divisorsAntidiagonal' (fun a b => fw s a * vonMangoldt b)]
           apply sum_le_sum
           intro h hh
           have dvd := Nat.dvd_of_mem_divisors hh
           have dvd' := Nat.div_dvd_of_dvd dvd
           have nd : n/h≠0 := (Nat.div_pos (Nat.le_of_dvd (by omega) dvd)
             (Nat.pos_of_mem_divisors hh)).ne'
           apply mul_le_mul_of_nonneg_right _ vonMangoldt_nonneg
           rw [fw_apply hn',fw_apply nd]
           exact pow_le_pow_of_le_one hs hs' (card_le_card (Nat.primeFactors_mono dvd' hn'))
       _ = ∑ n ∈ Ioc 0 N, fw s n*∑ m ∈ Ioc 0 (N/n), vonMangoldt m :=
            sum_Ioc_mul_eq_sum_sum _ _ _
       _ ≤ ∑ n ∈ Ioc 0 N, (Real.log 4+4)*N*frac s n := by
           apply sum_le_sum
           intro n hn
           have H := Chebyshev.psi_le_const_mul_self (x:=((N/n:ℕ):ℝ)) (by positivity)
           simp only [Chebyshev.psi,Nat.floor_natCast] at H
           have hC : 0≤Real.log 4+4 := by positivity
           have hp := (mem_Ioc.mp hn).1
           have hh := H.trans (mul_le_mul_of_nonneg_left (Nat.cast_div_le (m:=N) (n:=n) (α:=ℝ)) hC)
           exact (mul_le_mul_of_nonneg_left hh (fw_pos hs n)).trans_eq (by rw [frac_apply]; ring)
       _ = _ := (mul_sum ..).symm

lemma harmonic_interval (s : ℝ) (hs : 0 ≤ s) (hs' : s≤1) :
    ∃ K : ℝ, 0<K ∧ ∀ y : ℕ, 2≤y →
      ∑ d ∈ Icc y (2*y), frac s d ≤ K*(Real.log ((2*y:ℕ):ℝ))^(s-1) := by
  obtain ⟨C,hC,HC⟩ := harmonic_bound s hs
  refine ⟨4*(Real.log 4+4)*C,by positivity,?_⟩
  intro y hy
  let N := 2*y
  have hN : 2≤N := by dsimp [N]; omega
  have hY : (2:ℝ)≤y := by exact_mod_cast hy
  have hNcast : (N:ℝ)=2*y := by simp [N]
  have hlog : 0<Real.log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  have hYlog : Real.log (N:ℝ)≤2*Real.log y := by
    rw [hNcast,Real.log_mul (by norm_num) (by positivity)]
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) hY]
  have hrow (d : ℕ) (hd : d∈Icc y N) : frac s d*((y:ℝ)*Real.log N) ≤ 2*(fw s d*Real.log d) := by
    have hyd := (mem_Icc.mp hd).1
    have hd' : 0<(d:ℝ) := by exact_mod_cast (show 0<d by omega)
    have hleft : (y:ℝ)*Real.log N ≤ (d:ℝ)*(2*Real.log d) := by
      apply mul_le_mul (by exact_mod_cast hyd) _ hlog.le hd'.le
      exact hYlog.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by exact_mod_cast hyd)) (by norm_num))
    rw [frac_apply]
    calc _ = (fw s d / d)*((y:ℝ)*Real.log N) := rfl
         _ ≤ (fw s d / d)*((d:ℝ)*(2*Real.log d)) :=
               mul_le_mul_of_nonneg_left hleft (div_nonneg (fw_pos hs _) hd'.le)
         _ = _ := by field_simp <;> ring
  have hsub : Icc y N ⊆ Ioc 0 N := fun d hd => mem_Ioc.mpr ⟨by have := (mem_Icc.mp hd).1; omega,(mem_Icc.mp hd).2⟩
  have hall := sum_le_sum hrow
  rw [← sum_mul,← mul_sum] at hall
  have hpos (n : ℕ) (hn : n∈Ioc 0 N) : 0≤fw s n*Real.log n :=
    mul_nonneg (fw_pos hs _) (log_nonneg (by exact_mod_cast (mem_Ioc.mp hn).1))
  have h1 := sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hpos n hn)
  have H := log_weight s hs hs' N
  have h2 := mul_le_mul_of_nonneg_left (HC N hN) (show 0≤(Real.log 4+4)*N by positivity)
  have h3 : (∑ d ∈ Icc y N, frac s d)*((y:ℝ)*Real.log N) ≤ 2*((Real.log 4+4)*N*(C*(Real.log N)^s)) :=
    hall.trans (mul_le_mul_of_nonneg_left (h1.trans (H.trans h2)) (by norm_num))
  change _ ≤ _*(Real.log (N:ℝ))^(s-1)
  rw [Real.rpow_sub hlog,Real.rpow_one]
  apply (le_of_mul_le_mul_right ?_ (show 0<(y:ℝ)*Real.log N by positivity))
  apply h3.trans_eq
  rw [hNcast] at hlog ⊢; field_simp <;> ring

end
end Work692


namespace Work692
open Finset Filter Real
open scoped Classical BigOperators
noncomputable section

def momentConst (v : ℝ) := exp (|v| * OMALib.Mertens.mertens2NatConst)

lemma primeMoment {N : ℕ} (hN : 2≤N) {v : ℝ} (hv : -1≤v) :
    ∏ p ∈ N.primesLE, (1+v/p) ≤ momentConst v*(log (N:ℝ))^v := by
  have hM := OMALib.Mertens.abs_sum_inv_sub_log_log_le_nat N hN
  have hl : 0<log (N:ℝ) := log_pos (by exact_mod_cast (show 1<N by omega))
  calc _ ≤ ∏ p ∈ N.primesLE, exp (v/p) := by
           apply Finset.prod_le_prod
           · intro p h
             have hp : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE h).two_le
             have hh : -1≤v/(p:ℝ) := (le_div_iff₀ (by linarith)).mpr (by linarith)
             linarith
           · intro p _; linarith [add_one_le_exp (v/p)]
       _ = exp (v * ∑ p ∈ N.primesLE, (1:ℝ)/p) := by
           rw [← exp_sum,mul_sum]; congr 1; apply sum_congr rfl; intro p _; ring
       _ ≤ _ := by
           rw [momentConst,rpow_def_of_pos hl,←exp_add]
           apply exp_le_exp.mpr
           have b : v*((∑ p ∈ N.primesLE, (1:ℝ)/p)-log (log N)) ≤ |v| * OMALib.Mertens.mertens2NatConst := (le_abs_self (v*((∑ p ∈ N.primesLE, (1:ℝ)/p)-log (log N)))).trans
             (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hM (abs_nonneg v))
           linarith

def slab (y : ℕ) : Set ℕ := {x | ∃ d∈Icc y (2*y), d∣x}

private lemma cond {N d : ℕ} (hd : 0<d) (hdN : d≤N) :
    (1/(d:ℝ))*∏ p ∈ N.primesLE, factor d p (2/3) ≤
      frac (4/5) d * ∏ p ∈ N.primesLE, (1+(-(1/3:ℝ))/p) := by
  have hF : N.primesLE.filter (· ∣ d)=d.primeFactors := by
    ext p
    simp only [mem_filter,Nat.mem_primesLE,Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨_,hp⟩,h⟩; exact ⟨hp,h,hd.ne'⟩
    · rintro ⟨hp,h,_⟩; exact ⟨⟨(Nat.le_of_dvd hd h).trans hdN,hp⟩,h⟩
  have pw : (∏ p ∈ N.primesLE, (if p∣d then (4/5:ℝ) else 1))=(4/5:ℝ)^d.primeFactors.card := by
    rw [←prod_filter,hF,prod_const]
  have loc (p : ℕ) (hp : p∈N.primesLE) : factor d p (2/3) ≤
      (if p∣d then (4/5:ℝ) else 1)*(1+(-(1/3:ℝ))/p) := by
    have h : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
    dsimp [factor]
    split_ifs
    · field_simp; linarith
    · ring_nf; rfl
  calc _ ≤ (1/(d:ℝ))*∏ p ∈ N.primesLE,
             ((if p∣d then (4/5:ℝ) else 1)*(1+(-(1/3:ℝ))/p)) := by
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           apply Finset.prod_le_prod _ loc
           intro p hp
           have h : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).two_le
           dsimp [factor]; split_ifs
           · norm_num
           · have h' : (-(1/3:ℝ))/(p:ℝ) ≥ -1 := (le_div_iff₀ (by linarith)).mpr (by linarith)
             norm_num at *; linarith
       _ = _ := by rw [prod_mul_distrib,pw,frac_apply,fw_apply hd.ne']; ring

lemma bound_slab : ∃ C : ℝ, 0<C ∧ ∀ y : ℕ, 2≤y →
    boundSet (slab y) (C/(log ((2*y:ℕ):ℝ))^(1/60:ℝ)) := by
  obtain ⟨K,hK,HK⟩ := harmonic_interval (4/5) (by norm_num) (by norm_num)
  let C₁ := momentConst (1/2)
  let C₂ := momentConst (-(1/3))
  have p₁ : 0<C₁ := exp_pos _
  have p₂ : 0<C₂ := exp_pos _
  refine ⟨C₁+K*C₂,by positivity,?_⟩
  intro y hy
  let N := 2*y
  let P := N.primesLE
  let D := Icc y N
  let l := log (N:ℝ)
  have hN : 2≤N := by dsimp [N]; omega
  have hl : 0<l := log_pos (by exact_mod_cast (show 1<N by omega))
  let T := l^(31/60:ℝ)
  have pT : 0<T := rpow_pos_of_pos hl _
  have pr : ∀ p∈P,p.Prime := fun _ h => Nat.prime_of_mem_primesLE h
  have Hu := mean_row P pr 1 (by decide) (3/2)
  have Heq : (∏ p ∈ P, factor 1 p (3/2))=∏ p ∈ P, (1+(1/2:ℝ)/p) := by
    apply prod_congr rfl
    intro p hp; simp [factor,(pr p hp).not_dvd_one]; ring
  have Hlo := fun d (h : d∈D) => mean_row P pr d (show 0<d by have := (mem_Icc.mp h).1; omega) (2/3)
  have Hlo' := (Filter.eventually_all_finset D).mpr Hlo
  have M1 : (∏ p ∈ P, factor 1 p (3/2)) ≤ C₁*l^(1/2:ℝ) := by
    rw [Heq]; exact primeMoment hN (by norm_num)
  have M2 : (∑ d ∈ D, (1/(d:ℝ))*∏ p ∈ P, factor d p (2/3)) ≤
      (K*l^(4/5-1:ℝ))*(C₂*l^(-(1/3):ℝ)) := by
    calc _ ≤ ∑ d ∈ D, frac (4/5) d * ∏ p ∈ P, (1+(-(1/3:ℝ))/p) := by
             apply sum_le_sum; intro d h; obtain ⟨hd,hd'⟩ := mem_Icc.mp h; exact cond (by omega) hd'
         _ = _ := sum_mul .. |>.symm
         _ ≤ _ := by
             apply mul_le_mul (HK y hy) (primeMoment hN (by norm_num)) _ (by positivity)
             apply prod_nonneg; intro p hp
             have h : (2:ℝ)≤p := by exact_mod_cast (pr p hp).two_le
             have h' : (-1:ℝ)≤(-(1/3:ℝ))/(p:ℝ) := (le_div_iff₀ (by linarith)).mpr (by linarith)
             linarith
  have inv (x : ℕ) : wgt P (3/2) x*wgt P (2/3) x=1 := by
    dsimp [wgt]; rw [←prod_mul_distrib]
    apply prod_eq_one; intro p _; split_ifs <;> norm_num
  have major (x : ℕ) : ind (slab y) x ≤ row P 1 (3/2) x/T+T*∑ d ∈ D,row P d (2/3) x := by
    have sw : 0≤∑ d ∈ D,row P d (2/3) x := sum_nonneg fun d _ => r_nonneg (by norm_num) d x
    have rw1 : row P 1 (3/2) x=wgt P (3/2) x := by simp [row]
    rw [rw1]
    by_cases h : x∈slab y
    · obtain ⟨d,hd,dvd⟩ := h
      rw [show ind (slab y) x=1 by simp [ind,show x∈slab y from ⟨d,hd,dvd⟩]]
      by_cases big : T≤wgt P (3/2) x
      · have := (one_le_div pT).mpr big
        linarith [mul_nonneg pT.le sw]
      · have single := single_le_sum (s:=D) (f:=fun k=>row P k (2/3) x)
          (fun k _ => r_nonneg (by norm_num) k x) hd
        rw [row,if_pos dvd] at single
        have a := mul_le_mul_of_nonneg_right (le_of_not_ge big) (w_nonneg (P:=P) (by norm_num : (0:ℝ)≤2/3) x)
        have b := mul_le_mul_of_nonneg_left single pT.le
        linarith [inv x,div_nonneg (w_nonneg (P:=P) (by norm_num : (0:ℝ)≤3/2) x) pT.le]
    · simp only [ind,if_neg h]
      exact add_nonneg (div_nonneg (w_nonneg (by norm_num) _) pT.le) (mul_nonneg pT.le sw)
  filter_upwards [Hu,Hlo'] with M U V
  have hh := sum_le_sum (s:=range M.factorial) (fun x _ => major x)
  rw [sum_add_distrib,←sum_div,←mul_sum,sum_comm,U] at hh
  simp only [Nat.cast_one,div_one,one_mul] at hh
  rw [sum_congr rfl V,←sum_mul] at hh
  have b1 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right M1 (Nat.cast_nonneg M.factorial)) pT.le
  have b2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right M2 (Nat.cast_nonneg M.factorial)) pT.le
  apply hh.trans ((add_le_add b1 b2).trans_eq ?_)
  change C₁*l^(1/2:ℝ)*M.factorial/T+T*((K*l^(4/5-1:ℝ)*(C₂*l^(-(1/3):ℝ)))*M.factorial)=
    ((C₁+K*C₂)/l^(1/60:ℝ))*M.factorial
  have e1 : l^(1/2:ℝ)/T=l^(-(1/60):ℝ) := by
    dsimp [T]; rw [←rpow_sub hl]; norm_num
  have e2 : T*(l^(4/5-1:ℝ)*l^(-(1/3):ℝ))=l^(-(1/60):ℝ) := by
    dsimp [T]; rw [←rpow_add hl,←rpow_add hl]; norm_num
  have einv : l^(-(1/60):ℝ)=(l^(1/60:ℝ))⁻¹ := rpow_neg hl.le _
  linear_combination C₁*(M.factorial:ℝ)*(e1.trans einv) + K*C₂*(M.factorial:ℝ)*(e2.trans einv)

end
end Work692



noncomputable section
open Finset Filter Real Erdos859 Work692
open scoped Classical Topology
namespace PracticalUpper

def small (y t : ℕ) : Set ℕ := {n | t ≤ ∑ d ∈ Icc 1 y, if d ∣ n then d else 0}

lemma small_bound (y t : ℕ) (ht : 0<t) : boundSet (small y t) ((y:ℝ)/t) := by
  let D := Icc 1 y
  have hp : (0:ℝ)<t := by exact_mod_cast ht
  have means : ∀ᶠ N : ℕ in atTop, ∀ d∈D,
      ∑ n ∈ range N.factorial, (if d∣n then (1:ℝ) else 0) = (1/(d:ℝ))*N.factorial :=
    (eventually_all_finset D).mpr fun d hd => mean_dvd d (mem_Icc.mp hd).1
  filter_upwards [means] with N hN
  have hrow (n : ℕ) : ind (small y t) n * t ≤ ∑ d ∈ D, (d:ℝ)*(if d∣n then 1 else 0) := by
    by_cases hh : n ∈ small y t
    · rw [ind,if_pos hh,one_mul]
      change t ≤ ∑ d ∈ D, if d ∣ n then d else 0 at hh
      have hc : (t:ℝ) ≤ ∑ d ∈ D, if d ∣ n then (d:ℝ) else 0 := by exact_mod_cast hh
      simpa [mul_ite] using hc
    · rw [ind,if_neg hh,zero_mul]
      exact sum_nonneg (fun d _ => mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> norm_num))
  have h := sum_le_sum (s := range N.factorial) (fun n _ => hrow n)
  rw [←sum_mul,sum_comm] at h
  have hs (d) (hd : d∈D) : (∑ n ∈ range N.factorial, (d:ℝ)*(if d∣n then 1 else 0)) = N.factorial := by
    rw [←mul_sum,hN d hd]
    have hd' : 0 < (d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
    field_simp
  rw [sum_congr rfl hs] at h
  have hcard : D.card=y := by simp [D]
  simp only [sum_const,hcard,nsmul_eq_mul] at h
  exact (le_div_iff₀ hp).mpr h |>.trans_eq (by ring)

lemma cover {t j H : ℕ} (hj : j = Nat.log 2 t) :
    DivisorSumSet t ⊆ small (2^(j-H)) t ∪ ⋃ i∈Icc (j-H) j, slab (2^i) := by
  intro n hn
  obtain ⟨S,hS,ht⟩ := hn
  by_cases h : ∃ d∈S, 2^(j-H) ≤ d
  · obtain ⟨d,hd,hlo⟩ := h
    have dt : d≤t := ht ▸ single_le_sum (f:=id) (fun _ _ => Nat.zero_le _) hd
    have dp := Nat.pos_of_mem_divisors (hS hd)
    let i := Nat.log 2 d
    apply Or.inr
    apply Set.mem_iUnion₂.mpr
    refine ⟨i,mem_Icc.mpr ⟨(Nat.le_log_iff_pow_le (by decide) dp.ne').mpr hlo,?_⟩,?_⟩
    · rw [hj]; exact Nat.log_mono_right dt
    · exact ⟨d,mem_Icc.mpr ⟨Nat.pow_log_le_self _ dp.ne',by
        have := Nat.lt_pow_succ_log_self (by decide : 1<2) d
        simpa [i,pow_succ'] using this.le⟩,(Nat.mem_divisors.mp (hS hd)).1⟩
  · apply Or.inl
    have sub : S ⊆ Icc 1 (2^(j-H)) := fun d hd => mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors (hS hd),(lt_of_not_ge (fun hl => h ⟨d,hd,hl⟩)).le⟩
    change t ≤ _
    rw [ht]
    calc
      _ = ∑ d ∈ S, if d∣n then d else 0 := sum_congr rfl fun d hd => (if_pos (Nat.mem_divisors.mp (hS hd)).1).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset sub
end PracticalUpper

noncomputable section
open Finset Filter Real Work692 PracticalUpper
open scoped Classical Topology

theorem OMA.solution : OMA.R_Erdos859_erdos_859_variants_erdos_upper_lower_bounds_R1.H2 := by
  obtain ⟨C,hC,hslab⟩ := Work692.bound_slab
  have grow : Tendsto (fun t : ℕ => log (t:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have grow' := (tendsto_rpow_atTop (by norm_num : 0<(1/240:ℝ))).comp grow
  refine ⟨1/240,by norm_num,?_⟩
  filter_upwards [grow.eventually_ge_atTop 16,grow'.eventually_gt_atTop (1+6*C),
    eventually_ge_atTop (2:ℕ)] with t hl hlarge ht
  let L := log (t:ℝ)
  let R := L^(1/240:ℝ)
  let T := L^(1/120:ℝ)
  let H := ⌊T⌋₊+1
  let j := Nat.log 2 t
  let y := 2^(j-H)
  change 16≤L at hl
  change 1+6*C < R at hlarge
  have hl1 : 1≤L := by linarith
  have hlp : 0<L := by linarith
  have hT : 1≤T := one_le_rpow hl1 (by norm_num)
  have pT : 0<T := by linarith
  have pR : 0<R := rpow_pos_of_pos hlp _
  have hR : R*R=T := by dsimp [R,T]; rw [←rpow_add hlp]; norm_num
  have hTT : T*T=L^(1/60:ℝ) := by dsimp [T]; rw [←rpow_add hlp]; norm_num
  have Hhi : (H:ℝ) ≤ T+1 := by dsimp [H]; push_cast; linarith [Nat.floor_le pT.le]
  have Hlo : T ≤ (H:ℝ) := by simpa [H] using (Nat.lt_floor_add_one T).le
  have hL : L≤(j:ℝ)+1 := by
    have h := Nat.lt_pow_succ_log_self (by decide : 1<2) t
    have hh := log_le_log (show (0:ℝ)<t by exact_mod_cast (show 0<t by omega))
      (show (t:ℝ) ≤ (2:ℝ)^(j+1) by exact_mod_cast h.le)
    rw [log_pow] at hh
    push_cast at hh
    exact hh.trans (mul_le_of_le_one_right (by positivity) (by linarith [log_two_lt_d9]))
  have hTroot : T ≤ sqrt L := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
  have jH : 2*H ≤ j := by
    exact_mod_cast (show (2:ℝ)*H ≤ j by nlinarith [Real.sq_sqrt hlp.le,sq_nonneg (sqrt L-2)])
  have hbig {i : ℕ} (hi : i ∈ Icc (j-H) j) :
      Work692.boundSet (slab (2^i)) (2*C/(T*T)) := by
    obtain ⟨ha,hb⟩ := mem_Icc.mp hi
    have hi1 : 1 ≤ i := by dsimp [H] at *; omega
    have hip : 2≤2^i := Nat.pow_le_pow_right (by decide : 0<2) hi1
    have hlog : L ≤ 2*log ((2*2^i:ℕ):ℝ) := by
      have hj := Nat.lt_pow_succ_log_self (by decide : 1<2) t
      have hpow : j+1 ≤ (i+1)*2 := by omega
      have bound : (t:ℝ) ≤ (2:ℝ)^((i+1)*2) := by
        exact_mod_cast (hj.le.trans (Nat.pow_le_pow_right (by decide : 0<2) hpow))
      have hh := log_le_log (show (0:ℝ)<t by exact_mod_cast (show 0<t by omega)) bound
      change log (t:ℝ) ≤ _
      push_cast
      rw [← pow_succ',log_pow]
      rw [log_pow] at hh
      push_cast at hh ⊢
      linarith
    let z := log ((2*2^i:ℕ):ℝ)
    have zp : 0<z := by dsimp [z]; linarith
    have two : (2:ℝ)^(1/60:ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
    have q : T*T ≤ 2*z^(1/60:ℝ) := calc
      _ = L^(1/60:ℝ) := hTT
      _ ≤ (2*z)^(1/60:ℝ) := Real.rpow_le_rpow hlp.le hlog (by norm_num)
      _ = (2:ℝ)^(1/60:ℝ)*z^(1/60:ℝ) := Real.mul_rpow (by norm_num) zp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right two (by positivity)
    apply bound_mono Set.Subset.rfl _ (hslab _ hip)
    change C/z^(1/60:ℝ) ≤ _
    rw [div_le_div_iff₀ (rpow_pos_of_pos zp _) (mul_pos pT pT)]
    nlinarith only [mul_le_mul_of_nonneg_left q hC.le]
  have hfin := bound_union (small_bound y t (by omega)) (bound_iUnion (Icc (j-H) j)
    (fun i => slab (2^i)) _ (fun _ hi => hbig hi))
  have hd := density_bound (OMA.R_Erdos859_erdos_859_variants_erdos_upper_lower_bounds_R1.divisor_sum_density t)
    (bound_mono (PracticalUpper.cover (t:=t) (j:=j) (H:=H) rfl) le_rfl hfin)
  have hp : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hy : (y:ℝ)/t ≤ 1/T := by
    rw [div_le_div_iff₀ hp pT,one_mul]
    have hypos : 0 ≤ (y:ℝ) := Nat.cast_nonneg _
    calc (y:ℝ)*T ≤ (y:ℝ)*H := mul_le_mul_of_nonneg_left Hlo hypos
         _ ≤ (y:ℝ)*(2:ℝ)^H := by exact_mod_cast Nat.mul_le_mul_left y (Nat.lt_two_pow_self (n:=H)).le
         _ ≤ t := by
           exact_mod_cast (show y*2^H ≤ t by dsimp [y]; rw [← pow_add,Nat.sub_add_cancel (by omega)]; exact Nat.pow_log_le_self _ (by omega))
  have hc : ((Icc (j-H) j).card : ℝ) ≤ 3*T := by
    have hn : (Icc (j-H) j).card ≤ H+1 := by rw [Nat.card_Icc]; omega
    have hh : ((Icc (j-H) j).card:ℝ) ≤ (H:ℝ)+1 := by exact_mod_cast hn
    linarith
  have hs : (y:ℝ)/t + ((Icc (j-H) j).card:ℝ)*(2*C/(T*T)) ≤ (1+6*C)/T := calc
    _ ≤ 1/T+3*T*(2*C/(T*T)) := add_le_add hy (mul_le_mul_of_nonneg_right hc (by positivity))
    _ = _ := by field_simp; ring
  apply (hd.trans hs).trans_lt
  change (1+6*C)/T < 1/R
  rw [div_lt_div_iff₀ pT pR,one_mul,← hR]
  exact mul_lt_mul_of_pos_right hlarge pR
