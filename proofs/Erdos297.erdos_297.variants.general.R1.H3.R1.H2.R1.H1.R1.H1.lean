import OMAReductions.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1
import Mathlib
/-! Mertens estimates from @senamakel via @marcusbuffett’s merged Erdős 377 and 299 proofs. The square-divisor exceptional set and prime window are adapted from the latter. -/

section
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


end OMALib.Mertens
end

section
open Filter Finset Real Asymptotics
open scoped Topology BigOperators
open OMALib.Mertens
namespace Mass377
noncomputable abbrev S (x : ℝ) := ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1:ℝ)/p
lemma Cpos : 0 ≤ mertens1Const := by
  exact (abs_nonneg _).trans (abs_sum_log_div_sub_log_le_nat 2)
lemma Gdiff (m n : ℕ) (hm : 2 ≤ m) (hn : m ≤ n) :
    |mertensG n - mertensG m| ≤ (mertens1Const+1)*(1/log m-1/log n) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    calc |mertensG (n+1)-mertensG m| =
        |(mertensG (n+1)-mertensG n)+(mertensG n-mertensG m)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add (mertensG_step n (hm.trans hn)) ih
      _ = _ := by ring
lemma logTop : Tendsto (fun n : ℕ => log n) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
lemma natMertens : ∃ b : ℝ, Tendsto (fun n : ℕ => (∑ p ∈ Nat.primesLE n, (1:ℝ)/p) -
    log (log n)) atTop (𝓝 b) := by
  have hC : CauchySeq mertensG := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => (mertens1Const+1)/log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logTop
    obtain ⟨m,hm,he⟩ := ((eventually_ge_atTop 2).and (hlim.eventually_lt_const hε)).exists
    refine ⟨m,fun n hn => ?_⟩
    rw [Real.dist_eq]
    apply (Gdiff m n hm hn).trans_lt
    have hn' : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hp : 0≤(mertens1Const+1)*(1/log n) := mul_nonneg (by linarith [Cpos]) (by positivity [log_pos hn'])
    rw [mul_sub,←div_eq_mul_one_div]
    linarith
  obtain ⟨b,hb⟩ := cauchySeq_tendsto_of_complete hC
  let R (n : ℕ) := ((∑ p ∈ Nat.primesLE n, log p / p)-log n)/log n
  have hR : Tendsto R atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun n : ℕ => mertens1Const/log n) atTop (𝓝 0) from tendsto_const_nhds.div_atTop logTop)
    filter_upwards [logTop.eventually_gt_atTop 0] with n hn
    dsimp only [R]
    rw [Real.norm_eq_abs, abs_div,abs_of_pos hn]
    exact div_le_div_of_nonneg_right (abs_sum_log_div_sub_log_le_nat n) hn.le
  refine ⟨b,?_⟩
  simpa [R,mertensG] using hb.add hR
lemma realMertens : ∃ b : ℝ, Tendsto (fun x : ℝ => S x-log (log x)) atTop (𝓝 b) := by
  obtain ⟨b,hb⟩ := natMertens
  have he := (isEquivalent_nat_floor (R:=ℝ)).log tendsto_id
  have hz := tendsto_log_atTop.eventually_ne_atTop 0
  have ht := ((isEquivalent_iff_tendsto_one hz).1 he).log (by norm_num)
  have hfloor : Tendsto (fun x : ℝ => log (⌊x⌋₊:ℝ)) atTop atTop := logTop.comp tendsto_nat_floor_atTop
  have hdiff : Tendsto (fun x : ℝ => log (log (⌊x⌋₊:ℝ)) - log (log x)) atTop (𝓝 0) := by
    rw [Real.log_one] at ht
    apply ht.congr'
    filter_upwards [hz,hfloor.eventually_ne_atTop 0] with x hx hf
    exact log_div hf hx
  refine ⟨b,?_⟩
  have h := (hb.comp tendsto_nat_floor_atTop).add hdiff
  simpa [S,Function.comp_def,sub_add_sub_cancel] using h
end Mass377
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
noncomputable abbrev cutoff (N : ℕ) (c : ℝ) := (N:ℝ)^c
lemma cut_top {c : ℝ} (hc : 0<c) : Tendsto (fun N : ℕ => cutoff N c) atTop atTop :=
  (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
lemma prime_window (δ : ℝ) (hδ : 0<δ) : ∃ c : ℝ, 0<c ∧ c<1 ∧ ∀ᶠ N : ℕ in atTop,
    (∑ p ∈ Nat.primesLE N \ Nat.primesLE ⌊cutoff N c⌋₊, (1:ℝ)/p) ≤ δ := by
  let c := exp (-δ/2)
  have hc : 0<c := exp_pos _
  have hc1 : c < 1 := exp_lt_one_iff.mpr (by linarith)
  obtain ⟨b,hb⟩ := Mass377.realMertens
  have hN := hb.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hY := hb.comp (cut_top hc)
  have lim := (hN.sub hY).sub (tendsto_const_nhds (x := log c))
  have goal : Tendsto (fun N : ℕ => Mass377.S N - Mass377.S (cutoff N c)) atTop (𝓝 (-log c)) := by
    simp only [sub_self,zero_sub] at lim
    apply lim.congr'
    filter_upwards [eventually_ge_atTop 2] with N h
    have hr : (1:ℝ) < N := by exact_mod_cast (show 1<N by omega)
    dsimp only [Function.comp_apply,Function.comp_def, Pi.sub_apply, cutoff]
    rw [Real.log_rpow (by linarith),Real.log_mul hc.ne' (Real.log_pos hr).ne']
    ring
  have he : -log c < δ := by dsimp [c]; rw [log_exp]; linarith
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [goal.eventually_lt_const he,eventually_ge_atTop 1] with N h hN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hy : cutoff N c ≤ N := by simpa using rpow_le_rpow_of_exponent_le hNr hc1.le
  have sub : Nat.primesLE ⌊cutoff N c⌋₊ ⊆ Nat.primesLE N := by
    intro p hp
    obtain ⟨hle,hpr⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hle.trans (Nat.floor_le_of_le hy),hpr⟩
  have eq := sum_sdiff sub (f:=fun p : ℕ => (1:ℝ)/p)
  simp only [Mass377.S,Nat.floor_natCast] at h
  linarith

lemma mult_union (N : ℕ) (D : Finset ℕ) :
    (((D.biUnion fun d => (Ioc 0 N).filter (d ∣ ·)).card):ℝ) ≤
      N * ∑ d ∈ D, (1:ℝ)/d := by
  calc _ ≤ ((∑ d ∈ D, ((Ioc 0 N).filter (d ∣ ·)).card : ℕ):ℝ) := by exact_mod_cast card_biUnion_le
       _ = ∑ d ∈ D, ((N/d:ℕ):ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
       _ ≤ ∑ d ∈ D, (N:ℝ)/d := sum_le_sum fun _ _ => Nat.cast_div_le
       _ = _ := by simp [mul_sum, div_eq_mul_inv]

lemma square_tail (δ : ℝ) (hδ : 0<δ) : ∃ A : ℕ, ∀ N : ℕ,
    (∑ a ∈ Icc A N, (1:ℝ)/(a:ℝ)^2) ≤ δ := by
  have hs : Summable (fun a : ℕ => (1:ℝ)/(a:ℝ)^2) := by
    simpa only [one_div] using (Real.summable_nat_pow_inv.mpr (by decide : 1<2))
  let s := ∑' a : ℕ, (1:ℝ)/(a:ℝ)^2
  obtain ⟨A,hA⟩ := (hs.hasSum.tendsto_sum_nat.eventually_const_lt (show s-δ < s by linarith)).exists
  refine ⟨A,fun N => ?_⟩
  have hd : Disjoint (range A) (Icc A N) := by
    rw [Finset.disjoint_left]; intro x hx hy
    exact (mem_range.mp hx).not_ge (mem_Icc.mp hy).1
  have h := hs.sum_le_tsum (range A ∪ Icc A N) (fun a _ => by positivity)
  rw [sum_union hd] at h
  change _ ≤ s at h
  linarith

lemma square_mult (N A : ℕ) :
    ((((Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)).card):ℝ) ≤
      N * ∑ a ∈ Icc A N, (1:ℝ)/(a:ℝ)^2 := by
  calc _ ≤ ((∑ a ∈ Icc A N, ((Ioc 0 N).filter (a^2 ∣ ·)).card:ℕ):ℝ) := by exact_mod_cast card_biUnion_le
       _ = ∑ a ∈ Icc A N, ((N/a^2:ℕ):ℝ) := by simp [Nat.Ioc_filter_dvd_card_eq_div]
       _ ≤ ∑ a ∈ Icc A N, (N:ℝ)/(a^2:ℕ) := sum_le_sum fun _ _ => Nat.cast_div_le
       _ = _ := by simp [mul_sum, div_eq_mul_inv]
end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299

lemma smooth (δ : ℝ) (hδ : 0<δ) : ∃ c : ℝ, 0<c ∧ c<1 ∧ ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ,
    (E.card:ℝ) ≤ 2*δ*N ∧ ∀ n ∈ Ioc 0 N, n ∉ E → ∀ q : ℕ, IsPrimePow q → q ∣ n →
    (q:ℝ) ≤ cutoff N c := by
  classical
  obtain ⟨c,hc,hc1,hwin⟩ := prime_window δ hδ
  obtain ⟨A,hA⟩ := square_tail δ hδ
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [hwin,(cut_top hc).eventually_ge_atTop ((A:ℝ)^3),
    eventually_ge_atTop 1] with N hwin hcut hN
  let P := Nat.primesLE N \ Nat.primesLE ⌊cutoff N c⌋₊
  let U := P.biUnion fun p => (Ioc 0 N).filter (p ∣ ·)
  let V := (Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)
  have hd1 := (mult_union N P).trans (mul_le_mul_of_nonneg_left hwin (Nat.cast_nonneg N))
  have hd2 := (square_mult N A).trans (mul_le_mul_of_nonneg_left (hA N) (Nat.cast_nonneg N))
  refine ⟨U ∪ V, ?_, fun n hn hex q hq hqn => ?_⟩
  · have h : ((U ∪ V).card:ℝ) ≤ U.card + V.card := by exact_mod_cast card_union_le U V
    change (U.card:ℝ) ≤ _ at hd1
    change (V.card:ℝ) ≤ _ at hd2
    linarith
  apply le_of_not_gt
  intro hgt
  have hqbig := hgt
  have hqN := (Nat.le_of_dvd (mem_Ioc.mp hn).1 hqn).trans (mem_Ioc.mp hn).2
  obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff q).mp hq
  by_cases hk1 : k=1
  · subst k
    simp only [pow_one] at *
    apply hex (mem_union_left _ (mem_biUnion.mpr ?_))
    refine ⟨p,mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hqN,hp⟩,?_⟩,mem_filter.mpr ⟨hn,hqn⟩⟩
    intro hh
    have hl := (Nat.mem_primesLE.mp hh).1
    exact hqbig.not_ge ((Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) c)).mp hl)
  · let a := p^(k/2)
    have ha2 : a^2 ∣ p^k := by
      dsimp [a]; rw [← pow_mul]; exact pow_dvd_pow p (by omega)
    have h3 : p^k ≤ a^3 := by
      dsimp [a]; rw [← pow_mul]; exact Nat.pow_le_pow_right hp.pos (by omega)
    have haA : A ≤ a := by
      by_contra! h
      have : a^3 ≤ A^3 := Nat.pow_le_pow_left h.le 3
      have hh : ((p^k:ℕ):ℝ) ≤ (A:ℝ)^3 := by exact_mod_cast h3.trans this
      linarith
    have haN : a ≤ N := (Nat.le_of_dvd (mem_Ioc.mp hn).1 ((dvd_pow_self a (by decide : 2≠0)).trans (ha2.trans hqn))).trans (mem_Ioc.mp hn).2
    exact hex (mem_union_right _ (mem_biUnion.mpr ⟨a,mem_Icc.mpr ⟨haA,haN⟩,
      mem_filter.mpr ⟨hn,ha2.trans hqn⟩⟩))


end Regular299
end

namespace OMA.DenominatorReserve
open Finset Real Filter
open scoped Classical Topology

def J (B : ℕ) := (Icc 1 B).lcm id

noncomputable def reserve (ε : ℝ) (K i : ℕ) := (Icc 1 (i*i)).filter fun n => IsPrimePow i ∧ i∣n ∧
  Nat.Coprime i (n/i) ∧ (i:ℝ)^ε ≤ (n/i:ℕ) ∧ ((n/i:ℕ):ℝ) ≤ 2*(i:ℝ)^ε ∧ ¬ K ∣ n

lemma member_dvd {v B : ℕ} (hv : 0<v) (hB : v≤B) : v ∣ J B :=
  Finset.dvd_lcm (f:=id) (mem_Icc.mpr ⟨hv,hB⟩)

lemma Jpos (B : ℕ) : 0 < J B := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr
  fun p hp => (Nat.ne_of_gt (mem_Icc.mp hp).1 : p ≠ 0))

lemma smooth_dvd {n B : ℕ} (h : ∀ q : ℕ, IsPrimePow q → q ∣ n → q ≤ B) : n ∣ J B := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd ..).mpr
  intro p k hp hd
  rcases k.eq_zero_or_pos with rfl|hk
  · simp
  · exact member_dvd (pow_pos hp.pos _) (h _ (hp.isPrimePow.pow hk.ne') hd)

lemma reserve_disjoint {ε : ℝ} (hε : ε < 1/2) {K i j : ℕ} (hi : 16 ≤ i) (hij : i < j) :
    Disjoint (reserve ε K i) (reserve ε K j) := by
  rw [Finset.disjoint_left]
  intro n hni hnj
  obtain ⟨hin,_,hd,hcop,_,hup,_⟩ := mem_filter.mp hni
  obtain ⟨_,hpj,hdj,_⟩ := mem_filter.mp hnj
  have hn := (mem_Icc.mp hin).1
  have hh := (hcop.isPrimePow_dvd_mul hpj).mp
    (show j ∣ i*(n/i) by rwa [Nat.mul_div_cancel' hd])
  have hir : (16:ℝ) ≤ i := by exact_mod_cast hi
  have sqrt4 : 4 ≤ √(i:ℝ) := by rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have hsqrt : (i:ℝ)^ε ≤ √(i:ℝ) := by
    rw [Real.sqrt_eq_rpow]; exact rpow_le_rpow_of_exponent_le (by linarith) hε.le
  have strict : (n/i:ℕ) < i := by
    have : ((n/i:ℕ):ℝ) < i := by
      nlinarith [Real.sq_sqrt (Nat.cast_nonneg i),
        mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0:ℝ)≤2)]
    exact_mod_cast this
  rcases hh with h | h
  · exact hij.not_ge (Nat.le_of_dvd (by omega) h)
  · have p : 0<n/i := Nat.div_pos (Nat.le_of_dvd hn hd) (by omega)
    exact (show ¬ j ≤ n/i by omega) (Nat.le_of_dvd p h)

lemma small_scale {s η : ℝ} (hs : s<1) (hη : 0<η) :
    ∀ᶠ N : ℕ in atTop, 2*(N:ℝ)^s ≤ η*N := by
  have ht := ((tendsto_rpow_neg_atTop (sub_pos.mpr hs)).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_lt_const (show 0<η/2 by positivity)
  filter_upwards [ht,eventually_ge_atTop 1] with N h hN
  change (N:ℝ)^(-(1-s)) < η/2 at h
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have eq : (N:ℝ)^s = (N:ℝ)^(-(1-s))*N := by
    conv_rhs => rhs; rw [← Real.rpow_one (N:ℝ)]
    rw [← rpow_add hn]; congr 1; ring
  rw [eq]; nlinarith only [mul_le_mul_of_nonneg_right h.le hn.le]

lemma reserve_small {c ε : ℝ} (hε : 0<ε) {N i K : ℕ} (hN : 0<N) (hi : i≤⌊(N:ℝ)^c⌋₊)
    {n : ℕ} (hn : n ∈ reserve ε K i) : (n:ℝ) ≤ 2*(N:ℝ)^(c*(1+ε)) := by
  obtain ⟨_,_,hd,_,_,hup,_⟩ := mem_filter.mp hn
  have hcast : (n:ℝ) = (i:ℝ)*((n/i:ℕ):ℝ) := by exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hbound : (i:ℝ) ≤ (N:ℝ)^c := (Nat.le_floor_iff (rpow_nonneg (Nat.cast_nonneg _) _)).mp hi
  calc
    _ = _ := hcast
    _ ≤ (N:ℝ)^c*(2*((N:ℝ)^c)^ε) := mul_le_mul hbound
      (hup.trans (mul_le_mul_of_nonneg_left (rpow_le_rpow (Nat.cast_nonneg _) hbound hε.le) (by norm_num)))
      (by positivity) (by positivity)
    _ = _ := by
      rw [← rpow_mul (Nat.cast_nonneg N), mul_add,mul_one]
      rw [rpow_add (Nat.cast_pos.mpr hN)]; ring

end OMA.DenominatorReserve

open Filter Finset Real OMA.DenominatorReserve
open scoped Classical Topology

theorem OMA.solution : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1_H1_R1.H1 := by
  classical
  intro x _ δ hδ
  let η := min (δ/8) (1/8)
  have hη : 0<η := lt_min (by positivity) (by norm_num)
  have hη1 : η≤1 := (min_le_right ..).trans (by norm_num)
  obtain ⟨c,hc,hc1,sm⟩ := Regular299.smooth η hη
  let ε := (1-c)/4
  have hε : 0<ε := by dsimp [ε]; linarith
  have hε2 : ε<1/2 := by dsimp [ε]; linarith
  have hs : c*(1+ε)<1 := by dsimp [ε]; nlinarith [sq_nonneg (1-c)]
  refine ⟨ε,hε,hε2,?_⟩
  intro L₀
  let L := max (max L₀ 16) ⌈1/η⌉₊
  have hL : 16 ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  have hL' : ⌈1/η⌉₊ ≤ L := le_max_right _ _
  have hKL : L ≤ J L := Nat.le_of_dvd (Jpos _) (member_dvd (by omega) le_rfl)
  have hK : 1/η ≤ (J L : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hL'.trans hKL)
  have hK' : 1 / (J L : ℝ) ≤ η := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (Jpos L))).mpr
    have := (div_le_iff₀ hη).mp hK
    linarith
  refine ⟨L,(le_max_left _ _).trans (le_max_left _ _),?_⟩
  have Btop := tendsto_nat_floor_atTop.comp (Regular299.cut_top hc)
  filter_upwards [sm, small_scale hs hη,Btop.eventually_ge_atTop (max L x.den),
    eventually_ge_atTop 1] with N ⟨E,ec,smooth⟩ sc bbig hN
  let B := ⌊(N:ℝ)^c⌋₊
  change max L x.den ≤ B at bbig
  let V := (Ioc 0 N).filter (J L ∣ ·)
  let W := Icc 1 ⌊η*N⌋₊
  let T := Icc 1 N
  let U := T \ (E ∪ V ∪ W)
  refine ⟨B,(le_max_left ..).trans bbig,U,sdiff_subset,?_,
    member_dvd x.den_pos ((le_max_right ..).trans bbig),?_,?_,?_⟩
  · have sub : T \ U ⊆ E ∪ V ∪ W := by
      intro n hn
      obtain ⟨ht,hu⟩ := mem_sdiff.mp hn
      exact of_not_not (fun h => hu (mem_sdiff.mpr ⟨ht,h⟩))
    have card : (T \ U).card ≤ E.card + V.card + W.card := (card_le_card sub).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    have hV : (V.card : ℝ) ≤ η*N := by
      change (((Ioc 0 N).filter (J L ∣ ·)).card : ℝ) ≤ _
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      exact (Nat.cast_div_le).trans (by simpa [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_right hK' (Nat.cast_nonneg N))
    have hW : (W.card : ℝ) ≤ η*N := by simpa [W] using Nat.floor_le (mul_nonneg hη.le (Nat.cast_nonneg N))
    have h := mul_le_mul_of_nonneg_right (min_le_left (δ/8) (1/8:ℝ)) (Nat.cast_nonneg N)
    change η*N ≤ _ at h
    have cc : ((T \ U).card:ℝ) ≤ E.card + V.card + W.card := by exact_mod_cast card
    linarith
  · intro u hu
    obtain ⟨ht,hrest⟩ := mem_sdiff.mp hu
    have hu' := mem_Icc.mp ht
    have huN : u∈Ioc 0 N := mem_Ioc.mpr hu'
    have hE : u∉E := fun hm => hrest (mem_union_left _ (mem_union_left _ hm))
    exact ⟨smooth_dvd (fun q hp hd => Nat.le_floor (smooth u huN hE q hp hd)),
      fun hd => hrest (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨huN,hd⟩)))⟩
  · intro i hi
    have loc {n : ℕ} (hn : n∈reserve ε (J L) i) : n∈W := mem_Icc.mpr
      ⟨(mem_Icc.mp (mem_filter.mp hn).1).1,Nat.le_floor ((reserve_small hε hN (mem_Ioc.mp hi).2 hn).trans sc)⟩
    refine ⟨fun n hn => ?_,Finset.disjoint_left.mpr (fun n hu hn => (mem_sdiff.mp hu).2
      (mem_union_right _ (loc hn)))⟩
    obtain ⟨p,q⟩ := mem_Icc.mp (loc hn)
    exact mem_Icc.mpr ⟨p,q.trans (Nat.floor_le_of_le (by simpa using mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg N)))⟩
  · intro i hi j _ hij
    exact reserve_disjoint hε2 (hL.trans (mem_Ioc.mp hi).1.le) hij
