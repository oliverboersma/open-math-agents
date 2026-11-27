import OMAReductions.R_Erdos1100_erdos_1100_variants_normal_order_R1
import Mathlib

/-!
The Mertens estimates are adapted from @marcusbuffett's merged Erdős 377 proof,
which credits @senamakel for the first Mertens estimate and bounded successive
errors. The variance estimate and square-divisor bounds are from our Erdős 299
regularity proof. Here we use them to prove the Hardy–Ramanujan upper normal
order for the number of prime factors counted with multiplicity. Outside an
arbitrarily sparse union of multiples of squares the excess over the number
of distinct factors is bounded independently of the integer.
-/

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
end Mass377
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
noncomputable abbrev mass (P : Finset ℕ) := ∑ p ∈ P, (1:ℝ)/p
def cnt (P : Finset ℕ) (n : ℕ) := (P.filter (· ∣ n)).card
def hit (p n : ℕ) : ℝ := if p ∣ n then 1 else 0
lemma sum_hit (N p : ℕ) : ∑ n ∈ Ioc 0 N, hit p n = (N/p:ℕ) := by
  simp [hit, ← Nat.Ioc_filter_dvd_card_eq_div]
lemma cnt_sum (P : Finset ℕ) (n : ℕ) : (cnt P n : ℝ) = ∑ p ∈ P, hit p n := by
  simp [cnt,hit]
lemma first (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    N*mass P - P.card ≤ ∑ n ∈ Ioc 0 N, (cnt P n:ℝ) := by
  simp_rw [cnt_sum]
  rw [sum_comm]
  simp_rw [sum_hit]
  calc _ = ∑ p ∈ P, ((N:ℝ)/p-1) := by simp [mass,mul_sum,sum_sub_distrib,div_eq_mul_inv]
       _ ≤ _ := sum_le_sum fun p hp => OMALib.Mertens.real_div_sub_one_le_nat_div N p (hP p hp).pos

lemma pair_sum (N p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ∑ n ∈ Ioc 0 N, hit p n * hit q n ≤
      (N:ℝ)*((1/(p:ℝ))*(1/q)) + (if p=q then (N:ℝ)/p else 0) := by
  by_cases he : p=q
  · subst q
    simp only [if_pos rfl]
    have h : ∀ n, hit p n * hit p n = hit p n := fun n => by unfold hit; split_ifs <;> norm_num
    simp_rw [h,sum_hit]
    exact (Nat.cast_div_le (α:=ℝ)).trans (le_add_of_nonneg_left (by positivity))
  · have hc := (Nat.coprime_primes hp hq).mpr he
    have h (n) : hit p n * hit q n = hit (p*q) n := by
      have eq : p*q ∣ n ↔ p∣n ∧ q∣n := ⟨fun h => ⟨(dvd_mul_right p q).trans h,(dvd_mul_left q p).trans h⟩, fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
      simp only [hit,eq]
      split_ifs <;> simp_all
    simp_rw [h,sum_hit,if_neg he,add_zero]
    calc _ ≤ (N:ℝ)/(p*q:ℕ) := Nat.cast_div_le
         _ = _ := by push_cast; ring

lemma second (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∑ n ∈ Ioc 0 N, (cnt P n:ℝ)^2 ≤ (N:ℝ) * (mass P)^2 + N * mass P := by
  have eq (n) : (cnt P n:ℝ)^2 = ∑ p ∈ P, ∑ q ∈ P, hit p n * hit q n := by
    rw [cnt_sum,pow_two,sum_mul]
    exact sum_congr rfl fun p _ => mul_sum ..
  simp_rw [eq]
  rw [sum_comm]
  simp_rw [sum_comm (s := Ioc 0 N) (t := P)]
  calc _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((N:ℝ)*((1/(p:ℝ))*(1/q)) + (if p=q then (N:ℝ)/p else 0)) :=
            sum_le_sum fun p hp => sum_le_sum fun q hq => pair_sum N p q (hP p hp) (hP q hq)
       _ = _ := by
         simp only [sum_add_distrib, ←mul_sum, ←sum_mul, sum_ite_eq, mass]
         simp only [sum_ite_mem, inter_self]
         simp [mul_sum, sum_mul, pow_two, mul_assoc, div_eq_mul_inv]

lemma variance (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N) :
    ∑ n ∈ Ioc 0 N, ((cnt P n:ℝ)-mass P)^2 ≤ 3*N*mass P := by
  have hm : 0 ≤ mass P := sum_nonneg fun _ _ => by positivity
  have e (n) : ((cnt P n:ℝ)-mass P)^2 =
      (cnt P n:ℝ)^2 - 2*mass P*(cnt P n:ℝ) + (mass P)^2 := by ring
  simp_rw [e]
  rw [sum_add_distrib,sum_sub_distrib,←mul_sum]
  simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  have hcr : (P.card:ℝ) ≤ N := by exact_mod_cast hc
  nlinarith only [first P N hP,second P N hP,
    mul_nonneg hm (sub_nonneg.mpr (first P N hP)), mul_nonneg hm (sub_nonneg.mpr hcr)]

lemma cheb (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    (((Ioc 0 N).filter (fun n => t ≤ |(cnt P n:ℝ)-mass P|)).card:ℝ)*t^2 ≤ 3*N*mass P := by
  classical
  let E := (Ioc 0 N).filter (fun n => t ≤ |(cnt P n:ℝ)-mass P|)
  calc (E.card:ℝ)*t^2 = ∑ _n ∈ E, t^2 := by simp
         _ ≤ ∑ n ∈ E, ((cnt P n:ℝ)-mass P)^2 := sum_le_sum fun n hn => by
           have h := (mem_filter.mp hn).2
           simpa using (sq_le_sq' (by linarith [abs_nonneg ((cnt P n:ℝ)-mass P)] : -|(cnt P n:ℝ)-mass P| ≤ t) h)
         _ ≤ _ := (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)).trans (variance P N hP hc)
end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
lemma bad_count (P : Finset ℕ) (N : ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hc : P.card ≤ N)
    (δ t : ℝ) (ht : 0 < t) (hd : 3*mass P ≤ δ*t^2) :
    ∃ E : Finset ℕ, (E.card:ℝ) ≤ δ*N ∧
      ∀ n ∈ Ioc 0 N, n ∉ E → |(cnt P n:ℝ)-mass P| < t := by
  classical
  let E := (Ioc 0 N).filter fun n => t ≤ |(cnt P n:ℝ)-mass P|
  refine ⟨E, (le_of_mul_le_mul_right ?_ (sq_pos_of_pos ht)), fun n hn he => ?_⟩
  · calc (E.card:ℝ)*t^2 ≤ 3*N*mass P := cheb P N hP hc t ht.le
         _ ≤ (δ*N)*t^2 := by nlinarith only [mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg N)]
  · exact lt_of_not_ge (fun h => he (mem_filter.mpr ⟨hn,h⟩))

lemma primes_card (N : ℕ) : (Nat.primesLE N).card ≤ N := by
  calc _ ≤ (Ioc 0 N).card := card_le_card fun p h => by
          obtain ⟨hle, hp⟩ := Nat.mem_primesLE.mp h
          exact mem_Ioc.mpr ⟨hp.pos,hle⟩
       _ = _ := by simp

noncomputable abbrev w (N : ℕ) := log (log N)
lemma wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp Mass377.logTop

end Regular299
end

section
open Finset Real Filter
open scoped BigOperators Topology
namespace Regular299
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

lemma small (δ : ℝ) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop, ∃ E : Finset ℕ,
    (E.card:ℝ) ≤ 2*δ*N ∧ ∀ n : ℕ, n ∉ E → 0<n ∧ (N:ℝ)^(1-1/w N) ≤ n := by
  have hg := (tendsto_exp_div_pow_atTop 1).comp wtop
  filter_upwards [hg.eventually_gt_atTop (-log δ), Mass377.logTop.eventually_gt_atTop 0,
    eventually_ge_atTop 1, (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (1/δ)] with N hh hl hN hbig
  change -log δ < exp (w N)/(w N)^1 at hh
  rw [pow_one, show exp (w N) = log N from exp_log hl] at hh
  have hNr : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have h1 := (div_le_iff₀ hδ).mp hbig
  let E := range (⌊δ*N⌋₊+1)
  refine ⟨E,?_,fun n hn => ?_⟩
  · simp only [E,card_range,Nat.cast_add,Nat.cast_one]
    have hf := Nat.floor_le (mul_nonneg hδ.le hNr.le)
    nlinarith
  · have hfn : ⌊δ*N⌋₊ < n := by simpa [E, Nat.succ_le_iff] using hn
    have hsmall : (N:ℝ)^(1-1/w N) ≤ δ*N := by
      rw [Real.rpow_def_of_pos hNr, show log (N:ℝ)*(1-1/w N) = log N + -(log N/w N) by ring,exp_add,exp_log hNr]
      have he : exp (-(log N/w N)) ≤ δ := by rw [←Real.exp_log hδ]; exact exp_le_exp.mpr (by linarith)
      linarith only [mul_le_mul_of_nonneg_left he hNr.le]
    exact ⟨by omega,hsmall.trans (Nat.lt_of_floor_lt hfn).le⟩

end Regular299
end

section
open Finset Real Filter ArithmeticFunction
open scoped BigOperators Topology
open Regular299
namespace Omega1100

lemma distinct_upper (η δ : ℝ) (hη : 0<η) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop,
    ∃ E : Finset ℕ, (E.card:ℝ) ≤ δ*N ∧ ∀ n ∈ Ioc 0 N, n ∉ E →
      (n.primeFactors.card:ℝ) ≤ (1+η)*w N := by
  obtain ⟨b,hb⟩ := Mass377.natMertens
  let t := η/2
  have ht : 0<t := by dsimp [t]; positivity
  filter_upwards [hb.eventually_lt_const (show b < b+1 by linarith),
    wtop.eventually_gt_atTop (|b|+1),wtop.eventually_gt_atTop ((|b|+1)/t),
    wtop.eventually_gt_atTop (6/(δ*t^2))] with N hu hw hw₁ hw₂
  let P := Nat.primesLE N
  change mass P - w N < b+1 at hu
  have hm : mass P ≤ 2*w N := by linarith [le_abs_self b]
  have hw0 : 0<w N := by linarith [abs_nonneg b]
  have hh := (div_lt_iff₀ (by positivity : 0<δ*t^2)).mp hw₂
  have h1 := (div_lt_iff₀ ht).mp hw₁
  obtain ⟨E,hE,he⟩ := bad_count P N (fun p hp => (Nat.mem_primesLE.mp hp).2) (primes_card N)
    δ (t*w N) (by positivity) (by nlinarith only [hm,mul_lt_mul_of_pos_right hh hw0])
  refine ⟨E,hE,fun n hn hx => ?_⟩
  have hn' := mem_Ioc.mp hn
  have eq : P.filter (· ∣ n) = n.primeFactors := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE,Nat.mem_primeFactors,P]
    exact ⟨fun h => ⟨h.1.2,h.2,hn'.1.ne'⟩,fun h => ⟨⟨(Nat.le_of_dvd hn'.1 h.2.1).trans hn'.2,h.1⟩,h.2.1⟩⟩
  have h := (abs_lt.mp (he n hn hx)).2
  simp only [cnt,eq] at h
  dsimp [t] at h h1
  linarith [le_abs_self b]

lemma bounded_excess (δ : ℝ) (hδ : 0<δ) : ∃ M : ℕ, ∀ N : ℕ, ∃ E : Finset ℕ,
    (E.card:ℝ) ≤ δ*N ∧ ∀ n ∈ Ioc 0 N, n ∉ E → cardFactors n ≤ n.primeFactors.card + M := by
  classical
  obtain ⟨A,hA⟩ := square_tail δ hδ
  let M := ∑ b ∈ range A, 2 * cardFactors b
  refine ⟨M,fun N => ?_⟩
  let E := (Icc A N).biUnion fun a => (Ioc 0 N).filter (a^2 ∣ ·)
  have hc := (square_mult N A).trans (mul_le_mul_of_nonneg_left (hA N) (Nat.cast_nonneg N))
  refine ⟨E,by simpa [E,mul_comm] using hc,fun n hn he => ?_⟩
  obtain ⟨hn0,hnN⟩ := mem_Ioc.mp hn
  obtain ⟨a,b,ha,hb,eq,sf⟩ := Nat.sq_mul_squarefree_of_pos hn0
  have dvd : b^2 ∣ n := ⟨a,eq.symm⟩
  have bd : b ≤ N := (Nat.le_of_dvd hn0 ((dvd_pow_self b (by decide : 2≠0)).trans dvd)).trans hnN
  have hbA : b < A := lt_of_not_ge (fun h => he (mem_biUnion.mpr ⟨b,mem_Icc.mpr ⟨h,bd⟩, mem_filter.mpr ⟨hn,dvd⟩⟩))
  have hm : 2*cardFactors b ≤ M := single_le_sum (f:=fun j => 2*cardFactors j) (fun _ _ => Nat.zero_le _) (mem_range.mpr hbA)
  have eq1 : cardFactors n = 2*cardFactors b + cardFactors a := by
    rw [←eq,cardFactors_mul (pow_ne_zero _ hb.ne') ha.ne',cardFactors_pow]
  have eq2 : cardFactors a = a.primeFactors.card := by
    rw [cardFactors_apply,←Nat.toFinset_factors]
    exact (List.toFinset_card_of_nodup sf.nodup_primeFactorsList).symm
  have hsub := card_le_card (Nat.primeFactors_mono (show a∣n from eq ▸ dvd_mul_left a (b^2)) hn0.ne')
  omega

lemma bad_count_final (η ε : ℝ) (hη : 0<η) (hε : 0<ε) : ∀ᶠ N : ℕ in atTop,
    (((range N).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+η)*w n)).card:ℝ) ≤ ε*N := by
  classical
  let δ := ε/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨M,hM⟩ := bounded_excess δ hδ
  filter_upwards [distinct_upper (η/2) δ (by positivity) hδ,small δ hδ,
    wtop.eventually_gt_atTop (2*((M:ℝ)+(1+η)*Real.log 2)/η),
    wtop.eventually_gt_atTop 2, Mass377.logTop.eventually_gt_atTop 0, eventually_gt_atTop 0]
    with N hd hs hslack hw hl hN
  obtain ⟨E,hE,ee⟩ := hd
  obtain ⟨S,hS,ss⟩ := hs
  obtain ⟨T,hT,tt⟩ := hM N
  have sub : (range N).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+η)*w n) ⊆ E∪S∪T := by
    intro n hn
    obtain ⟨hnN,hbad⟩ := mem_filter.mp hn
    by_contra h
    simp only [mem_union,not_or] at h
    obtain ⟨hn0,hscale⟩ := ss n h.1.2
    have hi : n ∈ Ioc 0 N := mem_Ioc.mpr ⟨hn0,(mem_range.mp hnN).le⟩
    have ho := ee n hi h.1.1
    have ht : (cardFactors n:ℝ) ≤ n.primeFactors.card + (M:ℝ) := by exact_mod_cast tt n hi h.2
    have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
    have hlog := log_le_log (rpow_pos_of_pos hNr _) hscale
    rw [log_rpow hNr] at hlog
    have hw' : 1/w N ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hw.le
    have hlow : log (N:ℝ)/2 ≤ Real.log n := by nlinarith only [hlog,mul_le_mul_of_nonneg_right hw' hl.le]
    have hlow2 := log_le_log (div_pos hl (by norm_num : (0:ℝ)<2)) hlow
    rw [log_div hl.ne' (by norm_num : (2:ℝ)≠0)] at hlow2
    change w N - Real.log 2 ≤ w n at hlow2
    have hsl := (div_lt_iff₀ hη).mp hslack
    apply hbad
    nlinarith only [ht,ho,hsl,mul_le_mul_of_nonneg_left hlow2 (by linarith : 0≤1+η)]
  have h1 : (((range N).filter (fun n => ¬(cardFactors n:ℝ) ≤ (1+η)*w n)).card:ℝ) ≤ (E∪S∪T).card := by exact_mod_cast card_le_card sub
  have upper (A B : Finset ℕ) : ((A∪B).card:ℝ) ≤ A.card + B.card := by exact_mod_cast card_union_le A B
  dsimp [δ] at hE hS hT
  linarith [upper E S,upper (E∪S) T]
end Omega1100
end

open Filter Finset Real ArithmeticFunction
open scoped Topology
open OMA.R_Erdos1100_erdos_1100_variants_normal_order_R1

theorem OMA.solution : OMA.R_Erdos1100_erdos_1100_variants_normal_order_R1.H4 := by
  classical
  intro η hη
  apply hasDensity_one_iff_compl_zero.mpr
  rw [Set.HasDensity, Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Omega1100.bad_count_final η (ε/2) hη (by positivity), eventually_gt_atTop 0] with N hb hN
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (pd_nonneg _ _),pd_eq]
  apply lt_of_le_of_lt ((div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr hb)
  linarith
