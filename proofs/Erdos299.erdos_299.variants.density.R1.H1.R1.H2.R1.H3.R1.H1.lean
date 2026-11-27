import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1
import Mathlib

/-!
# Common divisors with a heavy cofactor family

The weighted divisor argument follows Bhavik Mehta and Thomas Bloom,
b-mehta/unit-fractions, src/aux_lemmas.lean at commit
10ef71a300cf29e5f19beb2bbc723a035a0678de, including contributions by
Eric Rodriguez. Copyright (c) 2021 Bhavik Mehta, Thomas Bloom.
Used under Apache-2.0. The large prime-power cutoff and the weighted
pigeonhole argument follow the fleet's shared note for this target.

Mertens' estimate is adapted from the merged Erdős 377 proof by
@marcusbuffett, starting with the Erdős 962 estimate by @senamakel
(open-math-agents commit d757b84b7870c7b80a9e62d5e93a293328aee0d4).
The finite Euler product is adapted from @marcusbuffett's merged Erdős 299
cofactor mass proof, PR 4548, head 358fc57ae2c26dfe465cbae94da6ea06a76713c6.

Write w = log log N. The sum of reciprocals of the available prime powers
above exp(log N/(2w²)) is o(w). A fixed exponential weight on the number
of factors therefore leaves enough mass on a single common divisor with
few prime factors. Its complementary factor keeps nearly all prime factors
of the original denominator.
-/

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

open Filter Finset Real
open scoped Classical Topology
namespace Param299
noncomputable abbrev w (N : ℕ) := log (log N)
noncomputable abbrev e (N : ℕ) := (log N)^(-(1/100:ℝ))
noncomputable abbrev M (N : ℕ) := (N:ℝ)^(1-1/w N)
lemma wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp Mass377.logTop
lemma geom (p : ℕ) (hp : 2≤p) (N : ℕ) :
    (∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1)) ≤ 2/(p:ℝ) := by
  have h : (∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1))+2/(p:ℝ)^(N+1) ≤ 2/(p:ℝ) := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have hpos : 0<(p:ℝ) := by exact_mod_cast (show 0<p by omega)
      have htwo : (2:ℝ)≤p := by exact_mod_cast hp
      have hh : 2/(p:ℝ)^(n+1+1) ≤ 1/(p:ℝ)^(n+1) := by
        rw [pow_succ _ (n+1),div_mul_eq_div_div]
        apply (div_le_iff₀ hpos).mpr
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      calc _ ≤ ((∑ k ∈ range n, (1:ℝ)/(p:ℝ)^(k+1))+1/(p:ℝ)^(n+1))+1/(p:ℝ)^(n+1) := add_le_add le_rfl hh
           _ = (∑ k ∈ range n, (1:ℝ)/(p:ℝ)^(k+1))+2/(p:ℝ)^(n+1) := by ring
           _ ≤ _ := ih
  linarith [show 0≤2/(p:ℝ)^(N+1) by positivity]
end Param299

open Real Filter Finset
open scoped Classical Topology
namespace Rough299
noncomputable abbrev w (N:ℕ) := log (log (N:ℝ))
noncomputable abbrev X (N:ℕ) := exp (log N/(2*(w N)^2))
noncomputable abbrev G (N:ℕ) := (range N).filter fun q : ℕ => IsPrimePow q ∧ X N < q
noncomputable abbrev R (N:ℕ) := (range N).filter fun d => 0<d ∧
  ∀ p : ℕ, p∈d.primeFactors → X N < (p:ℝ)^d.factorization p
lemma nonsimple : ∃ C : ℝ, ∀ (N : ℕ) (Q : Finset ℕ),
    (∀ q ∈ Q, IsPrimePow q ∧ ¬q.Prime ∧ q≤N) → ∑ q∈Q,(1:ℝ)/q ≤ C := by
  let C := ∑' n : ℕ, ((n:ℝ)^2)⁻¹
  refine ⟨2*C,?_⟩
  intro N Q hQ
  let U := Nat.primesLE N ×ˢ range N
  let f (z : ℕ×ℕ) := z.1^(z.2+2)
  have sub : Q⊆U.image f := by
    intro q hq
    obtain ⟨pp,no,le⟩ := hQ q hq
    obtain ⟨p,lp,k,lk,pr,pk,e⟩ := (isPrimePow_nat_iff_bounded q).mp pp
    have g : k≠1 := by rintro rfl; simp_all
    exact mem_image.mpr ⟨(p,k-2),mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨lp.trans le,pr⟩,mem_range.mpr (by omega)⟩,
      by dsimp [f]; rwa [show k-2+2=k by omega]⟩
  calc _ ≤ ∑ q∈U.image f,(1:ℝ)/q := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
       _ ≤ ∑ z∈U,(1:ℝ)/(f z) := sum_image_le_of_nonneg (fun _ _ => by positivity)
       _ = ∑ p∈Nat.primesLE N, ∑ k∈ range N, (1:ℝ)/(p:ℝ)^(k+2) := by simp [U,f,sum_product]
       _ ≤ ∑ p∈Nat.primesLE N, 2*((p:ℝ)^2)⁻¹ := by
         apply sum_le_sum
         intro p hp
         have g := Param299.geom p (Nat.mem_primesLE.mp hp).2.two_le N
         have pp : (0:ℝ)<p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
         simp_rw [show ∀ k : ℕ, (1:ℝ)/(p:ℝ)^(k+2)=(1/(p:ℝ)^(k+1))/p by intro k; rw [pow_succ,div_div]]
         rw [←sum_div]
         calc _ ≤ ((2:ℝ)/p)/p := div_le_div_of_nonneg_right g pp.le
              _ = _ := by ring
       _ ≤ _ := by
         rw [←mul_sum]
         exact mul_le_mul_of_nonneg_left ((Real.summable_nat_pow_inv.mpr (by norm_num : 1<2)).sum_le_tsum _ (fun _ _ => by positivity)) (by norm_num)
lemma small_mass (c : ℝ) (hc : 0<c) :
    ∀ᶠ N : ℕ in atTop, ∑ q∈G N,(1:ℝ)/q ≤ c*w N := by
  have wt : Tendsto w atTop atTop := Param299.wtop
  have xt : Tendsto X atTop atTop := by
    have ht := (tendsto_exp_div_pow_atTop 2).comp wt
    have h2 := ht.atTop_div_const (by norm_num : (0:ℝ)<2)
    apply tendsto_exp_atTop.comp
    apply h2.congr'
    filter_upwards [Mass377.logTop.eventually_gt_atTop 0] with N hN
    simp only [Function.comp_apply,w,exp_log hN,div_div]
    ring
  obtain ⟨b,hb⟩ := Mass377.realMertens
  obtain ⟨C,cc⟩ := nonsimple
  have little := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp wt).eventually_lt_const (show 0<c/4 by positivity)
  filter_upwards [(hb.comp xt).eventually_const_lt (show b-1<b by linarith),
    (hb.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_lt_const (show b<b+1 by linarith),
    little, wt.eventually_gt_atTop 2, wt.eventually_gt_atTop (2*(2+log 2+C)/c),
    Mass377.logTop.eventually_gt_atTop 0,eventually_ge_atTop 2] with N lower upper small hw huge nlog hn
  have wp : 0<w N := by linarith
  have xp : X N≤N := by
    apply (le_log_iff_exp_le (by positivity : (0:ℝ)<N)).mp
    exact div_le_self nlog.le (by nlinarith [sq_nonneg (w N-1)])
  have lt : log (log (X N)) = w N-log 2-2*log (w N) := by
    rw [X,log_exp,log_div nlog.ne' (by positivity),log_mul (by norm_num) (by positivity),log_pow]
    dsimp only [w]; ring
  let P := (G N).filter Nat.Prime
  let Q := G N \ P
  have sub : P ⊆ Nat.primesLE N \ Nat.primesLE ⌊X N⌋₊ := by
    intro q hq
    obtain ⟨qG,pr⟩ := mem_filter.mp hq
    obtain ⟨qr,_,gt⟩ := mem_filter.mp qG
    exact mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨(mem_range.mp qr).le,pr⟩,
      fun h => (not_le_of_gt gt) ((Nat.le_floor_iff (exp_pos _).le).mp (Nat.mem_primesLE.mp h).1)⟩
  have incl : Nat.primesLE ⌊X N⌋₊ ⊆ Nat.primesLE N := by
    intro p hp
    have le : ⌊X N⌋₊ ≤ N := Nat.floor_le_of_le (by exact_mod_cast xp)
    exact Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans le,(Nat.mem_primesLE.mp hp).2⟩
  have prim := sum_le_sum_of_subset_of_nonneg (f:=fun q : ℕ => (1:ℝ)/q) sub (fun _ _ _ => by positivity)
  have sumP := sum_sdiff (f:=fun q : ℕ => (1:ℝ)/q) incl
  have sP : ∑ q∈P,(1:ℝ)/q ≤ Mass377.S N-Mass377.S (X N) := by
    simp only [Mass377.S,Nat.floor_natCast]
    linarith
  have ns := cc N Q (fun q hq => by
    obtain ⟨qG,no⟩ := mem_sdiff.mp hq
    obtain ⟨qr,pr,_⟩ := mem_filter.mp qG
    exact ⟨pr,fun p => no (mem_filter.mpr ⟨qG,p⟩),(mem_range.mp qr).le⟩)
  have tot := sum_sdiff (f:=fun q : ℕ => (1:ℝ)/q) (show P⊆G N from filter_subset _ _)
  change (∑ q∈Q, _)+(∑ q∈P, _) = _ at tot
  change b-1 < Mass377.S (X N)-log (log (X N)) at lower
  change Mass377.S N-w N<b+1 at upper
  change log (w N)/w N<c/4 at small
  rw [div_lt_iff₀ wp] at small
  rw [div_lt_iff₀ hc] at huge
  rw [lt] at lower
  linarith
end Rough299

namespace Rough299
open Finset Real
open scoped BigOperators
def factors (n : ℕ) := n.primeFactors.image (fun p => p ^ n.factorization p)
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
lemma exponential_bound (N : ℕ) (u : ℝ) :
    (∑ n ∈ R N, exp (u*(n.primeFactors.card:ℝ))/n) ≤
      exp (exp u*∑ q ∈ G N,(1:ℝ)/q) := by
  let C := R N
  have hz : 0∉C := fun h => (mem_filter.mp h).2.1.false
  classical
  let w (q : ℕ) := exp u / (q : ℝ)
  have reconstruct (n : ℕ) (hn : n ∈ C) : ∏ q ∈ factors n, w q = exp (u*(n.primeFactors.card:ℝ)) / n := by
    have hne : n ≠ 0 := fun e => hz (e ▸ hn)
    have den : (∏ q ∈ factors n, (q : ℝ)) = n := by
      change (∏ x ∈ factors n, (Nat.castRingHom ℝ) x) = (Nat.castRingHom ℝ) n
      rw [← map_prod,recover hne]
    simp only [w,prod_div_distrib,prod_const,den]
    rw [factors,card_image_of_injOn (distinct n),← exp_nat_mul,mul_comm]
  have inject : Set.InjOn factors (↑C) := by
    intro n hn m hm heq
    have h := congrArg (fun s : Finset ℕ => ∏ q ∈ s, q) heq
    simpa only [recover (show n≠0 from fun e => hz (e ▸ hn)),recover (show m≠0 from fun e => hz (e ▸ hm))] using h
  have included : C.image factors ⊆ (G N).powerset := by
    intro s hs
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hs
    apply mem_powerset.mpr
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    obtain ⟨ng,pos,rough⟩ := mem_filter.mp hn
    have pr := Nat.prime_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd pos (Nat.ordProj_dvd n p)).trans_lt (mem_range.mp ng)),
      pr.isPrimePow.pow (Finsupp.mem_support_iff.mp hp),by exact_mod_cast rough p hp⟩
  calc
    _ = ∑ s ∈ C.image factors, ∏ q ∈ s, w q := by
      rw [sum_image inject]
      exact sum_congr rfl (fun n hn => (reconstruct n hn).symm)
    _ ≤ ∑ s ∈ (G N).powerset, ∏ q ∈ s, w q :=
      sum_le_sum_of_subset_of_nonneg included (fun _ _ _ => prod_nonneg fun _ _ => by dsimp [w]; positivity)
    _ = ∏ q ∈ G N, (1+w q) := (prod_one_add _).symm
    _ ≤ ∏ q ∈ G N, exp (w q) := prod_le_prod
      (fun q _ => by dsimp [w]; positivity) (fun q _ => by linarith [add_one_le_exp (w q)])
    _ = _ := by rw [← Real.exp_sum,Finset.mul_sum]; congr 1; apply sum_congr rfl; intro q hq; dsimp [w]; ring
end Rough299

open Real Filter Finset
open scoped Classical Topology
namespace Rough299
lemma budget : ∀ᶠ N : ℕ in atTop,
    ∑ d∈R N, (if (d.primeFactors.card:ℝ)≤w N/110 then (log N)^(-(1/99:ℝ))
      else 1+log N)/d < (log N)^(-(1/100:ℝ))/2 := by
  let δ : ℝ := 1/30000
  have dil : 0<δ/exp 330 := by dsimp [δ]; positivity
  filter_upwards [small_mass _ dil,Param299.wtop.eventually_gt_atTop 0,
    Mass377.logTop.eventually_gt_atTop 2,Param299.wtop.eventually_gt_atTop (20000*log 2)]
    with N small hw hb big
  let b := log (N:ℝ)
  let a := b^(-(1/99:ℝ))
  have bp : 0<b := by dsimp [b]; linarith
  have ap : 0<a := rpow_pos_of_pos bp _
  have form : a=exp (-(1/99:ℝ)*w N) := by rw [show a=b^(-(1/99:ℝ)) by rfl,rpow_def_of_pos bp]; congr 1; ring
  have est := exponential_bound N 330
  have em : exp 330*(∑ q∈G N,(1:ℝ)/q) ≤ δ*w N := by
    calc _ ≤ exp 330*((δ/exp 330)*w N) := mul_le_mul_of_nonneg_left small (exp_pos 330).le
         _ = _ := by field_simp
  have point (d : ℕ) : (if (d.primeFactors.card:ℝ)≤w N/110 then a else 1+b) ≤
      a*exp (330*(d.primeFactors.card:ℝ)) := by
    split_ifs with h
    · have one : 1 ≤ exp (330*(d.primeFactors.card:ℝ)) := one_le_exp (by positivity)
      simpa using mul_le_mul_of_nonneg_left one ap.le
    · have lt := lt_of_not_ge h
      rw [form,←exp_add]
      have high : 2*w N < -(1/99:ℝ)*w N+330*d.primeFactors.card := by linarith
      have eq : exp (2*w N)=b^2 := by rw [show 2*w N=w N*2 by ring,Real.exp_mul]; norm_cast; rw [exp_log bp]
      have ge : 1+b ≤ b^2 := by change 2<b at hb; nlinarith [sq_nonneg (b-2)]
      exact ge.trans (eq ▸ (exp_le_exp.mpr high.le))
  calc
    _ ≤ ∑ d∈R N, a*(exp (330*(d.primeFactors.card:ℝ))/d) := by
      apply sum_le_sum
      intro d hd
      simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right (point d) (Nat.cast_nonneg d : (0:ℝ)≤d))
    _ ≤ a*exp (δ*w N) := by
      rw [←mul_sum]
      exact mul_le_mul_of_nonneg_left (est.trans (exp_le_exp.mpr em)) ap.le
    _ < _ := by
      rw [form,←exp_add,lt_div_iff₀ (by norm_num : (0:ℝ)<2),
        show (2:ℝ)=exp (log 2) from (exp_log (by norm_num)).symm,←exp_add,rpow_def_of_pos bp,exp_lt_exp]
      change _ < w N * (-(1/100:ℝ))
      dsimp only [δ]
      linarith
end Rough299

open Real Finset Filter
open scoped Classical Topology
namespace Rough299
lemma select : ∀ᶠ N : ℕ in atTop,
  let M := (N:ℝ)^(1-1/w N)
  ∀ n q : ℕ, 0<n → n<N → M≤n → (n.primeFactors.card:ℝ)≤2*w N →
    IsPrimePow q → q∣n → Nat.Coprime q (n/q) → ∃ d∈R N,
    M*(N:ℝ)^(-2/w N) < q*(d:ℝ) ∧ q*d∣n ∧ Nat.Coprime (q*d) (n/(q*d)) := by
  filter_upwards [Param299.wtop.eventually_gt_atTop 1,Mass377.logTop.eventually_gt_atTop 0,eventually_gt_atTop 1]
    with N hw hb hn
  intro M n q nz nb nM count qp qn cp
  let m := n/q
  have mpos : 0 < m := Nat.div_pos (Nat.le_of_dvd nz qn) qp.pos
  have eqn : q*m=n := Nat.mul_div_cancel' qn
  let S := m.primeFactors.filter fun p : ℕ => X N < (p:ℝ)^m.factorization p
  let V := m.primeFactors \ S
  let F (p : ℕ) := p^m.factorization p
  let d := ∏ p∈S, F p
  let t := ∏ p∈V, F p
  have prod : d*t=m := by
    rw [mul_comm,show t*d = ∏ p∈m.primeFactors, F p from prod_sdiff (filter_subset _ _)]
    exact (Nat.prod_primeFactors_pow_factorization mpos.ne').symm
  have posprod : 0<d*t := prod.symm ▸ mpos
  have dpos : 0<d := by
    by_contra! he
    rw [show d=0 by omega,zero_mul] at posprod
    omega
  have tpos : 0<t := by
    by_contra! he
    rw [show t=0 by omega,mul_zero] at posprod
    omega
  have ddiv : d∣m := ⟨t,prod.symm⟩
  have mdiv : m∣n := ⟨q,by simpa [mul_comm] using eqn.symm⟩
  have split : Nat.Coprime d t := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro a ha
    exact (((Nat.coprime_primes (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
      (Nat.prime_of_mem_primeFactors (mem_sdiff.mp ha).1)).mpr (by rintro rfl; exact (mem_sdiff.mp ha).2 hp)).pow_left _).pow_right _
  have dR : d∈R N := by
    refine mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd nz (ddiv.trans mdiv)).trans_lt nb),dpos,?_⟩
    intro p pd
    have pm := Nat.primeFactors_mono ddiv mpos.ne' pd
    have pp := Nat.prime_of_mem_primeFactors pd
    have pds := Nat.dvd_of_mem_primeFactors pd
    have npt := (pp.coprime_iff_not_dvd).mp (split.coprime_dvd_left pds)
    have e : m.factorization p=d.factorization p := by
      rw [←prod,Nat.factorization_mul_apply_of_coprime split,Nat.factorization_eq_zero_of_not_dvd npt,add_zero]
    rw [←e]
    by_contra! fail
    have pv : p∈V := mem_sdiff.mpr ⟨pm,by simpa [S,pm] using fail⟩
    exact npt ((dvd_pow_self _ (Finsupp.mem_support_iff.mp pm)).trans (dvd_prod_of_mem F pv))
  have nrep : (q*d)*t=n := by rw [mul_assoc,prod,eqn]
  have cop : Nat.Coprime (q*d) t := Nat.Coprime.mul_left (cp.coprime_dvd_right (show t∣m from ⟨d,by rw [mul_comm,prod]⟩)) split
  have divt : n/(q*d)=t := by rw [←nrep,Nat.mul_div_cancel_left _ (Nat.mul_pos qp.pos dpos)]
  refine ⟨d,dR,?_,⟨t,nrep.symm⟩,divt ▸ cop⟩
  have logt : log (t:ℝ) ≤ log N / w N := by
    have vp (p : ℕ) (hp : p∈V) : 0<(F p:ℝ) := by
      dsimp [F]
      positivity [(Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1).pos]
    have val (p : ℕ) (hp : p∈V) : log (F p:ℝ)≤log N/(2*(w N)^2) := by
      have ne := (mem_sdiff.mp hp).2
      have h : (F p:ℝ)≤X N := by
        by_contra! no
        apply ne
        apply mem_filter.mpr
        exact ⟨(mem_sdiff.mp hp).1,by simpa [F] using no⟩
      exact (log_le_log (vp p hp) h).trans_eq (log_exp _)
    have vsub : V⊆n.primeFactors := (sdiff_subset).trans (Nat.primeFactors_mono mdiv nz.ne')
    have card : (V.card:ℝ)≤2*w N := (by exact_mod_cast card_le_card vsub : (V.card:ℝ)≤n.primeFactors.card).trans count
    have eval : log (t:ℝ)=∑ p∈V, log (F p:ℝ) := by
      simp only [t,Nat.cast_prod]
      exact log_prod (fun p hp => (vp p hp).ne')
    rw [eval]
    calc _ ≤ ∑ _p∈V, log N/(2*(w N)^2) := sum_le_sum val
         _ ≤ 2*w N*(log N/(2*(w N)^2)) := by
           simp only [sum_const,nsmul_eq_mul]
           exact mul_le_mul_of_nonneg_right card (by positivity)
         _ = _ := by field_simp <;> ring
  have nr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have tr : (0:ℝ)<t := by exact_mod_cast tpos
  have upper : (t:ℝ)<(N:ℝ)^(2/w N) := by
    apply (log_lt_log_iff tr (rpow_pos_of_pos nr _)).mp
    rw [log_rpow nr]
    have bpos : 0<log N/w N := by positivity
    linarith [show 2/w N*log N=2*(log N/w N) by ring]
  have rho := rpow_pos_of_pos nr (2/w N)
  rw [show (-2:ℝ)/w N=-(2/w N) by ring,rpow_neg nr.le,←div_eq_mul_inv,div_lt_iff₀ rho]
  have eqr : (q:ℝ)*d*t=n := by exact_mod_cast nrep
  exact nM.trans_lt (eqr ▸ (mul_lt_mul_of_pos_left upper (by exact_mod_cast Nat.mul_pos qp.pos dpos : 0<(q:ℝ)*d)))
end Rough299

open Real Filter Finset
open scoped Classical Topology
namespace Rough299
lemma divisor_sample {N : ℕ} {S : Finset ℕ} (hN : 0<N) (sm : S⊆Icc 1 N) :
    (∑ n∈S,(1:ℝ)/n) ≤ 1+log N := by
  have e := harmonic_floor_le_one_add_log (N:ℝ) (by exact_mod_cast hN)
  rw [Nat.floor_natCast,harmonic_eq_sum_Icc,Rat.cast_sum] at e
  push_cast at e
  simpa [one_div] using (sum_le_sum_of_subset_of_nonneg (f:=fun n : ℕ => (n:ℝ)⁻¹) sm (fun _ _ _ => by positivity)).trans e
theorem result : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1.H1 := by
  classical
  filter_upwards [select,budget,Param299.wtop.eventually_gt_atTop 1000,eventually_gt_atTop 2,
    Mass377.logTop.eventually_gt_atTop 0] with N hsel estimate hw hn hb
  intro A q ha an reg qp mass
  let J := A.filter (fun n => q∣n ∧ Nat.Coprime q (n/q))
  let M := (N:ℝ)^(1-1/w N)
  let K := M*(N:ℝ)^(-2/w N)
  let b := log (N:ℝ)
  let v (d : ℕ) := if (d.primeFactors.card:ℝ)≤w N/110 then b^(-(1/99:ℝ)) else 1+b
  let a := b^(-(1/99:ℝ))
  have ap : 0<a := rpow_pos_of_pos hb _
  have qp0 : 0<q := qp.pos
  have haveD {n : ℕ} (hn : n∈J) := hsel n q
    (Nat.pos_of_ne_zero (fun e => ha (e ▸ (mem_filter.mp hn).1))) (mem_range.mp (an (mem_filter.mp hn).1))
    (reg n (mem_filter.mp hn).1).1 (reg n (mem_filter.mp hn).1).2.2.2 qp (mem_filter.mp hn).2.1 (mem_filter.mp hn).2.2
  let f (n : ℕ) := if hn : n∈J then (haveD hn).choose else 1
  have spec {n : ℕ} (hn : n∈J) : f n∈R N ∧ K<q*(f n:ℝ) ∧ q*f n∣n ∧ Nat.Coprime (q*f n) (n/(q*f n)) := by
    simpa [f,hn,K,M] using (haveD hn).choose_spec
  let F (d : ℕ) := J.filter fun n => f n=d
  let C (d : ℕ) := (F d).image (fun n => n/(q*d))
  let m (S : Finset ℕ) := ∑ n∈S,(1:ℝ)/n
  have Dspec {d n : ℕ} (hn : n∈F d) : n∈A ∧ K<q*(d:ℝ) ∧ q*d∣n ∧ Nat.Coprime (q*d) (n/(q*d)) := by
    obtain ⟨j,e⟩ := mem_filter.mp hn
    exact ⟨(mem_filter.mp j).1,e ▸ (spec j).2⟩
  have factor {d n : ℕ} (hn : n∈F d) : q*d*(n/(q*d))=n := Nat.mul_div_cancel' (Dspec hn).2.2.1
  have fiber (d : ℕ) (hd : d∈R N) : m (C d)/d=∑ n∈F d,(q:ℝ)/n := by
    have dp := (mem_filter.mp hd).2.1
    dsimp only [m,C]
    rw [sum_image,sum_div]
    · apply sum_congr rfl
      intro n hn
      have pos : 0<n := Nat.pos_of_ne_zero (fun e => ha (e ▸ (Dspec hn).1))
      have rn : (0:ℝ)<n := by exact_mod_cast pos
      have rd : (0:ℝ)<d := by exact_mod_cast dp
      have rm : (0:ℝ)<(n/(q*d):ℕ) := by exact_mod_cast Nat.div_pos (Nat.le_of_dvd pos (Dspec hn).2.2.1) (Nat.mul_pos qp0 dp)
      have re : (q:ℝ)*d*(n/(q*d):ℕ)=n := by exact_mod_cast factor hn
      field_simp
      linarith
    · intro n h m hm eq
      exact (factor h).symm.trans ((congrArg (q*d*·) eq).trans (factor hm))
  have total := sum_fiberwise_of_maps_to (s:=J) (t:=R N) (g:=f) (fun n hn => (spec hn).1) (fun n => (q:ℝ)/n)
  have win : ∃ d∈R N, v d < m (C d) := by
    by_contra! fail
    have le := sum_le_sum (s:=R N) (fun d hd => div_le_div_of_nonneg_right (fail d hd) (Nat.cast_nonneg d : (0:ℝ)≤d))
    change ∑ d∈R N, v d / d < b^(-(1/100:ℝ))/2 at estimate
    change b^(-(1/100:ℝ))/2≤∑ n∈J,(q:ℝ)/n at mass
    have eq : ∑ d∈R N, m (C d)/d = ∑ n∈J,(q:ℝ)/n := (sum_congr rfl fiber).trans total
    linarith
  obtain ⟨d,hd,win⟩ := win
  have dp := (mem_filter.mp hd).2.1
  have hbnd : C d ⊆ Icc 1 N := by
    intro s hs
    obtain ⟨n,h,rfl⟩ := mem_image.mp hs
    have pos : 0<n := Nat.pos_of_ne_zero (fun e => ha (e ▸ (Dspec h).1))
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd pos (Dspec h).2.2.1) (Nat.mul_pos qp0 dp),
      (Nat.div_le_self _ _).trans (mem_range.mp (an (Dspec h).1)).le⟩
  have low : (d.primeFactors.card:ℝ)≤w N/110 := by
    by_contra no
    have h := divisor_sample (by omega : 0<N) hbnd
    change m (C d) ≤ 1+b at h
    exact (not_lt_of_ge h) (by simpa only [v,if_neg no] using win)
  change (if _ then _ else _) < m (C d) at win
  rw [if_pos low] at win
  have non : (F d).Nonempty := by
    by_contra! empty
    have e : C d=∅ := by simp [C,empty]
    rw [e] at win
    change a < ∑ n∈(∅:Finset ℕ), (1:ℝ)/n at win
    simp at win
    linarith
  obtain ⟨n,hnF⟩ := non
  refine ⟨q*d,C d,by change K < ((q*d:ℕ):ℝ); rw [Nat.cast_mul]; exact (Dspec hnF).2.1,dvd_mul_right _ _,win.le,?_⟩
  intro s hs
  obtain ⟨n,h,rfl⟩ := mem_image.mp hs
  have e := factor h
  have data := Dspec h
  refine ⟨by rw [e]; exact data.1,data.2.2.2.symm,?_,?_⟩
  · let s := n/(q*d)
    have spos : 0<s := (mem_Icc.mp (hbnd (mem_image.mpr ⟨n,h,rfl⟩))).1
    have qc : q.primeFactors.card=1 := by
      obtain ⟨p,k,pr,pk,eq⟩ := (isPrimePow_nat_iff q).mp qp
      rw [←eq,Nat.primeFactors_prime_pow (by omega) pr,card_singleton]
    have card : n.primeFactors.card ≤ 1+d.primeFactors.card+s.primeFactors.card := by
      rw [←e,Nat.primeFactors_mul (Nat.mul_pos qp0 dp).ne' spos.ne']
      have ab := card_union_le (q*d).primeFactors s.primeFactors
      have first := card_union_le q.primeFactors d.primeFactors
      rw [Nat.primeFactors_mul qp0.ne' dp.ne'] at ab ⊢
      omega
    have realc : (n.primeFactors.card:ℝ) ≤ 1+d.primeFactors.card+s.primeFactors.card := by exact_mod_cast card
    have lower := (reg n data.1).2.2.1
    change 99/100*w N ≤ n.primeFactors.card at lower
    change (1-2/99)*w N ≤ s.primeFactors.card
    change 1000<w N at hw
    linarith
  · have sub := Nat.primeFactors_mono (show n/(q*d)∣n from ⟨_,e.symm.trans (Nat.mul_comm _ _)⟩) (fun eq => ha (eq ▸ data.1))
    exact (show ((n/(q*d)).primeFactors.card:ℝ) ≤ n.primeFactors.card by exact_mod_cast card_le_card sub).trans (reg n data.1).2.2.2
end Rough299

theorem OMA.solution : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1.H1 := Rough299.result
