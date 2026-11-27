import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1
import Mathlib

/-!
The pruning argument adapts Lemmas 5.5 and 5.6 and the main technical lemma
from Bhavik Mehta and Thomas Bloom, b-mehta/unit-fractions, src/main_results.lean,
commit 10ef71a300cf29e5f19beb2bbc723a035a0678de.
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Copyright (c) 2022 Bhavik Mehta, Thomas Bloom. All rights reserved.
Used under Apache-2.0.

The proof maximizes a penalized mass to clean the set, erases one safe element
at a time to tune the mass, and maximizes the target divisor. The Mertens
estimates are adapted from the merged Erdős 377 proof by @marcusbuffett,
which credits @senamakel for the first estimate and successive-error bounds.
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
open Filter Finset Real
open scoped Classical Topology
namespace Prune299
noncomputable abbrev mass (A : Finset ℕ) := ∑ n ∈ A, (1:ℝ)/n
def rel (q n : ℕ) : Prop := q ∣ n ∧ Nat.Coprime q (n/q)
noncomputable def part (A : Finset ℕ) (q : ℕ) := A.filter (rel q)
noncomputable def active (P A : Finset ℕ) := P.filter fun q => (part A q).Nonempty
def stable (P A : Finset ℕ) (e : ℝ) : Prop :=
  ∀ q ∈ active P A, e/(q:ℝ) ≤ mass (part A q)
lemma mass_nn (A : Finset ℕ) : 0 ≤ mass A := sum_nonneg fun n _ => by positivity
lemma mass_mono {A B : Finset ℕ} (h : A⊆B) : mass A ≤ mass B :=
  sum_le_sum_of_subset_of_nonneg h (fun n _ _ => by positivity)
lemma part_mono {A B : Finset ℕ} (h : A⊆B) (q : ℕ) : part A q ⊆ part B q :=
  filter_subset_filter _ h
lemma active_mono (P : Finset ℕ) {A B : Finset ℕ} (h : A⊆B) : active P A ⊆ active P B := by
  intro q hq
  obtain ⟨hp,hn⟩ := mem_filter.mp hq
  exact mem_filter.mpr ⟨hp,hn.mono (part_mono h q)⟩
lemma cleanup (P A : Finset ℕ) (e : ℝ) (he : 0≤e) :
    ∃ B⊆A, stable P B e ∧ mass A-e*mass P ≤ mass B := by
  classical
  let score (S : Finset ℕ) := mass S - e*mass (active P S)
  obtain ⟨B,hB,hmax⟩ := exists_max_image A.powerset score ⟨A,mem_powerset.mpr (Subset.refl A)⟩
  have sub := mem_powerset.mp hB
  have best := hmax A (mem_powerset.mpr (Subset.refl A))
  have lower : mass A-e*mass P ≤ mass B := by
    dsimp [score] at best
    have hP := mass_mono (filter_subset (fun q => (part A q).Nonempty) P)
    change mass (active P A) ≤ mass P at hP
    linarith only [best,mul_le_mul_of_nonneg_left hP he,mul_nonneg he (mass_nn (active P B))]
  refine ⟨B,sub,?_,lower⟩
  intro q hq
  let C := B \ part B q
  have cb : C ⊆ B := sdiff_subset
  have eq := sum_sdiff (filter_subset (rel q) B) (f:=fun n : ℕ => (1:ℝ)/n)
  change mass C + mass (part B q) = mass B at eq
  have qC : q ∉ active P C := by
    intro h
    obtain ⟨n,hn⟩ := (mem_filter.mp h).2
    obtain ⟨hc,hr⟩ := mem_filter.mp hn
    exact (mem_sdiff.mp hc).2 (mem_filter.mpr ⟨(mem_sdiff.mp hc).1,hr⟩)
  have inc : insert q (active P C) ⊆ active P B := insert_subset hq (active_mono P cb)
  have cost := mass_mono inc
  rw [mass,sum_insert qC] at cost
  have bound := hmax C (mem_powerset.mpr (cb.trans sub))
  change mass C - e*mass (active P C) ≤ mass B-e*mass (active P B) at bound
  change 1/(q:ℝ)+mass (active P C) ≤ mass (active P B) at cost
  have hc := mul_le_mul_of_nonneg_left cost he
  rw [mul_add,mul_one_div] at hc
  linarith
lemma trim (P A : Finset ℕ) (e M t : ℝ) (he : 0≤e) (hM : 0<M)
    (hP : ∀ q ∈ P, 0<q ∧ (q:ℝ)≤e*M)
    (small : ∀ n ∈ A, M≤n) (heavy : 2*e*mass P < t)
    (start : t+e*mass P ≤ mass A) :
    ∃ B⊆A, stable P B e ∧ mass B<t ∧ t-1/M≤ mass B := by
  classical
  obtain ⟨S,sub,hgood,hm⟩ := cleanup P A e he
  have descend (V : Finset ℕ) (hV : V⊆A) (good : stable P V e) (hv : t-1/M≤ mass V) :
      ∃ B⊆V, stable P B e ∧ mass B<t ∧ t-1/M≤ mass B := by
    induction V using Finset.strongInductionOn with
    | _ V ih =>
      by_cases done : mass V<t
      · exact ⟨V,Subset.rfl,good,done,hv⟩
      obtain ⟨W,hw,gw,mw⟩ := cleanup P V (2*e) (by positivity)
      have posW : 0 < mass W := by linarith
      obtain ⟨x,hx⟩ := nonempty_of_ne_empty (s:=W) (fun eq => by simp [eq,mass] at posW)
      have xv := hw hx
      let D := V.erase x
      have subD : D ⊆ V := erase_subset _ _
      have proper : D ⊂ V := erase_ssubset xv
      have xM := small x (hV xv)
      have xm : (1:ℝ)/x ≤ 1/M := one_div_le_one_div_of_le hM xM
      have mD := sum_erase_add V (fun n : ℕ => (1:ℝ)/n) xv
      change mass D + 1/(x:ℝ) = mass V at mD
      have next : stable P D e := by
        intro q hq
        have old := good q (active_mono P subD hq)
        have qp := (mem_filter.mp hq).1
        have eq : part D q = (part V q).erase x := by
          ext n
          simp [D,part,and_assoc,and_left_comm,and_comm]
        by_cases hr : rel q x
        · have wq : q ∈ active P W := mem_filter.mpr ⟨qp,⟨x,mem_filter.mpr ⟨hx,hr⟩⟩⟩
          have better := (gw q wq).trans (mass_mono (part_mono hw q))
          have delta := sum_erase_add (part V q) (fun n : ℕ => (1:ℝ)/n) (mem_filter.mpr ⟨xv,hr⟩)
          rw [←eq] at delta
          have qpos : (0:ℝ)<q := by exact_mod_cast (hP q qp).1
          have xcost : (1:ℝ)/x ≤ e/q := by
            apply (div_le_div_iff₀ (hM.trans_le xM) qpos).mpr
            simpa using ((hP q qp).2.trans (mul_le_mul_of_nonneg_left xM he))
          rw [mul_div_assoc] at better
          change mass (part D q) + 1/(x:ℝ) = mass (part V q) at delta
          linarith
        · have absent : x ∉ part V q := fun hn => hr (mem_filter.mp hn).2
          rw [eq,erase_eq_of_notMem absent]
          exact old
      obtain ⟨B,hB,gb,mb,mB⟩ := ih D proper (subD.trans hV) next (by linarith)
      exact ⟨B,hB.trans subD,gb,mb,mB⟩
  obtain ⟨B,hB,gb,mb,mB⟩ := descend S sub hgood (by linarith [one_div_pos.mpr hM])
  exact ⟨B,hB.trans sub,gb,mb,mB⟩
end Prune299
end

section
open Filter Finset Real
open scoped Classical Topology
namespace Param299
noncomputable abbrev w (N : ℕ) := log (log N)
noncomputable abbrev e (N : ℕ) := (log N)^(-(1/100:ℝ))
noncomputable abbrev M (N : ℕ) := (N:ℝ)^(1-1/w N)
lemma wtop : Tendsto w atTop atTop := tendsto_log_atTop.comp Mass377.logTop
lemma Mtop : Tendsto M atTop atTop := by
  have h := (tendsto_rpow_atTop (by norm_num : 0<(1/2:ℝ))).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply tendsto_atTop_mono' _ _ h
  filter_upwards [wtop.eventually_ge_atTop 2,eventually_ge_atTop 1] with N hw hn
  apply rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  linarith [one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hw]
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
lemma prime_mass (N : ℕ) (P : Finset ℕ) (hb : ∀ q ∈ P, IsPrimePow q ∧ q≤N) :
    (∑ q ∈ P, (1:ℝ)/q) ≤ 2*∑ p ∈ Nat.primesLE N,(1:ℝ)/p := by
  let U := Nat.primesLE N ×ˢ range N
  let f (p : ℕ×ℕ) := p.1^(p.2+1)
  have sub : P ⊆ U.image f := by
    intro q hq
    obtain ⟨pp,le⟩ := hb q hq
    obtain ⟨p,hp,k,hk,pr,hk0,eq⟩ := (isPrimePow_nat_iff_bounded q).mp pp
    cases k with
    | zero => omega
    | succ j =>
      exact mem_image.mpr ⟨(p,j),mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨hp.trans le,pr⟩,
        mem_range.mpr (by omega)⟩,eq⟩
  calc _ ≤ ∑ q ∈ U.image f, (1:ℝ)/q := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
       _ ≤ ∑ a ∈ U, (1:ℝ)/(f a) := sum_image_le_of_nonneg (fun _ _ => by positivity)
       _ = ∑ p ∈ Nat.primesLE N, ∑ k ∈ range N, (1:ℝ)/(p:ℝ)^(k+1) := by
         simp [U,f,sum_product]
       _ ≤ ∑ p ∈ Nat.primesLE N, 2/(p:ℝ) := sum_le_sum fun p hp => geom p (Nat.mem_primesLE.mp hp).2.two_le N
       _ = _ := by rw [mul_sum]; congr 1; ext; ring
lemma eMass : Tendsto (fun N => e N*w N) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1/100:ℝ) (by norm_num)).comp wtop
  apply h.congr'
  filter_upwards [Mass377.logTop.eventually_gt_atTop 0] with N hN
  simp only [Function.comp_apply,Real.rpow_one,e,Real.rpow_def_of_pos hN]
  dsimp only [w]
  ring_nf
lemma params (δ : ℝ) (hδ : 0<δ) : ∀ᶠ N : ℕ in atTop,
    0<e N ∧ 0<M N ∧ 1/M N<δ ∧ (N:ℝ)^(1-8/w N) ≤ e N*M N ∧
    ∀ P : Finset ℕ, (∀ q ∈ P, IsPrimePow q ∧ q≤N) → e N*(∑ q ∈ P,(1:ℝ)/q)<δ := by
  obtain ⟨b,hb⟩ := Mass377.natMertens
  filter_upwards [eMass.eventually_lt_const (show 0<δ/4 by positivity),
    hb.eventually_lt_const (show b<b+1 by linarith),wtop.eventually_gt_atTop (|b|+2),
    (tendsto_exp_div_pow_atTop 2 |>.comp wtop).eventually_ge_atTop 1,
    (tendsto_inv_atTop_zero.comp Mtop).eventually_lt_const hδ,
    Mass377.logTop.eventually_gt_atTop 0,eventually_ge_atTop 1] with N het hb hw hex hM hl hN
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have pos : 0<e N := Real.rpow_pos_of_pos hl _
  have hw0 : 0<w N := by linarith [abs_nonneg b]
  refine ⟨pos,Real.rpow_pos_of_pos hn _,by simpa [one_div] using hM,?_,?_⟩
  · change 1≤exp (w N)/(w N)^2 at hex
    rw [show exp (w N)=log N from exp_log hl] at hex
    have hw2 := (le_div_iff₀ (sq_pos_of_pos hw0)).mp hex
    rw [e,M,Real.rpow_def_of_pos hl,Real.rpow_def_of_pos hn,Real.rpow_def_of_pos hn,←exp_add]
    apply exp_le_exp.mpr
    change log N*(1-8/w N) ≤ w N * -(1/100:ℝ)+log N*(1-1/w N)
    field_simp [hw0.ne']
    nlinarith
  · intro P hP
    change (∑ p ∈ Nat.primesLE N,(1:ℝ)/p)-w N < b+1 at hb
    have s : (∑ p ∈ Nat.primesLE N,(1:ℝ)/p) ≤ 2*w N := by linarith [le_abs_self b]
    have bound := mul_le_mul_of_nonneg_left ((prime_mass N P hP).trans (mul_le_mul_of_nonneg_left s (by norm_num))) pos.le
    change e N*w N < δ/4 at het
    linarith
end Param299
end

section
open Filter Finset Real
open scoped Classical Topology
namespace Prune299
noncomputable def powers (A : Finset ℕ) := A.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
lemma powers_mem {A : Finset ℕ} {q : ℕ} (h : q ∈ powers A) :
    IsPrimePow q ∧ ∃ n ∈ A, n ≠ 0 ∧ rel q n := by
  obtain ⟨n,hn,hq⟩ := mem_biUnion.mp h
  obtain ⟨div,pp,copr⟩ := mem_filter.mp hq
  obtain ⟨hd,hpos⟩ := Nat.mem_divisors.mp div
  exact ⟨pp,n,hn,hpos,hd,copr⟩
lemma solve (z : ℕ) : ∀ᶠ N : ℕ in atTop,
  ∀ (A : Finset ℕ) (u v : ℕ), 1≤u → u≤v → 2≤v → v≤z → 0∉A → A ⊆ range N →
  (∀ n ∈ A, Param299.M N ≤ n ∧
    (∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ) ≤ (N:ℝ)^(1-8/Param299.w N)) ∧
    (99/100:ℝ)*Param299.w N ≤ n.primeFactors.card ∧ (n.primeFactors.card:ℝ) ≤ 2*Param299.w N) →
  2/(u:ℝ) + 1/(10*(z:ℝ)) ≤ mass A →
  (∀ n ∈ A, ∃ d ∈ Icc u v, d∣n) →
  ∃ B⊆A, ∃ d ∈ Icc u v,
    (mass B < 2/(d:ℝ) ∧ 2/(d:ℝ)-1/Param299.M N ≤ mass B ∧ d∣B.lcm id ∧
      ∀ q ∈ powers B, Param299.e N ≤ ∑ n ∈ part B q, (q:ℝ)/n) ∧
    ∀ n ∈ B, ∀ j : ℕ, j∣n → u≤j → d≤j := by
  classical
  let δ : ℝ := 1/(100*((z:ℝ)+1)^2)
  have hδ : 0<δ := by dsimp [δ]; positivity
  filter_upwards [Param299.params δ hδ] with N hN
  intro A u v hu huv hv hvz h0 hAN reg massA divs
  obtain ⟨he,hM,inv,scale,cost⟩ := hN
  let P := powers A
  let e := Param299.e N
  let M := Param299.M N
  have zr : (2:ℝ)≤z := by exact_mod_cast hv.trans hvz
  have zp : (0:ℝ)<z := by linarith
  have sep : δ≤1/(10*(z:ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [sq_nonneg (z:ℝ)]
  have powersP (q : ℕ) (hq : q∈P) : IsPrimePow q ∧ q≤N ∧ (q:ℝ)≤e*M := by
    obtain ⟨pp,n,hn,hn0,hr⟩ := powers_mem hq
    exact ⟨pp,(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hr.1).trans (mem_range.mp (hAN hn)).le,
      ((reg n hn).2.1 q pp hr.1).trans scale⟩
  have hcost := cost P fun q hq => ⟨(powersP q hq).1,(powersP q hq).2.1⟩
  change e*mass P<δ at hcost
  have hP (q : ℕ) (hq : q∈P) : 0<q ∧ (q:ℝ)≤e*M :=
    ⟨(powersP q hq).1.pos,(powersP q hq).2.2⟩
  have target (d : ℕ) (hd : d ∈ Icc u v) : 2*δ<2/(d:ℝ) := by
    have dp : (0:ℝ)<d := by exact_mod_cast (show 0<d from Nat.lt_of_lt_of_le (by omega) (mem_Icc.mp hd).1)
    have dz : (d:ℝ)≤z := by exact_mod_cast (mem_Icc.mp hd).2.trans hvz
    have tmp : δ<1/(d:ℝ) := by
      apply one_div_lt_one_div_of_lt dp
      nlinarith [sq_nonneg (z:ℝ)]
    calc 2*δ < 2*(1/(d:ℝ)) := mul_lt_mul_of_pos_left tmp (by norm_num)
         _ = 2/d := by ring
  let can (d : ℕ) : Prop := ∃ B⊆A, stable P B e ∧ mass B<2/(d:ℝ) ∧
    2/(d:ℝ)-1/M≤ mass B ∧ ∀ n ∈ B, ∀ j : ℕ, j∣n → u≤j → d≤j
  let D := (Icc u v).filter can
  have huI := mem_Icc.mpr (show u≤u ∧ u≤v from ⟨le_rfl,huv⟩)
  obtain ⟨S,hS,gs,ms,mS⟩ := trim P A e M (2/u) he.le hM hP (fun n hn => (reg n hn).1)
    (by linarith [target u huI]) (by linarith)
  have ud : u∈D := mem_filter.mpr ⟨huI,S,hS,gs,ms,mS,fun n hn j hj hju => hju⟩
  let d := D.max' ⟨u,ud⟩
  have hd : d∈D := max'_mem _ _
  obtain ⟨hdi,B,hB,gb,mb,mB,minB⟩ := mem_filter.mp hd
  have dr : (0:ℝ)<d := by exact_mod_cast (show 0<d by have := (mem_Icc.mp hdi).1; omega)
  have exist : ∃ n ∈ B, d∣n := by
    by_contra! none
    have Bpos : 0 < mass B := by
      change 1/M<δ at inv
      linarith [target d hdi]
    obtain ⟨n,hn⟩ := nonempty_of_ne_empty (s:=B) (fun eq => by simp [eq,mass] at Bpos)
    obtain ⟨j,hj,hjn⟩ := divs n (hB hn)
    have jmin := minB n hn j hjn (mem_Icc.mp hj).1
    have jne : j≠d := by rintro rfl; exact none n hn hjn
    have hs : d+1 ∈ Icc u v := mem_Icc.mpr ⟨by have := (mem_Icc.mp hdi).1; omega,
      by have := (mem_Icc.mp hj).2; omega⟩
    have ds : (0:ℝ)<(d:ℝ)+1 := by linarith
    have dz : (d:ℝ)+1≤z := by exact_mod_cast (mem_Icc.mp hs).2.trans hvz
    have gap : 2*δ ≤ 2/(d:ℝ)-2/((d:ℝ)+1) := by
      have big : (d:ℝ)*((d:ℝ)+1) ≤ 100*((z:ℝ)+1)^2 := by
        nlinarith [mul_le_mul (show (d:ℝ)≤(z:ℝ)+1 by linarith) (show (d:ℝ)+1≤(z:ℝ)+1 by linarith) ds.le (by positivity : 0≤(z:ℝ)+1),sq_nonneg ((z:ℝ)+1)]
      have u' := one_div_le_one_div_of_le (mul_pos dr ds) big
      change δ≤1/((d:ℝ)*((d:ℝ)+1)) at u'
      calc 2*δ ≤ 2*(1/((d:ℝ)*((d:ℝ)+1))) := by linarith
           _ = _ := by field_simp; ring
    obtain ⟨C,hC,gC,mc,mC⟩ := trim P B e M (2/((d+1:ℕ):ℝ)) he.le hM hP
      (fun n hn => (reg n (hB hn)).1) (by linarith [target (d+1) hs])
      (by push_cast; change 1/M<δ at inv; linarith)
    have next : d+1 ∈ D := mem_filter.mpr ⟨hs,C,hC.trans hB,gC,mc,mC,by
      intro n hn j hj hju
      have le := minB n (hC hn) j hj hju
      have ne : j≠d := by rintro rfl; exact none n (hC hn) hj
      omega⟩
    have le := le_max' D (d+1) next
    change d+1≤d at le
    omega
  obtain ⟨x,hx,hdx⟩ := exist
  refine ⟨B,hB,d,hdi,⟨mb,mB,hdx.trans (dvd_lcm hx),?_⟩,minB⟩
  intro q hq
  obtain ⟨pp,n,hn,h0,hr⟩ := powers_mem hq
  have qp : q∈P := mem_biUnion.mpr ⟨n,hB hn,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hr.1,h0⟩,pp,hr.2⟩⟩
  have h := gb q (mem_filter.mpr ⟨qp,⟨n,mem_filter.mpr ⟨hn,hr⟩⟩⟩)
  have qr : (0:ℝ)<q := by exact_mod_cast (hP q qp).1
  have hh := (div_le_iff₀ qr).mp h
  calc e ≤ mass (part B q)*(q:ℝ) := hh
       _ = ∑ n ∈ part B q, (q:ℝ)/n := by rw [mass,sum_mul]; apply sum_congr rfl; intro n hn; ring
end Prune299
end

theorem OMA.solution : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H1 := by
  classical
  intro z
  filter_upwards [Prune299.solve z] with N hN
  intro A u v hu huv hv hvz h0 hAN reg massA divs
  obtain ⟨B,hB,d,hd,⟨lo,hi,dvd,localSum⟩,minimal⟩ :=
    hN A u v hu huv hv hvz h0 hAN reg massA divs
  refine ⟨B,hB,d,hd,⟨lo,hi,dvd,?_⟩,minimal⟩
  intro q hq
  have hp : q ∈ Prune299.powers B := by simpa [Prune299.powers] using hq
  have eq : Prune299.part B q = B.filter (fun n => q∣n ∧ Nat.Coprime q (n/q)) := by
    ext n
    simp [Prune299.part,Prune299.rel]
  simpa only [eq] using localSum q hp
