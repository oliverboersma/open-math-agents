import OMAReductions.R_Erdos308_erdos_308_variants_croot_R1_H2_R1
import Mathlib

/-! The first Mertens estimate is adapted from @marcusbuffett's merged
Erdős 1100 normal-order proof (d11bab2e5cca11149ef46efd98a8acd1f654c894),
which credits @senamakel. We integrate the weighted prime count over the
logarithmic window and bound the errors from the cofactor harmonic sum
and the change of logarithmic weight. -/
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
end OMALib.Mertens
end

namespace Croot308

open Finset Filter Real MeasureTheory
open scoped Topology

noncomputable def mass (N : ℕ) (t : ℝ) := ∑ p ∈ (Nat.primesLE N).filter
  (fun p : ℕ => log (N:ℝ) - log (p:ℝ) < t), log p / p

lemma mass_approx {C : ℝ} (hC : ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C)
    (N : ℕ) (t : ℝ) (ht : 0 ≤ t) (hn : 2 ≤ exp (log N-t)) :
    |mass N t-t| ≤ 2*C := by
  classical
  let v := exp (log N-t)
  have Npos : (0:ℝ) < N := by
    by_contra! hh
    have nz : N=0 := by exact_mod_cast (le_antisymm hh (Nat.cast_nonneg N))
    subst N
    simp only [Nat.cast_zero,log_zero,zero_sub] at hn
    have := exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    linarith
  have vN : v ≤ N := (exp_le_exp.mpr (sub_le_self _ ht)).trans_eq (exp_log Npos)
  have v2 : 2 ≤ v := hn
  have n2 : 2 ≤ (N:ℝ) := v2.trans vN
  have parts := sum_filter_add_sum_filter_not (Nat.primesLE N)
    (fun p : ℕ => log (N:ℝ) - log (p:ℝ) < t) (fun p : ℕ => log p / p)
  have rem : (Nat.primesLE N).filter (fun p : ℕ => ¬ log (N:ℝ)-log (p:ℝ)<t) = Nat.primesLE ⌊v⌋₊ := by
    ext p
    simp only [mem_filter,Nat.mem_primesLE,not_lt]
    constructor
    · rintro ⟨⟨_,hp⟩,hl⟩
      refine ⟨(Nat.le_floor_iff (exp_pos _).le).mpr ?_,hp⟩
      rw [← exp_log (by exact_mod_cast hp.pos : (0:ℝ)<p)]
      exact exp_le_exp.mpr (by linarith)
    · rintro ⟨h,hp⟩
      have pv : (p:ℝ) ≤ v := (Nat.le_floor_iff (exp_pos _).le).mp h
      have l := log_le_log (by exact_mod_cast hp.pos : (0:ℝ)<p) pv
      rw [show log v = log N-t from log_exp _] at l
      exact ⟨⟨by exact_mod_cast pv.trans vN,hp⟩,by linarith⟩
  rw [rem] at parts
  change mass N t + _ = _ at parts
  have big := abs_le.mp (hC N n2)
  rw [Nat.floor_natCast] at big
  have small := abs_le.mp (hC v v2)
  rw [show log v = log N-t from log_exp _] at small
  rw [abs_le]
  constructor <;> linarith

private lemma first_moment {P : Finset ℕ} (x w : ℕ → ℝ) (T D : ℝ) (ht : 0 ≤ T)
    (hx : ∀ p ∈ P, 0 ≤ x p ∧ x p < T)
    (approx : ∀ s ∈ Set.Icc 0 T, |(∑ p ∈ P.filter (fun p => x p<s), w p)-s| ≤ D) :
    |(∑ p ∈ P, x p*w p)-T^2/2| ≤ 2*T*D := by
  classical
  let f (p : ℕ) := (Set.Ioi (x p)).indicator (fun _ : ℝ => w p)
  let F (s : ℝ) := ∑ p ∈ P, f p s
  have fi (p : ℕ) : IntegrableOn (f p) (Set.Ioc 0 T) :=
    (integrableOn_const (C := w p) (by simp) (by finiteness)).indicator measurableSet_Ioi
  have fint : IntegrableOn F (Set.Ioc 0 T) := integrable_finsetSum _ (fun p _ => fi p)
  have fval (s : ℝ) : F s = ∑ p ∈ P.filter (fun p => x p<s), w p := by
    simp [F,f,Set.indicator,Finset.sum_filter]
  have hint : ∫ s in Set.Ioc 0 T, F s = ∑ p ∈ P,(T-x p)*w p := by
    change (∫ s in Set.Ioc 0 T, ∑ p ∈ P,f p s) = _
    rw [integral_finsetSum _ (fun p _ => fi p)]
    apply sum_congr rfl
    intro p hp
    rw [show (∫ s in Set.Ioc 0 T,f p s) = ∫ s in Set.Ioc 0 T ∩ Set.Ioi (x p), w p from
      setIntegral_indicator measurableSet_Ioi]
    have eq : Set.Ioc 0 T ∩ Set.Ioi (x p) = Set.Ioc (x p) T := by
      ext s
      simp only [Set.mem_inter_iff,Set.mem_Ioc,Set.mem_Ioi]
      constructor
      · rintro ⟨⟨_,h⟩,h'⟩; exact ⟨h',h⟩
      · rintro ⟨h,h'⟩; exact ⟨⟨(hx p hp).1.trans_lt h,h'⟩,h⟩
    rw [eq,setIntegral_const,Real.volume_real_Ioc_of_le (hx p hp).2.le,smul_eq_mul]
  have Fi : IntervalIntegrable F volume 0 T := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr fint
  have hh (s : ℝ) (hs : s ∈ Set.Icc 0 T) := abs_le.mp (approx s hs)
  have lo := intervalIntegral.integral_mono_on ht ((continuous_id.sub continuous_const).intervalIntegrable _ _) Fi
    (show ∀ s ∈ Set.Icc 0 T, s-D ≤ F s by intro s hs; rw [fval]; linarith [(hh s hs).1])
  have hi := intervalIntegral.integral_mono_on ht Fi ((continuous_id.add continuous_const).intervalIntegrable _ _)
    (show ∀ s ∈ Set.Icc 0 T, F s ≤ s+D by intro s hs; rw [fval]; linarith [(hh s hs).2])
  change (∫ s in (0:ℝ)..T,s-D) ≤ _ at lo
  change _ ≤ (∫ s in (0:ℝ)..T,s+D) at hi
  rw [intervalIntegral.integral_sub (f := fun y : ℝ => y) (g := fun _ : ℝ => D) (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    integral_id,intervalIntegral.integral_const,intervalIntegral.integral_of_le ht,hint] at lo
  rw [intervalIntegral.integral_add (f := fun y : ℝ => y) (g := fun _ : ℝ => D) (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    integral_id,intervalIntegral.integral_const,intervalIntegral.integral_of_le ht,hint] at hi
  simp only [sub_mul,sum_sub_distrib,←mul_sum,zero_pow (by decide : 2≠0),sub_zero,smul_eq_mul] at lo hi
  have atT : |(∑ p ∈ P,w p)-T| ≤ D := by
    simpa [Finset.filter_true_of_mem (fun p hp => (hx p hp).2)] using
      approx T ⟨ht,le_rfl⟩
  obtain ⟨tl,tu⟩ := abs_le.mp atT
  rw [abs_le]
  constructor <;> nlinarith only [lo,hi,mul_le_mul_of_nonneg_left tl ht,mul_le_mul_of_nonneg_left tu ht]
private lemma estimate {C : ℝ} (hC : ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C)
    (N : ℕ) (T : ℝ) (nt : 0 < (N:ℝ)) (t0 : 0 ≤ T)
    (nlarge : 2 ≤ exp (log N-T)) (large : T^2+2*T ≤ log N) :
    let P := (Nat.primesLE N).filter (fun p : ℕ => log N-log p<T)
    |(∑ p ∈ P,(harmonic (N/p):ℝ)/p)*log N-T^2/2| ≤ 4*T*C+2*(T+2*C) := by
  classical
  intro P
  let x (p : ℕ) := log N-log p
  let w (p : ℕ) := log p/p
  have mem {p : ℕ} (hp : p ∈ P) : p≤N ∧ p.Prime ∧ x p<T := by
    obtain ⟨hp,ht⟩ := mem_filter.mp hp
    obtain ⟨pN,pr⟩ := Nat.mem_primesLE.mp hp
    exact ⟨pN,pr,ht⟩
  have xrange (p : ℕ) (hp : p ∈ P) : 0 ≤ x p ∧ x p<T := by
    obtain ⟨pN,pr,ht⟩ := mem hp
    exact ⟨sub_nonneg.mpr (log_le_log (by exact_mod_cast pr.pos) (by exact_mod_cast pN)),ht⟩
  have m (s : ℝ) (hs : s ∈ Set.Icc 0 T) : |(∑ p ∈ P.filter (fun p => x p<s),w p)-s| ≤ 2*C := by
    have e : P.filter (fun p => x p<s) = (Nat.primesLE N).filter (fun p => x p<s) := by
      ext p
      simp only [P,mem_filter]
      exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.trans_le hs.2⟩,h.2⟩⟩
    rw [e]
    exact mass_approx hC N s hs.1 (nlarge.trans (exp_le_exp.mpr (by linarith [hs.2])))
  have W := first_moment x w T (2*C) t0 xrange m
  have mT := abs_le.mp (mass_approx hC N T t0 nlarge)
  change _ ∧ (∑ p ∈ P,w p)-T ≤ 2*C at mT
  have per (p : ℕ) (hp : p ∈ P) :
      x p*w p ≤ ((harmonic (N/p):ℝ)/p)*log N ∧
      ((harmonic (N/p):ℝ)/p)*log N ≤ x p*w p+2*w p := by
    obtain ⟨pN,pr,hxt⟩ := mem hp
    have pp : 0 < (p:ℝ) := by exact_mod_cast pr.pos
    have pn : (p:ℝ) ≤ N := by exact_mod_cast pN
    have lo := log_le_harmonic_floor ((N:ℝ)/p) (by positivity)
    have hi := harmonic_floor_le_one_add_log ((N:ℝ)/p) ((one_le_div pp).mpr pn)
    rw [Nat.floor_div_natCast,Nat.floor_natCast,log_div nt.ne' pp.ne'] at lo hi
    change x p ≤ _ at lo
    change _ ≤ 1+x p at hi
    have xp := (xrange p hp).1
    have lp := log_nonneg (show 1 ≤ (p:ℝ) by exact_mod_cast pr.one_le)
    have lN := log_nonneg (show 1 ≤ (N:ℝ) by linarith [show 1 ≤ (p:ℝ) by exact_mod_cast pr.one_le])
    have xeq : x p=log N-log p := rfl
    have sq : (x p)^2 ≤ T^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hxt.le) (add_nonneg t0 xp)]
    change x p*(log p/p) ≤ _ ∧ _ ≤ x p*(log p/p)+2*(log p/p)
    constructor
    · apply (mul_le_mul_iff_of_pos_right pp).mp
      field_simp
      nlinarith only [mul_le_mul_of_nonneg_right lo lN,mul_nonneg xp (sub_nonneg.mpr (show log p≤log N by linarith [xeq]))]
    · apply (mul_le_mul_iff_of_pos_right pp).mp
      field_simp
      nlinarith only [mul_le_mul_of_nonneg_right hi lN,sq,large,xeq,hxt.le,
        congrArg (fun y => x p*y) xeq]
  have bot := sum_le_sum (fun p hp => (per p hp).1)
  have top := sum_le_sum (fun p hp => (per p hp).2)
  rw [←sum_mul] at bot top
  rw [sum_add_distrib,←mul_sum] at top
  obtain ⟨wl,wu⟩ := abs_le.mp W
  rw [abs_le]
  have c0 := (abs_nonneg _).trans (hC 2 le_rfl)
  constructor <;> nlinarith only [wl,wu,mT.2,bot,top,c0,t0]

lemma profile (a : ℝ) (a0 : 0<a) (a2 : a<2) {C : ℝ}
    (hC : ∀ x : ℝ, 2 ≤ x → |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ C) :
    Tendsto (fun N : ℕ => (∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*(log N)^a),
      (harmonic (N/p):ℝ)/p)*log N/(log (log N))^2) atTop (𝓝 (a^2/2)) := by
  classical
  let L (N : ℕ) := log (N:ℝ)
  let w (N : ℕ) := log (L N)
  have hl : Tendsto L atTop atTop := tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hw : Tendsto w atTop atTop := tendsto_log_atTop.comp hl
  have c0 := (abs_nonneg _).trans (hC 2 le_rfl)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hw.eventually_gt_atTop 60,hl.eventually_gt_atTop 0,eventually_gt_atTop 0,
      hw.eventually_gt_atTop ((4*a*C+2*a+4*C)/ε)] with N hw60 hL hn hδ
  let T := a*w N
  have wp : 0 < w N := by linarith
  have tpos : 0 ≤ T := mul_nonneg a0.le wp.le
  have tsmall : T ≤ 2*w N := mul_le_mul_of_nonneg_right a2.le wp.le
  have ol := Real.pow_div_factorial_le_exp (w N) wp.le 3
  rw [show exp (w N) = L N from exp_log hL] at ol
  norm_num at ol
  have big : T^2+2*T ≤ L N := by
    have ss := sq_le_sq' (by linarith : -(2*w N) ≤ T) tsmall
    nlinarith only [ss,tsmall,ol,mul_nonneg (show 0≤w N-60 by linarith) (sq_nonneg (w N)),
      mul_nonneg wp.le (show 0≤w N-1 by linarith)]
  have two : 2 ≤ exp (L N-T) := by
    have oo := Real.add_one_le_exp (L N-T)
    nlinarith only [oo,ol,tsmall,hw60,mul_nonneg (show 0≤w N-60 by linarith) (sq_nonneg (w N)),
      sq_nonneg (w N-1)]
  have np : 0 < (N:ℝ) := by exact_mod_cast hn
  have est := estimate hC N T np tpos two big
  have eq : (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*(log N)^a) =
      (Nat.primesLE N).filter (fun p : ℕ => log N-log p<T) := by
    apply filter_congr
    intro p hp
    have pp : (0:ℝ)<p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
    rw [← log_lt_log_iff np (mul_pos pp (rpow_pos_of_pos hL a)),log_mul pp.ne' (rpow_pos_of_pos hL a).ne',
      log_rpow hL]
    change log N<log p+a*w N ↔ log N-log p<a*w N
    constructor <;> intro h <;> linarith
  change dist (_ / (w N)^2) (a^2/2)<ε
  rw [eq,Real.dist_eq,div_sub' (pow_ne_zero 2 wp.ne'),abs_div,abs_of_pos (sq_pos_of_pos wp)]
  apply (div_lt_iff₀ (sq_pos_of_pos wp)).mpr
  rw [show (w N)^2*(a^2/2)=T^2/2 by dsimp [T]; ring]
  apply lt_of_le_of_lt est
  have eps := (div_lt_iff₀ hε).mp hδ
  have cut := mul_lt_mul_of_pos_right eps wp
  dsimp [T]
  nlinarith only [cut, mul_nonneg c0 (show 0 ≤ w N-1 by linarith)]

end Croot308

theorem OMA.solution : OMA.R_Erdos308_erdos_308_variants_croot_R1_H2_R1.H1 := by
  obtain ⟨C,hC⟩ := OMALib.Mertens.mertens1
  exact fun a ha hb => Croot308.profile a ha hb hC
