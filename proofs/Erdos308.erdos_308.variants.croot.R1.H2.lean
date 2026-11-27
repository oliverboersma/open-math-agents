import OMAReductions.R_Erdos308_erdos_308_variants_croot_R1
import Mathlib

/-!
# The reciprocal mass excluded by the large prime factorial obstruction

The first Mertens estimate is adapted from @senamakel's merged Erdős 962 proof
(open-math-agents commit d757b84b7870c7b80a9e62d5e93a293328aee0d4),
as reused in @marcusbuffett's Erdős 377 proof. All subsequent arguments are new.

Integrating Mertens' bounded error over a logarithmic window gives its
weighted first moment. Harmonic cofactor weights have the same main term.
The factorial cutoff lies between the exponents 1 − d and 1 + d, and
distinct eligible primes never divide the same denominator.
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

end OMALib.Mertens

open Filter Finset MeasureTheory Real
open scoped Classical Topology
namespace Window308
noncomputable def primes (b : ℝ) := Nat.primesLE ⌊exp b⌋₊
noncomputable def band (l b : ℝ) := primes b \ primes l
noncomputable abbrev weight (p : ℕ) := log p/(p:ℝ)
noncomputable abbrev raw (l b : ℝ) := ∑ p ∈ band l b, weight p
noncomputable abbrev moment (l b : ℝ) := ∑ p ∈ band l b, (b-log p)*weight p
lemma mem_primes {p : ℕ} {b : ℝ} : p∈primes b ↔ p.Prime ∧ log p≤b := by
  rw [primes,Nat.mem_primesLE]
  constructor
  · rintro ⟨le,pp⟩
    have hp : 0<(p:ℝ) := by exact_mod_cast pp.pos
    exact ⟨pp,(log_le_iff_le_exp hp).mpr ((Nat.le_floor_iff (exp_pos b).le).mp le)⟩
  · rintro ⟨pp,le⟩
    have hp : 0<(p:ℝ) := by exact_mod_cast pp.pos
    exact ⟨Nat.le_floor ((log_le_iff_le_exp hp).mp le),pp⟩
lemma mem_band {p : ℕ} {l b : ℝ} : p∈band l b ↔ p.Prime ∧ l<log p ∧ log p≤b := by
  change p∈primes b \ primes l ↔ _
  rw [Finset.mem_sdiff,mem_primes,mem_primes]
  constructor
  · rintro ⟨⟨pp,hi⟩,hn⟩
    exact ⟨pp,lt_of_not_ge (fun h => hn ⟨pp,h⟩),hi⟩
  · rintro ⟨pp,h,hi⟩
    exact ⟨⟨pp,hi⟩,fun h' => h.not_ge h'.2⟩
lemma raw_error : ∃ C : ℝ, 0≤C ∧ ∀ l b : ℝ, log 2≤l → l≤b → |raw l b-(b-l)|≤C := by
  obtain ⟨c,hc⟩ := OMALib.Mertens.mertens1
  have cp := (abs_nonneg _).trans (hc 2 le_rfl)
  refine ⟨2*c,by linarith,?_⟩
  intro l b hl h
  have he (t : ℝ) (ht : log 2≤t) : |(∑ p ∈ primes t,weight p)-t|≤c := by
    have h2 : 2≤exp t := (log_le_iff_le_exp (by norm_num : (0:ℝ)<2)).mp ht
    simpa only [primes,weight,log_exp] using hc (exp t) h2
  have sub : primes l ⊆ primes b := fun p hp =>
    mem_primes.mpr ⟨(mem_primes.mp hp).1,(mem_primes.mp hp).2.trans h⟩
  have eq := sum_sdiff sub (f:=weight)
  change raw l b+(∑ p ∈ primes l,weight p)=∑ p ∈ primes b,weight p at eq
  have hl' := abs_le.mp (he l hl)
  have hb' := abs_le.mp (he b (hl.trans h))
  exact abs_le.mpr ⟨by linarith [hl'.1,hl'.2,hb'.1,hb'.2],by linarith [hl'.1,hl'.2,hb'.1,hb'.2]⟩
lemma moment_error {C : ℝ} (err : ∀ l b : ℝ, log 2≤l → l≤b → |raw l b-(b-l)|≤C)
    {l b : ℝ} (hl : log 2≤l) (hlb : l≤b) :
    |moment l b-(b-l)^2/2| ≤ C*(b-l) := by
  classical
  let Y := b-l
  have hY : 0≤Y := sub_nonneg.mpr hlb
  let v (p : ℕ) (u : ℝ) := (Set.Iic (b-log p)).indicator (fun _ => weight p) u
  let cum (u : ℝ) := ∑ p ∈ band l b, v p u
  have intv (p : ℕ) : IntervalIntegrable (v p) volume 0 Y := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hY).mpr
    exact (integrableOn_const (C:=weight p) (hs:=measure_Ioc_lt_top.ne)).indicator measurableSet_Iic
  have intc : IntervalIntegrable cum volume 0 Y := by
    have go (S : Finset ℕ) : IntervalIntegrable (fun u => ∑ p ∈ S, v p u) volume 0 Y := by
      induction S using Finset.induction_on with
      | empty => simpa using (intervalIntegrable_const (μ:=volume) (a:=0) (b:=Y) (c:=(0:ℝ)))
      | insert p S hp ih => simpa only [sum_insert hp] using (intv p).add ih
    exact go _
  have iMoment : (∫ u in 0..Y, cum u) = moment l b := by
    dsimp only [cum]
    rw [intervalIntegral.integral_finsetSum (fun p _ => intv p)]
    apply sum_congr rfl
    intro p hp
    obtain ⟨_,lo,hi⟩ := mem_band.mp hp
    have hv : b-log p ∈ Set.Icc 0 Y := ⟨by linarith,by dsimp [Y];linarith⟩
    change (∫ u in (0:ℝ)..Y, Set.indicator {u : ℝ | u≤b-log p} (fun _ => weight p) u) = _
    rw [intervalIntegral.integral_indicator hv,intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  have point (u : ℝ) (hu : u∈Set.Icc 0 Y) : |cum u-(Y-u)|≤C := by
    have sub : (band l b).filter (fun p : ℕ => u≤b-log p) = band l (b-u) := by
      ext p
      simp only [mem_filter,mem_band]
      have h0 := hu.1
      constructor
      · rintro ⟨⟨pp,h₁,h₂⟩,h₃⟩; exact ⟨pp,h₁,by linarith⟩
      · rintro ⟨pp,h₁,h₂⟩; exact ⟨⟨pp,h₁,by linarith⟩,by linarith⟩
    have e : cum u=raw l (b-u) := by
      dsimp only [cum,v,raw]
      rw [←sub,sum_filter]
      apply sum_congr rfl
      intro p hp
      by_cases h : u≤b-log p <;> simp [Set.indicator,Set.mem_Iic,h]
    rw [e,show Y-u=b-u-l by dsimp [Y];ring]
    apply err _ _ hl
    have : u≤b-l := hu.2
    linarith
  have linear : IntervalIntegrable (fun u : ℝ => Y-u) volume 0 Y :=
    (continuous_const.sub continuous_id).intervalIntegrable _ _
  have ilin : (∫ u in 0..Y,Y-u) = Y^2/2 := by
    rw [intervalIntegral.integral_sub (f:=fun _ : ℝ => Y) (g:=fun t : ℝ => t) intervalIntegrable_const (continuous_id.intervalIntegrable _ _),
      intervalIntegral.integral_const,integral_id]
    simp only [sub_zero,smul_eq_mul,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow]
    ring
  have ide : (∫ u in 0..Y,cum u-(Y-u)) = moment l b-Y^2/2 := by
    rw [intervalIntegral.integral_sub intc linear,iMoment,ilin]
  change |moment l b-Y^2/2|≤C*Y
  rw [←ide]
  calc _ ≤ ∫ u in 0..Y,|cum u-(Y-u)| := intervalIntegral.abs_integral_le_integral_abs hY
       _ ≤ ∫ _ in (0:ℝ)..Y,C := intervalIntegral.integral_mono_on hY (intc.sub linear).abs
             intervalIntegrable_const point
       _ = _ := by simp [mul_comm]
end Window308

open Filter Finset Real
open scoped Classical Topology
namespace Window308
noncomputable abbrev L (N : ℕ) := log (N:ℝ)
noncomputable abbrev W (N : ℕ) := log (L N)
noncomputable abbrev lo (a : ℝ) (N : ℕ) := L N-a*W N
noncomputable abbrev harmonicMass (a : ℝ) (N : ℕ) := ∑ p ∈ band (lo a N) (L N),
  (harmonic (N/p):ℝ)/p
lemma band_nat {N : ℕ} (hN : 1<N) (a : ℝ) : band (lo a N) (L N) =
    (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*(log N)^a) := by
  have hn : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hL : 0<log (N:ℝ) := log_pos (by exact_mod_cast hN)
  ext p
  rw [mem_band,mem_filter,Nat.mem_primesLE]
  by_cases pp : p.Prime
  · have hp : 0<(p:ℝ) := by exact_mod_cast pp.pos
    have e : lo a N < log p ↔ (N:ℝ)<p*(log N)^a := by
      rw [← Real.log_lt_log_iff hn (mul_pos hp (rpow_pos_of_pos hL _)),Real.log_mul hp.ne' (rpow_pos_of_pos hL _).ne',
        Real.log_rpow hL]
      dsimp [lo,L,W]; constructor <;> intro h <;> linarith
    have e' : log (p:ℝ)≤L N ↔ p≤N := by
      rw [L,Real.log_le_log_iff hp hn,Nat.cast_le]
    simp [e,e',pp,and_comm]
  · simp [pp]
lemma harmonic_bounds (N : ℕ) (hN : 1<N) (a : ℝ) (hl : 0≤lo a N) :
    moment (lo a N) (L N) ≤ harmonicMass a N*L N ∧
    harmonicMass a N*lo a N ≤ moment (lo a N) (L N)+raw (lo a N) (L N) := by
  have h (p : ℕ) (hp : p ∈ band (lo a N) (L N)) :
      (L N-log p)*weight p ≤ (harmonic (N/p):ℝ)/p*L N ∧
      (harmonic (N/p):ℝ)/p*lo a N ≤ (L N-log p)*weight p+weight p := by
    obtain ⟨pr,lo',up⟩ := mem_band.mp hp
    have pos : 0<(p:ℝ) := by exact_mod_cast pr.pos
    have npos : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
    have pN : (p:ℝ)≤N := (log_le_log_iff pos npos).mp up
    have ratio : 1≤(N:ℝ)/p := (one_le_div pos).mpr pN
    have fl : ⌊(N:ℝ)/p⌋₊=N/p := by rw [Nat.floor_div_natCast,Nat.floor_natCast]
    have low := log_le_harmonic_floor ((N:ℝ)/p) (by positivity)
    have high := harmonic_floor_le_one_add_log ((N:ℝ)/p) ratio
    rw [fl,log_div npos.ne' pos.ne'] at low high
    change L N-log p ≤ (harmonic (N/p):ℝ) at low
    change (harmonic (N/p):ℝ) ≤ 1+(L N-log p) at high
    have lg := hl.trans lo'.le
    have diff : 0≤L N-log p := sub_nonneg.mpr up
    constructor
    · unfold weight
      rw [mul_div_assoc',div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ pos.le
      exact mul_le_mul low up lg (diff.trans low)
    · unfold weight
      rw [div_mul_eq_mul_div,mul_div_assoc',←add_div]
      apply div_le_div_of_nonneg_right _ pos.le
      calc _ ≤ (1+(L N-log p))*log p := mul_le_mul high lo'.le hl (by linarith)
           _ = _ := by ring
  constructor
  · change _ ≤ (∑ p ∈ band (lo a N) (L N), (harmonic (N/p):ℝ)/p)*L N
    rw [sum_mul]
    exact sum_le_sum fun p hp => (h p hp).1
  · change (∑ p ∈ band (lo a N) (L N), (harmonic (N/p):ℝ)/p)*lo a N ≤
        (∑ p ∈ band (lo a N) (L N), (L N-log p)*weight p)+∑ p ∈ band (lo a N) (L N),weight p
    rw [sum_mul,←sum_add_distrib]
    exact sum_le_sum fun p hp => (h p hp).2
lemma limit (a : ℝ) (ha : 0<a) :
    Tendsto (fun N : ℕ => (∑ p ∈ (Nat.primesLE N).filter (fun p : ℕ => (N:ℝ)<p*(log N)^a),
      (harmonic (N/p):ℝ)/p)*log N/(log (log N))^2) atTop (𝓝 (a^2/2)) := by
  have ltop : Tendsto L atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have wtop : Tendsto W atTop atTop := tendsto_log_atTop.comp ltop
  have ratio : Tendsto (fun N : ℕ => W N/L N) atTop (𝓝 0) := by
    simpa only [Function.comp_def,W,one_mul,add_zero,pow_one] using
      (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp ltop
  have invw : Tendsto (fun N : ℕ => (W N)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp wtop
  have rr : Tendsto (fun N : ℕ => 1-a*(W N/L N)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (ratio.const_mul a)
  have poslo : ∀ᶠ N : ℕ in atTop, log 2 ≤ lo a N := by
    filter_upwards [rr.eventually_const_lt (show (1/2:ℝ)<1 by norm_num),
      ltop.eventually_gt_atTop (2*log 2)] with N r hL
    have lp : 0<L N := by linarith [log_pos one_lt_two]
    have hh := mul_lt_mul_of_pos_right r lp
    field_simp [lp.ne'] at hh
    dsimp only [lo]; nlinarith
  have lr : Tendsto (fun N : ℕ => L N/lo a N) atTop (𝓝 1) := by
    have hh := rr.inv₀ (by norm_num : (1:ℝ)≠0)
    apply (show Tendsto (fun N => (1-a*(W N/L N))⁻¹) atTop (𝓝 1) by simpa using hh).congr'
    filter_upwards [ltop.eventually_gt_atTop 0,poslo] with N hL hlo
    have hll : 0<lo a N := (log_pos one_lt_two).trans_le hlo
    dsimp only [lo] at hll ⊢
    field_simp
  obtain ⟨C,hC,err⟩ := raw_error
  let low (N : ℕ) := a^2/2-C*a*(W N)⁻¹
  let high (N : ℕ) := (a^2/2 + (C*a+a)*(W N)⁻¹+C*((W N)⁻¹)^2)*(L N/lo a N)
  have ll : Tendsto low atTop (𝓝 (a^2/2)) := by
    simpa [low] using (tendsto_const_nhds (x:=a^2/2)).sub (invw.const_mul (C*a))
  have hh : Tendsto high atTop (𝓝 (a^2/2)) := by
    simpa [high] using (((tendsto_const_nhds (x:=a^2/2)).add (invw.const_mul (C*a+a))).add
      ((invw.pow 2).const_mul C)).mul lr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ll hh
  all_goals filter_upwards [eventually_gt_atTop 1,poslo,wtop.eventually_gt_atTop 0] with N hn hl hw
  all_goals
    rw [←band_nat hn a]
    change _ ≤ _
    have hL : 0<L N := log_pos (by exact_mod_cast hn)
    have hlpos := (log_pos one_lt_two).trans_le hl
    have bandle : lo a N≤L N := sub_le_self _ (mul_nonneg ha.le hw.le)
    have gap : L N-lo a N = a*W N := by dsimp [lo];ring
    have me := abs_le.mp (moment_error err hl bandle)
    have re := abs_le.mp (err _ _ hl bandle)
    rw [gap] at me re
    have bh := harmonic_bounds N hn a hlpos.le
  · change low N ≤ harmonicMass a N*L N/(W N)^2
    apply (le_div_iff₀ (sq_pos_of_pos hw)).mpr
    have alg : low N*(W N)^2=(a*W N)^2/2-C*(a*W N) := by dsimp [low];field_simp <;> ring
    rw [alg]
    linarith only [bh.1,me.1]
  · change harmonicMass a N*L N/(W N)^2 ≤ high N
    have ub : harmonicMass a N*lo a N ≤ (a*W N)^2/2+C*(a*W N)+(a*W N)+C := by linarith only [bh.2,me.2,re.2]
    have mul := mul_le_mul_of_nonneg_right ub ((div_pos hL hlpos).le)
    have alg : high N*(W N)^2 = ((a*W N)^2/2+C*(a*W N)+(a*W N)+C)*(L N/lo a N) := by
      dsimp [high];field_simp;ring
    apply (div_le_iff₀ (sq_pos_of_pos hw)).mpr
    rw [alg]
    calc _ = harmonicMass a N*lo a N*(L N/lo a N) := by field_simp
         _ ≤ _ := mul
end Window308

open Filter Real Finset
open scoped Topology
namespace Factor308
lemma bounds (a b : ℝ) (ha : 0<a) (ha1 : a<1) (hb : 1<b) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ Nat.primesLE N,
    ((N:ℝ)<p*(log N)^a → (N/p)*(N/p).factorial<p) ∧
    ((N/p)*(N/p).factorial<p → (N:ℝ)<p*(log N)^b) := by
  let L (N : ℕ) := log (N:ℝ)
  let W (N : ℕ) := log (L N)
  have ltend : Tendsto L atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have sm : Tendsto (fun N => W N/(L N)^(1-a)) atTop (𝓝 0) := by
    simpa [Function.comp_def,W] using (isLittleO_log_rpow_atTop (sub_pos.mpr ha1)).tendsto_div_nhds_zero.comp ltend
  have grow := (tendsto_rpow_atTop (sub_pos.mpr hb)).comp ltend
  filter_upwards [sm.eventually_lt_const (show 0<1/(4*a) by positivity),ltend.eventually_gt_atTop 2,
      grow.eventually_gt_atTop (2+1/log 2),eventually_ge_atTop 2] with N small lg grow hn
  intro p hp
  obtain ⟨le,pp⟩ := Nat.mem_primesLE.mp hp
  have ppos : 0<(p:ℝ) := by exact_mod_cast pp.pos
  have npos : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  let j := N/p
  have jpos : 0<j := Nat.div_pos le pp.pos
  have jr : 0<(j:ℝ) := by exact_mod_cast jpos
  have j1 : 1≤(j:ℝ) := by exact_mod_cast jpos
  have jbound : (j:ℝ) ≤ (N:ℝ)/p := by
    apply (le_div_iff₀ ppos).mpr
    exact_mod_cast Nat.div_mul_le_self N p
  have jnext : (N:ℝ)/p < (j:ℝ)+1 := by
    rw [div_lt_iff₀ ppos]
    have h : N < (j+1)*p := by simpa only [j,Nat.mul_comm] using Nat.lt_mul_div_succ N pp.pos
    exact_mod_cast h
  have lpos : 0<L N := by linarith
  have la : 1≤(L N)^a := one_le_rpow (by linarith) ha.le
  have wpos : 0<W N := log_pos (by linarith)
  have scale : 4*a*W N*(L N)^a < L N := by
    have hs := (div_lt_div_iff₀ (rpow_pos_of_pos lpos (1-a)) (by positivity : 0<4*a)).mp small
    have hh := mul_lt_mul_of_pos_right hs (rpow_pos_of_pos lpos a)
    rw [one_mul,←rpow_add lpos,sub_add_cancel,rpow_one] at hh
    nlinarith only [hh]
  constructor
  · intro cut
    have jsmall : (j:ℝ)<(L N)^a := jbound.trans_lt ((div_lt_iff₀ ppos).mpr (by simpa [L,mul_comm] using cut))
    have jlog := log_le_log jr jsmall.le
    rw [log_rpow lpos] at jlog
    have hpoly : ((j:ℝ)+1)*log j < L N/2 := by
      have hs := mul_le_mul (show (j:ℝ)+1 ≤ 2*(L N)^a by linarith) jlog (log_nonneg j1) (by positivity)
      change ((j:ℝ)+1)*log j ≤ 2*(L N)^a*(a*W N) at hs
      nlinarith only [hs,scale]
    have pcut := log_lt_log npos cut
    rw [log_mul ppos.ne' (rpow_pos_of_pos lpos a).ne',log_rpow lpos] at pcut
    change L N < log p+a*W N at pcut
    have hwbound : a*W N<L N/2 := by nlinarith [mul_le_mul_of_nonneg_left la (mul_nonneg ha.le wpos.le)]
    have jp : j^(j+1)<p := by
      have h : log ((j:ℝ)^(j+1))<log (p:ℝ) := by rw [log_pow,Nat.cast_add,Nat.cast_one]; linarith
      exact_mod_cast (log_lt_log_iff (pow_pos jr _) ppos).mp h
    apply lt_of_le_of_lt _ jp
    rw [pow_succ]
    simpa [mul_comm] using Nat.mul_le_mul_left j (Nat.factorial_le_pow j)
  · intro cut
    have fac : 2^(j-1) ≤ j.factorial := by
      by_cases h : j=1
      · simp [h]
      · have hj : 2≤j := by omega
        have e : j-1=(j-2)+1 := by omega
        rw [e,pow_succ,mul_comm]
        simpa using (Nat.factorial_mul_pow_sub_le_factorial (n:=2) (m:=j) hj)
    have fp : j.factorial≤j*j.factorial := by simpa using Nat.mul_le_mul_right j.factorial (show 1≤j from jpos)
    have hpow : (2:ℝ)^(j-1) ≤ N := by exact_mod_cast (fac.trans (fp.trans (cut.le.trans le)))
    have logbd := log_le_log (by positivity) hpow
    rw [log_pow,Nat.cast_sub jpos,Nat.cast_one] at logbd
    change ((j:ℝ)-1)*log 2 ≤ L N at logbd
    have lp2 : 0<log 2 := log_pos one_lt_two
    have ju : (j:ℝ)-1 ≤ L N/log 2 := (le_div_iff₀ lp2).mpr logbd
    change 2+1/log 2 < (L N)^(b-1) at grow
    have big := mul_lt_mul_of_pos_left grow lpos
    have rpoweq : (L N)^(b-1)*L N=(L N)^b := by rw [←rpow_add_one lpos.ne',sub_add_cancel]
    rw [mul_comm _ ((L N)^(b-1)),rpoweq] at big
    have next : (j:ℝ)+1 < (L N)^b := by
      rw [mul_add,mul_one_div] at big
      linarith
    exact (div_lt_iff₀ ppos).mp (jnext.trans next) |>.trans_eq (mul_comm _ _)
end Factor308

open Real Filter Finset
open scoped Classical Topology
namespace Count308
noncomputable def eligible (N : ℕ) := (Nat.primesLE N).filter fun p => (N/p)*(N/p).factorial < p
lemma unique {N n p q : ℕ} (hn : n∈Icc 1 N) (hp : p∈eligible N) (hq : q∈eligible N)
    (dp : p∣n) (dq : q∣n) : p=q := by
  wlog h : p≤q generalizing p q
  · exact (this hq hp dq dp (by omega)).symm
  by_contra ne
  have prm := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
  have qrm := (Nat.mem_primesLE.mp (mem_filter.mp hq).1).2
  have hd : p*q∣n := ((Nat.coprime_primes prm qrm).mpr ne).mul_dvd_of_dvd_of_dvd dp dq
  have hb := (Nat.le_of_dvd (mem_Icc.mp hn).1 hd).trans (mem_Icc.mp hn).2
  have hq' : q≤N/p := (Nat.le_div_iff_mul_le prm.pos).mpr (by simpa [mul_comm] using hb)
  have hh : N/p<p := (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _)).trans_lt (mem_filter.mp hp).2
  omega
lemma fiber (N p : ℕ) (hp : p.Prime) :
    (∑ n ∈ (Icc 1 N).filter (p∣·), (1:ℝ)/n) = (harmonic (N/p):ℝ)/p := by
  rw [harmonic_eq_sum_Icc,Rat.cast_sum,sum_div]
  apply sum_bij (fun n _ => n/p)
  · intro n hn
    obtain ⟨hn,hp'⟩ := mem_filter.mp hn
    obtain ⟨pos,le⟩ := mem_Icc.mp hn
    exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd pos hp') hp.pos,Nat.div_le_div_right le⟩
  · intro n hn m hm eq
    have a := Nat.div_mul_cancel (mem_filter.mp hn).2
    have b := Nat.div_mul_cancel (mem_filter.mp hm).2
    grind
  · intro m hm
    obtain ⟨pos,le⟩ := mem_Icc.mp hm
    refine ⟨m*p, mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos pos hp.pos,(Nat.le_div_iff_mul_le hp.pos).mp le⟩,dvd_mul_left _ _⟩,?_⟩
    exact Nat.mul_div_cancel _ hp.pos
  · intro n hn
    have e := Nat.div_mul_cancel (mem_filter.mp hn).2
    have er : (↑(n/p):ℝ)*p=n := by exact_mod_cast e
    push_cast
    rw [←one_div,div_div,er]
lemma total (N : ℕ) :
    (∑ n ∈ (Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial<p), (1:ℝ)/n) =
      ∑ p ∈ eligible N, (harmonic (N/p):ℝ)/p := by
  classical
  have term (n : ℕ) (hn : n∈Icc 1 N) :
      (if ∃ p ∈ n.primeFactors, (N/p)*(N/p).factorial<p then (1:ℝ)/n else 0) =
        ∑ p ∈ eligible N, if p∣n then (1:ℝ)/n else 0 := by
    split_ifs with he
    · obtain ⟨p,hp,hcut⟩ := he
      have dp := Nat.dvd_of_mem_primeFactors hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have pel : p∈eligible N := mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (mem_Icc.mp hn).1 dp).trans (mem_Icc.mp hn).2,hpr⟩,hcut⟩
      rw [sum_eq_single_of_mem p pel]
      · simp [dp]
      · intro q hq ne
        exact if_neg (fun dq => ne (unique hn hq pel dq dp))
    · symm
      apply sum_eq_zero
      intro p hp
      apply if_neg
      intro dp
      apply he
      exact ⟨p,Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesLE.mp (mem_filter.mp hp).1).2,dp,(show 0<n from (mem_Icc.mp hn).1).ne'⟩,(mem_filter.mp hp).2⟩
  rw [sum_filter]
  calc
    _ = ∑ n ∈ Icc 1 N, ∑ p ∈ eligible N, if p∣n then (1:ℝ)/n else 0 := sum_congr rfl term
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [←sum_filter]
      exact fiber N p (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2
end Count308

open Real Filter Finset
open scoped Classical Topology
namespace Count308
noncomputable abbrev scaled (N : ℕ) (s : Finset ℕ) :=
  (∑ p ∈ s, (harmonic (N/p):ℝ)/p)*log N/(log (log N))^2
noncomputable abbrev window (N : ℕ) (a : ℝ) :=
  (Nat.primesLE N).filter fun p : ℕ => (N:ℝ)<p*(log N)^a
lemma mono {N : ℕ} (hn : 1≤N) {s t : Finset ℕ} (sub : s⊆t) :
    scaled N s ≤ scaled N t := by
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (log_nonneg (by exact_mod_cast hn))
  apply sum_le_sum_of_subset_of_nonneg sub
  intro p _ _
  rw [harmonic_eq_sum_Icc]
  push_cast
  positivity
theorem final_estimate :
    Tendsto (fun N : ℕ => (∑ n ∈ (Icc 1 N).filter (fun n => ∃ p ∈ n.primeFactors,
      (N/p)*(N/p).factorial<p), (1:ℝ)/n)*log N/(log (log N))^2) atTop (𝓝 (1/2:ℝ)) := by
  simp_rw [total]
  change Tendsto (fun N => scaled N (eligible N)) _ _
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have low : Tendsto (fun d : ℝ => (1-d)^2/2) (𝓝 0) (𝓝 (1/2:ℝ)) := by
    simpa using ((show Continuous (fun d : ℝ => (1-d)^2/2) by fun_prop).continuousAt (x:=0)).tendsto
  have high : Tendsto (fun d : ℝ => (1+d)^2/2) (𝓝 0) (𝓝 (1/2:ℝ)) := by
    simpa using ((show Continuous (fun d : ℝ => (1+d)^2/2) by fun_prop).continuousAt (x:=0)).tendsto
  have evlow := low.eventually_const_lt (show 1/2-ε < (1/2:ℝ) by linarith)
  have evhigh := high.eventually_lt_const (show (1/2:ℝ)<1/2+ε by linarith)
  have ev : ∀ᶠ d in 𝓝[>] (0:ℝ), 1/2-ε<(1-d)^2/2 ∧ (1+d)^2/2<1/2+ε := (evlow.and evhigh).filter_mono nhdsWithin_le_nhds
  obtain ⟨d,⟨ld,ud⟩,hd⟩ := (ev.and
    (show ∀ᶠ d in 𝓝[>] (0:ℝ), d∈ Set.Ioo 0 1 from Ioo_mem_nhdsGT zero_lt_one)).exists
  have ha : 0<1-d := sub_pos.mpr hd.2
  have hb : 0<1+d := by linarith [hd.1]
  filter_upwards [(Window308.limit (1-d) ha).eventually_const_lt ld,
    (Window308.limit (1+d) hb).eventually_lt_const ud,
    Factor308.bounds (1-d) (1+d) ha (by linarith [hd.1]) (by linarith [hd.1]),
    eventually_ge_atTop (1:ℕ)] with N l u bd hn
  change 1/2-ε < scaled N (window N (1-d)) at l
  change scaled N (window N (1+d)) < 1/2+ε at u
  have sl : window N (1-d) ⊆ eligible N := by
    intro p hp
    obtain ⟨hP,hcut⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hP,(bd p hP).1 hcut⟩
  have su : eligible N ⊆ window N (1+d) := by
    intro p hp
    obtain ⟨hP,hcut⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨hP,(bd p hP).2 hcut⟩
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith [mono hn sl,mono hn su]
end Count308

theorem OMA.solution : OMA.R_Erdos308_erdos_308_variants_croot_R1.H2 := Count308.final_estimate
