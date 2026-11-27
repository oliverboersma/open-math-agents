import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1
import Mathlib

/-!
# Fourier extraction of a unit fraction

The finite Fourier expansion, cosine estimates, and centered frequency window
are adapted from Will Howe (@H0W4RD-dev), H0W4RD-dev/croot-unit-fractions,
commit c58a7d45114c3af27e6abb19dcfca9d82b49b4a1, Basic.lean, Fourier.lean
and Prop2.lean, under Apache-2.0, as ported in the merged Erdős 319 proof.
The two classes of minor frequencies are from Bhavik Mehta and Thomas Bloom,
b-mehta/unit-fractions, src/fourier.lean, Lemma 4.22, commit
10ef71a300cf29e5f19beb2bbc723a035a0678de.
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. Used under Apache-2.0.

For each sparse minor frequency choose a nearby integer x supplied by the
interval hypothesis. The prime powers that do not divide x form a nonempty
set D. Each denominator accounts for at most its number of distinct prime
factors in the incidence count. A frequency with j missing prime powers
contributes at most N^(-6j), and the lcm divisibility confines its center to
at most 2 N^j + 1 possible values for any fixed D.
-/
section
/-!
# Basic definitions for the formalization of Croot's theorem

* `Croot.recipSum S = ∑_{n ∈ S} 1/n` as a rational number;
* `Croot.PPSmooth y n`: every prime power exactly dividing `n` is at most `y`.
-/

open Finset

namespace Croot

/-- The sum of reciprocals of a finite set of natural numbers, as a rational number. -/
def recipSum (S : Finset ℕ) : ℚ := ∑ n ∈ S, (1 : ℚ) / n

@[simp] lemma recipSum_empty : recipSum ∅ = 0 := by simp [recipSum]

lemma recipSum_union {S T : Finset ℕ} (h : Disjoint S T) :
    recipSum (S ∪ T) = recipSum S + recipSum T := by
  simp [recipSum, sum_union h]

lemma recipSum_sdiff {S T : Finset ℕ} (h : T ⊆ S) :
    recipSum (S \ T) = recipSum S - recipSum T := by
  have := sum_sdiff (f := fun n : ℕ => (1 : ℚ) / n) h
  simp only [recipSum]
  linarith

lemma recipSum_nonneg (S : Finset ℕ) : 0 ≤ recipSum S :=
  sum_nonneg fun _ _ => by positivity

lemma recipSum_mono {S T : Finset ℕ} (h : S ⊆ T) : recipSum S ≤ recipSum T :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

/-- `n` is `y`-prime-power-smooth: every prime power `p ^ v_p(n)` with `p ∣ n` is `≤ y`. -/
def PPSmooth (y n : ℕ) : Prop := ∀ p ∈ n.primeFactors, p ^ n.factorization p ≤ y

instance (y : ℕ) : DecidablePred (PPSmooth y) := fun n => by
  unfold PPSmooth; infer_instance

lemma ppSmooth_one (y : ℕ) : PPSmooth y 1 := by simp [PPSmooth]

lemma PPSmooth.mono {y y' n : ℕ} (h : PPSmooth y n) (hy : y ≤ y') : PPSmooth y' n :=
  fun p hp => (h p hp).trans hy

lemma PPSmooth.of_dvd {y n d : ℕ} (h : PPSmooth y n) (hn : n ≠ 0) (hd : d ∣ n) :
    PPSmooth y d := by
  intro p hp
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hn hd
  have hpn : p ∈ n.primeFactors := Nat.primeFactors_mono hd hn hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  calc p ^ d.factorization p ≤ p ^ n.factorization p :=
        Nat.pow_le_pow_right hpp.pos ((Nat.factorization_le_iff_dvd hd0 hn).2 hd p)
    _ ≤ y := h p hpn

/-- A `y`-pp-smooth positive integer divides `lcm(1, …, y)`. -/
lemma PPSmooth.dvd_lcmUpto {y n : ℕ} (h : PPSmooth y n) (hn : n ≠ 0) :
    n ∣ Nat.lcmUpto y := by
  rw [← Nat.factorization_le_iff_dvd hn (Nat.lcmUpto_ne_zero y)]
  intro p
  by_cases hp : p ∈ n.primeFactors
  · have hpp := Nat.prime_of_mem_primeFactors hp
    rw [Nat.factorization_lcmUpto y hpp]
    exact Nat.le_log_of_pow_le hpp.one_lt (h p hp)
  · have : n.factorization p = 0 := by
      rwa [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
    simp [this]

end Croot
end
section
/-!
# Finite Fourier analysis for subset sums of unit fractions

`eC t = exp (2 π i t)`.  For a finite set `Y` of positive integers dividing `P` and a rational
`x` with `x P ∈ ℤ`, summing `e(-h x) ∏_{m∈Y} (1 + e(h/m))` over any `P` consecutive integers `h`
counts (times `P`) the subsets `Z ⊆ Y` with `∑_{m∈Z} 1/m - x ∈ ℤ`.  We also record the
elementary estimates on the individual terms used in Croot's Proposition 2.
-/

namespace Croot

open Real Complex Finset

/-- `e(t) = exp(2 π i t)`. -/
noncomputable def eC (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-! ### Basic properties of `eC` -/

lemma eC_add (s t : ℝ) : eC (s + t) = eC s * eC t := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma eC_zero : eC 0 = 1 := by
  simp [eC]

lemma eC_eq_one_iff (t : ℝ) : eC t = 1 ↔ ∃ n : ℤ, t = n := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h3 : (t : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]
      ring
    exact_mod_cast h3
  · rintro ⟨n, rfl⟩
    exact ⟨n, by push_cast; ring⟩

lemma eC_intCast (n : ℤ) : eC n = 1 := (eC_eq_one_iff _).2 ⟨n, rfl⟩

lemma norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  have : (2 * (π : ℂ) * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma eC_re (t : ℝ) : (eC t).re = Real.cos (2 * π * t) := by
  unfold eC
  have : (2 * (π : ℂ) * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

lemma eC_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    eC (∑ i ∈ s, f i) = ∏ i ∈ s, eC (f i) := by
  unfold eC
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]

lemma eC_nat_mul (n : ℕ) (t : ℝ) : eC (n * t) = eC t ^ n := by
  unfold eC
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `1 + e(θ) = e(θ/2) · 2 cos(π θ)`. -/
lemma one_add_eC (θ : ℝ) :
    1 + eC θ = eC (θ / 2) * ((2 * Real.cos (π * θ) : ℝ) : ℂ) := by
  have h1 : ((2 * Real.cos (π * θ) : ℝ) : ℂ) =
      Complex.exp (((π * θ : ℝ) : ℂ) * I) + Complex.exp (-((π * θ : ℝ) : ℂ) * I) := by
    rw [← Complex.two_cos]
    push_cast
    rfl
  rw [h1, mul_add]
  unfold eC
  rw [← Complex.exp_add, ← Complex.exp_add]
  have e1 : 2 * (π : ℂ) * I * ((θ / 2 : ℝ) : ℂ) + ((π * θ : ℝ) : ℂ) * I = 2 * π * I * θ := by
    push_cast
    ring
  have e2 : 2 * (π : ℂ) * I * ((θ / 2 : ℝ) : ℂ) + -((π * θ : ℝ) : ℂ) * I = 0 := by
    push_cast
    ring
  rw [e1, e2, Complex.exp_zero, add_comm]

lemma norm_one_add_eC (θ : ℝ) : ‖1 + eC θ‖ = 2 * |Real.cos (π * θ)| := by
  rw [one_add_eC, norm_mul, norm_eC, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_two]

lemma norm_one_add_eC_le_two (θ : ℝ) : ‖1 + eC θ‖ ≤ 2 := by
  calc ‖1 + eC θ‖ ≤ ‖(1 : ℂ)‖ + ‖eC θ‖ := norm_add_le _ _
    _ = 2 := by rw [norm_one, norm_eC]; norm_num

/-- `cos (π u) ≤ 1 - 4 u²` for `0 ≤ u ≤ 1/2`: Taylor bound for `u ≤ 3/10`, and
`cos (π u) = sin (π (1/2 - u)) ≤ π (1/2 - u)` for `u ≥ 3/10`. -/
lemma cos_pi_mul_le (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) :
    Real.cos (π * u) ≤ 1 - 4 * u ^ 2 := by
  have hpi1 := Real.pi_gt_d2
  have hpi2 := Real.pi_lt_d2
  rcases le_or_gt u (3 / 10) with hu | hu
  · have hpu : 0 ≤ π * u := by positivity
    have hx : |π * u| ≤ 1 := by
      rw [abs_of_nonneg hpu]
      nlinarith
    have hb := Real.cos_bound hx
    rw [abs_of_nonneg hpu] at hb
    have hb' := (abs_le.mp hb).2
    have hp2 : 9.85 ≤ π ^ 2 := by nlinarith
    have hp2' : π ^ 2 ≤ 9.93 := by nlinarith
    have hu2 : u ^ 2 ≤ 9 / 100 := by nlinarith
    have hu2' : 0 ≤ u ^ 2 := by positivity
    have hq1 : (u ^ 2) ^ 2 ≤ 9 / 100 * u ^ 2 := by nlinarith
    have hq2 : (π ^ 2) ^ 2 ≤ 9.93 ^ 2 := by nlinarith
    have h4 : (π * u) ^ 4 ≤ 9.93 ^ 2 * (9 / 100 * u ^ 2) := by
      have : (π * u) ^ 4 = (π ^ 2) ^ 2 * (u ^ 2) ^ 2 := by ring
      rw [this]
      exact mul_le_mul hq2 hq1 (by positivity) (by positivity)
    have h5 : 9.85 * u ^ 2 ≤ (π * u) ^ 2 := by
      have : (π * u) ^ 2 = π ^ 2 * u ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hp2 hu2'
    nlinarith
  · have hc : Real.cos (π * u) = Real.sin (π / 2 - π * u) := (Real.sin_pi_div_two_sub _).symm
    rw [hc]
    have hs := Real.sin_le (by nlinarith : 0 ≤ π / 2 - π * u)
    have hm : 0 ≤ (1 / 2 - u) * (2 + 4 * u - π) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- If `θ` is at distance `≥ δ` from every integer, then `‖1 + e(θ)‖ ≤ 2 (1 - 4 δ²)`. -/
lemma norm_one_add_eC_le_of_far (θ δ : ℝ) (hδ : 0 ≤ δ) (hfar : ∀ j : ℤ, δ ≤ |θ - j|) :
    ‖1 + eC θ‖ ≤ 2 * (1 - 4 * δ ^ 2) := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, |θ - j| ≤ 1 / 2 := ⟨round θ, abs_sub_round θ⟩
  have hδd : δ ≤ |θ - j| := hfar j
  have heq : eC θ = eC (θ - j) := by
    conv_lhs => rw [show θ = (θ - j) + (j : ℝ) by ring]
    rw [eC_add, eC_intCast, mul_one]
  rw [heq, norm_one_add_eC]
  have hcos : |Real.cos (π * (θ - j))| = Real.cos (π * |θ - j|) := by
    rw [← Real.cos_abs (π * (θ - j)), abs_mul, abs_of_pos Real.pi_pos]
    apply abs_of_nonneg
    have hle : π * |θ - j| ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
    have hge : 0 ≤ π * |θ - j| := mul_nonneg Real.pi_pos.le (abs_nonneg _)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> linarith [Real.pi_pos]
  rw [hcos]
  have hc := cos_pi_mul_le |θ - j| (abs_nonneg _) hj
  have hsq : δ * δ ≤ |θ - j| * |θ - j| := mul_le_mul hδd hδd hδ (abs_nonneg _)
  nlinarith

/-! ### Integrality and the window sum -/

lemma recipSum_mul_natCast_int (Z : Finset ℕ) (P : ℕ) (hZ : ∀ m ∈ Z, m ∣ P) :
    ∃ z : ℤ, recipSum Z * P = z := by
  refine ⟨∑ m ∈ Z, ((P / m : ℕ) : ℤ), ?_⟩
  rw [recipSum, Finset.sum_mul, Int.cast_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Int.cast_natCast, Nat.cast_div_charZero (hZ m hm)]
  ring

open scoped Classical in
/-- A complete geometric sum over a window of `P` consecutive integers. -/
lemma sum_Ico_eC (r : ℝ) (P : ℕ) (hr : eC (P * r) = 1) (h₀ : ℤ) :
    ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC ((h : ℝ) * r) =
      if ∃ k : ℤ, r = k then (P : ℂ) else 0 := by
  have hre : ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC ((h : ℝ) * r) =
      ∑ k ∈ Finset.range P, eC ((h₀ : ℝ) * r) * eC r ^ k := by
    refine Finset.sum_nbij' (fun h => (h - h₀).toNat) (fun k => h₀ + k) ?_ ?_ ?_ ?_ ?_
    · intro h hh
      simp only [Finset.mem_Ico, Finset.mem_range] at hh ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh ⊢
      omega
    · intro k _
      omega
    · intro h hh
      simp only [Finset.mem_Ico] at hh
      rw [← eC_nat_mul, ← eC_add]
      congr 1
      have h1 : (((h - h₀).toNat : ℕ) : ℝ) = (h : ℝ) - h₀ := by
        have : (((h - h₀).toNat : ℕ) : ℤ) = h - h₀ := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      rw [h1]
      ring
  rw [hre, ← Finset.mul_sum]
  split_ifs with hk
  · obtain ⟨k, rfl⟩ := hk
    have e1 : eC (k : ℝ) = 1 := eC_intCast k
    have e2 : eC ((h₀ : ℝ) * k) = 1 := by
      rw [show ((h₀ : ℝ) * k) = ((h₀ * k : ℤ) : ℝ) by push_cast; ring]
      exact eC_intCast _
    simp [e1, e2]
  · have hne : eC r ≠ 1 := fun h1 => hk ((eC_eq_one_iff r).1 h1)
    rw [geom_sum_eq hne, ← eC_nat_mul, hr]
    simp

-- `hP` is part of the fixed statement but not needed (for `P = 0` both sides vanish).
open scoped Classical in
/-- The counting identity, over any window of `P` consecutive integers. -/
theorem fourier_count (Y : Finset ℕ) (P : ℕ) (hP : 0 < P) (hY : ∀ m ∈ Y, 0 < m ∧ m ∣ P)
    (x : ℚ) (hx : ∃ z : ℤ, x * P = z) (h₀ : ℤ) :
    ∑ h ∈ Finset.Ico h₀ (h₀ + P), eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m)) =
      (P : ℂ) * ((Y.powerset.filter (fun Z => ∃ k : ℤ, recipSum Z - x = k)).card : ℂ) := by
  -- expand the product over subsets and combine the exponentials
  have key : ∀ h : ℤ, eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m)) =
      ∑ Z ∈ Y.powerset, eC ((h : ℝ) * ((recipSum Z - x : ℚ) : ℝ)) := by
    intro h
    rw [Finset.prod_one_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [← eC_sum, ← eC_add]
    congr 1
    simp only [recipSum, Rat.cast_sub, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    rw [mul_sub, Finset.mul_sum]
    simp only [mul_one_div]
    ring
  rw [Finset.sum_congr rfl fun h _ => key h, Finset.sum_comm, Finset.natCast_card_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun Z hZ => ?_
  -- for each subset `Z`, `(recipSum Z - x) * P` is an integer
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := recipSum_mul_natCast_int Z P
    (fun m hm => (hY m (Finset.mem_powerset.1 hZ hm)).2)
  have hq : (recipSum Z - x) * P = ((w - z : ℤ) : ℚ) := by
    rw [sub_mul, hw, hz, Int.cast_sub]
  have hr' : (P : ℝ) * ((recipSum Z - x : ℚ) : ℝ) = ((w - z : ℤ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hq
    push_cast at this ⊢
    linarith
  have hr : eC ((P : ℝ) * ((recipSum Z - x : ℚ) : ℝ)) = 1 := by
    rw [hr']
    exact eC_intCast _
  rw [sum_Ico_eC _ P hr h₀]
  have hiff : (∃ k : ℤ, ((recipSum Z - x : ℚ) : ℝ) = k) ↔ (∃ k : ℤ, recipSum Z - x = k) := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by exact_mod_cast hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [hk]; push_cast; rfl⟩
  by_cases hc : ∃ k : ℤ, recipSum Z - x = k
  · rw [if_pos (hiff.2 hc), if_pos hc, mul_one]
  · rw [if_neg (fun h' => hc (hiff.1 h')), if_neg hc, mul_zero]

/-- The `h = 0` term. -/
theorem term_zero (Y : Finset ℕ) (x : ℚ) :
    eC (-(((0 : ℤ) : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC (((0 : ℤ) : ℝ) / m)) = (2 : ℂ) ^ Y.card := by
  simp only [Int.cast_zero, zero_mul, neg_zero, zero_div, eC_zero, one_mul, Finset.prod_const]
  norm_num

/-- Terms with small `|h|` have nonnegative real part. -/
theorem re_term_nonneg (Y : Finset ℕ) (x : ℚ) (h : ℤ)
    (hY : ∀ m ∈ Y, 0 < m ∧ 2 * |(h : ℝ)| ≤ m)
    (hsmall : |(h : ℝ) * ((recipSum Y : ℝ) / 2 - (x : ℝ))| ≤ 1 / 4) :
    0 ≤ (eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m))).re := by
  -- the term is `e(h (recipSum Y / 2 - x)) * ∏ 2 cos (π h / m)`
  simp_rw [one_add_eC]
  rw [Finset.prod_mul_distrib, ← eC_sum, ← mul_assoc, ← eC_add, ← Complex.ofReal_prod,
    Complex.re_mul_ofReal]
  apply mul_nonneg
  · rw [eC_re]
    have hsum : ∑ m ∈ Y, (h : ℝ) / m / 2 = (h : ℝ) * (∑ m ∈ Y, (1 : ℝ) / m) / 2 := by
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hrs : ((recipSum Y : ℚ) : ℝ) = ∑ m ∈ Y, (1 : ℝ) / m := by
      simp only [recipSum, Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
    have hphi : -((h : ℝ) * (x : ℝ)) + ∑ m ∈ Y, (h : ℝ) / m / 2 =
        (h : ℝ) * ((recipSum Y : ℝ) / 2 - (x : ℝ)) := by
      rw [hsum, hrs]
      ring
    rw [hphi]
    obtain ⟨h1, h2⟩ := abs_le.mp hsmall
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  · apply Finset.prod_nonneg
    intro m hm
    obtain ⟨hm0, hm1⟩ := hY m hm
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm0
    have habs : |(h : ℝ) / m| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
      linarith
    obtain ⟨h1, h2⟩ := abs_le.mp habs
    apply mul_nonneg (by norm_num)
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]

/-- Norm bound: factors with `h/m` at distance `≥ δ` from every integer save `1 - 4 δ²`. -/
theorem norm_term_le (Y J : Finset ℕ) (hJ : J ⊆ Y) (x : ℚ) (h : ℤ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hδ' : δ ≤ 1 / 2) (hfar : ∀ m ∈ J, ∀ j : ℤ, δ ≤ |(h : ℝ) / m - j|) :
    ‖eC (-((h : ℝ) * (x : ℝ))) * ∏ m ∈ Y, (1 + eC ((h : ℝ) / m))‖ ≤
      2 ^ Y.card * (1 - 4 * δ ^ 2) ^ J.card := by
  rw [norm_mul, norm_eC, one_mul, norm_prod, ← Finset.prod_sdiff hJ]
  have hc : 0 ≤ 1 - 4 * δ ^ 2 := by nlinarith
  have h1 : ∏ m ∈ Y \ J, ‖1 + eC ((h : ℝ) / m)‖ ≤ 2 ^ (Y \ J).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun m _ => norm_one_add_eC_le_two _)
  have h2 : ∏ m ∈ J, ‖1 + eC ((h : ℝ) / m)‖ ≤ (2 * (1 - 4 * δ ^ 2)) ^ J.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun m hm => norm_one_add_eC_le_of_far _ _ hδ (hfar m hm))
  calc (∏ m ∈ Y \ J, ‖1 + eC ((h : ℝ) / m)‖) * ∏ m ∈ J, ‖1 + eC ((h : ℝ) / m)‖
      ≤ 2 ^ (Y \ J).card * (2 * (1 - 4 * δ ^ 2)) ^ J.card :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (by positivity)
    _ = 2 ^ Y.card * (1 - 4 * δ ^ 2) ^ J.card := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Finset.card_sdiff_add_card_eq_card hJ]

end Croot
end

namespace Croot
open Finset
lemma abs_le_of_mem_window {P : ℕ} {h : ℤ} (hh : h ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ))
    (-((P / 2 : ℕ) : ℤ) + P)) : |(h : ℝ)| ≤ (P : ℝ) / 2 := by
  rw [Finset.mem_Ico] at hh
  obtain ⟨h1, h2⟩ := hh
  have hP2 : ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast Nat.div_mul_le_self P 2
  have hP2' : (P : ℝ) - ((P / 2 : ℕ) : ℝ) ≤ (P : ℝ) / 2 + 1 / 2 := by
    have : (P : ℝ) ≤ 2 * ((P / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show P ≤ 2 * (P / 2) + 1 by omega)
    linarith
  have h1' : -((P / 2 : ℕ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast h1
  have h2' : (h : ℝ) + 1 ≤ -((P / 2 : ℕ) : ℝ) + P := by
    have : h + 1 ≤ -((P / 2 : ℕ) : ℤ) + P := h2
    exact_mod_cast this
  rw [abs_le]
  constructor <;> linarith

lemma zero_mem_window {P : ℕ} (hP : 0 < P) :
    (0 : ℤ) ∈ Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P) := by
  rw [Finset.mem_Ico]
  have : P / 2 < P := Nat.div_lt_self hP (by norm_num)
  constructor <;> omega

lemma card_window (P : ℕ) :
    (Finset.Ico (-((P / 2 : ℕ) : ℤ)) (-((P / 2 : ℕ) : ℤ) + P)).card = P := by
  rw [Int.card_Ico]
  simp

end Croot

open Real Finset Filter
open scoped Classical Topology
namespace Circle299
noncomputable abbrev span (P : ℕ) : Finset ℤ := Ico (-((P/2:ℕ):ℤ)) (-((P/2:ℕ):ℤ)+P)
noncomputable abbrev minor (P : ℕ) (K : ℝ) : Finset ℤ := (span P).filter fun h : ℤ => K/2 < |(h:ℝ)|
noncomputable abbrev interval (h : ℤ) (K : ℝ) := Icc (⌈(h:ℝ)-K/2⌉:ℤ) ⌊(h:ℝ)+K/2⌋
noncomputable def miss (A : Finset ℕ) (K : ℝ) (h : ℤ) : Finset ℕ :=
  A.filter fun n : ℕ => ∀ v∈interval h K, ¬(n:ℤ)∣v
noncomputable abbrev damp (A : Finset ℕ) (N : ℕ) (K : ℝ) (h : ℤ) :=
  exp (-((K/N)^2)*(miss A K h).card)
noncomputable abbrev term (A : Finset ℕ) (x : ℚ) (h : ℤ) :=
  Croot.eC (-((h:ℝ)*(x:ℝ))) * ∏ n ∈ A, (1+Croot.eC ((h:ℝ)/n))
lemma bound_term {A : Finset ℕ} {N : ℕ} {K : ℝ} (hN : 0<N) (hK : 0≤K) (hKN : K≤N)
    (hp : ∀ n∈A, 0<n ∧ n≤N) (x : ℚ) (h : ℤ) :
    ‖term A x h‖ ≤ (2:ℝ)^A.card*damp A N K h := by
  have npos : (0:ℝ)<N := by exact_mod_cast hN
  let δ := K/(2*N)
  have dp : 0≤δ := by dsimp [δ]; positivity
  have du : δ≤1/2 := by dsimp [δ]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hs : miss A K h ⊆ A := filter_subset _ _
  have far (n : ℕ) (hn : n ∈ miss A K h) (j : ℤ) : δ≤|(h:ℝ)/n-j| := by
    have pos : (0:ℝ)<n := by exact_mod_cast (hp n (hs hn)).1
    have nle : (n:ℝ)≤N := by exact_mod_cast (hp n (hs hn)).2
    have hh : K/2 < |(h:ℝ)-(n:ℝ)*j| := by
      by_contra! ne
      obtain ⟨lo,hi⟩ := abs_le.mp ne
      apply (mem_filter.mp hn).2 ((n:ℤ)*j) _ (dvd_mul_right _ _)
      apply mem_Icc.mpr
      constructor
      · apply Int.ceil_le.mpr
        push_cast
        linarith
      · apply Int.le_floor.mpr
        push_cast
        linarith
    rw [div_sub',abs_div,abs_of_pos pos,le_div_iff₀ pos] <;> try positivity
    dsimp [δ]
    have t := mul_le_mul_of_nonneg_left nle dp
    dsimp [δ] at t
    have e : K/(2*(N:ℝ))*N=K/2 := by field_simp
    rw [e] at t
    simpa [mul_comm] using t.trans hh.le
  have est := Croot.norm_term_le A (miss A K h) hs x h δ dp du far
  apply est.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have pos : 0≤1-4*δ^2 := by nlinarith [mul_nonneg dp (sub_nonneg.mpr du),sq_nonneg (δ-1/2)]
  have small : 1-4*δ^2 ≤ exp (-4*δ^2) := by linarith [Real.add_one_le_exp (-4*δ^2)]
  have pe := pow_le_pow_left₀ pos small (miss A K h).card
  rw [←Real.exp_nat_mul] at pe
  have e : 4*δ^2=(K/N)^2 := by dsimp [δ]; ring
  simpa only [damp,←neg_mul,neg_mul_eq_neg_mul, mul_comm (↑(miss A K h).card : ℝ)] using
    (pe.trans_eq (congrArg exp (show ((miss A K h).card:ℝ)*(-4*δ^2) = -((K/N)^2)*(miss A K h).card by rw [←e]; ring)))
lemma extract {A : Finset ℕ} {N d : ℕ} {K M : ℝ} (hN : 0<N) (hd : 0<d)
    (hK : 0≤K) (hKM : K≤M) (hMN : M≤N) (hM : 0<M)
    (ha : ∀ n∈A, 0<n ∧ M≤n ∧ n≤N) (hdP : d∣A.lcm id)
    (hh : (Croot.recipSum A:ℝ)<2/d) (hl : 2/(d:ℝ)-1/M≤Croot.recipSum A)
    (period : ((A.lcm id:ℕ):ℝ) < (2:ℝ)^A.card/2)
    (tail : ∑ h ∈ minor (A.lcm id) K, damp A N K h ≤ 1/2) :
    ∃ S ⊆ A, Croot.recipSum S = 1/d := by
  classical
  let P := A.lcm id
  let x : ℚ := 1/d
  have dr : (0:ℝ)<d := by exact_mod_cast hd
  have dq : 0<(d:ℚ) := by exact_mod_cast hd
  have ar (n : ℕ) (hn : n∈A) : 0<n ∧ n∣P := ⟨(ha n hn).1,dvd_lcm hn⟩
  have pp : 0<P := by
    change 0<A.lcm id
    exact Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr fun n hn => (ha n hn).1.ne')
  have xp : ∃ z : ℤ, x*P=z := by
    obtain ⟨j,hj⟩ := hdP
    refine ⟨j,?_⟩
    change (1/(d:ℚ))*(A.lcm id:ℕ)=_
    rw [hj]
    push_cast
    field_simp
  have count := Croot.fourier_count A P pp ar x xp (-((P/2:ℕ):ℤ))
  let Z := A.powerset.filter fun S => ∃ k : ℤ, Croot.recipSum S-x=k
  have ident : (∑ h ∈ span P, (term A x h).re) = (P:ℝ)*Z.card := by
    have e := congrArg Complex.re count
    simpa [term,span,Z,Complex.re_sum] using e
  have major {h : ℤ} (lo : |(h:ℝ)|≤K/2) : 0≤(term A x h).re := by
    apply Croot.re_term_nonneg
    · intro n hn
      exact ⟨(ha n hn).1, by linarith [(ha n hn).2.1]⟩
    · rw [show (2:ℝ)/d=2*(1/d) by ring] at hh hl
      have xval : (x:ℝ)=1/d := by simp [x]
      rw [xval,abs_mul,abs_of_nonpos (by linarith : (Croot.recipSum A:ℝ)/2-1/d≤0)]
      have h1 : -((Croot.recipSum A:ℝ)/2-1/d) ≤ 1/(2*M) := by
        have eq : 1/(2*M)=(1/M)/2 := by ring
        rw [eq]; linarith
      calc _ ≤ (M/2)*(1/(2*M)) := mul_le_mul (lo.trans (by linarith)) h1 (by linarith) (by positivity)
           _ = _ := by field_simp <;> norm_num
  have zero := Croot.term_zero A x
  have sumlow : (2:ℝ)^A.card/2 ≤ ∑ h ∈ span P, (term A x h).re := by
    let F := minor P K
    let R := span P \ F
    have zR : (0:ℤ)∈R := mem_sdiff.mpr ⟨Croot.zero_mem_window pp,by simp [F,minor,show 0≤K/2 by positivity]⟩
    have main : (2:ℝ)^A.card ≤ ∑ h ∈ R, (term A x h).re := by
      have nn (h : ℤ) (hh : h∈R) : 0≤(term A x h).re := by
        have he := mem_sdiff.mp hh
        exact major (le_of_not_gt (fun hlt => he.2 (mem_filter.mpr ⟨he.1,hlt⟩)))
      have sg := single_le_sum nn zR
      have z : (term A x 0).re=(2:ℝ)^A.card := by rw [show term A x 0=_ from zero]; norm_cast
      simpa only [z] using sg
    have err : -(∑ h ∈ F, (term A x h).re) ≤ (2:ℝ)^A.card/2 := by
      rw [←sum_neg_distrib]
      calc _ ≤ ∑ h ∈ F, (2:ℝ)^A.card*damp A N K h := by
             apply sum_le_sum
             intro h _
             exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
               (bound_term hN hK (hKM.trans hMN) (fun n hn => ⟨(ha n hn).1,(ha n hn).2.2⟩) x h))
           _ ≤ _ := by rw [←mul_sum]; nlinarith [mul_le_mul_of_nonneg_left tail (by positivity : 0≤(2:ℝ)^A.card)]
    have spl := sum_sdiff (f:=fun h => (term A x h).re) (show F⊆span P from filter_subset _ _)
    change (∑ h ∈ R, _)+(∑ h ∈ F, _) = _ at spl
    linarith
  by_contra! none
  have single : Z ⊆ {∅} := by
    intro S hS
    obtain ⟨sm,k,ek⟩ := mem_filter.mp hS
    have sa := mem_powerset.mp sm
    by_contra ne
    have sn : S.Nonempty := nonempty_iff_ne_empty.mpr (by simpa using ne)
    have positive : 0<Croot.recipSum S := sum_pos' (fun n _ => by positivity)
      (sn.imp (fun n hn => ⟨hn,one_div_pos.mpr (by exact_mod_cast (ha n (sa hn)).1)⟩))
    have b := Croot.recipSum_mono sa
    have aq : Croot.recipSum A < 2/(d:ℚ) := by
      apply (Rat.cast_lt (K:=ℝ)).mp
      push_cast
      exact hh
    rw [show (2:ℚ)/d=2*x by dsimp [x]; ring] at aq
    have x1 : x≤1 := by dsimp [x]; rw [div_le_iff₀ dq]; simpa only [one_mul] using (show (1:ℚ)≤d by exact_mod_cast hd)
    have : (k:ℚ)<1 := by linarith
    have : (-1:ℚ)<k := by linarith
    have kz : k=0 := by
      have kl : -1<k := by exact_mod_cast ‹(-1:ℚ)<k›
      have ku : k<1 := by exact_mod_cast ‹(k:ℚ)<1›
      omega
    apply none S sa
    rw [kz,Int.cast_zero] at ek
    exact sub_eq_zero.mp ek
  have card : Z.card≤1 := (card_le_card single).trans_eq (card_singleton _)
  have bound : (P:ℝ)*Z.card≤P := by simpa using mul_le_mul_of_nonneg_left (show (Z.card:ℝ)≤1 by exact_mod_cast card) (by positivity : (0:ℝ)≤P)
  change (P:ℝ)<_ at period
  linarith
end Circle299

open Finset Real Filter
open scoped Classical Topology
namespace Circle299
noncomputable def powers (A : Finset ℕ) := A.biUnion fun n =>
  n.divisors.filter fun q => IsPrimePow q ∧ Nat.Coprime q (n/q)
noncomputable def part (A : Finset ℕ) (q : ℕ) := A.filter fun n => q∣n ∧ Nat.Coprime q (n/q)
noncomputable abbrev absent (A : Finset ℕ) (x : ℤ) := (powers A).filter fun q : ℕ => ¬(q:ℤ)∣x
lemma power_mem {A : Finset ℕ} {q : ℕ} (h : q ∈ powers A) :
    IsPrimePow q ∧ ∃ n ∈ A, n ≠ 0 ∧ q∣n ∧ Nat.Coprime q (n/q) := by
  obtain ⟨n,hn,hq⟩ := mem_biUnion.mp h
  obtain ⟨dv,pp,cp⟩ := mem_filter.mp hq
  obtain ⟨hd,h0⟩ := Nat.mem_divisors.mp dv
  exact ⟨pp,n,hn,h0,hd,cp⟩
lemma cover (A : Finset ℕ) (ha : 0∉A) (x : ℤ) :
    (A.lcm id:ℕ) ∣ x.natAbs * ∏ q ∈ absent A x, q := by
  apply Finset.lcm_dvd
  intro n hn
  have nz : n≠0 := by rintro rfl; exact ha hn
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k pp h
  by_cases k0 : k=0
  · simp [k0]
  have ek := (pp.pow_dvd_iff_le_factorization nz).mp h
  set q := p^n.factorization p
  have qn : q∣n := Nat.ordProj_dvd n p
  have qpp : IsPrimePow q := (pp.isPrimePow.pow (by omega : n.factorization p≠0))
  have qc : Nat.Coprime q (n/q) := (Nat.coprime_ordCompl pp nz).pow_left _
  have hq : q∈powers A := mem_biUnion.mpr ⟨n,hn,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨qn,nz⟩,qpp,qc⟩⟩
  apply (pow_dvd_pow p ek).trans
  by_cases hd : (q:ℤ)∣x
  · exact dvd_mul_of_dvd_left (by simpa using Int.natAbs_dvd_natAbs.mpr hd) _
  · exact dvd_mul_of_dvd_right (dvd_prod_of_mem id (mem_filter.mpr ⟨hq,hd⟩)) _
lemma index_subset {A : Finset ℕ} {n : ℕ} (hn : n≠0) (D : Finset ℕ) (hD : D⊆powers A) :
    (D.filter (fun q => n ∈ part A q)) ⊆ n.primeFactors.image (fun p => p^n.factorization p) := by
  intro q hq
  obtain ⟨qD,mem⟩ := mem_filter.mp hq
  obtain ⟨_,qn,cp⟩ := mem_filter.mp mem
  obtain ⟨p,_,k,_,pr,kn,eq⟩ := (isPrimePow_nat_iff_bounded q).mp (power_mem (hD qD)).1
  subst q
  have pd : p∣p^k := dvd_pow_self _ (by omega)
  have pm := Nat.mem_primeFactors.mpr ⟨pr,pd.trans qn,hn⟩
  refine mem_image.mpr ⟨p,pm,?_⟩
  have cp' := cp.coprime_dvd_left pd
  have nodiv := (Nat.Prime.coprime_iff_not_dvd pr).mp cp'
  have zero := Nat.factorization_eq_zero_of_not_dvd nodiv
  have en := Nat.mul_div_cancel' qn
  have e : n.factorization p=k := by
    conv_lhs => rw [←en]
    rw [Nat.factorization_mul_apply_of_coprime cp,zero,add_zero,pr.factorization_pow]
    simp
  rw [e]
lemma missed_count {A D : Finset ℕ} {Y L W : ℝ} {h : ℤ} {K : ℝ}
    (ha : ∀ n∈A, n≠0 ∧ (n.primeFactors.card:ℝ)≤W)
    (hD : D⊆powers A) (qy : ∀ q∈D, (q:ℝ)≤Y)
    (hy : 0<Y) (hl : 0≤L) (hw : 0≤W)
    (many : ∀ q∈D, L/q ≤ (((miss A K h).filter (fun n => n ∈ part A q)).card:ℝ)) :
    D.card*(L/Y) ≤ (miss A K h).card*W := by
  let J := miss A K h
  have hq (q : ℕ) (hq : q∈D) : 0<(q:ℝ) := by exact_mod_cast (power_mem (hD hq)).1.pos
  have sumineq : ∑ q ∈ D, L/Y ≤ ∑ q ∈ D, (((J.filter (fun n => n∈part A q)).card):ℝ) := by
    apply sum_le_sum
    intro q qD
    exact (div_le_div_of_nonneg_left hl (hq q qD) (qy q qD)).trans (many q qD)
  have swap : (∑ q ∈ D, (((J.filter (fun n => n∈part A q)).card):ℝ)) =
      ∑ n ∈ J, (((D.filter (fun q => n∈part A q)).card):ℝ) := by
    simp_rw [natCast_card_filter]
    exact sum_comm
  rw [swap,sum_const,nsmul_eq_mul] at sumineq
  apply sumineq.trans
  calc _ ≤ ∑ _n ∈ J, W := by
         apply sum_le_sum
         intro n hn
         have nA := (mem_filter.mp hn).1
         have c := (card_le_card (index_subset (ha n nA).1 D hD)).trans card_image_le
         exact (show (((D.filter (fun q => n∈part A q)).card):ℝ) ≤ n.primeFactors.card by exact_mod_cast c).trans (ha n nA).2
       _ = _ := by simp [J]
end Circle299

open Finset Real
open scoped Classical
namespace Circle299
noncomputable abbrev size (D : Finset ℕ) := ∏ q ∈ D, q
noncomputable abbrev box (q : ℕ) := Icc (-(q:ℤ)) (q:ℤ)
noncomputable def candidates (P N : ℕ) (D : Finset ℕ) :=
  ((box (size D)) ×ˢ (box N)).image fun z : ℤ × ℤ => z.1*P/(size D:ℤ)+z.2
lemma box_card (q : ℕ) : (box q).card=2*q+1 := by
  rw [box,Int.card_Icc]
  omega
lemma cand_card {D : Finset ℕ} {N P : ℕ} (hn : 1≤N) (hD : ∀ q∈D, 1≤q ∧ q≤N) :
    (candidates P N D).card ≤ 9*N*N^D.card := by
  have hs : size D≤N^D.card := by
    rw [←prod_const]
    apply prod_le_prod' (fun q hq => (hD q hq).2)
  have hp : 1≤N^D.card := Nat.one_le_pow _ _ hn
  have cc := card_image_le (f:=fun z : ℤ×ℤ => z.1*P/(size D:ℤ)+z.2) (s:=(box (size D)) ×ˢ (box N))
  rw [card_product,box_card,box_card] at cc
  change (candidates P N D).card≤_ at cc
  have a : 2*size D+1≤3*N^D.card := by omega
  have b : 2*N+1≤3*N := by omega
  exact cc.trans ((Nat.mul_le_mul a b).trans_eq (by ring))
lemma distance {K : ℝ} {h x : ℤ} (hx : x∈interval h K) : |(x:ℝ)-h| ≤ K/2 := by
  obtain ⟨l,u⟩ := mem_Icc.mp hx
  have lo := Int.ceil_le.mp l
  have hi := Int.le_floor.mp u
  rw [abs_le]
  constructor <;> linarith
lemma cand_member {A : Finset ℕ} {K : ℝ} {N : ℕ} {h x : ℤ} (ha : 0∉A)
    (hK : K<((A.lcm id:ℕ):ℝ)) (hN : K≤N) (hh : h ∈ minor (A.lcm id) K)
    (hx : x ∈ interval h K) :
    (absent A x).Nonempty ∧ h∈candidates (A.lcm id) N (absent A x) := by
  let P : ℕ := A.lcm id
  let D := absent A x
  have pp : 0<P := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr (fun n hn he => ha (by simpa [id] using he ▸ hn)))
  have pr : (0:ℝ)<P := by exact_mod_cast pp
  have hd := distance hx
  have wh := Croot.abs_le_of_mem_window (mem_filter.mp hh).1
  change |(h:ℝ)|≤(P:ℝ)/2 at wh
  have ax : |(x:ℝ)| < P := by
    change K<(P:ℝ) at hK
    calc _ = |((x:ℝ)-h)+h| := by ring_nf
         _ ≤ |(x:ℝ)-h|+|(h:ℝ)| := abs_add_le _ _
         _ < _ := by linarith
  have dP : (P:ℤ)∣x*(size D:ℤ) := by
    apply Int.natAbs_dvd_natAbs.mp
    rw [Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_natCast]
    exact cover A ha x
  have qs : 0<size D := prod_pos (fun q hq => (power_mem (mem_filter.mp hq).1).1.pos)
  have az : |x|<(P:ℤ) := by exact_mod_cast ax
  have ds : D.Nonempty := by
    by_contra! empty
    have de : D=∅ := empty
    have px : (P:ℤ)∣x := by simpa [de,size] using dP
    have xz : x=0 := by
      by_contra nz
      have nb := Int.natAbs_le_of_dvd_ne_zero px nz
      have az' : x.natAbs<P := by
        exact_mod_cast (show (x.natAbs:ℤ)<P by rw [Int.natCast_natAbs]; exact az)
      simpa using (not_le_of_gt az') (by simpa using nb)
    have e := (mem_filter.mp hh).2
    subst x
    simp only [Int.cast_zero,zero_sub,abs_neg] at hd
    linarith
  refine ⟨ds,?_⟩
  obtain ⟨j,hj⟩ := dP
  have hJ : |j|≤(size D:ℤ) := by
    have eq := congrArg abs hj
    simp only [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)] at eq
    nlinarith only [eq,mul_le_mul_of_nonneg_right az.le (show 0≤(size D:ℤ) by positivity),
      (show 0<(P:ℤ) by exact_mod_cast pp)]
  have hZ : |h-x| ≤ (N:ℤ) := by
    have h0 : 0≤K/2 := (abs_nonneg _).trans hd
    have e : |(h:ℝ)-x|≤(N:ℝ) := by rw [abs_sub_comm]; linarith
    exact_mod_cast e
  refine mem_image.mpr ⟨(j,h-x), mem_product.mpr ⟨mem_Icc.mpr (abs_le.mp hJ),mem_Icc.mpr (abs_le.mp hZ)⟩,?_⟩
  change j*P/(size D:ℤ)+(h-x)=h
  rw [mul_comm j,←hj,Int.mul_ediv_cancel _ (by exact_mod_cast qs.ne')]
  ring
end Circle299

open Finset Real
open scoped Classical
namespace Circle299
lemma sparse_sum {S : Finset ℤ} {Q : Finset ℕ} {N P : ℕ} {v : ℤ→ℝ}
    (hn : 36≤N) (qbound : ∀ q∈Q, 1≤q ∧ q≤N)
    (assign : ∀ h∈S, ∃ D ⊆ Q, D.Nonempty ∧ h∈candidates P N D ∧
        v h ≤ 1/((N:ℝ)^D.card)^6) :
    ∑ h ∈ S, v h ≤ 1/4 := by
  classical
  let f (h : ℤ) := if hs : h∈S then (assign h hs).choose else ∅
  have spec {h : ℤ} (hs : h∈S) : f h⊆Q ∧ (f h).Nonempty ∧ h∈candidates P N (f h) ∧
      v h ≤ 1/((N:ℝ)^(f h).card)^6 := by
    simpa [f,hs] using (assign h hs).choose_spec
  have qsmall : Q.card ≤ N := by
    have e : Q⊆Icc 1 N := fun q hq => mem_Icc.mpr (qbound q hq)
    simpa using card_le_card e
  have rpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have nn : (36:ℝ)≤N := by exact_mod_cast hn
  have maps (h : ℤ) (hs : h∈S) : (f h).card∈Icc 1 N :=
    mem_Icc.mpr ⟨card_pos.mpr (spec hs).2.1,(card_le_card (spec hs).1).trans qsmall⟩
  have partition := sum_fiberwise_of_maps_to (s:=S) (t:=Icc 1 N) (g:=fun h => (f h).card) maps v
  rw [←partition]
  have one (j : ℕ) (hj : j∈Icc 1 N) : ∑ h ∈ S.filter (fun h => (f h).card=j), v h ≤ 1/(4*N) := by
    let J := S.filter (fun h => (f h).card=j)
    let F := Q.powersetCard j
    have sub : J⊆F.biUnion (candidates P N) := by
      intro h hh
      obtain ⟨hs,e⟩ := mem_filter.mp hh
      exact mem_biUnion.mpr ⟨f h,mem_powersetCard.mpr ⟨(spec hs).1,e⟩,(spec hs).2.2.1⟩
    have fc : F.card≤N^j := by
      rw [show F.card=Q.card.choose j from card_powersetCard _ _]
      exact (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left qsmall _)
    have card : J.card ≤ N^j*(9*N*N^j) := by
      apply (card_le_card sub).trans
      apply card_biUnion_le.trans
      calc _ ≤ ∑ _D ∈ F, 9*N*N^j := by
             apply sum_le_sum
             intro D hD
             have a := mem_powersetCard.mp hD
             simpa only [a.2] using (cand_card (P:=P) (by omega : 1≤N) (fun q hq => qbound q (a.1 hq)))
           _ = F.card*(9*N*N^j) := by simp
           _ ≤ _ := Nat.mul_le_mul_right _ fc
    let b := (N:ℝ)^j
    have bpos : 0<b := pow_pos rpos _
    have nb : (N:ℝ)≤b := by
      simpa using pow_le_pow_right₀ (by linarith : (1:ℝ)≤N) (mem_Icc.mp hj).1
    have B1 : 1≤b := by linarith
    have bound : 36*(N:ℝ)^2≤ b^4 := by
      have eq := mul_le_mul (show (36:ℝ)≤b^2 by nlinarith [sq_nonneg (b-1)]) (pow_le_pow_left₀ rpos.le nb 2) (sq_nonneg _) (sq_nonneg _)
      nlinarith only [eq]
    calc _ ≤ ∑ _h ∈ J, 1/b^6 := by
           apply sum_le_sum
           intro h hh
           obtain ⟨hs,e⟩ := mem_filter.mp hh
           simpa only [e] using (spec hs).2.2.2
         _ = J.card*(1/b^6) := by simp
         _ ≤ (b*(9*N*b))*(1/b^6) := by
           apply mul_le_mul_of_nonneg_right _ (by positivity)
           dsimp [b]
           exact_mod_cast card
         _ ≤ _ := by
           rw [mul_one_div,div_le_div_iff₀ (by positivity) (by positivity)]
           nlinarith only [mul_le_mul_of_nonneg_right bound (sq_nonneg b)]
  calc _ ≤ ∑ _j ∈ Icc 1 N, 1/(4*(N:ℝ)) := sum_le_sum one
       _ = _ := by simp; field_simp <;> ring
end Circle299

open Finset Real Filter
open scoped Classical Topology
namespace Circle299
lemma total_tail {A : Finset ℕ} {N : ℕ} {K T L Y : ℝ}
    (hn : 36≤N) (ha : 0∉A) (hK : K < ((A.lcm id:ℕ):ℝ)) (hKN : K≤N)
    (hy : 1≤Y) (hB : 2≤log (N:ℝ)) (tL : T/2≤L) (lpos : 0≤L)
    (hreg : ∀ n∈A, (n.primeFactors.card:ℝ) ≤ 2*log N)
    (hQ : ∀ q∈powers A, q≤N ∧ (q:ℝ)≤Y)
    (hP : log ((A.lcm id:ℕ):ℝ) ≤ 7*Y)
    (scale : 100*(log N)^3*Y ≤ (K/N)^2*T)
    (good : ∀ h : ℤ, T ≤ ((miss A K h).card:ℝ) ∨ ∃ x∈interval h K,
      ∀ q∈powers A, ((((miss A K h).filter (fun n => n∈part A q)).card:ℝ) < L/q) → (q:ℤ)∣x) :
    ∑ h∈minor (A.lcm id) K, damp A N K h ≤ 1/2 := by
  classical
  let P : ℕ := A.lcm id
  let F := minor P K
  let E := F.filter fun h => T ≤ ((miss A K h).card:ℝ)
  let S := F \ E
  let r := (K/N)^2
  let B := log (N:ℝ)
  have pp : 0<P := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr (fun n hn he => ha (by simpa [id] using he ▸ hn)))
  have pr : (0:ℝ)<P := by exact_mod_cast pp
  have nr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have yy : 0<Y := by linarith
  have bb : 2≤B := hB
  have rp : 0≤r := sq_nonneg _
  change 100*B^3*Y ≤ r*T at scale
  have hl4 : log 4 ≤ 3 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have big : r*T ≥ log 4+log P := by
    have z : 1≤B^3 := one_le_pow₀ (by linarith : 1≤B)
    have m := mul_le_mul_of_nonneg_right z yy.le
    change log (P:ℝ)≤7*Y at hP
    nlinarith only [m,hl4,hP,scale,hy]
  have heavy : ∑ h∈E, damp A N K h ≤ 1/4 := by
    have point (h : ℤ) (he : h∈E) : damp A N K h ≤ 1/(4*P) := by
      have e := mul_le_mul_of_nonneg_left (mem_filter.mp he).2 rp
      change exp (-r*(miss A K h).card) ≤ _
      rw [one_div,←exp_log (by positivity : (0:ℝ)<4*P),←exp_neg,exp_le_exp,log_mul (by norm_num) pr.ne']
      linarith
    calc _ ≤ ∑ _h∈E, 1/(4*(P:ℝ)) := sum_le_sum point
         _ ≤ (P:ℝ)*(1/(4*P)) := by
           simp only [sum_const,nsmul_eq_mul]
           apply mul_le_mul_of_nonneg_right _ (by positivity)
           exact_mod_cast (card_le_card (show E⊆span P from (filter_subset _ _).trans (filter_subset _ _))).trans_eq (Croot.card_window P)
         _ = _ := by field_simp
  have dscale : 6*B*(2*B*Y) ≤ r*L := by
    have e := mul_le_mul_of_nonneg_left tL rp
    have bound := mul_le_mul_of_nonneg_right (show 24*B^2 ≤ 100*B^3 by nlinarith [mul_nonneg (sq_nonneg B) (show 0≤B-2 by linarith)]) yy.le
    nlinarith only [bound,scale,e]
  have small : ∑ h∈S, damp A N K h ≤ 1/4 := by
    apply sparse_sum (P:=P) (Q:=powers A) hn (fun q hq => ⟨(power_mem hq).1.pos,(hQ q hq).1⟩)
    intro h hs
    obtain ⟨hf,he⟩ := mem_sdiff.mp hs
    have nt : ¬ T≤((miss A K h).card:ℝ) := fun e => he (mem_filter.mpr ⟨hf,e⟩)
    obtain ⟨x,hx,prop⟩ := (good h).resolve_left nt
    let D := absent A x
    have de := cand_member ha hK hKN hf hx
    refine ⟨D,filter_subset _ _,de.1,de.2,?_⟩
    have cnt := missed_count (A:=A) (D:=D) (h:=h) (K:=K)
      (fun n hn => ⟨(by rintro rfl; exact ha hn),hreg n hn⟩)
      (filter_subset _ _) (fun q hq => (hQ q (mem_filter.mp hq).1).2) yy lpos (by positivity : 0≤2*log (N:ℝ))
      (fun q hq => le_of_not_gt (fun e => (mem_filter.mp hq).2 (prop q (mem_filter.mp hq).1 e)))
    change D.card*(L/Y) ≤ (miss A K h).card*(2*B) at cnt
    rw [←mul_div_assoc,div_le_iff₀ yy] at cnt
    have c := mul_le_mul_of_nonneg_left cnt rp
    have a := mul_le_mul_of_nonneg_right dscale (Nat.cast_nonneg D.card : (0:ℝ)≤D.card)
    have e : 6*B*D.card*(2*B*Y) ≤ (r*(miss A K h).card)*(2*B*Y) := by nlinarith only [c,a]
    have div := le_of_mul_le_mul_right e (by positivity : 0<2*B*Y)
    change exp (-r*(miss A K h).card) ≤ _
    rw [one_div,←exp_log (by positivity : 0<((N:ℝ)^D.card)^6),←exp_neg,exp_le_exp,log_pow,log_pow]
    change _ ≤ -(6*(D.card*B))
    linarith
  have e := sum_sdiff (f:=damp A N K) (show E⊆F from filter_subset _ _)
  change (∑ h∈S, damp A N K h)+(∑ h∈E, damp A N K h)=_ at e
  change (∑ h∈F, damp A N K h)≤_
  linarith
end Circle299

open Filter Real Finset
open scoped Classical Topology
namespace BloomScale
noncomputable abbrev B (N:ℕ) := log (N:ℝ)
noncomputable abbrev w (N:ℕ) := log (B N)
noncomputable abbrev M (N:ℕ) := (N:ℝ)^(1-1/w N)
noncomputable abbrev K (N:ℕ) := M N*(N:ℝ)^(-2/w N)
noncomputable abbrev Y (N:ℕ) := (N:ℝ)^(1-8/w N)
noncomputable abbrev T (N:ℕ) := M N/B N
noncomputable abbrev L (N:ℕ) := M N/(2*(B N)^(1/100:ℝ))
noncomputable abbrev U (N:ℕ) := (N:ℝ)^(1/w N)
lemma large (c : ℝ) : ∀ᶠ N : ℕ in atTop,
    1<N ∧ 8≤w N ∧ 2≤B N ∧ 0<K N ∧ K N<M N ∧ M N≤N ∧
    1≤Y N ∧ T N/2≤L N ∧ c*(B N)^3*Y N ≤ (K N/N)^2*T N := by
  have bt : Tendsto B atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have wt : Tendsto w atTop atTop := tendsto_log_atTop.comp bt
  have hs : Tendsto (fun x : ℝ => (log x)^(2:ℕ)/x) atTop (𝓝 0) := by
    simpa using (isLittleO_log_rpow_rpow_atTop 2 (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
  filter_upwards [eventually_gt_atTop 1,wt.eventually_ge_atTop 8,bt.eventually_ge_atTop 2,
      bt.eventually_ge_atTop c,(hs.comp bt).eventually_lt_const (show (0:ℝ)<1/8 by norm_num)]
    with N hn hw hb hbc hs
  have nr : (1:ℝ)<N := by exact_mod_cast hn
  have np : 0<(N:ℝ) := by linarith
  have bp : 0<B N := by linarith
  have wp : 0<w N := by linarith
  have up : 1<U N := one_lt_rpow nr (by positivity)
  have up0 : 0<U N := by linarith
  have h : (B N)^8 ≤ U N := by
    apply (log_le_log_iff (by positivity) up0).mp
    rw [log_pow,log_rpow np]
    change (w N)^2/B N < 1/8 at hs
    have g := (div_lt_iff₀ bp).mp hs
    change (8:ℝ)*w N ≤ 1/w N*B N
    rw [one_div_mul_eq_div,le_div_iff₀ wp]
    nlinarith only [g]
  have powU (i : ℕ) : (N:ℝ)^((i:ℝ)/w N) = U N^i := by
    rw [←Real.rpow_natCast (U N),←rpow_mul np.le]
    congr 1
    ring
  have ms : M N=(N:ℝ)/U N := by rw [M,rpow_sub np,rpow_one]
  have ks : K N=(N:ℝ)/U N^3 := by
    rw [K,ms,show (-2:ℝ)/w N=-(2/w N) by ring,rpow_neg np.le,show (N:ℝ)^(2/w N)=U N^2 by simpa using powU 2]
    field_simp
    <;> ring
  have ys : Y N=(N:ℝ)/U N^8 := by
    rw [Y,rpow_sub np,rpow_one,show (N:ℝ)^(8/w N)=U N^8 by simpa using powU 8]
  have mpos : 0<M N := rpow_pos_of_pos np _
  refine ⟨hn,hw,hb,by rw [ks]; positivity,?_,?_,?_,?_,?_⟩
  · rw [ks,ms]
    exact div_lt_div_of_pos_left np up0 (by nlinarith [sq_pos_of_pos up0,mul_pos up0 (sub_pos.mpr up),mul_pos up0 (show 0<U N^2-1 by nlinarith [sq_nonneg (U N-1)])])
  · rw [ms]
    exact div_le_self np.le up.le
  · apply one_le_rpow nr.le
    have : 8/w N≤1 := (div_le_one wp).mpr hw
    linarith
  · have le : (B N)^(1/100:ℝ) ≤ B N := by
      simpa using (rpow_le_rpow_of_exponent_le (by linarith : 1≤B N) (show (1/100:ℝ)≤1 by norm_num))
    rw [T,L,div_div]
    apply div_le_div_of_nonneg_left mpos.le (by positivity)
    linarith
  · have eq : (K N/N)^2*T N = Y N*U N/B N := by
      rw [T,ks,ms,ys]
      field_simp
      <;> ring
    rw [eq,le_div_iff₀ bp]
    have hpow : B N^5≤B N^8 := pow_le_pow_right₀ (by linarith) (by omega)
    have v : c*B N^4 ≤ U N := by
      calc _ ≤ B N^5 := by nlinarith only [mul_le_mul_of_nonneg_right hbc (pow_nonneg bp.le 4)]
           _ ≤ _ := hpow.trans h
    have := mul_le_mul_of_nonneg_right v (rpow_pos_of_pos np (1-8/w N)).le
    change c*B N^4*Y N ≤ U N*Y N at this
    nlinarith only [this]
end BloomScale

open Real Filter Finset
open scoped Classical Topology
namespace Circle299
open BloomScale
lemma lcm_est {Y : ℝ} (hy : 0≤Y) {A : Finset ℕ} (ha : 0∉A)
    (smooth : ∀ n∈A, ∀ q : ℕ, IsPrimePow q → q∣n → (q:ℝ)≤Y) :
    log ((A.lcm id:ℕ):ℝ) ≤ 7*Y := by
  have hd : A.lcm id ∣ Nat.lcmUpto ⌊Y⌋₊ := by
    apply Finset.lcm_dvd
    intro n hn
    have nz : n≠0 := by rintro rfl; exact ha hn
    apply Croot.PPSmooth.dvd_lcmUpto _ nz
    intro p hp
    have pr := Nat.prime_of_mem_primeFactors hp
    have f : 0<n.factorization p := Nat.pos_of_ne_zero (by simpa only [←Finsupp.mem_support_iff,Nat.support_factorization] using hp)
    exact Nat.le_floor (smooth n hn (p^n.factorization p) (pr.isPrimePow.pow f.ne') (Nat.ordProj_dvd n p))
  have ppos : 0<A.lcm id := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun n hn h => ha (by simpa [id] using h ▸ hn))
  have logle := log_le_log (show (0:ℝ)<(A.lcm id:ℕ) by exact_mod_cast ppos)
    (show ((A.lcm id:ℕ):ℝ)≤Nat.lcmUpto ⌊Y⌋₊ by exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos _) hd)
  rw [←Chebyshev.psi_eq_log_lcmUpto] at logle
  have hh := Chebyshev.psi_le_const_mul_self (x:=(⌊Y⌋₊:ℝ)) (by positivity)
  have l4 : log 4≤3 := by linarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  have f := Nat.floor_le hy
  nlinarith only [logle,hh,mul_le_mul_of_nonneg_right l4 (Nat.cast_nonneg ⌊Y⌋₊ : (0:ℝ)≤⌊Y⌋₊),f]
theorem complete : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H4 := by
  classical
  intro z
  filter_upwards [BloomScale.large (100*(z+1)),eventually_ge_atTop 36] with N sc hn
  obtain ⟨n1,hw,hb,kpos,km,mn,hy,tl,sc⟩ := sc
  intro A d hd dz ha an reg balance good
  let P : ℕ := A.lcm id
  have pp : 0<P := Nat.pos_of_ne_zero (lcm_ne_zero_iff.mpr fun n hn he => ha (by simpa [id] using he ▸ hn))
  have nr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have dr : (0:ℝ)<d := by exact_mod_cast hd
  have zr : (0:ℝ)≤z := by positivity
  have dzr : (d:ℝ)≤z := by exact_mod_cast dz
  have yy : 0<Y N := by linarith
  have bp : 0<B N := by linarith
  have mp : 0<M N := kpos.trans km
  have lp : 0<L N := by dsimp [L]; exact div_pos mp (mul_pos (by norm_num) (rpow_pos_of_pos bp _))
  obtain ⟨hi,lo,dp,_⟩ := balance
  have cast_sum : (Croot.recipSum A:ℝ) = ∑ n∈A,(1:ℝ)/n := by simp [Croot.recipSum]
  have lower : 2/(d:ℝ)-1/M N ≤ Croot.recipSum A := by rwa [cast_sum]
  have upper : (Croot.recipSum A:ℝ) < 2/d := by rwa [cast_sum]
  have hnr (n : ℕ) (hn : n∈A) : 0<n ∧ M N≤n ∧ n≤N :=
    ⟨Nat.pos_of_ne_zero (by rintro rfl; exact ha hn),(reg n hn).1,(mem_range.mp (an hn)).le⟩
  have smooth (n : ℕ) (hn : n∈A) := (reg n hn).2.1
  have logp := lcm_est yy.le ha smooth
  change log (P:ℝ) ≤ 7*Y N at logp
  have rat : (K N/N)^2≤1 := by
    have e := (div_le_one nr).mpr (km.le.trans mn)
    have pos : 0≤K N/(N:ℝ) := by positivity
    nlinarith [mul_nonneg pos (sub_nonneg.mpr e)]
  have rT : (K N/N)^2*T N ≤ M N := by
    have tp : 0≤T N := div_nonneg mp.le bp.le
    calc _ ≤ 1*T N := mul_le_mul_of_nonneg_right rat tp
         _ ≤ _ := by simpa [T] using (div_le_self mp.le (by linarith : 1≤B N))
  have bc : 1≤B N^3 := one_le_pow₀ (by linarith)
  have g := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bc (show 0≤100*((z:ℝ)+1) by positivity)) yy.le
  have huge : 100*((z:ℝ)+1)*Y N≤M N := by linarith only [g,sc,rT]
  have base : 100*(B N)^3*Y N≤(K N/N)^2*T N := by
    have e := mul_le_mul_of_nonneg_right (show (100:ℝ)≤100*((z:ℝ)+1) by linarith) (mul_nonneg (pow_nonneg bp.le 3) yy.le)
    nlinarith only [e,sc]
  have lowcard : 2*(M N/d)-1 ≤ (A.card:ℝ) := by
    have ess : (Croot.recipSum A:ℝ) ≤ A.card*(1/M N) := by
      rw [cast_sum]
      calc _ ≤ ∑ _n∈A, 1/M N := sum_le_sum fun n hn => one_div_le_one_div_of_le mp (hnr n hn).2.1
           _ = _ := by simp
    have e := mul_le_mul_of_nonneg_right (lower.trans ess) mp.le
    field_simp [mp.ne',dr.ne'] at e ⊢
    nlinarith
  have many : 100*Y N≤M N/d := by
    rw [le_div_iff₀ dr]
    nlinarith only [huge,mul_le_mul_of_nonneg_right dzr yy.le,hy]
  have period : (P:ℝ)<(2:ℝ)^A.card/2 := by
    have e : 1/2≤log (2:ℝ) := by have h := one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2); norm_num at h; linarith
    apply (log_lt_log_iff (by exact_mod_cast pp) (by positivity)).mp
    rw [log_div (by positivity) (by norm_num),log_pow]
    have ec := mul_le_mul_of_nonneg_left e (show 0≤(A.card:ℝ)-1 by linarith)
    nlinarith only [ec,logp,lowcard,many,hy]
  have ne : A.Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ)<A.card by linarith))
  obtain ⟨n,hnA⟩ := ne
  have np : n≤P := Nat.le_of_dvd pp (dvd_lcm hnA)
  have kp : K N < (P:ℝ) := km.trans_le ((hnr n hnA).2.1.trans (by exact_mod_cast np))
  apply extract (N:=N) (K:=K N) (M:=M N) (by omega) hd kpos.le km.le mn mp hnr dp upper lower period
  refine total_tail hn ha kp (km.le.trans mn) hy hb tl lp.le ?_ ?_ logp base ?_
  · intro n hn
    have up := (reg n hn).2.2.2
    change (n.primeFactors.card:ℝ)≤2*w N at up
    have e := log_le_sub_one_of_pos bp
    change log (B N) ≤ B N-1 at e
    change _ ≤ 2*B N
    dsimp [w] at up
    linarith
  · intro q hq
    obtain ⟨pr,n,hn,_,dv,_⟩ := power_mem hq
    exact ⟨(Nat.le_of_dvd (hnr n hn).1 dv).trans (hnr n hn).2.2,smooth n hn q pr dv⟩
  · intro h
    have gh := good (h:ℝ)
    rcases gh with big|⟨x,hx,hxq⟩
    · exact Or.inl big
    · refine Or.inr ⟨x,hx,fun q hq e => hxq q hq ?_⟩
      have sets : (miss A (K N) h).filter (fun n => n ∈ part A q) =
          (part A q).filter (fun n : ℕ => ∀ x ∈ interval h (K N), ¬(n:ℤ)∣x) := by ext n; simp [miss,part,and_left_comm,and_assoc,and_comm]
      rw [sets] at e
      exact e
end Circle299

theorem OMA.solution : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1.H4 := Circle299.complete
