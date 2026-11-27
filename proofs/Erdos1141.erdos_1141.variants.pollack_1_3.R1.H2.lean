import OMAReductions.R_Erdos1141_erdos_1141_variants_pollack_1_3_R1
import Mathlib

/-!
Siegel's lower bound for quadratic L-values in Pollack's Theorem 1.3.
Adapted from the Pollack17 development imported by Boris Alexeev in plby/lean-proofs,
whose enclosing formalization credits GPT-5.4 Pro and Yuta Oriike,
commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e, and the BoundedGaps
contributors, frenzymath/FormalPantheon (Apache License 2.0), commit ffbb65c21afc8a36ace67720f1b0df1c63d26bd1.
-/

/-! ## Positive divisor-pair reindexing

Source module `BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

def positiveFactorPairs (Q : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc 0 Q ×ˢ Finset.Ioc 0 Q).filter
    (fun p ↦ p.1 * p.2 ≤ Q)

theorem sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ p ∈ q.divisorsAntidiagonal, f p.1 p.2) =
      ∑ p ∈ positiveFactorPairs Q, f p.1 p.2 := by
  let T : Finset ℕ := Finset.Ioc 0 Q
  let g : ℕ × ℕ → ℕ := fun p ↦ p.1 * p.2
  have hmaps : ∀ p ∈ positiveFactorPairs Q, g p ∈ T := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact Finset.mem_Ioc.mpr ⟨Nat.mul_pos hp₁.1 hp₂.1, hprod⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := positiveFactorPairs Q) (t := T) hmaps
    (fun p ↦ f p.1 p.2)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (N := Q)]
  · apply Finset.sum_congr
    · ext p
      simp only [positiveFactorPairs, g, Finset.mem_filter]
      constructor
      · rintro ⟨hp, hprod⟩
        exact ⟨⟨hp, hprod.le.trans (Finset.mem_Ioc.mp hq).2⟩, hprod⟩
      · rintro ⟨⟨hp, _⟩, hprod⟩
        exact ⟨hp, hprod⟩
    · intro p _
      rfl
  · exact (Finset.mem_Ioc.mp hq).1.ne'
  · exact (Finset.mem_Ioc.mp hq).2

theorem sum_divisors_up_to_eq_sum_positiveFactorPairs
    {Q : ℕ} {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) :
    (∑ q ∈ Finset.Ioc 0 Q,
      ∑ d ∈ q.divisors, f q d) =
      ∑ p ∈ positiveFactorPairs Q,
        f (p.1 * p.2) p.1 := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q, ∑ d ∈ q.divisors, f q d) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ p ∈ q.divisorsAntidiagonal,
            f (p.1 * p.2) p.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [← Nat.sum_divisorsAntidiagonal
        (f := fun d _k ↦ f q d)]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [hp.1]
    _ = _ :=
      sum_divisorsAntidiagonal_up_to_eq_sum_positiveFactorPairs
        (fun d k ↦ f (d * k) d)

end BoundedGaps.Maynard

end

/-! ## Cross-level characters in Goldfeld's argument

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldCrossLevelCharacters`. -/

noncomputable section

namespace BoundedGaps.Maynard

def goldfeldCharactersDistinct {q1 q : ℕ}
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q) : Prop :=
  chi1.changeLevel (Nat.dvd_lcm_left q1 q) ≠
    chi.changeLevel (Nat.dvd_lcm_right q1 q)

theorem goldfeldCharactersDistinct_same_level_iff
    {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter Complex q) :
    goldfeldCharactersDistinct chi1 chi ↔ chi1 ≠ chi := by
  letI : NeZero (Nat.lcm q q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q) (NeZero.ne q)⟩
  unfold goldfeldCharactersDistinct
  rw [show Nat.dvd_lcm_right q q = Nat.dvd_lcm_left q q from
    Subsingleton.elim _ _]
  exact (DirichletCharacter.changeLevel_injective
    (R := Complex) (Nat.dvd_lcm_left q q)).ne_iff

theorem goldfeldCharactersDistinct_of_modulus_ne
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q)
    (hprimitive1 : DirichletCharacter.IsPrimitive chi1)
    (hprimitive : DirichletCharacter.IsPrimitive chi)
    (hmodulus : q1 ≠ q) :
    goldfeldCharactersDistinct chi1 chi := by
  letI : NeZero (Nat.lcm q1 q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩
  rw [goldfeldCharactersDistinct]
  intro heq
  apply hmodulus
  have hconductor := congrArg DirichletCharacter.conductor heq
  rw [chi1.conductor_changeLevel, chi.conductor_changeLevel] at hconductor
  exact hprimitive1.symm.trans (hconductor.trans hprimitive)

private lemma GoldfeldCrossLevelCharacters_changeLevel_sq_eq_one
    {q m : ℕ} (hqm : q ∣ m)
    (chi : DirichletCharacter Complex q) (hsquare : chi ^ 2 = 1) :
    (chi.changeLevel hqm) ^ 2 = 1 := by
  rw [← map_pow, hsquare, map_one]

theorem goldfeldCrossLevelMul_ne_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter Complex q1)
    (chi : DirichletCharacter Complex q)
    (hsquare1 : chi1 ^ 2 = 1)
    (hdistinct : goldfeldCharactersDistinct chi1 chi) :
    DirichletCharacter.mul chi1 chi ≠ 1 := by
  intro hprincipal
  apply hdistinct
  have hsquareLift := GoldfeldCrossLevelCharacters_changeLevel_sq_eq_one
    (Nat.dvd_lcm_left q1 q) chi1 hsquare1
  have hproduct :
      chi1.changeLevel (Nat.dvd_lcm_left q1 q) *
          chi.changeLevel (Nat.dvd_lcm_right q1 q) = 1 := by
    simpa [DirichletCharacter.mul] using hprincipal
  have hinv :
      (chi1.changeLevel (Nat.dvd_lcm_left q1 q))⁻¹ =
        chi1.changeLevel (Nat.dvd_lcm_left q1 q) := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hsquareLift
  exact ((eq_inv_of_mul_eq_one_right hproduct).trans hinv).symm

end BoundedGaps.Maynard

end

/-! ## The inducing Dirichlet Euler product

Source module `BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProduct`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private local instance InducingEulerProduct_conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

noncomputable def inducingEulerProduct
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors,
    (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))

private lemma InducingEulerProduct_primitiveCharacter_ne_one_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hpsi
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter]
  exact (DirichletCharacter.changeLevel_eq_one_iff
    chi.conductor_dvd_level).2 hpsi

theorem LFunction_eq_inducingPrimitive_mul_inducingEulerProduct
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hguard : chi ≠ 1 ∨ s ≠ 1) :
    DirichletCharacter.LFunction chi s =
      DirichletCharacter.LFunction chi.primitiveCharacter s *
        inducingEulerProduct chi s := by
  have hprimitiveGuard : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1 :=
    hguard.imp (InducingEulerProduct_primitiveCharacter_ne_one_of_ne_one chi) id
  calc
    DirichletCharacter.LFunction chi s =
        DirichletCharacter.LFunction
          (DirichletCharacter.changeLevel chi.conductor_dvd_level
            chi.primitiveCharacter) s := by
      rw [chi.changeLevel_primitiveCharacter]
    _ = DirichletCharacter.LFunction chi.primitiveCharacter s *
        ∏ p ∈ q.primeFactors,
          (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)) :=
      DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
        chi.primitiveCharacter hprimitiveGuard
    _ = _ := rfl

private lemma InducingEulerProduct_norm_character_mul_cpow_lt_one
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    ‖psi p * (p : ℂ) ^ (-s)‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re]
  calc
    ‖psi p‖ * (p : ℝ) ^ (-s.re) ≤
        1 * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (psi.norm_le_one p)
        (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ < 1 := by
      simpa using
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos hs)

private lemma InducingEulerProduct_inducingEulerFactor_ne_zero_of_re_pos
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    (1 : ℂ) - psi p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have hw : psi p * (p : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm := InducingEulerProduct_norm_character_mul_cpow_lt_one psi p hp s hs
  rw [hw, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

theorem inducingEulerProduct_ne_zero_of_re_pos
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    inducingEulerProduct chi s ≠ 0 := by
  rw [inducingEulerProduct, Finset.prod_ne_zero_iff]
  intro p hp
  exact InducingEulerProduct_inducingEulerFactor_ne_zero_of_re_pos chi.primitiveCharacter p
    (Nat.prime_of_mem_primeFactors hp) s hs

end BoundedGaps.Maynard

end

/-! ## Fixed-strip Dirichlet Gamma-factor ratio

Source module `BoundedGaps.BombieriVinogradov.Analytic.FixedStripGammaRatio`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Set MeasureTheory

private lemma FixedStripGammaRatio_one_div_Gamma_eq_prod_mul_one_div_Gamma_add_nat
    (z : ℂ) (n : ℕ) :
    (Complex.Gamma z)⁻¹ =
      (∏ j ∈ Finset.range n, (z + j)) * (Complex.Gamma (z + n))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ih, Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one,
        Finset.prod_range_succ, Nat.cast_succ]
      ring_nf

private lemma FixedStripGammaRatio_Gamma_div_Gamma_eq_prod_mul_beta_div
    (w X : ℂ) (d : ℝ) (hX : 0 < X.re) (hd : 0 < d)
    (hsum : X + (d : ℂ) = w + 11) :
    Complex.Gamma X / Complex.Gamma w =
      (∏ j ∈ Finset.range 11, (w + j)) *
        (Complex.betaIntegral X d / Complex.Gamma d) := by
  have hXd : 0 < (X + (d : ℂ)).re := by simp; linarith
  have hGXd := Complex.Gamma_ne_zero_of_re_pos hXd
  have hGd := Complex.Gamma_ne_zero_of_re_pos
    (show 0 < ((d : ℂ)).re by simpa)
  rw [div_eq_mul_inv, FixedStripGammaRatio_one_div_Gamma_eq_prod_mul_one_div_Gamma_add_nat w 11]
  have hsum' : w + (11 : ℕ) = X + (d : ℂ) := by simpa using hsum.symm
  rw [hsum', Complex.betaIntegral_eq_Gamma_mul_div X d hX
    (show 0 < ((d : ℂ)).re by simpa)]
  field_simp [hGXd, hGd]

private lemma FixedStripGammaRatio_norm_betaIntegral_fixed_re_le
    {u : ℂ} {q : ℝ} (hu : (1 / 4 : ℝ) ≤ u.re)
    (hq : (1 / 2 : ℝ) ≤ q) :
    ‖Complex.betaIntegral u q‖ ≤ 12 := by
  rw [Complex.betaIntegral]
  let f : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ ((q : ℂ) - 1)
  let g : ℝ → ℝ := fun x =>
    2 * x ^ (-(3 / 4 : ℝ)) + 2 * (1 - x) ^ (-(1 / 2 : ℝ))
  have hxpow : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hhalfpow :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hsubpow :
      IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    simpa only [sub_zero, sub_self] using (hhalfpow.comp_sub_left 1).symm
  have hg : IntervalIntegrable g volume 0 1 :=
    (hxpow.const_mul 2).add (hsubpow.const_mul 2)
  have hf : IntervalIntegrable f volume 0 1 :=
    Complex.betaIntegral_convergent
      (lt_of_lt_of_le (by norm_num) hu)
      (show 0 < ((q : ℂ)).re by simp; linarith)
  have hpoint : ∀ x : ℝ, x ∈ Icc 0 1 → ‖f x‖ ≤ g x := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · have hzero : ‖(0 : ℂ) ^ (u - 1)‖ ≤ 1 := by
        by_cases h : u - 1 = 0
        · rw [h, Complex.cpow_zero, norm_one]
        · rw [Complex.zero_cpow h, norm_zero]
          norm_num
      have htwo : ‖(0 : ℂ) ^ (u - 1)‖ ≤ 2 := hzero.trans (by norm_num)
      simpa [f, g] using htwo
    rcases eq_or_ne x 1 with rfl | hx1
    · have hzero : ‖(0 : ℂ) ^ ((q : ℂ) - 1)‖ ≤ 1 := by
        by_cases h : (q : ℂ) - 1 = 0
        · rw [h, Complex.cpow_zero, norm_one]
        · rw [Complex.zero_cpow h, norm_zero]
          norm_num
      have htwo : ‖(0 : ℂ) ^ ((q : ℂ) - 1)‖ ≤ 2 := hzero.trans (by norm_num)
      simpa [f, g] using htwo
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    have hsubpos : 0 < 1 - x := sub_pos.mpr hxlt
    dsimp [f]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos hsubpos]
    simp only [sub_re, one_re, ofReal_re]
    have hxpow_le : x ^ (u.re - 1) ≤ x ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hxpos hx.2 (by linarith)
    have hsubpow_le :
        (1 - x) ^ (q - 1) ≤ (1 - x) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hsubpos (sub_le_self 1 hxpos.le) (by linarith)
    have hxnonneg := Real.rpow_nonneg hxpos.le (u.re - 1)
    have hsubnonneg := Real.rpow_nonneg hsubpos.le (q - 1)
    have hbase :
        x ^ (u.re - 1) * (1 - x) ^ (q - 1) ≤
          x ^ (-(3 / 4 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul hxpow_le hsubpow_le hsubnonneg
        (Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ)))
    have hmajor :
        x ^ (-(3 / 4 : ℝ)) * (1 - x) ^ (-(1 / 2 : ℝ)) ≤ g x := by
      by_cases hhalf : x ≤ 1 / 2
      · have hsubhalf : (1 / 2 : ℝ) ≤ 1 - x := by linarith
        have hone :
            (1 - x) ^ (-(1 / 2 : ℝ)) ≤ (1 - x) ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hsubpos (sub_le_self 1 hxpos.le) (by norm_num)
        have hinv : (1 - x) ^ (-(1 : ℝ)) ≤ 2 := by
          rw [Real.rpow_neg_one, ← one_div]
          exact (one_div_le hsubpos (by norm_num)).2 hsubhalf
        dsimp [g]
        have hxrp := Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ))
        have hsrp := Real.rpow_nonneg hsubpos.le (-(1 / 2 : ℝ))
        nlinarith
      · have hxhalf : (1 / 2 : ℝ) ≤ x := le_of_not_ge hhalf
        have hone :
            x ^ (-(3 / 4 : ℝ)) ≤ x ^ (-(1 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hxpos hx.2 (by norm_num)
        have hinv : x ^ (-(1 : ℝ)) ≤ 2 := by
          rw [Real.rpow_neg_one, ← one_div]
          exact (one_div_le hxpos (by norm_num)).2 hxhalf
        dsimp [g]
        have hxrp := Real.rpow_nonneg hxpos.le (-(3 / 4 : ℝ))
        have hsrp := Real.rpow_nonneg hsubpos.le (-(1 / 2 : ℝ))
        nlinarith
    exact hbase.trans hmajor
  calc
    _ ≤ ∫ x in (0 : ℝ)..1, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x in (0 : ℝ)..1, g x :=
      intervalIntegral.integral_mono_on (by norm_num) hf.norm hg hpoint
    _ = 12 := by
      dsimp [g]
      rw [intervalIntegral.integral_add (hxpow.const_mul 2) (hsubpow.const_mul 2),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      have hsub :
          (∫ x in (0 : ℝ)..1, (1 - x) ^ (-(1 / 2 : ℝ))) =
            ∫ x in (0 : ℝ)..1, x ^ (-(1 / 2 : ℝ)) := by
        simpa using intervalIntegral.integral_comp_sub_left
          (a := (0 : ℝ)) (b := 1) (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1
      rw [hsub, integral_rpow (Or.inl (by norm_num)),
        integral_rpow (Or.inl (by norm_num))]
      norm_num

private lemma FixedStripGammaRatio_exists_norm_one_div_Gamma_Icc_le :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℝ, (1 / 2 : ℝ) ≤ d → d ≤ 11 →
      ‖(Complex.Gamma (d : ℂ))⁻¹‖ ≤ K := by
  have hcont : Continuous (fun d : ℝ => ‖(Complex.Gamma (d : ℂ))⁻¹‖) :=
    (Complex.differentiable_one_div_Gamma.continuous.comp
      Complex.continuous_ofReal).norm
  obtain ⟨c, hc⟩ := bddAbove_def.mp
    (IsCompact.bddAbove_image isCompact_Icc hcont.continuousOn)
  let K : ℝ := max c 0 + 1
  refine ⟨K, by dsimp [K]; linarith [le_max_right c 0], ?_⟩
  intro d hd hd11
  have hdmem : d ∈ Icc (1 / 2 : ℝ) 11 := ⟨hd, hd11⟩
  exact (hc _ (mem_image_of_mem _ hdmem)).trans
    (by dsimp [K]; linarith [le_max_left c 0])

private lemma FixedStripGammaRatio_norm_prod_range_eleven_add_le
    (w : ℂ) (t : ℝ)
    (hwlower : -(5 : ℝ) ≤ w.re) (hwupper : w.re ≤ (3 / 4 : ℝ))
    (hwim : |w.im| = |t| / 2) :
    ‖∏ j ∈ Finset.range 11, (w + j)‖ ≤
      (6 : ℝ) ^ 11 * (|t| + 2) ^ 11 := by
  have hfactor : ∀ j ∈ Finset.range 11,
      ‖w + (j : ℂ)‖ ≤ 6 * (|t| + 2) := by
    intro j hj
    have hjlt : j < 11 := Finset.mem_range.mp hj
    have hjle : j ≤ 10 := Nat.le_pred_of_lt hjlt
    have hjreal : (j : ℝ) ≤ 10 := by exact_mod_cast hjle
    have hjnonneg : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hreabs : |(w + (j : ℂ)).re| ≤ 43 / 4 := by
      rw [add_re, natCast_re]
      apply abs_le.mpr
      constructor <;> linarith
    have himabs : |(w + (j : ℂ)).im| = |t| / 2 := by
      simp only [add_im, natCast_im, add_zero, hwim]
    calc
      ‖w + (j : ℂ)‖ ≤ |(w + (j : ℂ)).re| + |(w + (j : ℂ)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 43 / 4 + |t| / 2 := by rw [himabs]; gcongr
      _ ≤ 6 * (|t| + 2) := by nlinarith [abs_nonneg t]
  calc
    ‖∏ j ∈ Finset.range 11, (w + j)‖ ≤
        ∏ j ∈ Finset.range 11, ‖w + (j : ℂ)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ _j ∈ Finset.range 11, (6 * (|t| + 2)) := by
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfactor
    _ = (6 * (|t| + 2)) ^ 11 := by simp
    _ = (6 : ℝ) ^ 11 * (|t| + 2) ^ 11 := by ring

private lemma FixedStripGammaRatio_norm_Gamma_div_Gamma_fixedStrip_le
    (K : ℝ)
    (hK : ∀ d : ℝ, (1 / 2 : ℝ) ≤ d → d ≤ 11 →
      ‖(Complex.Gamma (d : ℂ))⁻¹‖ ≤ K)
    (a : ℝ) (s : ℂ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hslo : -(10 : ℝ) ≤ s.re) (hshi : s.re ≤ (1 / 2 : ℝ)) :
    ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
        Complex.Gamma ((s + (a : ℂ)) / 2)‖ ≤
      (12 * K * 6 ^ 11) * (|s.im| + 2) ^ 11 := by
  let w : ℂ := ((starRingEnd ℂ) s + (a : ℂ)) / 2
  let X : ℂ := (1 - s + (a : ℂ)) / 2
  let d : ℝ := 21 / 2 + s.re
  have hwlower : -(5 : ℝ) ≤ w.re := by
    rw [show w.re = (s.re + a) / 2 by norm_num [w]]
    linarith
  have hwupper : w.re ≤ (3 / 4 : ℝ) := by
    rw [show w.re = (s.re + a) / 2 by norm_num [w]]
    linarith
  have hwim : |w.im| = |s.im| / 2 := by
    rw [show w.im = -s.im / 2 by norm_num [w], abs_div, abs_neg]
    norm_num
  have hX : (1 / 4 : ℝ) ≤ X.re := by
    rw [show X.re = (1 - s.re + a) / 2 by norm_num [X]]
    linarith
  have hdlo : (1 / 2 : ℝ) ≤ d := by dsimp [d]; linarith
  have hdhi : d ≤ 11 := by dsimp [d]; linarith
  have hsum : X + (d : ℂ) = w + 11 := by
    dsimp [X, d, w]
    apply Complex.ext
    · norm_num
      ring
    · norm_num
  have hidentity := FixedStripGammaRatio_Gamma_div_Gamma_eq_prod_mul_beta_div w X d
    (lt_of_lt_of_le (by norm_num) hX) (lt_of_lt_of_le (by norm_num) hdlo) hsum
  have hwconj : w = (starRingEnd ℂ) ((s + (a : ℂ)) / 2) := by
    dsimp [w]
    rw [map_div₀, map_add, map_ofNat]
    norm_num
  have hdennorm :
      ‖Complex.Gamma ((s + (a : ℂ)) / 2)‖ = ‖Complex.Gamma w‖ := by
    have h := congrArg norm (Complex.Gamma_conj ((s + (a : ℂ)) / 2))
    rw [Complex.norm_conj] at h
    rw [hwconj, h]
  have hquotnorm :
      ‖Complex.Gamma X / Complex.Gamma ((s + (a : ℂ)) / 2)‖ =
        ‖Complex.Gamma X / Complex.Gamma w‖ := by
    simp only [norm_div, hdennorm]
  have hprod := FixedStripGammaRatio_norm_prod_range_eleven_add_le w s.im hwlower hwupper hwim
  have hresidual :
      ‖Complex.betaIntegral X d / Complex.Gamma d‖ ≤ 12 * K := by
    rw [div_eq_mul_inv, norm_mul]
    exact mul_le_mul (FixedStripGammaRatio_norm_betaIntegral_fixed_re_le hX hdlo)
      (hK d hdlo hdhi) (norm_nonneg _) (by norm_num)
  rw [show (1 - s + (a : ℂ)) / 2 = X by rfl, hquotnorm, hidentity, norm_mul]
  calc
    _ ≤ ((6 : ℝ) ^ 11 * (|s.im| + 2) ^ 11) * (12 * K) :=
      mul_le_mul hprod hresidual (norm_nonneg _)
        (mul_nonneg (by positivity) (by positivity))
    _ = (12 * K * 6 ^ 11) * (|s.im| + 2) ^ 11 := by ring

private lemma FixedStripGammaRatio_norm_GammaR_div_GammaR_le_Gamma_div_Gamma
    (a : ℝ) (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    ‖Complex.Gammaℝ (1 - s + (a : ℂ)) /
        Complex.Gammaℝ (s + (a : ℂ))‖ ≤
      ‖Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
        Complex.Gamma ((s + (a : ℂ)) / 2)‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  have hfactor :
      ((Real.pi : ℂ) ^ (-(1 - s + (a : ℂ)) / 2) *
          Complex.Gamma ((1 - s + (a : ℂ)) / 2)) /
        ((Real.pi : ℂ) ^ (-(s + (a : ℂ)) / 2) *
          Complex.Gamma ((s + (a : ℂ)) / 2)) =
      (((Real.pi : ℂ) ^ (-(1 - s + (a : ℂ)) / 2)) /
          ((Real.pi : ℂ) ^ (-(s + (a : ℂ)) / 2))) *
        (Complex.Gamma ((1 - s + (a : ℂ)) / 2) /
          Complex.Gamma ((s + (a : ℂ)) / 2)) := by
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [hfactor, norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_sub Real.pi_pos]
  have hexp :
      (-(1 - s + (a : ℂ)) / 2).re - (-(s + (a : ℂ)) / 2).re =
        s.re - 1 / 2 := by
    norm_num
    ring
  rw [hexp]
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_trans (by norm_num) Real.two_le_pi) (by linarith)

private lemma FixedStripGammaRatio_even_inv_for_gammaFactor
    {q : ℕ} {chi : DirichletCharacter ℂ q} (hchi : chi.Even) :
    (chi⁻¹).Even := by
  simp only [DirichletCharacter.Even] at hchi ⊢
  rw [MulChar.inv_apply_eq_inv', hchi, inv_one]

private lemma FixedStripGammaRatio_odd_inv_for_gammaFactor
    {q : ℕ} {chi : DirichletCharacter ℂ q} (hchi : chi.Odd) :
    (chi⁻¹).Odd := by
  simp only [DirichletCharacter.Odd] at hchi ⊢
  rw [MulChar.inv_apply_eq_inv', hchi]
  norm_num

theorem exists_norm_gammaFactor_ratio_fixedStrip_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (s : ℂ),
        -(10 : ℝ) ≤ s.re →
        s.re ≤ (1 / 2 : ℝ) →
        ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s‖ ≤
          C * (|s.im| + 2) ^ 11 := by
  obtain ⟨K, hKpos, hK⟩ := FixedStripGammaRatio_exists_norm_one_div_Gamma_Icc_le
  let C : ℝ := 12 * K * 6 ^ 11
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q _ chi s hslo hshi
  have hbound (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
      ‖Complex.Gammaℝ (1 - s + (a : ℂ)) /
          Complex.Gammaℝ (s + (a : ℂ))‖ ≤
        C * (|s.im| + 2) ^ 11 := by
    exact (FixedStripGammaRatio_norm_GammaR_div_GammaR_le_Gamma_div_Gamma a s hshi).trans
      (FixedStripGammaRatio_norm_Gamma_div_Gamma_fixedStrip_le K hK a s ha0 ha1 hslo hshi)
  rcases chi.even_or_odd with heven | hodd
  · rw [(FixedStripGammaRatio_even_inv_for_gammaFactor heven).gammaFactor_def, heven.gammaFactor_def]
    simpa using hbound 0 (by norm_num) (by norm_num)
  · rw [(FixedStripGammaRatio_odd_inv_for_gammaFactor hodd).gammaFactor_def, hodd.gammaFactor_def]
    convert hbound 1 (by norm_num) (by norm_num) using 1
    all_goals norm_num

end BoundedGaps.Maynard

end

/-! ## Primitive Gauss sums on `ZMod`

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveGaussSum`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem PrimitiveGaussSum_sum_star_mul_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, star (ZMod.dft f k) * ZMod.dft f k) =
      (q : ℂ) * ∑ j : ZMod q, star (f j) * f j := by
  classical
  have hstar (x : ZMod q) :
      star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    simpa only [Complex.star_def] using
      (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul]
  simp_rw [hstar]
  simp only [neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hsummand (i k : ZMod q) :
      star (f j) * ZMod.stdAddChar (j * k) *
          (ZMod.stdAddChar (-(i * k)) * f i) =
        (star (f j) * f i) * ZMod.stdAddChar (k * (j - i)) := by
    calc
      _ = (star (f j) * f i) *
          (ZMod.stdAddChar (j * k) * ZMod.stdAddChar (-(i * k))) := by ring
      _ = (star (f j) * f i) *
          ZMod.stdAddChar (j * k + -(i * k)) := by rw [map_add_eq_mul]
      _ = _ := by
        rw [show j * k + -(i * k) = k * (j - i) by ring]
  simp_rw [hsummand, ← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift (ψ := ZMod.stdAddChar) _
    (ZMod.isPrimitive_stdAddChar q)]
  simp only [sub_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero,
    mul_ite, mul_zero]
  simp [eq_comm]
  ring

theorem sum_norm_sq_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖ZMod.dft f k‖ ^ 2) =
      (q : ℝ) * ∑ j : ZMod q, ‖f j‖ ^ 2 := by
  have h := PrimitiveGaussSum_sum_star_mul_dft f
  rw [Complex.star_def] at h
  simp_rw [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

theorem sum_norm_sq_dirichletCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ j : ZMod q, ‖χ j‖ ^ 2) = (Nat.totient q : ℝ) := by
  classical
  calc
    (∑ j : ZMod q, ‖χ j‖ ^ 2) =
        ∑ j : ZMod q, if IsUnit j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : IsUnit j
      · have hnorm : ‖χ j‖ = 1 := by
          rw [← hj.unit_spec]
          exact χ.unit_norm_eq_one hj.unit
        simp [hj, hnorm]
      · simp [hj, χ.map_nonunit hj]
    _ = (((Finset.univ : Finset (ZMod q)).filter IsUnit).card : ℝ) := by
      simp
    _ = ((Fintype.card (ZMod q)ˣ : ℕ) : ℝ) := by
      congr 1
      calc
        ((Finset.univ : Finset (ZMod q)).filter IsUnit).card =
            (Finset.univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q),
              Units.val_injective⟩).card := by
          congr 1
          ext j
          simp [IsUnit]
        _ = Fintype.card (ZMod q)ˣ := by simp
    _ = (Nat.totient q : ℝ) := by rw [ZMod.card_units_eq_totient]

theorem norm_gaussSum_stdAddChar_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  have hmassNeg :
      (∑ k : ZMod q, ‖χ⁻¹ (-k)‖ ^ 2) = (Nat.totient q : ℝ) := by
    calc
      _ = ∑ k : ZMod q, ‖χ⁻¹ k‖ ^ 2 :=
        Equiv.sum_comp (Equiv.neg (ZMod q)) (fun k ↦ ‖χ⁻¹ k‖ ^ 2)
      _ = (Nat.totient q : ℝ) := sum_norm_sq_dirichletCharacter χ⁻¹
  have hparseval := sum_norm_sq_dft (f := fun j ↦ χ j)
  simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum, norm_mul, mul_pow] at hparseval
  rw [← Finset.sum_mul, hmassNeg,
    sum_norm_sq_dirichletCharacter χ] at hparseval
  have htotient : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne q))))
  have hsquare : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
    apply mul_left_cancel₀ htotient
    calc
      (Nat.totient q : ℝ) * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 =
          (q : ℝ) * Nat.totient q := hparseval
      _ = (Nat.totient q : ℝ) * q := by ring
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q),
    norm_nonneg (gaussSum χ ZMod.stdAddChar), Real.sqrt_nonneg (q : ℝ)]

theorem primitive_fourier_expansion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) =
      χ n * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hfourier := hχinv.fourierTransform_eq_inv_mul_gaussSum (-n)
  simpa only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg, inv_inv,
    mul_comm] using hfourier

theorem primitive_fourier_expansion_div {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) /
      gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hnorm := norm_gaussSum_stdAddChar_of_isPrimitive χ⁻¹ hχinv
  have hgauss : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    nlinarith [Real.sqrt_pos.2 hqpos]
  rw [primitive_fourier_expansion χ hχ n,
    mul_div_cancel_right₀ _ hgauss]

end BoundedGaps.Maynard

end

/-! ## Primitive Dirichlet functional equation

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveFunctionalEquation`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private lemma PrimitiveFunctionalEquation_gammaFactor_inv_one_sub_ne_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re ≤ (1 / 2 : ℝ)) :
    DirichletCharacter.gammaFactor chi⁻¹ (1 - s) ≠ 0 := by
  rcases chi⁻¹.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  · rw [hodd.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

theorem norm_rootNumber_of_isPrimitive
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive) :
    ‖DirichletCharacter.rootNumber chi‖ = 1 := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  rw [DirichletCharacter.rootNumber, norm_div, norm_div,
    norm_gaussSum_stdAddChar_of_isPrimitive chi hchi, norm_pow,
    Complex.norm_I, one_pow, div_one,
    Complex.norm_natCast_cpow_of_pos hqpos]
  simp [Real.sqrt_eq_rpow, hq0]

theorem LFunction_eq_functionalEquation_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    DirichletCharacter.LFunction chi s =
      (q : ℂ) ^ ((1 / 2 : ℂ) - s) *
        DirichletCharacter.rootNumber chi *
        DirichletCharacter.LFunction chi⁻¹ (1 - s) *
        (DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s) := by
  have hqne : q ≠ 1 := Nat.ne_of_gt hq
  have hcompleted :
      DirichletCharacter.completedLFunction chi s =
        (q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          DirichletCharacter.rootNumber chi *
          DirichletCharacter.completedLFunction chi⁻¹ (1 - s) := by
    convert hchi.completedLFunction_one_sub (1 - s) using 1 <;> ring_nf
  have hgamma := PrimitiveFunctionalEquation_gammaFactor_inv_one_sub_ne_zero chi hs
  have hreflected :
      DirichletCharacter.completedLFunction chi⁻¹ (1 - s) =
        DirichletCharacter.LFunction chi⁻¹ (1 - s) *
          DirichletCharacter.gammaFactor chi⁻¹ (1 - s) := by
    symm
    exact (eq_div_iff hgamma).mp
      (DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹
        (1 - s) (.inr hqne))
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi s (.inr hqne),
    hcompleted, hreflected]
  ring

theorem norm_LFunction_eq_functionalEquation_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    ‖DirichletCharacter.LFunction chi s‖ =
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
        ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
        ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s‖ := by
  rw [LFunction_eq_functionalEquation_of_isPrimitive hq chi hchi s hs,
    norm_mul, norm_mul, norm_mul, norm_rootNumber_of_isPrimitive chi hchi,
    Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hq)]
  norm_num

end BoundedGaps.Maynard

end

/-! ## Abel continuation for nonprincipal Dirichlet L-functions

Source module `BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionAbelContinuation`. -/

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set

open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private noncomputable def DirichletLFunctionAbelContinuation_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun u ↦ ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y

private lemma DirichletLFunctionAbelContinuation_measurable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) :
    Measurable (DirichletLFunctionAbelContinuation_characterPrefixTail chi) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact
    (measurable_of_countable
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q))).comp
      Nat.measurable_floor

private lemma DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (y : ℝ) :
    ‖DirichletLFunctionAbelContinuation_characterPrefixTail chi y‖ ≤ C := by
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · rw [DirichletLFunctionAbelContinuation_characterPrefixTail, indicator_of_mem hy]
    exact hprefix ⌊y⌋₊
  · rw [DirichletLFunctionAbelContinuation_characterPrefixTail, indicator_of_notMem hy, norm_zero]
    exact hC

private lemma DirichletLFunctionAbelContinuation_locallyIntegrable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    LocallyIntegrableOn (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (Ioi 0) := by
  have hnormScale : ‖((C : ℝ) : ℂ)‖ = C := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  refine ((locallyIntegrable_const ((C : ℝ) : ℂ)).locallyIntegrableOn
      (Ioi 0)).mono
      (DirichletLFunctionAbelContinuation_measurable_characterPrefixTail chi).aestronglyMeasurable ?_
  filter_upwards with y
  rw [hnormScale]
  exact DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le chi C hC hprefix y

private lemma DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    DirichletLFunctionAbelContinuation_characterPrefixTail chi =O[atTop] (fun y : ℝ ↦ y ^ (-(0 : ℝ))) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun y ↦ ?_⟩
  simpa using DirichletLFunctionAbelContinuation_norm_characterPrefixTail_le chi C hC hprefix y

private lemma DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_nhdsGT_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) (b : ℝ) :
    DirichletLFunctionAbelContinuation_characterPrefixTail chi =O[𝓝[>] 0] (fun y : ℝ ↦ y ^ (-b)) := by
  have hlt : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hlt] with y hy
  simp [DirichletLFunctionAbelContinuation_characterPrefixTail, not_lt.mpr hy.le]

private lemma DirichletLFunctionAbelContinuation_differentiableAt_characterPrefixMellin_neg
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun w ↦ mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) s := by
  have hm : DifferentiableAt ℂ (mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (DirichletLFunctionAbelContinuation_locallyIntegrable_characterPrefixTail chi C hC hprefix)
      (DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_atTop chi C hC hprefix) ?_
      (DirichletLFunctionAbelContinuation_characterPrefixTail_isBigO_nhdsGT_zero chi ((-s).re - 1)) ?_
    · simpa using (neg_lt_zero.mpr hs)
    · linarith
  exact hm.comp s differentiableAt_id.neg

private lemma DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) =
      ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  simp only [smul_eq_mul]
  calc
    (∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (-s - 1) * DirichletLFunctionAbelContinuation_characterPrefixTail chi y) =
        ∫ y : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun u ↦ (u : ℂ) ^ (-s - 1) *
            ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      by_cases hy : y ∈ Ioi (1 : ℝ)
      · simp [DirichletLFunctionAbelContinuation_characterPrefixTail, hy]
      · simp [DirichletLFunctionAbelContinuation_characterPrefixTail, hy]
    _ = ∫ y : ℝ in Ioi 0 ∩ Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ y : ℝ in Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ y : ℝ in Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma DirichletLFunctionAbelContinuation_characterPartialSums_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ)) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun n ↦ ?_⟩
  simpa using hprefix n

private lemma DirichletLFunctionAbelContinuation_LFunction_eq_characterPrefixMellin_of_one_lt_re
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) := by
  calc
    DirichletCharacter.LFunction chi s = LSeries (chi ·) s :=
      DirichletCharacter.LFunction_eq_LSeries chi hs
    _ = s * ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) :=
      LSeries_eq_mul_integral (chi ·) (r := 0) le_rfl (zero_lt_one.trans hs)
        (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
        (DirichletLFunctionAbelContinuation_characterPartialSums_isBigO_atTop chi C hprefix)
    _ = s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) := by
      rw [DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral]

theorem LFunction_eq_abelIntegral_of_prefixBound
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  have hC : 0 ≤ C := by
    simpa using hprefix 0
  let U : Set ℂ := {w | 0 < w.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUPre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLeft :
      AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi) U :=
    (DirichletCharacter.differentiable_LFunction hchi).differentiableOn.analyticOnNhd hUOpen
  have hRight : AnalyticOnNhd ℂ
      (fun w ↦ w * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) hUOpen
    exact (differentiableAt_id.mul
      (DirichletLFunctionAbelContinuation_differentiableAt_characterPrefixMellin_neg chi C hC hprefix hw)).differentiableWithinAt
  have hEq : EqOn (DirichletCharacter.LFunction chi)
      (fun w ↦ w * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-w)) U := by
    refine hLeft.eqOn_of_preconnected_of_eventuallyEq hRight hUPre
      (show (2 : ℂ) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro w hw
    exact DirichletLFunctionAbelContinuation_LFunction_eq_characterPrefixMellin_of_one_lt_re chi C hprefix hw
  rw [hEq hs]
  change s * mellin (DirichletLFunctionAbelContinuation_characterPrefixTail chi) (-s) = _
  rw [DirichletLFunctionAbelContinuation_characterPrefixMellin_neg_eq_integral]

end BoundedGaps.Maynard

end

/-! ## Standard additive characters on translated integer intervals

Source module `BoundedGaps.BombieriVinogradov.Analytic.StandardAddCharInterval`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem StandardAddCharInterval_sum_Ioc_int_eq_sum_range_add_succ
    {A : Type*} [AddCommMonoid A] (f : ℤ → A) (M : ℤ) (N : ℕ) :
    (∑ m ∈ Finset.Ioc M (M + (N : ℤ)), f m) =
      ∑ n ∈ Finset.range N, f (M + (n + 1 : ℕ)) := by
  rw [Int.Ioc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  congr 1
  · simp
  · funext n
    congr 1
    push_cast
    ring

private theorem StandardAddCharInterval_stdAddChar_mul_int_add_succ {q : ℕ} [NeZero q]
    (a : ZMod q) (M : ℤ) (n : ℕ) :
    ZMod.stdAddChar (a * ((M + ((n + 1 : ℕ) : ℤ) : ℤ) : ZMod q)) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ZMod.stdAddChar a ^ n := by
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  simp only [nsmul_eq_mul]
  ring

private theorem StandardAddCharInterval_stdAddChar_ne_one_of_ne_zero
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0) :
    ZMod.stdAddChar a ≠ 1 := by
  intro h
  apply ha
  apply ZMod.injective_stdAddChar
  simpa only [AddChar.map_zero_eq_one] using h

private theorem StandardAddCharInterval_norm_stdAddChar_sub_one_eq_two_mul_abs_sin
    {q : ℕ} [NeZero q] (a : ZMod q) :
    ‖ZMod.stdAddChar a - 1‖ =
      2 * |Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))| := by
  rw [← ZMod.natCast_zmod_val a]
  rw [show (a.val : ZMod q) = ((a.val : ℤ) : ZMod q) by simp,
    ZMod.stdAddChar_coe]
  simp only [Int.cast_natCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) / (q : ℂ) =
      Complex.I * ((2 * Real.pi * (a.val : ℝ) / (q : ℝ) : ℝ) : ℂ) by
        push_cast
        ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [show (2 * Real.pi * (a.val : ℝ) / (q : ℝ)) / 2 =
    Real.pi * (a.val : ℝ) / (q : ℝ) by ring]
  rw [Real.norm_eq_abs, abs_mul]
  norm_num

theorem sum_stdAddChar_Ioc_eq_geometric
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ((1 - ZMod.stdAddChar (a * (N : ZMod q))) /
          (1 - ZMod.stdAddChar a)) := by
  rw [StandardAddCharInterval_sum_Ioc_int_eq_sum_range_add_succ]
  simp_rw [StandardAddCharInterval_stdAddChar_mul_int_add_succ]
  rw [← Finset.mul_sum, geom_sum_eq (StandardAddCharInterval_stdAddChar_ne_one_of_ne_zero ha)]
  have hpow : ZMod.stdAddChar (a * (N : ZMod q)) =
      ZMod.stdAddChar a ^ N := by
    rw [show a * (N : ZMod q) = N • a by ring,
      AddChar.map_nsmul_eq_pow]
  rw [hpow]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv,
    show ZMod.stdAddChar a - 1 = -(1 - ZMod.stdAddChar a) by ring,
    inv_neg]
  ring

theorem norm_sum_stdAddChar_Ioc_le_inv_sin
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))‖ ≤
      (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have havalpos : (0 : ℝ) < a.val := by
    exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha)
  have hanglepos : 0 < Real.pi * (a.val : ℝ) / (q : ℝ) :=
    div_pos (mul_pos Real.pi_pos havalpos) hqpos
  have hanglelt : Real.pi * (a.val : ℝ) / (q : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hqpos]
    have havallt : (a.val : ℝ) < q := by exact_mod_cast a.val_lt
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hanglepos hanglelt
  have hnum : ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar (a * (N : ZMod q))‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [AddChar.norm_apply]; norm_num
  have hdenom : ‖1 - ZMod.stdAddChar a‖ =
      2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) := by
    rw [show (1 : ℂ) - ZMod.stdAddChar a =
      -(ZMod.stdAddChar a - 1) by ring, norm_neg,
      StandardAddCharInterval_norm_stdAddChar_sub_one_eq_two_mul_abs_sin,
      abs_of_pos hsin]
  rw [sum_stdAddChar_Ioc_eq_geometric ha, norm_mul,
    AddChar.norm_apply, one_mul, norm_div, hdenom]
  calc
    ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ /
        (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) ≤
        2 / (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
      field_simp

end BoundedGaps.Maynard

end

/-! ## Primitive character sums on translated integer intervals

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveCharacterInterval`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem PrimitiveCharacterInterval_sum_zmod_erase_zero_eq_sum_Ico_val
    {q : ℕ} [NeZero q]
    {A : Type*} [AddCommMonoid A] (f : ZMod q → A) :
    (∑ a ∈ Finset.univ.erase (0 : ZMod q), f a) =
      ∑ a ∈ Finset.Ico 1 q, f (a : ZMod q) := by
  classical
  apply Finset.sum_nbij (fun a : ZMod q => a.val)
  · intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
    exact Finset.mem_Ico.mpr ⟨ZMod.val_pos.mpr ha0, a.val_lt⟩
  · exact (ZMod.val_injective q).injOn
  · intro b hb
    have hbmem := Finset.mem_Ico.mp hb
    refine ⟨(b : ZMod q), ?_, ?_⟩
    · apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      apply (ZMod.val_ne_zero _).mp
      rw [ZMod.val_cast_of_lt hbmem.2]
      exact Nat.ne_of_gt hbmem.1
    · exact ZMod.val_cast_of_lt hbmem.2
  · intro a ha
    rw [ZMod.natCast_zmod_val]

theorem sum_dirichletCharacter_Ioc_eq_fourier
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a : ZMod q, chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hpoint (n : ℤ) :
      chi (n : ZMod q) =
        (∑ a : ZMod q,
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
    exact primitive_fourier_expansion_div chi hchi (n : ZMod q)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ((∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
            gaussSum chi⁻¹ ZMod.stdAddChar) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact hpoint n
    _ = (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ∑ a : ZMod q,
            chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      rw [Finset.sum_div]
    _ = (∑ a : ZMod q, ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          chi⁻¹ a * ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum]

theorem sum_dirichletCharacter_Ioc_eq_fourier_erase_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar (a * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  have hzero : chi⁻¹ (0 : ZMod q) = 0 :=
    DirichletCharacter.map_zero' chi⁻¹ (Nat.ne_of_gt hq)
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a : ZMod q, chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier chi hchi M N
    _ = (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod q))]
      simp [hzero]

theorem sum_dirichletCharacter_Ioc_eq_nat_fourier
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
      (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
        gaussSum chi⁻¹ ZMod.stdAddChar := by
  classical
  calc
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)) =
        (∑ a ∈ Finset.univ.erase (0 : ZMod q), chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar :=
      sum_dirichletCharacter_Ioc_eq_fourier_erase_zero hq chi hchi M N
    _ = (∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))) /
          gaussSum chi⁻¹ ZMod.stdAddChar := by
      congr 1
      exact PrimitiveCharacterInterval_sum_zmod_erase_zero_eq_sum_Ico_val
        (f := fun a : ZMod q => chi⁻¹ a *
          ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
            ZMod.stdAddChar (a * (n : ZMod q)))

theorem norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
      (∑ a ∈ Finset.Ico 1 q,
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
        Real.sqrt q := by
  classical
  have hchiInv : chi⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hchi
  have hgaussNorm : ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ = Real.sqrt q :=
    norm_gaussSum_stdAddChar_of_isPrimitive chi⁻¹ hchiInv
  have hnumerator :
      ‖∑ a ∈ Finset.Ico 1 q, chi⁻¹ (a : ZMod q) *
        ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
          ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ ≤
        ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
    calc
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          ‖chi⁻¹ (a : ZMod q) *
            ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
              ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
        apply Finset.sum_le_sum
        intro a ha
        have haIco := Finset.mem_Ico.mp ha
        have ha0 : (a : ZMod q) ≠ 0 := by
          apply (ZMod.val_ne_zero (a : ZMod q)).mp
          rw [ZMod.val_cast_of_lt haIco.2]
          exact Nat.ne_of_gt haIco.1
        have hinterval := norm_sum_stdAddChar_Ioc_le_inv_sin
          (q := q) (a := (a : ZMod q)) ha0 M N
        rw [ZMod.val_cast_of_lt haIco.2] at hinterval
        calc
          ‖chi⁻¹ (a : ZMod q) *
              ∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ =
              ‖chi⁻¹ (a : ZMod q)‖ *
                ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
                  ZMod.stdAddChar ((a : ZMod q) * (n : ZMod q))‖ :=
            norm_mul _ _
          _ ≤ 1 * (Real.sin
                (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ :=
            mul_le_mul (DirichletCharacter.norm_le_one chi⁻¹ (a : ZMod q))
              hinterval (norm_nonneg _) zero_le_one
          _ = (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := one_mul _
  rw [sum_dirichletCharacter_Ioc_eq_nat_fourier hq chi hchi M N,
    norm_div, hgaussNorm]
  exact div_le_div_of_nonneg_right hnumerator (Real.sqrt_nonneg q)

end BoundedGaps.Maynard

end

/-! ## The sharp reciprocal-sine aggregate

Source module `BoundedGaps.BombieriVinogradov.Analytic.ReciprocalSineAggregate`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

open Finset

private theorem ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one (n : ℕ) :
    (harmonic n : ℝ) ≤ Real.log (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
      have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have hlog := Real.le_log_one_add_of_nonneg
        (show (0 : ℝ) ≤ 2 / (2 * (n : ℝ) + 1) by positivity)
      have hincrement :
          ((n : ℝ) + 1)⁻¹ ≤
            Real.log (2 * ((n : ℝ) + 1) + 1) -
              Real.log (2 * (n : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) hden.ne']
        convert hlog using 1 <;> field_simp <;> ring_nf
      linarith

private theorem ReciprocalSineAggregate_harmonic_cast_lt_log_two_mul_add_one {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) < Real.log (2 * (n : ℝ) + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
  have hbase := ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one n
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hlog := Real.lt_log_one_add_of_pos
    (show (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) by positivity)
  have hincrement :
      ((n : ℝ) + 1)⁻¹ <
        Real.log (2 * ((n : ℝ) + 1) + 1) -
          Real.log (2 * (n : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    convert hlog using 1 <;> field_simp <;> ring_nf
  linarith

private theorem ReciprocalSineAggregate_harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul
    {m : ℕ} (hm : 0 < m) :
    (harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹ <
      Real.log (((2 * m : ℕ) : ℝ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ]
  have hbase := ReciprocalSineAggregate_harmonic_cast_le_log_two_mul_add_one m
  have hden : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) < (2 * (m : ℝ) + 1)⁻¹ := by positivity
  have hlog := Real.lt_log_one_add_of_pos hx
  have hincrement :
      (2 * ((m : ℝ) + 1))⁻¹ <
        Real.log (2 * ((m : ℝ) + 1)) -
          Real.log (2 * (m : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    calc
      (2 * ((m : ℝ) + 1))⁻¹ <
          2 * (2 * (m : ℝ) + 1)⁻¹ /
            ((2 * (m : ℝ) + 1)⁻¹ + 2) := by
        field_simp
        linarith
      _ < Real.log (1 + (2 * (m : ℝ) + 1)⁻¹) := hlog
      _ = Real.log (2 * ((m : ℝ) + 1) / (2 * (m : ℝ) + 1)) := by
        congr 1
        field_simp
        ring
  linarith

private noncomputable def ReciprocalSineAggregate_reciprocalSineTerm (q a : ℕ) : ℝ :=
  (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹

private theorem ReciprocalSineAggregate_reciprocalSineTerm_le_div {q a : ℕ} (hq : 0 < q)
    (ha : 0 < a) (haq : 2 * a ≤ q) :
    ReciprocalSineAggregate_reciprocalSineTerm q a ≤ (q : ℝ) / (2 * (a : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hangle0 : 0 ≤ Real.pi * (a : ℝ) / (q : ℝ) := by positivity
  have hanglehalf : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hqR zero_lt_two]
    have haqR : (2 : ℝ) * (a : ℝ) ≤ q := by exact_mod_cast haq
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_le_sin hangle0 hanglehalf
  have hbase : 0 < 2 / Real.pi *
      (Real.pi * (a : ℝ) / (q : ℝ)) := by positivity
  have hinv := inv_anti₀ hbase hjordan
  calc
    ReciprocalSineAggregate_reciprocalSineTerm q a =
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := rfl
    _ ≤ (2 / Real.pi * (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := hinv
    _ = (q : ℝ) / (2 * (a : ℝ)) := by field_simp

private theorem ReciprocalSineAggregate_reciprocalSineTerm_sub {q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    ReciprocalSineAggregate_reciprocalSineTerm q (q - a) = ReciprocalSineAggregate_reciprocalSineTerm q a := by
  rw [ReciprocalSineAggregate_reciprocalSineTerm, ReciprocalSineAggregate_reciprocalSineTerm, Nat.cast_sub ha]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [show Real.pi * ((q : ℝ) - (a : ℝ)) / (q : ℝ) =
      Real.pi - Real.pi * (a : ℝ) / (q : ℝ) by field_simp,
    Real.sin_pi_sub]

private theorem ReciprocalSineAggregate_reciprocalSineTerm_two_mul_self {m : ℕ} (hm : 0 < m) :
    ReciprocalSineAggregate_reciprocalSineTerm (2 * m) m = 1 := by
  rw [ReciprocalSineAggregate_reciprocalSineTerm]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [show Real.pi * (m : ℝ) / ((2 * m : ℕ) : ℝ) = Real.pi / 2 by
      push_cast
      field_simp,
    Real.sin_pi_div_two, inv_one]

private theorem ReciprocalSineAggregate_sum_Ico_inv_eq_harmonic (n : ℕ) :
    (∑ a ∈ Finset.Ico 1 (n + 1), ((a : ℝ))⁻¹) = (harmonic n : ℝ) := by
  rw [Finset.Ico_add_one_right_eq_Icc]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
    {q m : ℕ} (hq : 0 < q) (hmq : 2 * m ≤ q) :
    (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm q a) ≤
      (q : ℝ) / 2 * (harmonic m : ℝ) := by
  calc
    (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm q a) ≤
        ∑ a ∈ Finset.Ico 1 (m + 1), (q : ℝ) / (2 * (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact ReciprocalSineAggregate_reciprocalSineTerm_le_div hq (Finset.mem_Ico.mp ha).1
        ((Nat.mul_le_mul_left 2
          (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2)).trans hmq)
    _ = (q : ℝ) / 2 *
        ∑ a ∈ Finset.Ico 1 (m + 1), ((a : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      field_simp
    _ = (q : ℝ) / 2 * (harmonic m : ℝ) := by
      rw [ReciprocalSineAggregate_sum_Ico_inv_eq_harmonic]

private theorem ReciprocalSineAggregate_sum_reciprocalSine_odd_eq_two_mul (m : ℕ) :
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
      2 * ∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
  have hq : 0 < 2 * m + 1 := by omega
  have hreflect := Finset.sum_Ico_reflect
    (ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1)) 1
    (m := m + 1) (n := 2 * m + 1) (by omega)
  have hb1 : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
  have hb2 : 2 * m + 1 + 1 - 1 = 2 * m + 1 := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
        ∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply ReciprocalSineAggregate_reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2).trans (by omega)
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) =
        (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
            ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by
      rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1))
        (by omega) (by omega)]
    _ = 2 * ∑ a ∈ Finset.Ico 1 (m + 1),
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a := by rw [hupper]; ring

private theorem ReciprocalSineAggregate_sum_reciprocalSine_even_eq_two_mul_add_one
    {m : ℕ} (hm : 0 < m) :
    (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
      2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 := by
  have hq : 0 < 2 * m := Nat.mul_pos two_pos hm
  have hreflect := Finset.sum_Ico_reflect
    (ReciprocalSineAggregate_reciprocalSineTerm (2 * m)) 1
    (m := m) (n := 2 * m) (by omega)
  have hb1 : 2 * m + 1 - m = m + 1 := by omega
  have hb2 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        ∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply ReciprocalSineAggregate_reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt (Finset.mem_Ico.mp ha).2).trans (by omega)
  have hrest :
      (∑ a ∈ Finset.Ico m (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        ReciprocalSineAggregate_reciprocalSineTerm (2 * m) m +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
    calc
      _ = (∑ a ∈ Finset.Ico m (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
        rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m))
          (by omega) (by omega)]
      _ = _ := by simp
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) =
        (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico m (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a := by
      rw [Finset.sum_Ico_consecutive (ReciprocalSineAggregate_reciprocalSineTerm (2 * m))
        (by omega) (by omega)]
    _ = 2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 := by
      rw [hrest, hupper, ReciprocalSineAggregate_reciprocalSineTerm_two_mul_self hm]
      ring

theorem sum_reciprocalSine_Ico_lt_mul_log {q : ℕ} (hq : 1 < q) :
    (∑ a ∈ Finset.Ico 1 q,
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) <
      (q : ℝ) * Real.log (q : ℝ) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' q
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m), ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) < _
    rw [ReciprocalSineAggregate_sum_reciprocalSine_even_eq_two_mul_add_one hm]
    have hhalf := ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m) (m := m - 1) (by omega) (by omega)
    have htop : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [htop] at hhalf
    have hlog := ReciprocalSineAggregate_harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 m, ReciprocalSineAggregate_reciprocalSineTerm (2 * m) a) + 1 ≤
          2 * (((2 * m : ℕ) : ℝ) / 2 * (harmonic (m - 1) : ℝ)) + 1 :=
        by
          simpa only [add_comm] using add_le_add_right
            (mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 2 by norm_num)) 1
      _ = ((2 * m : ℕ) : ℝ) *
          ((harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹) := by
        have htwoM : (((2 * m : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
      _ < ((2 * m : ℕ) : ℝ) * Real.log (((2 * m : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_left hlog (by positivity)
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m + 1),
      ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) < _
    rw [ReciprocalSineAggregate_sum_reciprocalSine_odd_eq_two_mul]
    have hhalf := ReciprocalSineAggregate_sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m + 1) (m := m) (by omega) (by omega)
    have hlog := ReciprocalSineAggregate_harmonic_cast_lt_log_two_mul_add_one hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 (m + 1), ReciprocalSineAggregate_reciprocalSineTerm (2 * m + 1) a) ≤
          2 * (((2 * m + 1 : ℕ) : ℝ) / 2 * (harmonic m : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ = ((2 * m + 1 : ℕ) : ℝ) * (harmonic m : ℝ) := by ring
      _ < ((2 * m + 1 : ℕ) : ℝ) * Real.log (((2 * m + 1 : ℕ) : ℝ)) := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlog

end BoundedGaps.Maynard

end

/-! ## Primitive Polya--Vinogradov interval bound

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitivePolyaVinogradov`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.zero_lt_of_lt hq
  have hsqrt : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqpos
  calc
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)), chi (n : ZMod q)‖ ≤
        (∑ a ∈ Finset.Ico 1 q,
          (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) /
          Real.sqrt q :=
      norm_sum_dirichletCharacter_Ioc_le_reciprocalSineSum hq chi hchi M N
    _ < ((q : ℝ) * Real.log (q : ℝ)) / Real.sqrt q :=
      div_lt_div_of_pos_right (sum_reciprocalSine_Ico_lt_mul_log hq) hsqrt
    _ = Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      apply (div_eq_iff hsqrt.ne').2
      calc
        (q : ℝ) * Real.log (q : ℝ) =
            (Real.sqrt (q : ℝ)) ^ 2 * Real.log (q : ℝ) := by
          rw [Real.sq_sqrt hqpos.le]
        _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            Real.sqrt (q : ℝ) := by ring

end BoundedGaps.Maynard

end

/-! ## Vaughan's second-term finite reduction

Source module `BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermReduction`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable def dirichletCharacterIntervalSum
    (a b q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ h ∈ Finset.Icc a b, χ h

end BoundedGaps.Maynard

end

/-! ## Polya--Vinogradov bound for Vaughan's second term

Source module `BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermPolyaVinogradov`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
    {q : ℕ} (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (a b : ℕ) :
    ‖dirichletCharacterIntervalSum a b q chi‖ <
      Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  letI : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
  have hboundPos :
      0 < Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
    exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hq))
      (Real.log_pos (by exact_mod_cast hq))
  by_cases hab : a ≤ b
  · have hendpoint :
        (a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ) = (b : ℤ) := by
      rw [Nat.cast_add, Nat.cast_sub hab]
      push_cast
      ring
    have hfinset :
        (Finset.Icc a b).map (Nat.castEmbedding : ℕ ↪ ℤ) =
          Finset.Ioc ((a : ℤ) - 1) (b : ℤ) := by
      ext n
      simp only [Finset.mem_map, Nat.castEmbedding_apply, Finset.mem_Icc,
        Finset.mem_Ioc]
      constructor
      · rintro ⟨m, hm, rfl⟩
        constructor <;> omega
      · intro hn
        have hnnonneg : 0 ≤ n := by
          have : (a : ℤ) ≤ n := by omega
          exact (Int.natCast_nonneg a).trans this
        lift n to ℕ using hnnonneg with m
        refine ⟨m, ?_, rfl⟩
        constructor <;> omega
    rw [dirichletCharacterIntervalSum]
    calc
      ‖∑ n ∈ Finset.Icc a b, chi n‖ =
          ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1) (b : ℤ),
            chi (n : ZMod q)‖ := by
        rw [← hfinset, Finset.sum_map]
        simp
      _ = ‖∑ n ∈ Finset.Ioc ((a : ℤ) - 1)
            ((a : ℤ) - 1 + (((b - a) + 1 : ℕ) : ℤ)),
            chi (n : ZMod q)‖ := by rw [hendpoint]
      _ < Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        norm_sum_dirichletCharacter_Ioc_lt_sqrt_mul_log hq chi hchi
          ((a : ℤ) - 1) ((b - a) + 1)
  · rw [dirichletCharacterIntervalSum, Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, norm_zero]
    exact hboundPos

end BoundedGaps.Maynard

end

/-! ## Primitive Dirichlet L-functions in the central strip

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionCentralStrip`. -/

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set

open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private lemma PrimitiveLFunctionCentralStrip_polyaVinogradovScale_pos {q : ℕ} (hq : 1 < q) :
    0 < Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  exact mul_pos
    (Real.sqrt_pos.2 (by exact_mod_cast Nat.zero_lt_of_lt hq))
    (Real.log_pos (by exact_mod_cast hq))

theorem character_ne_one_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive) : chi ≠ 1 := by
  intro heq
  have hc : chi.conductor = 1 :=
    DirichletCharacter.eq_one_iff_conductor_eq_one.mp heq
  have hp : chi.conductor = q := hchi
  omega

theorem LFunction_eq_abelIntegral_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)) := by
  simpa [dirichletCharacterIntervalSum] using
    LFunction_eq_abelIntegral_of_prefixBound chi
      (character_ne_one_of_isPrimitive hq chi hchi)
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ))
      (fun n ↦ by
        simpa [dirichletCharacterIntervalSum] using
          (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
            hq chi hchi 1 n).le)
      s hs

private lemma PrimitiveLFunctionCentralStrip_norm_characterAbelIntegral_le
    {q : ℕ} (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {s : ℂ} (hs : 0 < s.re) :
    ‖∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / s.re := by
  have hPower : IntegrableOn
      (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hScale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    (PrimitiveLFunctionCentralStrip_polyaVinogradovScale_pos hq).le
  have hDom : IntegrableOn
      (fun y : ℝ ↦
        (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
          y ^ (-(s.re + 1))) (Ioi 1) :=
    hPower.const_mul _
  have hActualMeasurable : AEStronglyMeasurable
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))) (volume.restrict (Ioi 1)) := by
    have hPrefix : Measurable
        (fun y : ℝ ↦ dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi) :=
      (measurable_of_countable
        (fun n : ℕ ↦ dirichletCharacterIntervalSum 1 n q chi)).comp
        Nat.measurable_floor
    have hCpow : ContinuousOn
        (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1))) (Ioi 1) :=
      continuousOn_of_forall_continuousAt fun y hy ↦
        continuousAt_ofReal_cpow_const y (-(s + 1))
          (Or.inr (zero_lt_one.trans hy).ne')
    exact hPrefix.aestronglyMeasurable.mul
      (hCpow.aestronglyMeasurable measurableSet_Ioi)
  have hBound : ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi 1),
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
          y ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hy)]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
        hq chi hchi 1 ⌊y⌋₊).le
      (Real.rpow_nonneg (zero_lt_one.trans hy).le _)
  have hActual : IntegrableOn
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    hDom.mono' hActualMeasurable hBound
  calc
    ‖∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        ∫ y in Ioi (1 : ℝ),
          ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
            (y : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi (1 : ℝ),
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            y ^ (-(s.re + 1)) :=
      setIntegral_mono_ae_restrict hActual.norm hDom hBound
    _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
        ∫ y in Ioi (1 : ℝ), y ^ (-(s.re + 1)) := by
      rw [integral_const_mul]
    _ = (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      field_simp [hs.ne']
      ring

theorem norm_LFunction_centralStrip_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    {sigma t : ℝ} (hsigma_lower : (1 / 2 : ℝ) ≤ sigma)
    (hsigma_upper : sigma ≤ 2) :
    ‖DirichletCharacter.LFunction chi ((sigma : ℂ) + t * I)‖ ≤
      2 * (|t| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let s : ℂ := (sigma : ℂ) + t * I
  have hsigma_pos : 0 < sigma := by linarith
  have hsre : s.re = sigma := by simp [s]
  have hspos : 0 < s.re := hsre.symm ▸ hsigma_pos
  have hscale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    (PrimitiveLFunctionCentralStrip_polyaVinogradovScale_pos hq).le
  have hnormS : ‖s‖ ≤ |t| + 2 := by
    calc
      ‖s‖ ≤ ‖(sigma : ℂ)‖ + ‖(t : ℂ) * I‖ := by
        simpa only [s] using norm_add_le (sigma : ℂ) ((t : ℂ) * I)
      _ = |sigma| + |t| := by simp [Real.norm_eq_abs]
      _ = sigma + |t| := by rw [abs_of_nonneg hsigma_pos.le]
      _ ≤ |t| + 2 := by linarith
  have hinv : 1 / sigma ≤ 2 := by
    apply (div_le_iff₀ hsigma_pos).2
    linarith
  have hquot :
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma ≤
        2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by
    calc
      (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma =
          (1 / sigma) *
            (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by ring
      _ ≤ 2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hinv hscale
  have hIntegral := PrimitiveLFunctionCentralStrip_norm_characterAbelIntegral_le hq chi hchi hspos
  rw [hsre] at hIntegral
  change ‖DirichletCharacter.LFunction chi s‖ ≤ _
  calc
    ‖DirichletCharacter.LFunction chi s‖ =
        ‖s‖ *
          ‖∫ y in Ioi (1 : ℝ),
            dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
              (y : ℂ) ^ (-(s + 1))‖ := by
      rw [LFunction_eq_abelIntegral_of_isPrimitive hq chi hchi s hspos,
        norm_mul]
    _ ≤ ‖s‖ *
        ((Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma) :=
      mul_le_mul_of_nonneg_left hIntegral (norm_nonneg s)
    _ ≤ (|t| + 2) *
        ((Real.sqrt (q : ℝ) * Real.log (q : ℝ)) / sigma) :=
      mul_le_mul_of_nonneg_right hnormS
        (div_nonneg hscale hsigma_pos.le)
    _ ≤ (|t| + 2) *
        (2 * (Real.sqrt (q : ℝ) * Real.log (q : ℝ))) :=
      mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = 2 * (|t| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      ring

end BoundedGaps.Maynard

end

/-! ## Primitive Dirichlet L-functions on a fixed left strip

Source module `BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionFixedStrip`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

theorem norm_LFunction_farRight_le_three
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (z : ℂ)
    (hz : (2 : ℝ) ≤ z.re) :
    ‖DirichletCharacter.LFunction chi z‖ ≤ 3 := by
  have hz1 : 1 < z.re := one_lt_two.trans_le hz
  have hsummable : LSeriesSummable (chi ·) z :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re chi hz1
  rw [DirichletCharacter.LFunction_eq_LSeries chi hz1, LSeries]
  calc
    ‖∑' n : ℕ, LSeries.term (chi ·) z n‖ ≤
        ∑' n : ℕ, ‖LSeries.term (chi ·) z n‖ :=
      norm_tsum_le_tsum_norm hsummable.norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
      apply hsummable.norm.tsum_le_tsum
      · intro n
        rw [LSeries.norm_term_eq]
        split_ifs with hn
        · simp
        · have hn1 : (1 : ℝ) ≤ n := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
          have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ z.re := by
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le hn1 hz
          calc
            ‖chi n‖ / (n : ℝ) ^ z.re ≤ 1 / (n : ℝ) ^ z.re :=
              div_le_div_of_nonneg_right (chi.norm_le_one n)
                (Real.rpow_nonneg (Nat.cast_nonneg n) z.re)
            _ ≤ 1 / (n : ℝ) ^ 2 :=
              one_div_le_one_div_of_le (by positivity) hpow
      · exact Real.summable_one_div_nat_pow.mpr (by norm_num)
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
    _ ≤ 3 := by nlinarith [Real.pi_nonneg, Real.pi_le_four]

theorem exists_norm_LFunction_fixedStrip_le_const_mul_pow_twelve :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(10 : ℝ) ≤ s.re → s.re ≤ (1 / 2 : ℝ) →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              C * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_gammaFactor_ratio_fixedStrip_le
  refine ⟨3 * Cgamma, mul_pos (by norm_num) hCgamma, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hT2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hT1 : (1 : ℝ) ≤ |s.im| + 2 := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ |s.im| + 2 := zero_le_one.trans hT1
  have hchiInv : chi⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hchi
  have hgamma' := hgamma q chi s hslo hshi
  rw [norm_LFunction_eq_functionalEquation_of_isPrimitive hq chi hchi s hshi]
  by_cases hmid : -(1 : ℝ) ≤ s.re
  · have hreflected := norm_LFunction_centralStrip_le hq chi⁻¹ hchiInv
      (sigma := 1 - s.re) (t := -s.im) (by linarith) (by linarith)
    have hreflectArg :
        (((1 - s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * I) = 1 - s := by
      apply Complex.ext <;> simp
    rw [hreflectArg] at hreflected
    simp only [abs_neg] at hreflected
    have hqpow :
        (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have hsqrt : Real.sqrt (q : ℝ) ≤ q :=
      Real.sqrt_le_self_iff.mpr (Or.inr hq1)
    have hlog : Real.log (q : ℝ) ≤ q :=
      (Real.log_le_sub_one_of_pos hqpos).trans
        (sub_le_self _ zero_le_one)
    have hqpowFour : (q : ℝ) ^ 4 ≤ (q : ℝ) ^ 12 :=
      pow_le_pow_right₀ hq1 (by norm_num)
    calc
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
            ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
          ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
            DirichletCharacter.gammaFactor chi s‖ ≤
          (q : ℝ) ^ 2 *
              (2 * (|s.im| + 2) * Real.sqrt (q : ℝ) * Real.log (q : ℝ)) *
            (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ ≤ (q : ℝ) ^ 2 *
              (2 * (|s.im| + 2) * (q : ℝ) * (q : ℝ)) *
            (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ = (2 * Cgamma) * (q : ℝ) ^ 4 * (|s.im| + 2) ^ 12 := by
        ring
      _ ≤ (3 * Cgamma) * (q : ℝ) ^ 12 * (|s.im| + 2) ^ 12 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (by nlinarith) hqpowFour (pow_nonneg hq0 4)
            (by positivity))
          (pow_nonneg hT0 12)
      _ = (3 * Cgamma) * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
        rw [mul_pow]
        ring
  · have hreflected := norm_LFunction_farRight_le_three chi⁻¹ (1 - s) (by
      simp only [sub_re, one_re]
      linarith)
    have hqpow :
        (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) ≤ (q : ℝ) ^ (11 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
    have hqpowstep : (q : ℝ) ^ 11 ≤ (q : ℝ) ^ 12 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hq0 11) hq1
    have hTpowstep : (|s.im| + 2) ^ 11 ≤ (|s.im| + 2) ^ 12 := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hT0 11) hT1
    calc
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
            ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
          ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
            DirichletCharacter.gammaFactor chi s‖ ≤
          (q : ℝ) ^ 11 * 3 * (Cgamma * (|s.im| + 2) ^ 11) := by
        gcongr
      _ = (3 * Cgamma) * (q : ℝ) ^ 11 * (|s.im| + 2) ^ 11 := by
        ring
      _ ≤ (3 * Cgamma) * (q : ℝ) ^ 12 * (|s.im| + 2) ^ 12 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hqpowstep (by positivity)) hTpowstep
          (pow_nonneg hT0 11) (by positivity)
      _ = (3 * Cgamma) * ((q : ℝ) * (|s.im| + 2)) ^ 12 := by
        rw [mul_pow]
        ring

private lemma PrimitiveLFunctionFixedStrip_natCast_le_four_pow (n : ℕ) : (n : ℝ) ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      have hone : (1 : ℝ) ≤ 4 ^ n := one_le_pow₀ (by norm_num)
      nlinarith

theorem exists_norm_LFunction_fixedStrip_le_pow :
    ∃ A : ℕ, 12 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(10 : ℝ) ≤ s.re → s.re ≤ (1 / 2 : ℝ) →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨C, _hCpos, hC⟩ :=
    exists_norm_LFunction_fixedStrip_le_const_mul_pow_twelve
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge C
  refine ⟨n + 12, by omega, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hT2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
  have hbase4 : (4 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) := by
    nlinarith
  have hbase0 : (0 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) :=
    zero_le_four.trans hbase4
  have hCbase : C ≤ ((q : ℝ) * (|s.im| + 2)) ^ n := by
    calc
      C ≤ (n : ℝ) := hn
      _ ≤ 4 ^ n := PrimitiveLFunctionFixedStrip_natCast_le_four_pow n
      _ ≤ ((q : ℝ) * (|s.im| + 2)) ^ n :=
        pow_le_pow_left₀ (by norm_num) hbase4 n
  calc
    ‖DirichletCharacter.LFunction chi s‖ ≤
        C * ((q : ℝ) * (|s.im| + 2)) ^ 12 :=
      hC q hq chi hchi s hslo hshi
    _ ≤ ((q : ℝ) * (|s.im| + 2)) ^ n *
        ((q : ℝ) * (|s.im| + 2)) ^ 12 :=
      mul_le_mul_of_nonneg_right hCbase (pow_nonneg hbase0 12)
    _ = ((q : ℝ) * (|s.im| + 2)) ^ (n + 12) := by
      rw [pow_add]

end BoundedGaps.Maynard

end

/-! ## Dirichlet L-functions on the Goldfeld strip

Source module `BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionClosedStripGrowth`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

theorem norm_inducingEulerProduct_le_sq_of_neg_one_le_re
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : -(1 : ℝ) ≤ s.re) :
    ‖inducingEulerProduct chi s‖ ≤ (q : ℝ) ^ 2 := by
  rw [inducingEulerProduct]
  calc
    ‖∏ p ∈ q.primeFactors,
        (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))‖ ≤
        ∏ p ∈ q.primeFactors,
          ‖1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) ^ 2 := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
        have hpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) := by
          calc
            (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
            _ = (p : ℝ) := Real.rpow_one _
        calc
          ‖1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ ≤
              1 + ‖chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ := by
            simpa using norm_sub_le (1 : ℂ)
              (chi.primitiveCharacter p * (p : ℂ) ^ (-s))
          _ = 1 + ‖chi.primitiveCharacter p‖ * (p : ℝ) ^ (-s.re) := by
            rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpPrime.pos, neg_re]
          _ ≤ 1 + 1 * (p : ℝ) := by
            gcongr
            exact chi.primitiveCharacter.norm_le_one p
          _ ≤ (p : ℝ) ^ 2 := by nlinarith
    _ = (∏ p ∈ q.primeFactors, (p : ℝ)) ^ 2 :=
      Finset.prod_pow q.primeFactors 2 (fun p : ℕ => (p : ℝ))
    _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ 2 := by
      push_cast
      rfl
    _ ≤ (q : ℝ) ^ 2 := by
      gcongr
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q)
        (Nat.prod_primeFactors_dvd q)

private theorem DirichletLFunctionClosedStripGrowth_exists_norm_primitiveLFunction_closedStrip_le_pow :
    ∃ A : ℕ, 12 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(1 : ℝ) ≤ s.re → s.re ≤ 3 →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨A, hA, hleft⟩ := exists_norm_LFunction_fixedStrip_le_pow
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg s.im]
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  by_cases hleftCase : s.re ≤ (1 / 2 : ℝ)
  · exact hleft q hq chi hchi s (by linarith) hleftCase
  · have hhalf : (1 / 2 : ℝ) ≤ s.re := le_of_not_ge hleftCase
    by_cases hcentral : s.re ≤ 2
    · have hc := norm_LFunction_centralStrip_le hq chi hchi
          (sigma := s.re) (t := s.im) hhalf hcentral
      have hsarg : (((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I) = s := by
        apply Complex.ext <;> simp
      rw [hsarg] at hc
      have hsqrt : Real.sqrt (q : ℝ) ≤ q :=
        Real.sqrt_le_self_iff.mpr (Or.inr hq1)
      have hlog : Real.log (q : ℝ) ≤ q :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans
          (sub_le_self _ zero_le_one)
      have hcentralBound :
          2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤ B ^ 2 := by
        calc
          2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
              2 * T * (q : ℝ) * (q : ℝ) := by gcongr
          _ ≤ ((q : ℝ) * T) ^ 2 := by nlinarith
          _ = B ^ 2 := rfl
      calc
        ‖DirichletCharacter.LFunction chi s‖ ≤
            2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
          simpa [T] using hc
        _ ≤ B ^ 2 := hcentralBound
        _ ≤ B ^ A := pow_le_pow_right₀ hB1 (by omega)
    · have hfar : (2 : ℝ) ≤ s.re := le_of_not_ge hcentral
      have hf := norm_LFunction_farRight_le_three chi s hfar
      calc
        ‖DirichletCharacter.LFunction chi s‖ ≤ 3 := hf
        _ ≤ B ^ 1 := by simp; linarith
        _ ≤ B ^ A := pow_le_pow_right₀ hB1 (by omega)

theorem exists_norm_LFunction_closedStrip_le_pow :
    ∃ A : ℕ, 14 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 →
          ∀ s : ℂ, -(1 : ℝ) ≤ s.re → s.re ≤ 3 →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨A, hA, hprimitive⟩ :=
    DirichletLFunctionClosedStripGrowth_exists_norm_primitiveLFunction_closedStrip_le_pow
  refine ⟨A + 2, by omega, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  let d := chi.conductor
  letI : NeZero d := ⟨chi.conductor_ne_zero⟩
  have hd1 : 1 < d := by
    have hdne : d ≠ 1 := by
      intro hd
      apply hchi
      exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd
    have hd0 : d ≠ 0 := NeZero.ne d
    omega
  have hdq : d ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg s.im]
  have hT0 : (0 : ℝ) ≤ T := zero_le_two.trans hT2
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hprimitiveBound := hprimitive d hd1 chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive s hslo hshi
  have hbase : (d : ℝ) * T ≤ B := by
    dsimp [B]
    gcongr
  have hprimitiveBound' :
      ‖DirichletCharacter.LFunction chi.primitiveCharacter s‖ ≤ B ^ A :=
    hprimitiveBound.trans (by
      simpa [T] using
        pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg d) hT0) hbase A)
  have hEuler := norm_inducingEulerProduct_le_sq_of_neg_one_le_re chi hslo
  have hqB : (q : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hqSq : (q : ℝ) ^ 2 ≤ B ^ 2 := by gcongr
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi (.inl hchi),
    norm_mul]
  calc
    ‖DirichletCharacter.LFunction chi.primitiveCharacter s‖ *
        ‖inducingEulerProduct chi s‖ ≤ B ^ A * B ^ 2 :=
      mul_le_mul hprimitiveBound' (hEuler.trans hqSq)
        (norm_nonneg _) (pow_nonneg (zero_le_one.trans hB1) A)
    _ = B ^ (A + 2) := by rw [pow_add]

end BoundedGaps.Maynard

end

/-! ## Goldfeld's four-factor coefficient

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldCoefficient`. -/

noncomputable section

open scoped ComplexOrder

open ArithmeticFunction

namespace BoundedGaps.Maynard

private instance GoldfeldCoefficient_goldfeldLcmNeZero {q1 q : ℕ} [NeZero q1] [NeZero q] :
    NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

noncomputable def goldfeldCoefficient
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) : ArithmeticFunction ℂ :=
  ((ArithmeticFunction.zeta * toArithmeticFunction (chi1 ·)) *
      toArithmeticFunction (chi ·)) *
    toArithmeticFunction (DirichletCharacter.mul chi1 chi ·)

theorem goldfeldCrossLevelMul_apply
    {q1 q n : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) :
    DirichletCharacter.mul chi1 chi n = chi1 n * chi n := by
  by_cases h1 : Nat.Coprime n q1
  · by_cases h2 : Nat.Coprime n q
    · have hlcm : Nat.Coprime n (Nat.lcm q1 q) :=
        Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul q1 q) (h1.mul_right h2)
      change
        (chi1.changeLevel (Nat.dvd_lcm_left q1 q) *
          chi.changeLevel (Nat.dvd_lcm_right q1 q)) n = _
      rw [MulChar.mul_apply]
      have hInt : IsCoprime (n : ℤ) (Nat.lcm q1 q : ℤ) :=
        Nat.Coprime.isCoprime hlcm
      simpa using congrArg₂ (· * ·)
        (DirichletCharacter.changeLevel_eq_cast_of_dvd' chi1
          (Nat.dvd_lcm_left q1 q) hInt)
        (DirichletCharacter.changeLevel_eq_cast_of_dvd' chi
          (Nat.dvd_lcm_right q1 q) hInt)
    · have hlcm : ¬Nat.Coprime n (Nat.lcm q1 q) := fun h =>
        h2 (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_right q1 q) h)
      have hpzero : DirichletCharacter.mul chi1 chi n = 0 :=
        MulChar.map_nonunit _ (by
          simpa [ZMod.isUnit_iff_coprime] using hlcm)
      have hzero : chi n = 0 :=
        MulChar.map_nonunit _ (by
          simpa [ZMod.isUnit_iff_coprime] using h2)
      rw [hpzero, hzero, mul_zero]
  · have hlcm : ¬Nat.Coprime n (Nat.lcm q1 q) := fun h =>
      h1 (Nat.Coprime.of_dvd_right (Nat.dvd_lcm_left q1 q) h)
    have hpzero : DirichletCharacter.mul chi1 chi n = 0 :=
      MulChar.map_nonunit _ (by
        simpa [ZMod.isUnit_iff_coprime] using hlcm)
    have hzero : chi1 n = 0 :=
      MulChar.map_nonunit _ (by
        simpa [ZMod.isUnit_iff_coprime] using h1)
    rw [hpzero, hzero, zero_mul]

theorem goldfeldCoefficient_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) :
    goldfeldCoefficient chi1 chi 1 = 1 := by
  simp only [goldfeldCoefficient, ArithmeticFunction.mul_apply_one]
  simp [toArithmeticFunction]

private theorem GoldfeldCoefficient_characterAF_prime_pow
    {q p k : ℕ} (chi : DirichletCharacter ℂ q) (hp : p.Prime) :
    toArithmeticFunction (chi ·) (p ^ k) = (chi p) ^ k := by
  rw [← chi.apply_eq_toArithmeticFunction_apply (pow_ne_zero k hp.ne_zero)]
  simpa only [Nat.cast_pow] using map_pow chi (p : ZMod q) k

private theorem GoldfeldCoefficient_productAF_prime_pow
    {q1 q p k : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hp : p.Prime) :
    toArithmeticFunction (DirichletCharacter.mul chi1 chi ·) (p ^ k) =
      (chi1 p * chi p) ^ k := by
  rw [GoldfeldCoefficient_characterAF_prime_pow _ hp, goldfeldCrossLevelMul_apply]

private theorem GoldfeldCoefficient_zeta_prime_pow {p k : ℕ} (hp : p.Prime) :
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (p ^ k) = 1 := by
  have hpow : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
  simp only [ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hpow, Nat.cast_one]

private theorem GoldfeldCoefficient_mul_apply_prime_pow
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime) :
    (f * g) (p ^ k) =
      ∑ i ∈ Finset.range (k + 1), f (p ^ i) * g (p ^ (k - i)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => f x * g y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.pow_div (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hp.pos]

private theorem GoldfeldCoefficient_mul_apply_prime_pow_eq_left_of_right_unit
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime)
    (hone : g 1 = 1) (hzero : ∀ j, 0 < j → g (p ^ j) = 0) :
    (f * g) (p ^ k) = f (p ^ k) := by
  rw [GoldfeldCoefficient_mul_apply_prime_pow f g hp]
  classical
  rw [Finset.sum_eq_single k]
  · simp [hone]
  · intro i hi hik
    have hik' : i < k :=
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).lt_of_ne hik
    rw [hzero (k - i) (Nat.sub_pos_of_lt hik'), mul_zero]
  · simp

private theorem GoldfeldCoefficient_mul_prime_pow_nonneg_of_local_eq
    (f g : ArithmeticFunction ℂ) {p k : ℕ} (hp : p.Prime)
    (hf : ∀ n, 0 ≤ f n) (hlocal : ∀ j, g (p ^ j) = f (p ^ j)) :
    0 ≤ (f * g) (p ^ k) := by
  rw [GoldfeldCoefficient_mul_apply_prime_pow f g hp]
  exact Finset.sum_nonneg fun i _ => by
    rw [hlocal]
    exact mul_nonneg (hf _) (hf _)

private theorem GoldfeldCoefficient_goldfeldCoefficient_prime_pow_nonneg
    {q1 q p : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    (hp : p.Prime) (k : ℕ) :
    0 ≤ goldfeldCoefficient chi1 chi (p ^ k) := by
  let A := toArithmeticFunction (chi1 ·)
  let B := toArithmeticFunction (chi ·)
  let C := toArithmeticFunction (DirichletCharacter.mul chi1 chi ·)
  let Z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  have hA : ∀ j, A (p ^ j) = (chi1 p) ^ j := fun _ =>
    GoldfeldCoefficient_characterAF_prime_pow chi1 hp
  have hB : ∀ j, B (p ^ j) = (chi p) ^ j := fun _ =>
    GoldfeldCoefficient_characterAF_prime_pow chi hp
  have hC : ∀ j, C (p ^ j) = (chi1 p * chi p) ^ j := fun _ =>
    GoldfeldCoefficient_productAF_prime_pow chi1 chi hp
  have hZ : ∀ j, Z (p ^ j) = 1 := fun _ => GoldfeldCoefficient_zeta_prime_pow hp
  have hZA : ∀ n, 0 ≤ (Z * A) n := fun n => by
    simpa [Z, A, DirichletCharacter.zetaMul] using
      chi1.zetaMul_nonneg hsquare1 n
  have hZB : ∀ n, 0 ≤ (Z * B) n := fun n => by
    simpa [Z, B, DirichletCharacter.zetaMul] using
      chi.zetaMul_nonneg hsquare n
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare1 p with ha | ha | ha
  · have hCunit : C 1 = 1 := by simpa using hC 0
    have hCzero : ∀ j, 0 < j → C (p ^ j) = 0 := by
      intro j hj
      rw [hC]
      simp [ha, zero_pow hj.ne']
    have hAC (j : ℕ) : (A * C) (p ^ j) = A (p ^ j) :=
      GoldfeldCoefficient_mul_apply_prime_pow_eq_left_of_right_unit A C hp hCunit hCzero
    have hACunit : (A * C) 1 = 1 := by
      calc
        (A * C) 1 = (A * C) (p ^ 0) := by simp
        _ = A (p ^ 0) := hAC 0
        _ = (chi1 p) ^ 0 := hA 0
        _ = 1 := by simp
    have hACzero : ∀ j, 0 < j → (A * C) (p ^ j) = 0 := by
      intro j hj
      rw [hAC, hA]
      simp [ha, zero_pow hj.ne']
    rw [goldfeldCoefficient]
    rw [show ((Z * A) * B) * C = (Z * B) * (A * C) by ac_rfl]
    rw [GoldfeldCoefficient_mul_apply_prime_pow_eq_left_of_right_unit (Z * B) (A * C)
      hp hACunit hACzero]
    exact hZB _
  · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with hb | hb | hb
    · have hBunit : B 1 = 1 := by simpa using hB 0
      have hBzero : ∀ j, 0 < j → B (p ^ j) = 0 := by
        intro j hj
        rw [hB]
        simp [hb, zero_pow hj.ne']
      have hCB (j : ℕ) : (C * B) (p ^ j) = C (p ^ j) :=
        GoldfeldCoefficient_mul_apply_prime_pow_eq_left_of_right_unit C B hp hBunit hBzero
      have hCBunit : (C * B) 1 = 1 := by
        calc
          (C * B) 1 = (C * B) (p ^ 0) := by simp
          _ = C (p ^ 0) := hCB 0
          _ = (chi1 p * chi p) ^ 0 := hC 0
          _ = 1 := by simp
      have hCBzero : ∀ j, 0 < j → (C * B) (p ^ j) = 0 := by
        intro j hj
        rw [hCB, hC]
        simp [hb, zero_pow hj.ne']
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      rw [GoldfeldCoefficient_mul_apply_prime_pow_eq_left_of_right_unit (Z * A) (C * B)
        hp hCBunit hCBzero]
      exact hZA _
    · have hpair (j : ℕ) : (B * C) (p ^ j) = (Z * A) (p ^ j) := by
        rw [GoldfeldCoefficient_mul_apply_prime_pow B C hp, GoldfeldCoefficient_mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hB, hC, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (B * C) by ac_rfl]
      exact GoldfeldCoefficient_mul_prime_pow_nonneg_of_local_eq (Z * A) (B * C) hp hZA hpair
    · have hpair (j : ℕ) : (A * C) (p ^ j) = (Z * B) (p ^ j) := by
        rw [GoldfeldCoefficient_mul_apply_prime_pow A C hp, GoldfeldCoefficient_mul_apply_prime_pow Z B hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hA, hC, hZ, hB]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * B) * (A * C) by ac_rfl]
      exact GoldfeldCoefficient_mul_prime_pow_nonneg_of_local_eq (Z * B) (A * C) hp hZB hpair
  · rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with hb | hb | hb
    · have hBunit : B 1 = 1 := by simpa using hB 0
      have hBzero : ∀ j, 0 < j → B (p ^ j) = 0 := by
        intro j hj
        rw [hB]
        simp [hb, zero_pow hj.ne']
      have hCB (j : ℕ) : (C * B) (p ^ j) = C (p ^ j) :=
        GoldfeldCoefficient_mul_apply_prime_pow_eq_left_of_right_unit C B hp hBunit hBzero
      have hCBunit : (C * B) 1 = 1 := by
        calc
          (C * B) 1 = (C * B) (p ^ 0) := by simp
          _ = C (p ^ 0) := hCB 0
          _ = (chi1 p * chi p) ^ 0 := hC 0
          _ = 1 := by simp
      have hCBzero : ∀ j, 0 < j → (C * B) (p ^ j) = 0 := by
        intro j hj
        rw [hCB, hC]
        simp [hb, zero_pow hj.ne']
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      rw [GoldfeldCoefficient_mul_apply_prime_pow_eq_left_of_right_unit (Z * A) (C * B)
        hp hCBunit hCBzero]
      exact hZA _
    · have hpair (j : ℕ) : (B * C) (p ^ j) = (Z * A) (p ^ j) := by
        rw [GoldfeldCoefficient_mul_apply_prime_pow B C hp, GoldfeldCoefficient_mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hB, hC, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (B * C) by ac_rfl]
      exact GoldfeldCoefficient_mul_prime_pow_nonneg_of_local_eq (Z * A) (B * C) hp hZA hpair
    · have hpair (j : ℕ) : (C * B) (p ^ j) = (Z * A) (p ^ j) := by
        rw [GoldfeldCoefficient_mul_apply_prime_pow C B hp, GoldfeldCoefficient_mul_apply_prime_pow Z A hp]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hC, hB, hZ, hA]
        simp [ha, hb]
      rw [goldfeldCoefficient]
      rw [show ((Z * A) * B) * C = (Z * A) * (C * B) by ac_rfl]
      exact GoldfeldCoefficient_mul_prime_pow_nonneg_of_local_eq (Z * A) (C * B) hp hZA hpair

private theorem GoldfeldCoefficient_goldfeldCoefficient_isMultiplicative
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q) :
    (goldfeldCoefficient chi1 chi).IsMultiplicative := by
  exact (((ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    chi1.isMultiplicative_toArithmeticFunction).mul
      chi.isMultiplicative_toArithmeticFunction).mul
        (DirichletCharacter.mul chi1 chi).isMultiplicative_toArithmeticFunction)

theorem goldfeldCoefficient_nonneg
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1) (n : ℕ) :
    0 ≤ goldfeldCoefficient chi1 chi n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [(GoldfeldCoefficient_goldfeldCoefficient_isMultiplicative chi1 chi).multiplicative_factorization _ hn]
    exact Finset.prod_nonneg fun p hp =>
      GoldfeldCoefficient_goldfeldCoefficient_prime_pow_nonneg chi1 chi hsquare1 hsquare
        (Nat.prime_of_mem_primeFactors hp) _

private theorem GoldfeldCoefficient_characterAF_LSeriesHasSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (toArithmeticFunction (chi ·)) s
      (DirichletCharacter.LFunction chi s) := by
  have hsummable : LSeriesSummable (toArithmeticFunction (chi ·)) s :=
    (LSeriesSummable_congr s fun hn =>
      chi.apply_eq_toArithmeticFunction_apply hn).mp
        (ZMod.LSeriesSummable_of_one_lt_re chi hs)
  rw [chi.LFunction_eq_LSeries hs,
    LSeries_congr (fun hn => chi.apply_eq_toArithmeticFunction_apply hn) s]
  exact hsummable.LSeriesHasSum

theorem goldfeldCoefficient_LSeriesHasSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (goldfeldCoefficient chi1 chi) s
      (riemannZeta s * DirichletCharacter.LFunction chi1 s *
        DirichletCharacter.LFunction chi s *
          DirichletCharacter.LFunction
            (DirichletCharacter.mul chi1 chi) s) := by
  exact ArithmeticFunction.LSeriesHasSum_mul
    (ArithmeticFunction.LSeriesHasSum_mul
      (ArithmeticFunction.LSeriesHasSum_mul
        (ArithmeticFunction.LSeriesHasSum_zeta hs)
        (GoldfeldCoefficient_characterAF_LSeriesHasSum chi1 hs))
      (GoldfeldCoefficient_characterAF_LSeriesHasSum chi hs))
    (GoldfeldCoefficient_characterAF_LSeriesHasSum (DirichletCharacter.mul chi1 chi) hs)

end BoundedGaps.Maynard

end

/-! ## Smooth Mellin inversion for an absolutely convergent L-series

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldMellinInversion`. -/

noncomputable section

open Complex MeasureTheory

namespace BoundedGaps.Maynard

private lemma GoldfeldMellinInversion_cpow_div_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ s = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (div_ne_zero hx.ne' hy.ne')),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.exp_sub]
  congr 1
  rw [← sub_mul]
  congr 1
  rw [← Complex.ofReal_log (div_nonneg hx.le hy.le),
    Real.log_div hx.ne' hy.ne', Complex.ofReal_sub,
    Complex.ofReal_log hx.le, Complex.ofReal_log hy.le]

private lemma GoldfeldMellinInversion_cpow_neg_div_of_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((x / y : ℝ) : ℂ) ^ (-s) =
      (x : ℂ) ^ (-s) * (y : ℂ) ^ s := by
  rw [GoldfeldMellinInversion_cpow_div_of_pos hx hy, Complex.cpow_neg, Complex.cpow_neg,
    div_inv_eq_mul]

theorem smoothMellinLSeriesInversion
    (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (phi : ℝ → ℂ) {alpha x : ℝ}
    (_halpha : 0 < alpha) (hx : 0 < x)
    (hsum : LSeriesSummable a (alpha : ℂ))
    (hphi : MellinConvergent phi (alpha : ℂ))
    (hphiVertical : VerticalIntegrable (mellin phi) alpha)
    (hphiContinuous : Continuous phi) :
    (∑' n : ℕ, a n * phi ((n : ℝ) / x)) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t : ℝ,
          LSeries a ((alpha : ℂ) + t * I) *
            mellin phi ((alpha : ℂ) + t * I) *
            (x : ℂ) ^ ((alpha : ℂ) + t * I) := by
  let s : ℝ → ℂ := fun t => (alpha : ℂ) + t * I
  let phiLine : ℝ → ℂ := fun t => mellin phi (s t)
  let F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term a (s t) n * phiLine t * (x : ℂ) ^ (s t)
  let G : ℝ → ℂ := fun t =>
    LSeries a (s t) * phiLine t * (x : ℂ) ^ (s t)
  have hsContinuous : Continuous s := by
    fun_prop
  have hxPowContinuous : Continuous fun t : ℝ => (x : ℂ) ^ (s t) := by
    exact continuous_const.cpow hsContinuous fun _ =>
      Complex.ofReal_mem_slitPlane.mpr hx
  have htermContinuous (n : ℕ) :
      Continuous fun t : ℝ => LSeries.term a (s t) n := by
    rcases eq_or_ne n 0 with rfl | hn
    · simpa using (continuous_const : Continuous fun _ : ℝ => (0 : ℂ))
    · have hnReal : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hpow : Continuous fun t : ℝ => (n : ℂ) ^ (s t) := by
        exact continuous_const.cpow hsContinuous fun _ => by
          simpa only [← Complex.ofReal_natCast] using
            Complex.ofReal_mem_slitPlane.mpr hnReal
      have hpowNe (t : ℝ) : (n : ℂ) ^ (s t) ≠ 0 :=
        Complex.cpow_ne_zero_iff.mpr <| Or.inl <| Nat.cast_ne_zero.mpr hn
      simp only [LSeries.term_of_ne_zero hn]
      exact continuous_const.div hpow hpowNe
  have hphiLineIntegrable : Integrable phiLine := by
    simpa [VerticalIntegrable, phiLine, s] using hphiVertical
  have hmultiplierContinuous (n : ℕ) : Continuous fun t : ℝ =>
      LSeries.term a (s t) n * (x : ℂ) ^ (s t) :=
    (htermContinuous n).mul hxPowContinuous
  have hmultiplierNorm (n : ℕ) (t : ℝ) :
      ‖LSeries.term a (s t) n * (x : ℂ) ^ (s t)‖ =
        ‖LSeries.term a (alpha : ℂ) n‖ * x ^ alpha := by
    rw [norm_mul, LSeries.norm_term_eq, LSeries.norm_term_eq,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [s]
  have hFIntegrable (n : ℕ) : Integrable (F n) := by
    have h := hphiLineIntegrable.mul_bdd
      (hmultiplierContinuous n).aestronglyMeasurable
      (ae_of_all _ fun t => (hmultiplierNorm n t).le)
    convert h using 1
    funext t
    simp only [F, phiLine]
    ring
  have hFNormIntegral (n : ℕ) :
      (∫ t : ℝ, ‖F n t‖) =
        ‖LSeries.term a (alpha : ℂ) n‖ * x ^ alpha *
          ∫ t : ℝ, ‖phiLine t‖ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [show F n t = phiLine t *
        (LSeries.term a (s t) n * (x : ℂ) ^ (s t)) by
      simp only [F]
      ring]
    rw [norm_mul, hmultiplierNorm]
    ring
  have hFNormSummable : Summable fun n : ℕ => ∫ t : ℝ, ‖F n t‖ := by
    refine (hsum.norm.mul_right
      (x ^ alpha * ∫ t : ℝ, ‖phiLine t‖)).congr ?_
    intro n
    rw [hFNormIntegral]
    ring
  have hFHasSum (t : ℝ) : HasSum (fun n : ℕ => F n t) (G t) := by
    have hline : LSeriesSummable a (s t) :=
      hsum.of_re_le_re (by simp [s])
    have h := (hline.LSeriesHasSum.mul_right (phiLine t)).mul_right
      ((x : ℂ) ^ (s t))
    simpa [F, G] using h
  have hinterchange : HasSum (fun n : ℕ => ∫ t : ℝ, F n t)
      (∫ t : ℝ, G t) := by
    have h := hasSum_integral_of_summable_integral_norm hFIntegrable hFNormSummable
    rw [← integral_congr_ae
      (ae_of_all _ fun t => (hFHasSum t).tsum_eq)]
    exact h
  have hterm (n : ℕ) :
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * (∫ t : ℝ, F n t) =
        a n * phi ((n : ℝ) / x) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [ha0, F]
    · have hnReal : (0 : ℝ) < n := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hratio : 0 < (n : ℝ) / x := div_pos hnReal hx
      have hpoint (t : ℝ) : F n t =
          a n * (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t := by
        dsimp only [F]
        rw [LSeries.term_def₀ ha0, GoldfeldMellinInversion_cpow_neg_div_of_pos hnReal hx]
        simp only [Complex.ofReal_natCast]
        ring
      have hintegral : (∫ t : ℝ, F n t) =
          a n * ∫ t : ℝ,
            (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t := by
        calc
          (∫ t : ℝ, F n t) = ∫ t : ℝ,
              a n * ((((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t) := by
            apply integral_congr_ae
            exact ae_of_all _ fun t => by rw [hpoint]; ring
          _ = a n * ∫ t : ℝ,
              (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t :=
            MeasureTheory.integral_const_mul _ _
      have hinversion := mellinInv_mellin_eq alpha phi hratio hphi
        hphiVertical (hphiContinuous.continuousAt)
      have hinversion' :
          (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
              (∫ t : ℝ,
                (((n : ℝ) / x : ℝ) : ℂ) ^ (-(s t)) * phiLine t) =
            phi ((n : ℝ) / x) := by
        simpa [mellinInv, s, phiLine, smul_eq_mul, div_eq_mul_inv,
          mul_comm] using hinversion
      rw [hintegral, ← mul_assoc, mul_comm _ (a n), mul_assoc,
        hinversion']
  have hscaled := hinterchange.mul_left (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  have hsumSmoothed : HasSum (fun n : ℕ =>
      a n * phi ((n : ℝ) / x))
      ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t : ℝ, G t) :=
    hscaled.congr_fun fun n => (hterm n).symm
  simpa [G, phiLine, s] using hsumSmoothed.tsum_eq

end BoundedGaps.Maynard

end

/-! ## Goldfeld's smooth plateau and Mellin boundary

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldPlateauMellin`. -/

noncomputable section

open Complex Set MeasureTheory Filter

open scoped ContDiff Topology

namespace BoundedGaps.Maynard

private noncomputable def GoldfeldPlateauMellin_goldfeldPlateauBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 2, 3 / 2, by norm_num, by norm_num⟩

noncomputable def goldfeldPlateau : ℝ → ℝ := GoldfeldPlateauMellin_goldfeldPlateauBump

theorem goldfeldPlateau_contDiff : ContDiff ℝ ∞ goldfeldPlateau := by
  simpa [goldfeldPlateau] using
    (GoldfeldPlateauMellin_goldfeldPlateauBump.contDiff : ContDiff ℝ ∞ (GoldfeldPlateauMellin_goldfeldPlateauBump : ℝ → ℝ))

theorem goldfeldPlateau_range : Set.range goldfeldPlateau ⊆ Icc 0 1 := by
  rintro _ ⟨y, rfl⟩
  exact ⟨GoldfeldPlateauMellin_goldfeldPlateauBump.nonneg, GoldfeldPlateauMellin_goldfeldPlateauBump.le_one⟩

theorem goldfeldPlateau_nonneg (y : ℝ) : 0 ≤ goldfeldPlateau y := by
  exact (goldfeldPlateau_range ⟨y, rfl⟩).1

theorem goldfeldPlateau_le_one (y : ℝ) : goldfeldPlateau y ≤ 1 := by
  exact (goldfeldPlateau_range ⟨y, rfl⟩).2

theorem goldfeldPlateau_eq_one {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    goldfeldPlateau y = 1 := by
  apply GoldfeldPlateauMellin_goldfeldPlateauBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq]
  simp only [GoldfeldPlateauMellin_goldfeldPlateauBump]
  rw [abs_le]
  constructor <;> linarith

theorem goldfeldPlateau_eq_zero {y : ℝ} (hy : 2 ≤ y) :
    goldfeldPlateau y = 0 := by
  apply GoldfeldPlateauMellin_goldfeldPlateauBump.zero_of_le_dist
  rw [Real.dist_eq]
  simp only [GoldfeldPlateauMellin_goldfeldPlateauBump]
  rw [abs_of_nonneg (by linarith : 0 ≤ y - 1 / 2)]
  linarith

theorem goldfeldPlateau_hasCompactSupport :
    HasCompactSupport goldfeldPlateau := by
  simpa [goldfeldPlateau] using GoldfeldPlateauMellin_goldfeldPlateauBump.hasCompactSupport

private noncomputable def GoldfeldPlateauMellin_goldfeldPlateauComplex : ℝ → ℂ :=
  fun y => goldfeldPlateau y

noncomputable def goldfeldRawMellin (s : ℂ) : ℂ :=
  mellin GoldfeldPlateauMellin_goldfeldPlateauComplex s

private lemma GoldfeldPlateauMellin_goldfeldPlateauComplex_locallyIntegrable :
    LocallyIntegrableOn GoldfeldPlateauMellin_goldfeldPlateauComplex (Ioi (0 : ℝ)) := by
  apply (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous).continuousOn
    |>.locallyIntegrableOn measurableSet_Ioi

private lemma GoldfeldPlateauMellin_goldfeldPlateauComplex_isBigO_top :
    ∀ a : ℝ, GoldfeldPlateauMellin_goldfeldPlateauComplex =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  intro a
  refine Filter.Eventually.isBigO ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
  change ‖(goldfeldPlateau y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_eq_zero hy.le]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg (by linarith) _

private lemma GoldfeldPlateauMellin_goldfeldPlateauComplex_isBigO_zero :
    GoldfeldPlateauMellin_goldfeldPlateauComplex =O[nhdsWithin 0 (Ioi 0)] (fun _ : ℝ => (1 : ℝ)) := by
  refine Filter.Eventually.isBigO ?_
  filter_upwards [] with y
  change ‖(goldfeldPlateau y : ℂ)‖ ≤ 1
  calc
    ‖(goldfeldPlateau y : ℂ)‖ = |goldfeldPlateau y| := RCLike.norm_ofReal _
    _ = goldfeldPlateau y := abs_of_nonneg (goldfeldPlateau_nonneg y)
    _ ≤ 1 := goldfeldPlateau_le_one y

theorem goldfeldRawMellin_convergent {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent GoldfeldPlateauMellin_goldfeldPlateauComplex s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
    GoldfeldPlateauMellin_goldfeldPlateauComplex_locallyIntegrable ?_ ?_ ?_ ?_
  · simpa using GoldfeldPlateauMellin_goldfeldPlateauComplex_isBigO_top (s.re + 1)
  · linarith
  · simpa using GoldfeldPlateauMellin_goldfeldPlateauComplex_isBigO_zero
  · linarith

noncomputable def goldfeldPlateauDerivativeComplex : ℝ → ℂ :=
  fun y => ((deriv goldfeldPlateau) y : ℂ)

noncomputable def goldfeldMellinDerivativeWeight (y : ℝ) : ℂ :=
  (y : ℂ) * goldfeldPlateauDerivativeComplex y

theorem goldfeldPlateau_deriv_contDiff :
    ContDiff ℝ ∞ (deriv goldfeldPlateau) :=
  (contDiff_infty_iff_deriv.mp goldfeldPlateau_contDiff).2

private theorem GoldfeldPlateauMellin_goldfeldPlateau_deriv_hasCompactSupport :
    HasCompactSupport (deriv goldfeldPlateau) :=
  goldfeldPlateau_hasCompactSupport.deriv

theorem goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    deriv goldfeldPlateau y = 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y := hasDerivAt_const y 1
  have h := hconst.congr_of_eventuallyEq
    (show (fun z : ℝ => goldfeldPlateau z) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) by
      filter_upwards [Ioo_mem_nhds hy0 hy1] with z hz
      exact goldfeldPlateau_eq_one hz.1.le hz.2.le)
  exact h.deriv

theorem goldfeldPlateau_deriv_eq_zero_of_two_lt
    {y : ℝ} (hy : 2 < y) : deriv goldfeldPlateau y = 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 y := hasDerivAt_const y 0
  have h := hconst.congr_of_eventuallyEq
    (show (fun z : ℝ => goldfeldPlateau z) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact goldfeldPlateau_eq_zero hz.le)
  exact h.deriv

private lemma GoldfeldPlateauMellin_goldfeldPlateauDerivativeComplex_locallyIntegrable :
    LocallyIntegrableOn goldfeldPlateauDerivativeComplex (Ioi (0 : ℝ)) := by
  have hcont : Continuous (deriv goldfeldPlateau) :=
    goldfeldPlateau_contDiff.continuous_deriv (by norm_num)
  exact (Complex.continuous_ofReal.comp hcont).continuousOn.locallyIntegrableOn
    (μ := volume) measurableSet_Ioi

private lemma GoldfeldPlateauMellin_goldfeldPlateauDerivativeComplex_isBigO_top :
    ∀ a : ℝ, goldfeldPlateauDerivativeComplex =O[atTop]
      (fun x : ℝ => x ^ (-a)) := by
  intro a
  refine Filter.Eventually.isBigO ?_
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
  change ‖((deriv goldfeldPlateau) y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_deriv_eq_zero_of_two_lt hy]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg (by linarith) _

private lemma GoldfeldPlateauMellin_goldfeldPlateauDerivativeComplex_isBigO_zero :
    ∀ b : ℝ, goldfeldPlateauDerivativeComplex =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => x ^ (-b)) := by
  intro b
  refine Filter.Eventually.isBigO ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with y hy
  change ‖((deriv goldfeldPlateau) y : ℂ)‖ ≤ _
  rw [goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one hy.1 hy.2]
  simp only [Complex.ofReal_zero, norm_zero]
  exact Real.rpow_nonneg hy.1.le _

private theorem GoldfeldPlateauMellin_goldfeldPlateauDerivativeComplex_mellin_differentiableAt
    (s : ℂ) :
    DifferentiableAt ℂ (mellin goldfeldPlateauDerivativeComplex) s := by
  refine mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := s.re - 1)
    GoldfeldPlateauMellin_goldfeldPlateauDerivativeComplex_locallyIntegrable ?_ ?_ ?_ ?_
  · simpa using GoldfeldPlateauMellin_goldfeldPlateauDerivativeComplex_isBigO_top (s.re + 1)
  · linarith
  · simpa using GoldfeldPlateauMellin_goldfeldPlateauDerivativeComplex_isBigO_zero (s.re - 1)
  · linarith

noncomputable def goldfeldDerivativeMellin (s : ℂ) : ℂ :=
  mellin goldfeldPlateauDerivativeComplex (s + 1)

theorem goldfeldDerivativeMellin_eq_weight (s : ℂ) :
    goldfeldDerivativeMellin s = mellin goldfeldMellinDerivativeWeight s := by
  unfold goldfeldDerivativeMellin goldfeldMellinDerivativeWeight
  rw [← mellin_cpow_smul]
  simp only [Complex.cpow_one, smul_eq_mul]

private theorem GoldfeldPlateauMellin_goldfeldDerivativeMellin_differentiableAt (s : ℂ) :
    DifferentiableAt ℂ goldfeldDerivativeMellin s := by
  exact (GoldfeldPlateauMellin_goldfeldPlateauDerivativeComplex_mellin_differentiableAt (s + 1)).comp s
    ((hasDerivAt_id' s).add_const 1).differentiableAt

theorem differentiable_goldfeldDerivativeMellin :
    Differentiable ℂ goldfeldDerivativeMellin :=
  fun s => GoldfeldPlateauMellin_goldfeldDerivativeMellin_differentiableAt s

noncomputable def goldfeldMellinCandidate (s : ℂ) : ℂ :=
  -goldfeldDerivativeMellin s / s

theorem goldfeldMellinCandidate_eq_raw {s : ℂ} (hs : 0 < s.re) :
    goldfeldMellinCandidate s = goldfeldRawMellin s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    simp at hs
  let u : ℝ → ℂ := fun x => (x : ℂ) ^ s
  let v : ℝ → ℂ := GoldfeldPlateauMellin_goldfeldPlateauComplex
  let uD : ℝ → ℂ := fun x => s * (x : ℂ) ^ (s - 1)
  let vD : ℝ → ℂ := fun x => Complex.ofReal ((deriv goldfeldPlateau) x)
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (uD x) x := by
    intro x hx
    exact hasDerivAt_ofReal_cpow_const hx.ne' hs0
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (vD x) x := by
    intro x hx
    exact (goldfeldPlateau_contDiff.differentiable (by simp)).differentiableAt
      |>.hasDerivAt.ofReal_comp
  have hvD_cont : Continuous vD := by
    exact Complex.continuous_ofReal.comp goldfeldPlateau_deriv_contDiff.continuous
  have hvD_compact : HasCompactSupport vD := by
    change HasCompactSupport (Complex.ofReal ∘ deriv goldfeldPlateau)
    exact GoldfeldPlateauMellin_goldfeldPlateau_deriv_hasCompactSupport.comp_left Complex.ofReal_zero
  have huvD : IntegrableOn (u * vD) (Ioi 0) := by
    apply Integrable.integrableOn
    exact ((Complex.continuous_ofReal_cpow_const hs).mul hvD_cont)
      |>.integrable_of_hasCompactSupport hvD_compact.mul_left
  have huDv : IntegrableOn (uD * v) (Ioi 0) := by
    have hm := goldfeldRawMellin_convergent hs
    rw [MellinConvergent] at hm
    change Integrable
      (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * GoldfeldPlateauMellin_goldfeldPlateauComplex x)
      (volume.restrict (Ioi 0))
    simpa only [smul_eq_mul, mul_assoc] using hm.const_mul s
  have hzero : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hp : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc := (Complex.continuousAt_ofReal_cpow_const 0 s (Or.inl hs)).tendsto
      change Tendsto u (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 0)
      simpa [u, Complex.zero_cpow hs0] using hc.mono_left inf_le_left
    have hv0 : Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hphi0 : GoldfeldPlateauMellin_goldfeldPlateauComplex 0 = 1 := by
        change (goldfeldPlateau 0 : ℂ) = 1
        rw [goldfeldPlateau_eq_one (by norm_num) (by norm_num)]
        norm_num
      have hc : Tendsto GoldfeldPlateauMellin_goldfeldPlateauComplex (𝓝 (0 : ℝ))
          (𝓝 (GoldfeldPlateauMellin_goldfeldPlateauComplex 0)) :=
        (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous)
          |>.continuousAt.tendsto
      change Tendsto v (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 1)
      simpa [v, hphi0] using hc.mono_left inf_le_left
    change Tendsto (fun x => u x * v x) (𝓝[>] (0 : ℝ)) (𝓝 0)
    simpa using hp.mul hv0
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have heq : u * v =ᶠ[atTop] 0 := by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
      simp [Pi.mul_apply, v, GoldfeldPlateauMellin_goldfeldPlateauComplex, goldfeldPlateau_eq_zero hx]
    exact heq.tendsto
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (a := 0) hu hv huvD huDv hzero hinfty
  have hweight : mellin goldfeldMellinDerivativeWeight s =
      ∫ x : ℝ in Ioi 0, u x * vD x := by
    rw [mellin]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [goldfeldMellinDerivativeWeight, goldfeldPlateauDerivativeComplex,
      u, vD, smul_eq_mul]
    have hpow : (x : ℂ) ^ (s - 1) * (x : ℂ) = (x : ℂ) ^ s := by
      calc
        (x : ℂ) ^ (s - 1) * (x : ℂ) =
            (x : ℂ) ^ (s - 1) * (x : ℂ) ^ (1 : ℂ) := by
              rw [Complex.cpow_one]
        _ = (x : ℂ) ^ ((s - 1) + 1) :=
          (Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')).symm
        _ = (x : ℂ) ^ s := by rw [sub_add_cancel]
    rw [← mul_assoc, hpow]
  have hraw : ∫ x : ℝ in Ioi 0, uD x * v x =
      s * ∫ x : ℝ in Ioi 0,
        (x : ℂ) ^ (s - 1) * GoldfeldPlateauMellin_goldfeldPlateauComplex x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp [uD, v, mul_assoc]
  rw [hraw] at hibp
  rw [goldfeldMellinCandidate, goldfeldDerivativeMellin_eq_weight, hweight,
    goldfeldRawMellin, mellin]
  simp only [smul_eq_mul, zero_sub, sub_zero] at hibp ⊢
  rw [hibp]
  field_simp [hs0]

theorem goldfeldMellinCandidate_meromorphic :
    MeromorphicOn goldfeldMellinCandidate Set.univ := by
  have hJ : AnalyticOnNhd ℂ goldfeldDerivativeMellin Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (fun s => GoldfeldPlateauMellin_goldfeldDerivativeMellin_differentiableAt s)
  have hneg : AnalyticOnNhd ℂ (fun s : ℂ => -goldfeldDerivativeMellin s) Set.univ := by
    exact hJ.neg
  exact hneg.meromorphicOn.div analyticOnNhd_id.meromorphicOn

theorem goldfeldMellinCandidate_analyticAt {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ goldfeldMellinCandidate s := by
  have hJ : AnalyticOnNhd ℂ goldfeldDerivativeMellin Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (fun z => GoldfeldPlateauMellin_goldfeldDerivativeMellin_differentiableAt z)
  have hneg : AnalyticOnNhd ℂ (fun z : ℂ => -goldfeldDerivativeMellin z) {0}ᶜ :=
    hJ.neg.mono (by intro z hz; exact Set.mem_univ z)
  have hdiv : AnalyticOnNhd ℂ goldfeldMellinCandidate {0}ᶜ := by
    change AnalyticOnNhd ℂ (fun z : ℂ => -goldfeldDerivativeMellin z / z) {0}ᶜ
    exact hneg.div (analyticOnNhd_id.mono (by intro z hz; exact Set.mem_univ z))
      (fun z hz => hz)
  exact hdiv s (by simp [hs])

private theorem GoldfeldPlateauMellin_goldfeldDerivativeMellin_zero :
    goldfeldDerivativeMellin 0 = -1 := by
  unfold goldfeldDerivativeMellin
  rw [show (0 : ℂ) + 1 = 1 by norm_num]
  rw [mellin]
  simp only [sub_self, cpow_zero, one_smul]
  have h := goldfeldPlateau_hasCompactSupport.integral_Ioi_deriv_eq
    (goldfeldPlateau_contDiff.of_le (by norm_num)) (0 : ℝ)
  unfold goldfeldPlateauDerivativeComplex
  change (∫ t : ℝ in Ioi 0, ((deriv goldfeldPlateau t : ℝ) : ℂ)) = -1
  have hcast := (integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t : ℝ => (deriv goldfeldPlateau) t))
  calc
    (∫ t : ℝ in Ioi 0, (((deriv goldfeldPlateau) t : ℝ) : ℂ)) =
        Complex.ofReal (∫ t : ℝ in Ioi 0, (deriv goldfeldPlateau) t) := by
          exact hcast
    _ = -Complex.ofReal (goldfeldPlateau 0) := by
      simpa using congrArg Complex.ofReal h
    _ = -1 := by
      rw [goldfeldPlateau_eq_one (by norm_num) (by norm_num)]
      norm_num

theorem goldfeldMellinCandidate_residue :
    Tendsto (fun s => s * goldfeldMellinCandidate s) (𝓝[≠] 0) (𝓝 1) := by
  have hcont : Tendsto goldfeldDerivativeMellin (𝓝 0) (𝓝 (-(1 : ℂ))) := by
    have hc := (GoldfeldPlateauMellin_goldfeldDerivativeMellin_differentiableAt 0).continuousAt
    change Tendsto goldfeldDerivativeMellin (𝓝 0)
      (𝓝 (goldfeldDerivativeMellin 0)) at hc
    simpa only [GoldfeldPlateauMellin_goldfeldDerivativeMellin_zero] using hc
  have hpunct : Tendsto (fun s : ℂ => s * goldfeldMellinCandidate s)
      (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
    have heq : (fun s : ℂ => s * goldfeldMellinCandidate s) =ᶠ[𝓝[≠] 0]
        (fun s => -goldfeldDerivativeMellin s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [goldfeldMellinCandidate]
      calc
        s * (-goldfeldDerivativeMellin s / s) =
            (-goldfeldDerivativeMellin s) * s / s := by ring
        _ = -goldfeldDerivativeMellin s := mul_div_cancel_right₀ _ hs
    have hneg : Tendsto (fun s : ℂ => -goldfeldDerivativeMellin s)
        (𝓝[≠] 0) (𝓝 (1 : ℂ)) := by
      simpa using ((hcont.mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)).neg)
    exact hneg.congr' heq.symm
  exact hpunct

structure GoldfeldMellinContinuationData where
  Phi : ℂ → ℂ
  agrees_on_right : ∀ {s : ℂ}, 0 < s.re → Phi s = goldfeldRawMellin s
  equals_candidate : ∀ s, Phi s = goldfeldMellinCandidate s
  meromorphic : MeromorphicOn Phi Set.univ
  analytic_off_zero : ∀ {s : ℂ}, s ≠ 0 → AnalyticAt ℂ Phi s
  residue_one : Tendsto (fun s => s * Phi s) (𝓝[≠] 0) (𝓝 1)
  decay_on_neg_one : ∀ (A : ℕ), 1 ≤ A →
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Phi ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A

noncomputable def goldfeldMellinContinuationData_of_decay
    (hdecay : ∀ (A : ℕ), 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖goldfeldMellinCandidate ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A) :
    GoldfeldMellinContinuationData := by
  exact
    { Phi := goldfeldMellinCandidate
      agrees_on_right := fun hs => goldfeldMellinCandidate_eq_raw hs
      equals_candidate := fun _ => rfl
      meromorphic := goldfeldMellinCandidate_meromorphic
      analytic_off_zero := fun hs => goldfeldMellinCandidate_analyticAt hs
      residue_one := goldfeldMellinCandidate_residue
      decay_on_neg_one := hdecay }

end BoundedGaps.Maynard

end

/-! ## Vertical decay for the Goldfeld Mellin candidate

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldPlateauMellinDecay`. -/

noncomputable section

open Complex Set MeasureTheory Filter Real

open scoped ContDiff Topology SchwartzMap FourierTransform

namespace BoundedGaps.Maynard

private noncomputable def GoldfeldPlateauMellinDecay_goldfeldLogKernel (u : ℝ) : ℂ :=
  (Real.exp u : ℂ) * goldfeldMellinDerivativeWeight (Real.exp (-u))

private theorem GoldfeldPlateauMellinDecay_goldfeldMellinDerivativeWeight_contDiff :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem GoldfeldPlateauMellinDecay_goldfeldLogKernel_contDiff :
    ContDiff ℝ ∞ GoldfeldPlateauMellinDecay_goldfeldLogKernel := by
  have he : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_id.exp
  have hne : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) :=
    (contDiff_id.neg).exp
  unfold GoldfeldPlateauMellinDecay_goldfeldLogKernel
  exact he.mul (GoldfeldPlateauMellinDecay_goldfeldMellinDerivativeWeight_contDiff.comp hne)

private theorem GoldfeldPlateauMellinDecay_goldfeldLogKernel_eq_zero_of_pos {u : ℝ} (hu : 0 < u) :
    GoldfeldPlateauMellinDecay_goldfeldLogKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [GoldfeldPlateauMellinDecay_goldfeldLogKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem GoldfeldPlateauMellinDecay_goldfeldLogKernel_eq_zero_of_lt_neg_log_two
    {u : ℝ} (hu : u < -Real.log 2) : GoldfeldPlateauMellinDecay_goldfeldLogKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [GoldfeldPlateauMellinDecay_goldfeldLogKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem GoldfeldPlateauMellinDecay_goldfeldLogKernel_support_subset :
    Function.support GoldfeldPlateauMellinDecay_goldfeldLogKernel ⊆ Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hleft : u < -Real.log 2 ∨ 0 < u := by
    by_cases h₁ : u < -Real.log 2
    · exact Or.inl h₁
    · have h₁' : -Real.log 2 ≤ u := le_of_not_gt h₁
      by_cases h₂ : 0 < u
      · exact Or.inr h₂
      · have h₂' : u ≤ 0 := le_of_not_gt h₂
        exact False.elim (hnot ⟨h₁', h₂'⟩)
  rcases hleft with hleft | hright
  · exact hu (GoldfeldPlateauMellinDecay_goldfeldLogKernel_eq_zero_of_lt_neg_log_two hleft)
  · exact hu (GoldfeldPlateauMellinDecay_goldfeldLogKernel_eq_zero_of_pos hright)

private theorem GoldfeldPlateauMellinDecay_goldfeldLogKernel_hasCompactSupport :
    HasCompactSupport GoldfeldPlateauMellinDecay_goldfeldLogKernel := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Icc (-Real.log 2) 0)
    isCompact_Icc
  exact GoldfeldPlateauMellinDecay_goldfeldLogKernel_support_subset

private noncomputable def GoldfeldPlateauMellinDecay_goldfeldLogKernelSchwartz : 𝓢(ℝ, ℂ) :=
  GoldfeldPlateauMellinDecay_goldfeldLogKernel_hasCompactSupport.toSchwartzMap GoldfeldPlateauMellinDecay_goldfeldLogKernel_contDiff

private theorem GoldfeldPlateauMellinDecay_goldfeldDerivativeMellin_on_neg_one (t : ℝ) :
    goldfeldDerivativeMellin ((-1 : ℂ) + t * I) =
      𝓕 GoldfeldPlateauMellinDecay_goldfeldLogKernelSchwartz (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((-1 : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((-1 : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((-1 : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((-1 : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 GoldfeldPlateauMellinDecay_goldfeldLogKernelSchwartz (t / (2 * π)) := by
      norm_num
      rw [SchwartzMap.fourier_coe]
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [GoldfeldPlateauMellinDecay_goldfeldLogKernelSchwartz, GoldfeldPlateauMellinDecay_goldfeldLogKernel]

private theorem GoldfeldPlateauMellinDecay_schwartz_pointwise_bound (f : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ‖(f : ℝ → ℂ) x‖ ≤ C / (1 + |x|) ^ A := by
  obtain ⟨C, hC, hbound⟩ := f.decay A 0
  obtain ⟨C0, hC0, hbound0⟩ := f.decay 0 0
  refine ⟨max (C * 2 ^ A) (C0 * 2 ^ A), by positivity, ?_⟩
  intro x
  by_cases hx : 1 ≤ |x|
  · have hpow : (1 + |x|) ^ A ≤ (2 * |x|) ^ A := by
      apply pow_le_pow_left₀ (by positivity) _ _
      linarith
    have hprod := hbound x
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hprod
    have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hx
    have hnorm : ‖(f : ℝ → ℂ) x‖ ≤ C / |x| ^ A := by
      apply (le_div_iff₀ (pow_pos hxpos A)).2
      simpa [mul_comm] using hprod
    calc
      ‖(f : ℝ → ℂ) x‖ ≤ C / |x| ^ A := hnorm
      _ ≤ (C * 2 ^ A) / (1 + |x|) ^ A := by
        apply (div_le_div_iff₀ (pow_pos hxpos A) (by positivity)).2
        calc
          C * (1 + |x|) ^ A ≤ C * (2 * |x|) ^ A :=
            mul_le_mul_of_nonneg_left hpow hC.le
          _ = (C * 2 ^ A) * |x| ^ A := by rw [mul_pow]; ring
      _ ≤ max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).2
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hx' : |x| < 1 := lt_of_not_ge hx
    have h0 := hbound0 x
    have h0' : ‖(f : ℝ → ℂ) x‖ ≤ C0 := by
      simpa [norm_iteratedFDeriv_zero] using h0
    have hsmall : C0 ≤ C0 * 2 ^ A / (1 + |x|) ^ A := by
      have hden : (1 + |x|) ^ A ≤ 2 ^ A := by
        apply pow_le_pow_left₀ (by positivity) _ _
        linarith
      have hdenpos : 0 < (1 + |x|) ^ A := by positivity
      apply (le_div_iff₀ hdenpos).2
      exact mul_le_mul_of_nonneg_left hden hC0.le
    have hmax : C0 * 2 ^ A / (1 + |x|) ^ A ≤
        max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    calc
      ‖(f : ℝ → ℂ) x‖ ≤ C0 := h0'
      _ ≤ C0 * 2 ^ A / (1 + |x|) ^ A := hsmall
      _ ≤ max (C * 2 ^ A) (C0 * 2 ^ A) / (1 + |x|) ^ A := hmax

theorem goldfeldMellinCandidate_decay_on_neg_one (A : ℕ) (_hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖goldfeldMellinCandidate ((-1 : ℂ) + t * I)‖ ≤ C / (1 + |t|) ^ A := by
  obtain ⟨C, hC, hpoint⟩ :=
    GoldfeldPlateauMellinDecay_schwartz_pointwise_bound (𝓕 GoldfeldPlateauMellinDecay_goldfeldLogKernelSchwartz) A
  refine ⟨C * (2 * π) ^ A, by positivity, ?_⟩
  intro t
  have hs : ((-1 : ℂ) + t * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hnorms : 1 ≤ ‖(-1 : ℂ) + t * I‖ := by
    have h := Complex.abs_re_le_norm ((-1 : ℂ) + t * I)
    norm_num at h ⊢
    exact h
  rw [goldfeldMellinCandidate, norm_div, norm_neg]
  calc
    ‖goldfeldDerivativeMellin ((-1 : ℂ) + t * I)‖ /
        ‖(-1 : ℂ) + t * I‖ ≤
      ‖goldfeldDerivativeMellin ((-1 : ℂ) + t * I)‖ :=
        (div_le_self (norm_nonneg _) hnorms)
    _ = ‖𝓕 GoldfeldPlateauMellinDecay_goldfeldLogKernelSchwartz (t / (2 * π))‖ := by
      rw [GoldfeldPlateauMellinDecay_goldfeldDerivativeMellin_on_neg_one]
    _ ≤ C / (1 + |t / (2 * π)|) ^ A := hpoint _
    _ ≤ C * (2 * π) ^ A / (1 + |t|) ^ A := by
      have hpi : 0 < (2 * π : ℝ) := by positivity
      have hpi1 : (1 : ℝ) ≤ 2 * π := by
        nlinarith [two_le_pi]
      rw [abs_div, abs_of_pos hpi]
      have hscale : 1 + |t| ≤ (2 * π) * (1 + |t| / (2 * π)) := by
        rw [mul_add, mul_div_cancel₀ _ (ne_of_gt hpi)]
        nlinarith
      have hpowscale : (1 + |t|) ^ A ≤
          ((2 * π) * (1 + |t| / (2 * π))) ^ A :=
        pow_le_pow_left₀ (by positivity) hscale A
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      calc
        C * (1 + |t|) ^ A ≤
            C * ((2 * π) ^ A * (1 + |t| / (2 * π)) ^ A) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          simpa [mul_pow] using hpowscale
        _ = (C * (2 * π) ^ A) * (1 + |t| / (2 * π)) ^ A := by ring

noncomputable def goldfeldMellinContinuationData :
    GoldfeldMellinContinuationData :=
  goldfeldMellinContinuationData_of_decay
    goldfeldMellinCandidate_decay_on_neg_one

end BoundedGaps.Maynard

end

/-! ## Positive-line integrability of the Goldfeld Mellin transform

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldMellinPositiveLine`. -/

noncomputable section

open Complex Set MeasureTheory Real

open scoped ContDiff Topology SchwartzMap FourierTransform

namespace BoundedGaps.Maynard

private noncomputable def GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel
    (alpha u : ℝ) : ℂ :=
  (Real.exp (-alpha * u) : ℂ) *
    goldfeldMellinDerivativeWeight (Real.exp (-u))

private theorem GoldfeldMellinPositiveLine_goldfeldMellinDerivativeWeight_contDiff_positiveLine :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_contDiff (alpha : ℝ) :
    ContDiff ℝ ∞ (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel alpha) := by
  have hlinear : ContDiff ℝ ∞ (fun u : ℝ => -alpha * u) :=
    contDiff_const.mul contDiff_id
  have heReal : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-alpha * u)) :=
    hlinear.exp
  have he : ContDiff ℝ ∞ (fun u : ℝ => (Real.exp (-alpha * u) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp heReal
  have harg : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) := by
    fun_prop
  unfold GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel
  exact he.mul
    (GoldfeldMellinPositiveLine_goldfeldMellinDerivativeWeight_contDiff_positiveLine.comp harg)

private theorem GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_eq_zero_of_pos
    (alpha : ℝ) {u : ℝ} (hu : 0 < u) :
    GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel alpha u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_eq_zero_of_lt_neg_log_two
    (alpha : ℝ) {u : ℝ} (hu : u < -Real.log 2) :
    GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel alpha u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_support_subset (alpha : ℝ) :
    Function.support (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel alpha) ⊆
      Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_cases hright : 0 < u
      · exact Or.inr hright
      · exact False.elim (hnot ⟨hleft', le_of_not_gt hright⟩)
  rcases hcases with hleft | hright
  · exact hu (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_eq_zero_of_lt_neg_log_two alpha hleft)
  · exact hu (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_eq_zero_of_pos alpha hright)

private theorem GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_hasCompactSupport (alpha : ℝ) :
    HasCompactSupport (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel alpha) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-Real.log 2) 0) isCompact_Icc
  exact GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_support_subset alpha

private noncomputable def GoldfeldMellinPositiveLine_goldfeldPositiveLineKernelSchwartz
    (alpha : ℝ) : 𝓢(ℝ, ℂ) :=
  (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_hasCompactSupport alpha).toSchwartzMap
    (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel_contDiff alpha)

private theorem GoldfeldMellinPositiveLine_goldfeldDerivativeMellin_on_positiveLine
    (alpha t : ℝ) :
    goldfeldDerivativeMellin ((alpha : ℂ) + t * I) =
      𝓕 (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((alpha : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((alpha : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((alpha : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((alpha : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π)) := by
      norm_num
      rw [SchwartzMap.fourier_coe]
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [GoldfeldMellinPositiveLine_goldfeldPositiveLineKernelSchwartz, GoldfeldMellinPositiveLine_goldfeldPositiveLineKernel]

theorem goldfeldRawMellin_verticalIntegrable
    {alpha : ℝ} (halpha : 0 < alpha) :
    VerticalIntegrable goldfeldRawMellin alpha := by
  let fourierLine : ℝ → ℂ := fun t =>
    𝓕 (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernelSchwartz alpha) (t / (2 * π))
  let z : ℝ → ℂ := fun t => (alpha : ℂ) + t * I
  let invFactor : ℝ → ℂ := fun t => -(z t)⁻¹
  have hfourier : Integrable fourierLine := by
    have h := (𝓕 (GoldfeldMellinPositiveLine_goldfeldPositiveLineKernelSchwartz alpha)).integrable
      |>.comp_mul_right'
        (show (2 * π : ℝ)⁻¹ ≠ 0 by positivity)
    simpa [fourierLine, div_eq_mul_inv] using h
  have hzContinuous : Continuous z := by
    fun_prop
  have hzNe (t : ℝ) : z t ≠ 0 := by
    intro ht
    have hre := congrArg Complex.re ht
    simp [z] at hre
    exact halpha.ne' hre
  have hinvContinuous : Continuous invFactor := by
    exact (hzContinuous.inv₀ hzNe).neg
  have hzNorm (t : ℝ) : alpha ≤ ‖z t‖ := by
    have h := Complex.abs_re_le_norm (z t)
    simpa [z, abs_of_pos halpha] using h
  have hinvBound : ∀ᵐ t : ℝ, ‖invFactor t‖ ≤ alpha⁻¹ :=
    ae_of_all _ fun t => by
      change ‖-(z t)⁻¹‖ ≤ alpha⁻¹
      rw [norm_neg, norm_inv]
      exact (inv_le_inv₀ (halpha.trans_le (hzNorm t)) halpha).2 (hzNorm t)
  have hproduct : Integrable fun t => fourierLine t * invFactor t :=
    hfourier.mul_bdd hinvContinuous.aestronglyMeasurable hinvBound
  rw [VerticalIntegrable]
  refine hproduct.congr (ae_of_all _ fun t => ?_)
  have hraw : goldfeldRawMellin (z t) = fourierLine t * invFactor t := by
    rw [← goldfeldMellinCandidate_eq_raw (by simp [z, halpha])]
    rw [goldfeldMellinCandidate,
      GoldfeldMellinPositiveLine_goldfeldDerivativeMellin_on_positiveLine alpha t]
    simp only [fourierLine, invFactor, div_eq_mul_inv]
    ring
  simpa [z] using hraw.symm

end BoundedGaps.Maynard

end

/-! ## Goldfeld's smoothed four-factor sum

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldSmoothedSum`. -/

noncomputable section

open Complex MeasureTheory

namespace BoundedGaps.Maynard

private instance GoldfeldSmoothedSum_goldfeldSmoothedLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

noncomputable def goldfeldFourFactorLFunction
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  riemannZeta s * DirichletCharacter.LFunction chi1 s *
    DirichletCharacter.LFunction chi s *
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) s

noncomputable def goldfeldBetaCoefficient
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (goldfeldCoefficient chi1 chi) (beta : ℂ) n

private theorem GoldfeldSmoothedSum_goldfeldBetaCoefficient_term
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (goldfeldBetaCoefficient chi1 chi beta) s n =
      LSeries.term (goldfeldCoefficient chi1 chi)
        (s + (beta : ℂ)) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [goldfeldBetaCoefficient, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
    field_simp

theorem goldfeldBetaCoefficient_LSeriesHasSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) {s : ℂ}
    (hs : 1 < (s + (beta : ℂ)).re) :
    LSeriesHasSum (goldfeldBetaCoefficient chi1 chi beta) s
      (goldfeldFourFactorLFunction chi1 chi (s + (beta : ℂ))) := by
  have h := goldfeldCoefficient_LSeriesHasSum chi1 chi hs
  change HasSum (LSeries.term (goldfeldBetaCoefficient chi1 chi beta) s) _
  simpa [goldfeldFourFactorLFunction] using
    h.congr_fun (GoldfeldSmoothedSum_goldfeldBetaCoefficient_term chi1 chi beta s)

noncomputable def goldfeldSmoothedSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) : ℂ :=
  ∑' n : ℕ,
    goldfeldBetaCoefficient chi1 chi beta n *
      (goldfeldPlateau ((n : ℝ) / x) : ℂ)

noncomputable def goldfeldContourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  goldfeldFourFactorLFunction chi1 chi (s + (beta : ℂ)) *
    goldfeldMellinContinuationData.Phi s * (x : ℂ) ^ s

noncomputable def goldfeldVerticalIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t : ℝ,
      goldfeldContourIntegrand chi1 chi beta x
        ((alpha : ℂ) + t * I)

theorem goldfeldSmoothedSum_eq_verticalIntegral_two
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 1 ≤ x) :
    goldfeldSmoothedSum chi1 chi beta x =
      goldfeldVerticalIntegral chi1 chi beta x 2 := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsum : LSeriesSummable
      (goldfeldBetaCoefficient chi1 chi beta) (2 : ℂ) := by
    apply (goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := (2 : ℂ)) ?_).LSeriesSummable
    norm_num
    linarith
  have hinversion := smoothMellinLSeriesInversion
    (goldfeldBetaCoefficient chi1 chi beta) (by simp [goldfeldBetaCoefficient])
    (fun y : ℝ => (goldfeldPlateau y : ℂ))
    (alpha := 2) (x := x) (by norm_num) hxpos hsum
    (goldfeldRawMellin_convergent (by norm_num))
    (goldfeldRawMellin_verticalIntegrable (by norm_num))
    (Complex.continuous_ofReal.comp goldfeldPlateau_contDiff.continuous)
  rw [goldfeldSmoothedSum, goldfeldVerticalIntegral]
  calc
    (∑' n : ℕ,
        goldfeldBetaCoefficient chi1 chi beta n *
          (goldfeldPlateau ((n : ℝ) / x) : ℂ)) =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t : ℝ,
            LSeries (goldfeldBetaCoefficient chi1 chi beta)
                ((2 : ℂ) + t * I) *
              goldfeldRawMellin ((2 : ℂ) + t * I) *
              (x : ℂ) ^ ((2 : ℂ) + t * I) := hinversion
    _ = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
          ∫ t : ℝ,
            goldfeldContourIntegrand chi1 chi beta x
              ((2 : ℂ) + t * I) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      have hs : 1 < (((2 : ℂ) + t * I) + (beta : ℂ)).re := by
        norm_num
        linarith
      have hseries := (goldfeldBetaCoefficient_LSeriesHasSum
        chi1 chi beta (s := (2 : ℂ) + t * I) hs).LSeries_eq
      have hphi := goldfeldMellinContinuationData.agrees_on_right
        (s := (2 : ℂ) + t * I) (by norm_num)
      rw [hseries, ← hphi]
      rfl

end BoundedGaps.Maynard

end

/-! ## An Abel representation for regularized zeta

Source module `BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaAbel`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Asymptotics Complex Filter MeasureTheory Set

open scoped Topology

private noncomputable def RiemannZetaAbel_zetaFractionalTail (u : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun x : ℝ => ((Int.fract x : ℝ) : ℂ)) u

private noncomputable def RiemannZetaAbel_zetaFractionalMellin (s : ℂ) : ℂ :=
  mellin RiemannZetaAbel_zetaFractionalTail (-s)

private lemma RiemannZetaAbel_measurable_zetaFractionalTail :
    Measurable RiemannZetaAbel_zetaFractionalTail := by
  exact (Complex.continuous_ofReal.measurable.comp measurable_fract).indicator
    measurableSet_Ioi

private lemma RiemannZetaAbel_norm_zetaFractionalTail_le_one (u : ℝ) :
    ‖RiemannZetaAbel_zetaFractionalTail u‖ ≤ 1 := by
  by_cases hu : 1 < u
  · simpa [RiemannZetaAbel_zetaFractionalTail, hu, Complex.norm_real, Real.norm_eq_abs,
      Int.abs_fract] using
      (Int.fract_lt_one u).le
  · simp [RiemannZetaAbel_zetaFractionalTail, hu]

private lemma RiemannZetaAbel_locallyIntegrable_zetaFractionalTail :
    LocallyIntegrable RiemannZetaAbel_zetaFractionalTail := by
  refine (locallyIntegrable_const (1 : ℂ)).mono
    RiemannZetaAbel_measurable_zetaFractionalTail.aestronglyMeasurable ?_
  filter_upwards with u
  simpa using RiemannZetaAbel_norm_zetaFractionalTail_le_one u

private lemma RiemannZetaAbel_zetaFractionalTail_isBigO_atTop :
    RiemannZetaAbel_zetaFractionalTail =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun u => ?_⟩
  simpa using RiemannZetaAbel_norm_zetaFractionalTail_le_one u

private lemma RiemannZetaAbel_zetaFractionalTail_isBigO_nhdsGT_zero (b : ℝ) :
    RiemannZetaAbel_zetaFractionalTail =O[𝓝[>] 0] (fun u : ℝ => u ^ (-b)) := by
  have hsmall : ∀ᶠ u : ℝ in 𝓝[>] 0, u < 1 :=
    Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hsmall] with u hu
  simp [RiemannZetaAbel_zetaFractionalTail, not_lt.mpr hu.le]

private lemma RiemannZetaAbel_mellinConvergent_zetaFractionalTail
    {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent RiemannZetaAbel_zetaFractionalTail (-s) := by
  refine mellinConvergent_of_isBigO_rpow
    (a := 0) (b := (-s).re - 1)
    (RiemannZetaAbel_locallyIntegrable_zetaFractionalTail.locallyIntegrableOn (Ioi 0))
    (by simpa using RiemannZetaAbel_zetaFractionalTail_isBigO_atTop) ?_
    (RiemannZetaAbel_zetaFractionalTail_isBigO_nhdsGT_zero ((-s).re - 1)) ?_
  · simpa using hs
  · linarith

private lemma RiemannZetaAbel_differentiableAt_zetaFractionalMellin
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ RiemannZetaAbel_zetaFractionalMellin s := by
  have hMellin : DifferentiableAt ℂ (mellin RiemannZetaAbel_zetaFractionalTail) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (RiemannZetaAbel_locallyIntegrable_zetaFractionalTail.locallyIntegrableOn (Ioi 0))
      (by simpa using RiemannZetaAbel_zetaFractionalTail_isBigO_atTop) ?_
      (RiemannZetaAbel_zetaFractionalTail_isBigO_nhdsGT_zero ((-s).re - 1)) ?_
    · simpa using hs
    · linarith
  exact hMellin.comp s differentiableAt_id.neg

private lemma RiemannZetaAbel_zetaFractionalMellin_eq_integral (s : ℂ) :
    RiemannZetaAbel_zetaFractionalMellin s =
      ∫ u in Ioi (1 : ℝ),
        (((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))) := by
  rw [RiemannZetaAbel_zetaFractionalMellin, mellin]
  simp only [smul_eq_mul]
  calc
    (∫ u : ℝ in Ioi 0,
        (u : ℂ) ^ (-s - 1) * RiemannZetaAbel_zetaFractionalTail u) =
        ∫ u : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun x : ℝ =>
            (x : ℂ) ^ (-s - 1) * ((Int.fract x : ℝ) : ℂ)) u := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      by_cases hu : 1 < u <;> simp [RiemannZetaAbel_zetaFractionalTail, hu]
    _ = ∫ u : ℝ in Ioi (0 : ℝ) ∩ Ioi 1,
        (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ u : ℝ in Ioi 1,
        (u : ℂ) ^ (-s - 1) * ((Int.fract u : ℝ) : ℂ) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ u : ℝ in Ioi 1,
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma RiemannZetaAbel_norm_zetaFractionalMellin_le
    {s : ℂ} (hs : 0 < s.re) :
    ‖RiemannZetaAbel_zetaFractionalMellin s‖ ≤ 1 / s.re := by
  rw [RiemannZetaAbel_zetaFractionalMellin_eq_integral]
  have hmajorant : IntegrableOn
      (fun u : ℝ => u ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hconvergent := RiemannZetaAbel_mellinConvergent_zetaFractionalTail hs
  rw [MellinConvergent] at hconvergent
  have hrestricted :=
    hconvergent.mono_set (Ioi_subset_Ioi zero_le_one)
  have hintegrable : IntegrableOn
      (fun u : ℝ =>
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
    refine hrestricted.congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul]
    rw [RiemannZetaAbel_zetaFractionalTail, indicator_of_mem hu, mul_comm]
    congr 1
    ring_nf
  have hbound : ∀ᵐ (u : ℝ) ∂volume.restrict (Ioi 1),
      ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ ≤
        u ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hu)]
    simp only [neg_re, add_re, one_re, Complex.norm_real, Real.norm_eq_abs,
      Int.abs_fract]
    exact mul_le_of_le_one_left
      (Real.rpow_nonneg (zero_lt_one.trans hu).le _)
      (Int.fract_lt_one u).le
  calc
    ‖∫ u : ℝ in Ioi 1,
        ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ ≤
        ∫ u : ℝ in Ioi 1,
          ‖((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ in Ioi 1, u ^ (-(s.re + 1)) :=
      setIntegral_mono_ae_restrict hintegrable.norm hmajorant hbound
    _ = 1 / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      field_simp [hs.ne']
      ring

private lemma RiemannZetaAbel_unit_partialSums_isBigO :
    (fun n : ℕ => ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  simpa [Nat.card_Icc] using
    (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)

private lemma RiemannZetaAbel_riemannZeta_eq_pole_sub_mellin
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s / (s - 1) - s * RiemannZetaAbel_zetaFractionalMellin s := by
  have hseries :
      riemannZeta s =
        s * ∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by
    have h := LSeries_eq_mul_integral_of_nonneg
      (fun _ : ℕ => (1 : ℝ)) (r := 1) zero_le_one hs
      RiemannZetaAbel_unit_partialSums_isBigO (fun _ => zero_le_one)
    calc
      riemannZeta s = LSeries (1 : ℕ → ℂ) s :=
        (LSeries_one_eq_riemannZeta hs).symm
      _ = LSeries (fun _ : ℕ => ((1 : ℝ) : ℂ)) s := by
        apply LSeries_congr
        simp
      _ = s * ∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by simpa using h
  have hfloor :
      (∫ u : ℝ in Ioi 1,
          (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (1 : ℂ)) *
            (u : ℂ) ^ (-(s + 1))) =
        ∫ u : ℝ in Ioi 1,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
            (u : ℂ) ^ (-(s + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : 0 ≤ u := (zero_lt_one.trans hu).le
    have hfloorReal : (⌊u⌋₊ : ℝ) = u - Int.fract u := by
      rw [natCast_floor_eq_intCast_floor hu0]
      linarith [Int.floor_add_fract u]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
      Nat.add_sub_cancel, mul_one]
    rw [← Complex.ofReal_natCast, hfloorReal, Complex.ofReal_sub]
  rw [hfloor] at hseries
  have hpure : IntegrableOn
      (fun u : ℝ => (u : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one
  have hfrac : IntegrableOn
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) *
        (u : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    have hconv := RiemannZetaAbel_mellinConvergent_zetaFractionalTail (zero_lt_one.trans hs)
    rw [MellinConvergent] at hconv
    have hrestrict := hconv.mono_set (Ioi_subset_Ioi zero_le_one)
    refine hrestrict.congr_fun ?_ measurableSet_Ioi
    intro u hu
    simp only [smul_eq_mul]
    rw [RiemannZetaAbel_zetaFractionalTail, indicator_of_mem hu, mul_comm]
    congr 1
    ring_nf
  have hpoint : ∀ u ∈ Ioi (1 : ℝ),
      ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
          (u : ℂ) ^ (-(s + 1)) =
        (u : ℂ) ^ (-s) -
          ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(s + 1)) := by
    intro u hu
    rw [sub_mul]
    congr 2
    have hu0 : (u : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hu).ne'
    calc
      (u : ℂ) * (u : ℂ) ^ (-(s + 1)) =
          (u : ℂ) ^ 1 * (u : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
      _ = (u : ℂ) ^ (1 + -(s + 1)) := (cpow_add _ _ hu0).symm
      _ = (u : ℂ) ^ (-s) := by congr 1; ring
  have hintegral :
      (∫ u : ℝ in Ioi 1,
          ((u : ℂ) - ((Int.fract u : ℝ) : ℂ)) *
            (u : ℂ) ^ (-(s + 1))) =
        (∫ u : ℝ in Ioi 1, (u : ℂ) ^ (-s)) -
          ∫ u : ℝ in Ioi 1,
            ((Int.fract u : ℝ) : ℂ) *
              (u : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hpure hfrac]
    exact setIntegral_congr_fun measurableSet_Ioi hpoint
  rw [hintegral,
    integral_Ioi_cpow_of_lt (by simpa using hs) zero_lt_one,
    Complex.ofReal_one, one_cpow, ← RiemannZetaAbel_zetaFractionalMellin_eq_integral] at hseries
  have hpole : -1 / (-s + 1) = 1 / (s - 1) := by
    rw [show -s + 1 = -(s - 1) by ring, div_neg]
    ring
  calc
    riemannZeta s = s * (-1 / (-s + 1) - RiemannZetaAbel_zetaFractionalMellin s) := hseries
    _ = s / (s - 1) - s * RiemannZetaAbel_zetaFractionalMellin s := by
      rw [hpole]
      ring

theorem riemannZeta₁_eq_abelIntegral
    (s : ℂ) (hs : 0 < s.re) :
    riemannZeta₁ s =
      s - s * (s - 1) *
        ∫ u in Set.Ioi (1 : ℝ),
          (((Int.fract u : ℝ) : ℂ) *
            (u : ℂ) ^ (-(s + 1))) := by
  let U : Set ℂ := {z | 0 < z.re}
  let rhs : ℂ → ℂ := fun z =>
    z - z * (z - 1) * RiemannZetaAbel_zetaFractionalMellin z
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hleft : AnalyticOnNhd ℂ riemannZeta₁ U :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd hUopen
  have hright : AnalyticOnNhd ℂ rhs U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact (differentiableAt_id.sub
      ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
        (RiemannZetaAbel_differentiableAt_zetaFractionalMellin hz))).differentiableWithinAt
  have heq : Set.EqOn riemannZeta₁ rhs U := by
    refine hleft.eqOn_of_preconnected_of_eventuallyEq hright
      (convex_halfSpace_re_gt 0).isPreconnected
      (show (2 : ℂ) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hz
    have hfactor : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1]
      field_simp
    rw [hfactor, RiemannZetaAbel_riemannZeta_eq_pole_sub_mellin hz]
    dsimp [rhs]
    field_simp
  rw [heq hs]
  dsimp [rhs]
  rw [RiemannZetaAbel_zetaFractionalMellin_eq_integral]

theorem norm_riemannZeta₁_le_abel
    (s : ℂ) (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤
      ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by
  rw [riemannZeta₁_eq_abelIntegral s hs,
    ← RiemannZetaAbel_zetaFractionalMellin_eq_integral]
  calc
    ‖s - s * (s - 1) * RiemannZetaAbel_zetaFractionalMellin s‖ ≤
        ‖s‖ + ‖s * (s - 1) * RiemannZetaAbel_zetaFractionalMellin s‖ := norm_sub_le _ _
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ * ‖RiemannZetaAbel_zetaFractionalMellin s‖ := by
      rw [norm_mul, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * ‖s - 1‖ * (1 / s.re) := by
      gcongr
      exact RiemannZetaAbel_norm_zetaFractionalMellin_le hs
    _ = ‖s‖ + ‖s‖ * ‖s - 1‖ / s.re := by ring

end BoundedGaps.Maynard

end

/-! ## Regularized zeta growth on radius-four spheres

Source module `BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaRadiusFour`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Metric Set

private lemma RiemannZetaRadiusFour_even_one_mod_one :
    (1 : DirichletCharacter ℂ 1).Even := by
  rw [DirichletCharacter.Even]
  exact map_one _

theorem riemannZeta₁_eq_reflection_of_re_le
    (s : ℂ) (hs0 : s ≠ 0) (hs : s.re ≤ (1 / 2 : ℝ)) :
    riemannZeta₁ s =
      (1 - s) / s * riemannZeta₁ (1 - s) *
        (DirichletCharacter.gammaFactor
            (1 : DirichletCharacter ℂ 1) (1 - s) /
          DirichletCharacter.gammaFactor
            (1 : DirichletCharacter ℂ 1) s) := by
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  have hreflect0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  have hGammaReflect : Gammaℝ (1 - s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hGammaR :
      riemannZeta₁ s =
        (1 - s) / s * riemannZeta₁ (1 - s) *
          (Gammaℝ (1 - s) / Gammaℝ s) := by
    by_cases hGamma : Gammaℝ s = 0
    · obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hGamma
      have hn0 : n ≠ 0 := by
        intro hn0
        subst n
        simp at hn
        exact hs0 hn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      have hzeta : riemannZeta (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using
          riemannZeta_neg_two_mul_nat_add_one k
      have harg1 : -(2 * ((k + 1 : ℕ) : ℂ)) ≠ 1 := by
        intro h
        have hreal := congrArg Complex.re h
        norm_num at hreal
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hsub : -(2 * ((k + 1 : ℕ) : ℂ)) - 1 ≠ 0 :=
        sub_ne_zero.mpr harg1
      have hfactor := riemannZeta_eq_inv_sub_mul harg1
      rw [hzeta] at hfactor
      have hinv : (-(2 * ((k + 1 : ℕ) : ℂ)) - 1)⁻¹ ≠ 0 :=
        inv_ne_zero hsub
      have hzeta1 : riemannZeta₁ (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 :=
        (mul_eq_zero.mp hfactor.symm).resolve_left hinv
      have hden : Gammaℝ (-(2 * ((k + 1 : ℕ) : ℂ))) = 0 := by
        simpa [hn] using hGamma
      rw [hn, hzeta1, hden]
      simp
    · have hreflected :
          completedRiemannZeta (1 - s) =
            riemannZeta (1 - s) * Gammaℝ (1 - s) := by
        symm
        exact (eq_div_iff hGammaReflect).mp
          (riemannZeta_def_of_ne_zero hreflect0)
      have hzeta :
          riemannZeta s =
            riemannZeta (1 - s) * Gammaℝ (1 - s) / Gammaℝ s := by
        rw [riemannZeta_def_of_ne_zero hs0,
          ← completedRiemannZeta_one_sub s, hreflected]
      have hreg : riemannZeta₁ s = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul hs1]
        field_simp
      have hreflect1 : 1 - s ≠ 1 := by
        intro h
        apply hs0
        linear_combination -h
      have hregReflect :
          riemannZeta₁ (1 - s) =
            ((1 - s) - 1) * riemannZeta (1 - s) := by
        rw [riemannZeta_eq_inv_sub_mul hreflect1]
        field_simp
      rw [hreg, hzeta, hregReflect]
      field_simp [hs0, hGamma]
      ring
  rw [RiemannZetaRadiusFour_even_one_mod_one.gammaFactor_def, RiemannZetaRadiusFour_even_one_mod_one.gammaFactor_def]
  exact hGammaR

private lemma RiemannZetaRadiusFour_radiusFourSphere_geometry
    (t : ℝ) (z : ℂ)
    (hz : z ∈ sphere ((2 : ℂ) + t * I) 4) :
    -(2 : ℝ) ≤ z.re ∧ z.re ≤ 6 ∧
      |z.im| + 2 ≤ 3 * (|t| + 2) ∧
        ‖z‖ ≤ 3 * (|t| + 2) := by
  have hdist : ‖z - ((2 : ℂ) + t * I)‖ = 4 := by
    simpa [mem_sphere, Complex.dist_eq] using hz
  have hre : |z.re - 2| ≤ 4 := by
    calc
      |z.re - 2| = |(z - ((2 : ℂ) + t * I)).re| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_re_le_norm _
      _ = 4 := hdist
  have him : |z.im - t| ≤ 4 := by
    calc
      |z.im - t| = |(z - ((2 : ℂ) + t * I)).im| := by simp
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ := Complex.abs_im_le_norm _
      _ = 4 := hdist
  have hzIm : |z.im| ≤ |t| + 4 := by
    calc
      |z.im| = |(z.im - t) + t| := by rw [sub_add_cancel]
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ 4 + |t| := by linarith
      _ = |t| + 4 := by ring
  have hcenter : ‖(2 : ℂ) + t * I‖ ≤ 2 + |t| := by
    calc
      ‖(2 : ℂ) + t * I‖ ≤ ‖(2 : ℂ)‖ + ‖t * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp [Real.norm_eq_abs]
  have hnorm : ‖z‖ ≤ |t| + 6 := by
    calc
      ‖z‖ = ‖(z - ((2 : ℂ) + t * I)) + ((2 : ℂ) + t * I)‖ := by ring_nf
      _ ≤ ‖z - ((2 : ℂ) + t * I)‖ + ‖(2 : ℂ) + t * I‖ :=
        norm_add_le _ _
      _ ≤ 4 + (2 + |t|) := add_le_add (le_of_eq hdist) hcenter
      _ = |t| + 6 := by ring
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · rw [abs_le] at hre
    linarith
  constructor
  · linarith [abs_nonneg t]
  · linarith [abs_nonneg t]

private lemma RiemannZetaRadiusFour_exists_pos_norm_riemannZeta₁_closedBall_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖riemannZeta₁ z‖ ≤ C := by
  have hball : IsCompact (closedBall (0 : ℂ) 1) :=
    isCompact_closedBall (0 : ℂ) 1
  obtain ⟨C, hC⟩ := hball.exists_bound_of_continuousOn
    differentiable_riemannZeta₁.continuous.continuousOn
  refine ⟨max C 0 + 1, by linarith [le_max_right C 0], ?_⟩
  intro z hz
  exact (hC z hz).trans (by linarith [le_max_left C 0])

private lemma RiemannZetaRadiusFour_natCast_le_two_pow (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      have hone : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      nlinarith

theorem exists_nat_norm_riemannZeta₁_radiusFourSphere_le :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ (t : ℝ) (z : ℂ),
        z ∈ sphere ((2 : ℂ) + t * I) 4 →
          ‖riemannZeta₁ z‖ ≤ (|t| + 2) ^ E := by
  obtain ⟨Ccompact, hCcompact, hcompact⟩ :=
    RiemannZetaRadiusFour_exists_pos_norm_riemannZeta₁_closedBall_one_le
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    exists_norm_gammaFactor_ratio_fixedStrip_le
  let K : ℝ := max Ccompact (4 * Cgamma * 3 ^ 11)
  obtain ⟨n : ℕ, hn⟩ := exists_nat_ge K
  refine ⟨n + 19, by omega, ?_⟩
  intro t z hz
  obtain ⟨hzlo, hzhi, hzheight, hznorm⟩ :=
    RiemannZetaRadiusFour_radiusFourSphere_geometry t z hz
  let T : ℝ := |t| + 2
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ T := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hzsub : ‖z - 1‖ ≤ 4 * T := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * T + 1 := add_le_add (by simpa [T] using hznorm) (by norm_num)
      _ ≤ 4 * T := by linarith
  have hKpow : K ≤ T ^ n := by
    calc
      K ≤ (n : ℝ) := hn
      _ ≤ 2 ^ n := RiemannZetaRadiusFour_natCast_le_two_pow n
      _ ≤ T ^ n := pow_le_pow_left₀ (by norm_num) hT2 n
  by_cases hright : (1 / 2 : ℝ) ≤ z.re
  · have habel := norm_riemannZeta₁_le_abel z (by linarith)
    have hrightBound : ‖riemannZeta₁ z‖ ≤ T ^ 7 := by
      calc
        ‖riemannZeta₁ z‖ ≤ ‖z‖ + ‖z‖ * ‖z - 1‖ / z.re := habel
        _ ≤ 3 * T + (3 * T) * (4 * T) / (1 / 2 : ℝ) := by
          gcongr
        _ = 3 * T + 24 * T ^ 2 := by ring
        _ ≤ T ^ 7 := by
          have hT5 : (32 : ℝ) ≤ T ^ 5 := by
            have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 5
            norm_num at h
            exact h
          have hT7 : 32 * T ^ 2 ≤ T ^ 7 := by
            calc
              32 * T ^ 2 ≤ T ^ 5 * T ^ 2 :=
                mul_le_mul_of_nonneg_right hT5 (sq_nonneg T)
              _ = T ^ 7 := by ring
          nlinarith [sq_nonneg T]
    exact hrightBound.trans (pow_le_pow_right₀ hT1 (by omega))
  · have hzleft : z.re ≤ (1 / 2 : ℝ) := le_of_not_ge hright
    by_cases hzsmall : ‖z‖ ≤ 1
    · have hzball : z ∈ closedBall (0 : ℂ) 1 := by
        simpa [mem_closedBall, dist_zero_right] using hzsmall
      have hC : Ccompact ≤ K := le_max_left _ _
      calc
        ‖riemannZeta₁ z‖ ≤ Ccompact := hcompact z hzball
        _ ≤ K := hC
        _ ≤ T ^ n := hKpow
        _ ≤ T ^ (n + 19) := pow_le_pow_right₀ hT1 (by omega)
    · have hz0 : z ≠ 0 := by
        intro h
        subst z
        simp at hzsmall
      have hreflect := riemannZeta₁_eq_reflection_of_re_le z hz0 hzleft
      have hreflectRe : (1 / 2 : ℝ) ≤ (1 - z).re := by simp; linarith
      have hreflectNorm : ‖1 - z‖ ≤ 4 * T := by
        calc
          ‖1 - z‖ = ‖z - 1‖ := by
            rw [show 1 - z = -(z - 1) by ring, norm_neg]
          _ ≤ 4 * T := hzsub
      have hreflectSub : ‖(1 - z) - 1‖ ≤ 3 * T := by
        simpa only [sub_sub_cancel_left, norm_neg] using
          (show ‖z‖ ≤ 3 * T by simpa [T] using hznorm)
      have hreflectAbel := norm_riemannZeta₁_le_abel (1 - z) (by linarith)
      have hreflectBound : ‖riemannZeta₁ (1 - z)‖ ≤ T ^ 7 := by
        calc
          ‖riemannZeta₁ (1 - z)‖ ≤
              ‖1 - z‖ + ‖1 - z‖ * ‖(1 - z) - 1‖ / (1 - z).re :=
            hreflectAbel
          _ ≤ 4 * T + (4 * T) * (3 * T) / (1 / 2 : ℝ) := by
            gcongr
          _ = 4 * T + 24 * T ^ 2 := by ring
          _ ≤ T ^ 7 := by
            have hT5 : (32 : ℝ) ≤ T ^ 5 := by
              have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hT2 5
              norm_num at h
              exact h
            have hT7 : 32 * T ^ 2 ≤ T ^ 7 := by
              calc
                32 * T ^ 2 ≤ T ^ 5 * T ^ 2 :=
                  mul_le_mul_of_nonneg_right hT5 (sq_nonneg T)
                _ = T ^ 7 := by ring
            nlinarith [sq_nonneg T]
      have hratio : ‖(1 - z) / z‖ ≤ 4 * T := by
        rw [norm_div]
        have hzOne : (1 : ℝ) ≤ ‖z‖ := le_of_not_ge hzsmall
        exact (div_le_iff₀ (norm_pos_iff.mpr hz0)).2 (by
          calc
            ‖1 - z‖ ≤ 4 * T := hreflectNorm
            _ ≤ 4 * T * ‖z‖ := by
              exact le_mul_of_one_le_right (by positivity) hzOne)
      have hgamma' := hgamma 1 (1 : DirichletCharacter ℂ 1) z
        (by linarith) hzleft
      have hgammaBound :
          ‖DirichletCharacter.gammaFactor
                (1 : DirichletCharacter ℂ 1)⁻¹ (1 - z) /
              DirichletCharacter.gammaFactor
                (1 : DirichletCharacter ℂ 1) z‖ ≤
            Cgamma * (3 * T) ^ 11 := by
        exact hgamma'.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by simpa [T] using hzheight) 11)
          hCgamma.le)
      have hinvOne : (1 : DirichletCharacter ℂ 1)⁻¹ = 1 := inv_one
      rw [hinvOne] at hgammaBound
      rw [hreflect, norm_mul, norm_mul]
      calc
        ‖(1 - z) / z‖ * ‖riemannZeta₁ (1 - z)‖ *
              ‖DirichletCharacter.gammaFactor
                  (1 : DirichletCharacter ℂ 1) (1 - z) /
                DirichletCharacter.gammaFactor
                  (1 : DirichletCharacter ℂ 1) z‖ ≤
            (4 * T) * T ^ 7 * (Cgamma * (3 * T) ^ 11) := by
          gcongr
        _ = (4 * Cgamma * 3 ^ 11) * T ^ 19 := by ring
        _ ≤ K * T ^ 19 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hT0 19)
        _ ≤ T ^ n * T ^ 19 :=
          mul_le_mul_of_nonneg_right hKpow (pow_nonneg hT0 19)
        _ = T ^ (n + 19) := by rw [pow_add]

end BoundedGaps.Maynard

end

/-! ## Riemann zeta on the Goldfeld strip

Source module `BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaClosedStripGrowth`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Metric Set

theorem exists_norm_riemannZeta₁_closedStrip_le_pow :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ z : ℂ, -(1 : ℝ) ≤ z.re → z.re ≤ 3 →
        ‖riemannZeta₁ z‖ ≤ (|z.im| + 2) ^ E := by
  obtain ⟨E, hE, hsphere⟩ :=
    exists_nat_norm_riemannZeta₁_radiusFourSphere_le
  refine ⟨E, hE, ?_⟩
  intro z hzlo hzhi
  let c : ℂ := (2 : ℂ) + z.im * I
  have hzmem : z ∈ closedBall c 4 := by
    rw [mem_closedBall, Complex.dist_eq]
    have heq : z - c = ((z.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [heq, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := ball c 4) Metric.isBounded_ball
    differentiable_riemannZeta₁.diffContOnCl
    (C := (|z.im| + 2) ^ E)
  · intro w hw
    rw [frontier_ball c (by norm_num)] at hw
    exact hsphere z.im w (by simpa [c] using hw)
  · rw [closure_ball c (by norm_num)]
    exact hzmem

theorem exists_norm_riemannZeta_closedStrip_le_pow :
    ∃ E : ℕ, 1 ≤ E ∧
      ∀ z : ℂ, -(1 : ℝ) ≤ z.re → z.re ≤ 3 → 1 ≤ |z.im| →
        ‖riemannZeta z‖ ≤ (|z.im| + 2) ^ E := by
  obtain ⟨E, hE, hzetaOne⟩ :=
    exists_norm_riemannZeta₁_closedStrip_le_pow
  refine ⟨E, hE, ?_⟩
  intro z hzlo hzhi hzim
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzim
  have hsub : (1 : ℝ) ≤ ‖z - 1‖ := by
    have him := Complex.abs_im_le_norm (z - 1)
    simp only [sub_im, one_im, sub_zero] at him
    exact hzim.trans him
  have hinv : ‖(z - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hz1)) |>.2 hsub
  rw [riemannZeta_eq_inv_sub_mul hz1, norm_mul]
  calc
    ‖(z - 1)⁻¹‖ * ‖riemannZeta₁ z‖ ≤ 1 * ‖riemannZeta₁ z‖ :=
      mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
    _ ≤ (|z.im| + 2) ^ E := by simpa using hzetaOne z hzlo hzhi

end BoundedGaps.Maynard

end

/-! ## Goldfeld's four-factor function on the contour strip

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldFourFactorClosedStrip`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private instance GoldfeldFourFactorClosedStrip_goldfeldClosedStripLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

theorem exists_norm_goldfeldFourFactorLFunction_closedStrip_le_pow :
    ∃ A : ℕ, 57 ≤ A ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta : ℝ) (s : ℂ),
            0 ≤ beta → beta ≤ 1 →
            -(1 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
            ‖goldfeldFourFactorLFunction chi1 chi
                (s + (beta : ℂ))‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨L, hLexp, hL⟩ := exists_norm_LFunction_closedStrip_le_pow
  obtain ⟨E, hEexp, hZeta⟩ := exists_norm_riemannZeta_closedStrip_le_pow
  refine ⟨E + 4 * L, by omega, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross beta s
    hbeta0 hbeta1 hslo hshi hheight
  have hq : 1 < q := hq1.trans_le hq1q
  let w : ℂ := s + (beta : ℂ)
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hwre : w.re = s.re + beta := by simp [w]
  have hwim : w.im = s.im := by simp [w]
  have hwlo : -(1 : ℝ) ≤ w.re := by rw [hwre]; linarith
  have hwhi : w.re ≤ 3 := by rw [hwre]; linarith
  have hwheight : 1 ≤ |w.im| := by simpa [hwim] using hheight
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1r : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1r
  have hT3 : (3 : ℝ) ≤ T := by
    dsimp [T]
    linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hZetaBound : ‖riemannZeta w‖ ≤ B ^ E := by
    have hz := hZeta w hwlo hwhi hwheight
    have hTB : T ≤ B := by
      dsimp [B]
      nlinarith
    exact hz.trans (by
      simpa [T, hwim] using pow_le_pow_left₀ hT0 hTB E)
  have hchi1Bound :
      ‖DirichletCharacter.LFunction chi1 w‖ ≤ B ^ L := by
    have h := hL q1 hq1 chi1 hchi1 w hwlo hwhi
    have hbase : (q1 : ℝ) * (|w.im| + 2) ≤ B := by
      dsimp [B, T]
      rw [hwim]
      gcongr
    exact h.trans (pow_le_pow_left₀ (by positivity) hbase L)
  have hchiBound :
      ‖DirichletCharacter.LFunction chi w‖ ≤ B ^ L := by
    simpa [B, T, hwim] using hL q hq chi hchi w hwlo hwhi
  let m := Nat.lcm q1 q
  have hmpos : 0 < m := Nat.lcm_pos (NeZero.pos q1) (NeZero.pos q)
  letI : NeZero m := ⟨hmpos.ne'⟩
  have hqm : q ≤ m := Nat.le_of_dvd hmpos (Nat.dvd_lcm_right q1 q)
  have hm1 : 1 < m := hq.trans_le hqm
  have hmqq : m ≤ q1 * q :=
    Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
      (Nat.lcm_dvd_mul q1 q)
  have hmqqReal : (m : ℝ) ≤ (q : ℝ) ^ 2 := by
    calc
      (m : ℝ) ≤ ((q1 * q : ℕ) : ℝ) := by exact_mod_cast hmqq
      _ = (q1 : ℝ) * (q : ℝ) := by norm_num
      _ ≤ (q : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hq1qReal hq0
      _ = (q : ℝ) ^ 2 := by ring
  have hmBase : (m : ℝ) * (|w.im| + 2) ≤ B ^ 2 := by
    rw [hwim]
    dsimp [B, T]
    calc
      (m : ℝ) * (|s.im| + 2) ≤
          (q : ℝ) ^ 2 * (|s.im| + 2) :=
        mul_le_mul_of_nonneg_right hmqqReal (by positivity)
      _ ≤ (q : ℝ) ^ 2 * (|s.im| + 2) ^ 2 := by
        gcongr
        nlinarith
      _ = ((q : ℝ) * (|s.im| + 2)) ^ 2 := by ring
  have hcrossBound :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
        B ^ (2 * L) := by
    have h := hL m hm1 (DirichletCharacter.mul chi1 chi) hcross w hwlo hwhi
    calc
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
          ((m : ℝ) * (|w.im| + 2)) ^ L := h
      _ ≤ (B ^ 2) ^ L := pow_le_pow_left₀ (by positivity) hmBase L
      _ = B ^ (2 * L) := by rw [pow_mul]
  rw [goldfeldFourFactorLFunction, norm_mul, norm_mul, norm_mul]
  calc
    ‖riemannZeta w‖ * ‖DirichletCharacter.LFunction chi1 w‖ *
          ‖DirichletCharacter.LFunction chi w‖ *
        ‖DirichletCharacter.LFunction
            (DirichletCharacter.mul chi1 chi) w‖ ≤
      B ^ E * B ^ L * B ^ L * B ^ (2 * L) := by gcongr
    _ = B ^ (E + 4 * L) := by ring

end BoundedGaps.Maynard

end

/-! ## Goldfeld bounds on the left contour line

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLeftLineBounds`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex

private instance GoldfeldLeftLineBounds_goldfeldLeftLineBoundsLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

theorem exists_norm_goldfeldFourFactorLFunction_leftLine_le_pow :
    ∃ A : ℕ, 57 ≤ A ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta t : ℝ),
            0 ≤ beta → beta ≤ 1 →
            ‖goldfeldFourFactorLFunction chi1 chi
                (((-1 : ℂ) + t * I) + (beta : ℂ))‖ ≤
              ((q : ℝ) * (|t| + 2)) ^ A := by
  obtain ⟨L, hLexp, hL⟩ := exists_norm_LFunction_closedStrip_le_pow
  obtain ⟨E, hEexp, hZetaOne⟩ :=
    exists_norm_riemannZeta₁_closedStrip_le_pow
  refine ⟨E + 4 * L, by omega, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta t hbeta0 hbeta1
  let w : ℂ := ((-1 : ℂ) + t * I) + (beta : ℂ)
  let T : ℝ := |t| + 2
  let B : ℝ := (q : ℝ) * T
  have hwre : w.re = -1 + beta := by simp [w]
  have hwim : w.im = t := by simp [w]
  have hwlo : -(1 : ℝ) ≤ w.re := by rw [hwre]; linarith
  have hwhi : w.re ≤ 3 := by rw [hwre]; linarith
  have hq : 1 < q := hq1.trans_le hq1q
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1r : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq1r
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg t]
  have hT1 : (1 : ℝ) ≤ T := one_le_two.trans hT2
  have hT0 : (0 : ℝ) ≤ T := zero_le_one.trans hT1
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hwOne : w ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hwre] at hre
    norm_num at hre
    linarith
  have hwSubNorm : (1 : ℝ) ≤ ‖w - 1‖ := by
    have hre : (w - 1).re ≤ -1 := by
      simp only [sub_re, one_re]
      rw [hwre]
      linarith
    have habs : (1 : ℝ) ≤ |(w - 1).re| := by
      rw [abs_of_nonpos (hre.trans (by norm_num))]
      linarith
    exact habs.trans (Complex.abs_re_le_norm (w - 1))
  have hZetaInv : ‖(w - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hwOne))).2 hwSubNorm
  have hZetaBound : ‖riemannZeta w‖ ≤ B ^ E := by
    have hregular := hZetaOne w hwlo hwhi
    have hTB : T ≤ B := by
      dsimp [B]
      nlinarith
    rw [riemannZeta_eq_inv_sub_mul hwOne, norm_mul]
    calc
      ‖(w - 1)⁻¹‖ * ‖riemannZeta₁ w‖ ≤
          1 * ‖riemannZeta₁ w‖ :=
        mul_le_mul_of_nonneg_right hZetaInv (norm_nonneg _)
      _ ≤ T ^ E := by simpa [T, hwim] using hregular
      _ ≤ B ^ E := pow_le_pow_left₀ hT0 hTB E
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hchi1Bound :
      ‖DirichletCharacter.LFunction chi1 w‖ ≤ B ^ L := by
    have h := hL q1 hq1 chi1 hchi1 w hwlo hwhi
    have hbase : (q1 : ℝ) * (|w.im| + 2) ≤ B := by
      dsimp [B, T]
      rw [hwim]
      gcongr
    exact h.trans (pow_le_pow_left₀ (by positivity) hbase L)
  have hchiBound :
      ‖DirichletCharacter.LFunction chi w‖ ≤ B ^ L := by
    simpa [B, T, hwim] using hL q hq chi hchi w hwlo hwhi
  let m := Nat.lcm q1 q
  have hmpos : 0 < m := Nat.lcm_pos (NeZero.pos q1) (NeZero.pos q)
  letI : NeZero m := ⟨hmpos.ne'⟩
  have hqm : q ≤ m := Nat.le_of_dvd hmpos (Nat.dvd_lcm_right q1 q)
  have hm1 : 1 < m := hq.trans_le hqm
  have hmqq : m ≤ q1 * q :=
    Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
      (Nat.lcm_dvd_mul q1 q)
  have hmqqReal : (m : ℝ) ≤ (q : ℝ) ^ 2 := by
    calc
      (m : ℝ) ≤ ((q1 * q : ℕ) : ℝ) := by exact_mod_cast hmqq
      _ = (q1 : ℝ) * (q : ℝ) := by norm_num
      _ ≤ (q : ℝ) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hq1qReal hq0
      _ = (q : ℝ) ^ 2 := by ring
  have hmBase : (m : ℝ) * (|w.im| + 2) ≤ B ^ 2 := by
    rw [hwim]
    dsimp [B, T]
    calc
      (m : ℝ) * (|t| + 2) ≤
          (q : ℝ) ^ 2 * (|t| + 2) :=
        mul_le_mul_of_nonneg_right hmqqReal (by positivity)
      _ ≤ (q : ℝ) ^ 2 * (|t| + 2) ^ 2 := by
        gcongr
        nlinarith
      _ = ((q : ℝ) * (|t| + 2)) ^ 2 := by ring
  have hcrossBound :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
        B ^ (2 * L) := by
    have h := hL m hm1 (DirichletCharacter.mul chi1 chi) hcross
      w hwlo hwhi
    calc
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) w‖ ≤
          ((m : ℝ) * (|w.im| + 2)) ^ L := h
      _ ≤ (B ^ 2) ^ L := pow_le_pow_left₀ (by positivity) hmBase L
      _ = B ^ (2 * L) := by rw [pow_mul]
  rw [goldfeldFourFactorLFunction, norm_mul, norm_mul, norm_mul]
  calc
    ‖riemannZeta w‖ * ‖DirichletCharacter.LFunction chi1 w‖ *
          ‖DirichletCharacter.LFunction chi w‖ *
        ‖DirichletCharacter.LFunction
            (DirichletCharacter.mul chi1 chi) w‖ ≤
      B ^ E * B ^ L * B ^ L * B ^ (2 * L) := by gcongr
    _ = B ^ (E + 4 * L) := by ring

private lemma GoldfeldLeftLineBounds_goldfeld_leftLine_decay_product_le
    {q u x C : ℝ} {A : ℕ}
    (hq : 0 ≤ q) (hu : 0 ≤ u) (hx : 0 < x) (hC : 0 ≤ C) :
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ ≤
      (C * (2 : ℝ) ^ A) * q ^ A /
        (x * (1 + u) ^ 2) := by
  have hbase : u + 2 ≤ 2 * (1 + u) := by linarith
  have hpow : (u + 2) ^ A ≤ (2 * (1 + u)) ^ A :=
    pow_le_pow_left₀ (by linarith) hbase A
  have hqpow : 0 ≤ q ^ A := pow_nonneg hq A
  have hprod :
      q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ ≤
        q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := by
    gcongr
  calc
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x⁻¹ =
        q ^ A * (u + 2) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := by rw [mul_pow]
    _ ≤ q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x⁻¹ := hprod
    _ = (C * (2 : ℝ) ^ A) * q ^ A /
          (x * (1 + u) ^ 2) := by
      rw [mul_pow]
      field_simp
      ring

theorem exists_norm_goldfeldContourIntegrand_leftLine_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x t : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            ‖goldfeldContourIntegrand chi1 chi beta x
                ((-1 : ℂ) + t * I)‖ ≤
              C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := by
  obtain ⟨A, hA, hF⟩ :=
    exists_norm_goldfeldFourFactorLFunction_leftLine_le_pow
  obtain ⟨Cphi, hCphi, hPhi⟩ :=
    goldfeldMellinContinuationData.decay_on_neg_one (A + 2) (by omega)
  let C : ℝ := Cphi * (2 : ℝ) ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x t hbeta0 hbeta1 hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hF' := hF q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
    beta t hbeta0 hbeta1
  have hPhi' := hPhi t
  have hxpow : ‖(x : ℂ) ^ ((-1 : ℂ) + t * I)‖ = x⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp [Real.rpow_neg_one]
  rw [goldfeldContourIntegrand, norm_mul, norm_mul, hxpow]
  calc
    ‖goldfeldFourFactorLFunction chi1 chi
          (((-1 : ℂ) + t * I) + (beta : ℂ))‖ *
        ‖goldfeldMellinContinuationData.Phi ((-1 : ℂ) + t * I)‖ * x⁻¹ ≤
      ((q : ℝ) * (|t| + 2)) ^ A *
        (Cphi / (1 + |t|) ^ (A + 2)) * x⁻¹ := by gcongr
    _ ≤ (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A /
          (x * (1 + |t|) ^ 2) :=
      GoldfeldLeftLineBounds_goldfeld_leftLine_decay_product_le hq0 (abs_nonneg t)
        hxpos hCphi.le
    _ = C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := by rfl

end BoundedGaps.Maynard

end

/-! ## Goldfeld's complete left-line integral

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLeftLineIntegral`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex MeasureTheory

private instance GoldfeldLeftLineIntegral_goldfeldLeftLineIntegralLcmNeZero
    {q1 q : ℕ} [NeZero q1] [NeZero q] : NeZero (Nat.lcm q1 q) :=
  ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩

private theorem GoldfeldLeftLineIntegral_continuous_goldfeldContourIntegrand_leftLine
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta1 : beta ≤ 1) (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      goldfeldContourIntegrand chi1 chi beta x
        ((-1 : ℂ) + t * I)) := by
  let s : ℝ → ℂ := fun t => (-1 : ℂ) + t * I
  have hs : Continuous s := by fun_prop
  have hs0 (t : ℝ) : s t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
  have hshift : Continuous (fun t : ℝ => s t + (beta : ℂ)) :=
    hs.add continuous_const
  have hshiftOne (t : ℝ) : s t + (beta : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hzeta : Continuous (fun t : ℝ =>
      riemannZeta (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hcomp :=
      (differentiableAt_riemannZeta (hshiftOne t)).continuousAt.comp
        (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
    simpa [Function.comp_def] using hcomp
  have hLchi1 : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi1).continuous.comp
      hshift
  have hLchi : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi).continuous.comp
      hshift
  have hLcross : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hcross).continuous.comp
      hshift
  have hPhi : Continuous (fun t : ℝ =>
      goldfeldMellinContinuationData.Phi (s t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (goldfeldMellinContinuationData.analytic_off_zero
        (hs0 t)).continuousAt.comp hs.continuousAt
  have hxpow : Continuous (fun t : ℝ => (x : ℂ) ^ s t) :=
    continuous_const.cpow hs fun _ => Complex.ofReal_mem_slitPlane.mpr hx
  have hproduct :=
    (((((hzeta.mul hLchi1).mul hLchi).mul hLcross).mul hPhi).mul hxpow)
  convert hproduct using 1
  ext t
  simp [s, goldfeldContourIntegrand, goldfeldFourFactorLFunction]

private lemma GoldfeldLeftLineIntegral_goldfeld_leftLine_source_envelope_le_cauchy
    {q A : ℕ} {C x t y : ℝ}
    (hC : 0 ≤ C) (hx : 0 < x)
    (hy : y ≤ C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2)) :
    y ≤ (C * (q : ℝ) ^ A / x) * (1 + t ^ 2)⁻¹ := by
  let K : ℝ := C * (q : ℝ) ^ A / x
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hden : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    nlinarith [sq_abs t, abs_nonneg t]
  have hinv : ((1 + |t|) ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hden
  calc
    y ≤ C * (q : ℝ) ^ A / (x * (1 + |t|) ^ 2) := hy
    _ = K * ((1 + |t|) ^ 2)⁻¹ := by
      dsimp [K]
      field_simp
    _ ≤ K * (1 + t ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hK

theorem goldfeldContourIntegrand_leftLine_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hx : 1 ≤ x) :
    VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) (-1) := by
  obtain ⟨A, _hA, C, hC, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_leftLine_le
  let K : ℝ := C * (q : ℝ) ^ A / x
  have hmajor : Integrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hcontinuous := GoldfeldLeftLineIntegral_continuous_goldfeldContourIntegrand_leftLine
    hchi1 hchi hcross hbeta1 (zero_lt_one.trans_le hx)
  rw [VerticalIntegrable]
  refine hmajor.mono' ?_ ?_
  · simpa using hcontinuous.aestronglyMeasurable
  · filter_upwards [] with t
    have hp := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x t hbeta0 hbeta1 hx
    have hcauchy := GoldfeldLeftLineIntegral_goldfeld_leftLine_source_envelope_le_cauchy
      hC.le (zero_lt_one.trans_le hx) hp
    simpa [K] using hcauchy

theorem exists_norm_goldfeldVerticalIntegral_neg_one_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤
              C * (q : ℝ) ^ A / x := by
  obtain ⟨A, hA, C0, hC0, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_leftLine_le
  let C : ℝ := C0 * Real.pi
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x hbeta0 hbeta1 hx
  let f : ℝ → ℂ := fun t =>
    goldfeldContourIntegrand chi1 chi beta x
      (((-1 : ℝ) : ℂ) + t * I)
  let K : ℝ := C0 * (q : ℝ) ^ A / x
  have hvertical := goldfeldContourIntegrand_leftLine_verticalIntegrable
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx
  have hraw : Integrable f := by
    simpa [VerticalIntegrable, f] using hvertical
  have hmajor : Integrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hmajorPoint : ∀ t : ℝ, ‖f t‖ ≤ K * (1 + t ^ 2)⁻¹ := by
    intro t
    have hp := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x t hbeta0 hbeta1 hx
    have hcauchy := GoldfeldLeftLineIntegral_goldfeld_leftLine_source_envelope_le_cauchy
      hC0.le (zero_lt_one.trans_le hx) hp
    simpa [f, K] using hcauchy
  have hnormIntegral : ‖∫ t : ℝ, f t‖ ≤ K * Real.pi := by
    calc
      ‖∫ t : ℝ, f t‖ ≤ ∫ t : ℝ, ‖f t‖ :=
        norm_integral_le_integral_norm f
      _ ≤ ∫ t : ℝ, K * (1 + t ^ 2)⁻¹ :=
        integral_mono_ae hraw.norm hmajor (ae_of_all _ hmajorPoint)
      _ = K * Real.pi := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq]
  have hcoefficient :
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    exact (inv_le_one₀ (by positivity : 0 < 2 * Real.pi)).2
      (by nlinarith [Real.two_le_pi])
  rw [goldfeldVerticalIntegral, norm_mul]
  calc
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ * ‖∫ t : ℝ, f t‖ ≤
        1 * (K * Real.pi) := by gcongr
    _ = C * (q : ℝ) ^ A / x := by
      dsimp [C, K]
      ring

end BoundedGaps.Maynard

end

/-! ## Goldfeld local cancellation and shifted-zeta residue

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLocalCancellation`. -/

noncomputable section

open Complex Set Filter

open scoped Topology

namespace BoundedGaps.Maynard

noncomputable def goldfeldShiftedZetaPole (beta : ℝ) : ℂ :=
  ((1 - beta : ℝ) : ℂ)

noncomputable def goldfeldShiftedLFunctionDividedSlope
    {q1 : ℕ} [NeZero q1]
    (chi1 : DirichletCharacter ℂ q1) (beta : ℝ) (s : ℂ) : ℂ :=
  dslope
    (fun z : ℂ => DirichletCharacter.LFunction chi1 (z + (beta : ℂ))) 0 s

noncomputable def goldfeldContourNumerator
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  riemannZeta₁ (s + (beta : ℂ)) *
    goldfeldShiftedLFunctionDividedSlope chi1 beta s *
    DirichletCharacter.LFunction chi (s + (beta : ℂ)) *
    DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
      (s + (beta : ℂ)) *
    (-goldfeldDerivativeMellin s) * (x : ℂ) ^ s

noncomputable def goldfeldRegularizedContourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  goldfeldContourNumerator chi1 chi beta x s /
    (s - goldfeldShiftedZetaPole beta)

noncomputable def goldfeldContourResidue
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) : ℂ :=
  (x : ℂ) ^ goldfeldShiftedZetaPole beta *
    DirichletCharacter.LFunction chi1 1 *
    DirichletCharacter.LFunction chi 1 *
    DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) 1 *
    goldfeldMellinContinuationData.Phi (goldfeldShiftedZetaPole beta)

private theorem GoldfeldLocalCancellation_goldfeldShiftedLFunctionDividedSlope_mul
    {q1 : ℕ} [NeZero q1]
    (chi1 : DirichletCharacter ℂ q1) (beta : ℝ)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (s : ℂ) :
    s * goldfeldShiftedLFunctionDividedSlope chi1 beta s =
      DirichletCharacter.LFunction chi1 (s + (beta : ℂ)) := by
  simpa [goldfeldShiftedLFunctionDividedSlope, smul_eq_mul] using
    (sub_smul_dslope_of_zero (f := fun z : ℂ =>
      DirichletCharacter.LFunction chi1 (z + (beta : ℂ)))
      (a := (0 : ℂ)) (by simpa using hzero) s)

theorem differentiable_goldfeldShiftedLFunctionDividedSlope
    {q1 : ℕ} [NeZero q1]
    {chi1 : DirichletCharacter ℂ q1} (hchi1 : chi1 ≠ 1)
    (beta : ℝ) :
    Differentiable ℂ (goldfeldShiftedLFunctionDividedSlope chi1 beta) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2
    (((DirichletCharacter.differentiable_LFunction hchi1).comp
      (differentiable_id.add_const (beta : ℂ))).differentiableOn)

theorem differentiable_goldfeldContourNumerator
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (goldfeldContourNumerator chi1 chi beta x) := by
  have hshift : Differentiable ℂ (fun s : ℂ => s + (beta : ℂ)) :=
    differentiable_id.add_const _
  have hzeta : Differentiable ℂ (fun s : ℂ =>
      riemannZeta₁ (s + (beta : ℂ))) :=
    differentiable_riemannZeta₁.comp hshift
  have hLchi : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction chi (s + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hchi).comp hshift
  have hLcross : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s + (beta : ℂ))) :=
    (DirichletCharacter.differentiable_LFunction hcross).comp hshift
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hxpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_id.const_cpow (.inl hx0)
  unfold goldfeldContourNumerator
  exact (((((hzeta.mul
    (differentiable_goldfeldShiftedLFunctionDividedSlope hchi1 beta)).mul
      hLchi).mul hLcross).mul
        differentiable_goldfeldDerivativeMellin.neg).mul hxpow)

theorem goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    {s : ℂ} (hs0 : s ≠ 0)
    (hspole : s ≠ goldfeldShiftedZetaPole beta) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x s =
      goldfeldContourIntegrand chi1 chi beta x s := by
  have hL := GoldfeldLocalCancellation_goldfeldShiftedLFunctionDividedSlope_mul chi1 beta hzero s
  have harg : s + (beta : ℂ) ≠ 1 := by
    intro h
    apply hspole
    rw [goldfeldShiftedZetaPole]
    norm_num at h ⊢
    linear_combination h
  have hshift : s + (beta : ℂ) - 1 =
      s - goldfeldShiftedZetaPole beta := by
    rw [goldfeldShiftedZetaPole]
    norm_num
    ring
  have hzeta := riemannZeta_eq_inv_sub_mul harg
  rw [hshift] at hzeta
  rw [goldfeldRegularizedContourIntegrand, goldfeldContourNumerator,
    goldfeldContourIntegrand, goldfeldFourFactorLFunction,
    hzeta, ← hL, goldfeldMellinContinuationData.equals_candidate,
    goldfeldMellinCandidate]
  field_simp [hs0, sub_ne_zero.mpr hspole]

theorem goldfeldContourNumerator_apply_shiftedZetaPole
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : beta < 1)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldContourNumerator chi1 chi beta x
        (goldfeldShiftedZetaPole beta) =
      goldfeldContourResidue chi1 chi beta x := by
  have hdelta0 : goldfeldShiftedZetaPole beta ≠ 0 := by
    rw [goldfeldShiftedZetaPole]
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hbeta.ne')
  have hshift : goldfeldShiftedZetaPole beta + (beta : ℂ) = 1 := by
    rw [goldfeldShiftedZetaPole]
    norm_num
  have hL := GoldfeldLocalCancellation_goldfeldShiftedLFunctionDividedSlope_mul chi1 beta hzero
    (goldfeldShiftedZetaPole beta)
  rw [hshift] at hL
  have hphi := goldfeldMellinContinuationData.equals_candidate
    (goldfeldShiftedZetaPole beta)
  rw [goldfeldMellinCandidate] at hphi
  have hphiMul : goldfeldShiftedZetaPole beta *
      goldfeldMellinContinuationData.Phi (goldfeldShiftedZetaPole beta) =
      -goldfeldDerivativeMellin (goldfeldShiftedZetaPole beta) := by
    rw [hphi]
    field_simp [hdelta0]
  rw [goldfeldContourNumerator, goldfeldContourResidue, hshift,
    riemannZeta₁_one, one_mul, ← hphiMul, ← hL]
  ring

end BoundedGaps.Maynard

end

/-! ## Uniform Mellin decay on Goldfeld's contour strip

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldMellinStripDecay`. -/

noncomputable section

open Complex Set MeasureTheory Filter Real

open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace

namespace BoundedGaps.Maynard

private theorem GoldfeldMellinStripDecay_iteratedDeriv_real_smul
    (n : ℕ) (f : ℝ → ℝ) (g : ℝ → ℂ) (u : ℝ)
    (hf : ContDiffAt ℝ n f u) (hg : ContDiffAt ℝ n g u) :
    iteratedDeriv n (f • g) u = ∑ i ∈ Finset.range (n + 1),
      n.choose i • iteratedDeriv i f u • iteratedDeriv (n - i) g u := by
  simpa only [iteratedDerivWithin_univ] using
    iteratedDerivWithin_smul (Set.mem_univ u) uniqueDiffOn_univ
      hf.contDiffWithinAt hg.contDiffWithinAt

private noncomputable def GoldfeldMellinStripDecay_baseKernel (u : ℝ) : ℂ :=
  goldfeldMellinDerivativeWeight (Real.exp (-u))

private noncomputable def GoldfeldMellinStripDecay_stripKernel (sigma u : ℝ) : ℂ :=
  Real.exp (-sigma * u) • GoldfeldMellinStripDecay_baseKernel u

private theorem GoldfeldMellinStripDecay_weight_contDiff :
    ContDiff ℝ ∞ goldfeldMellinDerivativeWeight := by
  have hd : ContDiff ℝ ∞ goldfeldPlateauDerivativeComplex :=
    Complex.ofRealCLM.contDiff.comp goldfeldPlateau_deriv_contDiff
  unfold goldfeldMellinDerivativeWeight
  exact (Complex.ofRealCLM.contDiff.comp contDiff_id).mul hd

private theorem GoldfeldMellinStripDecay_base_contDiff : ContDiff ℝ ∞ GoldfeldMellinStripDecay_baseKernel := by
  unfold GoldfeldMellinStripDecay_baseKernel
  exact GoldfeldMellinStripDecay_weight_contDiff.comp (contDiff_id.neg.exp)

private theorem GoldfeldMellinStripDecay_strip_contDiff (sigma : ℝ) :
    ContDiff ℝ ∞ (GoldfeldMellinStripDecay_stripKernel sigma) := by
  unfold GoldfeldMellinStripDecay_stripKernel
  exact (contDiff_const.mul contDiff_id).exp.smul GoldfeldMellinStripDecay_base_contDiff

private theorem GoldfeldMellinStripDecay_base_eq_zero_of_pos {u : ℝ} (hu : 0 < u) :
    GoldfeldMellinStripDecay_baseKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlt : Real.exp (-u) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hd := goldfeldPlateau_deriv_eq_zero_of_pos_of_lt_one harg hlt
  simp [GoldfeldMellinStripDecay_baseKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem GoldfeldMellinStripDecay_base_eq_zero_of_lt_neg_log_two
    {u : ℝ} (hu : u < -Real.log 2) : GoldfeldMellinStripDecay_baseKernel u = 0 := by
  have harg : 0 < Real.exp (-u) := Real.exp_pos _
  have hlog : Real.log 2 < -u := by linarith
  have hgt : 2 < Real.exp (-u) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact (Real.exp_lt_exp).2 hlog
  have hd := goldfeldPlateau_deriv_eq_zero_of_two_lt hgt
  simp [GoldfeldMellinStripDecay_baseKernel, goldfeldMellinDerivativeWeight,
    goldfeldPlateauDerivativeComplex, hd]

private theorem GoldfeldMellinStripDecay_base_support_subset :
    Function.support GoldfeldMellinStripDecay_baseKernel ⊆ Icc (-Real.log 2) 0 := by
  intro u hu
  by_contra hnot
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_cases hright : 0 < u
      · exact Or.inr hright
      · exact False.elim (hnot ⟨hleft', le_of_not_gt hright⟩)
  rcases hcases with hleft | hright
  · exact hu (GoldfeldMellinStripDecay_base_eq_zero_of_lt_neg_log_two hleft)
  · exact hu (GoldfeldMellinStripDecay_base_eq_zero_of_pos hright)

private theorem GoldfeldMellinStripDecay_base_hasCompactSupport : HasCompactSupport GoldfeldMellinStripDecay_baseKernel := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Icc (-Real.log 2) 0) isCompact_Icc
  exact GoldfeldMellinStripDecay_base_support_subset

private noncomputable def GoldfeldMellinStripDecay_baseSchwartz : 𝓢(ℝ, ℂ) :=
  GoldfeldMellinStripDecay_base_hasCompactSupport.toSchwartzMap GoldfeldMellinStripDecay_base_contDiff

private theorem GoldfeldMellinStripDecay_stripKernel_fourier (sigma t : ℝ) :
    goldfeldDerivativeMellin ((sigma : ℂ) + t * I) =
      𝓕 (GoldfeldMellinStripDecay_stripKernel sigma) (t / (2 * π)) := by
  calc
    goldfeldDerivativeMellin ((sigma : ℂ) + t * I) =
        mellin goldfeldMellinDerivativeWeight ((sigma : ℂ) + t * I) :=
      goldfeldDerivativeMellin_eq_weight _
    _ = 𝓕 (fun u : ℝ =>
        Real.exp (-((sigma : ℂ) + t * I).re * u) •
          goldfeldMellinDerivativeWeight (Real.exp (-u)))
        (((sigma : ℂ) + t * I).im / (2 * π)) :=
      mellin_eq_fourier goldfeldMellinDerivativeWeight
    _ = 𝓕 (GoldfeldMellinStripDecay_stripKernel sigma) (t / (2 * π)) := by
      norm_num
      apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * π)))
      funext u
      simp [GoldfeldMellinStripDecay_stripKernel, GoldfeldMellinStripDecay_baseKernel]

private theorem GoldfeldMellinStripDecay_iteratedDeriv_base_eq_zero_of_not_mem
    (n : ℕ) {u : ℝ} (hu : u ∉ Icc (-Real.log 2) 0) :
    iteratedDeriv n GoldfeldMellinStripDecay_baseKernel u = 0 := by
  have hcases : u < -Real.log 2 ∨ 0 < u := by
    by_cases hleft : u < -Real.log 2
    · exact Or.inl hleft
    · right
      have hleft' : -Real.log 2 ≤ u := le_of_not_gt hleft
      by_contra hnot
      exact hu ⟨hleft', le_of_not_gt hnot⟩
  rcases hcases with hleft | hright
  · have heq : Set.EqOn GoldfeldMellinStripDecay_baseKernel 0 (Iio (-Real.log 2)) := by
      intro v hv
      exact GoldfeldMellinStripDecay_base_eq_zero_of_lt_neg_log_two hv
    have h := heq.iteratedDeriv_of_isOpen isOpen_Iio n hleft
    simpa using h
  · have heq : Set.EqOn GoldfeldMellinStripDecay_baseKernel 0 (Ioi 0) := by
      intro v hv
      exact GoldfeldMellinStripDecay_base_eq_zero_of_pos hv
    have h := heq.iteratedDeriv_of_isOpen isOpen_Ioi n hright
    simpa using h

private theorem GoldfeldMellinStripDecay_norm_iteratedDeriv_base_le_seminorm (n : ℕ) (u : ℝ) :
    ‖iteratedDeriv n GoldfeldMellinStripDecay_baseKernel u‖ ≤
      SchwartzMap.seminorm ℝ 0 n GoldfeldMellinStripDecay_baseSchwartz := by
  have h := SchwartzMap.le_seminorm' ℝ 0 n GoldfeldMellinStripDecay_baseSchwartz u
  change ‖iteratedDeriv n (GoldfeldMellinStripDecay_baseSchwartz : ℝ → ℂ) u‖ ≤
    SchwartzMap.seminorm ℝ 0 n GoldfeldMellinStripDecay_baseSchwartz
  simpa using h

private theorem GoldfeldMellinStripDecay_expFactor_iteratedDeriv (sigma : ℝ) (n : ℕ) :
    iteratedDeriv n (fun u : ℝ => Real.exp (-sigma * u)) =
      fun u => (-sigma) ^ n * Real.exp (-sigma * u) := by
  simpa only [neg_mul] using iteratedDeriv_exp_const_mul n (-sigma)

private theorem GoldfeldMellinStripDecay_expFactor_le_four
    {sigma u : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (hu : u ∈ Icc (-Real.log 2) 0) :
    Real.exp (-sigma * u) ≤ 4 := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsigmaAbs : |sigma| ≤ 2 :=
    (abs_le).2 ⟨by linarith [hsigma.1], hsigma.2⟩
  have huAbs : |u| ≤ Real.log 2 := by
    rw [abs_of_nonpos hu.2]
    linarith [hu.1]
  have hprod : |sigma * u| ≤ 2 * Real.log 2 := by
    rw [abs_mul]
    exact mul_le_mul hsigmaAbs huAbs (abs_nonneg u) (by norm_num)
  have harg : -sigma * u ≤ 2 * Real.log 2 := by
    calc
      -sigma * u = -(sigma * u) := by ring
      _ ≤ |sigma * u| := neg_le_abs _
      _ ≤ 2 * Real.log 2 := hprod
  calc
    Real.exp (-sigma * u) ≤ Real.exp (2 * Real.log 2) :=
      Real.exp_le_exp.mpr harg
    _ = 4 := by
      rw [show (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 by ring,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

private theorem GoldfeldMellinStripDecay_norm_iteratedDeriv_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (u : ℝ) :
    ‖iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma) u‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz := by
  by_cases hu : u ∈ Icc (-Real.log 2) 0
  · rw [show GoldfeldMellinStripDecay_stripKernel sigma =
        (fun u : ℝ => Real.exp (-sigma * u)) • GoldfeldMellinStripDecay_baseKernel by rfl]
    have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
      (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
        exact_mod_cast le_top)
    have hBase : ContDiffAt ℝ n GoldfeldMellinStripDecay_baseKernel u :=
      GoldfeldMellinStripDecay_base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
    rw [GoldfeldMellinStripDecay_iteratedDeriv_real_smul n _ _ u hExp hBase]
    calc
      ‖∑ i ∈ Finset.range (n + 1),
          n.choose i •
            iteratedDeriv i (fun u : ℝ => Real.exp (-sigma * u)) u •
              iteratedDeriv (n - i) GoldfeldMellinStripDecay_baseKernel u‖ ≤
          ∑ i ∈ Finset.range (n + 1),
            ‖n.choose i •
              iteratedDeriv i (fun u : ℝ => Real.exp (-sigma * u)) u •
                iteratedDeriv (n - i) GoldfeldMellinStripDecay_baseKernel u‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * 2 ^ i * 4 *
            SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz := by
        apply Finset.sum_le_sum
        intro i hi
        rw [GoldfeldMellinStripDecay_expFactor_iteratedDeriv]
        rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul,
          norm_smul, Real.norm_eq_abs]
        have hsigmaPow : |(-sigma) ^ i| ≤ (2 : ℝ) ^ i := by
          rw [abs_pow, abs_neg]
          exact pow_le_pow_left₀ (abs_nonneg sigma) (by
            exact (abs_le).2 ⟨by linarith [hsigma.1], hsigma.2⟩) i
        have hexp := GoldfeldMellinStripDecay_expFactor_le_four hsigma hu
        have hbase := GoldfeldMellinStripDecay_norm_iteratedDeriv_base_le_seminorm (n - i) u
        have hchoose : 0 ≤ (n.choose i : ℝ) := by positivity
        have hpow : 0 ≤ (2 : ℝ) ^ i := by positivity
        have hseminorm : 0 ≤ SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz :=
          by positivity
        rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
        change (n.choose i : ℝ) *
            (|(-sigma) ^ i| * Real.exp (-sigma * u) *
              ‖iteratedDeriv (n - i) GoldfeldMellinStripDecay_baseKernel u‖) ≤ _
        calc
          (n.choose i : ℝ) *
                (|(-sigma) ^ i| * Real.exp (-sigma * u) *
                  ‖iteratedDeriv (n - i) GoldfeldMellinStripDecay_baseKernel u‖) ≤
              (n.choose i : ℝ) *
                ((2 : ℝ) ^ i * 4 *
                  SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz) := by
            gcongr
          _ = (n.choose i : ℝ) * 2 ^ i * 4 *
              SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz := by ring
  · have hzero : iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma) u = 0 := by
      rw [show GoldfeldMellinStripDecay_stripKernel sigma =
        (fun u : ℝ => Real.exp (-sigma * u)) • GoldfeldMellinStripDecay_baseKernel by rfl]
      have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
        (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
          exact_mod_cast le_top)
      have hBase : ContDiffAt ℝ n GoldfeldMellinStripDecay_baseKernel u :=
        GoldfeldMellinStripDecay_base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
      rw [GoldfeldMellinStripDecay_iteratedDeriv_real_smul n _ _ u hExp hBase]
      apply Finset.sum_eq_zero
      intro i hi
      rw [GoldfeldMellinStripDecay_iteratedDeriv_base_eq_zero_of_not_mem (n - i) hu]
      simp
    rw [hzero, norm_zero]
    positivity

private theorem GoldfeldMellinStripDecay_strip_hasCompactSupport (sigma : ℝ) :
    HasCompactSupport (GoldfeldMellinStripDecay_stripKernel sigma) := by
  change HasCompactSupport
    ((fun u : ℝ => Real.exp (-sigma * u)) • GoldfeldMellinStripDecay_baseKernel)
  exact GoldfeldMellinStripDecay_base_hasCompactSupport.smul_left

private theorem GoldfeldMellinStripDecay_hasCompactSupport_iteratedDeriv
    {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∀ n : ℕ, HasCompactSupport (iteratedDeriv n f)
  | 0 => by simpa using hf
  | n + 1 => by
      rw [iteratedDeriv_succ]
      exact (GoldfeldMellinStripDecay_hasCompactSupport_iteratedDeriv hf n).deriv

private theorem GoldfeldMellinStripDecay_integrable_iteratedDeriv_stripKernel
    (sigma : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (GoldfeldMellinStripDecay_strip_contDiff sigma).continuous_iteratedDeriv n (by
      exact_mod_cast le_top)
  · exact GoldfeldMellinStripDecay_hasCompactSupport_iteratedDeriv (GoldfeldMellinStripDecay_strip_hasCompactSupport sigma) n

private theorem GoldfeldMellinStripDecay_iteratedDeriv_stripKernel_eq_zero_of_not_mem
    (n : ℕ) (sigma : ℝ) {u : ℝ}
    (hu : u ∉ Icc (-Real.log 2) 0) :
    iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma) u = 0 := by
  rw [show GoldfeldMellinStripDecay_stripKernel sigma =
    (fun u : ℝ => Real.exp (-sigma * u)) • GoldfeldMellinStripDecay_baseKernel by rfl]
  have hExp : ContDiffAt ℝ n (fun u : ℝ => Real.exp (-sigma * u)) u :=
    (contDiff_const.mul contDiff_id).exp.contDiffAt.of_le (by
      exact_mod_cast le_top)
  have hBase : ContDiffAt ℝ n GoldfeldMellinStripDecay_baseKernel u :=
    GoldfeldMellinStripDecay_base_contDiff.contDiffAt.of_le (by exact_mod_cast le_top)
  rw [GoldfeldMellinStripDecay_iteratedDeriv_real_smul n _ _ u hExp hBase]
  apply Finset.sum_eq_zero
  intro i hi
  rw [GoldfeldMellinStripDecay_iteratedDeriv_base_eq_zero_of_not_mem (n - i) hu]
  simp

private theorem GoldfeldMellinStripDecay_integral_norm_iteratedDeriv_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2) :
    ∫ u : ℝ, ‖iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma) u‖ ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz) * Real.log 2 := by
  let M : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) * 2 ^ i * 4 *
      SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hsupport : (fun u : ℝ => ‖iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma) u‖) =
      (Icc (-Real.log 2) 0).indicator
        (fun u : ℝ => ‖iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma) u‖) := by
    funext u
    by_cases hu : u ∈ Icc (-Real.log 2) 0
    · simp [hu]
    · rw [GoldfeldMellinStripDecay_iteratedDeriv_stripKernel_eq_zero_of_not_mem n sigma hu]
      simp [hu]
  rw [hsupport, integral_indicator measurableSet_Icc]
  calc
    (∫ u : ℝ in Icc (-Real.log 2) 0,
        ‖iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma) u‖) ≤
        ∫ _u : ℝ in Icc (-Real.log 2) 0, M := by
      apply setIntegral_mono_on
      · exact (GoldfeldMellinStripDecay_integrable_iteratedDeriv_stripKernel sigma n).norm.integrableOn
      · apply integrableOn_const
        · exact ne_of_lt isCompact_Icc.measure_lt_top
        · finiteness
      · exact measurableSet_Icc
      · intro u hu
        simpa [M] using GoldfeldMellinStripDecay_norm_iteratedDeriv_stripKernel_le n hsigma u
    _ = M * Real.log 2 := by
      rw [setIntegral_const, Measure.real, Real.volume_Icc]
      rw [show 0 - -Real.log 2 = Real.log 2 by ring]
      rw [ENNReal.toReal_ofReal (Real.log_nonneg (by norm_num))]
      simp [smul_eq_mul, mul_comm]
    _ = (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz) * Real.log 2 := rfl

private theorem GoldfeldMellinStripDecay_abs_pow_mul_norm_fourier_stripKernel_le
    (n : ℕ) {sigma : ℝ} (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2)
    (t : ℝ) :
    |t| ^ n * ‖𝓕 (GoldfeldMellinStripDecay_stripKernel sigma) (t / (2 * π))‖ ≤
      (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz) * Real.log 2 := by
  let xi : ℝ := t / (2 * π)
  have hFourier := congrFun
    (Real.fourier_iteratedDeriv (N := n)
      ((GoldfeldMellinStripDecay_strip_contDiff sigma).of_le (by exact_mod_cast le_top))
      (fun m _hm => GoldfeldMellinStripDecay_integrable_iteratedDeriv_stripKernel sigma m)
      (n := n) (by rfl)) xi
  have hfreq : ‖(2 * (π : ℂ) * I * (xi : ℂ))‖ = |t| := by
    have hcoeff : 2 * (π : ℂ) * I * (xi : ℂ) = (t : ℂ) * I := by
      dsimp [xi]
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [hcoeff, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  calc
    |t| ^ n * ‖𝓕 (GoldfeldMellinStripDecay_stripKernel sigma) (t / (2 * π))‖ =
        ‖(2 * (π : ℂ) * I * (xi : ℂ)) ^ n •
          𝓕 (GoldfeldMellinStripDecay_stripKernel sigma) xi‖ := by
      rw [norm_smul, norm_pow, hfreq]
    _ = ‖𝓕 (iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma)) xi‖ := by
      rw [hFourier]
    _ ≤ ∫ u : ℝ, ‖iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma) u‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 volume (innerₗ ℝ) (iteratedDeriv n (GoldfeldMellinStripDecay_stripKernel sigma)) xi
    _ ≤ (∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * 2 ^ i * 4 *
          SchwartzMap.seminorm ℝ 0 (n - i) GoldfeldMellinStripDecay_baseSchwartz) * Real.log 2 :=
      GoldfeldMellinStripDecay_integral_norm_iteratedDeriv_stripKernel_le n hsigma

theorem goldfeldMellinCandidate_decay_on_closedStrip
    (A : ℕ) (_hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, sigma ∈ Icc (-(1 : ℝ)) 2 →
        1 ≤ |t| →
          ‖goldfeldMellinCandidate ((sigma : ℂ) + t * I)‖ ≤
            C / (1 + |t|) ^ A := by
  let M : ℝ := (∑ i ∈ Finset.range (A + 1),
    (A.choose i : ℝ) * 2 ^ i * 4 *
      SchwartzMap.seminorm ℝ 0 (A - i) GoldfeldMellinStripDecay_baseSchwartz) * Real.log 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  let C : ℝ := (M + 1) * 2 ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma ht
  let s : ℂ := (sigma : ℂ) + t * I
  have htpos : 0 < |t| := zero_lt_one.trans_le ht
  have hsNorm : (1 : ℝ) ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    have him' : |t| ≤ ‖s‖ := by simpa [s] using him
    exact ht.trans him'
  have hcandidate :
      ‖goldfeldMellinCandidate s‖ ≤ ‖goldfeldDerivativeMellin s‖ := by
    rw [goldfeldMellinCandidate, norm_div, norm_neg]
    exact div_le_self (norm_nonneg _) hsNorm
  have hfourier :
      ‖goldfeldDerivativeMellin s‖ =
        ‖𝓕 (GoldfeldMellinStripDecay_stripKernel sigma) (t / (2 * π))‖ := by
    rw [GoldfeldMellinStripDecay_stripKernel_fourier]
  have hpow := GoldfeldMellinStripDecay_abs_pow_mul_norm_fourier_stripKernel_le A hsigma t
  have hfourierDecay :
      ‖𝓕 (GoldfeldMellinStripDecay_stripKernel sigma) (t / (2 * π))‖ ≤ M / |t| ^ A := by
    apply (le_div_iff₀ (pow_pos htpos A)).2
    simpa [M, mul_comm] using hpow
  have hscale : 1 + |t| ≤ 2 * |t| := by linarith
  have hpowscale : (1 + |t|) ^ A ≤ (2 * |t|) ^ A :=
    pow_le_pow_left₀ (by positivity) hscale A
  have hconvert : M / |t| ^ A ≤ C / (1 + |t|) ^ A := by
    apply (div_le_div_iff₀ (pow_pos htpos A) (by positivity)).2
    calc
      M * (1 + |t|) ^ A ≤ M * (2 * |t|) ^ A :=
        mul_le_mul_of_nonneg_left hpowscale hM
      _ ≤ (M + 1) * (2 * |t|) ^ A := by
        gcongr
        linarith
      _ = C * |t| ^ A := by
        dsimp [C]
        rw [mul_pow]
        ring
  calc
    ‖goldfeldMellinCandidate s‖ ≤ ‖goldfeldDerivativeMellin s‖ := hcandidate
    _ = ‖𝓕 (GoldfeldMellinStripDecay_stripKernel sigma) (t / (2 * π))‖ := hfourier
    _ ≤ M / |t| ^ A := hfourierDecay
    _ ≤ C / (1 + |t|) ^ A := hconvert

theorem goldfeldMellinContinuation_decay_on_closedStrip
    (A : ℕ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ sigma t : ℝ, sigma ∈ Icc (-(1 : ℝ)) 2 →
        1 ≤ |t| →
          ‖goldfeldMellinContinuationData.Phi
              ((sigma : ℂ) + t * I)‖ ≤
            C / (1 + |t|) ^ A := by
  obtain ⟨C, hC, hbound⟩ :=
    goldfeldMellinCandidate_decay_on_closedStrip A hA
  refine ⟨C, hC, ?_⟩
  intro sigma t hsigma ht
  rw [goldfeldMellinContinuationData.equals_candidate]
  exact hbound sigma t hsigma ht

end BoundedGaps.Maynard

end

/-! ## Goldfeld horizontal-edge decay

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldHorizontalEdge`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set Filter

open scoped Interval Topology

private lemma GoldfeldHorizontalEdge_goldfeld_mul_decay_bound
    {q u x C : ℝ} {A : ℕ} (hq : 0 ≤ q) (hu : 0 ≤ u)
    (_hx : 0 ≤ x) (hC : 0 ≤ C) :
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 ≤
      (C * (2 : ℝ) ^ A) * q ^ A * x ^ 2 / (1 + u) ^ 2 := by
  have hbase : u + 2 ≤ 2 * (1 + u) := by linarith
  have hpow : (u + 2) ^ A ≤ (2 * (1 + u)) ^ A :=
    pow_le_pow_left₀ (by linarith) hbase A
  have hqpow : 0 ≤ q ^ A := pow_nonneg hq A
  have hprod :
      q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 ≤
        q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x ^ 2 := by
    gcongr
  calc
    (q * (u + 2)) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 =
        q ^ A * (u + 2) ^ A * (C / (1 + u) ^ (A + 2)) * x ^ 2 := by
      rw [mul_pow]
    _ ≤ q ^ A * (2 * (1 + u)) ^ A *
          (C / (1 + u) ^ (A + 2)) * x ^ 2 := hprod
    _ = (C * (2 : ℝ) ^ A) * q ^ A * x ^ 2 / (1 + u) ^ 2 := by
      rw [mul_pow]
      field_simp
      ring

private theorem GoldfeldHorizontalEdge_norm_goldfeldContourIntegrand_horizontal_le_of_bounds
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    {A : ℕ} {Cphi beta x sigma t : ℝ}
    (hx : 1 ≤ x)
    (hsigma : sigma ∈ Icc (-(1 : ℝ)) 2) (ht : 1 ≤ |t|)
    (hF : ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ ≤
      ((q : ℝ) * (|t| + 2)) ^ A)
    (hPhi : ‖goldfeldMellinContinuationData.Phi
        ((sigma : ℂ) + t * I)‖ ≤ Cphi / (1 + |t|) ^ (A + 2))
    (hCphi : 0 ≤ Cphi) :
    ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + t * I)‖ ≤
      (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A * x ^ 2 /
        (1 + |t|) ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hsigmaPow : x ^ sigma ≤ x ^ (2 : ℕ) := by
    calc
      x ^ sigma ≤ x ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx hsigma.2
      _ = x ^ (2 : ℕ) := Real.rpow_two x
  have hpowprod := GoldfeldHorizontalEdge_goldfeld_mul_decay_bound (A := A) hq0 (abs_nonneg t)
    (by positivity : 0 ≤ x) hCphi
  have hcpow : ‖(x : ℂ) ^ ((sigma : ℂ) + t * I)‖ = x ^ sigma := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp
  rw [goldfeldContourIntegrand, norm_mul, norm_mul, hcpow]
  calc
    ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ *
        ‖goldfeldMellinContinuationData.Phi ((sigma : ℂ) + t * I)‖ *
        x ^ sigma ≤
      ((q : ℝ) * (|t| + 2)) ^ A *
        (Cphi / (1 + |t|) ^ (A + 2)) * x ^ 2 := by
      calc
        _ ≤
            ‖goldfeldFourFactorLFunction chi1 chi
                (((sigma : ℂ) + t * I) + (beta : ℂ))‖ *
              ‖goldfeldMellinContinuationData.Phi ((sigma : ℂ) + t * I)‖ *
              x ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hsigmaPow
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ ≤ _ := by
          gcongr
    _ ≤ (Cphi * (2 : ℝ) ^ A) * (q : ℝ) ^ A * x ^ 2 /
          (1 + |t|) ^ 2 := hpowprod

theorem exists_norm_goldfeldContourIntegrand_horizontal_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x sigma t : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            sigma ∈ Icc (-(1 : ℝ)) 2 → 1 ≤ |t| →
            ‖goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) + t * I)‖ ≤
              C * (q : ℝ) ^ A * x ^ 2 / (1 + |t|) ^ 2 := by
  obtain ⟨A, hA, hF⟩ :=
    exists_norm_goldfeldFourFactorLFunction_closedStrip_le_pow
  obtain ⟨Cphi, hCphi, hPhi⟩ :=
    goldfeldMellinContinuation_decay_on_closedStrip (A + 2) (by omega)
  let C : ℝ := Cphi * (2 : ℝ) ^ A
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x sigma t hbeta0 hbeta1 hx hsigma ht
  have him : (((sigma : ℂ) + t * I).im) = t := by simp
  have hF' : ‖goldfeldFourFactorLFunction chi1 chi
        (((sigma : ℂ) + t * I) + (beta : ℂ))‖ ≤
      ((q : ℝ) * (|t| + 2)) ^ A := by
    have h := hF q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta ((sigma : ℂ) + t * I) hbeta0 hbeta1
        (by simpa using hsigma.1) (by simpa using hsigma.2)
        (by simpa [him] using ht)
    simpa [him] using h
  have hPhi' := hPhi sigma t hsigma ht
  have hpoint := GoldfeldHorizontalEdge_norm_goldfeldContourIntegrand_horizontal_le_of_bounds
    (A := A) (q := q) (chi1 := chi1) (chi := chi)
    hx hsigma ht hF' hPhi' hCphi.le
  simpa [C, mul_assoc, mul_left_comm, mul_comm] using hpoint

private theorem GoldfeldHorizontalEdge_continuous_goldfeldRegularizedContourIntegrand_horizontal_plus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    Continuous (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
      chi1 chi beta x ((sigma : ℂ) + T * I)) := by
  have hpath : Continuous (fun sigma : ℝ => (sigma : ℂ) + T * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hnum : Continuous (goldfeldContourNumerator chi1 chi beta x) :=
    (differentiable_goldfeldContourNumerator hchi1 hchi hcross beta hx).continuous
  have hden : Continuous (fun sigma : ℝ =>
      ((sigma : ℂ) + T * I) - goldfeldShiftedZetaPole beta) :=
    hpath.sub continuous_const
  have hden_ne : ∀ sigma : ℝ,
      ((sigma : ℂ) + T * I) - goldfeldShiftedZetaPole beta ≠ 0 := by
    intro sigma hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  unfold goldfeldRegularizedContourIntegrand
  exact (hnum.comp hpath).div hden hden_ne

private theorem GoldfeldHorizontalEdge_continuous_goldfeldRegularizedContourIntegrand_horizontal_minus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    Continuous (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
      chi1 chi beta x ((sigma : ℂ) - T * I)) := by
  have hpath : Continuous (fun sigma : ℝ => (sigma : ℂ) - T * I) :=
    Complex.continuous_ofReal.sub continuous_const
  have hnum : Continuous (goldfeldContourNumerator chi1 chi beta x) :=
    (differentiable_goldfeldContourNumerator hchi1 hchi hcross beta hx).continuous
  have hden : Continuous (fun sigma : ℝ =>
      ((sigma : ℂ) - T * I) - goldfeldShiftedZetaPole beta) :=
    hpath.sub continuous_const
  have hden_ne : ∀ sigma : ℝ,
      ((sigma : ℂ) - T * I) - goldfeldShiftedZetaPole beta ≠ 0 := by
    intro sigma hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  unfold goldfeldRegularizedContourIntegrand
  exact (hnum.comp hpath).div hden hden_ne

theorem intervalIntegrable_goldfeldRegularizedContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T) :
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
        chi1 chi beta x ((sigma : ℂ) + T * I)) volume (-1) 2 ∧
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand
        chi1 chi beta x ((sigma : ℂ) - T * I)) volume (-1) 2 := by
  exact ⟨(GoldfeldHorizontalEdge_continuous_goldfeldRegularizedContourIntegrand_horizontal_plus
      hchi1 hchi hcross hx hT).intervalIntegrable _ _,
    (GoldfeldHorizontalEdge_continuous_goldfeldRegularizedContourIntegrand_horizontal_minus
      hchi1 hchi hcross hx hT).intervalIntegrable _ _⟩

private theorem GoldfeldHorizontalEdge_goldfeldRegularizedContourIntegrand_eq_horizontal_plus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) (sigma : ℝ) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I) =
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs0 : ((sigma : ℂ) + T * I) ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    simp at hi
    linarith
  have hsp : ((sigma : ℂ) + T * I) ≠ goldfeldShiftedZetaPole beta := by
    intro hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    chi1 chi hzero hs0 hsp

private theorem GoldfeldHorizontalEdge_goldfeldRegularizedContourIntegrand_eq_horizontal_minus
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1) (chi : DirichletCharacter ℂ q)
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) (sigma : ℝ) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I) =
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hs0 : ((sigma : ℂ) - T * I) ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    simp at hi
    linarith
  have hsp : ((sigma : ℂ) - T * I) ≠ goldfeldShiftedZetaPole beta := by
    intro hs
    have hi := congrArg Complex.im hs
    simp [goldfeldShiftedZetaPole] at hi
    linarith
  exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
    chi1 chi hzero hs0 hsp

theorem goldfeldRegularizedContourIntegrand_eq_intervalIntegral_goldfeldContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    {beta x T : ℝ}
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hT : 1 ≤ T) :
    (∫ sigma in (-1)..2,
      goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) =
      ∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I) ∧
    (∫ sigma in (-1)..2,
      goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) =
      ∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I) := by
  have hplus : Set.EqOn
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I))
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) (uIcc (-1) 2) := by
    intro sigma _hsigma
    exact GoldfeldHorizontalEdge_goldfeldRegularizedContourIntegrand_eq_horizontal_plus
      chi1 chi hzero hT sigma
  have hminus : Set.EqOn
      (fun sigma : ℝ => goldfeldRegularizedContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I))
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) (uIcc (-1) 2) := by
    intro sigma _hsigma
    exact GoldfeldHorizontalEdge_goldfeldRegularizedContourIntegrand_eq_horizontal_minus
      chi1 chi hzero hT sigma
  exact ⟨intervalIntegral.integral_congr hplus,
    intervalIntegral.integral_congr hminus⟩

theorem intervalIntegrable_goldfeldContourIntegrand_horizontal
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1} {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ} (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)) volume (-1) 2 ∧
    IntervalIntegrable
      (fun sigma : ℝ => goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)) volume (-1) 2 := by
  have hreg := intervalIntegrable_goldfeldRegularizedContourIntegrand_horizontal
    (beta := beta) hchi1 hchi hcross hx hT
  constructor
  · exact hreg.1.congr fun sigma _hsigma =>
      GoldfeldHorizontalEdge_goldfeldRegularizedContourIntegrand_eq_horizontal_plus
        chi1 chi hzero hT sigma
  · exact hreg.2.congr fun sigma _hsigma =>
      GoldfeldHorizontalEdge_goldfeldRegularizedContourIntegrand_eq_horizontal_minus
        chi1 chi hzero hT sigma

end BoundedGaps.Maynard

end

/-! ## Reciprocal integrals on rectangle boundaries

Source module `BoundedGaps.BombieriVinogradov.Analytic.RectangleReciprocalWedgeIntegral`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex MeasureTheory intervalIntegral

theorem wedgeIntegral_comp_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (z w p : ℂ) :
    Complex.wedgeIntegral z w (fun s => f (s - p)) =
      Complex.wedgeIntegral (z - p) (w - p) f := by
  simp_rw [Complex.wedgeIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro t _
    apply congrArg f
    apply Complex.ext <;> simp
  · apply congrArg (Complex.I • ·)
    apply intervalIntegral.integral_congr
    intro t _
    apply congrArg f
    apply Complex.ext <;> simp

private lemma RectangleReciprocalWedgeIntegral_sq_add_sq_ne_zero_right (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    x ^ 2 + y ^ 2 ≠ 0 := by
  positivity

private lemma RectangleReciprocalWedgeIntegral_inv_add_mul_I (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * I)⁻¹ =
      ((x : ℂ) - I * (y : ℂ)) / (x ^ 2 + y ^ 2 : ℝ) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr 1
  · simp [map_add, map_mul]
    ring
  · simp [Complex.normSq]
    ring

private lemma RectangleReciprocalWedgeIntegral_integral_self_div_sq_add_sq {a b y : ℝ} (hy : y ≠ 0) :
    ∫ x in a..b, x / (x ^ 2 + y ^ 2) =
      Real.log (b ^ 2 + y ^ 2) / 2 -
        Real.log (a ^ 2 + y ^ 2) / 2 := by
  let F : ℝ → ℝ := fun x => Real.log (x ^ 2 + y ^ 2) / 2
  have hF : ∀ x : ℝ, HasDerivAt F (x / (x ^ 2 + y ^ 2)) x := by
    intro x
    have hbase :
        HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).add_const (y ^ 2)
    convert! (hbase.log (RectangleReciprocalWedgeIntegral_sq_add_sq_ne_zero_right x hy)).div_const 2 using 1
    field_simp
  have hderiv : deriv F = fun x => x / (x ^ 2 + y ^ 2) :=
    funext fun x => (hF x).deriv
  rw [← hderiv, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (hF x).differentiableAt)]
  rw [hderiv]
  exact
    (continuous_id.div (continuous_id.pow 2 |>.add continuous_const)
      (fun x => RectangleReciprocalWedgeIntegral_sq_add_sq_ne_zero_right x hy)).intervalIntegrable _ _

private lemma RectangleReciprocalWedgeIntegral_integral_const_div_sq_add_sq {a b y : ℝ} (hy : y ≠ 0) :
    ∫ x in a..b, y / (x ^ 2 + y ^ 2) =
      Real.arctan (b / y) - Real.arctan (a / y) := by
  let F : ℝ → ℝ := fun x => Real.arctan (x / y)
  have hF : ∀ x : ℝ, HasDerivAt F (y / (x ^ 2 + y ^ 2)) x := by
    intro x
    have hquot : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
      simpa using hasDerivAt_id x |>.div_const y
    convert! (Real.hasDerivAt_arctan (x / y)).comp x hquot using 1
    field_simp [hy, RectangleReciprocalWedgeIntegral_sq_add_sq_ne_zero_right x hy]
    ring
  have hderiv : deriv F = fun x => y / (x ^ 2 + y ^ 2) :=
    funext fun x => (hF x).deriv
  rw [← hderiv, intervalIntegral.integral_deriv_eq_sub
    (fun x _ => (hF x).differentiableAt)]
  rw [hderiv]
  exact
    (continuous_const.div (continuous_id.pow 2 |>.add continuous_const)
      (fun x => RectangleReciprocalWedgeIntegral_sq_add_sq_ne_zero_right x hy)).intervalIntegrable _ _

private lemma RectangleReciprocalWedgeIntegral_integral_div_add_mul_I {a b y : ℝ} (hy : y ≠ 0) (c : ℂ) :
    ∫ x : ℝ in a..b, c / (x + y * I) =
      c * (Real.log (b ^ 2 + y ^ 2) / 2 -
        Real.log (a ^ 2 + y ^ 2) / 2) -
      c * I * (Real.arctan (b / y) - Real.arctan (a / y)) := by
  have hpoint (x : ℝ) :
      c / (x + y * I) =
        c * (x / (x ^ 2 + y ^ 2) : ℝ) -
          c * I * (y / (x ^ 2 + y ^ 2) : ℝ) := by
    rw [div_eq_mul_inv, RectangleReciprocalWedgeIntegral_inv_add_mul_I]
    push_cast
    ring
  have hdenom : Continuous fun x : ℝ => x ^ 2 + y ^ 2 :=
    continuous_id.pow 2 |>.add continuous_const
  have hxReal : Continuous fun x : ℝ => x / (x ^ 2 + y ^ 2) :=
    continuous_id.div hdenom (fun x => RectangleReciprocalWedgeIntegral_sq_add_sq_ne_zero_right x hy)
  have hyReal : Continuous fun x : ℝ => y / (x ^ 2 + y ^ 2) :=
    continuous_const.div hdenom (fun x => RectangleReciprocalWedgeIntegral_sq_add_sq_ne_zero_right x hy)
  have hx : IntervalIntegrable
      (fun x : ℝ => c * (x / (x ^ 2 + y ^ 2) : ℝ)) volume a b :=
    (continuous_const.mul (continuous_ofReal.comp hxReal)).intervalIntegrable _ _
  have hyi : IntervalIntegrable
      (fun x : ℝ => c * I * (y / (x ^ 2 + y ^ 2) : ℝ)) volume a b :=
    ((continuous_const.mul continuous_const).mul
      (continuous_ofReal.comp hyReal)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x),
    intervalIntegral.integral_sub hx hyi]
  simp_rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal, RectangleReciprocalWedgeIntegral_integral_self_div_sq_add_sq hy,
    RectangleReciprocalWedgeIntegral_integral_const_div_sq_add_sq hy]
  push_cast
  rfl

private lemma RectangleReciprocalWedgeIntegral_I_mul_div_add_mul_I (x y : ℝ) (c : ℂ) :
    I * (c / (x + y * I)) = c / (y + (-x) * I) := by
  have hrotate : (y : ℂ) + -(x : ℂ) * I =
      -I * ((x : ℂ) + (y : ℂ) * I) := by
    apply Complex.ext <;> simp
  change I * (c / ((x : ℂ) + (y : ℂ) * I)) =
    c / ((y : ℂ) + -(x : ℂ) * I)
  rw [hrotate]
  simp [div_eq_mul_inv]
  ring

private lemma RectangleReciprocalWedgeIntegral_I_mul_integral_div_add_mul_I
    {a b x : ℝ} (hx : x ≠ 0) (c : ℂ) :
    I * (∫ y : ℝ in a..b, c / (x + y * I)) =
      c * (Real.log (b ^ 2 + (-x) ^ 2) / 2 -
        Real.log (a ^ 2 + (-x) ^ 2) / 2) -
      c * I * (Real.arctan (b / (-x)) - Real.arctan (a / (-x))) := by
  rw [← intervalIntegral.integral_const_mul]
  calc
    (∫ y : ℝ in a..b, I * (c / (x + y * I))) =
        ∫ y : ℝ in a..b, c / (y + (-x) * I) :=
      intervalIntegral.integral_congr fun y _ => RectangleReciprocalWedgeIntegral_I_mul_div_add_mul_I x y c
    _ = _ := by
      simpa using
        (RectangleReciprocalWedgeIntegral_integral_div_add_mul_I (a := a) (b := b)
          (neg_ne_zero.mpr hx) c)

private lemma RectangleReciprocalWedgeIntegral_arctan_div_neg_eq_add_of_div_neg {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x / y < 0) :
    Real.arctan (y / -x) = Real.pi / 2 + Real.arctan (x / y) := by
  have hratio : y / x = (x / y)⁻¹ := by
    field_simp [hx, hy]
  calc
    Real.arctan (y / -x) = -Real.arctan (y / x) := by
      rw [div_neg, Real.arctan_neg]
    _ = -Real.arctan ((x / y)⁻¹) := by rw [hratio]
    _ = Real.pi / 2 + Real.arctan (x / y) := by
      rw [Real.arctan_inv_of_neg hxy]
      ring

private lemma RectangleReciprocalWedgeIntegral_arctan_div_neg_eq_sub_of_div_pos {x y : ℝ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : 0 < x / y) :
    Real.arctan (y / -x) = -Real.pi / 2 + Real.arctan (x / y) := by
  have hratio : y / x = (x / y)⁻¹ := by
    field_simp [hx, hy]
  calc
    Real.arctan (y / -x) = -Real.arctan (y / x) := by
      rw [div_neg, Real.arctan_neg]
    _ = -Real.arctan ((x / y)⁻¹) := by rw [hratio]
    _ = -Real.pi / 2 + Real.arctan (x / y) := by
      rw [Real.arctan_inv_of_pos hxy]
      ring

private theorem RectangleReciprocalWedgeIntegral_wedgeIntegral_add_wedgeIntegral_div_of_straddles_zero
    (z w c : ℂ)
    (hzRe : z.re < 0) (hwRe : 0 < w.re)
    (hzIm : z.im < 0) (hwIm : 0 < w.im) :
    Complex.wedgeIntegral z w (fun s => c / s) +
        Complex.wedgeIntegral w z (fun s => c / s) =
      2 * Real.pi * I * c := by
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq]
  simp only [smul_eq_mul]
  rw [RectangleReciprocalWedgeIntegral_integral_div_add_mul_I hzIm.ne c,
    RectangleReciprocalWedgeIntegral_integral_div_add_mul_I hwIm.ne' c,
    RectangleReciprocalWedgeIntegral_I_mul_integral_div_add_mul_I hwRe.ne' c,
    RectangleReciprocalWedgeIntegral_I_mul_integral_div_add_mul_I hzRe.ne c]
  have h₁ := RectangleReciprocalWedgeIntegral_arctan_div_neg_eq_add_of_div_neg
    hwRe.ne' hzIm.ne (div_neg_of_pos_of_neg hwRe hzIm)
  have h₂ := RectangleReciprocalWedgeIntegral_arctan_div_neg_eq_sub_of_div_pos
    hwRe.ne' hwIm.ne' (div_pos hwRe hwIm)
  have h₃ := RectangleReciprocalWedgeIntegral_arctan_div_neg_eq_sub_of_div_pos
    hzRe.ne hzIm.ne (div_pos_of_neg_of_neg hzRe hzIm)
  have h₄ := RectangleReciprocalWedgeIntegral_arctan_div_neg_eq_add_of_div_neg
    hzRe.ne hwIm.ne' (div_neg_of_neg_of_pos hzRe hwIm)
  rw [h₁, h₂, h₃, h₄]
  push_cast
  ring_nf

theorem wedgeIntegral_add_wedgeIntegral_div_sub_eq_two_pi_I_mul
    (z w p c : ℂ)
    (hzRe : z.re < p.re) (hpRe : p.re < w.re)
    (hzIm : z.im < p.im) (hpIm : p.im < w.im) :
    Complex.wedgeIntegral z w (fun s => c / (s - p)) +
        Complex.wedgeIntegral w z (fun s => c / (s - p)) =
      2 * Real.pi * I * c := by
  rw [wedgeIntegral_comp_sub (fun s => c / s) z w p,
    wedgeIntegral_comp_sub (fun s => c / s) w z p]
  apply RectangleReciprocalWedgeIntegral_wedgeIntegral_add_wedgeIntegral_div_of_straddles_zero
  · simpa using sub_neg.mpr hzRe
  · simpa using sub_pos.mpr hpRe
  · simpa using sub_neg.mpr hzIm
  · simpa using sub_pos.mpr hpIm

end BoundedGaps.Maynard

end

/-! ## Goldfeld's finite contour rectangle

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldContourRectangle`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set

open scoped Interval

noncomputable def goldfeldContourAnalyticRemainder
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x : ℝ) (s : ℂ) : ℂ :=
  dslope (goldfeldContourNumerator chi1 chi beta x)
    (goldfeldShiftedZetaPole beta) s

noncomputable def goldfeldTruncatedVerticalIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha T : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ t in (-T)..T,
      goldfeldContourIntegrand chi1 chi beta x
        ((alpha : ℂ) + t * I)

noncomputable def goldfeldTruncatedLowerIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x T : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
    (-(∫ sigma in (-1)..2,
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)))

noncomputable def goldfeldTruncatedUpperIntegral
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x T : ℝ) : ℂ :=
  ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
    ∫ sigma in (-1)..2,
      goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)

theorem differentiable_goldfeldContourAnalyticRemainder
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    {chi1 : DirichletCharacter ℂ q1}
    {chi : DirichletCharacter ℂ q}
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ
      (goldfeldContourAnalyticRemainder chi1 chi beta x) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope Filter.univ_mem).2
    (differentiable_goldfeldContourNumerator
      hchi1 hchi hcross beta hx).differentiableOn

theorem goldfeldRegularizedContourIntegrand_eq_remainder_add
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : beta < 1)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    {s : ℂ} (hs : s ≠ goldfeldShiftedZetaPole beta) :
    goldfeldRegularizedContourIntegrand chi1 chi beta x s =
      goldfeldContourAnalyticRemainder chi1 chi beta x s +
        goldfeldContourResidue chi1 chi beta x /
          (s - goldfeldShiftedZetaPole beta) := by
  have hnum := sub_smul_dslope
    (goldfeldContourNumerator chi1 chi beta x)
    (goldfeldShiftedZetaPole beta) s
  have hp := goldfeldContourNumerator_apply_shiftedZetaPole
    chi1 chi (x := x) hbeta hzero
  rw [hp] at hnum
  unfold goldfeldRegularizedContourIntegrand
    goldfeldContourAnalyticRemainder
  have hsub : s - goldfeldShiftedZetaPole beta ≠ 0 :=
    sub_ne_zero.mpr hs
  simp only [smul_eq_mul] at hnum
  apply (div_eq_iff hsub).2
  rw [add_mul, div_mul_cancel₀ _ hsub]
  calc
    goldfeldContourNumerator chi1 chi beta x s =
        (goldfeldContourNumerator chi1 chi beta x s -
          goldfeldContourResidue chi1 chi beta x) +
          goldfeldContourResidue chi1 chi beta x := by ring
    _ = (s - goldfeldShiftedZetaPole beta) *
          dslope (goldfeldContourNumerator chi1 chi beta x)
            (goldfeldShiftedZetaPole beta) s +
          goldfeldContourResidue chi1 chi beta x := by rw [hnum]
    _ = dslope (goldfeldContourNumerator chi1 chi beta x)
          (goldfeldShiftedZetaPole beta) s *
          (s - goldfeldShiftedZetaPole beta) +
          goldfeldContourResidue chi1 chi beta x := by ring

private lemma GoldfeldContourRectangle_continuous_horizontal_principal_part
    (c p : ℂ) (y : ℝ) (hy : y ≠ p.im) :
    Continuous (fun t : ℝ => c / ((t : ℂ) + y * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_ofReal.add (continuous_const.mul continuous_const)).sub
      continuous_const)
  intro t
  apply sub_ne_zero.mpr
  intro h
  apply hy
  simpa using congrArg Complex.im h

private lemma GoldfeldContourRectangle_continuous_vertical_principal_part
    (c p : ℂ) (x : ℝ) (hx : x ≠ p.re) :
    Continuous (fun t : ℝ => c / ((x : ℂ) + t * I - p)) := by
  apply Continuous.div continuous_const
    ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const)
  intro t
  apply sub_ne_zero.mpr
  intro h
  apply hx
  simpa using congrArg Complex.re h

private theorem GoldfeldContourRectangle_rectangle_boundary_eq_two_pi_I_mul_of_decomposition
    (f F : ℂ → ℂ) (z w p c : ℂ)
    (hF : Differentiable ℂ F)
    (hdecomp : ∀ s, s ≠ p → f s = F s + c / (s - p))
    (hzRe : z.re < p.re) (hpRe : p.re < w.re)
    (hzIm : z.im < p.im) (hpIm : p.im < w.im) :
    Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f =
      (2 * Real.pi * I) * c := by
  let G : ℂ → ℂ := fun s => c / (s - p)
  have hFcontinuous : Continuous F := hF.continuous
  have hFbottom : IntervalIntegrable
      (fun t : ℝ => F ((t : ℂ) + z.im * I)) volume z.re w.re :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFtop : IntervalIntegrable
      (fun t : ℝ => F ((t : ℂ) + w.im * I)) volume w.re z.re :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFright : IntervalIntegrable
      (fun t : ℝ => F ((w.re : ℂ) + t * I)) volume z.im w.im :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hFleft : IntervalIntegrable
      (fun t : ℝ => F ((z.re : ℂ) + t * I)) volume w.im z.im :=
    (hFcontinuous.comp (by fun_prop)).intervalIntegrable _ _
  have hGbottom : IntervalIntegrable
      (fun t : ℝ => G ((t : ℂ) + z.im * I)) volume z.re w.re := by
    exact (GoldfeldContourRectangle_continuous_horizontal_principal_part c p z.im
      (ne_of_lt hzIm)).intervalIntegrable _ _
  have hGtop : IntervalIntegrable
      (fun t : ℝ => G ((t : ℂ) + w.im * I)) volume w.re z.re := by
    exact (GoldfeldContourRectangle_continuous_horizontal_principal_part c p w.im
      (ne_of_gt hpIm)).intervalIntegrable _ _
  have hGright : IntervalIntegrable
      (fun t : ℝ => G ((w.re : ℂ) + t * I)) volume z.im w.im := by
    exact (GoldfeldContourRectangle_continuous_vertical_principal_part c p w.re
      (ne_of_gt hpRe)).intervalIntegrable _ _
  have hGleft : IntervalIntegrable
      (fun t : ℝ => G ((z.re : ℂ) + t * I)) volume w.im z.im := by
    exact (GoldfeldContourRectangle_continuous_vertical_principal_part c p z.re
      (ne_of_lt hzRe)).intervalIntegrable _ _
  have hnotBottom (t : ℝ) : (t : ℂ) + z.im * I ≠ p := by
    intro h
    exact (ne_of_lt hzIm) (by simpa using congrArg Complex.im h)
  have hnotTop (t : ℝ) : (t : ℂ) + w.im * I ≠ p := by
    intro h
    exact (ne_of_gt hpIm) (by simpa using congrArg Complex.im h)
  have hnotRight (t : ℝ) : (w.re : ℂ) + t * I ≠ p := by
    intro h
    exact (ne_of_gt hpRe) (by simpa using congrArg Complex.re h)
  have hnotLeft (t : ℝ) : (z.re : ℂ) + t * I ≠ p := by
    intro h
    exact (ne_of_lt hzRe) (by simpa using congrArg Complex.re h)
  have hbottom :
      (∫ t : ℝ in z.re..w.re, f ((t : ℂ) + z.im * I)) =
        ∫ t : ℝ in z.re..w.re,
          F ((t : ℂ) + z.im * I) + G ((t : ℂ) + z.im * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotBottom t)
  have htop :
      (∫ t : ℝ in w.re..z.re, f ((t : ℂ) + w.im * I)) =
        ∫ t : ℝ in w.re..z.re,
          F ((t : ℂ) + w.im * I) + G ((t : ℂ) + w.im * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotTop t)
  have hright :
      (∫ t : ℝ in z.im..w.im, f ((w.re : ℂ) + t * I)) =
        ∫ t : ℝ in z.im..w.im,
          F ((w.re : ℂ) + t * I) + G ((w.re : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotRight t)
  have hleft :
      (∫ t : ℝ in w.im..z.im, f ((z.re : ℂ) + t * I)) =
        ∫ t : ℝ in w.im..z.im,
          F ((z.re : ℂ) + t * I) + G ((z.re : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hdecomp _ (hnotLeft t)
  have hzw : Complex.wedgeIntegral z w f =
      Complex.wedgeIntegral z w F + Complex.wedgeIntegral z w G := by
    simp only [Complex.wedgeIntegral]
    rw [hbottom, hright,
      intervalIntegral.integral_add hFbottom hGbottom,
      intervalIntegral.integral_add hFright hGright]
    simp only [smul_add]
    abel
  have hwz : Complex.wedgeIntegral w z f =
      Complex.wedgeIntegral w z F + Complex.wedgeIntegral w z G := by
    simp only [Complex.wedgeIntegral]
    rw [htop, hleft,
      intervalIntegral.integral_add hFtop hGtop,
      intervalIntegral.integral_add hFleft hGleft]
    simp only [smul_add]
    abel
  have hFzero : Complex.wedgeIntegral z w F +
      Complex.wedgeIntegral w z F = 0 := by
    have hconservative := hF.differentiableOn.isConservativeOn z w
      (fun _ _ => mem_univ _)
    rw [hconservative]
    simp
  have hGsum : Complex.wedgeIntegral z w G +
      Complex.wedgeIntegral w z G = (2 * Real.pi * I) * c := by
    exact wedgeIntegral_add_wedgeIntegral_div_sub_eq_two_pi_I_mul
      z w p c hzRe hpRe hzIm hpIm
  rw [hzw, hwz]
  calc
    (Complex.wedgeIntegral z w F + Complex.wedgeIntegral z w G) +
        (Complex.wedgeIntegral w z F + Complex.wedgeIntegral w z G) =
      (Complex.wedgeIntegral z w F + Complex.wedgeIntegral w z F) +
        (Complex.wedgeIntegral z w G + Complex.wedgeIntegral w z G) := by
          abel
    _ = (2 * Real.pi * I) * c := by rw [hFzero, hGsum, zero_add]

theorem goldfeldRegularizedContourIntegrand_rectangle_boundary_eq
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    (∫ sigma in (-1)..2,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I)) -
      (∫ sigma in (-1)..2,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I)) +
      I * (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I)) -
      I * (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I)) =
      (2 * Real.pi * I) *
        goldfeldContourResidue chi1 chi beta x := by
  let z : ℂ := (-1 : ℂ) - T * I
  let w : ℂ := (2 : ℂ) + T * I
  let p : ℂ := goldfeldShiftedZetaPole beta
  let f : ℂ → ℂ := goldfeldRegularizedContourIntegrand chi1 chi beta x
  let F : ℂ → ℂ := goldfeldContourAnalyticRemainder chi1 chi beta x
  let c : ℂ := goldfeldContourResidue chi1 chi beta x
  have hzRe : z.re < p.re := by
    simp [z, p, goldfeldShiftedZetaPole]
    linarith
  have hpRe : p.re < w.re := by
    simp [w, p, goldfeldShiftedZetaPole]
    linarith
  have hzIm : z.im < p.im := by
    simp [z, p, goldfeldShiftedZetaPole]
    linarith
  have hpIm : p.im < w.im := by
    simp [w, p, goldfeldShiftedZetaPole]
    linarith
  have hboundary := GoldfeldContourRectangle_rectangle_boundary_eq_two_pi_I_mul_of_decomposition
    f F z w p c
    (differentiable_goldfeldContourAnalyticRemainder
      hchi1 hchi hcross beta hx)
    (fun s hs => goldfeldRegularizedContourIntegrand_eq_remainder_add
      chi1 chi hbeta1 hzero hs)
    hzRe hpRe hzIm hpIm
  rw [Complex.wedgeIntegral_add_wedgeIntegral_eq] at hboundary
  simpa [f, F, c, z, w, p, smul_eq_mul, sub_eq_add_neg] using hboundary

theorem goldfeldContourIntegrand_truncated_rectangle_decomposition
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x T : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 0 < x) (hT : 1 ≤ T)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldTruncatedVerticalIntegral chi1 chi beta x 2 T =
      goldfeldTruncatedLowerIntegral chi1 chi beta x T +
        goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1) T +
        goldfeldTruncatedUpperIntegral chi1 chi beta x T +
        goldfeldContourResidue chi1 chi beta x := by
  have hboundary :=
    goldfeldRegularizedContourIntegrand_rectangle_boundary_eq
      chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hT hzero
  have hhorizontal :=
    goldfeldRegularizedContourIntegrand_eq_intervalIntegral_goldfeldContourIntegrand_horizontal
      (chi1 := chi1) (chi := chi) (x := x) hzero hT
  have hright :
      (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I)) =
      ∫ t in (-T)..T,
        goldfeldContourIntegrand chi1 chi beta x
          ((2 : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
      chi1 chi hzero (by
        intro hs
        have hre := congrArg Complex.re hs
        norm_num at hre)
      (by
        intro hs
        have hre := congrArg Complex.re hs
        simp [goldfeldShiftedZetaPole] at hre
        linarith)
  have hleft :
      (∫ t in (-T)..T,
        goldfeldRegularizedContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I)) =
      ∫ t in (-T)..T,
        goldfeldContourIntegrand chi1 chi beta x
          ((-1 : ℂ) + t * I) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact goldfeldRegularizedContourIntegrand_eq_contourIntegrand
      chi1 chi hzero (by
        intro hs
        have hre := congrArg Complex.re hs
        norm_num at hre)
      (by
        intro hs
        have hre := congrArg Complex.re hs
        simp [goldfeldShiftedZetaPole] at hre
        linarith)
  rw [hhorizontal.2, hhorizontal.1, hright, hleft] at hboundary
  let lower : ℂ := ∫ sigma in (-1)..2,
    goldfeldContourIntegrand chi1 chi beta x
      ((sigma : ℂ) - T * I)
  let upper : ℂ := ∫ sigma in (-1)..2,
    goldfeldContourIntegrand chi1 chi beta x
      ((sigma : ℂ) + T * I)
  let right : ℂ := ∫ t in (-T)..T,
    goldfeldContourIntegrand chi1 chi beta x
      ((2 : ℂ) + t * I)
  let left : ℂ := ∫ t in (-T)..T,
    goldfeldContourIntegrand chi1 chi beta x
      ((-1 : ℂ) + t * I)
  change lower - upper + I * right - I * left =
    (2 * Real.pi * I) * goldfeldContourResidue chi1 chi beta x at hboundary
  have hIright :
      I * right =
        (2 * Real.pi * I) * goldfeldContourResidue chi1 chi beta x -
          lower + upper + I * left := by
    linear_combination hboundary
  have hmainMul :
      -I * ((2 * Real.pi * I) *
        goldfeldContourResidue chi1 chi beta x) =
        (((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x := by
    calc
      _ = (-I * I) * ((((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x) := by
        push_cast
        ring
      _ = _ := by rw [neg_mul, I_mul_I]; simp
  have hleftMul : -I * (I * left) = left := by
    rw [← mul_assoc, neg_mul, I_mul_I]
    simp
  have hrightEq :
      right = (((2 * Real.pi : ℝ) : ℂ)) *
          goldfeldContourResidue chi1 chi beta x +
        I * lower - I * upper + left := by
    calc
      _ = -I * (I * right) := by
        rw [← mul_assoc, neg_mul, I_mul_I]
        simp
      _ = -I * ((2 * Real.pi * I) *
          goldfeldContourResidue chi1 chi beta x -
          lower + upper + I * left) := by rw [hIright]
      _ = _ := by
        rw [mul_add, mul_add, mul_sub, hmainMul, hleftMul]
        ring
  simp only [goldfeldTruncatedVerticalIntegral,
    goldfeldTruncatedLowerIntegral, goldfeldTruncatedUpperIntegral]
  norm_num only [ofReal_neg, ofReal_one]
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹) * right =
    ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) * (-lower) +
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) * left +
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) * upper +
      goldfeldContourResidue chi1 chi beta x
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast Real.two_pi_pos.ne'
  rw [hrightEq]
  field_simp [hpi, I_ne_zero]
  simp [mul_add, mul_sub, ← mul_assoc, I_mul_I]
  ring

end BoundedGaps.Maynard

end

/-! ## Goldfeld horizontal-edge integral limits

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldHorizontalEdgeLimit`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex MeasureTheory Set Filter

open scoped Interval Topology

private theorem GoldfeldHorizontalEdgeLimit_norm_intervalIntegral_le_const_of_intervalIntegrable
    {f : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b)
    (hpoint : ∀ x ∈ Icc a b, ‖f x‖ ≤ M) :
    ‖∫ x in a..b, f x‖ ≤ M * (b - a) := by
  calc
    ‖∫ x in a..b, f x‖ ≤ ∫ x in a..b, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _x in a..b, M :=
      intervalIntegral.integral_mono_on hab hf.norm
        intervalIntegrable_const hpoint
    _ = M * (b - a) := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
      ring

theorem exists_norm_intervalIntegral_goldfeldContourIntegrand_horizontal_le :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x T : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x → 1 ≤ T →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            (‖∫ sigma in (-1)..2,
              goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) + T * I)‖ ≤
                3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) ∧
            (‖∫ sigma in (-1)..2,
              goldfeldContourIntegrand chi1 chi beta x
                ((sigma : ℂ) - T * I)‖ ≤
                3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) := by
  obtain ⟨A, hA, C, hC, hpoint⟩ :=
    exists_norm_goldfeldContourIntegrand_horizontal_le
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x T hbeta0 hbeta1 hx hT hzero
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTabs : 1 ≤ |T| := by simpa [abs_of_pos hTpos] using hT
  have hraw := intervalIntegrable_goldfeldContourIntegrand_horizontal
    (beta := beta) hchi1 hchi hcross (zero_lt_one.trans_le hx) hT hzero
  have hplusBound : ∀ sigma ∈ Icc (-(1 : ℝ)) 2,
      ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) + T * I)‖ ≤
        C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by
    intro sigma hsigma
    exact hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x sigma T hbeta0 hbeta1 hx hsigma hTabs
  have hminusBound : ∀ sigma ∈ Icc (-(1 : ℝ)) 2,
      ‖goldfeldContourIntegrand chi1 chi beta x
        ((sigma : ℂ) - T * I)‖ ≤
        C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by
    intro sigma hsigma
    have h := hpoint q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
      beta x sigma (-T) hbeta0 hbeta1 hx hsigma
      (by simpa [abs_of_pos hTpos, abs_neg] using hT)
    simpa [sub_eq_add_neg, abs_neg] using h
  have hplus := GoldfeldHorizontalEdgeLimit_norm_intervalIntegral_le_const_of_intervalIntegrable
    (by norm_num : (-1 : ℝ) ≤ 2) hraw.1 hplusBound
  have hminus := GoldfeldHorizontalEdgeLimit_norm_intervalIntegral_le_const_of_intervalIntegrable
    (by norm_num : (-1 : ℝ) ≤ 2) hraw.2 hminusBound
  constructor
  · calc
      ‖∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) + T * I)‖ ≤
          (C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) *
            ((2 : ℝ) - (-1)) := hplus
      _ = 3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by ring
  · calc
      ‖∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) - T * I)‖ ≤
          (C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2) *
            ((2 : ℝ) - (-1)) := hminus
      _ = 3 * C * (q : ℝ) ^ A * x ^ 2 / (1 + |T|) ^ 2 := by ring

theorem exists_tendsto_goldfeldContourIntegrand_horizontal_integrals_zero :
    ∃ A : ℕ, 57 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          DirichletCharacter.mul chi1 chi ≠ 1 →
          ∀ (beta x : ℝ),
            0 ≤ beta → beta ≤ 1 → 1 ≤ x →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            Tendsto
              (fun T : ℝ => ∫ sigma in (-1)..2,
                goldfeldContourIntegrand chi1 chi beta x
                  ((sigma : ℂ) + T * I)) atTop (𝓝 0) ∧
            Tendsto
              (fun T : ℝ => -(∫ sigma in (-1)..2,
                goldfeldContourIntegrand chi1 chi beta x
                  ((sigma : ℂ) - T * I))) atTop (𝓝 0) := by
  obtain ⟨A, hA, C, hC, hbound⟩ :=
    exists_norm_intervalIntegral_goldfeldContourIntegrand_horizontal_le
  refine ⟨A, hA, C, hC, ?_⟩
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi hcross
    beta x hbeta0 hbeta1 hx hzero
  let K : ℝ := 3 * C * (q : ℝ) ^ A * x ^ 2
  have hlinear : Tendsto (fun T : ℝ => 1 + T) atTop atTop := by
    simpa [add_comm] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop))
  have hsquare : Tendsto (fun T : ℝ => (1 + T) ^ 2) atTop atTop := by
    have h := tendsto_mul_self_atTop.comp hlinear
    simpa [Function.comp_def, pow_two] using h
  have hdecay : Tendsto (fun T : ℝ => K / (1 + T) ^ 2)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsquare
  have hupperNorm : Tendsto
      (fun T : ℝ => ‖∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) + T * I)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun T : ℝ => K / (1 + T) ^ 2)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have h := (hbound q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
        beta x T hbeta0 hbeta1 hx hT hzero).1
      simpa [K, abs_of_nonneg (zero_le_one.trans hT)] using h
    · exact hdecay
  have hlowerNorm : Tendsto
      (fun T : ℝ => ‖-(∫ sigma in (-1)..2,
        goldfeldContourIntegrand chi1 chi beta x
          ((sigma : ℂ) - T * I))‖) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun T : ℝ => K / (1 + T) ^ 2)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have h := (hbound q1 q hq1 hq1q chi1 chi hchi1 hchi hcross
        beta x T hbeta0 hbeta1 hx hT hzero).2
      simpa [K, norm_neg, abs_of_nonneg (zero_le_one.trans hT)] using h
    · exact hdecay
  exact ⟨tendsto_zero_iff_norm_tendsto_zero.mpr hupperNorm,
    tendsto_zero_iff_norm_tendsto_zero.mpr hlowerNorm⟩

end BoundedGaps.Maynard

end

/-! ## Goldfeld's complete contour displacement

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldContourLimit`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex MeasureTheory Filter

open scoped Topology

private theorem GoldfeldContourLimit_continuous_goldfeldRightLineMultiplier
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      goldfeldFourFactorLFunction chi1 chi
          (((2 : ℂ) + t * I) + (beta : ℂ)) *
        (x : ℂ) ^ ((2 : ℂ) + t * I)) := by
  let s : ℝ → ℂ := fun t => (2 : ℂ) + t * I
  have hs : Continuous s := by fun_prop
  have hshift : Continuous (fun t : ℝ => s t + (beta : ℂ)) :=
    hs.add continuous_const
  have hnotOne (t : ℝ) : s t + (beta : ℂ) ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hzeta : Continuous (fun t : ℝ =>
      riemannZeta (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (differentiableAt_riemannZeta (hnotOne t)).continuousAt.comp
        (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hchi1 : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction chi1
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hchi : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction chi
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hcross : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) := by
    rw [continuous_iff_continuousAt]
    intro t
    simpa [Function.comp_def] using
      (DirichletCharacter.differentiableAt_LFunction
        (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ)) (.inl (hnotOne t))).continuousAt.comp
          (f := fun u : ℝ => s u + (beta : ℂ)) hshift.continuousAt
  have hxpow : Continuous (fun t : ℝ => (x : ℂ) ^ (s t)) :=
    continuous_const.cpow hs fun _ => Complex.ofReal_mem_slitPlane.mpr hx
  have hfour := (((hzeta.mul hchi1).mul hchi).mul hcross)
  change Continuous (fun t : ℝ =>
    (((riemannZeta (s t + (beta : ℂ)) *
      DirichletCharacter.LFunction chi1 (s t + (beta : ℂ))) *
      DirichletCharacter.LFunction chi (s t + (beta : ℂ))) *
      DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
        (s t + (beta : ℂ))) * (x : ℂ) ^ (s t))
  exact hfour.mul hxpow

theorem goldfeldContourIntegrand_two_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) 2 := by
  let a : ℕ → ℂ := goldfeldBetaCoefficient chi1 chi beta
  let s : ℝ → ℂ := fun t => (2 : ℂ) + t * I
  let phiLine : ℝ → ℂ := fun t => goldfeldRawMellin (s t)
  let multiplier : ℝ → ℂ := fun t =>
    goldfeldFourFactorLFunction chi1 chi (s t + (beta : ℂ)) *
      (x : ℂ) ^ (s t)
  have hsum : LSeriesSummable a (2 : ℂ) := by
    apply (goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := (2 : ℂ)) ?_).LSeriesSummable
    norm_num
    linarith
  let K : ℝ := ∑' n : ℕ, ‖LSeries.term a (2 : ℂ) n‖
  have hfactor (t : ℝ) :
      ‖goldfeldFourFactorLFunction chi1 chi
        (s t + (beta : ℂ))‖ ≤ K := by
    have hsReal : 1 < ((s t + (beta : ℂ))).re := by
      simp [s]
      linarith
    have hseries := goldfeldBetaCoefficient_LSeriesHasSum
      chi1 chi beta (s := s t) hsReal
    have hline : LSeriesSummable a (s t) := by
      simpa [a] using hseries.LSeriesSummable
    have hlineNorm : Summable fun n : ℕ => ‖LSeries.term a (s t) n‖ :=
      summable_norm_iff.mpr hline
    calc
      ‖goldfeldFourFactorLFunction chi1 chi
          (s t + (beta : ℂ))‖ = ‖LSeries a (s t)‖ := by
            rw [hseries.LSeries_eq]
      _ ≤ ∑' n : ℕ, ‖LSeries.term a (s t) n‖ :=
        norm_tsum_le_tsum_norm hlineNorm
      _ = K := by
        apply tsum_congr
        intro n
        simp only [LSeries.norm_term_eq]
        congr 2
        simp [s]
  have hmultiplierContinuous : Continuous multiplier := by
    simpa [multiplier, s] using
      GoldfeldContourLimit_continuous_goldfeldRightLineMultiplier chi1 chi hbeta hx
  have hmultiplierBound : ∀ᵐ t : ℝ, ‖multiplier t‖ ≤ K * x ^ 2 :=
    ae_of_all _ fun t => by
      simp only [multiplier, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      have hxpow : x ^ (s t).re = x ^ 2 := by
        rw [show (s t).re = 2 by simp [s], Real.rpow_two]
      rw [hxpow]
      exact mul_le_mul_of_nonneg_right (hfactor t) (sq_nonneg x)
  have hphi : Integrable phiLine := by
    simpa [phiLine, s, VerticalIntegrable] using
      (goldfeldRawMellin_verticalIntegrable (alpha := 2) (by norm_num))
  have hproduct : Integrable fun t => phiLine t * multiplier t :=
    hphi.mul_bdd hmultiplierContinuous.aestronglyMeasurable
      hmultiplierBound
  rw [VerticalIntegrable]
  refine hproduct.congr (ae_of_all _ fun t => ?_)
  change phiLine t * multiplier t =
    goldfeldContourIntegrand chi1 chi beta x (s t)
  have hPhi := goldfeldMellinContinuationData.agrees_on_right
    (s := s t) (by simp [s])
  rw [goldfeldContourIntegrand, hPhi]
  simp only [phiLine, multiplier, s]
  ring

private theorem GoldfeldContourLimit_tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta x alpha : ℝ)
    (hvertical : VerticalIntegrable
      (goldfeldContourIntegrand chi1 chi beta x) alpha) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x alpha)
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x alpha)) := by
  let f : ℝ → ℂ := fun t =>
    goldfeldContourIntegrand chi1 chi beta x
      ((alpha : ℂ) + t * I)
  have hraw : Integrable f := by
    simpa [VerticalIntegrable, f] using hvertical
  have hlimit := MeasureTheory.intervalIntegral_tendsto_integral hraw
    tendsto_neg_atTop_atBot tendsto_id
  have hnormalized := hlimit.const_mul (((2 * Real.pi : ℝ) : ℂ)⁻¹)
  change Tendsto
    (fun T : ℝ => (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      ∫ t in (-T)..T, f t) atTop
    (𝓝 ((((2 * Real.pi : ℝ) : ℂ)⁻¹) * ∫ t : ℝ, f t))
  exact hnormalized

theorem tendsto_goldfeldContourIntegrand_truncated_vertical_two
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    {beta x : ℝ} (hbeta : -1 < beta) (hx : 0 < x) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x 2)
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x 2)) :=
  GoldfeldContourLimit_tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    chi1 chi beta x 2
      (goldfeldContourIntegrand_two_verticalIntegrable
        chi1 chi hbeta hx)

theorem tendsto_goldfeldContourIntegrand_truncated_vertical_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ} (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1)
    (hx : 1 ≤ x) :
    Tendsto
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1))
      atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x (-1))) :=
  GoldfeldContourLimit_tendsto_goldfeldTruncatedVerticalIntegral_of_verticalIntegrable
    chi1 chi beta x (-1)
      (goldfeldContourIntegrand_leftLine_verticalIntegrable
        hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx)

theorem goldfeldVerticalIntegral_two_eq_residue_add_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldVerticalIntegral chi1 chi beta x 2 =
      goldfeldContourResidue chi1 chi beta x +
        goldfeldVerticalIntegral chi1 chi beta x (-1) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hright := tendsto_goldfeldContourIntegrand_truncated_vertical_two
    chi1 chi (show -1 < beta by linarith) hxpos
  have hleft := tendsto_goldfeldContourIntegrand_truncated_vertical_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1.le hx
  obtain ⟨_A, _hA, _C, _hC, hhorizontal⟩ :=
    exists_tendsto_goldfeldContourIntegrand_horizontal_integrals_zero
  have hedges := hhorizontal q1 q hq1 hq1q chi1 chi
    hchi1 hchi hcross beta x hbeta0 hbeta1.le hx hzero
  have hlower : Tendsto
      (goldfeldTruncatedLowerIntegral chi1 chi beta x)
      atTop (𝓝 0) := by
    have h := hedges.2.const_mul
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹)
    change Tendsto (fun T : ℝ =>
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
        (-(∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) - T * I)))) atTop (𝓝 0)
    simpa only [mul_zero] using h
  have hupper : Tendsto
      (goldfeldTruncatedUpperIntegral chi1 chi beta x)
      atTop (𝓝 0) := by
    have h := hedges.1.const_mul
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹)
    change Tendsto (fun T : ℝ =>
      ((((2 * Real.pi : ℝ) : ℂ) * I)⁻¹) *
        ∫ sigma in (-1)..2,
          goldfeldContourIntegrand chi1 chi beta x
            ((sigma : ℂ) + T * I)) atTop (𝓝 0)
    simpa only [mul_zero] using h
  let rhs : ℝ → ℂ := fun T =>
    goldfeldTruncatedLowerIntegral chi1 chi beta x T +
      goldfeldTruncatedVerticalIntegral chi1 chi beta x (-1) T +
      goldfeldTruncatedUpperIntegral chi1 chi beta x T +
      goldfeldContourResidue chi1 chi beta x
  have hrhs : Tendsto rhs atTop
      (𝓝 (goldfeldVerticalIntegral chi1 chi beta x (-1) +
        goldfeldContourResidue chi1 chi beta x)) := by
    have hconstant : Tendsto
        (fun _ : ℝ => goldfeldContourResidue chi1 chi beta x) atTop
        (𝓝 (goldfeldContourResidue chi1 chi beta x)) :=
      tendsto_const_nhds
    have h := ((hlower.add hleft).add hupper).add hconstant
    simpa [rhs] using h
  have heq :
      (goldfeldTruncatedVerticalIntegral chi1 chi beta x 2) =ᶠ[atTop]
        rhs := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact goldfeldContourIntegrand_truncated_rectangle_decomposition
      chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hxpos hT hzero
  have hright' := hright.congr' heq
  have hresult := tendsto_nhds_unique hright' hrhs
  simpa [add_comm] using hresult

theorem goldfeldSmoothedSum_eq_residue_add_verticalIntegral_neg_one
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    goldfeldSmoothedSum chi1 chi beta x =
      goldfeldContourResidue chi1 chi beta x +
        goldfeldVerticalIntegral chi1 chi beta x (-1) := by
  rw [goldfeldSmoothedSum_eq_verticalIntegral_two
    chi1 chi (show -1 < beta by linarith) hx]
  exact goldfeldVerticalIntegral_two_eq_residue_add_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hzero

end BoundedGaps.Maynard

end

/-! ## Polya--Vinogradov for imprimitive prefixes

Source module `BoundedGaps.BombieriVinogradov.Analytic.ImprimitivePolyaVinogradovPrefix`. -/

noncomputable section

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

private theorem ImprimitivePolyaVinogradovPrefix_card_divisors_le_two_mul_sqrt
    {n : ℕ} (hn : 0 < n) :
    n.divisors.card ≤ 2 * Nat.sqrt n := by
  classical
  let small := n.divisors.filter fun d ↦ d ≤ Nat.sqrt n
  let large := n.divisors.filter fun d ↦ ¬d ≤ Nat.sqrt n
  have hsmall : small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    apply Finset.card_le_card
    intro d hd
    simp only [small, Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
  have hlarge : large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
    refine Finset.card_le_card_of_injOn (fun d ↦ n / d) ?_ ?_
    · intro d hd
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd
      have hdDvd : d ∣ n := (Nat.mem_divisors.mp hd.1).1
      have hdPos : 0 < d := Nat.pos_of_mem_divisors hd.1
      have hquotPos : 0 < n / d :=
        Nat.div_pos (Nat.le_of_dvd hn hdDvd) hdPos
      have hfactor : n = d * (n / d) := (Nat.mul_div_cancel' hdDvd).symm
      exact Finset.mem_Icc.mpr
        ⟨hquotPos, (Nat.le_sqrt_of_eq_mul hfactor).resolve_left hd.2⟩
    · intro d₁ hd₁ d₂ hd₂ heq
      simp only [large, Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
      have hd₁Dvd : d₁ ∣ n := (Nat.mem_divisors.mp hd₁.1).1
      have hd₂Dvd : d₂ ∣ n := (Nat.mem_divisors.mp hd₂.1).1
      have hquotPos : 0 < n / d₁ :=
        Nat.div_pos (Nat.le_of_dvd hn hd₁Dvd)
          (Nat.pos_of_mem_divisors hd₁.1)
      change n / d₁ = n / d₂ at heq
      apply Nat.mul_right_cancel hquotPos
      calc
        d₁ * (n / d₁) = n := Nat.mul_div_cancel' hd₁Dvd
        _ = d₂ * (n / d₂) := (Nat.mul_div_cancel' hd₂Dvd).symm
        _ = d₂ * (n / d₁) := by rw [heq]
  have hsmall' : small.card ≤ Nat.sqrt n := by
    calc
      small.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hsmall
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hlarge' : large.card ≤ Nat.sqrt n := by
    calc
      large.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := hlarge
      _ = Nat.sqrt n := by rw [Nat.card_Icc]; omega
  have hpartition : small.card + large.card = n.divisors.card := by
    simpa [small, large] using
      (Finset.card_filter_add_card_filter_not (s := n.divisors)
        (fun d ↦ d ≤ Nat.sqrt n))
  omega

private theorem ImprimitivePolyaVinogradovPrefix_divisors_gcd_eq_filter
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (n.gcd r).divisors = r.divisors.filter (fun a ↦ a ∣ n) := by
  ext a
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨ha, _⟩
    exact ⟨⟨ha.trans (Nat.gcd_dvd_right n r), hr.ne'⟩,
      ha.trans (Nat.gcd_dvd_left n r)⟩
  · rintro ⟨⟨har, _⟩, han⟩
    exact ⟨Nat.dvd_gcd han har, hgcd.ne'⟩

private theorem ImprimitivePolyaVinogradovPrefix_sum_moebius_divisors_eq_coprimeIndicator
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r) :
    (∑ a ∈ r.divisors,
      if a ∣ n then
        ((ArithmeticFunction.moebius a : ℤ) : ℂ)
      else 0) =
      if n.Coprime r then 1 else 0 := by
  have hgcd : 0 < n.gcd r := Nat.gcd_pos_of_pos_left r hn
  calc
    (∑ a ∈ r.divisors,
        if a ∣ n then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) =
        ∑ a ∈ r.divisors.filter (fun a ↦ a ∣ n),
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [Finset.sum_filter]
    _ = ∑ a ∈ (n.gcd r).divisors,
          ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
      rw [ImprimitivePolyaVinogradovPrefix_divisors_gcd_eq_filter hn hr]
    _ = ∑ a ∈ (n.gcd r).divisors,
          (ArithmeticFunction.moebius : ArithmeticFunction ℂ) a := by
      simp
    _ = (((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) (n.gcd r)) := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (1 : ArithmeticFunction ℂ) (n.gcd r) := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n.Coprime r then 1 else 0 := by
      by_cases hcop : n.Coprime r <;> simp [hcop]

private theorem ImprimitivePolyaVinogradovPrefix_character_eq_primitive_mul_coprimeIndicator
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (n : ℕ) :
    chi n = chi.primitiveCharacter n *
      (if n.Coprime (q / chi.conductor) then 1 else 0) := by
  have hdvd : chi.conductor ∣ q := chi.conductor_dvd_level
  have hfactor : chi.conductor * (q / chi.conductor) = q :=
    Nat.mul_div_cancel' hdvd
  by_cases hnr : n.Coprime (q / chi.conductor)
  · rw [if_pos hnr, mul_one]
    by_cases hnd : n.Coprime chi.conductor
    · have hnq : n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact ⟨hnd, hnr⟩
      simpa only [Int.cast_natCast] using
        (chi.primitiveCharacter_apply_of_isCoprime
          (Nat.isCoprime_iff_coprime.mpr hnq)).symm
    · have hnq : ¬n.Coprime q := by
        rw [← hfactor, Nat.coprime_mul_iff_right]
        exact fun h ↦ hnd h.1
      have hchiZero : chi (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
          (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))
      have hpsiZero : chi.primitiveCharacter (n : ℤ) = 0 :=
        (DirichletCharacter.apply_eq_zero_iff chi.primitiveCharacter (n : ℤ)).2
          (fun h ↦ hnd (Nat.isCoprime_iff_coprime.mp h))
      simpa only [Int.cast_natCast] using hchiZero.trans hpsiZero.symm
  · rw [if_neg hnr, mul_zero]
    have hnq : ¬n.Coprime q := by
      rw [← hfactor, Nat.coprime_mul_iff_right]
      exact fun h ↦ hnr h.2
    simpa only [Int.cast_natCast] using
      (DirichletCharacter.apply_eq_zero_iff chi (n : ℤ)).2
        (fun h ↦ hnq (Nat.isCoprime_iff_coprime.mp h))

private theorem ImprimitivePolyaVinogradovPrefix_sum_multiples_character
    {d a Y : ℕ} (ha : 0 < a) (psi : DirichletCharacter ℂ d) :
    (∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n), psi n) =
      ∑ m ∈ Finset.Icc 1 (Y / a), psi (a * m) := by
  classical
  refine Finset.sum_bij'
    (fun n _ ↦ n / a) (fun m _ ↦ a * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hnPos : 0 < n := zero_lt_one.trans_le hn.1.1
    exact Finset.mem_Icc.mpr
      ⟨Nat.div_pos (Nat.le_of_dvd hnPos hn.2) ha,
        Nat.div_le_div_right hn.1.2⟩
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos ha hm.1,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hm.2⟩,
        Nat.dvd_mul_right a m⟩
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m hm
    exact Nat.mul_div_cancel_left m ha
  · intro n hn
    simp only [Finset.mem_filter] at hn
    congr 1
    simpa only [Nat.cast_mul] using
      congrArg (fun k : ℕ ↦ (k : ZMod d))
        (Nat.mul_div_cancel' hn.2).symm

private theorem ImprimitivePolyaVinogradovPrefix_imprimitivePrefix_eq_divisorSum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (Y : ℕ) :
    dirichletCharacterIntervalSum 1 Y q chi =
      ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
  classical
  have hdPos : 0 < chi.conductor := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hrPos : 0 < q / chi.conductor :=
    Nat.div_pos
      (Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level) hdPos
  rw [dirichletCharacterIntervalSum]
  calc
    (∑ n ∈ Finset.Icc 1 Y, chi n) =
        ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (if n.Coprime (q / chi.conductor) then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact ImprimitivePolyaVinogradovPrefix_character_eq_primitive_mul_coprimeIndicator chi n
    _ = ∑ n ∈ Finset.Icc 1 Y,
          chi.primitiveCharacter n *
            (∑ a ∈ (q / chi.conductor).divisors,
              if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ImprimitivePolyaVinogradovPrefix_sum_moebius_divisors_eq_coprimeIndicator
        (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1) hrPos]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
          ∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ a ∈ (q / chi.conductor).divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
            chi.primitiveCharacter := by
      apply Finset.sum_congr rfl
      intro a ha
      have haPos : 0 < a := Nat.pos_of_mem_divisors ha
      calc
        (∑ n ∈ Finset.Icc 1 Y,
            chi.primitiveCharacter n *
              (if a ∣ n then
                ((ArithmeticFunction.moebius a : ℤ) : ℂ)
              else 0)) =
            ∑ n ∈ (Finset.Icc 1 Y).filter (fun n ↦ a ∣ n),
              chi.primitiveCharacter n *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro n hn
          by_cases han : a ∣ n <;> simp [han]
        _ = ∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter (a * m) *
                ((ArithmeticFunction.moebius a : ℤ) : ℂ) := by
          rw [← Finset.sum_mul, ImprimitivePolyaVinogradovPrefix_sum_multiples_character haPos,
            Finset.sum_mul]
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            (∑ m ∈ Finset.Icc 1 (Y / a),
              chi.primitiveCharacter m) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [map_mul]
          ring
        _ = (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) chi.conductor
              chi.primitiveCharacter := by
          rw [dirichletCharacterIntervalSum]

theorem norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (Y : ℕ) :
    ‖dirichletCharacterIntervalSum 1 Y q chi‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  let d := chi.conductor
  let r := q / d
  have hdPos : 0 < d := Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hdDvd : d ∣ q := chi.conductor_dvd_level
  have hfactor : d * r = q := Nat.mul_div_cancel' hdDvd
  have hrPos : 0 < r :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos q) hdDvd) hdPos
  have hdNeOne : d ≠ 1 := by
    intro hd
    exact hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd)
  have hd : 1 < d := by omega
  have hdLeq : d ≤ q := Nat.le_of_dvd (NeZero.pos q) hdDvd
  letI : NeZero d := ⟨hdPos.ne'⟩
  have hscalePos :
      0 < Real.sqrt (d : ℝ) * Real.log (d : ℝ) :=
    mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hdPos))
      (Real.log_pos (by exact_mod_cast hd))
  have hcard : r.divisors.card ≤ 2 * Nat.sqrt r :=
    ImprimitivePolyaVinogradovPrefix_card_divisors_le_two_mul_sqrt hrPos
  have hcardReal :
      (r.divisors.card : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by
    calc
      (r.divisors.card : ℝ) ≤ ((2 * Nat.sqrt r : ℕ) : ℝ) := by
        exact_mod_cast hcard
      _ = 2 * (Nat.sqrt r : ℝ) := by norm_num
      _ ≤ 2 * Real.sqrt (r : ℝ) := by
        gcongr
        exact Real.nat_sqrt_le_real_sqrt
  have hsqrt :
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) = Real.sqrt (q : ℝ) := by
    calc
      Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ) =
          Real.sqrt ((d : ℝ) * (r : ℝ)) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt (q : ℝ) := by rw [← Nat.cast_mul, hfactor]
  have hlog : Real.log (d : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hdPos) (by exact_mod_cast hdLeq)
  rw [ImprimitivePolyaVinogradovPrefix_imprimitivePrefix_eq_divisorSum chi Y]
  calc
    ‖∑ a ∈ r.divisors,
        (((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            chi.primitiveCharacter a) *
          dirichletCharacterIntervalSum 1 (Y / a) d
            chi.primitiveCharacter‖ ≤
        ∑ a ∈ r.divisors,
          ‖(((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a) *
            dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ r.divisors,
        Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hmu : ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ ≤ 1 := by
        rcases ArithmeticFunction.moebius_eq_or a with hzero | hone | hneg
        · simp [hzero]
        · simp [hone]
        · simp [hneg]
      have hcoeff :
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ ≤ 1 := by
        rw [norm_mul]
        calc
          ‖((ArithmeticFunction.moebius a : ℤ) : ℂ)‖ *
              ‖chi.primitiveCharacter a‖ ≤ 1 * 1 :=
            mul_le_mul hmu (chi.primitiveCharacter.norm_le_one a)
              (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      rw [norm_mul]
      calc
        ‖((ArithmeticFunction.moebius a : ℤ) : ℂ) *
              chi.primitiveCharacter a‖ *
            ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ ≤
            1 * ‖dirichletCharacterIntervalSum 1 (Y / a) d
              chi.primitiveCharacter‖ :=
          mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
        _ ≤ Real.sqrt (d : ℝ) * Real.log (d : ℝ) := by
          simpa using
            (norm_dirichletCharacterIntervalSum_lt_sqrt_mul_log
              hd chi.primitiveCharacter chi.primitiveCharacter_isPrimitive
              1 (Y / a)).le
    _ = (r.divisors.card : ℝ) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) := by simp
    _ ≤ (2 * Real.sqrt (r : ℝ)) *
        (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) :=
      mul_le_mul_of_nonneg_right hcardReal hscalePos.le
    _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by
      calc
        (2 * Real.sqrt (r : ℝ)) *
            (Real.sqrt (d : ℝ) * Real.log (d : ℝ)) =
            2 * (Real.sqrt (d : ℝ) * Real.sqrt (r : ℝ)) *
              Real.log (d : ℝ) := by ring
        _ = 2 * Real.sqrt (q : ℝ) * Real.log (d : ℝ) := by rw [hsqrt]
    _ ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      gcongr

end BoundedGaps.Maynard

end

/-! ## Partial summation for nonprincipal character prefixes

Source module `BoundedGaps.BombieriVinogradov.Analytic.CharacterPartialSummation`. -/

noncomputable section

open MeasureTheory Set

open scoped BigOperators

namespace BoundedGaps.Maynard

private noncomputable def CharacterPartialSummation_characterCumulative
    {q : ℕ} (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, chi (n : ZMod q)

private lemma CharacterPartialSummation_characterCumulative_eq_interval
    {q : ℕ} (hq : 1 < q) (chi : DirichletCharacter ℂ q) (t : ℝ) :
    CharacterPartialSummation_characterCumulative chi t =
      dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi := by
  rw [CharacterPartialSummation_characterCumulative, dirichletCharacterIntervalSum,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊t⌋₊), Finset.sum_cons]
  have hzero : chi ((0 : ℕ) : ZMod q) = 0 := by
    simpa only [Nat.cast_zero] using chi.map_zero' (Nat.ne_of_gt hq)
  rw [hzero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 ⌊t⌋₊]
  norm_num

private lemma CharacterPartialSummation_norm_characterCumulative_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (t : ℝ) :
    ‖CharacterPartialSummation_characterCumulative chi t‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  rw [CharacterPartialSummation_characterCumulative_eq_interval hq]
  exact norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
    hq chi hchi ⌊t⌋₊

private lemma CharacterPartialSummation_characterScale_nonneg {q : ℕ} (hq : 1 < q) :
    0 ≤ 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  exact mul_nonneg
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    (Real.log_pos (by exact_mod_cast hq)).le

private lemma CharacterPartialSummation_hasDerivAt_complexOfReal_inv {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ ((u : ℂ)⁻¹))
      (-((t : ℂ) ^ 2)⁻¹) t := by
  have hcomplex : HasDerivAt (fun z : ℂ ↦ z⁻¹)
      (-((t : ℂ) ^ 2)⁻¹) (t : ℂ) :=
    hasDerivAt_inv (by exact_mod_cast ht)
  exact hcomplex.comp_ofReal

private lemma CharacterPartialSummation_integrableOn_deriv_complexOfReal_inv
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc a b) := by
  let g : ℝ → ℂ := fun t ↦ -((t : ℂ) ^ 2)⁻¹
  have hgContinuous : ContinuousOn g (Icc a b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact Complex.continuous_ofReal.continuousOn.pow 2
    · intro t ht
      exact pow_ne_zero 2 (by exact_mod_cast (ha.trans_le ht.1).ne')
  apply hgContinuous.integrableOn_Icc.congr_fun _ measurableSet_Icc
  intro t ht
  exact (CharacterPartialSummation_hasDerivAt_complexOfReal_inv (ha.trans_le ht.1).ne').deriv.symm

private lemma CharacterPartialSummation_integral_Ioc_inv_sq
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t : ℝ in Ioc a b, (t ^ 2)⁻¹) = a⁻¹ - b⁻¹ := by
  have hdiff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻¹) t := by
    intro t ht
    apply differentiableAt_inv
    have ht' : t ∈ Icc a b := by
      simpa [Set.uIcc_of_le hab] using ht
    exact (ha.trans_le ht'.1).ne'
  have hint : IntervalIntegrable
      (deriv (fun u : ℝ ↦ u⁻¹)) volume a b := by
    rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
      funext u
      exact deriv_inv]
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀
    · exact continuousOn_id.pow 2
    · intro t ht
      have ht' : t ∈ Icc a b := by
        simpa [Set.uIcc_of_le hab] using ht
      exact pow_ne_zero 2 (ha.trans_le ht'.1).ne'
  have hfund := intervalIntegral.integral_deriv_eq_sub hdiff hint
  rw [intervalIntegral.integral_of_le hab] at hfund
  rw [show deriv (fun u : ℝ ↦ u⁻¹) = fun u ↦ -(u ^ 2)⁻¹ by
    funext u
    exact deriv_inv] at hfund
  rw [integral_neg] at hfund
  linarith

private lemma CharacterPartialSummation_integral_const_Ioc (C a b : ℝ) (hab : a ≤ b) :
    (∫ _t : ℝ in Ioc a b, C) = C * (b - a) := by
  rw [setIntegral_const, Measure.real_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  simp only [smul_eq_mul]
  ring

theorem norm_dirichletCharacterReciprocalIntervalSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x y : ℕ) (hx : 0 < x) :
    ‖∑ n ∈ Finset.Ioc x y,
      chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  by_cases hxy : x ≤ y
  · have hxReal : 0 < (x : ℝ) := by exact_mod_cast hx
    have hxyReal : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
    have hyReal : 0 < (y : ℝ) := hxReal.trans_le hxyReal
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hfDiff : ∀ t ∈ Icc (x : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t := by
      intro t ht
      exact (CharacterPartialSummation_hasDerivAt_complexOfReal_inv
        (hxReal.trans_le ht.1).ne').differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹))) (Icc (x : ℝ) y) :=
      CharacterPartialSummation_integrableOn_deriv_complexOfReal_inv hxReal
    have habel := sum_mul_eq_sub_sub_integral_mul'
      (f := fun t : ℝ ↦ ((t : ℂ)⁻¹))
      (c := fun n : ℕ ↦ chi (n : ZMod q)) hxy hfDiff hfInt
    have hrepresentation :
        (∑ n ∈ Finset.Ioc x y,
          chi (n : ZMod q) / (n : ℂ)) =
          ((y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
            (x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)) -
            ∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t := by
      simpa [CharacterPartialSummation_characterCumulative, div_eq_mul_inv, mul_comm] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
          CharacterPartialSummation_characterCumulative chi t) (Ioc (x : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) hxReal.le hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hReciprocalContinuous : ContinuousOn
        (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc (x : ℝ) y) := by
      apply ContinuousOn.inv₀
      · exact continuousOn_id.pow 2
      · intro t ht
        exact pow_ne_zero 2 (hxReal.trans_le ht.1).ne'
    have hMajorant : IntegrableOn
        (fun t : ℝ ↦ C * (t ^ 2)⁻¹) (Ioc (x : ℝ) y) :=
      (continuousOn_const.mul hReciprocalContinuous).integrableOn_Icc.mono_set
        Ioc_subset_Icc_self
    have hPoint : ∀ t ∈ Ioc (x : ℝ) y,
        ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
            CharacterPartialSummation_characterCumulative chi t‖ ≤ C * (t ^ 2)⁻¹ := by
      intro t ht
      have htPos : 0 < t := hxReal.trans ht.1
      rw [(CharacterPartialSummation_hasDerivAt_complexOfReal_inv htPos.ne').deriv, norm_mul]
      have hderivNorm : ‖-((t : ℂ) ^ 2)⁻¹‖ = (t ^ 2)⁻¹ := by
        rw [norm_neg, norm_inv, norm_pow, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos htPos]
      rw [hderivNorm]
      calc
        (t ^ 2)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi t‖ =
            ‖CharacterPartialSummation_characterCumulative chi t‖ * (t ^ 2)⁻¹ := mul_comm _ _
        _ ≤ C * (t ^ 2)⁻¹ := mul_le_mul_of_nonneg_right
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi t)
          (inv_nonneg.mpr (sq_nonneg t))
    have hIntegral :
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
      calc
        ‖∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
            ∫ t in Ioc (x : ℝ) y,
              ‖deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioc (x : ℝ) y, C * (t ^ 2)⁻¹ := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) := by
          rw [integral_const_mul, CharacterPartialSummation_integral_Ioc_inv_sq hxReal hxyReal]
    have hUpper :
        ‖(y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ ≤
          C * (y : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (y : ℝ)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ ≤
            (y : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi (y : ℝ))
          (inv_nonneg.mpr hyReal.le)
        _ = C * (y : ℝ)⁻¹ := mul_comm _ _
    have hLower :
        ‖(x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)‖ ≤
          C * (x : ℝ)⁻¹ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      calc
        (x : ℝ)⁻¹ * ‖CharacterPartialSummation_characterCumulative chi (x : ℝ)‖ ≤
            (x : ℝ)⁻¹ * C := mul_le_mul_of_nonneg_left
          (by simpa [C] using
            CharacterPartialSummation_norm_characterCumulative_le hq chi hchi (x : ℝ))
          (inv_nonneg.mpr hxReal.le)
        _ = C * (x : ℝ)⁻¹ := mul_comm _ _
    rw [hrepresentation]
    calc
      ‖((y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
          (x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)) -
          ∫ t in Ioc (x : ℝ) y,
            deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          (‖(y : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ +
            ‖(x : ℂ)⁻¹ * CharacterPartialSummation_characterCumulative chi (x : ℝ)‖) +
            ‖∫ t in Ioc (x : ℝ) y,
              deriv (fun u : ℝ ↦ ((u : ℂ)⁻¹)) t *
                CharacterPartialSummation_characterCumulative chi t‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (C * (y : ℝ)⁻¹ + C * (x : ℝ)⁻¹) +
          C * ((x : ℝ)⁻¹ - (y : ℝ)⁻¹) :=
        add_le_add (add_le_add hUpper hLower) hIntegral
      _ = 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
        dsimp [C]
        ring
  · have hyx : y ≤ x := Nat.le_of_not_ge hxy
    rw [Finset.Ioc_eq_empty_of_le hyx, Finset.sum_empty, norm_zero]
    have hNumerator :
        0 ≤ 4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      nlinarith [CharacterPartialSummation_characterScale_nonneg hq]
    exact div_nonneg hNumerator (by positivity)

theorem norm_dirichletCharacterWeightedPrefixSum_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (y : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 y,
      (n : ℂ) * chi (n : ZMod q)‖ ≤
      4 * (y : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  by_cases hy : y = 0
  · subst y
    simp
  · have hyPos : 0 < y := Nat.pos_of_ne_zero hy
    have hyOne : 1 ≤ y := hyPos
    have hyReal : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hyOne
    let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
    have hcastDeriv (t : ℝ) :
        HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := by
      simpa using (hasDerivAt_id (𝕜 := ℂ) (x := (t : ℂ))).comp_ofReal
    have hfDiff : ∀ t ∈ Icc (1 : ℝ) y,
        DifferentiableAt ℝ (fun u : ℝ ↦ (u : ℂ)) t := by
      intro t _
      exact (hcastDeriv t).differentiableAt
    have hfInt : IntegrableOn
        (deriv (fun u : ℝ ↦ (u : ℂ))) (Icc (1 : ℝ) y) := by
      apply (continuousOn_const : ContinuousOn
        (fun _t : ℝ ↦ (1 : ℂ)) (Icc (1 : ℝ) y)).integrableOn_Icc.congr_fun
        _ measurableSet_Icc
      intro t _
      exact (hcastDeriv t).deriv.symm
    have habel := sum_mul_eq_sub_integral_mul₀'
      (f := fun t : ℝ ↦ (t : ℂ))
      (c := fun n : ℕ ↦ chi (n : ZMod q))
      (by simpa only [Nat.cast_zero] using
        chi.map_zero' (Nat.ne_of_gt hq)) y hfDiff hfInt
    have hleft :
        (∑ n ∈ Finset.Icc 0 y,
          (n : ℂ) * chi (n : ZMod q)) =
          ∑ n ∈ Finset.Icc 1 y,
            (n : ℂ) * chi (n : ZMod q) := by
      rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le y), Finset.sum_cons]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      rw [← Finset.Icc_add_one_left_eq_Ioc 0 y]
      norm_num
    have hrepresentation :
        (∑ n ∈ Finset.Icc 1 y,
          (n : ℂ) * chi (n : ZMod q)) =
          (y : ℂ) * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
            ∫ t in Ioc (1 : ℝ) y,
              deriv (fun u : ℝ ↦ (u : ℂ)) t *
                CharacterPartialSummation_characterCumulative chi t := by
      rw [← hleft]
      simpa [CharacterPartialSummation_characterCumulative] using habel
    have hActual : IntegrableOn
        (fun t : ℝ ↦ deriv (fun u : ℝ ↦ (u : ℂ)) t *
          CharacterPartialSummation_characterCumulative chi t) (Ioc (1 : ℝ) y) := by
      apply (integrableOn_mul_sum_Icc
        (fun n : ℕ ↦ chi (n : ZMod q)) zero_le_one hfInt).mono_set
      exact Ioc_subset_Icc_self
    have hMajorant : IntegrableOn
        (fun _t : ℝ ↦ C) (Ioc (1 : ℝ) y) :=
      integrableOn_const measure_Ioc_lt_top.ne
    have hPoint : ∀ t ∈ Ioc (1 : ℝ) y,
        ‖deriv (fun u : ℝ ↦ (u : ℂ)) t *
            CharacterPartialSummation_characterCumulative chi t‖ ≤ C := by
      intro t _
      rw [(hcastDeriv t).deriv, one_mul]
      simpa [C] using CharacterPartialSummation_norm_characterCumulative_le hq chi hchi t
    have hIntegral :
        ‖∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          C * ((y : ℝ) - 1) := by
      calc
        ‖∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
            ∫ t in Ioc (1 : ℝ) y,
              ‖deriv (fun u : ℝ ↦ (u : ℂ)) t *
                CharacterPartialSummation_characterCumulative chi t‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _t in Ioc (1 : ℝ) y, C := by
          apply setIntegral_mono_ae_restrict hActual.norm hMajorant
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hPoint t ht
        _ = C * ((y : ℝ) - 1) := CharacterPartialSummation_integral_const_Ioc C 1 y hyReal
    have hEndpoint :
        ‖(y : ℂ) * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ ≤
          (y : ℝ) * C := by
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (by simpa [C] using
          CharacterPartialSummation_norm_characterCumulative_le hq chi hchi (y : ℝ))
        (by positivity)
    rw [hrepresentation]
    calc
      ‖(y : ℂ) * CharacterPartialSummation_characterCumulative chi (y : ℝ) -
          ∫ t in Ioc (1 : ℝ) y,
            deriv (fun u : ℝ ↦ (u : ℂ)) t *
              CharacterPartialSummation_characterCumulative chi t‖ ≤
          ‖(y : ℂ) * CharacterPartialSummation_characterCumulative chi (y : ℝ)‖ +
            ‖∫ t in Ioc (1 : ℝ) y,
              deriv (fun u : ℝ ↦ (u : ℂ)) t *
                CharacterPartialSummation_characterCumulative chi t‖ := norm_sub_le _ _
      _ ≤ (y : ℝ) * C + C * ((y : ℝ) - 1) :=
        add_le_add hEndpoint hIntegral
      _ ≤ 4 * (y : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
        dsimp [C]
        have hscale := CharacterPartialSummation_characterScale_nonneg hq
        nlinarith

end BoundedGaps.Maynard

end

/-! ## Abel continuation and the ordered value at one

Source module `BoundedGaps.BombieriVinogradov.Analytic.NonprincipalLFunctionAbel`. -/

noncomputable section

open Asymptotics Complex Filter MeasureTheory Set

open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

theorem LFunction_eq_abelIntegral_of_ne_one
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)) := by
  simpa [dirichletCharacterIntervalSum] using
    LFunction_eq_abelIntegral_of_prefixBound chi hchi
      (2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
      (fun n ↦ by
        simpa [dirichletCharacterIntervalSum] using
          norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
            hq chi hchi n)
      s hs

private theorem NonprincipalLFunctionAbel_tendsto_reciprocalPrefix_of_abelIntegral
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤ C)
    (habel : DirichletCharacter.LFunction chi (1 : ℂ) =
      (1 : ℂ) * ∫ y in Ioi (1 : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-((1 : ℂ) + 1))) :
    Tendsto (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
      chi (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let c : ℕ → ℂ := fun n ↦ chi (n : ZMod q)
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(1 : ℂ))
  have hc0 : c 0 = 0 := by
    simpa [c] using chi.map_zero' (Nat.ne_of_gt hq)
  have hCumulative (n : ℕ) :
      ∑ k ∈ Finset.Icc 0 n, c k =
        dirichletCharacterIntervalSum 1 n q chi := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [c, dirichletCharacterIntervalSum]
  have hfDiff : ∀ t ∈ Ici (1 : ℝ), DifferentiableAt ℝ f t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const
      (zero_lt_one.trans_le ht).ne' (by norm_num)
  have hfInt : LocallyIntegrableOn (deriv f) (Ici (1 : ℝ)) := by
    exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one
        (by norm_num))).locallyIntegrableOn
  have hEndpoint : Tendsto
      (fun n : ℕ ↦ f n * ∑ k ∈ Finset.Icc 0 n, c k) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun n : ℕ ↦ C / (n : ℝ))
    · exact Eventually.of_forall fun n ↦ norm_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with n hn
      rw [hCumulative, norm_mul]
      have hfn : ‖f n‖ = (n : ℝ)⁻¹ := by
        change ‖(n : ℂ) ^ (-(1 : ℂ))‖ = (n : ℝ)⁻¹
        rw [Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
      rw [hfn]
      calc
        (n : ℝ)⁻¹ *
            ‖dirichletCharacterIntervalSum 1 n q chi‖ ≤
            (n : ℝ)⁻¹ * C :=
          mul_le_mul_of_nonneg_left (hprefix n)
            (inv_nonneg.mpr (by positivity))
        _ = C / (n : ℝ) := by ring
    · simpa [div_eq_mul_inv] using
        ((tendsto_const_nhds (x := C)).mul
          (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hDom :
      (fun t ↦ deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =O[atTop]
        (fun t : ℝ ↦ t ^ (-2 : ℝ)) := by
    refine isBigO_iff.mpr ⟨C, ?_⟩
    filter_upwards [eventually_gt_atTop 1] with t ht
    rw [norm_mul, hCumulative]
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hderiv : ‖deriv f t‖ = t ^ (-2 : ℝ) := by
      rw [show deriv f t =
          deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
        deriv_ofReal_cpow_const ht0.ne' (by norm_num), norm_mul,
        norm_neg, norm_one, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      norm_num
    rw [hderiv]
    have hgNonneg : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht0.le _
    calc
      t ^ (-2 : ℝ) *
          ‖dirichletCharacterIntervalSum 1 ⌊t⌋₊ q chi‖ ≤
          t ^ (-2 : ℝ) * C :=
        mul_le_mul_of_nonneg_left (hprefix _) hgNonneg
      _ = C * ‖t ^ (-2 : ℝ)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hgNonneg]
        ring
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀
    (f := f) (l := 0) c hc0 hfDiff hfInt hEndpoint hDom
      (integrableAtFilter_rpow_atTop_iff.mpr (by norm_num))
  have hleft (n : ℕ) :
      (∑ k ∈ Finset.Icc 0 n, f k * c k) =
        ∑ k ∈ Finset.Icc 1 n,
          chi (k : ZMod q) / (k : ℂ) := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc0,
      mul_zero, zero_add, ← Finset.Icc_add_one_left_eq_Ioc 0 n]
    norm_num [f, c, Complex.cpow_neg_one, div_eq_mul_inv, mul_comm]
  have hright :
      0 - ∫ t in Ioi (1 : ℝ),
          deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
        DirichletCharacter.LFunction chi (1 : ℂ) := by
    rw [habel, one_mul, zero_sub, ← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change -(deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = _
    rw [show deriv f t =
        deriv (fun u : ℝ ↦ (u : ℂ) ^ (-(1 : ℂ))) t by rfl,
      deriv_ofReal_cpow_const (zero_lt_one.trans ht).ne' (by norm_num),
      hCumulative]
    ring_nf
  rw [← hright]
  exact hconv.congr' (Eventually.of_forall hleft)

theorem tendsto_dirichletCharacterReciprocalPrefix_atTop
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    Tendsto
      (fun x : ℕ ↦ ∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ))
      atTop (𝓝 (DirichletCharacter.LFunction chi (1 : ℂ))) := by
  let C : ℝ := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  apply NonprincipalLFunctionAbel_tendsto_reciprocalPrefix_of_abelIntegral hq chi C
  · intro n
    simpa [C] using
      norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
        hq chi hchi n
  · exact LFunction_eq_abelIntegral_of_ne_one
      hq chi hchi (1 : ℂ) (by norm_num)

theorem norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (x : ℕ) (hx : 0 < x) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        ∑ n ∈ Finset.Icc 1 x,
          chi (n : ZMod q) / (n : ℂ)‖ ≤
      4 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) / (x : ℝ) := by
  let P : ℕ → ℂ := fun y ↦ ∑ n ∈ Finset.Icc 1 y,
    chi (n : ZMod q) / (n : ℂ)
  have htail {y : ℕ} (hxy : x ≤ y) :
      P y - P x = ∑ n ∈ Finset.Ioc x y,
        chi (n : ZMod q) / (n : ℂ) := by
    have hunion : Finset.Icc 1 x ∪ Finset.Ioc x y =
        Finset.Icc 1 y := by
      ext n
      simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro (hn | hn) <;> omega
      · intro hn
        by_cases hnx : n ≤ x
        · exact Or.inl ⟨hn.1, hnx⟩
        · exact Or.inr ⟨lt_of_not_ge hnx, hn.2⟩
    have hdis : Disjoint (Finset.Icc 1 x) (Finset.Ioc x y) := by
      rw [Finset.disjoint_left]
      intro n hncc hnoc
      simp only [Finset.mem_Icc] at hncc
      simp only [Finset.mem_Ioc] at hnoc
      omega
    change (∑ n ∈ Finset.Icc 1 y,
        chi (n : ZMod q) / (n : ℂ)) -
      (∑ n ∈ Finset.Icc 1 x,
        chi (n : ZMod q) / (n : ℂ)) = _
    rw [← hunion, Finset.sum_union hdis]
    ring
  have hconv :=
    tendsto_dirichletCharacterReciprocalPrefix_atTop hq chi hchi
  have hlim : Tendsto (fun y ↦ ‖P y - P x‖) atTop
      (𝓝 ‖DirichletCharacter.LFunction chi (1 : ℂ) - P x‖) := by
    exact (hconv.sub_const (P x)).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with y hxy
  rw [htail hxy]
  exact norm_dirichletCharacterReciprocalIntervalSum_le
    hq chi hchi x y hx

end BoundedGaps.Maynard

end

/-! ## Nonprincipal Dirichlet L-functions near one

Source module `BoundedGaps.BombieriVinogradov.Analytic.NearOneLFunction`. -/

noncomputable section

open Complex MeasureTheory Metric Set

open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private lemma NearOneLFunction_three_le_modulus_of_character_ne_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    3 ≤ q := by
  by_contra hq
  have hqPos : 0 < q := NeZero.pos q
  have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
  have hqTwo : q = 2 := by omega
  subst q
  have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    norm_num
  exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)

private lemma NearOneLFunction_one_lt_log_modulus
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : (3 : ℝ) ≤ q := by
    exact_mod_cast NearOneLFunction_three_le_modulus_of_character_ne_one chi hchi
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThree))

private lemma NearOneLFunction_norm_characterIntervalSum_floor_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {y : ℝ} (hy : 1 < y) :
    ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ ≤ y := by
  have hfloorPos : 0 < ⌊y⌋₊ := Nat.floor_pos.mpr hy.le
  calc
    ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ ≤
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ‖chi (n : ZMod q)‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) := by
      exact Finset.sum_le_sum fun n _ ↦ chi.norm_le_one (n : ZMod q)
    _ = (⌊y⌋₊ : ℝ) := by
      simp [Nat.card_Icc]
    _ ≤ y := Nat.floor_le (zero_lt_one.trans hy).le

private lemma NearOneLFunction_measurable_characterAbelIntegrand
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    AEStronglyMeasurable
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)))
      (volume.restrict (Ioi 1)) := by
  have hPrefix : Measurable
      (fun y : ℝ ↦ dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi) :=
    (measurable_of_countable
      (fun n : ℕ ↦ dirichletCharacterIntervalSum 1 n q chi)).comp
      Nat.measurable_floor
  have hCpow : ContinuousOn
      (fun y : ℝ ↦ (y : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    continuousOn_of_forall_continuousAt fun y hy ↦
      continuousAt_ofReal_cpow_const y (-(s + 1))
        (Or.inr (zero_lt_one.trans hy).ne')
  exact hPrefix.aestronglyMeasurable.mul
    (hCpow.aestronglyMeasurable measurableSet_Ioi)

private lemma NearOneLFunction_integrableOn_characterAbelIntegrand
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun y : ℝ ↦
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
  let C := 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have hPower : IntegrableOn
      (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hMajorant : IntegrableOn
      (fun y : ℝ ↦ C * y ^ (-(s.re + 1))) (Ioi 1) :=
    hPower.const_mul C
  have hBound : ∀ᵐ (y : ℝ) ∂volume.restrict (Ioi 1),
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
        C * y ^ (-(s.re + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hyPos : 0 < y := zero_lt_one.trans hy
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (by
        simpa [C] using
          norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
            hq chi hchi ⌊y⌋₊)
      (Real.rpow_nonneg hyPos.le _)
  exact hMajorant.mono' (NearOneLFunction_measurable_characterAbelIntegrand chi s) hBound

private lemma NearOneLFunction_initial_characterAbelIntegral_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) {s : ℂ}
    (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re) :
    ‖∫ y in Ioc (1 : ℝ) q,
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      3 * Real.log (q : ℝ) := by
  let L := Real.log (q : ℝ)
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  let g : ℝ → ℝ := fun y ↦ 3 * y ^ (-1 : ℝ)
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans_le hqOne
  have hLpos : 0 < L := by
    exact Real.log_pos (by exact_mod_cast hq)
  have hLone : 1 < L := NearOneLFunction_one_lt_log_modulus chi hchi
  have hMajorant : IntegrableOn g (Ioc (1 : ℝ) q) := by
    apply (continuousOn_const.mul ?_).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    exact continuousOn_of_forall_continuousAt fun y hy ↦
      Real.continuousAt_rpow_const _ _
        (Or.inl (zero_lt_one.trans_le hy.1).ne')
  have hPoint : ∀ y ∈ Ioc (1 : ℝ) q, ‖f y‖ ≤ g y := by
    intro y hy
    have hyPos : 0 < y := zero_lt_one.trans hy.1
    have hyOne : 1 ≤ y := hy.1.le
    have hdelta : 1 - s.re ≤ 5 / (16 * L) := by
      dsimp [L]
      linarith
    have hpow : y ^ (1 - s.re) ≤ 3 := by
      by_cases hdeltaNonpos : 1 - s.re ≤ 0
      · exact (Real.rpow_le_one_of_one_le_of_nonpos hyOne hdeltaNonpos).trans
          (by norm_num)
      · have hdeltaNonneg : 0 ≤ 1 - s.re := le_of_not_ge hdeltaNonpos
        have hbase : y ^ (1 - s.re) ≤ (q : ℝ) ^ (1 - s.re) :=
          Real.rpow_le_rpow hyPos.le hy.2 hdeltaNonneg
        have hexponent :
            (q : ℝ) ^ (1 - s.re) ≤ (q : ℝ) ^ (5 / (16 * L)) :=
          Real.rpow_le_rpow_of_exponent_le hqOne hdelta
        have heval : (q : ℝ) ^ (5 / (16 * L)) = Real.exp (5 / 16) := by
          rw [Real.rpow_def_of_pos hqPos]
          congr 1
          dsimp [L]
          have hlogNe : Real.log (q : ℝ) ≠ 0 :=
            (Real.log_pos (by exact_mod_cast hq)).ne'
          field_simp [hlogNe]
        calc
          y ^ (1 - s.re) ≤ (q : ℝ) ^ (1 - s.re) := hbase
          _ ≤ (q : ℝ) ^ (5 / (16 * L)) := hexponent
          _ = Real.exp (5 / 16) := heval
          _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
          _ ≤ 3 := Real.exp_one_lt_three.le
    dsimp [f, g]
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    calc
      ‖dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi‖ *
          y ^ (-(s.re + 1)) ≤
          y * y ^ (-(s.re + 1)) :=
        mul_le_mul_of_nonneg_right
          (NearOneLFunction_norm_characterIntervalSum_floor_le chi hy.1)
          (Real.rpow_nonneg hyPos.le _)
      _ = y ^ (-s.re) := by
        rw [mul_comm, ← Real.rpow_add_one hyPos.ne']
        congr 1
        ring
      _ = y ^ (-1 : ℝ) * y ^ (1 - s.re) := by
        rw [← Real.rpow_add hyPos]
        congr 1
        ring
      _ ≤ y ^ (-1 : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hyPos.le _)
      _ = 3 * y ^ (-1 : ℝ) := by ring
  have hsPos : 0 < s.re := by
    have hfrac : 5 / (16 * L) ≤ 5 / 16 := by
      rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
      nlinarith
    linarith
  have hActual : IntegrableOn f (Ioc (1 : ℝ) q) :=
    (NearOneLFunction_integrableOn_characterAbelIntegrand hq chi hchi hsPos).mono_set
      Ioc_subset_Ioi_self
  calc
    ‖∫ y in Ioc (1 : ℝ) q, f y‖ ≤
        ∫ y in Ioc (1 : ℝ) q, ‖f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioc (1 : ℝ) q, g y :=
      setIntegral_mono_on hActual.norm hMajorant measurableSet_Ioc hPoint
    _ = 3 * Real.log (q : ℝ) := by
      rw [integral_const_mul]
      rw [← intervalIntegral.integral_of_le hqOne]
      simp_rw [Real.rpow_neg_one]
      rw [integral_inv_of_pos zero_lt_one hqPos]
      simp

private lemma NearOneLFunction_tail_characterAbelIntegral_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re) :
    ‖∫ y in Ioi (q : ℝ),
        dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
          (y : ℂ) ^ (-(s + 1))‖ ≤
      4 * Real.log (q : ℝ) := by
  let L := Real.log (q : ℝ)
  let C := 2 * Real.sqrt (q : ℝ) * L
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  let g : ℝ → ℝ := fun y ↦ C * y ^ (-(s.re + 1))
  have hqThree := NearOneLFunction_three_le_modulus_of_character_ne_one chi hchi
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hqThree.trans' (by norm_num)
  have hqPos : (0 : ℝ) < q := zero_lt_one.trans_le hqOne
  have hLone : 1 < L := NearOneLFunction_one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hfrac : 5 / (16 * L) ≤ 5 / 16 := by
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsLower : (11 / 16 : ℝ) ≤ s.re := by
    dsimp [L] at hfrac
    linarith
  have hsPos : 0 < s.re := by linarith
  have hCnonneg : 0 ≤ C := by positivity
  have hPower : IntegrableOn (fun y : ℝ ↦ y ^ (-(s.re + 1))) (Ioi q) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hqPos
  have hMajorant : IntegrableOn g (Ioi (q : ℝ)) := hPower.const_mul C
  have hPoint : ∀ y ∈ Ioi (q : ℝ), ‖f y‖ ≤ g y := by
    intro y hy
    have hyPos : 0 < y := hqPos.trans hy
    dsimp [f, g, C]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hyPos]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right
      (norm_dirichletCharacterPrefixSum_le_two_mul_sqrt_mul_log
        hq chi hchi ⌊y⌋₊)
      (Real.rpow_nonneg hyPos.le _)
  have hActual : IntegrableOn f (Ioi (q : ℝ)) :=
    (NearOneLFunction_integrableOn_characterAbelIntegrand hq chi hchi hsPos).mono_set
      (Ioi_subset_Ioi hqOne)
  have hnormIntegral :
      ‖∫ y in Ioi (q : ℝ), f y‖ ≤
        C * ((q : ℝ) ^ (-s.re) / s.re) := by
    calc
      ‖∫ y in Ioi (q : ℝ), f y‖ ≤
          ∫ y in Ioi (q : ℝ), ‖f y‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y in Ioi (q : ℝ), g y :=
        setIntegral_mono_on hActual.norm hMajorant measurableSet_Ioi hPoint
      _ = C * ∫ y in Ioi (q : ℝ), y ^ (-(s.re + 1)) := by
        rw [integral_const_mul]
      _ = C * ((q : ℝ) ^ (-s.re) / s.re) := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hqPos]
        congr 1
        field_simp [hsPos.ne']
        ring_nf
  have hsHalf : (1 / 2 : ℝ) ≤ s.re := by linarith
  have hpowProduct :
      Real.sqrt (q : ℝ) * (q : ℝ) ^ (-s.re) ≤ 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hqPos]
    exact Real.rpow_le_one_of_one_le_of_nonpos hqOne (by linarith)
  have hinv : 1 / s.re ≤ 2 := by
    exact (div_le_iff₀ hsPos).2 (by linarith)
  calc
    ‖∫ y in Ioi (q : ℝ), f y‖ ≤
        C * ((q : ℝ) ^ (-s.re) / s.re) := hnormIntegral
    _ = 2 * L *
        (Real.sqrt (q : ℝ) * (q : ℝ) ^ (-s.re)) * (1 / s.re) := by
      dsimp [C]
      ring
    _ ≤ 2 * L * 1 * 2 := by
      gcongr
    _ = 4 * Real.log (q : ℝ) := by
      dsimp [L]
      ring

theorem norm_LFunction_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ}
    (hsRe : 1 - 5 / (16 * Real.log (q : ℝ)) ≤ s.re)
    (hsNorm : ‖s‖ ≤ 2) :
    ‖DirichletCharacter.LFunction chi s‖ ≤
      32 * Real.log (q : ℝ) := by
  let f : ℝ → ℂ := fun y ↦
    dirichletCharacterIntervalSum 1 ⌊y⌋₊ q chi *
      (y : ℂ) ^ (-(s + 1))
  have hLone := NearOneLFunction_one_lt_log_modulus chi hchi
  have hLpos : 0 < Real.log (q : ℝ) := zero_lt_one.trans hLone
  have hRePos : 0 < s.re := by
    have hfrac : 5 / (16 * Real.log (q : ℝ)) ≤ 5 / 16 := by
      rw [div_le_iff₀ (by positivity : 0 < 16 * Real.log (q : ℝ))]
      nlinarith
    linarith
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hInitial := NearOneLFunction_initial_characterAbelIntegral_le hq chi hchi hsRe
  have hTail := NearOneLFunction_tail_characterAbelIntegral_le hq chi hchi hsRe
  have hIntegrable := NearOneLFunction_integrableOn_characterAbelIntegrand hq chi hchi hRePos
  have hSplit :
      (∫ y in Ioi (1 : ℝ), f y) =
        (∫ y in Ioc (1 : ℝ) q, f y) +
          (∫ y in Ioi (q : ℝ), f y) := by
    rw [← Ioc_union_Ioi_eq_Ioi hqOne,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hIntegrable.mono_set Ioc_subset_Ioi_self)
        (hIntegrable.mono_set (Ioi_subset_Ioi hqOne))]
  rw [LFunction_eq_abelIntegral_of_ne_one hq chi hchi s hRePos, norm_mul]
  change ‖s‖ * ‖∫ y in Ioi (1 : ℝ), f y‖ ≤ _
  rw [hSplit]
  calc
    ‖s‖ * ‖(∫ y in Ioc (1 : ℝ) q, f y) +
        (∫ y in Ioi (q : ℝ), f y)‖ ≤
      ‖s‖ * (‖∫ y in Ioc (1 : ℝ) q, f y‖ +
        ‖∫ y in Ioi (q : ℝ), f y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg s)
    _ ≤ 2 * (3 * Real.log (q : ℝ) + 4 * Real.log (q : ℝ)) := by
      gcongr
    _ ≤ 32 * Real.log (q : ℝ) := by nlinarith

theorem norm_deriv_LFunction_ofReal_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma : ℝ}
    (hsigmaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ sigma)
    (hsigmaOne : sigma ≤ 1) :
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      512 * (Real.log (q : ℝ)) ^ 2 := by
  let L := Real.log (q : ℝ)
  let r := 1 / (16 * L)
  have hLone : 1 < L := NearOneLFunction_one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hrPos : 0 < r := by positivity
  have hrLe : r ≤ 1 / 16 := by
    dsimp [r]
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsigmaPos : 0 < sigma := by
    have hquarter : 1 / (4 * L) < 1 := by
      rw [div_lt_one (by positivity : 0 < 4 * L)]
      nlinarith
    change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
    linarith
  have hsphere : ∀ z ∈ sphere (sigma : ℂ) r,
      ‖DirichletCharacter.LFunction chi z‖ ≤ 32 * L := by
    intro z hz
    have hdist : ‖z - (sigma : ℂ)‖ = r := by
      simpa [dist_eq_norm] using mem_sphere.mp hz
    have hreDiff : |z.re - sigma| ≤ r := by
      calc
        |z.re - sigma| = |(z - (sigma : ℂ)).re| := by simp
        _ ≤ ‖z - (sigma : ℂ)‖ := Complex.abs_re_le_norm _
        _ = r := hdist
    have hzRe : 1 - 5 / (16 * L) ≤ z.re := by
      have hrad : r = 1 / (16 * L) := rfl
      rw [hrad] at hreDiff
      have hlower := (abs_le.mp hreDiff).1
      change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
      have hratio : 1 / (4 * L) = 4 * (1 / (16 * L)) := by
        field_simp [hLpos.ne']
        ring
      rw [hratio] at hsigmaNear
      have hfive : 5 / (16 * L) = 5 * (1 / (16 * L)) := by ring
      rw [hfive]
      linarith
    have hzNorm : ‖z‖ ≤ 2 := by
      calc
        ‖z‖ ≤ ‖(sigma : ℂ)‖ + ‖z - (sigma : ℂ)‖ := by
          simpa [add_comm] using norm_add_le (z - (sigma : ℂ)) (sigma : ℂ)
        _ = sigma + r := by simp [abs_of_pos hsigmaPos, hdist]
        _ ≤ 2 := by linarith
    simpa [L] using norm_LFunction_near_one_le hq chi hchi hzRe hzNorm
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hrPos (DirichletCharacter.differentiable_LFunction hchi).diffContOnCl hsphere
  calc
    ‖deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
        (32 * L) / r := hCauchy
    _ = 512 * (Real.log (q : ℝ)) ^ 2 := by
      change (32 * L) / (1 / (16 * L)) = 512 * L ^ 2
      field_simp [hLpos.ne']
      ring

end BoundedGaps.Maynard

end

/-! ## Conjugation symmetry of Dirichlet L-functions

Source module `BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionConjugation`. -/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Filter

open scoped ComplexConjugate Topology

private lemma DirichletLFunctionConjugation_conj_LSeries_conj_eq_inv
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    conj (LSeries (chi ·) (conj s)) = LSeries (chi⁻¹ ·) s := by
  rw [LSeries, conj_tsum, LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      map_div₀]
    have hcoeff : (starRingEnd ℂ) (chi n) = chi⁻¹ n := by
      change star (chi n) = chi⁻¹ n
      exact MulChar.star_apply' chi n
    rw [hcoeff]
    congr 1
    rw [← Complex.conj_cpow (n : ℂ) s (by
      rw [Complex.natCast_arg]
      exact ne_of_eq_of_ne rfl Real.pi_ne_zero.symm),
      Complex.conj_natCast]

theorem LFunction_inv_conj
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (s : ℂ) :
    DirichletCharacter.LFunction chi⁻¹ (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  have hinvAnalytic : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunction chi⁻¹) Set.univ :=
    DifferentiableOn.analyticOnNhd
      (DirichletCharacter.differentiable_LFunction
        (inv_ne_one.mpr hchi)).differentiableOn isOpen_univ
  have hconjAnalytic : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        conj (DirichletCharacter.LFunction chi (conj z))) Set.univ :=
    DifferentiableOn.analyticOnNhd (fun z _ =>
      (differentiableAt_conj_conj_iff.mpr
        (DirichletCharacter.differentiable_LFunction hchi (conj z))).differentiableWithinAt)
      isOpen_univ
  have heq (z : ℂ) (hz : 1 < z.re) :
      DirichletCharacter.LFunction chi⁻¹ z =
        conj (DirichletCharacter.LFunction chi (conj z)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries chi⁻¹ hz,
      DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hz)]
    exact (DirichletLFunctionConjugation_conj_LSeries_conj_eq_inv chi z).symm
  have hfun : DirichletCharacter.LFunction chi⁻¹ =
      fun z : ℂ => conj (DirichletCharacter.LFunction chi (conj z)) :=
    hinvAnalytic.eq_of_eventuallyEq hconjAnalytic <|
      eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds
          (by norm_num : (1 : ℝ) < ((2 : ℂ).re))) heq
  simpa using congrFun hfun (conj s)

theorem LFunction_conj_of_sq_eq_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) (hsquare : chi ^ 2 = 1) (s : ℂ) :
    DirichletCharacter.LFunction chi (conj s) =
      conj (DirichletCharacter.LFunction chi s) := by
  have hinv : chi⁻¹ = chi :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsquare)
  simpa [hinv] using LFunction_inv_conj chi hchi s

end BoundedGaps.Maynard

end

/-! ## Explicit cutoff arithmetic for the quadratic L-value bound

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticLValueCutoff`. -/

noncomputable section

namespace BoundedGaps.Maynard

private noncomputable def QuadraticLValueCutoff_quadraticLValueScale (q : ℕ) : ℝ :=
  (2 ^ 22 : ℝ) * (q : ℝ) * (Real.log (q : ℝ)) ^ 4

noncomputable def quadraticLValueCutoff (q : ℕ) : ℕ :=
  ⌈QuadraticLValueCutoff_quadraticLValueScale q⌉₊

private lemma QuadraticLValueCutoff_one_half_lt_log_natCast {q : ℕ} (hq : 1 < q) :
    (1 / 2 : ℝ) < Real.log (q : ℝ) := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  exact hlogTwo.trans_le (Real.log_le_log (by norm_num) hqTwo)

private lemma QuadraticLValueCutoff_quadraticLValueScale_pos {q : ℕ} (hq : 1 < q) :
    0 < QuadraticLValueCutoff_quadraticLValueScale q := by
  have hqPos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_of_lt hq)
  have hlogPos : 0 < Real.log (q : ℝ) := by
    linarith [QuadraticLValueCutoff_one_half_lt_log_natCast hq]
  unfold QuadraticLValueCutoff_quadraticLValueScale
  exact mul_pos (mul_pos (by norm_num) hqPos) (pow_pos hlogPos 4)

private lemma QuadraticLValueCutoff_one_eighth_le_natCast_mul_log_pow_four {q : ℕ} (hq : 1 < q) :
    (1 / 8 : ℝ) ≤ (q : ℝ) * (Real.log (q : ℝ)) ^ 4 := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hlogPow : (1 / 2 : ℝ) ^ 4 ≤ (Real.log (q : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) (QuadraticLValueCutoff_one_half_lt_log_natCast hq).le 4
  have hmul := mul_le_mul hqTwo hlogPow (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 4)
    (by positivity : (0 : ℝ) ≤ q)
  norm_num at hmul ⊢
  exact hmul

private lemma QuadraticLValueCutoff_quadraticLValueScale_le_cutoff {q : ℕ} :
    QuadraticLValueCutoff_quadraticLValueScale q ≤ (quadraticLValueCutoff q : ℝ) := by
  exact Nat.le_ceil _

private lemma QuadraticLValueCutoff_cutoff_le_two_mul_quadraticLValueScale
    {q : ℕ} (hq : 1 < q) :
    (quadraticLValueCutoff q : ℝ) ≤ 2 * QuadraticLValueCutoff_quadraticLValueScale q := by
  unfold quadraticLValueCutoff
  apply Nat.ceil_le_two_mul
  have hmul := QuadraticLValueCutoff_one_eighth_le_natCast_mul_log_pow_four hq
  unfold QuadraticLValueCutoff_quadraticLValueScale
  nlinarith

theorem four_le_quadraticLValueCutoff {q : ℕ} (hq : 1 < q) :
    4 ≤ quadraticLValueCutoff q := by
  have hscale := QuadraticLValueCutoff_quadraticLValueScale_le_cutoff (q := q)
  have hmul := QuadraticLValueCutoff_one_eighth_le_natCast_mul_log_pow_four hq
  have hfour : (4 : ℝ) ≤ QuadraticLValueCutoff_quadraticLValueScale q := by
    unfold QuadraticLValueCutoff_quadraticLValueScale
    nlinarith
  exact_mod_cast hfour.trans hscale

theorem log_quadraticLValueCutoff_le {q : ℕ} (hq : 1 < q) :
    Real.log (quadraticLValueCutoff q : ℝ) ≤
      51 * Real.log (q : ℝ) := by
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqOne : (1 : ℝ) ≤ q := hqTwo.trans' (by norm_num)
  have hqPos : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hqTwo
  have hlogNonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  have hlogLeQ : Real.log (q : ℝ) ≤ (q : ℝ) :=
    (Real.log_le_sub_one_of_pos hqPos).trans (by linarith)
  have htwoPow : (2 : ℝ) ^ 23 ≤ (q : ℝ) ^ 23 :=
    pow_le_pow_left₀ (by norm_num) hqTwo 23
  have hlogPow : (Real.log (q : ℝ)) ^ 4 ≤ (q : ℝ) ^ 4 :=
    pow_le_pow_left₀ hlogNonneg hlogLeQ 4
  have hcutPow : (quadraticLValueCutoff q : ℝ) ≤ (q : ℝ) ^ 51 := by
    calc
      (quadraticLValueCutoff q : ℝ) ≤ 2 * QuadraticLValueCutoff_quadraticLValueScale q :=
        QuadraticLValueCutoff_cutoff_le_two_mul_quadraticLValueScale hq
      _ = (2 : ℝ) ^ 23 * q * (Real.log (q : ℝ)) ^ 4 := by
        unfold QuadraticLValueCutoff_quadraticLValueScale
        norm_num
        ring
      _ ≤ (q : ℝ) ^ 23 * q * (q : ℝ) ^ 4 := by
        gcongr
      _ = (q : ℝ) ^ 28 := by ring
      _ ≤ (q : ℝ) ^ 51 := pow_le_pow_right₀ hqOne (by norm_num)
  have hcutPos : (0 : ℝ) < quadraticLValueCutoff q := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 4)
      (four_le_quadraticLValueCutoff hq))
  have hlog := Real.log_le_log hcutPos hcutPow
  rw [Real.log_pow] at hlog
  norm_num at hlog ⊢
  exact hlog

private lemma QuadraticLValueCutoff_cutoffLowerScale_le_sqrt {q : ℕ} (hq : 1 < q) :
    2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤
      Real.sqrt (quadraticLValueCutoff q : ℝ) := by
  have hleftNonneg :
      0 ≤ 2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    positivity
  have hleftSq :
      (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        QuadraticLValueCutoff_quadraticLValueScale q := by
    have hsqrtQSq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
      Real.sq_sqrt (by positivity)
    unfold QuadraticLValueCutoff_quadraticLValueScale
    rw [show
      (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        4194304 * (Real.sqrt (q : ℝ)) ^ 2 *
          (Real.log (q : ℝ)) ^ 4 by ring]
    rw [hsqrtQSq]
    norm_num
  have hsqrtSq :
      (Real.sqrt (quadraticLValueCutoff q : ℝ)) ^ 2 =
        (quadraticLValueCutoff q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hscale := QuadraticLValueCutoff_quadraticLValueScale_le_cutoff (q := q)
  have hsqrtNonneg := Real.sqrt_nonneg (quadraticLValueCutoff q : ℝ)
  nlinarith

theorem quadraticLValueComparisonError_le {q : ℕ} (hq : 1 < q) :
    (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
      (1 / 8 : ℝ) * Real.sqrt (quadraticLValueCutoff q : ℝ) := by
  have hlogPos : 0 < Real.log (q : ℝ) := by
    linarith [QuadraticLValueCutoff_one_half_lt_log_natCast hq]
  have hcoef :
      6 + 4 * Real.log (quadraticLValueCutoff q : ℝ) ≤
        216 * Real.log (q : ℝ) := by
    have hlogCut := log_quadraticLValueCutoff_le hq
    have hlogHalf := QuadraticLValueCutoff_one_half_lt_log_natCast hq
    linarith
  have hfactorNonneg :
      0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
    mul_nonneg (Real.sqrt_nonneg _) hlogPos.le
  have herror :
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
        216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    calc
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) =
        (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by ring
      _ ≤ (216 * Real.log (q : ℝ)) *
          (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoef hfactorNonneg
      _ = 216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by ring
  have hlower := QuadraticLValueCutoff_cutoffLowerScale_le_sqrt hq
  calc
    (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
      216 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := herror
    _ ≤ 256 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
      gcongr
      norm_num
    _ = (1 / 8 : ℝ) *
        (2048 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) := by ring
    _ ≤ (1 / 8 : ℝ) * Real.sqrt (quadraticLValueCutoff q : ℝ) := by
      gcongr

theorem sqrt_quadraticLValueCutoff_le {q : ℕ} (hq : 1 < q) :
    Real.sqrt (quadraticLValueCutoff q : ℝ) ≤
      4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
  have hrightNonneg :
      0 ≤ 4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    positivity
  have hrightSq :
      (4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        4 * QuadraticLValueCutoff_quadraticLValueScale q := by
    have hsqrtQSq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
      Real.sq_sqrt (by positivity)
    unfold QuadraticLValueCutoff_quadraticLValueScale
    rw [show
      (4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) ^ 2 =
        16777216 * (Real.sqrt (q : ℝ)) ^ 2 *
          (Real.log (q : ℝ)) ^ 4 by ring]
    rw [hsqrtQSq]
    norm_num
    ring
  have hsqrtSq :
      (Real.sqrt (quadraticLValueCutoff q : ℝ)) ^ 2 =
        (quadraticLValueCutoff q : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hcut := QuadraticLValueCutoff_cutoff_le_two_mul_quadraticLValueScale hq
  have hscalePos := QuadraticLValueCutoff_quadraticLValueScale_pos hq
  have hsqrtNonneg := Real.sqrt_nonneg (quadraticLValueCutoff q : ℝ)
  nlinarith

end BoundedGaps.Maynard

end

/-! ## The finite Euler--Maclaurin cutoff

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaEulerMaclaurin`. -/

noncomputable section

open MeasureTheory Set

open scoped BigOperators

namespace BoundedGaps.Maynard

private lemma QuadraticZetaEulerMaclaurin_integrableOn_fract_Icc (a b : ℝ) :
    IntegrableOn (Int.fract : ℝ → ℝ) (Icc a b) := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
  · exact measurable_fract.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le

private lemma QuadraticZetaEulerMaclaurin_integral_fract_unit :
    (∫ t : ℝ in Set.Ioc 0 1, Int.fract t) = 1 / 2 := by
  calc
    (∫ t : ℝ in Set.Ioc 0 1, Int.fract t) =
        ∫ t : ℝ in Set.Ioc 0 1, t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht htne
      exact Int.fract_eq_self.mpr ⟨ht.1.le, lt_of_le_of_ne ht.2 htne⟩
    _ = 1 / 2 := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num

private lemma QuadraticZetaEulerMaclaurin_integral_fract_formula {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) =
      (⌊u⌋₊ : ℝ) / 2 + (u - (⌊u⌋₊ : ℝ)) ^ 2 / 2 := by
  let n : ℕ := ⌊u⌋₊
  have hbase : IntervalIntegrable (Int.fract : ℝ → ℝ) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact QuadraticZetaEulerMaclaurin_integrableOn_fract_Icc 0 1
  have hall (a b : ℝ) :
      IntervalIntegrable (Int.fract : ℝ → ℝ) volume a b :=
    (Int.fract_periodic ℝ).intervalIntegrable₀ one_ne_zero hbase a b
  have hbaseValue : (∫ t : ℝ in 0..1, Int.fract t) = 1 / 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact QuadraticZetaEulerMaclaurin_integral_fract_unit
  have hnValue : (∫ t : ℝ in 0..(n : ℝ), Int.fract t) = (n : ℝ) / 2 := by
    have hperiod := (Int.fract_periodic ℝ).intervalIntegral_add_zsmul_eq
      (n : ℤ) 0 hall
    simpa [hbaseValue, nsmul_eq_mul, div_eq_mul_inv] using hperiod
  have hn_le : (n : ℝ) ≤ u := by
    dsimp [n]
    exact Nat.floor_le hu.le
  have hu_lt : u < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one u
  have hrem : (∫ t : ℝ in (n : ℝ)..u, Int.fract t) =
      (u - (n : ℝ)) ^ 2 / 2 := by
    calc
      (∫ t : ℝ in (n : ℝ)..u, Int.fract t) =
          ∫ t : ℝ in (n : ℝ)..u, (t - (n : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.uIcc (n : ℝ) u := ht
        rw [Set.uIcc_of_le hn_le] at ht'
        rw [← Int.fract_sub_natCast t n]
        exact Int.fract_eq_self.mpr ⟨sub_nonneg.mpr ht'.1,
          (sub_lt_iff_lt_add).mpr
            (ht'.2.trans_lt (by simpa [add_comm] using hu_lt))⟩
      _ = (u - (n : ℝ)) ^ 2 / 2 := by
        rw [intervalIntegral.integral_sub]
        · rw [integral_id, intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
        · exact continuous_id.intervalIntegrable (μ := volume) _ _
        · exact continuous_const.intervalIntegrable (μ := volume) _ _
  rw [← intervalIntegral.integral_of_le hu.le]
  change (∫ t : ℝ in 0..u, Int.fract t) =
    (n : ℝ) / 2 + (u - (n : ℝ)) ^ 2 / 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hall 0 n) (hall n u),
    hnValue, hrem]

theorem sum_linear_cutoff_eq_half_sub_fractIntegral
    {u : ℝ} (hu : 0 < u) :
    (∑ b ∈ Finset.Icc 1 ⌊u⌋₊,
      (1 - (b : ℝ) / u)) =
      u / 2 - (1 / u) *
        (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) := by
  rw [QuadraticZetaEulerMaclaurin_integral_fract_formula hu]
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  have hsum_id : ∀ n : ℕ,
      (∑ b ∈ Finset.Icc 1 n, (b : ℝ)) =
        (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum_id]
  simp only [Nat.card_Icc]
  push_cast
  field_simp [hu.ne']
  ring

end BoundedGaps.Maynard

end

/-! ## Quadratic zeta-convolution coefficients at squares

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaConvolutionSquare`. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

open ArithmeticFunction

theorem one_le_zetaMul_prime_pow_two_mul
    {q p k : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hp : p.Prime) :
    (1 : ℂ) ≤ chi.zetaMul (p ^ (2 * k)) := by
  rw [show chi.zetaMul (p ^ (2 * k)) = ∑ d ∈ (p ^ (2 * k)).divisors, toArithmeticFunction (chi ·) d from
    coe_zeta_mul_apply (f := toArithmeticFunction (chi ·))]
  simp only [toArithmeticFunction, coe_mk, Nat.sum_divisors_prime_pow hp,
    pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hsquare p with h | h | h
  · simp [h]
  · simp [h]
    positivity
  · simp [h, neg_one_geom_sum]

theorem one_le_zetaMul_sq
    {q n : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hn : n ≠ 0) :
    (1 : ℂ) ≤ chi.zetaMul (n ^ 2) := by
  rw [chi.isMultiplicative_zetaMul.multiplicative_factorization _
    (pow_ne_zero 2 hn)]
  refine Finset.one_le_prod fun p hp => ?_
  have hp' : p.Prime := by
    exact Nat.prime_of_mem_primeFactors (by simpa using hp)
  simpa [Nat.factorization_pow] using
    one_le_zetaMul_prime_pow_two_mul (chi := chi) hsquare hp'

end BoundedGaps.Maynard

end

/-! ## A smoothed quadratic convolution lower bound

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaSmoothedSquareLower`. -/

noncomputable section

open scoped BigOperators ComplexOrder

namespace BoundedGaps.Maynard

noncomputable def quadraticZetaLinearSmoothedSum
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    chi.zetaMul n * ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)

theorem sum_square_linearCutoff_le_quadraticZetaLinearSmoothedSum
    {q X : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hX : 0 < X) :
    (∑ m ∈ Finset.Icc 1 X.sqrt,
        ((1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) : ℂ)) ≤
      quadraticZetaLinearSmoothedSum chi X := by
  classical
  let squares := Finset.Icc 1 X.sqrt
  let indices := Finset.Icc 1 X
  let square : ℕ → ℕ := fun m ↦ m ^ 2
  let weight : ℕ → ℂ := fun n ↦
    ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)
  let summand : ℕ → ℂ := fun n ↦ chi.zetaMul n * weight n
  have hXreal : (0 : ℝ) < X := by
    exact_mod_cast hX
  have hweight : ∀ n ∈ indices, (0 : ℂ) ≤ weight n := by
    intro n hn
    have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
    dsimp only [weight]
    rw [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨sub_nonneg.mpr ((div_le_one hXreal).2 (by exact_mod_cast hnX)), rfl⟩
  have hsquare_subset : squares.image square ⊆ indices := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
    have hm_bounds := Finset.mem_Icc.mp hm
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_pow 2 m (by omega)
    · exact Nat.le_sqrt'.mp hm_bounds.2
  have hsquare_injective : Set.InjOn square squares :=
    (Nat.pow_left_injective (by decide : 2 ≠ 0)).injOn
  have hselected :
      (∑ m ∈ squares, weight (square m)) ≤
        ∑ m ∈ squares, summand (square m) := by
    apply Finset.sum_le_sum
    intro m hm
    have hm_ne : m ≠ 0 := by
      have hm_one : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      omega
    have hm_image : square m ∈ squares.image square :=
      Finset.mem_image.mpr ⟨m, hm, rfl⟩
    simpa only [summand, square, one_mul] using
      mul_le_mul_of_nonneg_right
        (one_le_zetaMul_sq (chi := chi) hsquare hm_ne)
        (hweight _ (hsquare_subset hm_image))
  have hmain :
      (∑ m ∈ squares, weight (square m)) ≤ ∑ n ∈ indices, summand n := by
    calc
      (∑ m ∈ squares, weight (square m)) ≤
          ∑ m ∈ squares, summand (square m) := hselected
      _ = ∑ n ∈ squares.image square, summand n :=
        (Finset.sum_image hsquare_injective).symm
      _ ≤ ∑ n ∈ indices, summand n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsquare_subset fun n hn _ ↦
          mul_nonneg (chi.zetaMul_nonneg hsquare n) (hweight n hn)
  simpa [squares, indices, square, weight, summand,
    quadraticZetaLinearSmoothedSum, Nat.cast_pow] using hmain

end BoundedGaps.Maynard

end

/-! ## Direct Euler remainder for the quadratic zeta cutoff

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaDirectEulerRemainder`. -/

noncomputable section

open MeasureTheory Set

open scoped BigOperators

namespace BoundedGaps.Maynard

private theorem QuadraticZetaDirectEulerRemainder_mem_positiveFactorPairs_quadratic
    {X : ℕ} (p : ℕ × ℕ) :
    p ∈ positiveFactorPairs X ↔
      p.1 ∈ Finset.Icc 1 X ∧ p.2 ∈ Finset.Icc 1 (X / p.1) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact ⟨Finset.mem_Icc.mpr ⟨hp₁.1, hp₁.2⟩,
      Finset.mem_Icc.mpr ⟨hp₂.1,
        (Nat.le_div_iff_mul_le hp₁.1).mpr (by
          simpa only [Nat.mul_comm] using hprod)⟩⟩
  · rintro ⟨hm, hk⟩
    rw [Finset.mem_Icc] at hm hk
    have hprod : p.1 * p.2 ≤ X := by
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hm.1).mp hk.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr hm,
          Finset.mem_Ioc.mpr
            ⟨hk.1, hk.2.trans (Nat.div_le_self X p.1)⟩⟩,
        hprod⟩

private theorem QuadraticZetaDirectEulerRemainder_sum_divisors_cutoff_eq_nested_quadratic
    {X : ℕ} (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f n d) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), f (a * b) a := by
  calc
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f n d) =
        ∑ n ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors, f n d := by
      rw [show Finset.Icc 1 X = Finset.Ioc 0 X by
        simpa using Finset.Icc_succ_left_eq_Ioc 0 X]
    _ = ∑ p ∈ positiveFactorPairs X, f (p.1 * p.2) p.1 :=
      sum_divisors_up_to_eq_sum_positiveFactorPairs f
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
          f (a * b) a := by
      exact Finset.sum_finset_product' (f := fun a b ↦ f (a * b) a)
        (positiveFactorPairs X) (Finset.Icc 1 X)
        (fun a ↦ Finset.Icc 1 (X / a))
        QuadraticZetaDirectEulerRemainder_mem_positiveFactorPairs_quadratic

private theorem QuadraticZetaDirectEulerRemainder_zetaMul_cutoff_eq_nested_quadratic
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * w n) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
        chi (a : ZMod q) * w (a * b) := by
  have hz : (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * w n) =
      ∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ n.divisors, chi (d : ZMod q)) * w n := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [DirichletCharacter.zetaMul,
      ArithmeticFunction.coe_zeta_mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']
  rw [hz]
  simp_rw [Finset.sum_mul]
  rw [QuadraticZetaDirectEulerRemainder_sum_divisors_cutoff_eq_nested_quadratic]

noncomputable def quadraticZetaDirectEulerRemainder
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  (1 / (X : ℂ)) *
    ∑ a ∈ Finset.Icc 1 X,
      (a : ℂ) * chi (a : ZMod q) *
        (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
          ((Int.fract t : ℝ) : ℂ))

theorem quadraticZetaLinearSmoothedSum_eq_directEulerRemainder
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (hX : 0 < X) :
    quadraticZetaLinearSmoothedSum chi X =
      ((X : ℂ) / 2) *
        (∑ a ∈ Finset.Icc 1 X,
          chi (a : ZMod q) / (a : ℂ)) -
      quadraticZetaDirectEulerRemainder chi X := by
  let weight : ℕ → ℂ := fun n ↦
    ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hinner : ∀ a ∈ Finset.Icc 1 X,
      (∑ b ∈ Finset.Icc 1 (X / a), weight (a * b)) =
        (X : ℂ) / (2 * (a : ℂ)) -
          ((a : ℂ) / (X : ℂ)) *
            (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
              ((Int.fract t : ℝ) : ℂ)) := by
    intro a ha
    have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
    have haReal : (0 : ℝ) < a := by exact_mod_cast haPos
    let u : ℝ := (X : ℝ) / (a : ℝ)
    have hu : 0 < u := div_pos hXreal haReal
    have heuler := sum_linear_cutoff_eq_half_sub_fractIntegral hu
    have hfloor : ⌊u⌋₊ = X / a := by
      simpa [u] using (Nat.floor_div_eq_div (K := ℝ) X a)
    rw [hfloor] at heuler
    have hweight : ∀ b : ℕ,
        (1 - (a : ℝ) * (b : ℝ) / (X : ℝ)) =
          1 - (b : ℝ) / u := by
      intro b
      dsimp [u]
      field_simp [hXreal.ne', haReal.ne']
    have hreal :
        (∑ b ∈ Finset.Icc 1 (X / a),
          (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) =
          u / 2 - (1 / u) *
            (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) := by
      rw [show (∑ b ∈ Finset.Icc 1 (X / a),
          (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) =
          ∑ b ∈ Finset.Icc 1 (X / a),
            (1 - (b : ℝ) / u) by
        apply Finset.sum_congr rfl
        intro b hb
        exact hweight b]
      exact heuler
    calc
      (∑ b ∈ Finset.Icc 1 (X / a), weight (a * b)) =
          (((∑ b ∈ Finset.Icc 1 (X / a),
            (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp [weight, Nat.cast_mul]
      _ = _ := by
        rw [hreal, Complex.ofReal_sub, Complex.ofReal_mul]
        rw [show ((∫ t : ℝ in Set.Ioc 0 u, Int.fract t : ℝ) : ℂ) =
            ∫ t : ℝ in Set.Ioc 0 u, ((Int.fract t : ℝ) : ℂ) by
          exact integral_ofReal.symm]
        dsimp [u]
        push_cast
        field_simp [hXreal.ne', haReal.ne']
  rw [quadraticZetaLinearSmoothedSum]
  change (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * weight n) = _
  rw [QuadraticZetaDirectEulerRemainder_zetaMul_cutoff_eq_nested_quadratic]
  calc
    (∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
        chi (a : ZMod q) * weight (a * b)) =
        ∑ a ∈ Finset.Icc 1 X,
          chi (a : ZMod q) *
            ((X : ℂ) / (2 * (a : ℂ)) -
              ((a : ℂ) / (X : ℂ)) *
                (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
                  ((Int.fract t : ℝ) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum, hinner a ha]
    _ = ∑ a ∈ Finset.Icc 1 X,
          (((X : ℂ) / 2) *
              (chi (a : ZMod q) / (a : ℂ)) -
            (1 / (X : ℂ)) *
              ((a : ℂ) * chi (a : ZMod q) *
                (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
                  ((Int.fract t : ℝ) : ℂ)))) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haNe : (a : ℂ) ≠ 0 := by
        have haPos : 0 < a := lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp ha).1
        exact_mod_cast haPos.ne'
      have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
      field_simp [haNe, hXne]
    _ = ((X : ℂ) / 2) *
          (∑ a ∈ Finset.Icc 1 X,
            chi (a : ZMod q) / (a : ℂ)) -
        quadraticZetaDirectEulerRemainder chi X := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      unfold quadraticZetaDirectEulerRemainder
      rw [Finset.mul_sum]

end BoundedGaps.Maynard

end

/-! ## Swapping the fractional-part Euler remainder

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaSwappedEulerRemainder`. -/

noncomputable section

open MeasureTheory Set

open scoped BigOperators

namespace BoundedGaps.Maynard

noncomputable def quadraticEulerCutoff (X : ℕ) (t : ℝ) : ℕ :=
  if t = 0 then X else min X ⌊(X : ℝ) / t⌋₊

noncomputable def quadraticZetaSwappedEulerRemainder
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  (1 / (X : ℂ)) *
    ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
      ((Int.fract t : ℝ) : ℂ) *
        ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t),
          (a : ℂ) * chi (a : ZMod q)

private lemma QuadraticZetaSwappedEulerRemainder_mem_quadraticEulerCutoff_iff
    {X : ℕ} {t : ℝ} (ht : 0 < t) (a : ℕ) :
    a ∈ Finset.Icc 1 (quadraticEulerCutoff X t) ↔
      a ∈ Finset.Icc 1 X ∧ (a : ℝ) ≤ (X : ℝ) / t := by
  rw [quadraticEulerCutoff, if_neg ht.ne']
  rw [Finset.mem_Icc, Finset.mem_Icc, Nat.le_min]
  constructor
  · rintro ⟨ha1, haX, haf⟩
    refine ⟨⟨ha1, haX⟩, ?_⟩
    rw [Nat.le_floor_iff (div_nonneg (by positivity) ht.le)] at haf
    exact haf
  · rintro ⟨⟨ha1, haX⟩, har⟩
    refine ⟨ha1, haX, ?_⟩
    exact (Nat.le_floor_iff (div_nonneg (by positivity) ht.le)).mpr har

private lemma QuadraticZetaSwappedEulerRemainder_ratio_swap_iff
    {X a : ℕ} {t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t ≤ (X : ℝ) / (a : ℝ) ↔ (a : ℝ) ≤ (X : ℝ) / t := by
  have haReal : (0 : ℝ) < a := by exact_mod_cast ha
  rw [le_div_iff₀ haReal, le_div_iff₀ ht]
  ring_nf

private lemma QuadraticZetaSwappedEulerRemainder_interval_inter_quadratic_cutoff
    {X a : ℕ} (hX : 0 < X) (ha : a ∈ Finset.Icc 1 X) :
    Set.Ioc 0 (X : ℝ) ∩ Set.Iic ((X : ℝ) / (a : ℝ)) =
      Set.Ioc 0 ((X : ℝ) / (a : ℝ)) := by
  have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
  have haReal : (0 : ℝ) < a := by exact_mod_cast haPos
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hle : (X : ℝ) / (a : ℝ) ≤ (X : ℝ) := by
    rw [div_le_iff₀ haReal]
    nlinarith [show (1 : ℝ) ≤ a by exact_mod_cast (Finset.mem_Icc.mp ha).1]
  ext t
  constructor
  · rintro ⟨⟨ht0, htX⟩, hta⟩
    exact ⟨ht0, hta⟩
  · rintro ⟨ht0, hta⟩
    exact ⟨⟨ht0, hta.trans hle⟩, hta⟩

private lemma QuadraticZetaSwappedEulerRemainder_sum_integral_indicator
    {X : ℕ} (hX : 0 < X) (f : ℝ → ℂ)
    (hf : IntegrableOn f (Set.Ioc 0 (X : ℝ))) (g : ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 X, g a *
      (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)), f t)) =
      ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
        ∑ a ∈ Finset.Icc 1 X,
          g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
  have hmeas : ∀ a ∈ Finset.Icc 1 X,
      MeasurableSet (Set.Iic ((X : ℝ) / (a : ℝ))) := by
    intro a ha
    exact measurableSet_Iic
  have hIntIndicator : ∀ a ∈ Finset.Icc 1 X,
      IntegrableOn (Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f)
        (Set.Ioc 0 (X : ℝ)) := by
    intro a ha
    exact hf.indicator (hmeas a ha)
  calc
    (∑ a ∈ Finset.Icc 1 X, g a *
        (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)), f t)) =
        ∑ a ∈ Finset.Icc 1 X, g a *
          (∫ t : ℝ in Set.Ioc 0 (X : ℝ),
            Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [setIntegral_indicator (hmeas a ha)]
      rw [QuadraticZetaSwappedEulerRemainder_interval_inter_quadratic_cutoff hX ha]
    _ = ∑ a ∈ Finset.Icc 1 X,
          ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_const_mul]
    _ = ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          ∑ a ∈ Finset.Icc 1 X,
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t := by
      rw [integral_finsetSum]
      intro a ha
      exact (hIntIndicator a ha).const_mul _

private lemma QuadraticZetaSwappedEulerRemainder_indicator_sum_eq_cutoff
    {X : ℕ} {t : ℝ} (ht : 0 < t) (f : ℝ → ℂ) (g : ℕ → ℂ) :
    (∑ a ∈ Finset.Icc 1 X,
      g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) =
      f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
  calc
    (∑ a ∈ Finset.Icc 1 X,
        g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t) =
        f t * ∑ a ∈ (Finset.Icc 1 X).filter
          (fun a : ℕ ↦ t ≤ (X : ℝ) / (a : ℝ)), g a := by
      rw [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hmem : t ∈ Set.Iic ((X : ℝ) / (a : ℝ))
      · simp only [Set.mem_Iic] at hmem
        simp [Set.indicator, hmem, mul_comm]
      · simp only [Set.mem_Iic] at hmem
        simp [Set.indicator, hmem]
    _ = f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
      apply congrArg (fun s : Finset ℕ => f t * ∑ a ∈ s, g a) ?_
      ext a
      rw [Finset.mem_filter, QuadraticZetaSwappedEulerRemainder_mem_quadraticEulerCutoff_iff ht]
      apply and_congr_right
      intro ha
      exact QuadraticZetaSwappedEulerRemainder_ratio_swap_iff (lt_of_lt_of_le Nat.zero_lt_one
        (Finset.mem_Icc.mp ha).1) ht

private lemma QuadraticZetaSwappedEulerRemainder_integrableOn_fractComplex {X : ℕ} :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ))
      (Set.Ioc 0 (X : ℝ)) := by
  apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
  · exact (Complex.continuous_ofReal.measurable.comp measurable_fract).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le

theorem quadraticZetaDirectEulerRemainder_eq_swapped
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (hX : 0 < X) :
    quadraticZetaDirectEulerRemainder chi X =
      quadraticZetaSwappedEulerRemainder chi X := by
  let f : ℝ → ℂ := fun t => ((Int.fract t : ℝ) : ℂ)
  let g : ℕ → ℂ := fun a => (a : ℂ) * chi (a : ZMod q)
  have hswap := QuadraticZetaSwappedEulerRemainder_sum_integral_indicator hX f
    (QuadraticZetaSwappedEulerRemainder_integrableOn_fractComplex (X := X)) g
  have hcut :
      ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          ∑ a ∈ Finset.Icc 1 X,
            g a * Set.indicator (Set.Iic ((X : ℝ) / (a : ℝ))) f t =
        ∫ t : ℝ in Set.Ioc 0 (X : ℝ),
          f t * ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t), g a := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [QuadraticZetaSwappedEulerRemainder_indicator_sum_eq_cutoff ht.1]
  unfold quadraticZetaDirectEulerRemainder quadraticZetaSwappedEulerRemainder
  dsimp [f, g] at hswap hcut ⊢
  rw [hcut] at hswap
  simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg
    (fun z : ℂ => (1 / (X : ℂ)) * z) hswap

private lemma QuadraticZetaSwappedEulerRemainder_quadraticEulerCutoff_le (X : ℕ) (t : ℝ) :
    quadraticEulerCutoff X t ≤ X := by
  by_cases ht : t = 0
  · simp [quadraticEulerCutoff, ht]
  · simp [quadraticEulerCutoff, ht]

private lemma QuadraticZetaSwappedEulerRemainder_cast_quadraticEulerCutoff_le_div
    {X : ℕ} {t : ℝ} (ht : 0 < t) :
    (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) / t := by
  rw [quadraticEulerCutoff, if_neg ht.ne']
  have hfloor : (min X ⌊(X : ℝ) / t⌋₊ : ℕ) ≤ ⌊(X : ℝ) / t⌋₊ :=
    min_le_right _ _
  have hfloor_le :
      (⌊(X : ℝ) / t⌋₊ : ℝ) ≤ (X : ℝ) / t :=
    Nat.floor_le (div_nonneg (by positivity) ht.le)
  have hcast : ((min X ⌊(X : ℝ) / t⌋₊ : ℕ) : ℝ) ≤
      (⌊(X : ℝ) / t⌋₊ : ℝ) := by exact_mod_cast hfloor
  exact hcast.trans hfloor_le

private lemma QuadraticZetaSwappedEulerRemainder_measurable_quadraticEulerCutoff (X : ℕ) :
    Measurable (quadraticEulerCutoff X) := by
  unfold quadraticEulerCutoff
  have hzero : MeasurableSet ({(0 : ℝ)} : Set ℝ) := measurableSet_singleton (0 : ℝ)
  apply Measurable.ite (by simpa only [Set.setOf_eq_eq_singleton] using hzero)
    measurable_const
  have hdiv : Measurable (fun t : ℝ ↦ (X : ℝ) / t) :=
    measurable_const.div measurable_id
  exact (measurable_of_countable (fun y : ℕ ↦ min X y)).comp hdiv.nat_floor

private lemma QuadraticZetaSwappedEulerRemainder_integrableOn_quadraticSwappedIntegrand
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    IntegrableOn
      (fun t : ℝ ↦ ((Int.fract t : ℝ) : ℂ) *
        ∑ a ∈ Finset.Icc 1 (quadraticEulerCutoff X t),
          (a : ℂ) * chi (a : ZMod q))
      (Set.Ioc 0 (X : ℝ)) := by
  let charPrefix : ℕ → ℂ := fun y ↦
    ∑ a ∈ Finset.Icc 1 y, (a : ℂ) * chi (a : ZMod q)
  let F : ℝ → ℂ := fun t ↦ ((Int.fract t : ℝ) : ℂ) *
    charPrefix (quadraticEulerCutoff X t)
  have hprefixMeas : Measurable (fun t ↦
      charPrefix (quadraticEulerCutoff X t)) :=
    (measurable_of_countable charPrefix).comp
      (QuadraticZetaSwappedEulerRemainder_measurable_quadraticEulerCutoff X)
  have hFMeas : Measurable F :=
    (Complex.continuous_ofReal.measurable.comp measurable_fract).mul hprefixMeas
  apply IntegrableOn.of_bound measure_Ioc_lt_top hFMeas.aestronglyMeasurable
    (4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
  rw [norm_mul]
  have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le
  have hprefix := norm_dirichletCharacterWeightedPrefixSum_le
    hq chi hchi (quadraticEulerCutoff X t)
  change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
  calc
    ‖((Int.fract t : ℝ) : ℂ)‖ *
        ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
        1 * (4 * (quadraticEulerCutoff X t : ℝ) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
      mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
    _ ≤ 4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
      have hlog : 0 ≤ Real.log (q : ℝ) :=
        (Real.log_pos (by exact_mod_cast hq)).le
      have hscale : 0 ≤ Real.sqrt (q : ℝ) * Real.log (q : ℝ) :=
        mul_nonneg (Real.sqrt_nonneg _) hlog
      have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) := by
        exact_mod_cast QuadraticZetaSwappedEulerRemainder_quadraticEulerCutoff_le X t
      have hfour : (0 : ℝ) ≤ 4 := by norm_num
      have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
          4 * (X : ℝ) := mul_le_mul_of_nonneg_left hcut hfour
      calc
        1 * (4 * (quadraticEulerCutoff X t : ℝ) * Real.sqrt (q : ℝ) *
            Real.log (q : ℝ)) =
            (4 * (quadraticEulerCutoff X t : ℝ)) *
              (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) := by
              ring
        _ ≤ (4 * (X : ℝ)) * (Real.sqrt (q : ℝ) * Real.log (q : ℝ)) :=
          mul_le_mul_of_nonneg_right h4cut hscale
        _ = 4 * (X : ℝ) * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
          ring

theorem norm_quadraticZetaSwappedEulerRemainder_le
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (hX : 0 < X) :
    ‖quadraticZetaSwappedEulerRemainder chi X‖ ≤
      4 * (1 + Real.log (X : ℝ)) * Real.sqrt (q : ℝ) *
        Real.log (q : ℝ) := by
  let charPrefix : ℕ → ℂ := fun y ↦
    ∑ a ∈ Finset.Icc 1 y, (a : ℂ) * chi (a : ZMod q)
  let F : ℝ → ℂ := fun t ↦ ((Int.fract t : ℝ) : ℂ) *
    charPrefix (quadraticEulerCutoff X t)
  let S : ℝ := Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have hXone : 1 ≤ X := hX
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hOneX : (1 : ℝ) ≤ X := by exact_mod_cast hXone
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _)
    (Real.log_pos (by exact_mod_cast hq)).le
  have hFint : IntegrableOn F (Set.Ioc 0 (X : ℝ)) := by
    simpa [F, charPrefix] using
      QuadraticZetaSwappedEulerRemainder_integrableOn_quadraticSwappedIntegrand hq chi hchi (X := X)
  have hpointFirst : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ‖F t‖ ≤ 4 * (X : ℝ) * S := by
    intro t ht
    change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
    rw [norm_mul]
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hprefix :=
      norm_dirichletCharacterWeightedPrefixSum_le
        hq chi hchi (quadraticEulerCutoff X t)
    change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
    calc
      ‖((Int.fract t : ℝ) : ℂ)‖ *
          ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
          1 * (4 * (quadraticEulerCutoff X t : ℝ) * S) := by
        simpa [S, mul_assoc] using
          mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
      _ ≤ 4 * (X : ℝ) * S := by
        have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) := by
          exact_mod_cast QuadraticZetaSwappedEulerRemainder_quadraticEulerCutoff_le X t
        have hfour : (0 : ℝ) ≤ 4 := by norm_num
        have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
            4 * (X : ℝ) := mul_le_mul_of_nonneg_left hcut hfour
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right h4cut hS
  have hpointSecond : ∀ t ∈ Set.Ioc (1 : ℝ) X,
      ‖F t‖ ≤ (4 * (X : ℝ) * S) * t⁻¹ := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht.1
    change ‖((Int.fract t : ℝ) : ℂ) *
      charPrefix (quadraticEulerCutoff X t)‖ ≤ _
    rw [norm_mul]
    have hfract : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Int.fract_nonneg t)]
      exact (Int.fract_lt_one t).le
    have hprefix := norm_dirichletCharacterWeightedPrefixSum_le
      hq chi hchi (quadraticEulerCutoff X t)
    change ‖charPrefix (quadraticEulerCutoff X t)‖ ≤ _ at hprefix
    calc
      ‖((Int.fract t : ℝ) : ℂ)‖ *
          ‖charPrefix (quadraticEulerCutoff X t)‖ ≤
          1 * (4 * (quadraticEulerCutoff X t : ℝ) * S) := by
        simpa [S, mul_assoc] using
          mul_le_mul hfract hprefix (norm_nonneg _) zero_le_one
      _ ≤ 4 * ((X : ℝ) / t) * S := by
        have hcut : (quadraticEulerCutoff X t : ℝ) ≤ (X : ℝ) / t :=
          QuadraticZetaSwappedEulerRemainder_cast_quadraticEulerCutoff_le_div ht0
        have hfour : (0 : ℝ) ≤ 4 := by norm_num
        have h4cut : 4 * (quadraticEulerCutoff X t : ℝ) ≤
            4 * ((X : ℝ) / t) :=
          mul_le_mul_of_nonneg_left hcut hfour
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right h4cut hS
      _ = (4 * (X : ℝ) * S) * t⁻¹ := by ring
  have hFirstInt : IntegrableOn (fun t ↦ ‖F t‖) (Set.Ioc (0 : ℝ) 1) :=
    (hFint.mono_set (Set.Ioc_subset_Ioc_right hOneX)).norm
  have hSecondInt : IntegrableOn (fun t ↦ ‖F t‖) (Set.Ioc (1 : ℝ) X) :=
    (hFint.mono_set (Set.Ioc_subset_Ioc_left zero_le_one)).norm
  have hFirstMajor : IntegrableOn (fun _t : ℝ ↦ 4 * (X : ℝ) * S)
      (Set.Ioc (0 : ℝ) 1) := integrableOn_const measure_Ioc_lt_top.ne
  have hSecondMajor : IntegrableOn (fun t : ℝ ↦
      (4 * (X : ℝ) * S) * t⁻¹) (Set.Ioc (1 : ℝ) X) := by
    have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc 1 X) := by
      apply ContinuousOn.inv₀ continuousOn_id
      intro t ht
      exact (zero_lt_one.trans_le ht.1).ne'
    exact (hinv.const_mul (4 * (X : ℝ) * S)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hFirst : (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) ≤
      4 * (X : ℝ) * S := by
    calc
      (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) ≤
          ∫ _t : ℝ in Set.Ioc 0 1, 4 * (X : ℝ) * S := by
        apply setIntegral_mono_ae_restrict hFirstInt hFirstMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointFirst t ht
      _ = 4 * (X : ℝ) * S := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Ioc]
        norm_num [smul_eq_mul]
  have hSecond : (∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖) ≤
      4 * (X : ℝ) * S * Real.log (X : ℝ) := by
    calc
      (∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖) ≤
          ∫ t : ℝ in Set.Ioc 1 (X : ℝ),
            (4 * (X : ℝ) * S) * t⁻¹ := by
        apply setIntegral_mono_ae_restrict hSecondInt hSecondMajor
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpointSecond t ht
      _ = 4 * (X : ℝ) * S * Real.log (X : ℝ) := by
        rw [integral_const_mul]
        rw [← intervalIntegral.integral_of_le hOneX]
        rw [integral_inv_of_pos zero_lt_one hXreal]
        simp only [div_one]
  have hunion : Set.Ioc (0 : ℝ) (X : ℝ) =
      Set.Ioc (0 : ℝ) (1 : ℝ) ∪ Set.Ioc (1 : ℝ) (X : ℝ) := by
    ext t
    simp only [Set.mem_Ioc, Set.mem_union]
    constructor
    · intro ht
      by_cases ht1 : t ≤ 1
      · exact Or.inl ⟨ht.1, ht1⟩
      · exact Or.inr ⟨lt_of_not_ge ht1, ht.2⟩
    · rintro (ht | ht) <;> constructor
      · exact ht.1
      · exact ht.2.trans hOneX
      · exact zero_lt_one.trans ht.1
      · exact ht.2
  have hdis : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioc 1 X) := by
    rw [Set.disjoint_left]
    intro t ht1 ht2
    exact (not_lt_of_ge ht1.2) ht2.1
  have hnormIntegral : ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
      4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S := by
    calc
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
          ∫ t : ℝ in Set.Ioc 0 (X : ℝ), ‖F t‖ :=
        norm_integral_le_integral_norm _
      _ = (∫ t : ℝ in Set.Ioc 0 1, ‖F t‖) +
          ∫ t : ℝ in Set.Ioc 1 (X : ℝ), ‖F t‖ := by
        rw [hunion, setIntegral_union hdis measurableSet_Ioc
          hFirstInt hSecondInt]
      _ ≤ 4 * (X : ℝ) * S +
          4 * (X : ℝ) * S * Real.log (X : ℝ) := add_le_add hFirst hSecond
      _ = 4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S := by ring
  unfold quadraticZetaSwappedEulerRemainder
  rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  change (1 / (X : ℝ)) *
      ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤ _
  calc
    (1 / (X : ℝ)) * ‖∫ t : ℝ in Set.Ioc 0 (X : ℝ), F t‖ ≤
        (1 / (X : ℝ)) *
          (4 * (X : ℝ) * (1 + Real.log (X : ℝ)) * S) :=
      mul_le_mul_of_nonneg_left hnormIntegral (by positivity)
    _ = 4 * (1 + Real.log (X : ℝ)) * Real.sqrt (q : ℝ) *
        Real.log (q : ℝ) := by
      dsimp [S]
      field_simp [hXreal.ne']

end BoundedGaps.Maynard

end

/-! ## Comparison with the ordered value at one

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaLFunctionComparison`. -/

noncomputable section

open scoped BigOperators

namespace BoundedGaps.Maynard

theorem norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_le
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (hX : 0 < X)
    (B : ℝ)
    (hB : ‖quadraticZetaSwappedEulerRemainder chi X‖ ≤ B) :
    ‖quadraticZetaLinearSmoothedSum chi X -
        ((X : ℂ) / 2) * DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) + B := by
  let P : ℂ := ∑ a ∈ Finset.Icc 1 X,
    chi (a : ZMod q) / (a : ℂ)
  let S : ℝ := Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have htail := norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    hq chi hchi X hX
  have htail' : ‖P - DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      4 * S / (X : ℝ) := by
    rw [norm_sub_rev]
    dsimp [P, S]
    convert htail using 1 ; ring
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hmain := quadraticZetaLinearSmoothedSum_eq_directEulerRemainder chi hX
  have hswap := quadraticZetaDirectEulerRemainder_eq_swapped chi hX
  have hscale : ‖((X : ℂ) / 2)‖ = (X : ℝ) / 2 := by
    rw [norm_div, Complex.norm_natCast]
    norm_num
  have hscaled : ‖((X : ℂ) / 2) *
        (P - DirichletCharacter.LFunction chi (1 : ℂ))‖ ≤ 2 * S := by
    rw [norm_mul, hscale]
    calc
      ((X : ℝ) / 2) * ‖P - DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          ((X : ℝ) / 2) * (4 * S / (X : ℝ)) :=
        mul_le_mul_of_nonneg_left htail' (by positivity)
      _ = 2 * S := by
        field_simp [hXreal.ne']
        ring
  calc
    ‖quadraticZetaLinearSmoothedSum chi X -
        ((X : ℂ) / 2) * DirichletCharacter.LFunction chi (1 : ℂ)‖ =
        ‖((X : ℂ) / 2) *
            (P - DirichletCharacter.LFunction chi (1 : ℂ)) -
          quadraticZetaSwappedEulerRemainder chi X‖ := by
      rw [hmain, hswap]
      dsimp [P]
      ring_nf
    _ ≤ ‖((X : ℂ) / 2) *
          (P - DirichletCharacter.LFunction chi (1 : ℂ))‖ +
        ‖quadraticZetaSwappedEulerRemainder chi X‖ := norm_sub_le _ _
    _ ≤ 2 * S + B := add_le_add hscaled hB
    _ = 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) + B := by
      dsimp [S]
      ring

end BoundedGaps.Maynard

end

/-! ## Square-root scale of the smoothed square sum

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaSquareScaleLower`. -/

noncomputable section

open scoped BigOperators ComplexOrder

namespace BoundedGaps.Maynard

theorem three_eighths_mul_real_sqrt_le_sum_square_linearCutoff
    {X : ℕ} (hX : 4 ≤ X) :
    (3 / 8 : ℝ) * Real.sqrt (X : ℝ) ≤
      ∑ m ∈ Finset.Icc 1 X.sqrt,
        (1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) := by
  have hXpos : 0 < X := by omega
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hsqrt_two : 2 ≤ X.sqrt := by
    rw [Nat.le_sqrt]
    omega
  have hsum_sq : ∀ r : ℕ,
      (∑ m ∈ Finset.Icc 1 r, (m : ℝ) ^ 2) =
        (r : ℝ) * ((r : ℝ) + 1) * (2 * (r : ℝ) + 1) / 6 := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring
  have hsum_weights :
      (∑ m ∈ Finset.Icc 1 X.sqrt,
          (1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ)) =
        (X.sqrt : ℝ) -
          (X.sqrt : ℝ) * ((X.sqrt : ℝ) + 1) *
            (2 * (X.sqrt : ℝ) + 1) / (6 * (X : ℝ)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum_sq]
    simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
    push_cast
    simp
    ring
  rw [hsum_weights]
  let r : ℝ := X.sqrt
  let R : ℝ := Real.sqrt (X : ℝ)
  let u : ℝ := R - r
  change (3 / 8 : ℝ) * R ≤
    r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ))
  have hr : (2 : ℝ) ≤ r := by
    dsimp only [r]
    exact_mod_cast hsqrt_two
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hR_sq : R ^ 2 = (X : ℝ) := by
    dsimp only [R]
    exact Real.sq_sqrt hXreal.le
  have hrR : r ≤ R := by
    dsimp only [r, R]
    exact Real.nat_sqrt_le_real_sqrt
  have hRlt : R < r + 1 := by
    dsimp only [r, R]
    exact Real.real_sqrt_lt_nat_sqrt_succ
  have hu0 : (0 : ℝ) ≤ u := by
    dsimp only [u]
    linarith
  have hu1 : u < 1 := by
    dsimp only [u]
    linarith
  have hru : r * u ≤ r := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hu1.le)]
  have hu_sq : u ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1.le)]
  have hr_sq : (4 : ℝ) ≤ r ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (by linarith : 0 ≤ r + 2)]
  have hbracket :
      (0 : ℝ) ≤ 21 * r ^ 2 - 3 * r * u - 9 * u ^ 2 := by
    nlinarith
  have hfirst :
      (0 : ℝ) ≤ r * (r - 2) * (7 * r + 2) :=
    mul_nonneg (mul_nonneg hr0 (sub_nonneg.mpr hr)) (by nlinarith)
  have hsecond :
      (0 : ℝ) ≤ u * (21 * r ^ 2 - 3 * r * u - 9 * u ^ 2) :=
    mul_nonneg hu0 hbracket
  have hidentity :
      24 * (X : ℝ) *
          (r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ)) -
            (3 / 8 : ℝ) * R) =
        r * (r - 2) * (7 * r + 2) +
          u * (21 * r ^ 2 - 3 * r * u - 9 * u ^ 2) := by
    rw [← hR_sq]
    dsimp only [u]
    field_simp [show R ≠ 0 by positivity]
    ring
  have hscaled :
      (0 : ℝ) ≤ 24 * (X : ℝ) *
        (r - r * (r + 1) * (2 * r + 1) / (6 * (X : ℝ)) -
          (3 / 8 : ℝ) * R) := by
    rw [hidentity]
    exact add_nonneg hfirst hsecond
  have hscale_pos : (0 : ℝ) < 24 * (X : ℝ) := by positivity
  have := (mul_nonneg_iff_of_pos_left hscale_pos).mp hscaled
  linarith

theorem three_eighths_mul_real_sqrt_le_quadraticZetaLinearSmoothedSum
    {q X : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hsquare : chi ^ 2 = 1) (hX : 4 ≤ X) :
    (((3 / 8 : ℝ) * Real.sqrt (X : ℝ) : ℝ) : ℂ) ≤
      quadraticZetaLinearSmoothedSum chi X := by
  have hscalar :
      (((3 / 8 : ℝ) * Real.sqrt (X : ℝ) : ℝ) : ℂ) ≤
        ∑ m ∈ Finset.Icc 1 X.sqrt,
          ((1 - (m : ℝ) ^ 2 / (X : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    exact_mod_cast
      three_eighths_mul_real_sqrt_le_sum_square_linearCutoff hX
  exact hscalar.trans
    (sum_square_linearCutoff_le_quadraticZetaLinearSmoothedSum
      hsquare (by omega))

end BoundedGaps.Maynard

end

/-! ## Effective lower bound for quadratic L-values at one

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticLValueLowerBound`. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

theorem LFunction_one_im_eq_zero_of_sq_eq_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) :
    (DirichletCharacter.LFunction chi (1 : ℂ)).im = 0 := by
  have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (1 : ℂ)
  apply Complex.conj_eq_iff_im.mp
  simpa using hconj.symm

private theorem QuadraticLValueLowerBound_norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_cutoff_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    ‖quadraticZetaLinearSmoothedSum chi (quadraticLValueCutoff q) -
        ((quadraticLValueCutoff q : ℂ) / 2) *
          DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have hXpos : 0 < quadraticLValueCutoff q := by
    exact lt_of_lt_of_le (by norm_num) (four_le_quadraticLValueCutoff hq)
  have hrem := norm_quadraticZetaSwappedEulerRemainder_le hq chi hchi hXpos
  have hcomparison :=
    norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_le
      hq chi hchi hXpos
        (4 * (1 + Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ)) hrem
  calc
    ‖quadraticZetaLinearSmoothedSum chi (quadraticLValueCutoff q) -
        ((quadraticLValueCutoff q : ℂ) / 2) *
          DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) +
        4 * (1 + Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) := hcomparison
    _ = (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by ring

theorem effectiveQuadraticLValueLowerBound
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) :
    (((1 / (8192 * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 2) : ℝ) : ℂ)) ≤
      DirichletCharacter.LFunction chi (1 : ℂ) := by
  let X := quadraticLValueCutoff q
  let T := quadraticZetaLinearSmoothedSum chi X
  let L := DirichletCharacter.LFunction chi (1 : ℂ)
  let R := Real.sqrt (X : ℝ)
  have hXfour : 4 ≤ X := by
    simpa [X] using four_le_quadraticLValueCutoff hq
  have hXpos : 0 < X := by omega
  have hXrealPos : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hRpos : 0 < R := by
    exact Real.sqrt_pos.2 hXrealPos
  have hLim : L.im = 0 := by
    simpa [L] using LFunction_one_im_eq_zero_of_sq_eq_one chi hchi hsquare
  have hTlower : (((3 / 8 : ℝ) * R : ℝ) : ℂ) ≤ T := by
    simpa [X, T, R] using
      three_eighths_mul_real_sqrt_le_quadraticZetaLinearSmoothedSum
        hsquare hXfour
  have hTre : (3 / 8 : ℝ) * R ≤ T.re := by
    simpa using (Complex.le_def.mp hTlower).1
  have hTim : T.im = 0 := by
    simpa using (Complex.le_def.mp hTlower).2.symm
  have hnorm :
      ‖T - ((X : ℂ) / 2) * L‖ ≤ (1 / 8 : ℝ) * R := by
    have hcomparison :=
      QuadraticLValueLowerBound_norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_cutoff_le
        hq chi hchi
    have herror := quadraticLValueComparisonError_le hq
    exact (by simpa [X, T, L, R] using hcomparison.trans herror)
  have hdiffRe :
      T.re - ((X : ℝ) / 2) * L.re ≤ (1 / 8 : ℝ) * R := by
    have habs := (Complex.abs_re_le_norm (T - ((X : ℂ) / 2) * L)).trans hnorm
    have hupper := (abs_le.mp habs).2
    simpa [Complex.mul_re, hLim] using hupper
  have hmainLower :
      (1 / 4 : ℝ) * R ≤ ((X : ℝ) / 2) * L.re := by
    linarith
  have hhalfXPos : 0 < (X : ℝ) / 2 := by positivity
  have hLlower : (1 / (2 * R) : ℝ) ≤ L.re := by
    apply (mul_le_mul_iff_of_pos_left hhalfXPos).mp
    calc
      ((X : ℝ) / 2) * (1 / (2 * R) : ℝ) = (1 / 4 : ℝ) * R := by
        have hRsq : R ^ 2 = (X : ℝ) := by
          dsimp [R]
          exact Real.sq_sqrt hXrealPos.le
        field_simp [hRpos.ne']
        nlinarith
      _ ≤ ((X : ℝ) / 2) * L.re := hmainLower
  have hsqrtUpper :
      R ≤ 4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    simpa [X, R] using sqrt_quadraticLValueCutoff_le hq
  have hdenom :
      2 * R ≤ 8192 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    nlinarith
  have hreciprocal :
      (1 / (8192 * Real.sqrt (q : ℝ) *
          (Real.log (q : ℝ)) ^ 2) : ℝ) ≤ 1 / (2 * R) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  refine Complex.le_def.mpr ⟨?_, ?_⟩
  · change (1 / (8192 * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 2) : ℝ) ≤
      (DirichletCharacter.LFunction chi (1 : ℂ)).re
    simpa only [L] using hreciprocal.trans hLlower
  · change (0 : ℝ) = (DirichletCharacter.LFunction chi (1 : ℂ)).im
    simpa only [L] using hLim.symm

end BoundedGaps.Maynard

end

/-! ## Effective real-zero gap for quadratic Dirichlet L-functions

Source module `BoundedGaps.BombieriVinogradov.Analytic.QuadraticRealZeroGap`. -/

noncomputable section

open Set

namespace BoundedGaps.Maynard

private lemma QuadraticRealZeroGap_one_lt_log_modulus_of_character_ne_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : 3 ≤ q := by
    by_contra hq
    have hqPos : 0 < q := NeZero.pos q
    have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
    have hqTwo : q = 2 := by omega
    subst q
    have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
      rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      norm_num
    exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)
  have hqThreeReal : (3 : ℝ) ≤ q := by exact_mod_cast hqThree
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThreeReal))

theorem norm_LFunction_one_sub_ofReal_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {beta : ℝ}
    (hbetaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ beta)
    (hbetaOne : beta ≤ 1) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        DirichletCharacter.LFunction chi (beta : ℂ)‖ ≤
      512 * (Real.log (q : ℝ)) ^ 2 * (1 - beta) := by
  let f : ℝ → ℂ := fun sigma ↦
    DirichletCharacter.LFunction chi (sigma : ℂ)
  let f' : ℝ → ℂ := fun sigma ↦
    deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)
  have hderiv : ∀ sigma ∈ Icc beta 1,
      HasDerivWithinAt f (f' sigma) (Icc beta 1) sigma := by
    intro sigma _
    exact ((DirichletCharacter.differentiable_LFunction hchi
      (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ sigma ∈ Ico beta 1,
      ‖f' sigma‖ ≤ 512 * (Real.log (q : ℝ)) ^ 2 := by
    intro sigma hsigma
    dsimp [f']
    apply norm_deriv_LFunction_ofReal_near_one_le hq chi hchi
    · exact hbetaNear.trans hsigma.1
    · exact hsigma.2.le
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound (1 : ℝ) (right_mem_Icc.mpr hbetaOne)
  simpa [f] using hmean

theorem effectiveQuadraticRealZeroGap
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    {beta : ℝ} (hbetaOne : beta ≤ 1)
    (hzero : DirichletCharacter.LFunction chi (beta : ℂ) = 0) :
    1 / ((2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 4) ≤
      1 - beta := by
  let L := Real.log (q : ℝ)
  let D := (2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) * L ^ 4
  have hLpos : 0 < L := Real.log_pos (by exact_mod_cast hq)
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (q : ℝ) := by
    simpa using Real.sqrt_le_sqrt hqOne
  have hLone : 1 < L := by
    exact QuadraticRealZeroGap_one_lt_log_modulus_of_character_ne_one chi hchi
  have hLpow : L ≤ L ^ 4 := by
    simpa using pow_le_pow_right₀ hLone.le (show 1 ≤ 4 by norm_num)
  have hdenom : 4 * L ≤ D := by
    have hprod : L ≤ Real.sqrt (q : ℝ) * L ^ 4 := by
      calc
        L ≤ L ^ 4 := hLpow
        _ = 1 * L ^ 4 := by ring
        _ ≤ Real.sqrt (q : ℝ) * L ^ 4 := by gcongr
    dsimp [D]
    nlinarith
  have hfarTarget : 1 / D ≤ 1 / (4 * L) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  by_cases hbetaNear : 1 - 1 / (4 * L) ≤ beta
  · have hmean := norm_LFunction_one_sub_ofReal_le hq chi hchi
      (by simpa [L] using hbetaNear) hbetaOne
    have hmeanZero :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := by
      simpa [hzero, L] using hmean
    have hLower := effectiveQuadraticLValueLowerBound hq chi hchi hsquare
    have hLowerRe :
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          (DirichletCharacter.LFunction chi (1 : ℂ)).re := by
      have hLowerReRaw := (Complex.le_def.mp hLower).1
      change
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          (DirichletCharacter.LFunction chi (1 : ℂ)).re at hLowerReRaw
      exact hLowerReRaw
    have hcombined :
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          512 * L ^ 2 * (1 - beta) :=
      hLowerRe.trans (Complex.re_le_norm _ |>.trans hmeanZero)
    have hscalePos : 0 < 512 * L ^ 2 := by positivity
    have hsqrtPos : 0 < Real.sqrt (q : ℝ) := by positivity
    calc
      1 / D =
          (1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2)) /
            (512 * L ^ 2) := by
        dsimp [D]
        field_simp [hLpos.ne', hsqrtPos.ne']
        norm_num
      _ ≤ (512 * L ^ 2 * (1 - beta)) / (512 * L ^ 2) :=
        (div_le_div_iff_of_pos_right hscalePos).2 hcombined
      _ = 1 - beta := by field_simp
  · exact hfarTarget.trans (by
      have : 1 / (4 * L) < 1 - beta := by linarith
      exact this.le)

theorem effectiveQuadraticLFunction_ofReal_ne_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    {sigma : ℝ}
    (hsigma :
      1 - 1 / ((2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 4) < sigma) :
    DirichletCharacter.LFunction chi (sigma : ℂ) ≠ 0 := by
  by_cases hsigmaOne : sigma ≤ 1
  · intro hzero
    have hgap := effectiveQuadraticRealZeroGap hq chi hchi hsquare
      hsigmaOne hzero
    linarith
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi
      (.inl hchi) (by simp; linarith)

end BoundedGaps.Maynard

end

/-! ## The equation-(12.11) L-value upper bound

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLValueUpper`. -/

noncomputable section

namespace BoundedGaps.Maynard

theorem norm_LFunction_one_of_real_zero_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {beta : ℝ} (hbetaOne : beta ≤ 1)
    (hzero : DirichletCharacter.LFunction chi (beta : ℂ) = 0) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 2 := by
  let L := Real.log (q : ℝ)
  let Q := (q : ℝ) ^ ((1 - beta) / 2)
  have hLpos : 0 < L := by
    exact Real.log_pos (by exact_mod_cast hq)
  have hdelta : 0 ≤ 1 - beta := sub_nonneg.mpr hbetaOne
  have hqOne : (1 : ℝ) ≤ q := by
    exact_mod_cast hq.le
  have hQone : 1 ≤ Q := by
    exact Real.one_le_rpow hqOne (div_nonneg hdelta (by norm_num))
  by_cases hbetaNear : 1 - 1 / (4 * L) ≤ beta
  · have hmean := norm_LFunction_one_sub_ofReal_le hq chi hchi
      (by simpa [L] using hbetaNear) hbetaOne
    have hbase :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := by
      simpa [hzero, L] using hmean
    calc
      ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := hbase
      _ = 512 * (1 - beta) * 1 * L ^ 2 := by ring
      _ ≤ 512 * (1 - beta) * Q * L ^ 2 := by gcongr
      _ = 512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 2 := rfl
  · have hfar : 1 / (4 * L) < 1 - beta := by
      linarith
    have hvalue :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤ 32 * L := by
      simpa [L] using
        norm_LFunction_near_one_le hq chi hchi (s := (1 : ℂ))
          (by
            have hfrac : 0 ≤ 5 / (16 * L) := by positivity
            simpa [L] using sub_le_self (1 : ℝ) hfrac)
          (by norm_num)
    calc
      ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤ 32 * L := hvalue
      _ ≤ 128 * L := by nlinarith
      _ = 512 * (1 / (4 * L)) * 1 * L ^ 2 := by
        field_simp [hLpos.ne']
        ring
      _ ≤ 512 * (1 - beta) * Q * L ^ 2 := by gcongr
      _ = 512 * (1 - beta) * (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 2 := rfl

end BoundedGaps.Maynard

end

/-! ## Goldfeld Mellin transform on the positive real axis

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldMellinPositiveBound`. -/

noncomputable section

open Complex Set MeasureTheory

namespace BoundedGaps.Maynard

theorem norm_goldfeldMellinContinuationData_Phi_ofReal_le_two_div
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    ‖goldfeldMellinContinuationData.Phi (delta : ℂ)‖ ≤ 2 / delta := by
  rw [goldfeldMellinContinuationData.agrees_on_right (by simpa using hdelta0)]
  let f : ℝ → ℂ := fun y =>
    (y : ℂ) ^ (((delta : ℝ) : ℂ) - 1) * (goldfeldPlateau y : ℂ)
  have hfIoi : IntegrableOn f (Ioi (0 : ℝ)) := by
    have hconv := goldfeldRawMellin_convergent
      (s := ((delta : ℝ) : ℂ)) (by simpa using hdelta0)
    rw [MellinConvergent] at hconv
    change IntegrableOn f (Ioi (0 : ℝ)) at hconv
    exact hconv
  have htruncate :
      (∫ y in Ioi (0 : ℝ), f y) = ∫ y in Ioc (0 : ℝ) 2, f y := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun _ hy => hy.1)
    intro y hy
    have hyTwo : 2 ≤ y := by
      exact (lt_of_not_ge fun hyLe => hy.2 ⟨hy.1, hyLe⟩).le
    simp [f, goldfeldPlateau_eq_zero hyTwo]
  have hfIoc : IntegrableOn f (Ioc (0 : ℝ) 2) :=
    hfIoi.mono_set (fun _ hy => hy.1)
  have hpowInterval : IntervalIntegrable
      (fun y : ℝ => y ^ (delta - 1)) volume 0 2 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hpowIoc : IntegrableOn (fun y : ℝ => y ^ (delta - 1))
      (Ioc (0 : ℝ) 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1
      hpowInterval
  have hpoint : ∀ y ∈ Ioc (0 : ℝ) 2, ‖f y‖ ≤ y ^ (delta - 1) := by
    intro y hy
    dsimp only [f]
    rw [norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hy.1]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (goldfeldPlateau_nonneg y)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hy.1.le _)
      (goldfeldPlateau_le_one y)
  have heval :
      (∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1)) =
        (2 : ℝ) ^ delta / delta := by
    calc
      (∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1)) =
          ∫ y in (0 : ℝ)..2, y ^ (delta - 1) := by
        exact (intervalIntegral.integral_of_le (by norm_num)).symm
      _ = ((2 : ℝ) ^ ((delta - 1) + 1) -
            (0 : ℝ) ^ ((delta - 1) + 1)) / ((delta - 1) + 1) := by
        rw [integral_rpow (Or.inl (by linarith))]
      _ = (2 : ℝ) ^ delta / delta := by
        rw [show delta - 1 + 1 = delta by ring,
          Real.zero_rpow hdelta0.ne']
        ring
  have hpow : (2 : ℝ) ^ delta ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) hdelta1
  rw [goldfeldRawMellin, mellin]
  change ‖∫ y in Ioi (0 : ℝ), f y‖ ≤ 2 / delta
  rw [htruncate]
  calc
    ‖∫ y in Ioc (0 : ℝ) 2, f y‖ ≤
        ∫ y in Ioc (0 : ℝ) 2, ‖f y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioc (0 : ℝ) 2, y ^ (delta - 1) :=
      setIntegral_mono_on hfIoc.norm hpowIoc measurableSet_Ioc hpoint
    _ = (2 : ℝ) ^ delta / delta := heval
    _ ≤ 2 / delta :=
      (div_le_div_iff_of_pos_right hdelta0).2 hpow

end BoundedGaps.Maynard

end

/-! ## Goldfeld's smoothed-sum lower bound

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldSmoothedSumLowerBound`. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

private theorem GoldfeldSmoothedSumLowerBound_goldfeldSmoothedSummand_nonneg
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    (beta x : ℝ) (n : ℕ) :
    0 ≤ goldfeldBetaCoefficient chi1 chi beta n *
      (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
  apply mul_nonneg
  · simpa [goldfeldBetaCoefficient] using
      LSeries.term_nonneg
        (goldfeldCoefficient_nonneg chi1 chi hsquare1 hsquare n) beta
  · exact (RCLike.ofReal_nonneg (K := ℂ)).2
      (goldfeldPlateau_nonneg _)

private theorem GoldfeldSmoothedSumLowerBound_goldfeldSmoothedSummand_summable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      goldfeldBetaCoefficient chi1 chi beta n *
        (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
  apply summable_of_ne_finset_zero
    (s := Finset.range (Nat.ceil (2 * x)))
  intro n hn
  have hnceil : Nat.ceil (2 * x) ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  have hcutoff : 2 * x ≤ (n : ℝ) := by
    calc
      2 * x ≤ (Nat.ceil (2 * x) : ℕ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast hnceil
  have hratio : 2 ≤ (n : ℝ) / x :=
    (le_div_iff₀ hx).2 hcutoff
  rw [goldfeldPlateau_eq_zero hratio]
  simp

theorem one_le_goldfeldSmoothedSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    {beta x : ℝ} (hx : 1 ≤ x) :
    (1 : ℂ) ≤ goldfeldSmoothedSum chi1 chi beta x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsummable :=
    GoldfeldSmoothedSumLowerBound_goldfeldSmoothedSummand_summable chi1 chi beta hxpos
  rw [goldfeldSmoothedSum]
  calc
    (1 : ℂ) = goldfeldBetaCoefficient chi1 chi beta 1 *
        (goldfeldPlateau ((1 : ℝ) / x) : ℂ) := by
      rw [goldfeldBetaCoefficient,
        LSeries.term_of_ne_zero one_ne_zero, goldfeldCoefficient_one]
      have hplateau : goldfeldPlateau ((1 : ℝ) / x) = 1 :=
        goldfeldPlateau_eq_one
          (div_nonneg zero_le_one hxpos.le)
          ((div_le_one hxpos).2 hx)
      rw [hplateau]
      norm_num
    _ ≤ ∑' n : ℕ,
        goldfeldBetaCoefficient chi1 chi beta n *
          (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
      simpa using hsummable.sum_le_tsum {1} fun n _ =>
        GoldfeldSmoothedSumLowerBound_goldfeldSmoothedSummand_nonneg
          chi1 chi hsquare1 hsquare beta x n

end BoundedGaps.Maynard

end

/-! ## Quantitative bounds for Goldfeld's contour residue

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldQuantitativeResidue`. -/

noncomputable section

open Complex

open scoped ComplexOrder

namespace BoundedGaps.Maynard

theorem half_le_norm_goldfeldContourResidue_of_leftLine
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1) (hchi : chi ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0)
    (hleft : ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤ 1 / 2) :
    1 / 2 ≤ ‖goldfeldContourResidue chi1 chi beta x‖ := by
  have hsumOrder := one_le_goldfeldSmoothedSum
    chi1 chi hsquare1 hsquare (beta := beta) hx
  have hsumRe : 1 ≤ (goldfeldSmoothedSum chi1 chi beta x).re := by
    have hre := Complex.re_le_re hsumOrder
    simpa using hre
  have hsumNorm : 1 ≤ ‖goldfeldSmoothedSum chi1 chi beta x‖ :=
    hsumRe.trans (Complex.re_le_norm _)
  rw [goldfeldSmoothedSum_eq_residue_add_verticalIntegral_neg_one
    hq1 hq1q chi1 chi hchi1 hchi hcross hbeta0 hbeta1 hx hzero] at hsumNorm
  have htriangle :
      1 ≤ ‖goldfeldContourResidue chi1 chi beta x‖ +
        ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ :=
    hsumNorm.trans (norm_add_le _ _)
  linarith

theorem norm_goldfeldContourResidue_le
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (hq1 : 1 < q1) (hq1q : q1 ≤ q)
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hchi1 : chi1 ≠ 1)
    (hcross : DirichletCharacter.mul chi1 chi ≠ 1)
    {beta x : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hx : 1 ≤ x)
    (hzero : DirichletCharacter.LFunction chi1 (beta : ℂ) = 0) :
    ‖goldfeldContourResidue chi1 chi beta x‖ ≤
      65536 * x ^ (1 - beta) *
        (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
  let delta : ℝ := 1 - beta
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta ≤ 1 := by dsimp [delta]; linarith
  have hdeltaNonneg : 0 ≤ delta := hdelta0.le
  have hq1Pos : 0 < (q1 : ℝ) := by positivity
  have hq1qReal : (q1 : ℝ) ≤ q := by exact_mod_cast hq1q
  have hlogq1Nonneg : 0 ≤ Real.log (q1 : ℝ) :=
    (Real.log_pos (by exact_mod_cast hq1)).le
  have hlogq1q : Real.log (q1 : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log hq1Pos hq1qReal
  have hqpow :
      (q1 : ℝ) ^ (delta / 2) ≤ (q : ℝ) ^ (delta / 2) :=
    Real.rpow_le_rpow hq1Pos.le hq1qReal (by positivity)
  have hlogpow :
      (Real.log (q1 : ℝ)) ^ 2 ≤ (Real.log (q : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlogq1Nonneg hlogq1q 2
  have hLone := norm_LFunction_one_of_real_zero_le
    hq1 chi1 hchi1 hbeta1.le hzero
  have hLoneQ :
      ‖DirichletCharacter.LFunction chi1 (1 : ℂ)‖ ≤
        512 * delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 2 := by
    calc
      ‖DirichletCharacter.LFunction chi1 (1 : ℂ)‖ ≤
          512 * delta * (q1 : ℝ) ^ (delta / 2) *
            (Real.log (q1 : ℝ)) ^ 2 := by simpa [delta] using hLone
      _ ≤ 512 * delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 2 := by
        gcongr
  letI : NeZero (Nat.lcm q1 q) :=
    ⟨Nat.lcm_ne_zero (NeZero.ne q1) (NeZero.ne q)⟩
  have hlcmPos : 0 < Nat.lcm q1 q := NeZero.pos _
  have hq1lcm : q1 ≤ Nat.lcm q1 q :=
    Nat.le_of_dvd hlcmPos (Nat.dvd_lcm_left q1 q)
  have hlcmOne : 1 < Nat.lcm q1 q := hq1.trans_le hq1lcm
  have hlcmNat : Nat.lcm q1 q ≤ q ^ 2 := by
    calc
      Nat.lcm q1 q ≤ q1 * q :=
        Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q1) (NeZero.pos q))
          (Nat.lcm_dvd_mul q1 q)
      _ ≤ q * q := Nat.mul_le_mul_right q hq1q
      _ = q ^ 2 := by ring
  have hlcmReal : (Nat.lcm q1 q : ℝ) ≤ (q : ℝ) ^ 2 := by
    exact_mod_cast hlcmNat
  have hlcmLog :
      Real.log (Nat.lcm q1 q : ℝ) ≤ 2 * Real.log (q : ℝ) := by
    calc
      Real.log (Nat.lcm q1 q : ℝ) ≤ Real.log ((q : ℝ) ^ 2) :=
        Real.log_le_log (by exact_mod_cast hlcmPos) hlcmReal
      _ = 2 * Real.log (q : ℝ) := by rw [Real.log_pow]; norm_num
  have hcrossValue := norm_LFunction_near_one_le hlcmOne
    (DirichletCharacter.mul chi1 chi) hcross (s := (1 : ℂ))
    (by
      exact sub_le_self 1 (div_nonneg (by norm_num) (by positivity)))
    (by norm_num)
  have hcrossQ :
      ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi)
          (1 : ℂ)‖ ≤ 64 * Real.log (q : ℝ) := by
    nlinarith
  have hPhi :=
    norm_goldfeldMellinContinuationData_Phi_ofReal_le_two_div
      hdelta0 hdelta1
  have hxPos : 0 < x := zero_lt_one.trans_le hx
  have hxpow :
      ‖(x : ℂ) ^ goldfeldShiftedZetaPole beta‖ = x ^ delta := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
    simp [goldfeldShiftedZetaPole, delta]
  rw [goldfeldContourResidue]
  simp only [norm_mul]
  rw [hxpow]
  calc
    x ^ delta * ‖DirichletCharacter.LFunction chi1 1‖ *
          ‖DirichletCharacter.LFunction chi 1‖ *
          ‖DirichletCharacter.LFunction (DirichletCharacter.mul chi1 chi) 1‖ *
          ‖goldfeldMellinContinuationData.Phi
            (goldfeldShiftedZetaPole beta)‖ ≤
        x ^ delta *
          (512 * delta * (q : ℝ) ^ (delta / 2) *
            (Real.log (q : ℝ)) ^ 2) *
          ‖DirichletCharacter.LFunction chi 1‖ *
          (64 * Real.log (q : ℝ)) * (2 / delta) := by
      have hPhi' :
          ‖goldfeldMellinContinuationData.Phi
              (goldfeldShiftedZetaPole beta)‖ ≤ 2 / delta := by
        simpa [goldfeldShiftedZetaPole, delta] using hPhi
      gcongr
    _ = 65536 * x ^ (1 - beta) *
        (q : ℝ) ^ ((1 - beta) / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
      have hbetaNe : 1 - beta ≠ 0 := by linarith
      dsimp [delta]
      field_simp [hbetaNe]
      ring

end BoundedGaps.Maynard

end

/-! ## Goldfeld's distinct-character L-value lower bound

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldDistinctLValueLower`. -/

noncomputable section

open Complex

namespace BoundedGaps.Maynard

theorem exists_goldfeldDistinctLValueLowerBound :
    ∃ A : ℕ, 58 ≤ A ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          chi1 ^ 2 = 1 → chi ^ 2 = 1 →
          goldfeldCharactersDistinct chi1 chi →
          ∀ beta : ℝ, 0 ≤ beta → beta < 1 →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            c * (q : ℝ) ^ (-((A : ℝ) * (1 - beta))) /
                (Real.log (q : ℝ)) ^ 3 ≤
              ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
  obtain ⟨E, hE, C, hC, hleft⟩ :=
    exists_norm_goldfeldVerticalIntegral_neg_one_le
  let D : ℝ := 2 * max 1 C
  let A : ℕ := E + 1
  let c : ℝ := (131072 * D)⁻¹
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDone : 1 ≤ D := by
    dsimp [D]
    nlinarith [le_max_left (1 : ℝ) C]
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨A, ?_, c, hcpos, ?_⟩
  · dsimp [A]
    omega
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi
    hsquare1 hsquare hdistinct beta hbeta0 hbeta1 hzero
  have hqOne : 1 < q := hq1.trans_le hq1q
  have hqPos : 0 < (q : ℝ) := by positivity
  have hqRealOne : (1 : ℝ) ≤ q := by exact_mod_cast hqOne.le
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hqOne)
  have hcross : DirichletCharacter.mul chi1 chi ≠ 1 :=
    goldfeldCrossLevelMul_ne_one chi1 chi hsquare1 hdistinct
  let x : ℝ := D * (q : ℝ) ^ E
  have hqPowPos : 0 < (q : ℝ) ^ E := pow_pos hqPos E
  have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ E := one_le_pow₀ hqRealOne
  have hxOne : 1 ≤ x := by
    dsimp [x]
    exact one_le_mul_of_one_le_of_one_le hDone hqPowOne
  have hleftAtScale := hleft q1 q hq1 hq1q chi1 chi
    hchi1 hchi hcross beta x hbeta0 hbeta1.le hxOne
  have hscaleIdentity : C * (q : ℝ) ^ E / x = C / D := by
    dsimp [x]
    field_simp [hDpos.ne', hqPowPos.ne']
  have hCmax : C ≤ max 1 C := le_max_right 1 C
  have hCdiv : C / D ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hDpos).2
    dsimp [D]
    nlinarith
  have hleftSmall :
      ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤ 1 / 2 :=
    hleftAtScale.trans (hscaleIdentity.trans_le hCdiv)
  have hresLower := half_le_norm_goldfeldContourResidue_of_leftLine
    hq1 hq1q chi1 chi hchi1 hchi hcross hsquare1 hsquare
    hbeta0 hbeta1 hxOne hzero hleftSmall
  have hresUpper := norm_goldfeldContourResidue_le
    hq1 hq1q chi1 chi hchi1 hcross hbeta0 hbeta1 hxOne hzero
  let delta : ℝ := 1 - beta
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta ≤ 1 := by dsimp [delta]; linarith
  have hdeltaNonneg : 0 ≤ delta := hdelta0.le
  have hmaster :
      1 ≤ 131072 * x ^ delta * (q : ℝ) ^ (delta / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    calc
      (1 : ℝ) = 2 * (1 / 2 : ℝ) := by norm_num
      _ ≤ 2 * ‖goldfeldContourResidue chi1 chi beta x‖ :=
        mul_le_mul_of_nonneg_left hresLower (by norm_num)
      _ ≤ 2 * (65536 * x ^ (1 - beta) *
          (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hresUpper (by norm_num)
      _ = 131072 * x ^ delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        dsimp [delta]
        ring
  have hDpow : D ^ delta ≤ D := by
    simpa using Real.rpow_le_rpow_of_exponent_le hDone hdelta1
  have hexponent :
      (E : ℝ) * delta + delta / 2 ≤ (A : ℝ) * delta := by
    dsimp [A]
    push_cast
    nlinarith
  have hqExponent :
      (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) ≤
        (q : ℝ) ^ ((A : ℝ) * delta) :=
    Real.rpow_le_rpow_of_exponent_le hqRealOne hexponent
  have hscalePower :
      x ^ delta * (q : ℝ) ^ (delta / 2) ≤
        D * (q : ℝ) ^ ((A : ℝ) * delta) := by
    calc
      x ^ delta * (q : ℝ) ^ (delta / 2) =
          (D ^ delta * (((q : ℝ) ^ E) ^ delta)) *
            (q : ℝ) ^ (delta / 2) := by
        dsimp [x]
        rw [Real.mul_rpow hDpos.le (pow_nonneg hqPos.le E)]
      _ = D ^ delta *
          (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) := by
        rw [← Real.rpow_natCast_mul hqPos.le E delta,
          mul_assoc, ← Real.rpow_add hqPos]
      _ ≤ D * (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) :=
        mul_le_mul_of_nonneg_right hDpow (Real.rpow_nonneg hqPos.le _)
      _ ≤ D * (q : ℝ) ^ ((A : ℝ) * delta) :=
        mul_le_mul_of_nonneg_left hqExponent hDpos.le
  have hmaster' :
      1 ≤ 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    calc
      (1 : ℝ) ≤ 131072 *
          (x ^ delta * (q : ℝ) ^ (delta / 2)) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        simpa [mul_assoc] using hmaster
      _ ≤ 131072 *
          (D * (q : ℝ) ^ ((A : ℝ) * delta)) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        gcongr
      _ = 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by ring
  have hdenPos :
      0 < 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
        (Real.log (q : ℝ)) ^ 3 := by
    positivity
  have hdivided :
      1 / (131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3) ≤
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    apply (div_le_iff₀ hdenPos).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmaster'
  calc
    c * (q : ℝ) ^ (-((A : ℝ) * (1 - beta))) /
          (Real.log (q : ℝ)) ^ 3 =
        1 / (131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3) := by
      dsimp [c, delta]
      rw [Real.rpow_neg hqPos.le]
      field_simp [hDpos.ne',
        (Real.rpow_pos_of_pos hqPos ((A : ℝ) * (1 - beta))).ne',
        hlogqPos.ne']
    _ ≤ ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := hdivided

end BoundedGaps.Maynard

end

/-! ## Goldfeld's global exceptional character

Source module `BoundedGaps.BombieriVinogradov.Analytic.GoldfeldExceptionalCharacter`. -/

noncomputable section

open Complex Set

namespace BoundedGaps.Maynard

structure GoldfeldPrimitiveRealCharacter where
  modulus : ℕ
  modulus_gt_one : 1 < modulus
  character : DirichletCharacter ℂ modulus
  isPrimitive : character.IsPrimitive
  ne_one : character ≠ 1
  sq_eq_one : character ^ 2 = 1

instance (psi : GoldfeldPrimitiveRealCharacter) : NeZero psi.modulus :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt psi.modulus_gt_one)⟩

def goldfeldPrimitiveNearOneZero
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) : Prop :=
  ∃ beta : ℝ,
    1 - c * (psi.modulus : ℝ) ^ (-epsilon) < beta ∧
      beta < 1 ∧
        DirichletCharacter.LFunction psi.character (beta : ℂ) = 0

def goldfeldPrimitiveZeroFree
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) : Prop :=
  ∀ sigma : ℝ,
    1 - c * (psi.modulus : ℝ) ^ (-epsilon) < sigma →
      DirichletCharacter.LFunction psi.character (sigma : ℂ) ≠ 0

theorem goldfeldPrimitiveRealCharacter_distinct_iff_ne
    (psi1 psi2 : GoldfeldPrimitiveRealCharacter) :
    goldfeldCharactersDistinct psi1.character psi2.character ↔
      psi1 ≠ psi2 := by
  constructor
  · intro hdistinct heq
    subst psi2
    exact (goldfeldCharactersDistinct_same_level_iff _ _).mp hdistinct rfl
  · intro hne
    by_cases hmodulus : psi1.modulus = psi2.modulus
    · cases psi1 with
      | mk q hq chi hprimitive hchi hsquare =>
        cases psi2 with
        | mk q' hq' chi' hprimitive' hchi' hsquare' =>
          dsimp at hmodulus
          subst q'
          letI : NeZero q :=
            ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hq)⟩
          rw [goldfeldCharactersDistinct_same_level_iff]
          intro hcharacters
          apply hne
          cases hcharacters
          rfl
    · exact goldfeldCharactersDistinct_of_modulus_ne
        psi1.character psi2.character psi1.isPrimitive psi2.isPrimitive
        hmodulus

theorem goldfeldPrimitiveNearOneZero_iff_not_zeroFree
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) :
    goldfeldPrimitiveNearOneZero epsilon c psi ↔
      ¬ goldfeldPrimitiveZeroFree epsilon c psi := by
  constructor
  · rintro ⟨beta, hbetaLower, _, hzero⟩ hzeroFree
    exact hzeroFree beta hbetaLower hzero
  · intro hnotZeroFree
    classical
    simp only [goldfeldPrimitiveZeroFree, not_forall,
      not_ne_iff] at hnotZeroFree
    obtain ⟨sigma, hsigmaLower, hzero⟩ := hnotZeroFree
    refine ⟨sigma, hsigmaLower, ?_, hzero⟩
    by_contra hsigmaOne
    have hone : 1 ≤ sigma := le_of_not_gt hsigmaOne
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re
      psi.character (.inl psi.ne_one) (by simpa using hone)) hzero

theorem exists_goldfeldPrimitiveNearOneZero_subsingleton :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        Set.Subsingleton
          {psi : GoldfeldPrimitiveRealCharacter |
            goldfeldPrimitiveNearOneZero epsilon c psi} := by
  intro epsilon hepsilon
  obtain ⟨A, hA, c0, hc0, hLValueLower⟩ :=
    exists_goldfeldDistinctLValueLowerBound
  let r : ℝ := epsilon / 20
  let c : ℝ := min (1 / 2) (min
    (epsilon / (2 * (A : ℝ))) (c0 * r ^ 5 / 1024))
  have hAOne : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
  have hAPos : (0 : ℝ) < A := zero_lt_one.trans_le hAOne
  have hrPos : 0 < r := by dsimp [r]; positivity
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hcHalf : c ≤ 1 / 2 := by
    dsimp [c]
    exact min_le_left _ _
  have hcExponent : c ≤ epsilon / (2 * (A : ℝ)) := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcLog : c ≤ c0 * r ^ 5 / 1024 := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hordered :
      ∀ (psi1 psi : GoldfeldPrimitiveRealCharacter),
        psi1.modulus ≤ psi.modulus →
          goldfeldPrimitiveNearOneZero epsilon c psi1 →
            goldfeldPrimitiveNearOneZero epsilon c psi →
              goldfeldCharactersDistinct psi1.character psi.character →
                False := by
    intro psi1 psi hmoduli hnear1 hnear hdistinct
    obtain ⟨beta1, hbeta1Lower, hbeta1One, hzero1⟩ := hnear1
    obtain ⟨beta, hbetaLower, hbetaOne, hzero⟩ := hnear
    let Q : ℝ := psi.modulus
    let L : ℝ := Real.log Q
    let delta1 : ℝ := 1 - beta1
    let delta : ℝ := 1 - beta
    have hQOne : 1 ≤ Q := by
      dsimp [Q]
      exact_mod_cast psi.modulus_gt_one.le
    have hQPos : 0 < Q := zero_lt_one.trans_le hQOne
    have hLPos : 0 < L := by
      dsimp [L, Q]
      exact Real.log_pos (by exact_mod_cast psi.modulus_gt_one)
    have hq1PowLeOne :
        (psi1.modulus : ℝ) ^ (-epsilon) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast psi1.modulus_gt_one.le) (by linarith)
    have hqPowLeOne : Q ^ (-epsilon) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hQOne (by linarith)
    have hdelta1Near :
        delta1 < c * (psi1.modulus : ℝ) ^ (-epsilon) := by
      dsimp [delta1]
      linarith
    have hdeltaNear : delta < c * Q ^ (-epsilon) := by
      dsimp [delta, Q] at hbetaLower ⊢
      linarith
    have hdelta1LtC : delta1 < c :=
      hdelta1Near.trans_le (mul_le_of_le_one_right hcPos.le hq1PowLeOne)
    have hdeltaLtC : delta < c :=
      hdeltaNear.trans_le (mul_le_of_le_one_right hcPos.le hqPowLeOne)
    have hbeta1Half : 1 / 2 < beta1 := by
      have hbase : 1 - c ≤
          1 - c * (psi1.modulus : ℝ) ^ (-epsilon) := by
        linarith [mul_le_of_le_one_right hcPos.le hq1PowLeOne]
      linarith
    have hbetaHalf : 1 / 2 < beta := by
      have hbase : 1 - c ≤ 1 - c * Q ^ (-epsilon) := by
        linarith [mul_le_of_le_one_right hcPos.le hqPowLeOne]
      dsimp [Q] at hbase hbetaLower
      linarith
    have hLower := hLValueLower psi1.modulus psi.modulus
      psi1.modulus_gt_one hmoduli psi1.character psi.character
      psi1.ne_one psi.ne_one psi1.sq_eq_one psi.sq_eq_one hdistinct
      beta1 (by linarith) hbeta1One hzero1
    have hUpper := norm_LFunction_one_of_real_zero_le
      psi.modulus_gt_one psi.character psi.ne_one hbetaOne.le hzero
    have hLThreePos : 0 < L ^ 3 := pow_pos hLPos 3
    have hcomparison :
        c0 * Q ^ (-((A : ℝ) * delta1)) ≤
          512 * delta * Q ^ (delta / 2) * L ^ 5 := by
      calc
        c0 * Q ^ (-((A : ℝ) * delta1)) ≤
            ‖DirichletCharacter.LFunction psi.character (1 : ℂ)‖ *
              L ^ 3 := by
          apply (div_le_iff₀ hLThreePos).mp
          simpa [Q, L, delta1] using hLower
        _ ≤ (512 * delta * Q ^ (delta / 2) * L ^ 2) * L ^ 3 :=
          mul_le_mul_of_nonneg_right (by simpa [Q, L, delta] using hUpper)
            hLThreePos.le
        _ = 512 * delta * Q ^ (delta / 2) * L ^ 5 := by ring
    have hdelta1Exponent :
        (A : ℝ) * delta1 < epsilon / 2 := by
      have hdelta1Bound :
          delta1 < epsilon / (2 * (A : ℝ)) :=
        hdelta1LtC.trans_le hcExponent
      calc
        (A : ℝ) * delta1 <
            (A : ℝ) * (epsilon / (2 * (A : ℝ))) :=
          mul_lt_mul_of_pos_left hdelta1Bound hAPos
        _ = epsilon / 2 := by field_simp [hAPos.ne']
    have hleftFloor :
        c0 * Q ^ (-epsilon / 2) ≤
          c0 * Q ^ (-((A : ℝ) * delta1)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQOne (by linarith)) hc0.le
    have hcScaled : c * (2 * (A : ℝ)) ≤ epsilon :=
      (le_div_iff₀ (by positivity : 0 < 2 * (A : ℝ))).mp hcExponent
    have hcEpsilonHalf : c ≤ epsilon / 2 := by
      have htwoC : 2 * c ≤ c * (2 * (A : ℝ)) := by
        calc
          2 * c = c * (2 * 1) := by ring
          _ ≤ c * (2 * (A : ℝ)) := by gcongr
      linarith
    have hdeltaQuarter : delta / 2 ≤ epsilon / 4 := by
      linarith
    have hdeltaPower : Q ^ (delta / 2) ≤ Q ^ (epsilon / 4) :=
      Real.rpow_le_rpow_of_exponent_le hQOne hdeltaQuarter
    have hlogBase : L ≤ Q ^ r / r := by
      simpa [L, Q] using
        Real.log_natCast_le_rpow_div psi.modulus hrPos
    have hlogPow : L ^ 5 ≤ Q ^ (epsilon / 4) / r ^ 5 := by
      calc
        L ^ 5 ≤ (Q ^ r / r) ^ 5 :=
          pow_le_pow_left₀ hLPos.le hlogBase 5
        _ = Q ^ (epsilon / 4) / r ^ 5 := by
          rw [div_pow, ← Real.rpow_mul_natCast hQPos.le]
          congr 2
          dsimp [r]
          ring
    have hpowThreeQuarter :
        Q ^ (-epsilon) * Q ^ (epsilon / 4) =
          Q ^ (-3 * epsilon / 4) := by
      rw [← Real.rpow_add hQPos]
      congr 1
      ring
    have hpowHalf :
        Q ^ (-3 * epsilon / 4) * Q ^ (epsilon / 4) =
          Q ^ (-epsilon / 2) := by
      rw [← Real.rpow_add hQPos]
      congr 1
      ring
    have hupperStrict :
        512 * delta * Q ^ (delta / 2) * L ^ 5 <
          c0 * Q ^ (-epsilon / 2) := by
      calc
        512 * delta * Q ^ (delta / 2) * L ^ 5 <
            512 * (c * Q ^ (-epsilon)) * Q ^ (delta / 2) *
              L ^ 5 := by gcongr
        _ ≤ 512 * (c * Q ^ (-epsilon)) * Q ^ (epsilon / 4) *
              L ^ 5 := by gcongr
        _ = 512 * c * Q ^ (-3 * epsilon / 4) * L ^ 5 := by
          rw [show 512 * (c * Q ^ (-epsilon)) * Q ^ (epsilon / 4) *
              L ^ 5 = 512 * c *
                (Q ^ (-epsilon) * Q ^ (epsilon / 4)) * L ^ 5 by ring,
            hpowThreeQuarter]
        _ ≤ 512 * (c0 * r ^ 5 / 1024) *
              Q ^ (-3 * epsilon / 4) *
                (Q ^ (epsilon / 4) / r ^ 5) := by gcongr
        _ = (c0 / 2) * Q ^ (-epsilon / 2) := by
          calc
            512 * (c0 * r ^ 5 / 1024) * Q ^ (-3 * epsilon / 4) *
                (Q ^ (epsilon / 4) / r ^ 5) =
                (c0 / 2) *
                  (Q ^ (-3 * epsilon / 4) * Q ^ (epsilon / 4)) := by
              field_simp [hrPos.ne']; ring
            _ = (c0 / 2) * Q ^ (-epsilon / 2) := by rw [hpowHalf]
        _ < c0 * Q ^ (-epsilon / 2) := by
          have hproductPos : 0 < c0 * Q ^ (-epsilon / 2) :=
            mul_pos hc0 (Real.rpow_pos_of_pos hQPos _)
          nlinarith
    exact (not_lt_of_ge (hleftFloor.trans hcomparison)) hupperStrict
  refine ⟨c, hcPos, ?_⟩
  intro psi1 hnear1 psi2 hnear2
  by_contra hne
  rcases le_total psi1.modulus psi2.modulus with hle | hle
  · exact hordered psi1 psi2 hle hnear1 hnear2
      ((goldfeldPrimitiveRealCharacter_distinct_iff_ne _ _).2 hne)
  · exact hordered psi2 psi1 hle hnear2 hnear1
      ((goldfeldPrimitiveRealCharacter_distinct_iff_ne _ _).2 (Ne.symm hne))

theorem exists_goldfeldPrimitiveExceptionalCharacter :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∃ exception : Option GoldfeldPrimitiveRealCharacter,
          ∀ psi : GoldfeldPrimitiveRealCharacter,
            some psi ≠ exception →
              goldfeldPrimitiveZeroFree epsilon c psi := by
  intro epsilon hepsilon
  obtain ⟨c, hc, hsubsingleton⟩ :=
    exists_goldfeldPrimitiveNearOneZero_subsingleton epsilon hepsilon
  refine ⟨c, hc, ?_⟩
  classical
  by_cases hnonempty :
      Set.Nonempty
        {psi : GoldfeldPrimitiveRealCharacter |
          goldfeldPrimitiveNearOneZero epsilon c psi}
  · obtain ⟨exception, hexception⟩ := hnonempty
    refine ⟨some exception, ?_⟩
    intro psi hpsi
    by_contra hnotZeroFree
    have hnear :=
      (goldfeldPrimitiveNearOneZero_iff_not_zeroFree _ _ _).2
        hnotZeroFree
    have heq : psi = exception := hsubsingleton hnear hexception
    exact hpsi (congrArg some heq)
  · refine ⟨none, ?_⟩
    intro psi _
    by_contra hnotZeroFree
    exact hnonempty ⟨psi,
      (goldfeldPrimitiveNearOneZero_iff_not_zeroFree _ _ _).2
        hnotZeroFree⟩

end BoundedGaps.Maynard

end

/-! ## Siegel's real-character zero-free region

Source module `BoundedGaps.BombieriVinogradov.Analytic.SiegelZeroFreeRegion`. -/

noncomputable section

open Complex

namespace BoundedGaps.Maynard

theorem exists_siegelPrimitiveRealCharacterZeroFree :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∀ psi : GoldfeldPrimitiveRealCharacter,
          goldfeldPrimitiveZeroFree epsilon c psi := by
  intro epsilon hepsilon
  obtain ⟨c0, hc0, exception, hzeroFree⟩ :=
    exists_goldfeldPrimitiveExceptionalCharacter epsilon hepsilon
  cases exception with
  | none =>
      let c : ℝ := min c0 (1 / 2)
      have hcPos : 0 < c := by
        dsimp [c]
        exact lt_min hc0 (by norm_num)
      refine ⟨c, hcPos, ?_⟩
      intro psi sigma hsigma
      apply hzeroFree psi (by simp) sigma
      have hcLe : c ≤ c0 := by
        dsimp [c]
        exact min_le_left _ _
      have hweightNonneg :
          0 ≤ (psi.modulus : ℝ) ^ (-epsilon) :=
        Real.rpow_nonneg (Nat.cast_nonneg psi.modulus) _
      have hscaled :=
        mul_le_mul_of_nonneg_right hcLe hweightNonneg
      linarith
  | some exception =>
      let gap : ℝ :=
        1 / ((2 ^ 22 : ℝ) * Real.sqrt (exception.modulus : ℝ) *
          (Real.log (exception.modulus : ℝ)) ^ 4)
      let weight : ℝ :=
        (exception.modulus : ℝ) ^ (-epsilon)
      let c : ℝ := min (min c0 (1 / 2)) (gap / weight)
      have hmodulusPos : (0 : ℝ) < exception.modulus := by
        exact_mod_cast (Nat.zero_lt_of_lt exception.modulus_gt_one)
      have hlogPos : 0 < Real.log (exception.modulus : ℝ) :=
        Real.log_pos (by exact_mod_cast exception.modulus_gt_one)
      have hgapPos : 0 < gap := by
        dsimp [gap]
        positivity
      have hweightPos : 0 < weight := by
        dsimp [weight]
        exact Real.rpow_pos_of_pos hmodulusPos _
      have hcPos : 0 < c := by
        dsimp [c]
        exact lt_min (lt_min hc0 (by norm_num))
          (div_pos hgapPos hweightPos)
      have hcLe : c ≤ c0 := by
        dsimp [c]
        exact (min_le_left _ _).trans (min_le_left _ _)
      have hcGap : c * weight ≤ gap := by
        apply (le_div_iff₀ hweightPos).mp
        dsimp [c]
        exact min_le_right _ _
      refine ⟨c, hcPos, ?_⟩
      intro psi
      by_cases hpsi : psi = exception
      · subst psi
        intro sigma hsigma
        apply effectiveQuadraticLFunction_ofReal_ne_zero
          exception.modulus_gt_one exception.character exception.ne_one
            exception.sq_eq_one
        have hthreshold : 1 - gap ≤ 1 - c * weight := by
          linarith
        exact hthreshold.trans_lt (by simpa [weight] using hsigma)
      · intro sigma hsigma
        apply hzeroFree psi (by simpa using hpsi) sigma
        have hweightNonneg :
            0 ≤ (psi.modulus : ℝ) ^ (-epsilon) :=
          Real.rpow_nonneg (Nat.cast_nonneg psi.modulus) _
        have hscaled :=
          mul_le_mul_of_nonneg_right hcLe hweightNonneg
        linarith

theorem exists_siegelRealCharacterZeroFree :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∀ (q : ℕ) [NeZero q]
          (chi : DirichletCharacter ℂ q),
            chi ≠ 1 →
              chi ^ 2 = 1 →
                ∀ sigma : ℝ,
                  1 - c * (q : ℝ) ^ (-epsilon) < sigma →
                    DirichletCharacter.LFunction chi (sigma : ℂ) ≠ 0 := by
  intro epsilon hepsilon
  obtain ⟨c0, hc0, hprimitive⟩ :=
    exists_siegelPrimitiveRealCharacterZeroFree epsilon hepsilon
  let c : ℝ := min c0 (1 / 2)
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min hc0 (by norm_num)
  have hcLe : c ≤ c0 := by
    dsimp [c]
    exact min_le_left _ _
  have hcHalf : c ≤ 1 / 2 := by
    dsimp [c]
    exact min_le_right _ _
  refine ⟨c, hcPos, ?_⟩
  intro q _ chi hchi hsquare sigma hsigma
  have hconductorOne : 1 < chi.conductor := by
    have hconductorZero : chi.conductor ≠ 0 := chi.conductor_ne_zero
    have hconductorNeOne : chi.conductor ≠ 1 := by
      intro hconductor
      exact hchi
        (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hconductor)
    omega
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hprimitiveNeOne : chi.primitiveCharacter ≠ 1 := by
    intro hprincipal
    apply hchi
    rw [← chi.changeLevel_primitiveCharacter]
    exact (DirichletCharacter.changeLevel_eq_one_iff
      chi.conductor_dvd_level).2 hprincipal
  have hprimitiveSquare : chi.primitiveCharacter ^ 2 = 1 := by
    apply DirichletCharacter.changeLevel_injective
      chi.conductor_dvd_level
    rw [map_pow, chi.changeLevel_primitiveCharacter, hsquare, map_one]
  let psi : GoldfeldPrimitiveRealCharacter :=
    { modulus := chi.conductor
      modulus_gt_one := hconductorOne
      character := chi.primitiveCharacter
      isPrimitive := chi.primitiveCharacter_isPrimitive
      ne_one := hprimitiveNeOne
      sq_eq_one := hprimitiveSquare }
  have hconductorLe : chi.conductor ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hconductorPos : (0 : ℝ) < chi.conductor := by
    exact_mod_cast (Nat.zero_lt_of_lt hconductorOne)
  have hconductorLevel : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast hconductorLe
  have hnegativePower :
      (q : ℝ) ^ (-epsilon) ≤
        (chi.conductor : ℝ) ^ (-epsilon) :=
    Real.rpow_le_rpow_of_nonpos hconductorPos hconductorLevel
      (by linarith)
  have hconductorWeightNonneg :
      0 ≤ (chi.conductor : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg (Nat.cast_nonneg chi.conductor) _
  have hscaled :
      c * (q : ℝ) ^ (-epsilon) ≤
        c0 * (chi.conductor : ℝ) ^ (-epsilon) := by
    calc
      c * (q : ℝ) ^ (-epsilon) ≤
          c * (chi.conductor : ℝ) ^ (-epsilon) :=
        mul_le_mul_of_nonneg_left hnegativePower hcPos.le
      _ ≤ c0 * (chi.conductor : ℝ) ^ (-epsilon) :=
        mul_le_mul_of_nonneg_right hcLe hconductorWeightNonneg
  have hprimitiveThreshold :
      1 - c0 * (chi.conductor : ℝ) ^ (-epsilon) < sigma := by
    linarith
  have hprimitiveNonzero :
      DirichletCharacter.LFunction chi.primitiveCharacter
          (sigma : ℂ) ≠ 0 := by
    apply hprimitive psi sigma
    simpa [psi] using hprimitiveThreshold
  have hlevelOne : (1 : ℝ) ≤ q := by
    exact_mod_cast NeZero.pos q
  have hlevelWeightLeOne :
      (q : ℝ) ^ (-epsilon) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlevelOne (by linarith)
  have hscaledHalf : c * (q : ℝ) ^ (-epsilon) ≤ 1 / 2 :=
    (mul_le_of_le_one_right hcPos.le hlevelWeightLeOne).trans hcHalf
  have hsigmaPos : 0 < sigma := by
    linarith
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
    (.inl hchi)]
  exact mul_ne_zero hprimitiveNonzero
    (inducingEulerProduct_ne_zero_of_re_pos chi (by simpa using hsigmaPos))

end BoundedGaps.Maynard

end

/-! ## A small quadratic L-value forces a nearby real zero

Source module `ErdosProblems.Erdos1141.SiegelNearOne`. -/

noncomputable section

namespace Pollack17

open Complex MeasureTheory Metric Set Filter

open ArithmeticFunction

open scoped BigOperators ComplexOrder Real Topology

open BoundedGaps.Maynard

private lemma SiegelNearOne_three_le_modulus_of_character_ne_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    3 ≤ q := by
  by_contra hq
  have hqPos : 0 < q := NeZero.pos q
  have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
  have hqTwo : q = 2 := by omega
  subst q
  have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
    norm_num
  exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)

private lemma SiegelNearOne_one_lt_log_modulus
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : (3 : ℝ) ≤ q := by
    exact_mod_cast SiegelNearOne_three_le_modulus_of_character_ne_one chi hchi
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThree))

private lemma SiegelNearOne_norm_first_order_remainder_right_le
    {f f' f'' : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b,
      HasDerivWithinAt f (f' t) (Icc a b) t)
    (hf' : ∀ t ∈ Icc a b,
      HasDerivWithinAt f' (f'' t) (Icc a b) t)
    (hbound : ∀ t ∈ Ico a b, ‖f'' t‖ ≤ M) :
    ‖f b - f a - ((b - a : ℝ) : ℂ) * f' a‖ ≤
      M * (b - a) ^ 2 := by
  have hvar : ∀ t ∈ Icc a b, ‖f' t - f' a‖ ≤ M * (t - a) :=
    norm_image_sub_le_of_norm_deriv_le_segment' hf' hbound
  let g : ℝ → ℂ := fun t ↦ f t - ((t - a : ℝ) : ℂ) * f' a
  have hg : ∀ t ∈ Icc a b,
      HasDerivWithinAt g (f' t - f' a) (Icc a b) t := by
    intro t ht
    have hlinear : HasDerivAt
        (fun u : ℝ ↦ ((u - a : ℝ) : ℂ) * f' a) (f' a) t := by
      simpa only [id_eq, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
        ((((hasDerivAt_id t).sub_const a).ofReal_comp).mul_const (f' a))
    change HasDerivWithinAt
      (fun u : ℝ ↦ f u - ((u - a : ℝ) : ℂ) * f' a)
        (f' t - f' a) (Icc a b) t
    exact (hf t ht).sub hlinear.hasDerivWithinAt
  have hgbound : ∀ t ∈ Ico a b,
      ‖f' t - f' a‖ ≤ M * (b - a) := by
    intro t ht
    exact (hvar t ⟨ht.1, ht.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2.le a) hM)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hg hgbound b (right_mem_Icc.mpr hab)
  dsimp [g] at hmean
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at hmean
  have heq :
      f b - ((b - a : ℝ) : ℂ) * f' a - f a =
        f b - f a - ((b - a : ℝ) : ℂ) * f' a := by ring
  rw [heq] at hmean
  simpa [g, pow_two, mul_assoc] using hmean

private lemma SiegelNearOne_norm_first_order_remainder_left_le
    {f f' f'' : ℝ → ℂ} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hf : ∀ t ∈ Icc a b,
      HasDerivWithinAt f (f' t) (Icc a b) t)
    (hf' : ∀ t ∈ Icc a b,
      HasDerivWithinAt f' (f'' t) (Icc a b) t)
    (hbound : ∀ t ∈ Ico a b, ‖f'' t‖ ≤ M) :
    ‖f a - f b - ((a - b : ℝ) : ℂ) * f' b‖ ≤
      M * (b - a) ^ 2 := by
  have hvar : ∀ t ∈ Icc a b, ‖f' t - f' b‖ ≤ M * (b - t) := by
    intro t ht
    have hsub : Icc t b ⊆ Icc a b := by
      intro u hu
      exact ⟨ht.1.trans hu.1, hu.2⟩
    have hderiv : ∀ u ∈ Icc t b,
        HasDerivWithinAt f' (f'' u) (Icc t b) u := by
      intro u hu
      exact (hf' u (hsub hu)).mono hsub
    have hbd : ∀ u ∈ Ico t b, ‖f'' u‖ ≤ M := by
      intro u hu
      exact hbound u ⟨ht.1.trans hu.1, hu.2⟩
    have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
      hderiv hbd b (right_mem_Icc.mpr ht.2)
    simpa [norm_sub_rev] using hmean
  let g : ℝ → ℂ := fun t ↦ f t - ((t - b : ℝ) : ℂ) * f' b
  have hg : ∀ t ∈ Icc a b,
      HasDerivWithinAt g (f' t - f' b) (Icc a b) t := by
    intro t ht
    have hlinear : HasDerivAt
        (fun u : ℝ ↦ ((u - b : ℝ) : ℂ) * f' b) (f' b) t := by
      simpa only [id_eq, Complex.ofReal_sub, Complex.ofReal_one, one_mul] using
        ((((hasDerivAt_id t).sub_const b).ofReal_comp).mul_const (f' b))
    change HasDerivWithinAt
      (fun u : ℝ ↦ f u - ((u - b : ℝ) : ℂ) * f' b)
        (f' t - f' b) (Icc a b) t
    exact (hf t ht).sub hlinear.hasDerivWithinAt
  have hgbound : ∀ t ∈ Ico a b,
      ‖f' t - f' b‖ ≤ M * (b - a) := by
    intro t ht
    exact (hvar t ⟨ht.1, ht.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left ht.1 b) hM)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hg hgbound b (right_mem_Icc.mpr hab)
  rw [norm_sub_rev] at hmean
  dsimp [g] at hmean
  simp only [sub_self, Complex.ofReal_zero, zero_mul, sub_zero] at hmean
  have heq :
      f a - ((a - b : ℝ) : ℂ) * f' b - f b =
        f a - f b - ((a - b : ℝ) : ℂ) * f' b := by ring
  rw [heq] at hmean
  simpa [g, pow_two, mul_assoc] using hmean

private lemma SiegelNearOne_hasDerivAt_deriv_LFunction_ofReal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (sigma : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ deriv (DirichletCharacter.LFunction chi) (t : ℂ))
      (iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ))
      sigma := by
  have hdiff : Differentiable ℂ
      (deriv (DirichletCharacter.LFunction chi)) :=
    (DirichletCharacter.differentiable_LFunction hchi).deriv
  have h := (hdiff (sigma : ℂ)).hasDerivAt.comp_ofReal
  simpa [iteratedDeriv_succ'] using h

theorem norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma : ℝ}
    (hsigmaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ sigma)
    (hsigmaUpper : sigma ≤ 3 / 2) :
    ‖iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
      16384 * (Real.log (q : ℝ)) ^ 3 := by
  let L := Real.log (q : ℝ)
  let r := 1 / (16 * L)
  have hLone : 1 < L := SiegelNearOne_one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hrPos : 0 < r := by positivity
  have hrLe : r ≤ 1 / 16 := by
    dsimp [r]
    rw [div_le_iff₀ (by positivity : 0 < 16 * L)]
    nlinarith
  have hsigmaPos : 0 < sigma := by
    have hquarter : 1 / (4 * L) < 1 := by
      rw [div_lt_one (by positivity : 0 < 4 * L)]
      nlinarith
    change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
    linarith
  have hsphere : ∀ z ∈ sphere (sigma : ℂ) r,
      ‖DirichletCharacter.LFunction chi z‖ ≤ 32 * L := by
    intro z hz
    have hdist : ‖z - (sigma : ℂ)‖ = r := by
      simpa [dist_eq_norm] using mem_sphere.mp hz
    have hreDiff : |z.re - sigma| ≤ r := by
      calc
        |z.re - sigma| = |(z - (sigma : ℂ)).re| := by simp
        _ ≤ ‖z - (sigma : ℂ)‖ := Complex.abs_re_le_norm _
        _ = r := hdist
    have hzRe : 1 - 5 / (16 * L) ≤ z.re := by
      have hrad : r = 1 / (16 * L) := rfl
      rw [hrad] at hreDiff
      have hlower := (abs_le.mp hreDiff).1
      change 1 - 1 / (4 * L) ≤ sigma at hsigmaNear
      have hratio : 1 / (4 * L) = 4 * (1 / (16 * L)) := by
        field_simp [hLpos.ne']
        ring
      rw [hratio] at hsigmaNear
      have hfive : 5 / (16 * L) = 5 * (1 / (16 * L)) := by ring
      rw [hfive]
      linarith
    have hzNorm : ‖z‖ ≤ 2 := by
      calc
        ‖z‖ ≤ ‖(sigma : ℂ)‖ + ‖z - (sigma : ℂ)‖ := by
          simpa [add_comm] using norm_add_le (z - (sigma : ℂ)) (sigma : ℂ)
        _ = sigma + r := by simp [abs_of_pos hsigmaPos, hdist]
        _ ≤ 2 := by linarith
    simpa [L] using norm_LFunction_near_one_le hq chi hchi hzRe hzNorm
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    2 hrPos (DirichletCharacter.differentiable_LFunction hchi).diffContOnCl hsphere
  calc
    ‖iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)‖ ≤
        Nat.factorial 2 * (32 * L) / r ^ 2 := hCauchy
    _ = 16384 * (Real.log (q : ℝ)) ^ 3 := by
      change 2 * (32 * L) / (1 / (16 * L)) ^ 2 = 16384 * L ^ 3
      field_simp [hLpos.ne']
      ring

theorem one_le_riemannZeta_mul_LFunction_ofReal
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q)
    (hsquare : chi ^ 2 = 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    (1 : ℂ) ≤ riemannZeta (sigma : ℂ) *
      DirichletCharacter.LFunction chi (sigma : ℂ) := by
  have hsum : LSeriesSummable chi.zetaMul (sigma : ℂ) :=
    chi.LSeriesSummable_zetaMul (by simpa using hsigma)
  have hterm : (1 : ℂ) ≤ LSeries chi.zetaMul (sigma : ℂ) := by
    have hnonneg (n : ℕ) :
        0 ≤ LSeries.term (chi.zetaMul ·) (sigma : ℂ) n :=
      LSeries.term_nonneg (DirichletCharacter.zetaMul_nonneg hsquare n) sigma
    have hone :
        LSeries.term (chi.zetaMul ·) (sigma : ℂ) 1 = (1 : ℂ) := by
      rw [LSeries.term_of_ne_zero one_ne_zero]
      simp [chi.isMultiplicative_zetaMul.map_one]
    calc
      (1 : ℂ) = ∑ n ∈ ({1} : Finset ℕ),
          LSeries.term (chi.zetaMul ·) (sigma : ℂ) n := by
        simp only [Finset.sum_singleton]
        exact hone.symm
      _ ≤ ∑' n : ℕ, LSeries.term (chi.zetaMul ·) (sigma : ℂ) n :=
        hsum.sum_le_tsum ({1} : Finset ℕ) (fun n _ ↦ hnonneg n)
      _ = LSeries chi.zetaMul (sigma : ℂ) := rfl
  calc
    (1 : ℂ) ≤ LSeries chi.zetaMul (sigma : ℂ) := hterm
    _ = riemannZeta (sigma : ℂ) *
        DirichletCharacter.LFunction chi (sigma : ℂ) := by
      rw [DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul,
        LSeries_convolution']
      · have hs : 1 < ((sigma : ℂ)).re := by simpa using hsigma
        congr 1
        · simp only [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
        · rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
          exact (LSeries_congr chi.apply_eq_toArithmeticFunction_apply (sigma : ℂ)).symm
      · exact LSeriesSummable_zeta_iff.mpr (by simpa using hsigma)
      · exact (LSeriesSummable_congr _ fun h ↦
          (chi.apply_eq_toArithmeticFunction_apply h).symm).mpr
            (ZMod.LSeriesSummable_of_one_lt_re chi (by simpa using hsigma))

theorem riemannZeta_ofReal_eq_tsum_rpow
    {sigma : ℝ} (hsigma : 1 < sigma) :
    riemannZeta (sigma : ℂ) =
      ((∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
  calc
    riemannZeta (sigma : ℂ) =
        ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (sigma : ℂ) :=
      zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hsigma)
    _ = ∑' n : ℕ, (((n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
      apply tsum_congr
      intro n
      have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have hcpow :
          ((((n : ℝ) + 1) ^ sigma : ℝ) : ℂ) =
            (((n : ℝ) + 1 : ℝ) : ℂ) ^ (sigma : ℂ) :=
        @Complex.ofReal_cpow ((n : ℝ) + 1) hn sigma
      rw [@Real.rpow_neg ((n : ℝ) + 1) hn sigma]
      calc
        1 / ((n : ℂ) + 1) ^ (sigma : ℂ) =
            ((((n : ℝ) + 1) ^ sigma : ℝ) : ℂ)⁻¹ := by
          rw [show (n : ℂ) + 1 = (((n : ℝ) + 1 : ℝ) : ℂ) by norm_num,
            ← hcpow, one_div]
        _ = (((((n : ℝ) + 1) ^ sigma)⁻¹ : ℝ) : ℂ) :=
          (Complex.ofReal_inv _).symm
    _ = ((∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma) : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm

theorem riemannZeta_ofReal_le_one_add_inv_sub_one
    {sigma : ℝ} (hsigma : 1 < sigma) :
    riemannZeta (sigma : ℂ) ≤
      (((1 + 1 / (sigma - 1) : ℝ) : ℂ)) := by
  let f : ℝ → ℝ := fun x ↦ x ^ (-sigma)
  have hanti : AntitoneOn f (Ici (1 : ℝ)) := by
    intro a ha b hb hab
    change 1 ≤ a at ha
    change 1 ≤ b at hb
    dsimp [f]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)
  have hint : IntegrableOn f (Ioi (1 : ℝ)) := by
    dsimp [f]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hnonneg : ∀ x ∈ Ioi (1 : ℝ), 0 ≤ f x := by
    intro x hx
    change 1 < x at hx
    dsimp [f]
    exact Real.rpow_nonneg (by linarith) _
  have hanti' : AntitoneOn f (Ici ((1 : ℕ) : ℝ)) := by
    simpa using hanti
  have hint' : IntegrableOn f (Ioi ((1 : ℕ) : ℝ)) := by
    simpa using hint
  have hnonneg' : ∀ x ∈ Ioi ((1 : ℕ) : ℝ), 0 ≤ f x := by
    simpa using hnonneg
  have htail := AntitoneOn.tsum_comp_add_le_integral
    (f := f) 1 hanti' hint' hnonneg'
  norm_num at htail
  have hintegral : ∫ x in Ioi (1 : ℝ), f x = 1 / (sigma - 1) := by
    dsimp [f]
    rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
    rw [Real.one_rpow]
    have hleft : -sigma + 1 ≠ 0 := by linarith
    have hright : sigma - 1 ≠ 0 := by linarith
    field_simp [hleft, hright]
    ring
  rw [hintegral] at htail
  have hsummable : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-sigma)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((_root_.summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1)))
  have hreal :
      (∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma)) ≤
        1 + 1 / (sigma - 1) := by
    rw [hsummable.tsum_eq_zero_add]
    simpa [f, add_assoc, Nat.cast_add, Nat.cast_one,
      Real.rpow_neg, one_div] using add_le_add_left htail 1
  rw [riemannZeta_ofReal_eq_tsum_rpow hsigma]
  exact_mod_cast hreal

theorem one_le_riemannZeta_ofReal
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (1 : ℂ) ≤ riemannZeta (sigma : ℂ) := by
  have hsummable : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ (-sigma)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((_root_.summable_nat_add_iff 1).mpr
        (Real.summable_nat_rpow.mpr (by linarith : -sigma < -1)))
  have htail : 0 ≤ ∑' n : ℕ, (((n : ℝ) + 1) + 1) ^ (-sigma) :=
    tsum_nonneg fun _ ↦ Real.rpow_nonneg (by positivity) _
  rw [riemannZeta_ofReal_eq_tsum_rpow hsigma]
  apply Complex.le_def.mpr
  constructor
  · change (1 : ℝ) ≤ ∑' n : ℕ, (n + 1 : ℝ) ^ (-sigma)
    rw [hsummable.tsum_eq_zero_add]
    norm_num
    exact htail
  · simp

theorem sub_one_div_self_le_LFunction_ofReal
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) {sigma : ℝ} (hsigma : 1 < sigma) :
    ((((sigma - 1) / sigma : ℝ) : ℂ)) ≤
      DirichletCharacter.LFunction chi (sigma : ℂ) := by
  let Z := riemannZeta (sigma : ℂ)
  let V := DirichletCharacter.LFunction chi (sigma : ℂ)
  have hprod : (1 : ℂ) ≤ Z * V := by
    simpa [Z, V] using
      one_le_riemannZeta_mul_LFunction_ofReal chi hsquare hsigma
  have hZupper : Z ≤ (((1 + 1 / (sigma - 1) : ℝ) : ℂ)) := by
    simpa [Z] using riemannZeta_ofReal_le_one_add_inv_sub_one hsigma
  have hZlower : (1 : ℂ) ≤ Z := by
    simpa [Z] using one_le_riemannZeta_ofReal hsigma
  have hZim : Z.im = 0 := by
    simpa using (Complex.le_def.mp hZlower).2.symm
  have hVim : V.im = 0 := by
    have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (sigma : ℂ)
    apply Complex.conj_eq_iff_im.mp
    simpa [V] using hconj.symm
  have hprodRe : 1 ≤ Z.re * V.re := by
    have h := (Complex.le_def.mp hprod).1
    simpa [Complex.mul_re, hZim, hVim] using h
  have hZupperRe : Z.re ≤ 1 + 1 / (sigma - 1) := by
    have h := (Complex.le_def.mp hZupper).1
    change Z.re ≤ 1 + 1 / (sigma - 1) at h
    exact h
  have hZlowerRe : 1 ≤ Z.re := by
    simpa using (Complex.le_def.mp hZlower).1
  have hZpos : 0 < Z.re := zero_lt_one.trans_le hZlowerRe
  have hrecipZ : 1 / Z.re ≤ V.re := by
    apply (div_le_iff₀ hZpos).mpr
    simpa [one_div, mul_comm] using hprodRe
  have hrecipUpper :
      1 / (1 + 1 / (sigma - 1)) ≤ 1 / Z.re :=
    one_div_le_one_div_of_le hZpos hZupperRe
  have hsigmaPos : 0 < sigma := by linarith
  have hsubPos : 0 < sigma - 1 := by linarith
  have hid : 1 / (1 + 1 / (sigma - 1)) = (sigma - 1) / sigma := by
    field_simp [hsigmaPos.ne', hsubPos.ne']
    ring
  apply Complex.le_def.mpr
  constructor
  · change (sigma - 1) / sigma ≤ V.re
    rw [← hid]
    exact hrecipUpper.trans hrecipZ
  · simpa [V] using hVim.symm

theorem exists_real_zero_of_LFunction_one_re_lt
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    (hsmall :
      (DirichletCharacter.LFunction chi (1 : ℂ)).re <
        1 / ((2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3)) :
    ∃ beta : ℝ,
      1 - 8 * (DirichletCharacter.LFunction chi (1 : ℂ)).re ≤ beta ∧
      beta ≤ 1 ∧
      DirichletCharacter.LFunction chi (beta : ℂ) = 0 := by
  let L := Real.log (q : ℝ)
  let ell := (DirichletCharacter.LFunction chi (1 : ℂ)).re
  let delta := 8 * ell
  let M := 16384 * L ^ 3
  let F : ℝ → ℂ := fun sigma ↦
    DirichletCharacter.LFunction chi (sigma : ℂ)
  let F' : ℝ → ℂ := fun sigma ↦
    deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)
  let F'' : ℝ → ℂ := fun sigma ↦
    iteratedDeriv 2 (DirichletCharacter.LFunction chi) (sigma : ℂ)
  have hLone : 1 < L := SiegelNearOne_one_lt_log_modulus chi hchi
  have hLpos : 0 < L := zero_lt_one.trans hLone
  have hellPos : 0 < ell := by
    have heff := effectiveQuadraticLValueLowerBound hq chi hchi hsquare
    have heffRe := (Complex.le_def.mp heff).1
    have hbasePos : 0 <
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) := by
      positivity
    change 1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤ ell at heffRe
    exact hbasePos.trans_le heffRe
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hdenomPos : 0 < (2 ^ 24 : ℝ) * L ^ 3 := by positivity
  have hscaled : (2 ^ 24 : ℝ) * L ^ 3 * ell < 1 := by
    have hs : ell * ((2 ^ 24 : ℝ) * L ^ 3) < 1 := by
      apply (lt_div_iff₀ hdenomPos).mp
      simpa [L, ell] using hsmall
    simpa [mul_comm] using hs
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hdeltaNear : delta ≤ 1 / (4 * L) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * L)).mpr
    have hbase : 0 ≤ L * ell := mul_nonneg hLpos.le hellPos.le
    have hcomparison :
        32 * L * ell ≤ (2 ^ 24 : ℝ) * L ^ 3 * ell := by
      calc
        32 * L * ell ≤ (2 ^ 24 : ℝ) * (L * ell) := by
          nlinarith
        _ ≤ (2 ^ 24 : ℝ) * (L ^ 2 * (L * ell)) := by
          gcongr <;> nlinarith
        _ = (2 ^ 24 : ℝ) * L ^ 3 * ell := by ring
    dsimp [delta]
    convert hcomparison.trans hscaled.le using 1
    all_goals ring
  have hdeltaHalf : delta ≤ 1 / 2 := by
    have hquarter : 1 / (4 * L) < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity : 0 < 4 * L)]
      nlinarith
    exact hdeltaNear.trans hquarter.le
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have herror : 2 * M * delta ^ 2 < ell := by
    dsimp [M, delta]
    nlinarith
  have hrightRem :
      ‖F (1 + delta) - F 1 - (delta : ℂ) * F' 1‖ ≤
        M * delta ^ 2 := by
    have hraw := SiegelNearOne_norm_first_order_remainder_right_le
        (a := (1 : ℝ)) (b := 1 + delta) (M := M)
        (f := F) (f' := F') (f'' := F'')
        (by linarith) hMnonneg
        (by
          intro sigma _
          dsimp [F, F']
          exact ((DirichletCharacter.differentiable_LFunction hchi
            (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
        (by
          intro sigma _
          dsimp [F', F'']
          exact (SiegelNearOne_hasDerivAt_deriv_LFunction_ofReal chi hchi sigma).hasDerivWithinAt)
        (by
          intro sigma hsigma
          dsimp [F'']
          apply norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
            hq chi hchi
          · have hfrac : 0 < 1 / (4 * L) := by positivity
            have : 1 - 1 / (4 * L) < 1 := by linarith
            change 1 - 1 / (4 * L) ≤ sigma
            exact this.le.trans hsigma.1
          · linarith [hsigma.2, hdeltaHalf])
    simpa using hraw
  have hleftRem :
      ‖F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1‖ ≤
        M * delta ^ 2 := by
    have hraw := SiegelNearOne_norm_first_order_remainder_left_le
      (a := 1 - delta) (b := (1 : ℝ)) (M := M)
      (f := F) (f' := F') (f'' := F'')
      (by linarith : 1 - delta ≤ (1 : ℝ)) hMnonneg
      (by
        intro sigma _
        dsimp [F, F']
        exact ((DirichletCharacter.differentiable_LFunction hchi
          (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt)
      (by
        intro sigma _
        dsimp [F', F'']
        exact (SiegelNearOne_hasDerivAt_deriv_LFunction_ofReal chi hchi sigma).hasDerivWithinAt)
      (by
        intro sigma hsigma
        dsimp [F'']
        apply norm_iteratedDeriv_two_LFunction_ofReal_near_one_le
          hq chi hchi
        · change 1 - 1 / (4 * L) ≤ sigma
          linarith [hsigma.1, hdeltaNear]
        · linarith [hsigma.2])
    simpa using hraw
  have hrightLower : 4 * ell ≤ (F (1 + delta)).re := by
    have hcomplex := sub_one_div_self_le_LFunction_ofReal
      chi hchi hsquare (sigma := 1 + delta) (by linarith)
    have hre := (Complex.le_def.mp hcomplex).1
    have hratio : 4 * ell ≤ delta / (1 + delta) := by
      apply (le_div_iff₀ (by linarith : 0 < 1 + delta)).mpr
      dsimp [delta]
      nlinarith [hdeltaHalf]
    norm_num only [Complex.ofReal_re] at hre
    change ((1 + delta - 1) / (1 + delta) : ℝ) ≤
      (F (1 + delta)).re at hre
    have hre' : (delta / (1 + delta) : ℝ) ≤
        (F (1 + delta)).re := by
      convert hre using 1
      all_goals ring
    exact hratio.trans hre'
  have hrightError :
      (F (1 + delta)).re - ell - delta * (F' 1).re ≤
        M * delta ^ 2 := by
    have h := (Complex.abs_re_le_norm
      (F (1 + delta) - F 1 - (delta : ℂ) * F' 1)).trans hrightRem
    have hupper := (abs_le.mp h).2
    simpa [F, ell] using hupper
  have hleftError :
      (F (1 - delta)).re - ell + delta * (F' 1).re ≤
        M * delta ^ 2 := by
    have h := (Complex.abs_re_le_norm
      (F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1)).trans hleftRem
    have hupper := (abs_le.mp h).2
    calc
      (F (1 - delta)).re - ell + delta * (F' 1).re =
          (F (1 - delta) - F 1 - ((-delta : ℝ) : ℂ) * F' 1).re := by
        simp [F, ell]
      _ ≤ M * delta ^ 2 := hupper
  have hleftNeg : (F (1 - delta)).re < 0 := by
    nlinarith
  let g : ℝ → ℝ := fun sigma ↦ (F sigma).re
  have hgContinuous : Continuous g := by
    dsimp [g, F]
    exact Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hchi).continuous.comp
        Complex.continuous_ofReal)
  have hzeroMem : (0 : ℝ) ∈ Icc (g (1 - delta)) (g 1) := by
    constructor
    · simpa [g] using hleftNeg.le
    · change 0 ≤ ell
      exact hellPos.le
  obtain ⟨beta, hbetaMem, hbetaZero⟩ :=
    intermediate_value_Icc (by linarith : 1 - delta ≤ (1 : ℝ))
      hgContinuous.continuousOn hzeroMem
  refine ⟨beta, ?_, hbetaMem.2, ?_⟩
  · simpa [delta, ell] using hbetaMem.1
  · have hreal : (F beta).re = 0 := by
      simpa [g] using hbetaZero
    have himag : (F beta).im = 0 := by
      have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (beta : ℂ)
      apply Complex.conj_eq_iff_im.mp
      simpa [F] using hconj.symm
    apply Complex.ext
    · simpa [F] using hreal
    · simpa [F] using himag

end Pollack17

end

/-! ## Siegel's lower bound with an arbitrary positive exponent

Source module `ErdosProblems.Erdos1141.SiegelLowerBound`. -/

noncomputable section

namespace Pollack17

open Filter

open BoundedGaps.Maynard

theorem eventually_rpow_neg_le_log_threshold {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ^ (-δ) ≤ 1 / ((2 ^ 24 : ℝ) * (Real.log (q : ℝ)) ^ 3) := by
  have hlittle := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hδ).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound := hlittle.bound (show (0 : ℝ) < 1 / (2 ^ 24 : ℝ) by positivity)
  filter_upwards [hbound, eventually_ge_atTop 3] with q hbound hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith)
  have hpow : 0 < (q : ℝ) ^ δ := Real.rpow_pos_of_pos hq0 _
  simp only [Function.comp_apply, Real.norm_eq_abs] at hbound
  rw [abs_of_pos (Real.rpow_pos_of_pos hlog _), abs_of_pos hpow] at hbound
  have hlogpow : Real.log (q : ℝ) ^ (3 : ℝ) = Real.log (q : ℝ) ^ (3 : ℕ) := by
    norm_num [Real.rpow_natCast]
  rw [hlogpow] at hbound
  have hdom : (2 ^ 24 : ℝ) * Real.log (q : ℝ) ^ 3 ≤ (q : ℝ) ^ δ := by
    nlinarith only [hbound]
  have hrecip := one_div_le_one_div_of_le
    (by positivity : 0 < (2 ^ 24 : ℝ) * Real.log (q : ℝ) ^ 3) hdom
  simpa only [Real.rpow_neg hq0.le, one_div] using hrecip

theorem eventually_quadratic_LFunction_one_re_ge_rpow {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ q : ℕ in atTop,
      ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ.IsQuadratic →
        (q : ℝ) ^ (-δ) ≤ (DirichletCharacter.LFunction χ (1 : ℂ)).re := by
  obtain ⟨c, hc, hzeroFree⟩ := exists_siegelRealCharacterZeroFree (δ / 2) (half_pos hδ)
  have hpowTendsto : Tendsto (fun q : ℕ => (q : ℝ) ^ (-(δ / 2))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (half_pos hδ)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hpowTendsto.eventually (eventually_lt_nhds (show 0 < c / 8 by positivity))
  filter_upwards [eventually_rpow_neg_le_log_threshold hδ, hsmall, eventually_gt_atTop 1]
    with q hlog hsmall hq
  intro _ χ hχ1 hχ
  by_contra hnot
  have hv : (DirichletCharacter.LFunction χ (1 : ℂ)).re < (q : ℝ) ^ (-δ) := lt_of_not_ge hnot
  obtain ⟨β, hβlower, _hβupper, hβzero⟩ :=
    exists_real_zero_of_LFunction_one_re_lt hq χ hχ1 hχ.sq_eq_one (hv.trans_le hlog)
  have hq0 : (0 : ℝ) < q := by positivity
  have hsq : (q : ℝ) ^ (-δ) = ((q : ℝ) ^ (-(δ / 2))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have ha : 0 < (q : ℝ) ^ (-(δ / 2)) := Real.rpow_pos_of_pos hq0 _
  have hgap : 8 * (DirichletCharacter.LFunction χ (1 : ℂ)).re < c * (q : ℝ) ^ (-(δ / 2)) := by
    rw [hsq] at hv
    nlinarith only [hv, hsmall, ha]
  have hβ : 1 - c * (q : ℝ) ^ (-(δ / 2)) < β := by linarith only [hgap, hβlower]
  exact (hzeroFree q χ hχ1 hχ.sq_eq_one β hβ) hβzero

end Pollack17

end

theorem OMA.solution : OMA.R_Erdos1141_erdos_1141_variants_pollack_1_3_R1.H2 := by
  intro exponent h
  exact Pollack17.eventually_quadratic_LFunction_one_re_ge_rpow h
