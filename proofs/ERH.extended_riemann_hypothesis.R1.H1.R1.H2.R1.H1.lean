import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! For a real quadratic field, integrate the theta series of each ideal class over one
fundamental-unit period. Unfolding the nonzero orbits gives the inverse Mellin kernel with
two real gamma factors. The origin in each ideal class contributes one regulator, giving
the constant four times the regulator times the class number divided by the torsion order. -/

-- Credit: @STARDUSTLC666

namespace OMA.RealQuadratic

namespace KernelData

open Complex Filter Set NumberField NumberField.InfinitePlace MeasureTheory Asymptotics
open scoped NumberField Topology

noncomputable abbrev coeff (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

theorem coeff_mean (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (coeff K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum, coeff]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem summable (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (coeff K n : ℂ)) s := by
  have h := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (coeff K n : ℝ))
    (r := 1) (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using coeff_mean K))
    (fun n => Nat.cast_nonneg _) zero_le_one hs
  simpa only [ofReal_natCast] using h

def StripBound (a b : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b → ‖F s‖ ≤ C

def StripDecay (a b : ℝ) (F : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re ∈ Icc a b → (1 + s.im ^ 2) * ‖F s‖ ≤ C

theorem StripDecay.bound {a b : ℝ} {F : ℂ → ℂ} (h : StripDecay a b F) : StripBound a b F := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun s hs => le_trans ?_ (h s hs)⟩
  nlinarith [mul_nonneg (sq_nonneg s.im) (norm_nonneg (F s))]

theorem StripBound.pow {a b : ℝ} {F : ℂ → ℂ} (h : StripBound a b F) (n : ℕ) :
    StripBound a b (fun s => F s ^ n) := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C ^ n, pow_nonneg hC _, fun s hs => (norm_pow _ _).le.trans (pow_le_pow_left₀ (norm_nonneg _) (h s hs) n)⟩

theorem StripDecay.mul_bound {a b : ℝ} {F G : ℂ → ℂ} (hF : StripDecay a b F) (hG : StripBound a b G) :
    StripDecay a b (fun s => F s * G s) := by
  obtain ⟨C, hC, hF⟩ := hF
  obtain ⟨D, hD, hG⟩ := hG
  refine ⟨C * D, mul_nonneg hC hD, fun s hs => ?_⟩
  dsimp only
  rw [norm_mul, ← mul_assoc]
  exact mul_le_mul (hF s hs) (hG s hs) (norm_nonneg _) hC

theorem StripDecay.pow_succ {a b : ℝ} {F : ℂ → ℂ} (hF : StripDecay a b F) (n : ℕ) :
    StripDecay a b (fun s => F s ^ (n + 1)) := by
  simpa only [pow_succ'] using hF.mul_bound (hF.bound.pow n)

theorem gamma_strip {a b : ℝ} (ha : 0 < a) : StripDecay a b Gamma := by
  let g (x : ℝ) := Real.Gamma x + Real.Gamma (x + 2)
  have hcont {x : ℝ} (hx : 0 < x) : ContinuousAt Real.Gamma x :=
    (Real.differentiableAt_Gamma (fun n => ne_of_gt (by have := Nat.cast_nonneg (α := ℝ) n; linarith : -(n : ℝ) < x))).continuousAt
  have hg : ContinuousOn g (Icc a b) := by
    intro x hx
    have hadd : ContinuousAt (fun y : ℝ => y + 2) x := by fun_prop
    have hshift : ContinuousAt (fun y : ℝ => Real.Gamma (y + 2)) x :=
      (hcont (x := x + 2) (by linarith [hx.1])).comp (f := fun y : ℝ => y + 2) hadd
    exact ((hcont (ha.trans_le hx.1)).fun_add hshift).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hg
  refine ⟨max C 0, le_max_right _ _, fun s hs => ?_⟩
  have h0 : 0 < s.re := ha.trans_le hs.1
  have h2 := OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.gamma_shift_bound h0 2
  simp only [Nat.cast_ofNat, sq_abs] at h2
  calc (1 + s.im ^ 2) * ‖Gamma s‖ ≤ g s.re := by dsimp [g]; linarith [OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.norm_Gamma_le_real h0]
       _ ≤ C := hC (mem_image_of_mem _ hs)
       _ ≤ _ := le_max_left _ _

theorem gammaR_strip {a b : ℝ} (ha : 0 < a) : StripDecay a b Gammaℝ := by
  obtain ⟨C, hC, h⟩ := gamma_strip (b := b / 2) (half_pos ha)
  refine ⟨4 * C, by positivity, fun s hs => ?_⟩
  have hhalf : (s / 2).re ∈ Icc (a / 2) (b / 2) := by
    simp only [Set.mem_Icc, div_ofNat_re]; constructor <;> linarith [hs.1, hs.2]
  have hx := h (s / 2) hhalf
  have hπ : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp; linarith [hs.1]
  have hG : ‖Gammaℝ s‖ ≤ ‖Gamma (s / 2)‖ := by
    rw [Gammaℝ_def, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hπ
  refine (mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 1 + s.im ^ 2)).trans ?_
  simp only [div_ofNat_im] at hx
  nlinarith [norm_nonneg (Gamma (s / 2))]

theorem StripDecay.vertical {F : ℂ → ℂ} {a b σ : ℝ} (h : StripDecay a b F) (hσ : σ ∈ Icc a b)
    (hcont : Continuous (fun y : ℝ => F (σ + y * I))) : VerticalIntegrable F σ := by
  obtain ⟨C, hC, h⟩ := h
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  filter_upwards with y
  change ‖F (σ + y * I)‖ ≤ C * (1 + y ^ 2)⁻¹
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa [mul_comm] using h ((σ : ℂ) + y * I) (by simpa using hσ)

noncomputable def completion (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) * Gammaℝ s ^ nrRealPlaces K *
    Gammaℂ s ^ nrComplexPlaces K * dedekindZeta K s

noncomputable abbrev kernel (K : Type*) [Field K] [NumberField K] := mellinInv 2 (completion K)

end KernelData

namespace IdealClasses

open Submodule Set NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone
open scoped NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

abbrev ClassFiber (C : ClassGroup (𝓞 K)) (n : ℕ) :=
  {I : (Ideal (𝓞 K))⁰ // Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C}

theorem class_norm_to_principal {C : ClassGroup (𝓞 K)} (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (n : ℕ) :
    Nat.card (ClassFiber K C n) = Nat.card {I : (Ideal (𝓞 K))⁰ //
      (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
      Ideal.absNorm (I : Ideal (𝓞 K)) = Ideal.absNorm (J : Ideal (𝓞 K)) * n} := by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  apply Nat.card_congr
  refine ((Equiv.dvd J).subtypeEquiv (p := fun I : (Ideal (𝓞 K))⁰ => Ideal.absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C) ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ => J ∣ I) _)
  intro I
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp only [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ, inv_mul_eq_one,
    Nat.mul_right_inj (Ideal.absNorm_pos_of_nonZeroDivisors J).ne']
  tauto

theorem class_count (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰) (hJ : ClassGroup.mk0 J = C⁻¹) (n : ℕ) :
    Nat.card (ClassFiber K C n) * torsionOrder K =
      Nat.card {x : idealSet K J // mixedEmbedding.norm (x : mixedSpace K) =
        (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ)} := by
  rw [class_norm_to_principal K J hJ n, torsionOrder, ← Nat.card_prod]
  exact Nat.card_congr (idealSetEquivNorm (K := K) (J := J) _).symm

theorem coeff_eq_sum_classes {n : ℕ} (hn : n ≠ 0) :
    KernelData.coeff K n = ∑ C : ClassGroup (𝓞 K), Nat.card (ClassFiber K C n) := by
  classical
  let A := {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  let asNonzero (x : A) : (Ideal (𝓞 K))⁰ := ⟨x.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
    intro h; apply hn; rw [← x.2, h]; exact map_zero _)⟩
  let fieldClass (x : A) := ClassGroup.mk0 (asNonzero x)
  let e (C : ClassGroup (𝓞 K)) : {x : A // fieldClass x = C} ≃ ClassFiber K C n := {
    toFun := fun x => ⟨asNonzero x.1, x.1.2, x.2⟩
    invFun := fun I => ⟨⟨I.1.1, I.2.1⟩, I.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let : Finite A := (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
  let (C : ClassGroup (𝓞 K)) : Finite (ClassFiber K C n) := Finite.of_equiv _ (e C)
  rw [← Nat.card_sigma]
  exact Nat.card_congr ((Equiv.sigmaFiberEquiv fieldClass).symm.trans (Equiv.sigmaCongrRight e))

end IdealClasses

namespace IdealLattices

open NumberField NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable abbrev Lattice (J : (Ideal (𝓞 K))⁰) := idealLattice K (FractionalIdeal.mk0 K J)

end IdealLattices

namespace NormGrading

open NumberField NumberField.mixedEmbedding IdealLattices
open scoped NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable def grade (J : (Ideal (𝓞 K))⁰) (x : Lattice K J) : ℕ := (OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.exists_grade K J x).choose

theorem grade_eq_iff (J : (Ideal (𝓞 K))⁰) (x : Lattice K J) (n : ℕ) :
    grade K J x = n ↔ mixedEmbedding.norm (x : mixedSpace K) = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) := by
  rw [(OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.exists_grade K J x).choose_spec, Nat.cast_inj, Nat.mul_right_inj (Ideal.absNorm_pos_of_nonZeroDivisors J).ne']
  rfl

end NormGrading

namespace LatticeTheta

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory Module
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K]

abbrev Places := Fin 2 ≃ {w : InfinitePlace K // IsReal w}

noncomputable def coords (e : Places K) (r : ℝ) (x : mixedSpace K) : ℂ :=
  ⟨Real.exp r * x.1 (e 0), Real.exp (-r) * x.1 (e 1)⟩

theorem det_coords (e : Places K) (r : ℝ) (x y : mixedSpace K) :
    (coords K e r x).re * (coords K e r y).im - (coords K e r x).im * (coords K e r y).re =
      x.1 (e 0) * y.1 (e 1) - x.1 (e 1) * y.1 (e 0) := by
  dsimp only [coords]
  have h : Real.exp r * Real.exp (-r) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc _ = (Real.exp r * Real.exp (-r)) * (x.1 (e 0) * y.1 (e 1) - x.1 (e 1) * y.1 (e 0)) := by ring
       _ = _ := by rw [h, one_mul]

theorem coords_combination (e : Places K) (r : ℝ) (m n : ℤ) (a b : mixedSpace K) :
    coords K e r (m • a + n • b) = (m : ℂ) * coords K e r a + (n : ℂ) * coords K e r b := by
  apply Complex.ext <;> simp [coords, Complex.mul_re, Complex.mul_im, zsmul_eq_mul] <;> ring

variable [NumberField K]

theorem area (hC : nrComplexPlaces K = 0) (J : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (IdealLattices.Lattice K J) = (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) *
      Real.sqrt ((discr K).natAbs : ℝ) := by
  rw [mixedEmbedding.covolume_idealLattice, hC, pow_zero, mul_one, FractionalIdeal.coe_mk0,
    FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, Nat.cast_natAbs, Int.cast_abs]

noncomputable def gaussian (e : Places K) (J : (Ideal (𝓞 K))⁰) (r t : ℝ)
    (x : IdealLattices.Lattice K J) : ℂ :=
  Real.exp (-Real.pi * (Complex.normSq (coords K e r x.val) / ZLattice.covolume (IdealLattices.Lattice K J)) * t)

noncomputable def theta (e : Places K) (J : (Ideal (𝓞 K))⁰) (r t : ℝ) : ℂ := ∑' x, gaussian K e J r t x

theorem reciprocal (e : Places K) (hC : nrComplexPlaces K = 0) (J : (Ideal (𝓞 K))⁰) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    Summable (gaussian K e J r t) ∧ theta K e J r (1 / t) = (t : ℂ) * theta K e J r t := by
  let : IsEmpty {w : InfinitePlace K // IsComplex w} := Fintype.card_eq_zero_iff.mp hC
  let idx : Fin 2 ≃ index K := {
    toFun := fun i => Sum.inl (e i)
    invFun := Sum.elim e.symm fun p => isEmptyElim p.1
    left_inv := e.symm_apply_apply
    right_inv := fun j => by rcases j with w | ⟨w,i⟩; exact congrArg Sum.inl (e.apply_symm_apply w); exact isEmptyElim w }
  let s := (stdBasis K).reindex idx.symm
  let L := IdealLattices.Lattice K J
  have hrank : finrank ℤ L = 2 := by rw [ZLattice.rank ℝ L, finrank_eq_card_basis s, Fintype.card_fin]
  let b := finBasisOfFinrankEq ℤ L hrank
  let a₀ := coords K e r (b 0 : mixedSpace K)
  let a₁ := coords K e r (b 1 : mixedSpace K)
  have hvol : volume.real (ZSpan.fundamentalDomain s) = 1 := by
    rw [measureReal_def, ZSpan.fundamentalDomain_reindex, volume_fundamentalDomain_stdBasis]; simp
  have hdet : ZLattice.covolume L = |a₀.re * a₁.im - a₀.im * a₁.re| := by
    dsimp only [a₀, a₁]
    rw [det_coords, ZLattice.covolume_eq_det_mul_measureReal L volume b s, hvol, mul_one, Basis.det_apply, Matrix.det_fin_two]
    change |(b 0 : mixedSpace K).1 (e 0) * (b 1 : mixedSpace K).1 (e 1) - (b 1 : mixedSpace K).1 (e 0) * (b 0 : mixedSpace K).1 (e 1)| = _
    rw [mul_comm ((b 1 : mixedSpace K).1 (e 0)) ((b 0 : mixedSpace K).1 (e 1))]
  obtain ⟨u, v, hv, hshape⟩ := OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.shape a₀ a₁ (ZLattice.covolume_pos L) hdet
  let B : ℤ × ℤ ≃ L := (Equiv.prodComm ℤ ℤ).trans ((finTwoArrowEquiv ℤ).symm.trans b.equivFun.toEquiv.symm)
  have hcoord (p : ℤ × ℤ) : B p = p.2 • b 0 + p.1 • b 1 := by
    change b.equivFun.symm ((finTwoArrowEquiv ℤ).symm (p.2, p.1)) = _
    rw [Basis.equivFun_symm_apply, Fin.sum_univ_two]; rfl
  let W (t : ℝ) (p : ℤ × ℤ) : ℂ := Real.exp (-Real.pi * (((p.2 : ℝ) + u * p.1) ^ 2 / v + v * (p.1 : ℝ) ^ 2) * t)
  have hweight (y : ℝ) (p : ℤ × ℤ) : gaussian K e J r y (B p) = W y p := by
    simp only [gaussian, hcoord p, Submodule.coe_add, Submodule.coe_smul_of_tower, coords_combination, W]
    exact congrArg (fun q : ℝ => (Real.exp (-Real.pi * q * y) : ℂ)) (hshape p.2 p.1)
  have heq (y : ℝ) : theta K e J r y = ∑' p, W y p := by
    rw [theta, ← B.tsum_eq]
    exact tsum_congr (hweight y)
  obtain ⟨hs, hi⟩ := OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.planar_gaussian u v hv
  exact ⟨B.summable_iff.mp ((hs t ht).congr fun p => (hweight t p).symm), by rw [heq, heq, hi t ht]⟩

theorem averaged_reciprocal (e : Places K) (hC : nrComplexPlaces K = 0) (J : (Ideal (𝓞 K))⁰) (R : ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ r in (0 : ℝ)..R, theta K e J r (1 / t)) = (t : ℂ) * ∫ r in (0 : ℝ)..R, theta K e J r t := by
  simp_rw [(reciprocal K e hC J _ ht).2, intervalIntegral.integral_const_mul]

omit [NumberField K] in
theorem normSq_coords (e : Places K) (r : ℝ) (x : mixedSpace K) :
    Complex.normSq (coords K e r x) = Real.exp r ^ 2 * (x.1 (e 0)) ^ 2 + Real.exp (-r) ^ 2 * (x.1 (e 1)) ^ 2 := by
  rw [Complex.normSq_apply]; dsimp [coords]; ring

theorem theta_continuousOn (e : Places K) (hC : nrComplexPlaces K = 0) (J : (Ideal (𝓞 K))⁰)
    (a b : ℝ) {t : ℝ} (ht : 0 < t) : ContinuousOn (fun r => theta K e J r t) (Set.uIcc a b) := by
  let m := min (Real.exp (min a b) ^ 2) (Real.exp (-(max a b)) ^ 2)
  have hm : 0 < m := lt_min (by positivity) (by positivity)
  have hS := (reciprocal K e hC J 0 (mul_pos hm ht)).1.norm
  refine continuousOn_tsum (f := fun x r => gaussian K e J r t x) ?_ hS ?_
  · intro x
    simp only [gaussian, normSq_coords]
    fun_prop
  · intro x r hr
    have h₁ : m ≤ Real.exp r ^ 2 := (min_le_left ..).trans (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr hr.1) 2)
    have h₂ : m ≤ Real.exp (-r) ^ 2 := (min_le_right ..).trans (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr (neg_le_neg hr.2)) 2)
    have hnorm : m * Complex.normSq (coords K e 0 x.val) ≤ Complex.normSq (coords K e r x.val) := by
      simp only [normSq_coords, neg_zero, Real.exp_zero, one_pow, one_mul, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right h₁ (sq_nonneg _)) (mul_le_mul_of_nonneg_right h₂ (sq_nonneg _))
    have hA := ZLattice.covolume_pos (IdealLattices.Lattice K J)
    have hbound := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hnorm hA.le) (mul_pos Real.pi_pos ht).le
    simp only [gaussian, Complex.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    simp only [div_eq_mul_inv, neg_mul] at hbound ⊢
    apply neg_le_neg
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hbound

theorem theta_intervalIntegrable (e : Places K) (hC : nrComplexPlaces K = 0) (J : (Ideal (𝓞 K))⁰)
    (a b : ℝ) {t : ℝ} (ht : 0 < t) : IntervalIntegrable (fun r => theta K e J r t) volume a b :=
  (theta_continuousOn K e hC J a b ht).intervalIntegrable

end LatticeTheta

namespace OrbitIntegral

open MeasureTheory Set

noncomputable def profile (y r : ℝ) : ℝ :=
  Real.exp (-(Real.pi * y) * (Real.exp r ^ 2 + Real.exp (-r) ^ 2))

noncomputable def moment (y : ℝ) : ℝ := ∫ r : ℝ, profile y r

theorem integrable_profile {y : ℝ} (hy : 0 < y) : Integrable (profile y) := by
  apply (integrable_exp_neg_mul_sq (mul_pos Real.pi_pos hy)).mono' (by unfold profile; fun_prop)
  filter_upwards with r
  have h (a : ℝ) (ha : 0 ≤ a) : a ^ 2 ≤ Real.exp a ^ 2 := by
    apply pow_le_pow_left₀ ha
    linarith [Real.add_one_le_exp a]
  have hbound : r ^ 2 ≤ Real.exp r ^ 2 + Real.exp (-r) ^ 2 := by
    rcases le_total 0 r with hr | hr
    · exact (h _ hr).trans (le_add_of_nonneg_right (sq_nonneg _))
    · have hn := h (-r) (neg_nonneg.mpr hr)
      rw [neg_sq] at hn
      exact hn.trans (le_add_of_nonneg_left (sq_nonneg _))
  simp only [profile, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left hbound (neg_nonpos.mpr (mul_pos Real.pi_pos hy).le)

theorem shifted (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ d : ℝ, ∀ r : ℝ, Real.exp (-(Real.pi * t) * (a ^ 2 * Real.exp r ^ 2 + b ^ 2 * Real.exp (-r) ^ 2)) =
      profile (t * (a * b)) (r + d) := by
  let d := Real.log (a / b) / 2
  have hsq : Real.exp d ^ 2 = a / b := by
    rw [pow_two, ← Real.exp_add, show d + d = Real.log (a / b) by dsimp [d]; ring,
      Real.exp_log (div_pos ha hb)]
  have hinv : Real.exp (-d) ^ 2 = b / a := by rw [Real.exp_neg, inv_pow, hsq, inv_div]
  refine ⟨d, fun r => ?_⟩
  simp only [profile, neg_add_rev, Real.exp_add, mul_pow, hsq, hinv]
  congr 1; field_simp

theorem unfold_period {R : ℝ} (hR : 0 < R) (f : ℝ → ℝ) (hf : Integrable f) :
    (∫ r : ℝ, f r) = ∑' k : ℤ, ∫ r in (0 : ℝ)..R, f (r + (k : ℝ) * R) := by
  let e : ℤ ≃ AddSubgroup.zmultiples R := Equiv.ofInjective (fun n : ℤ => n • R) (zsmul_left_strictMono hR).injective
  rw [(isAddFundamentalDomain_Ioc hR 0 (volume : Measure ℝ)).integral_eq_tsum'' f hf, ← e.tsum_eq]
  apply tsum_congr
  intro k
  rw [intervalIntegral.integral_of_le hR.le, zero_add]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  change f (k • R + x) = f _
  rw [zsmul_eq_mul, add_comm]

theorem orbit_sum (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) {R : ℝ} (hR : 0 < R) :
    (∑' k : ℤ, ∫ r in (0 : ℝ)..R, Real.exp (-(Real.pi * t) *
      (a ^ 2 * Real.exp (r + (k : ℝ) * R) ^ 2 + b ^ 2 * Real.exp (-(r + (k : ℝ) * R)) ^ 2))) =
      moment (t * (a * b)) := by
  obtain ⟨d, hd⟩ := shifted a b t ha hb
  simp_rw [hd]
  have hi : Integrable (fun r : ℝ => profile (t * (a * b)) (r + d)) :=
    (integrable_profile (mul_pos ht (mul_pos ha hb))).comp_add_right d
  rw [← unfold_period hR (fun r => profile (t * (a * b)) (r + d)) hi]
  exact integral_add_right_eq_self _ _

end OrbitIntegral

namespace ArchimedeanMellin

open Complex Set MeasureTheory OrbitIntegral
open scoped Convolution

theorem hasMellin_log_iff (f : ℝ → ℂ) (s a : ℂ) : HasMellin f s a ↔
    Integrable (fun u : ℝ => exp (s * u) * f (Real.exp u)) ∧
      (∫ u : ℝ, exp (s * u) * f (Real.exp u)) = a := by
  have hr : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have h (u : ℝ) : |Real.exp u| • (((Real.exp u : ℂ) ^ (s - 1)) • f (Real.exp u)) = exp (s * u) * f (Real.exp u) := by
    rw [abs_of_pos (Real.exp_pos _), Complex.real_smul, smul_eq_mul, ← mul_assoc,
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ← ofReal_log (Real.exp_pos _).le,
      Real.log_exp, ofReal_exp, ← Complex.exp_add]
    congr 2; ring
  unfold HasMellin MellinConvergent mellin
  rw [← hr, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn, integrableOn_univ, setIntegral_univ]
  simp only [h]

noncomputable def gauss (x : ℝ) : ℂ := Real.exp (-Real.pi * x ^ 2)

theorem gauss_mellin {s : ℂ} (hs : 0 < s.re) : HasMellin gauss s (Gammaℝ s / 2) := by
  have hcont : Continuous gauss := by unfold gauss; fun_prop
  constructor
  · unfold MellinConvergent
    rw [mellin_convergent_iff_norm (s := s) (Subset.rfl) measurableSet_Ioi hcont.aestronglyMeasurable]
    simp only [gauss, Complex.norm_of_nonneg (Real.exp_pos _).le]
    exact integrableOn_rpow_mul_exp_neg_mul_sq Real.pi_pos (by linarith)
  · let g (t : ℝ) : ℂ := Real.exp (-t)
    have hsq : gauss = fun x : ℝ => g (Real.pi * x ^ (2 : ℝ)) := by
      funext x; simp [gauss, g]
    have hg := mellin_comp_rpow (fun t => g (Real.pi * t)) s 2
    rw [hsq, hg, mellin_comp_mul_left g _ Real.pi_pos]
    have hgamma : mellin g (s / 2) = Gamma (s / 2) := by
      rw [Gamma_eq_integral (by simpa using half_pos hs : 0 < (s / 2).re), GammaIntegral_eq_mellin]
    simp only [ofReal_ofNat, hgamma, Gammaℝ_def, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      Complex.real_smul, smul_eq_mul, ofReal_inv, neg_div]
    ring

noncomputable def H (s : ℂ) (u : ℝ) : ℂ := exp (s * u) * gauss (Real.exp u)

theorem profile_convolution (s : ℂ) (w : ℝ) :
    (H s ⋆[ContinuousLinearMap.mul ℝ ℂ] H s) w = exp (s * w) * (moment (Real.exp w) : ℂ) := by
  have hsq : Real.exp (w / 2) ^ 2 = Real.exp w := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hp (r : ℝ) : H s (r + w / 2) * H s (w - (r + w / 2)) = exp (s * w) * (profile (Real.exp w) r : ℂ) := by
    have hneg : w - (r + w / 2) = -r + w / 2 := by ring
    have hz : s * ((r + w / 2 : ℝ) : ℂ) + s * ((-r + w / 2 : ℝ) : ℂ) = s * w := by push_cast; ring
    simp only [hneg, H, gauss, profile]
    rw [mul_mul_mul_comm, ← Complex.exp_add, hz, ← ofReal_mul, ← Real.exp_add, Real.exp_add r, Real.exp_add (-r), mul_pow, mul_pow, hsq]
    congr 3; ring
  change (∫ u : ℝ, H s u * H s (w - u)) = _
  rw [← integral_add_right_eq_self (fun u : ℝ => H s u * H s (w - u)) (w / 2)]
  simp_rw [hp]
  rw [integral_const_mul, integral_complex_ofReal]; rfl

theorem moment_mellin {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ => (moment t : ℂ)) s (Gammaℝ s ^ 2 / 4) := by
  have hg := (hasMellin_log_iff gauss s _).mp (gauss_mellin hs)
  change Integrable (H s) ∧ (∫ u : ℝ, H s u) = Gammaℝ s / 2 at hg
  rw [hasMellin_log_iff]
  simp_rw [← profile_convolution s]
  refine ⟨hg.1.integrable_convolution (ContinuousLinearMap.mul ℝ ℂ) hg.1, ?_⟩
  rw [integral_convolution (ContinuousLinearMap.mul ℝ ℂ) hg.1 hg.1, ContinuousLinearMap.mul_apply', hg.2]
  ring

end ArchimedeanMellin

namespace KernelExpansion

open Complex Filter Set MeasureTheory NumberField NumberField.InfinitePlace KernelData OrbitIntegral
open scoped NumberField Topology

noncomputable def gammaPair (s : ℂ) := Gammaℝ s ^ 2

theorem gamma_continuous : Continuous (fun y : ℝ => gammaPair ((2 : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  let z := (2 : ℂ) + y * I
  have hz : 0 < z.re := by simp [z]
  have hc : ContinuousAt Gammaℝ z := by
    simpa only [Pi.inv_def, inv_inv] using (differentiable_Gammaℝ_inv z).continuousAt.inv₀ (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hz))
  exact ((hc.pow 2).comp (f := fun y : ℝ => (2 : ℂ) + y * I) (by fun_prop))

theorem pair_vertical : VerticalIntegrable gammaPair 2 := by
  exact ((gammaR_strip (a := 2) (b := 2) (by norm_num)).pow_succ 1).vertical ⟨le_rfl, le_rfl⟩ gamma_continuous

theorem moment_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt moment x := by
  apply continuousAt_of_dominated (F := profile) (bound := profile (x/2))
  · apply Eventually.of_forall; intro t; unfold profile; fun_prop
  · filter_upwards [lt_mem_nhds (show x / 2 < x by linarith)] with t ht
    apply Eventually.of_forall
    intro r
    simp only [profile, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_left ht.le Real.pi_pos.le)) (by positivity)
  · exact integrable_profile (half_pos hx)
  · apply Eventually.of_forall; intro r; unfold profile; fun_prop

theorem inv_pair {x : ℝ} (hx : 0 < x) : mellinInv 2 gammaPair x = 4 * (moment x : ℂ) := by
  let f (t : ℝ) : ℂ := 4 * (moment t : ℂ)
  have hm {s : ℂ} (hs : 0 < s.re) : HasMellin f s (gammaPair s) := by
    have h := ArchimedeanMellin.moment_mellin hs
    have he := hasMellin_const_smul h.1 (4 : ℂ)
    rw [h.2, smul_eq_mul, show (4 : ℂ) * (Gammaℝ s ^ 2 / 4) = gammaPair s by unfold gammaPair; ring] at he
    exact he
  have heq (y : ℝ) : mellin f ((2 : ℂ) + y * I) = gammaPair (2 + y * I) := (hm (by simp)).2
  have hF : VerticalIntegrable (mellin f) 2 := by
    change Integrable (fun y : ℝ => mellin f ((2 : ℂ) + y * I))
    simpa only [VerticalIntegrable, ofReal_ofNat, heq] using pair_vertical
  change mellinInv 2 gammaPair x = f x
  have hfc : ContinuousAt f x := continuousAt_const.mul (continuous_ofReal.continuousAt.comp (moment_continuousAt hx))
  rw [← mellinInv_mellin_eq 2 f hx (hm (s := 2) (by norm_num)).1 hF hfc]
  unfold mellinInv
  simp only [ofReal_ofNat, heq]

theorem inverse_series (K : Type*) [Field K] [NumberField K] {x : ℝ} (hx : 0 < x) :
    mellinInv 2 (fun s => gammaPair s * dedekindZeta K s) x =
      ∑' n : ℕ, if n = 0 then 0 else (coeff K n : ℂ) * (4 * (moment (x * n) : ℂ)) := by
  let z (y : ℝ) : ℂ := 2 + y * I
  let a (n : ℕ) : ℂ := coeff K n
  let G (n : ℕ) (y : ℝ) := (x : ℂ) ^ (-(z y)) * gammaPair (z y) * LSeries.term a (z y) n
  let w (n : ℕ) := ‖LSeries.term a 2 n‖
  have hw (n : ℕ) (y : ℝ) : ‖G n y‖ = (x ^ (-(2 : ℝ)) * w n) * ‖gammaPair (z y)‖ := by
    simp only [G, w, norm_mul, LSeries.norm_term_eq, norm_cpow_eq_rpow_re_of_pos hx, neg_re]
    simp [z, mul_right_comm]
  have hG (n : ℕ) : Integrable (G n) := by
    apply ((pair_vertical.norm).const_mul (x ^ (-(2 : ℝ)) * w n)).mono'
    · by_cases hn : n = 0
      · subst n; simpa [G, LSeries.term] using (aestronglyMeasurable_const (b := (0 : ℂ)) (μ := (volume : Measure ℝ)))
      · have hz : Continuous z := by dsimp [z]; fun_prop
        have hp : Continuous (fun y : ℝ => (x : ℂ) ^ (-z y)) := hz.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
        have hg : Continuous (fun y : ℝ => gammaPair (z y)) := gamma_continuous
        have ht : Continuous (fun y => LSeries.term a (z y) n) := by
          simp only [LSeries.term_of_ne_zero hn]
          have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
          exact continuous_const.div₀ (hz.const_cpow (Or.inl hn')) (fun y => cpow_ne_zero_iff.mpr (Or.inl hn'))
        exact ((hp.fun_mul hg).fun_mul ht).aestronglyMeasurable
    · exact Eventually.of_forall fun y => (hw n y).le
  have hsum : Summable fun n => ∫ y : ℝ, ‖G n y‖ := by
    simp_rw [hw, integral_const_mul, mul_assoc]
    exact (((KernelData.summable K (s := 2) (by norm_num)).norm.mul_right _).mul_left _)
  have hex (y : ℝ) : (x : ℂ) ^ (-z y) • (gammaPair (z y) * dedekindZeta K (z y)) = ∑' n, G n y := by
    simp only [G, dedekindZeta, LSeries, ← tsum_mul_left, smul_eq_mul, mul_assoc, a, coeff]
  unfold mellinInv
  change (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, (x : ℂ) ^ (-z y) • (gammaPair (z y) * dedekindZeta K (z y))) = _
  simp_rw [hex]
  rw [← integral_tsum_of_summable_integral_norm hG hsum, ← tsum_const_smul'']
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp [G, LSeries.term]
  · rw [if_neg hn]
    have hterm (y : ℝ) : G n y = a n * ((↑(x * n) : ℂ) ^ (-z y) • gammaPair (z y)) := by
      dsimp only [G]
      rw [LSeries.term_of_ne_zero hn, ofReal_mul, mul_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg _), ofReal_natCast]
      simp only [cpow_neg, smul_eq_mul, div_eq_mul_inv]
      ring
    simp_rw [hterm, integral_const_mul]
    have hx' : 0 < x * n := mul_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    rw [← inv_pair hx']
    unfold mellinInv
    simp [z, a, Algebra.smul_def, mul_left_comm, mul_assoc]

theorem kernel_expansion (K : Type*) [Field K] [NumberField K]
    (hR : nrRealPlaces K = 2) (hC : nrComplexPlaces K = 0) {x : ℝ} (hx : 0 < x) :
    let q := (Real.sqrt ((discr K).natAbs : ℝ))⁻¹
    kernel K x = 4 * ∑' n : ℕ, if n = 0 then 0 else (coeff K n : ℂ) * (moment (q * x * n) : ℂ) := by
  let d := Real.sqrt ((discr K).natAbs : ℝ)
  let q := d⁻¹
  have hd₀ : 0 < ((discr K).natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)
  have hd : 0 < d := Real.sqrt_pos.mpr hd₀
  have hq : 0 < q := inv_pos.mpr hd
  have hc (s : ℂ) : exp (s * (Real.log (discr K).natAbs / 2 : ℝ)) = (q : ℂ) ^ (-s) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hq.ne'), ← ofReal_log hq.le]
    dsimp only [q, d]
    rw [Real.log_inv, Real.log_sqrt hd₀.le, ofReal_neg]; congr 1; ring
  have hcomp : completion K = fun s => 1 * ((q : ℂ) ^ (-s) * (gammaPair s * dedekindZeta K s)) := by
    funext s
    simp only [completion, hR, hC, hc, gammaPair, pow_zero, mul_one, one_mul, mul_assoc]
  dsimp only
  rw [kernel, hcomp, OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.inverse_scaled _ _ hq hx _, one_mul, inverse_series K (mul_pos hq hx), ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, q, d]; ring

end KernelExpansion

namespace UnitOrbits

open NumberField NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone IdealLattices
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem unit_lattice {J : (Ideal (𝓞 K))⁰} (u : (𝓞 K)ˣ) {x : mixedSpace K} (hx : x ∈ Lattice K J) :
    u • x ∈ Lattice K J := by
  obtain ⟨y, hy, rfl⟩ := (mem_idealLattice K _).mp hx
  apply (mem_idealLattice K _).mpr
  let I := ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  refine ⟨(u : 𝓞 K) • y, (I : Submodule (𝓞 K) K).smul_mem (u : 𝓞 K) hy, ?_⟩
  change mixedEmbedding K ((u : K) * y) = _
  rw [unitSMul_smul, map_mul]

theorem one_generator (hr : rank K = 1) (j : Fin (rank K)) (u : (𝓞 K)ˣ) :
    ∃ (ζ : torsion K) (k : ℤ), u = (ζ : (𝓞 K)ˣ) * fundSystem K j ^ k := by
  let : Unique (Fin (rank K)) := (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using hr)).some
  obtain ⟨⟨ζ, f⟩, h, _⟩ := exist_unique_eq_mul_prod K u
  exact ⟨ζ, f j, by simpa only [Fintype.prod_unique, show (default : Fin (rank K)) = j from Subsingleton.elim _ _] using h⟩

theorem generator_pow_torsion (hr : rank K = 1) (j : Fin (rank K)) {k : ℤ} (h : fundSystem K j ^ k ∈ torsion K) : k = 0 := by
  let : Unique (Fin (rank K)) := (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using hr)).some
  have he := fun_eq_repr (K := K) (x := fundSystem K j ^ k) (ζ := 1) (f := fun _ => k) (one_mem _) (by
    rw [one_mul, Fintype.prod_unique, show (default : Fin (rank K)) = j from Subsingleton.elim _ _])
  have h₀ := fun_eq_repr (K := K) (x := fundSystem K j ^ k) (f := fun _ => 0) h (by simp)
  exact congrFun (he.trans h₀.symm) j

noncomputable def orbitEquiv (hr : rank K = 1) (j : Fin (rank K)) (J : (Ideal (𝓞 K))⁰) :
    ℤ × idealSet K J ≃ {x : Lattice K J // x ≠ 0} := by
  let u := fundSystem K j
  let F (p : ℤ × idealSet K J) : {x : Lattice K J // x ≠ 0} :=
    ⟨⟨u ^ p.1 • p.2.val, unit_lattice K _ p.2.prop.2⟩, by
      intro h
      have hh := congrArg (fun z : Lattice K J => (z : mixedSpace K)) h
      have hz := (unit_smul_eq_zero (u ^ p.1) p.2.val).mp hh
      have hn := (norm_pos_of_mem p.2.prop.1).ne'
      exact hn (hz ▸ map_zero _)⟩
  refine Equiv.ofBijective F ⟨?_, ?_⟩
  · rintro ⟨k, a⟩ ⟨l, b⟩ h
    have hEq : u ^ k • a.val = u ^ l • b.val := congrArg (fun z : {x : Lattice K J // x ≠ 0} => z.1.val) h
    have hd : u ^ (k - l) • a.val = b.val := by rw [zpow_sub, mul_comm, mul_smul, hEq, inv_smul_smul]
    have ht := (unit_smul_mem_iff_mem_torsion a.prop.1 _).mp (hd ▸ b.prop.1)
    have hkl : k = l := sub_eq_zero.mp (generator_pow_torsion K hr j ht)
    subst l
    exact Prod.ext rfl (Subtype.ext (by simpa using hd))
  · intro x
    obtain ⟨y, _, hy⟩ := (mem_idealLattice K _).mp x.1.prop
    have hne : mixedEmbedding.norm x.1.val ≠ 0 := (mixedEmbedding.norm_eq_zero_iff' ⟨y, hy⟩).not.mpr
      (fun h => x.prop (Subtype.ext h))
    obtain ⟨v, hv⟩ := exists_unit_smul_mem hne
    obtain ⟨ζ, k, hvk⟩ := one_generator K hr j v
    let b := u ^ k • x.1.val
    have hb : b ∈ fundamentalCone K := by
      have h := torsion_smul_mem_of_mem hv ((torsion K).inv_mem ζ.prop)
      simpa only [hvk, mul_smul, inv_smul_smul, b, u] using h
    refine ⟨⟨-k, ⟨b, hb, unit_lattice K _ x.1.prop⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change u ^ (-k) • (u ^ k • x.1.val) = x.1.val
    rw [zpow_neg, inv_smul_smul]

theorem orbitEquiv_apply (hr : rank K = 1) (j : Fin (rank K)) (J : (Ideal (𝓞 K))⁰) (p : ℤ × idealSet K J) :
    ((orbitEquiv K hr j J p).val : mixedSpace K) = fundSystem K j ^ p.1 • p.2.val := rfl

end UnitOrbits

namespace UnitPeriod

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding LatticeTheta OrbitIntegral
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem all_real (hC : nrComplexPlaces K = 0) (w : InfinitePlace K) : IsReal w := by
  let : IsEmpty {w : InfinitePlace K // IsComplex w} := Fintype.card_eq_zero_iff.mp hC
  exact (isReal_or_isComplex w).resolve_right (fun h => isEmptyElim (⟨w,h⟩ : {w : InfinitePlace K // IsComplex w}))

noncomputable def places (e : Places K) (hC : nrComplexPlaces K = 0) : Fin 2 ≃ InfinitePlace K :=
  e.trans (Equiv.subtypeUnivEquiv (all_real K hC))

theorem regulator_eq (e : Places K) (hC : nrComplexPlaces K = 0) (hr : rank K = 1) (j : Fin (rank K)) :
    regulator K = |Real.log ((e 0).val (fundSystem K j : K))| := by
  let w := places K e hC
  let D := {v : InfinitePlace K // v ≠ w 1}
  let w₀ : D := ⟨w 0, fun hh => (by decide : (0 : Fin 2) ≠ 1) (w.injective hh)⟩
  let : Unique D := {
    default := w₀
    uniq := fun ⟨v, hv⟩ => by
      obtain ⟨i, rfl⟩ := w.surjective v
      fin_cases i
      · rfl
      · exact (hv rfl).elim }
  let : Unique (Fin (rank K)) := (Fintype.card_eq_one_iff_nonempty_unique.mp (by simpa using hr)).some
  let g := Equiv.ofUnique D (Fin (rank K))
  rw [regulator_eq_det K (w 1) g, Matrix.det_unique]
  change |((mult ((e 0).val) : ℝ) * Real.log ((e 0).val (fundSystem K (g w₀) : K)))| = _
  rw [(e 0).prop.mult_eq_one, Nat.cast_one, one_mul, show g w₀ = j from Subsingleton.elim _ _]

theorem norm_eq (e : Places K) (hC : nrComplexPlaces K = 0) (x : mixedSpace K) :
    mixedEmbedding.norm x = |x.1 (e 0)| * |x.1 (e 1)| := by
  let w := places K e hC
  rw [mixedEmbedding.norm_apply, ← w.prod_comp, Fin.prod_univ_two]
  change normAtPlace (e 0).val x ^ mult (e 0).val * normAtPlace (e 1).val x ^ mult (e 1).val = _
  rw [(e 0).prop.mult_eq_one, (e 1).prop.mult_eq_one, pow_one, pow_one,
    normAtPlace_apply_of_isReal (e 0).prop, normAtPlace_apply_of_isReal (e 1).prop]; rfl

theorem unit_step (e : Places K) (hC : nrComplexPlaces K = 0) (u : (𝓞 K)ˣ) :
    let d := Real.log ((e 0).val (u : K))
    (e 0).val (u : K) = Real.exp d ∧ (e 1).val (u : K) = Real.exp (-d) := by
  let v := mixedEmbedding K (u : K)
  have he (i : Fin 2) : |v.1 (e i)| = (e i).val (u : K) := by
    rw [← normAtPlace_apply, normAtPlace_apply_of_isReal (e i).prop]; rfl
  have hp := (norm_eq K e hC v).symm.trans (norm_unit u)
  rw [he 0, he 1] at hp
  have hpos : 0 < (e 0).val (u : K) := lt_of_le_of_ne (he 0 ▸ abs_nonneg _) (fun h => by rw [← h, zero_mul] at hp; exact zero_ne_one hp)
  dsimp only
  rw [Real.exp_neg, Real.exp_log hpos]
  refine ⟨rfl, ?_⟩
  field_simp
  simpa [mul_comm] using hp

omit [NumberField K] in
theorem place_power (e : Places K) (u : (𝓞 K)ˣ) (i : Fin 2) (k : ℤ) (x : mixedSpace K) :
    |(u ^ k • x).1 (e i)| = ((e i).val (u : K)) ^ k * |x.1 (e i)| := by
  rw [← Real.norm_eq_abs, ← normAtPlace_apply_of_isReal (e i).prop, unitSMul_smul, map_mul,
    normAtPlace_apply, normAtPlace_apply_of_isReal (e i).prop, Real.norm_eq_abs,
    NumberField.Units.coe_zpow]
  change ((e i).val.val ((u : K) ^ k)) * _ = _
  rw [map_zpow₀]
  rfl

theorem exp_int_mul (d : ℝ) (k : ℤ) : Real.exp ((k : ℝ) * d) = Real.exp d ^ k := by
  apply Complex.ofReal_inj.mp
  push_cast
  exact Complex.exp_int_mul _ _

end UnitPeriod

namespace OrbitEvaluation

open NumberField NumberField.Units NumberField.InfinitePlace NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone LatticeTheta UnitPeriod OrbitIntegral
open scoped NumberField nonZeroDivisors Classical

theorem sum_signed (F : ℝ → ℝ) (R d : ℝ) (hd : |d| = R) :
    (∑' k : ℤ, ∫ r in (0 : ℝ)..R, F (r + (k : ℝ) * d)) =
      ∑' k : ℤ, ∫ r in (0 : ℝ)..R, F (r + (k : ℝ) * R) := by
  rcases le_total 0 d with h | h
  · rw [abs_of_nonneg h] at hd; rw [hd]
  · rw [abs_of_nonpos h] at hd
    have he : d = -R := by linarith
    rw [he]
    simpa only [Int.cast_neg, neg_mul, mul_neg] using tsum_comp_neg
      (fun k : ℤ => ∫ r in (0 : ℝ)..R, F (r + (k : ℝ) * R))

variable (K : Type*) [Field K] [NumberField K]

theorem orbit_value (e : Places K) (hC : nrComplexPlaces K = 0) (hr : rank K = 1) (j : Fin (rank K))
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) {t : ℝ} (ht : 0 < t) :
    (∑' k : ℤ, ∫ r in (0 : ℝ)..regulator K, gaussian K e J r t ((UnitOrbits.orbitEquiv K hr j J (k, a)).1)) =
      (moment (t / ZLattice.covolume (IdealLattices.Lattice K J) * mixedEmbedding.norm a.val) : ℂ) := by
  let u := fundSystem K j
  let d := Real.log ((e 0).val (u : K))
  let A := ZLattice.covolume (IdealLattices.Lattice K J)
  let p := |a.val.1 (e 0)|
  let q := |a.val.1 (e 1)|
  let F (r : ℝ) := Real.exp (-(Real.pi * (t / A)) * (p ^ 2 * Real.exp r ^ 2 + q ^ 2 * Real.exp (-r) ^ 2))
  have hA : 0 < A := ZLattice.covolume_pos (IdealLattices.Lattice K J)
  have hpq : p * q = mixedEmbedding.norm a.val := (norm_eq K e hC _).symm
  have hpos : 0 < p * q := hpq ▸ norm_pos_of_mem a.prop.1
  have hp : 0 < p := pos_of_mul_pos_left hpos (abs_nonneg _)
  have hq : 0 < q := pos_of_mul_pos_right hpos (abs_nonneg _)
  obtain ⟨hu₀, hu₁⟩ := unit_step K e hC u
  have hW (k : ℤ) (r : ℝ) : gaussian K e J r t ((UnitOrbits.orbitEquiv K hr j J (k,a)).1) =
      (F (r + (k : ℝ) * d) : ℂ) := by
    have h₀ := congrArg (fun x : ℝ => x ^ 2) (place_power K e u 0 k a.val)
    have h₁ := congrArg (fun x : ℝ => x ^ 2) (place_power K e u 1 k a.val)
    rw [sq_abs, hu₀, ← exp_int_mul] at h₀
    rw [sq_abs, hu₁, ← exp_int_mul] at h₁
    simp only [gaussian, normSq_coords, UnitOrbits.orbitEquiv_apply]
    change (Real.exp (-Real.pi * ((Real.exp r ^ 2 * ((u ^ k • a.val).1 (e 0)) ^ 2 + Real.exp (-r) ^ 2 * ((u ^ k • a.val).1 (e 1)) ^ 2) / A) * t) : ℂ) = _
    rw [h₀, h₁]
    dsimp only [F, p, q, d]
    simp only [neg_add, mul_neg, Real.exp_add, mul_pow]
    congr 2; ring
  simp_rw [hW, intervalIntegral.integral_ofReal]
  rw [← Complex.ofReal_tsum, sum_signed F _ d (regulator_eq K e hC hr j).symm,
    orbit_sum p q (t / A) hp hq (div_pos ht hA) (regulator_pos K), hpq]

end OrbitEvaluation

namespace OrbitSum

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone LatticeTheta IdealLattices MeasureTheory
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem hasSum_nonzero_integrals (e : Places K) (hC : nrComplexPlaces K = 0) (J : (Ideal (𝓞 K))⁰)
    (R : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun x : {x : Lattice K J // x ≠ 0} => ∫ r in (0 : ℝ)..R, gaussian K e J r t x.1)
      (∫ r in (0 : ℝ)..R, (theta K e J r t - 1)) := by
  classical
  let F (x : Lattice K J) (r : ℝ) := gaussian K e J r t x
  let T (r : ℝ) := theta K e J r t
  have h₀ (r : ℝ) : F 0 r = 1 := by simp [F, gaussian, coords]
  have hm (r : ℝ) : ∑' x, ‖F x r‖ = (T r).re := by
    have := (Complex.hasSum_re (reciprocal K e hC J r ht).1.hasSum).tsum_eq
    simpa only [F, gaussian, Complex.norm_of_nonneg (Real.exp_pos _).le, Complex.ofReal_re, T, theta] using this
  have hAll : HasSum (fun x : Lattice K J => ∫ r in (0 : ℝ)..R, F x r) (∫ r in (0 : ℝ)..R, T r) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun x r => ‖F x r‖)
    · intro x; simp only [F, gaussian, normSq_coords]; fun_prop
    · exact fun _ => .of_forall fun _ _ => le_rfl
    · exact .of_forall fun r _ => (reciprocal K e hC J r ht).1.norm
    · simp_rw [hm]; exact (Complex.continuous_re.comp_continuousOn (theta_continuousOn K e hC J 0 R ht)).intervalIntegrable
    · exact .of_forall fun r _ => (reciprocal K e hC J r ht).1.hasSum
  have hNZ := (({0} : Finset (Lattice K J)).hasSum_iff_compl).mp hAll
  simp only [Finset.sum_singleton, h₀] at hNZ
  rw [intervalIntegral.integral_sub (theta_intervalIntegrable K e hC J 0 R ht) intervalIntegrable_const]
  let E : {x : Lattice K J // x ≠ 0} ≃ {x : Lattice K J // x ∉ ({0} : Finset (Lattice K J))} :=
    Equiv.subtypeEquivRight (fun x => by simp)
  exact E.hasSum_iff.mpr hNZ

theorem hasSum_orbits (e : Places K) (hC : nrComplexPlaces K = 0) (hr : rank K = 1) (j : Fin (rank K))
    (J : (Ideal (𝓞 K))⁰) (R : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun a : idealSet K J => ∑' k : ℤ, ∫ r in (0 : ℝ)..R,
      gaussian K e J r t ((UnitOrbits.orbitEquiv K hr j J (k, a)).1))
      (∫ r in (0 : ℝ)..R, (theta K e J r t - 1)) := by
  let E := (Equiv.prodComm (idealSet K J) ℤ).trans (UnitOrbits.orbitEquiv K hr j J)
  have h := E.hasSum_iff.mpr (hasSum_nonzero_integrals K e hC J R ht)
  rw [← h.tsum_eq, h.summable.tsum_prod]
  exact h.summable.prod.hasSum

end OrbitSum

namespace NormCounting

open NumberField NumberField.InfinitePlace NumberField.Units NumberField.mixedEmbedding
open NumberField.mixedEmbedding.fundamentalCone IdealClasses OrbitIntegral KernelData
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable abbrev q := (Real.sqrt ((discr K).natAbs : ℝ))⁻¹

theorem group_class (hC : nrComplexPlaces K = 0) (C : ClassGroup (𝓞 K)) (J : (Ideal (𝓞 K))⁰)
    (hJ : ClassGroup.mk0 J = C⁻¹) (t : ℝ) {S : ℂ}
    (h : HasSum (fun a : idealSet K J => (moment (t / ZLattice.covolume (IdealLattices.Lattice K J) * mixedEmbedding.norm a.val) : ℂ)) S) :
    HasSum (fun n : ℕ => (Nat.card (ClassFiber K C n) * torsionOrder K : ℕ) * (moment (q K * t * n) : ℂ)) S := by
  let g (a : idealSet K J) := NormGrading.grade K J ⟨a.val, a.prop.2⟩
  have hg (a : idealSet K J) (n : ℕ) : g a = n ↔ mixedEmbedding.norm a.val = (Ideal.absNorm (J : Ideal (𝓞 K)) * n : ℕ) :=
    NormGrading.grade_eq_iff K J _ n
  have hN : (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) ≠ 0 := by exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors J).ne'
  have hd : Real.sqrt ((discr K).natAbs : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K))).ne'
  have hv (n : ℕ) (a : g ⁻¹' {n}) : t / ZLattice.covolume (IdealLattices.Lattice K J) * mixedEmbedding.norm a.val.val = q K * t * n := by
    rw [(hg a.val n).mp a.prop, LatticeTheta.area K hC J, Nat.cast_mul]
    dsimp only [q]; field_simp
  apply (h.tsum_fiberwise g).congr_fun
  intro n
  simp_rw [hv n]
  rw [tsum_const, nsmul_eq_mul, class_count K C J hJ n]
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun a => (hg a n).symm))

theorem kernel_of_classes (hR : nrRealPlaces K = 2) (hC : nrComplexPlaces K = 0) (t : ℝ) (ht : 0 < t)
    (S : ClassGroup (𝓞 K) → ℂ) (hS : ∀ C, HasSum (fun n : ℕ =>
      (Nat.card (ClassFiber K C n) * torsionOrder K : ℕ) * (moment (q K * t * n) : ℂ)) (S C)) :
    kernel K t = (4 / (torsionOrder K : ℂ)) * ∑ C, S C := by
  let b (n : ℕ) : ℂ := if n = 0 then 0 else (coeff K n : ℂ) * (moment (q K * t * n) : ℂ)
  have h : HasSum (fun n => (torsionOrder K : ℂ) * b n) (∑ C, S C) := by
    apply (hasSum_sum fun C _ => hS C).congr_fun
    intro n
    simp only [b, ← Finset.sum_mul, ← Nat.cast_sum, ← Finset.sum_mul]
    by_cases hn : n = 0
    · subst n
      have hzero (C : ClassGroup (𝓞 K)) : Nat.card (ClassFiber K C 0) = 0 := by
        let : IsEmpty (ClassFiber K C 0) := ⟨fun I => (Ideal.absNorm_pos_of_nonZeroDivisors I.val).ne' I.prop.1⟩
        simp
      simp [hzero]
    · rw [if_neg hn, ← coeff_eq_sum_classes K hn, Nat.cast_mul]; ring
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K)
  change kernel K t = _
  rw [KernelExpansion.kernel_expansion K hR hC ht, ← h.tsum_eq, tsum_mul_left]
  change 4 * ∑' n, b n = (4 / (torsionOrder K : ℂ)) * ((torsionOrder K : ℂ) * ∑' n, b n)
  field_simp

end NormCounting

namespace ThetaInversion

open NumberField NumberField.Units NumberField.InfinitePlace LatticeTheta KernelData
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem poisson_of_class_integrals (e : Places K) (hC : nrComplexPlaces K = 0)
    (J : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰)
    (h : ∀ t : ℝ, 0 < t → kernel K t = (4 / (torsionOrder K : ℂ)) *
      ∑ C, ∫ r in (0 : ℝ)..regulator K, (theta K e (J C) r t - 1)) {x : ℝ} (hx : 0 < x) :
    let c : ℂ := ((4 : ℝ) * regulator K * classNumber K / torsionOrder K : ℝ)
    kernel K (1 / x) + c = (x : ℂ) * (kernel K x + c) := by
  let R := regulator K
  let T (C : ClassGroup (𝓞 K)) (t : ℝ) := ∫ r in (0 : ℝ)..R, theta K e (J C) r t
  have hs (C : ClassGroup (𝓞 K)) {t : ℝ} (ht : 0 < t) :
      (∫ r in (0 : ℝ)..regulator K, (theta K e (J C) r t - 1)) = T C t - (R : ℂ) := by
    rw [intervalIntegral.integral_sub (theta_intervalIntegrable K e hC (J C) 0 R ht) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [R, T, sub_zero, Algebra.smul_def, Complex.coe_algebraMap, mul_one]
  let c : ℂ := ((4 : ℝ) * regulator K * classNumber K / torsionOrder K : ℝ)
  have expand {t : ℝ} (ht : 0 < t) : kernel K t + c = (4 / (torsionOrder K : ℂ)) * ∑ C, T C t := by
    rw [h t ht]
    simp_rw [hs _ ht]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [c, R, classNumber, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    ring
  change kernel K (1 / x) + c = (x : ℂ) * (kernel K x + c)
  rw [expand (one_div_pos.mpr hx), expand hx]
  have hT (C : ClassGroup (𝓞 K)) : T C (1 / x) = (x : ℂ) * T C x :=
    averaged_reciprocal K e hC (J C) R hx
  simp_rw [hT]
  rw [← Finset.mul_sum, mul_left_comm]

end ThetaInversion

end OMA.RealQuadratic

open OMA.RealQuadratic

open NumberField NumberField.Units NumberField.InfinitePlace LatticeTheta
open scoped NumberField nonZeroDivisors Classical

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1.H1 := by
  intro K _ _ hdeg hC f c x hx
  have hR : nrRealPlaces K = 2 := by simpa only [hC, mul_zero, add_zero, hdeg] using card_add_two_mul_card_eq_rank K
  have hr : rank K = 1 := by rw [rank, card_eq_nrRealPlaces_add_nrComplexPlaces, hR, hC]
  let e : Places K := (Fintype.equivFinOfCardEq hR).symm
  let j : Fin (rank K) := ⟨0, by omega⟩
  choose J hJ using fun C : ClassGroup (𝓞 K) => ClassGroup.mk0_surjective C⁻¹
  apply ThetaInversion.poisson_of_class_integrals K e hC J _ (lt_of_lt_of_le zero_lt_one hx)
  intro t ht
  apply NormCounting.kernel_of_classes K hR hC t ht
  intro C
  apply NormCounting.group_class K hC C (J C) (hJ C) t
  exact (OrbitSum.hasSum_orbits K e hC hr j (J C) (regulator K) ht).congr_fun
    (fun a => (OrbitEvaluation.orbit_value K e hC hr j (J C) a ht).symm)
