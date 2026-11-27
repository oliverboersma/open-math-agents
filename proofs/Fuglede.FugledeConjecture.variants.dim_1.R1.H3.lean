import OMAReductions.R_Fuglede_FugledeConjecture_variants_dim_1_R1
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Proof of `Fuglede.FugledeConjecture.variants.dim_1.R1.H3`

Self-contained proof of Iosevich-Kolountzakis (2013) + Landau density:
every bounded measurable unit-measure spectral set in `ℝ` admits a periodic spectrum
`Γ + pℤ` with `p ∈ ℕ`, `0 < p`, `Γ.card = p`, and `Γ ⊆ [0, p)`.
-/

namespace FugledeR1H3

open MeasureTheory Complex Real Set Filter Topology
open scoped InnerProductSpace ComplexConjugate FourierTransform Convolution
open OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1

/- ## Section 0: Basic 1D Reduction and Translation of Spectra -/

noncomputable def expLp {Ω : Set (Fin 1 → ℝ)} (hΩ_fin : volume Ω ≠ ⊤) (ξ : Fin 1 → ℝ) :
    Lp ℂ 2 (volume.restrict Ω) :=
  (exponentialCharacter_memLp hΩ_fin ξ).toLp (exponentialCharacter ξ)

lemma expLp_norm_sq {Ω : Set (Fin 1 → ℝ)} (hΩ_fin : volume Ω ≠ ⊤) (ξ : Fin 1 → ℝ) :
    ⟪expLp hΩ_fin ξ, expLp hΩ_fin ξ⟫_ℂ = ((volume Ω).toReal : ℂ) := by
  unfold expLp
  rw [inner_toLp_eq]
  have hmul : ∀ x : Fin 1 → ℝ,
      conj (exponentialCharacter ξ x) * exponentialCharacter ξ x = 1 := by
    intro x
    rw [ec1_conj, ← ec1_add_left]
    simp [ec1_eq]
  simp_rw [hmul]
  simp [Measure.real]

lemma spectrum_nonempty {Ω Λ : Set (Fin 1 → ℝ)} (hsp : spectralPair Ω Λ) : Λ.Nonempty := by
  rcases hsp with ⟨_, hpos, hfin, _, hspan⟩
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hrange : (Set.range fun ξ : Λ => expLp hfin ξ.1) = ∅ := by
    ext f
    simp [hemp]
  have hcl : Submodule.topologicalClosure
      (Submodule.span ℂ (Set.range fun ξ : Λ => expLp hfin ξ.1)) = ⊥ := by
    rw [hrange, Submodule.span_empty]
    ext f
    simp [Submodule.topologicalClosure_coe, isClosed_singleton.closure_eq]
  have htop : (⊥ : Submodule ℂ (Lp ℂ 2 (volume.restrict Ω))) = ⊤ := hcl.symm.trans hspan
  have hmem : expLp hfin 0 ∈ (⊥ : Submodule ℂ (Lp ℂ 2 (volume.restrict Ω))) := by
    rw [htop]; trivial
  have hzero : expLp hfin 0 = 0 := (Submodule.mem_bot ℂ).mp hmem
  have hinner : ⟪expLp hfin 0, expLp hfin 0⟫_ℂ = 0 := by rw [hzero, inner_zero_left]
  rw [expLp_norm_sq hfin 0] at hinner
  have hreal : (volume Ω).toReal = 0 := by exact_mod_cast hinner
  have hpos_real : 0 < (volume Ω).toReal := ENNReal.toReal_pos hpos.ne' hfin
  linarith

lemma spectralPair_translate {Ω Λ : Set (Fin 1 → ℝ)} (hsp : spectralPair Ω Λ) (ξ₀ : Fin 1 → ℝ) :
    spectralPair Ω {ξ | ξ + ξ₀ ∈ Λ} := by
  rcases hsp with ⟨hmeas, hpos, hfin, hortho, hspan⟩
  refine ⟨hmeas, hpos, hfin, ?_, ?_⟩
  · intro ξ₁ hξ₁ ξ₂ hξ₂ hne
    have hne' : ξ₁ + ξ₀ ≠ ξ₂ + ξ₀ := fun h => hne (add_right_cancel h)
    have h0 := hortho (ξ₁ + ξ₀) hξ₁ (ξ₂ + ξ₀) hξ₂ hne'
    change ⟪expLp hfin ξ₁, expLp hfin ξ₂⟫_ℂ = 0
    change ⟪expLp hfin (ξ₁ + ξ₀), expLp hfin (ξ₂ + ξ₀)⟫_ℂ = 0 at h0
    rw [← h0]
    unfold expLp
    rw [inner_toLp_eq, inner_toLp_eq]
    congr 1; funext x
    rw [ec1_conj, ec1_conj, ← ec1_add_left, ← ec1_add_left]
    congr 1
    ext i
    simp
    ring
  · set M : Submodule ℂ (Lp ℂ 2 (volume.restrict Ω)) :=
      Submodule.span ℂ (Set.range fun ξ : {ξ | ξ + ξ₀ ∈ Λ} => expLp hfin ξ.1)
    set M₀ : Submodule ℂ (Lp ℂ 2 (volume.restrict Ω)) :=
      Submodule.span ℂ (Set.range fun ξ : Λ => expLp hfin ξ.1)
    have hM0_orth : M₀ᗮ = ⊥ := by
      rw [← Submodule.orthogonal_eq_top_iff, Submodule.orthogonal_orthogonal_eq_closure]
      exact hspan
    rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.orthogonal_eq_top_iff]
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_bot]
    -- Multiply f by exponentialCharacter ξ₀
    have hmul_memLp : MemLp (fun x => exponentialCharacter ξ₀ x * f x) 2 (volume.restrict Ω) := by
      refine MemLp.mono (Lp.memLp f)
        ((continuous_exponentialCharacter ξ₀).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) ?_
      filter_upwards with x
      rw [norm_mul, norm_exponentialCharacter, one_mul]
    set g : Lp ℂ 2 (volume.restrict Ω) := hmul_memLp.toLp _
    have hg_orth : g ∈ M₀ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro _ ⟨⟨η, hη⟩, rfl⟩
        have hη' : η - ξ₀ ∈ {ξ | ξ + ξ₀ ∈ Λ} := by
          change (η - ξ₀) + ξ₀ ∈ Λ
          simpa using hη
        have hfeq : ⟪expLp hfin (η - ξ₀), f⟫_ℂ = 0 := by
          have hmemM : expLp hfin (η - ξ₀) ∈ M :=
            Submodule.subset_span ⟨⟨η - ξ₀, hη'⟩, rfl⟩
          exact (Submodule.mem_orthogonal M f).mp hf _ hmemM
        rw [← hfeq]
        unfold expLp g
        rw [L2.inner_def, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [(exponentialCharacter_memLp hfin η).coeFn_toLp,
          (exponentialCharacter_memLp hfin (η - ξ₀)).coeFn_toLp,
          hmul_memLp.coeFn_toLp] with x h1 h2 h3
        rw [h1, h2, h3, RCLike.inner_apply, RCLike.inner_apply]
        rw [ec1_conj, ec1_conj]
        have hrel : exponentialCharacter (-η) x * exponentialCharacter ξ₀ x =
            exponentialCharacter (-(η - ξ₀)) x := by
          rw [← ec1_add_left]
          congr 1
          ext i; simp; ring
        calc
          exponentialCharacter ξ₀ x * f x * exponentialCharacter (-η) x
              = (exponentialCharacter (-η) x * exponentialCharacter ξ₀ x) * f x := by ring
          _ = exponentialCharacter (-(η - ξ₀)) x * f x := by rw [hrel]
          _ = f x * exponentialCharacter (-(η - ξ₀)) x := by ring
      · simp
      · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
      · intro c x _ hx; rw [inner_smul_left, hx, mul_zero]
    rw [hM0_orth, Submodule.mem_bot] at hg_orth
    have hae : (fun x => exponentialCharacter ξ₀ x * f x) =ᵐ[volume.restrict Ω] 0 := by
      filter_upwards [hmul_memLp.coeFn_toLp, Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with x h1 h2
      have hgx : g x = 0 := by rw [hg_orth]; exact h2
      rw [← h1, hgx]; rfl
    have hfae : (f : (Fin 1 → ℝ) → ℂ) =ᵐ[volume.restrict Ω] 0 := by
      filter_upwards [hae] with x hx
      have hne0 : exponentialCharacter ξ₀ x ≠ 0 := by
        intro h0
        have := norm_exponentialCharacter ξ₀ x
        rw [h0, norm_zero] at this
        norm_num at this
      exact (mul_eq_zero.mp hx).resolve_left hne0
    exact Lp.ext (hfae.trans (Lp.coeFn_zero ℂ 2 (volume.restrict Ω)).symm)

/- ## Section 1: Entire Fourier Transform `F`, Parseval Tiling, Discreteness of Zeros -/

noncomputable def F (S : Set ℝ) (z : ℂ) : ℂ :=
  ∫ t in S, Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))

lemma F_zero {S : Set ℝ} (hS_vol : volume S = 1) : F S 0 = 1 := by
  unfold F
  simp [hS_vol, Measure.real]

lemma F_neg_real (S : Set ℝ) (ξ : ℝ) : F S ((-ξ : ℝ) : ℂ) = conj (F S (ξ : ℂ)) := by
  unfold F
  rw [← integral_conj]
  congr 1; funext t
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

lemma norm_F_real_le_one {S : Set ℝ} (hS_vol : volume S = 1) (ξ : ℝ) :
    ‖F S (ξ : ℂ)‖ ≤ 1 := by
  unfold F
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (t : ℂ))‖ = 1 := by
    intro t
    have h : -2 * Real.pi * Complex.I * (ξ : ℂ) * (t : ℂ) =
        Complex.I * ((-2 * Real.pi * ξ * t : ℝ) : ℂ) := by
      push_cast; ring
    rw [h, Complex.norm_exp_I_mul_ofReal]
  calc
    ‖∫ t in S, Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (t : ℂ))‖
        ≤ ∫ t in S, ‖Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (t : ℂ))‖ :=
          norm_integral_le_integral_norm _
    _ = ∫ _t in S, (1 : ℝ) := by simp_rw [hnorm]
    _ = 1 := by simp [hS_vol, Measure.real]

lemma inner_expLp_eq_F {Ω : Set (Fin 1 → ℝ)} {S : Set ℝ}
    (hΩ_eq : Ω = {x : Fin 1 → ℝ | x 0 ∈ S}) (hΩ_fin : volume Ω ≠ ⊤) (ξ η : Fin 1 → ℝ) :
    ⟪expLp hΩ_fin ξ, expLp hΩ_fin η⟫_ℂ = F S ((ξ 0 - η 0 : ℝ) : ℂ) := by
  unfold expLp F
  rw [inner_toLp_eq, hΩ_eq, setIntegral_preimage_apply0]
  congr 1; funext t
  rw [ec1_conj, ← ec1_add_left, ec1_eq]
  congr 1
  simp only [Pi.add_apply, Pi.neg_apply, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg]
  ring

lemma parseval_and_ortho {Ω : Set (Fin 1 → ℝ)} {S Λ : Set ℝ}
    (hΩ_eq : Ω = {x : Fin 1 → ℝ | x 0 ∈ S}) (hS_vol : volume S = 1)
    (hsp : spectralPair Ω {ξ : Fin 1 → ℝ | ξ 0 ∈ Λ}) :
    (∀ l₁ ∈ Λ, ∀ l₂ ∈ Λ, l₁ ≠ l₂ → F S ((l₁ - l₂ : ℝ) : ℂ) = 0) ∧
    (∀ t : ℝ, HasSum (fun lam : Λ => ‖F S ((t - lam.1 : ℝ) : ℂ)‖ ^ 2) 1) := by
  rcases hsp with ⟨_, _, hfin, hortho, hspan⟩
  have hΩ_vol : volume Ω = 1 := by rw [hΩ_eq, volume_preimage_apply0, hS_vol]
  have hF_ortho : ∀ l₁ ∈ Λ, ∀ l₂ ∈ Λ, l₁ ≠ l₂ → F S ((l₁ - l₂ : ℝ) : ℂ) = 0 := by
    intro l₁ h₁ l₂ h₂ hne
    have hne' : (fun _ : Fin 1 => l₁) ≠ (fun _ : Fin 1 => l₂) := fun h =>
      hne (congrFun h 0)
    have h0 := hortho (fun _ => l₁) h₁ (fun _ => l₂) h₂ hne'
    change ⟪expLp hfin (fun _ => l₁), expLp hfin (fun _ => l₂)⟫_ℂ = 0 at h0
    rw [inner_expLp_eq_F hΩ_eq hfin] at h0
    simpa using h0
  refine ⟨hF_ortho, ?_⟩
  -- Build HilbertBasis indexed by Λ
  let v : Λ → Lp ℂ 2 (volume.restrict Ω) := fun lam => expLp hfin (fun _ => lam.1)
  have hv_ortho : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, v, expLp_norm_sq, hΩ_vol]
      simp
    · simp only [hij, ↓reduceIte, v]
      rw [inner_expLp_eq_F hΩ_eq hfin]
      exact hF_ortho i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
  have hv_range : Set.range v =
      Set.range (fun ξ : {ξ : Fin 1 → ℝ | ξ 0 ∈ Λ} => expLp hfin ξ.1) := by
    ext f
    constructor
    · rintro ⟨⟨lam, hl⟩, rfl⟩
      exact ⟨⟨fun _ => lam, hl⟩, rfl⟩
    · rintro ⟨⟨ξ, hξ⟩, rfl⟩
      refine ⟨⟨ξ 0, hξ⟩, ?_⟩
      have hξ_eq : (fun _ : Fin 1 => ξ 0) = ξ := by ext i; fin_cases i; rfl
      simp [v, hξ_eq]
  have hv_span : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
    rw [hv_range]; exact hspan
  let b : HilbertBasis Λ ℂ (Lp ℂ 2 (volume.restrict Ω)) :=
    HilbertBasis.mk hv_ortho (by rw [hv_span])
  intro t
  have hb_eq : ∀ lam : Λ, b lam = v lam := fun lam => by simp [b]
  have hsumC := b.hasSum_inner_mul_inner (expLp hfin (fun _ => t)) (expLp hfin (fun _ => t))
  have hself : ⟪expLp hfin (fun _ => t), expLp hfin (fun _ => t)⟫_ℂ = 1 := by
    rw [expLp_norm_sq, hΩ_vol]; simp
  rw [hself] at hsumC
  have hterm : ∀ lam : Λ,
      ⟪expLp hfin (fun _ => t), b lam⟫_ℂ * ⟪b lam, expLp hfin (fun _ => t)⟫_ℂ =
        ((‖F S ((t - lam.1 : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
    intro lam
    rw [hb_eq]
    have hconj : ⟪v lam, expLp hfin (fun _ => t)⟫_ℂ = conj ⟪expLp hfin (fun _ => t), v lam⟫_ℂ := by
      rw [inner_conj_symm]
    rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hinner : ⟪expLp hfin (fun _ => t), v lam⟫_ℂ = F S ((t - lam.1 : ℝ) : ℂ) := by
      rw [inner_expLp_eq_F hΩ_eq hfin]
    rw [hinner]
  simp_rw [hterm] at hsumC
  have hre := Complex.reCLM.hasSum hsumC
  simpa [← Complex.ofReal_pow] using hre

lemma differentiable_F {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) : Differentiable ℂ (F S) := by
  intro z₀
  obtain ⟨R, hR⟩ := hS_bdd.subset_closedBall (0 : ℝ)
  set M : ℝ := max R 0
  have hS_bound : ∀ t ∈ S, |t| ≤ M := fun t ht => by
    have h1 : dist t 0 ≤ R := hR ht
    rw [Real.dist_eq, sub_zero] at h1
    exact le_trans h1 (le_max_left R 0)
  have hS_fin : volume S ≠ ⊤ := by
    have hsub : S ⊆ Set.Icc (-M) M := fun t ht => abs_le.mp (hS_bound t ht)
    exact ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono hsub)
  have : IsFiniteMeasure (volume.restrict S) := ⟨by simp [hS_fin.lt_top]⟩
  let f : ℂ → ℝ → ℂ := fun z t => Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))
  let f' : ℂ → ℝ → ℂ := fun z t =>
    (-2 * Real.pi * Complex.I * (t : ℂ)) * Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))
  let C : ℝ := 2 * Real.pi * M * Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M)
  have hdiff : ∀ t : ℝ, ∀ z : ℂ, HasDerivAt (fun w => f w t) (f' z t) z := by
    intro t z
    have hlin : HasDerivAt (fun w : ℂ => -2 * Real.pi * Complex.I * w * (t : ℂ))
        (-2 * Real.pi * Complex.I * (t : ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul (-2 * Real.pi * Complex.I)).mul_const (t : ℂ)
    simpa [f, f', mul_comm] using hlin.cexp
  have hbound : ∀ᵐ t ∂(volume.restrict S), ∀ z ∈ Metric.ball z₀ 1, ‖f' z t‖ ≤ C := by
    filter_upwards [ae_restrict_mem hS_meas] with t ht z hz
    have htm : |t| ≤ M := hS_bound t ht
    have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := Metric.mem_ball.mp hz
      calc ‖z‖ = ‖z₀ + (z - z₀)‖ := by ring_nf
        _ ≤ ‖z₀‖ + ‖z - z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + 1 := by rw [← dist_eq_norm]; linarith
    have him : |z.im| ≤ ‖z₀‖ + 1 := le_trans (Complex.abs_im_le_norm z) hz_norm
    have hexp_re : (-2 * Real.pi * Complex.I * z * (t : ℂ)).re = 2 * Real.pi * z.im * t := by
      simp [Complex.mul_re, Complex.mul_im]
    have hexp_norm : ‖Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))‖ ≤
        Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M) := by
      rw [Complex.norm_exp, hexp_re]
      apply Real.exp_le_exp.mpr
      have h1 : 2 * Real.pi * z.im * t ≤ 2 * Real.pi * |z.im| * |t| := by
        have hpi : 0 ≤ 2 * Real.pi := by positivity
        have h2 : z.im * t ≤ |z.im| * |t| := by
          rw [← abs_mul]; exact le_abs_self _
        nlinarith
      have h2 : 2 * Real.pi * |z.im| * |t| ≤ 2 * Real.pi * (‖z₀‖ + 1) * M := by
        gcongr
      exact le_trans h1 h2
    have hpref : ‖-2 * Real.pi * Complex.I * (t : ℂ)‖ ≤ 2 * Real.pi * M := by
      rw [norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      gcongr
    calc
      ‖f' z t‖ = ‖-2 * Real.pi * Complex.I * (t : ℂ)‖ *
          ‖Complex.exp (-2 * Real.pi * Complex.I * z * (t : ℂ))‖ := norm_mul _ _
      _ ≤ (2 * Real.pi * M) * Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M) := by
          gcongr
  have hF_int : Integrable (f z₀) (volume.restrict S) := by
    refine Integrable.of_bound (Continuous.aestronglyMeasurable (by fun_prop))
      (Real.exp (2 * Real.pi * (‖z₀‖ + 1) * M)) ?_
    filter_upwards [ae_restrict_mem hS_meas] with t ht
    have htm : |t| ≤ M := hS_bound t ht
    have him : |z₀.im| ≤ ‖z₀‖ + 1 := by linarith [Complex.abs_im_le_norm z₀]
    have hexp_re : (-2 * Real.pi * Complex.I * z₀ * (t : ℂ)).re = 2 * Real.pi * z₀.im * t := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [Complex.norm_exp, hexp_re]
    apply Real.exp_le_exp.mpr
    have h1 : z₀.im * t ≤ |z₀.im| * |t| := by rw [← abs_mul]; exact le_abs_self _
    have h2 : |z₀.im| * |t| ≤ (‖z₀‖ + 1) * M := by gcongr
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    nlinarith
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ zero_lt_one)
    (Eventually.of_forall fun z => Continuous.aestronglyMeasurable (by fun_prop))
    hF_int
    (Continuous.aestronglyMeasurable (by fun_prop))
    hbound
    (integrable_const C)
    (Eventually.of_forall fun t z _ => hdiff t z)
  exact hres.2.differentiableAt

lemma zero_set_inter_Icc_finite {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (R : ℝ) :
    ({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-R) R).Finite := by
  have han : AnalyticOnNhd ℂ (F S) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_F hS_bdd hS_meas)
  by_contra hinf
  have hcomp : IsCompact (Set.Icc (-R) R) := isCompact_Icc
  obtain ⟨x₀, hx₀_mem, hx₀_acc⟩ :=
    (Set.Infinite.exists_accPt_of_subset_isCompact hinf hcomp Set.inter_subset_right)
  have hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), F S z = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    rcases hU with ⟨V, hV_open, hx₀V, hVU⟩
    have hpre : Complex.ofReal ⁻¹' V ∈ 𝓝 x₀ :=
      (Complex.continuous_ofReal.isOpen_preimage V hV_open).mem_nhds hx₀V
    have hne : (({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-R) R) ∩ ((Complex.ofReal ⁻¹' V) \ {x₀})).Nonempty := by
      rw [accPt_iff_nhds] at hx₀_acc
      obtain ⟨y, hy1, hy2⟩ := hx₀_acc (Complex.ofReal ⁻¹' V) hpre
      exact ⟨y, hy1.2, hy1.1, hy2⟩
    rcases hne with ⟨y, ⟨hyF, _⟩, hyV, hyne⟩
    refine ⟨(y : ℂ), hVU ⟨hyV, ?_⟩, hyF⟩
    exact fun h => hyne (Complex.ofReal_injective h)
  have hzero : Set.EqOn (F S) 0 Set.univ :=
    han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ _) hfreq
  have h0 : F S 0 = 0 := hzero (mem_univ 0)
  rw [F_zero hS_vol] at h0
  exact one_ne_zero h0

lemma exists_min_gap {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    ∃ δ > 0, ∀ ξ : ℝ, F S (ξ : ℂ) = 0 → δ ≤ |ξ| := by
  have hfin := zero_set_inter_Icc_finite hS_bdd hS_meas hS_vol 1
  set Z1 : Finset ℝ := hfin.toFinset
  by_cases hne : Z1.Nonempty
  · set m : ℝ := (Z1.image abs).min' (hne.image abs)
    have hm_pos : 0 < m := by
      have hm_mem : m ∈ Z1.image abs := Finset.min'_mem _ _
      rcases Finset.mem_image.mp hm_mem with ⟨ξ, hξ, hm_eq⟩
      have hξ' : F S (ξ : ℂ) = 0 := ((hfin.mem_toFinset).mp hξ).1
      have hξ0 : ξ ≠ 0 := by
        intro h0; subst h0
        rw [Complex.ofReal_zero, F_zero hS_vol] at hξ'
        exact one_ne_zero hξ'
      rw [← hm_eq]
      exact abs_pos.mpr hξ0
    refine ⟨min 1 m, lt_min zero_lt_one hm_pos, ?_⟩
    intro ξ hξ
    by_cases h1 : |ξ| ≤ 1
    · have hmem : ξ ∈ Z1 := hfin.mem_toFinset.mpr ⟨hξ, abs_le.mp h1⟩
      exact le_trans (min_le_right 1 m) (Finset.min'_le _ _ (Finset.mem_image_of_mem abs hmem))
    · exact le_trans (min_le_left 1 m) (le_of_not_ge h1)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ξ hξ
    by_contra hlt
    push Not at hlt
    have hmem : ξ ∈ Z1 := hfin.mem_toFinset.mpr ⟨hξ, abs_le.mp hlt.le⟩
    exact hne ⟨ξ, hmem⟩

lemma separated_inter_Icc_finite_and_card_le {Λ : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → δ ≤ |x - y|) (a b : ℝ) :
    (Λ ∩ Set.Icc a b).Finite ∧
      (Λ ∩ Set.Icc a b).ncard ≤ Nat.floor (max 0 (b - a) / δ) + 1 := by
  set N : ℕ := Nat.floor (max 0 (b - a) / δ) + 1
  let f : (Λ ∩ Set.Icc a b : Set ℝ) → Fin N := fun x =>
    ⟨Nat.floor ((x.1 - a) / δ), by
      have hxa : 0 ≤ x.1 - a := sub_nonneg.mpr x.2.2.1
      have hxb : x.1 - a ≤ max 0 (b - a) := le_trans (sub_le_sub_right x.2.2.2 a) (le_max_right _ _)
      have hdiv : (x.1 - a) / δ ≤ max 0 (b - a) / δ := div_le_div_of_nonneg_right hxb hδ.le
      exact Nat.lt_succ_of_le (Nat.floor_mono hdiv)⟩
  have hfinj : Function.Injective f := by
    rintro ⟨x, hxΛ, hxa, _⟩ ⟨y, hyΛ, hya, _⟩ heq
    apply Subtype.ext
    by_contra hne
    have hfloor : Nat.floor ((x - a) / δ) = Nat.floor ((y - a) / δ) :=
      congrArg Fin.val heq
    have hx0 : 0 ≤ (x - a) / δ := div_nonneg (sub_nonneg.mpr hxa) hδ.le
    have hy0 : 0 ≤ (y - a) / δ := div_nonneg (sub_nonneg.mpr hya) hδ.le
    have hx_lo : (Nat.floor ((x - a) / δ) : ℝ) ≤ (x - a) / δ := Nat.floor_le hx0
    have hx_hi : (x - a) / δ < (Nat.floor ((x - a) / δ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hy_lo : (Nat.floor ((x - a) / δ) : ℝ) ≤ (y - a) / δ := hfloor ▸ Nat.floor_le hy0
    have hy_hi : (y - a) / δ < (Nat.floor ((x - a) / δ) : ℝ) + 1 := hfloor ▸ Nat.lt_floor_add_one _
    have hdiff : |(x - a) / δ - (y - a) / δ| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    have hdiff' : |x - y| / δ < 1 := by
      have heq1 : (x - a) / δ - (y - a) / δ = (x - y) / δ := by ring
      rw [heq1, abs_div, abs_of_pos hδ] at hdiff
      exact hdiff
    have hlt : |x - y| < δ := (div_lt_one hδ).mp hdiff'
    linarith [hsep x hxΛ y hyΛ hne]
  have : Finite (Λ ∩ Set.Icc a b : Set ℝ) := Finite.of_injective f hfinj
  have hfin : (Λ ∩ Set.Icc a b).Finite := Set.toFinite _
  refine ⟨hfin, ?_⟩
  have hcard := Nat.card_le_card_of_injective f hfinj
  rw [Nat.card_fin] at hcard
  rw [← Nat.card_coe_set_eq]
  exact hcard

lemma separated_countable {Λ : Set ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → δ ≤ |x - y|) : Λ.Countable := by
  have hunion : Λ = ⋃ n : ℕ, Λ ∩ Set.Icc (-(n : ℝ)) (n : ℝ) := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_Icc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_ge |x|
      exact ⟨n, hx, abs_le.mp hn⟩
    · rintro ⟨_, hx, _⟩; exact hx
  rw [hunion]
  exact Set.countable_iUnion fun n => (separated_inter_Icc_finite_and_card_le hδ hsep _ _).1.countable

/- ## Section 2: Autocorrelation, Fourier Inversion, Bounded Gaps, and Density 1 -/

lemma fourier_real_eq (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = ∫ v : ℝ, Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (w : ℂ)) * f v := by
  rw [Real.fourier_eq']
  congr 1; funext v
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 2; push_cast; ring

lemma fourierInv_real_eq (f : ℝ → ℂ) (w : ℝ) :
    𝓕⁻ f w = ∫ v : ℝ, Complex.exp (2 * Real.pi * Complex.I * (v : ℂ) * (w : ℂ)) * f v := by
  rw [Real.fourierInv_eq']
  congr 1; funext v
  simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
  congr 2; push_cast; ring

lemma integral_comp_neg_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x : ℝ, f (-x) = ∫ x : ℝ, f x := by
  have h := Measure.integral_comp_mul_left f (-1)
  simpa using h

lemma continuous_fourier_real {f : ℝ → ℂ} (hf : Integrable f volume) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

lemma integral_complex_ofReal (f : ℝ → ℝ) :
    ∫ x : ℝ, (f x : ℂ) = ((∫ x : ℝ, f x : ℝ) : ℂ) := by
  simpa using (integral_ofReal (𝕜 := ℂ) (f := f))

noncomputable def indS (S : Set ℝ) : ℝ → ℂ := S.indicator (fun _ => (1 : ℂ))

noncomputable def hAuto (S : Set ℝ) : ℝ → ℂ :=
  (indS S) ⋆[ContinuousLinearMap.mul ℂ ℂ] (fun x => indS S (-x))

noncomputable def gFun (S : Set ℝ) (ξ : ℝ) : ℝ := ‖F S (ξ : ℂ)‖ ^ 2

lemma gFun_nonneg (S : Set ℝ) (ξ : ℝ) : 0 ≤ gFun S ξ := sq_nonneg _

lemma gFun_even (S : Set ℝ) (ξ : ℝ) : gFun S (-ξ) = gFun S ξ := by
  unfold gFun
  rw [F_neg_real, Complex.norm_conj]

lemma gFun_le_one {S : Set ℝ} (hS_vol : volume S = 1) (ξ : ℝ) : gFun S ξ ≤ 1 := by
  unfold gFun
  have h := norm_F_real_le_one hS_vol ξ
  nlinarith [norm_nonneg (F S (ξ : ℂ))]

lemma continuous_gFun {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) : Continuous (gFun S) := by
  unfold gFun
  have hF : Continuous (fun ξ : ℝ => F S (ξ : ℂ)) :=
    (differentiable_F hS_bdd hS_meas).continuous.comp Complex.continuous_ofReal
  fun_prop

lemma integrable_indS {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    Integrable (indS S) volume := by
  unfold indS
  rw [integrable_indicator_iff hS_meas]
  exact integrableOn_const (by rw [hS_vol]; simp)

lemma integrable_indS_neg {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    Integrable (fun x => indS S (-x)) volume :=
  (integrable_indS hS_meas hS_vol).comp_neg

lemma integrable_hAuto {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    Integrable (hAuto S) volume :=
  (integrable_indS hS_meas hS_vol).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_indS_neg hS_meas hS_vol)

lemma hAuto_apply (S : Set ℝ) (y : ℝ) :
    hAuto S y = ∫ x, indS S x * indS S (x - y) := by
  unfold hAuto
  simp only [convolution_def, ContinuousLinearMap.mul_apply', neg_sub]

lemma hAuto_zero {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    hAuto S 0 = 1 := by
  rw [hAuto_apply]
  have hmul : ∀ x : ℝ, indS S x * indS S (x - 0) = indS S x := by
    intro x
    simp only [sub_zero, indS]
    by_cases hx : x ∈ S <;> simp [hx]
  simp_rw [hmul]
  unfold indS
  rw [integral_indicator hS_meas]
  simp [hS_vol, Measure.real]

lemma continuous_hAuto {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    Continuous (hAuto S) := by
  have hf : Integrable (indS S) volume := integrable_indS hS_meas hS_vol
  rw [Metric.continuous_iff]
  intro y₀ ε hε
  obtain ⟨φ, hφ_cs, hφ_approx, hφ_cont, hφ_int⟩ :=
    hf.exists_hasCompactSupport_integral_sub_le (show 0 < ε / 3 by linarith)
  -- Bound φ on its compact support
  obtain ⟨R, hR⟩ := hφ_cs.isBounded.subset_closedBall (0 : ℝ)
  set M : ℝ := max R 0
  have hφ_supp : ∀ x : ℝ, M < |x| → φ x = 0 := by
    intro x hx
    by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ (Function.mem_support.mpr hne)
    have hdist : dist x 0 ≤ R := hR hmem
    rw [Real.dist_eq, sub_zero] at hdist
    linarith [le_max_left R 0]
  have hφ_bdd : ∃ C : ℝ, ∀ x : ℝ, ‖φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hφ_cs.exists_bound_of_continuous hφ_cont
    exact ⟨C, hC⟩
  rcases hφ_bdd with ⟨C, hC⟩
  have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg (φ 0)) (hC 0)
  -- Continuity of translation for φ at 0 by dominated convergence
  have htrans : Tendsto (fun t : ℝ => ∫ x : ℝ, ‖φ (x - t) - φ x‖) (𝓝 0) (𝓝 0) := by
    have hlim : (0 : ℝ) = ∫ _x : ℝ, (0 : ℝ) := by simp
    conv_rhs => rw [hlim]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (Set.Icc (-(M + 1)) (M + 1)).indicator (fun _ => 2 * C) x) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun t =>
        (hφ_cont.comp (continuous_id.sub continuous_const) |>.sub hφ_cont).norm.aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      filter_upwards with x
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      by_cases hx : x ∈ Set.Icc (-(M + 1)) (M + 1)
      · rw [Set.indicator_of_mem hx]
        calc ‖φ (x - t) - φ x‖ ≤ ‖φ (x - t)‖ + ‖φ x‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring
      · rw [Set.indicator_of_notMem hx]
        have hx_gt : M + 1 < |x| := by
          by_contra hle; push Not at hle
          exact hx (abs_le.mp hle)
        have h1 : M < |x| := by linarith
        have h2 : M < |x - t| := by
          have := abs_sub_abs_le_abs_sub x t
          linarith
        rw [hφ_supp x h1, hφ_supp (x - t) h2, sub_self, norm_zero]
    · rw [integrable_indicator_iff measurableSet_Icc]
      exact integrableOn_const (by simp [Real.volume_Icc])
    · filter_upwards with x
      have h1 : Tendsto (fun t : ℝ => φ (x - t) - φ x) (𝓝 0) (𝓝 (φ (x - 0) - φ x)) :=
        ((hφ_cont.tendsto (x - 0)).comp (tendsto_const_nhds.sub tendsto_id)).sub tendsto_const_nhds
      rw [sub_zero, sub_self] at h1
      simpa using h1.norm
  rw [Metric.tendsto_nhds] at htrans
  have hmem_nhds := htrans (ε / 3) (by linarith)
  rw [Metric.eventually_nhds_iff] at hmem_nhds
  rcases hmem_nhds with ⟨δ, hδ_pos, hδ⟩
  refine ⟨δ, hδ_pos, ?_⟩
  intro y hy
  rw [dist_eq_norm]
  rw [hAuto_apply, hAuto_apply]
  have hint_sub : Integrable (fun x => indS S x * indS S (x - y)) volume := by
    refine hf.norm.mono' ?_ ?_
    · exact hf.aestronglyMeasurable.mul
        (hf.comp_sub_right y).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul]
      have h1 : ‖indS S (x - y)‖ ≤ 1 := by
        unfold indS; by_cases h : x - y ∈ S <;> simp [h]
      simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hint_sub0 : Integrable (fun x => indS S x * indS S (x - y₀)) volume := by
    refine hf.norm.mono' ?_ ?_
    · exact hf.aestronglyMeasurable.mul
        (hf.comp_sub_right y₀).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul]
      have h1 : ‖indS S (x - y₀)‖ ≤ 1 := by
        unfold indS; by_cases h : x - y₀ ∈ S <;> simp [h]
      simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  rw [← integral_sub hint_sub hint_sub0]
  have hstep1 : ‖∫ x, (indS S x * indS S (x - y) - indS S x * indS S (x - y₀))‖ ≤
      ∫ x, ‖indS S (x - y) - indS S (x - y₀)‖ := by
    calc
      ‖∫ x, (indS S x * indS S (x - y) - indS S x * indS S (x - y₀))‖
          ≤ ∫ x, ‖indS S x * (indS S (x - y) - indS S (x - y₀))‖ := by
            have := norm_integral_le_integral_norm (μ := volume)
              (fun x => indS S x * indS S (x - y) - indS S x * indS S (x - y₀))
            simpa [mul_sub] using this
      _ ≤ ∫ x, ‖indS S (x - y) - indS S (x - y₀)‖ := by
            apply integral_mono
            · exact (hint_sub.sub hint_sub0).norm.congr (Eventually.of_forall fun x => by simp [mul_sub])
            · exact ((hf.comp_sub_right y).sub (hf.comp_sub_right y₀)).norm
            · intro x
              dsimp only
              rw [norm_mul]
              have h1 : ‖indS S x‖ ≤ 1 := by
                unfold indS; by_cases h : x ∈ S <;> simp [h]
              simpa using mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hshift : ∫ x, ‖indS S (x - y) - indS S (x - y₀)‖ =
      ∫ u, ‖indS S (u - (y - y₀)) - indS S u‖ := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun u => ‖indS S (u - (y - y₀)) - indS S u‖) y₀
    rw [← h]
    congr 1; funext x; ring_nf
  have htri : ∫ u, ‖indS S (u - (y - y₀)) - indS S u‖ ≤
      (∫ u, ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖) +
      (∫ u, ‖φ (u - (y - y₀)) - φ u‖) +
      (∫ u, ‖φ u - indS S u‖) := by
    have hi1 : Integrable (fun u => ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖) volume :=
      ((hf.sub hφ_int).comp_sub_right (y - y₀)).norm
    have hi2 : Integrable (fun u => ‖φ (u - (y - y₀)) - φ u‖) volume :=
      ((hφ_int.comp_sub_right (y - y₀)).sub hφ_int).norm
    have hi3 : Integrable (fun u => ‖φ u - indS S u‖) volume :=
      (hφ_int.sub hf).norm
    have hi12 : Integrable (fun u => ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖ +
        ‖φ (u - (y - y₀)) - φ u‖) volume := hi1.add hi2
    rw [← integral_add hi1 hi2, ← integral_add hi12 hi3]
    apply integral_mono (((hf.comp_sub_right (y - y₀)).sub hf).norm) (hi12.add hi3)
    intro u
    dsimp only
    calc
      ‖indS S (u - (y - y₀)) - indS S u‖
          = ‖(indS S (u - (y - y₀)) - φ (u - (y - y₀))) +
              (φ (u - (y - y₀)) - φ u) + (φ u - indS S u)‖ := by ring_nf
      _ ≤ ‖(indS S (u - (y - y₀)) - φ (u - (y - y₀))) + (φ (u - (y - y₀)) - φ u)‖ +
            ‖φ u - indS S u‖ := norm_add_le _ _
      _ ≤ ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖ + ‖φ (u - (y - y₀)) - φ u‖ +
            ‖φ u - indS S u‖ := by gcongr; exact norm_add_le _ _
  have hterm1 : ∫ u, ‖indS S (u - (y - y₀)) - φ (u - (y - y₀))‖ ≤ ε / 3 := by
    rw [integral_sub_right_eq_self (fun u => ‖indS S u - φ u‖) (y - y₀)]
    exact hφ_approx
  have hterm3 : ∫ u, ‖φ u - indS S u‖ ≤ ε / 3 := by
    have : (fun u => ‖φ u - indS S u‖) = fun u => ‖indS S u - φ u‖ := by
      funext u; exact norm_sub_rev _ _
    rw [this]; exact hφ_approx
  have hterm2 : ∫ u, ‖φ (u - (y - y₀)) - φ u‖ < ε / 3 := by
    have hlt := hδ (by simpa [Real.dist_eq] using hy)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at hlt
    exact hlt
  linarith

lemma fourier_indS {S : Set ℝ} (hS_meas : MeasurableSet S) (ξ : ℝ) :
    𝓕 (indS S) ξ = F S (ξ : ℂ) := by
  rw [fourier_real_eq]
  unfold indS F
  have h : (fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (ξ : ℂ)) *
      S.indicator (fun _ => (1 : ℂ)) v) =
      S.indicator (fun v => Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (v : ℂ))) := by
    funext v
    by_cases hv : v ∈ S
    · simp only [Set.indicator_of_mem hv, mul_one]
      congr 1; ring
    · simp [Set.indicator_of_notMem hv]
  rw [h, integral_indicator hS_meas]

lemma fourier_indS_neg {S : Set ℝ} (hS_meas : MeasurableSet S) (ξ : ℝ) :
    𝓕 (fun x => indS S (-x)) ξ = conj (F S (ξ : ℂ)) := by
  rw [← F_neg_real, ← fourier_indS hS_meas (-ξ)]
  rw [fourier_real_eq, fourier_real_eq]
  rw [← integral_comp_neg_real (fun v =>
    Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * ((-ξ : ℝ) : ℂ)) * indS S v)]
  congr 1; funext v
  congr 1; push_cast; ring

lemma fourier_hAuto {S : Set ℝ} (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (ξ : ℝ) :
    𝓕 (hAuto S) ξ = ((gFun S ξ : ℝ) : ℂ) := by
  unfold hAuto gFun
  rw [Real.fourier_mul_convolution_eq (integrable_indS hS_meas hS_vol)
    (integrable_indS_neg hS_meas hS_vol)]
  rw [fourier_indS hS_meas, fourier_indS_neg hS_meas]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma integrable_gFun_and_integral_one {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    Integrable (gFun S) volume ∧ ∫ ξ, gFun S ξ = 1 := by
  have hh_int : Integrable (hAuto S) volume := integrable_hAuto hS_meas hS_vol
  have hh_cont : Continuous (hAuto S) := continuous_hAuto hS_meas hS_vol
  have hgauss_lim := Real.tendsto_integral_gaussian_smul' hh_int (v := (0 : ℝ)) hh_cont.continuousAt
  rw [hAuto_zero hS_meas hS_vol] at hgauss_lim
  -- Rewrite Gaussian convolution via Fourier flip identity
  have hflip : Tendsto (fun c : ℝ => ∫ v : ℝ,
      Complex.exp (-((c : ℂ)⁻¹) * (v : ℂ) ^ 2) * ((gFun S v : ℝ) : ℂ)) atTop (𝓝 1) := by
    refine hgauss_lim.congr' ?_
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    have hre : 0 < ((c : ℂ)⁻¹).re := by
      rw [← Complex.ofReal_inv, Complex.ofReal_re]
      exact inv_pos.mpr hc
    have hJ : Integrable (fun v : ℝ => Complex.exp (-((c : ℂ)⁻¹) * (‖v‖ : ℂ) ^ 2)) volume := by
      have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hre (0 : ℝ) (0 : ℝ)
      simpa using this
    have hstep := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hJ hh_int
    have hfg : ∀ w : ℝ,
        𝓕 (fun v : ℝ => Complex.exp (-((c : ℂ)⁻¹) * (‖v‖ : ℂ) ^ 2)) w =
          ((Real.pi * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
            Complex.exp (-Real.pi ^ 2 * (c : ℂ) * (‖(0 : ℝ) - w‖ : ℂ) ^ 2)) := by
      intro w
      rw [fourier_gaussian_innerProductSpace hre w]
      congr 1
      · congr 1
        rw [div_inv_eq_mul]
      · congr 1
        simp only [zero_sub, norm_neg]
        rw [div_inv_eq_mul]
        ring
    have h1 : ∫ w : ℝ, ((Real.pi * c : ℂ) ^ (Module.finrank ℝ ℝ / 2 : ℂ) *
          Complex.exp (-Real.pi ^ 2 * (c : ℂ) * (‖(0 : ℝ) - w‖ : ℂ) ^ 2)) • hAuto S w =
        ∫ w : ℝ, 𝓕 (fun v : ℝ => Complex.exp (-((c : ℂ)⁻¹) * (‖v‖ : ℂ) ^ 2)) w • hAuto S w := by
      congr 1; funext w; rw [hfg]
    rw [h1]
    have hflip' : ∫ w : ℝ, 𝓕 (fun v : ℝ => Complex.exp (-((c : ℂ)⁻¹) * (‖v‖ : ℂ) ^ 2)) w • hAuto S w =
        ∫ v : ℝ, Complex.exp (-((c : ℂ)⁻¹) * (‖v‖ : ℂ) ^ 2) • 𝓕 (hAuto S) v := by
      have hflipL : (innerₗ ℝ).flip = innerₗ ℝ := by ext a b; simp [real_inner_comm]
      rw [hflipL] at hstep
      exact hstep
    rw [hflip']
    congr 1; funext v
    rw [fourier_hAuto hS_meas hS_vol v, smul_eq_mul]
    congr 1
    rw [Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  -- Extract real part limit
  have hreal_lim : Tendsto (fun c : ℝ => ∫ v : ℝ, Real.exp (-c⁻¹ * v ^ 2) * gFun S v)
      atTop (𝓝 1) := by
    have hre := (Complex.continuous_re.tendsto 1).comp hflip
    simp only [Complex.one_re] at hre
    refine hre.congr' ?_
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    have heq : (fun v : ℝ => Complex.exp (-((c : ℂ)⁻¹) * (v : ℂ) ^ 2) * ((gFun S v : ℝ) : ℂ)) =
        fun v : ℝ => ((Real.exp (-c⁻¹ * v ^ 2) * gFun S v : ℝ) : ℂ) := by
      funext v
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      push_cast; rfl
    rw [Function.comp_apply, heq, integral_complex_ofReal, Complex.ofReal_re]
  -- Monotone convergence along c = n + 1
  let u : ℕ → ℝ → ENNReal := fun n v =>
    ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1)⁻¹) * v ^ 2) * gFun S v)
  have hu_meas : ∀ n, Measurable (u n) := fun n => by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (Continuous.measurable (by fun_prop)).mul (continuous_gFun hS_bdd hS_meas).measurable
  have hu_mono : Monotone u := by
    intro m n hmn v
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (gFun_nonneg S v)
    apply Real.exp_le_exp.mpr
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have hinv : ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹ := inv_anti₀ hm1 hmn'
    have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
    nlinarith
  have hu_sup : (fun v => ⨆ n, u n v) = fun v => ENNReal.ofReal (gFun S v) := by
    funext v
    have hlim_v : Tendsto (fun n : ℕ => u n v) atTop (𝓝 (ENNReal.ofReal (gFun S v))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      have h1 : Tendsto (fun n : ℕ => -(((n : ℝ) + 1)⁻¹) * v ^ 2) atTop (𝓝 0) := by
        have hnat : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using (hnat.neg.mul_const (v ^ 2))
      simpa using (Real.continuous_exp.tendsto 0 |>.comp h1).mul_const (gFun S v)
    exact tendsto_nhds_unique (tendsto_atTop_iSup (fun m n h => hu_mono h v)) hlim_v
  have hlint_eq : ∫⁻ v, ENNReal.ofReal (gFun S v) = 1 := by
    rw [← hu_sup, lintegral_iSup hu_meas hu_mono]
    have hterm_eq : ∀ n : ℕ, ∫⁻ v, u n v =
        ENNReal.ofReal (∫ v : ℝ, Real.exp (-(((n : ℝ) + 1)⁻¹) * v ^ 2) * gFun S v) := by
      intro n
      have hc : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hint_n : Integrable (fun v : ℝ => Real.exp (-(((n : ℝ) + 1)⁻¹) * v ^ 2) * gFun S v) volume := by
        refine (integrable_exp_neg_mul_sq (inv_pos.mpr hc)).mono' ?_ ?_
        · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul
            (continuous_gFun hS_bdd hS_meas).aestronglyMeasurable
        · filter_upwards with v
          rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (gFun_nonneg S v))]
          simpa using mul_le_mul_of_nonneg_left (gFun_le_one hS_vol v) (Real.exp_nonneg _)
      exact (ofReal_integral_eq_lintegral_ofReal hint_n
        (Eventually.of_forall fun v => mul_nonneg (Real.exp_nonneg _) (gFun_nonneg S v))).symm
    simp_rw [hterm_eq]
    have hnat_lim : Tendsto (fun n : ℕ =>
        ENNReal.ofReal (∫ v : ℝ, Real.exp (-(((n : ℝ) + 1)⁻¹) * v ^ 2) * gFun S v))
        atTop (𝓝 1) := by
      have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have h2 := (ENNReal.continuous_ofReal.tendsto 1).comp (hreal_lim.comp h1)
      simpa [Function.comp_def, neg_mul] using h2
    have hmono_int : Monotone (fun n : ℕ =>
        ENNReal.ofReal (∫ v : ℝ, Real.exp (-(((n : ℝ) + 1)⁻¹) * v ^ 2) * gFun S v)) := by
      intro m n hmn
      dsimp only
      rw [← hterm_eq m, ← hterm_eq n]
      exact lintegral_mono (hu_mono hmn)
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono_int) hnat_lim
  have hg_int : Integrable (gFun S) volume := by
    refine ⟨(continuous_gFun hS_bdd hS_meas).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have heq : (fun v => ‖gFun S v‖ₑ) = fun v => ENNReal.ofReal (gFun S v) := by
      funext v
      rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (gFun_nonneg S v)]
    rw [heq, hlint_eq]
    exact ENNReal.one_lt_top
  refine ⟨hg_int, ?_⟩
  have hofReal := ofReal_integral_eq_lintegral_ofReal hg_int
    (Eventually.of_forall (gFun_nonneg S))
  rw [hlint_eq] at hofReal
  have hnn : 0 ≤ ∫ ξ, gFun S ξ := integral_nonneg (gFun_nonneg S)
  have h1 := congrArg ENNReal.toReal hofReal
  simpa [ENNReal.toReal_ofReal hnn] using h1

lemma fourier_gFun_eq_hAuto {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (y : ℝ) :
    𝓕 (fun ξ : ℝ => ((gFun S ξ : ℝ) : ℂ)) y = hAuto S y := by
  have hg_int := (integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol).1
  have hFh_eq : 𝓕 (hAuto S) = fun ξ => ((gFun S ξ : ℝ) : ℂ) := by
    funext ξ; exact fourier_hAuto hS_meas hS_vol ξ
  have hFh_int : Integrable (𝓕 (hAuto S)) volume := by
    rw [hFh_eq]; exact hg_int.ofReal
  have hinv := (continuous_hAuto hS_meas hS_vol).fourierInv_fourier_eq
    (integrable_hAuto hS_meas hS_vol) hFh_int
  have hinv_y : 𝓕⁻ (fun ξ : ℝ => ((gFun S ξ : ℝ) : ℂ)) y = hAuto S y := by
    rw [← hFh_eq]; exact congrFun hinv y
  rw [← hinv_y, Real.fourierInv_eq_fourier_neg, fourier_real_eq, fourier_real_eq]
  rw [← integral_comp_neg_real (fun v =>
    Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * ((-y : ℝ) : ℂ)) * ((gFun S v : ℝ) : ℂ))]
  congr 1; funext v
  rw [gFun_even]
  congr 1; push_cast; ring

lemma interval_tiling_identity {S Λ : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1)
    (hΛ_cnt : Λ.Countable)
    (htile : ∀ t : ℝ, HasSum (fun lam : Λ => gFun S (t - lam.1)) 1)
    (a L : ℝ) (hL : 0 < L) :
    ∑' lam : Λ, ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t = L := by
  haveI : Countable Λ := hΛ_cnt.to_subtype
  have hg_int : Integrable (gFun S) volume := (integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol).1
  have hg_cont : Continuous (gFun S) := continuous_gFun hS_bdd hS_meas
  have hlint : ∫⁻ x in Set.Icc a (a + L), (1 : ENNReal) = ENNReal.ofReal L := by
    simp [Real.volume_Icc, hL.le]
  have hsum_en : ∀ x : ℝ, (1 : ENNReal) = ∑' lam : Λ, ENNReal.ofReal (gFun S (x - lam.1)) := by
    intro x
    have hs := htile x
    have hnn : ∀ lam : Λ, 0 ≤ gFun S (x - lam.1) := fun lam => gFun_nonneg S _
    rw [← ENNReal.ofReal_one, ← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg hnn hs.summable]
  have hton : ENNReal.ofReal L =
      ∑' lam : Λ, ∫⁻ x in Set.Icc a (a + L), ENNReal.ofReal (gFun S (x - lam.1)) := by
    rw [← hlint]
    calc
      ∫⁻ x in Set.Icc a (a + L), (1 : ENNReal)
          = ∫⁻ x in Set.Icc a (a + L), ∑' lam : Λ, ENNReal.ofReal (gFun S (x - lam.1)) := by
            congr 1; funext x; exact hsum_en x
      _ = ∑' lam : Λ, ∫⁻ x in Set.Icc a (a + L), ENNReal.ofReal (gFun S (x - lam.1)) := by
            refine lintegral_tsum fun lam => ?_
            exact (ENNReal.measurable_ofReal.comp
              (hg_cont.measurable.comp (measurable_id.sub measurable_const))).aemeasurable
  have hterm : ∀ lam : Λ,
      ∫⁻ x in Set.Icc a (a + L), ENNReal.ofReal (gFun S (x - lam.1)) =
        ENNReal.ofReal (∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t) := by
    intro lam
    have h1 : ∫⁻ x in Set.Icc a (a + L), ENNReal.ofReal (gFun S (x - lam.1)) =
        ENNReal.ofReal (∫ x in Set.Icc a (a + L), gFun S (x - lam.1)) := by
      refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun _ => gFun_nonneg S _)).symm
      exact (hg_int.comp_sub_right lam.1).integrableOn
    rw [h1]
    congr 1
    -- Direct change of variables via integral_sub_right_eq_self on indicator
    rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc]
    rw [← integral_sub_right_eq_self
      (fun t => (Set.Icc (a - lam.1) (a + L - lam.1)).indicator (gFun S) t) lam.1]
    congr 1; funext x
    by_cases hx : x ∈ Set.Icc a (a + L)
    · have hx' : x - lam.1 ∈ Set.Icc (a - lam.1) (a + L - lam.1) :=
        ⟨sub_le_sub_right hx.1 _, sub_le_sub_right hx.2 _⟩
      simp [hx, hx']
    · have hx' : x - lam.1 ∉ Set.Icc (a - lam.1) (a + L - lam.1) := fun h =>
        hx ⟨by linarith [h.1], by linarith [h.2]⟩
      simp [hx, hx']
  simp_rw [hterm] at hton
  have hsummable : Summable (fun lam : Λ => ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t) := by
    have hlt : ∑' lam : Λ, ENNReal.ofReal (∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t) ≠ ⊤ := by
      rw [← hton]; exact ENNReal.ofReal_ne_top
    exact (ENNReal.summable_toReal hlt).congr fun lam =>
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc fun _ _ => gFun_nonneg S _)
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun lam => setIntegral_nonneg measurableSet_Icc fun _ _ => gFun_nonneg S _) hsummable] at hton
  have hnn : 0 ≤ ∑' lam : Λ, ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t :=
    tsum_nonneg fun lam => setIntegral_nonneg measurableSet_Icc fun _ _ => gFun_nonneg S _
  have hres := congrArg ENNReal.toReal hton
  simpa [ENNReal.toReal_ofReal hL.le, ENNReal.toReal_ofReal hnn] using hres.symm

lemma exists_tail_integral_lt {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ M > 0, ∫ t in {t : ℝ | M < |t|}, gFun S t < ε := by
  have hg_int := (integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol).1
  have hlim : Tendsto (fun n : ℕ => ∫ t, ({t : ℝ | (n : ℝ) + 1 < |t|}).indicator (gFun S) t)
      atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _t : ℝ, (0 : ℝ) := by simp
    conv_rhs => rw [h0]
    refine tendsto_integral_of_dominated_convergence (gFun S) ?_ hg_int ?_ ?_
    · intro n
      refine hg_int.aestronglyMeasurable.indicator ?_
      exact measurableSet_lt measurable_const continuous_abs.measurable
    · intro n
      filter_upwards with t
      by_cases ht : t ∈ {t : ℝ | (n : ℝ) + 1 < |t|}
      · rw [Set.indicator_of_mem ht, Real.norm_of_nonneg (gFun_nonneg S t)]
      · rw [Set.indicator_of_notMem ht, norm_zero]; exact gFun_nonneg S t
    · filter_upwards with t
      obtain ⟨N, hN⟩ := exists_nat_ge |t|
      refine tendsto_atTop_of_eventually_const (i₀ := N) fun n hn => ?_
      have hnot : t ∉ {t : ℝ | (n : ℝ) + 1 < |t|} := by
        simp only [Set.mem_setOf_eq, not_lt]
        have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact Set.indicator_of_notMem hnot _
  rw [Metric.tendsto_nhds] at hlim
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim ε hε)
  refine ⟨(N : ℝ) + 1, by positivity, ?_⟩
  have hlt := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hlt
  have hmeas : MeasurableSet {t : ℝ | (N : ℝ) + 1 < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [integral_indicator hmeas] at hlt
  rw [abs_of_nonneg (setIntegral_nonneg hmeas fun _ _ => gFun_nonneg S _)] at hlt
  exact hlt

lemma tiling_card_bounds {S Λ : Set ℝ} {δ : ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (hδ : 0 < δ)
    (hsep : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → δ ≤ |x - y|)
    (htile : ∀ t : ℝ, HasSum (fun lam : Λ => gFun S (t - lam.1)) 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ M > 0, ∀ a L : ℝ, 0 < L →
      (1 - ε) * ((Λ ∩ Set.Icc (a + M) (a + L - M)).ncard : ℝ) ≤ L ∧
      L ≤ ((Λ ∩ Set.Icc (a - M) (a + L + M)).ncard : ℝ) + (L / δ + 1) * ε := by
  have hΛ_cnt : Λ.Countable := separated_countable hδ hsep
  haveI : Countable Λ := hΛ_cnt.to_subtype
  have ⟨hg_int, hg_one⟩ := integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol
  obtain ⟨M, hM_pos, htail⟩ := exists_tail_integral_lt hS_bdd hS_meas hS_vol hε
  refine ⟨M, hM_pos, fun a L hL => ?_⟩
  have hid := interval_tiling_identity hS_bdd hS_meas hS_vol hΛ_cnt htile a L hL
  have hsummable : Summable (fun lam : Λ => ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t) := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at hid
    linarith
  have hterm_nn : ∀ lam : Λ, 0 ≤ ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t :=
    fun lam => setIntegral_nonneg measurableSet_Icc fun _ _ => gFun_nonneg S _
  -- Inner mass on [-M, M] is > 1 - ε
  have hinner_mass : 1 - ε ≤ ∫ t in Set.Icc (-M) M, gFun S t := by
    have hcompl : {t : ℝ | M < |t|} = (Set.Icc (-M) M)ᶜ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le]
      constructor
      · intro h
        rcases lt_abs.mp h with h1 | h1
        · right; exact h1
        · left; linarith
      · rintro (h | h)
        · exact lt_abs.mpr (Or.inr (by linarith))
        · exact lt_abs.mpr (Or.inl h)
    have hadd := integral_add_compl (s := Set.Icc (-M) M) measurableSet_Icc hg_int
    rw [← hcompl, hg_one] at hadd
    linarith
  constructor
  · -- Upper bound on interior points
    have hfin := (separated_inter_Icc_finite_and_card_le hδ hsep (a + M) (a + L - M)).1
    let Fset : Finset Λ :=
      (hfin.toFinset.attach.image fun x =>
        ⟨x.1, ((hfin.mem_toFinset).mp x.2).1⟩)
    have hF_card : Fset.card = (Λ ∩ Set.Icc (a + M) (a + L - M)).ncard := by
      have hinj : Function.Injective (fun x : {y // y ∈ hfin.toFinset} =>
          (⟨x.1, ((hfin.mem_toFinset).mp x.2).1⟩ : Λ)) := by
        intro x y h; apply Subtype.ext; exact congrArg (fun z : Λ => z.1) h
      rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, Set.ncard_eq_toFinset_card _ hfin]
    have hsum_le : ∑ lam ∈ Fset, ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t ≤ L :=
      le_trans (hsummable.sum_le_tsum Fset (fun lam _ => hterm_nn lam)) hid.le
    have hsum_ge : (1 - ε) * (Fset.card : ℝ) ≤
        ∑ lam ∈ Fset, ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t := by
      calc
        (1 - ε) * (Fset.card : ℝ) = ∑ _lam ∈ Fset, (1 - ε) := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ lam ∈ Fset, ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t := by
          apply Finset.sum_le_sum
          intro lam hl
          rcases Finset.mem_image.mp hl with ⟨⟨x, hx⟩, _, hxeq⟩
          have hx_mem := (hfin.mem_toFinset).mp hx
          have hl_eq : lam.1 = x := congrArg Subtype.val hxeq.symm
          rw [hl_eq]
          have hsub : Set.Icc (-M) M ⊆ Set.Icc (a - x) (a + L - x) := by
            intro t ht
            exact ⟨by linarith [ht.1, hx_mem.2.1], by linarith [ht.2, hx_mem.2.2]⟩
          exact le_trans hinner_mass (setIntegral_mono_set hg_int.integrableOn
            (Eventually.of_forall fun _ => gFun_nonneg S _) hsub.eventuallyLE)
    rw [hF_card] at hsum_ge
    linarith
  · -- Lower bound via splitting into inside [a-M, a+L+M] and outside
    have hfin := (separated_inter_Icc_finite_and_card_le hδ hsep (a - M) (a + L + M)).1
    obtain ⟨Gset, hG_mem, hG_card⟩ : ∃ Gset : Finset Λ,
        (∀ lam : Λ, lam.1 ∈ Set.Icc (a - M) (a + L + M) → lam ∈ Gset) ∧
        Gset.card = (Λ ∩ Set.Icc (a - M) (a + L + M)).ncard := by
      refine ⟨hfin.toFinset.attach.image fun x => ⟨x.1, ((hfin.mem_toFinset).mp x.2).1⟩, ?_, ?_⟩
      · intro lam hmem
        have hx : lam.1 ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨lam.2, hmem⟩
        exact Finset.mem_image.mpr ⟨⟨lam.1, hx⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
      · have hinj : Function.Injective (fun x : {y // y ∈ hfin.toFinset} =>
            (⟨x.1, ((hfin.mem_toFinset).mp x.2).1⟩ : Λ)) := by
          intro x y h; apply Subtype.ext; exact congrArg (fun z : Λ => z.1) h
        rw [Finset.card_image_of_injective _ hinj, Finset.card_attach, Set.ncard_eq_toFinset_card _ hfin]
    have hsplit := hsummable.sum_add_tsum_compl (s := Gset)
    rw [hid] at hsplit
    have hinside : ∑ lam ∈ Gset, ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t ≤
        (Gset.card : ℝ) := by
      calc
        ∑ lam ∈ Gset, ∫ t in Set.Icc (a - lam.1) (a + L - lam.1), gFun S t
            ≤ ∑ _lam ∈ Gset, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro lam _
              rw [← hg_one]
              exact setIntegral_le_integral hg_int (Eventually.of_forall (gFun_nonneg S))
        _ = (Gset.card : ℝ) := by simp
    -- Bound tail sum over lam ∉ Gset by Tonelli
    have htail_sum :
        ∑' lam : ↥(Gset : Set Λ)ᶜ, ∫ t in Set.Icc (a - lam.1.1) (a + L - lam.1.1), gFun S t ≤
          (L / δ + 1) * ε := by
      have hK_le : ((Nat.floor (L / δ) + 1 : ℕ) : ℝ) ≤ L / δ + 1 := by
        push_cast
        have := Nat.floor_le (div_nonneg hL.le hδ.le)
        linarith
      -- Rewrite as lintegral and bound pointwise multiplicity
      have hmeas_tail : MeasurableSet {t : ℝ | M < |t|} :=
        measurableSet_lt measurable_const continuous_abs.measurable
      have hterm_tail : ∀ lam : ↥(Gset : Set Λ)ᶜ,
          ∫⁻ t, ENNReal.ofReal
            ((Set.Icc (a - lam.1.1) (a + L - lam.1.1)).indicator (gFun S) t) =
          ENNReal.ofReal (∫ t in Set.Icc (a - lam.1.1) (a + L - lam.1.1), gFun S t) := by
        intro lam
        rw [← ofReal_integral_eq_lintegral_ofReal (hg_int.indicator measurableSet_Icc)
          (Eventually.of_forall fun t => Set.indicator_nonneg (fun _ _ => gFun_nonneg S _) t)]
        rw [integral_indicator measurableSet_Icc]
      have hnot_in : ∀ lam : ↥(Gset : Set Λ)ᶜ, lam.1.1 ∉ Set.Icc (a - M) (a + L + M) :=
        fun lam hmem => lam.2 (hG_mem lam.1 hmem)
      have hpt_le : ∀ t : ℝ,
          ∑' lam : ↥(Gset : Set Λ)ᶜ,
            ENNReal.ofReal ((Set.Icc (a - lam.1.1) (a + L - lam.1.1)).indicator (gFun S) t) ≤
          ENNReal.ofReal ((L / δ + 1) * ({t : ℝ | M < |t|}).indicator (gFun S) t) := by
        intro t
        by_cases ht : M < |t|
        · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | M < |t|} from ht)]
          -- Count how many lam ∈ Λ have t ∈ [a - lam, a + L - lam], i.e., lam ∈ [a - t, a + L - t]
          have hfin_t := separated_inter_Icc_finite_and_card_le hδ hsep (a - t) (a + L - t)
          have hTt_fin : ({lam : ↥(Gset : Set Λ)ᶜ | lam.1.1 ∈ Set.Icc (a - t) (a + L - t)}).Finite := by
            have hsub : {lam : ↥(Gset : Set Λ)ᶜ | lam.1.1 ∈ Set.Icc (a - t) (a + L - t)} ⊆
                (fun lam : ↥(Gset : Set Λ)ᶜ => lam.1.1) ⁻¹' (Λ ∩ Set.Icc (a - t) (a + L - t)) :=
              fun lam hlam => ⟨lam.1.2, hlam⟩
            exact (hfin_t.1.preimage (f := fun lam : ↥(Gset : Set Λ)ᶜ => lam.1.1)
              (fun x _ y _ h => Subtype.ext (Subtype.ext h))).subset hsub
          let S_t : Finset ↥(Gset : Set Λ)ᶜ := hTt_fin.toFinset
          have hsupp : ∀ lam : ↥(Gset : Set Λ)ᶜ, lam ∉ S_t →
              ENNReal.ofReal ((Set.Icc (a - lam.1.1) (a + L - lam.1.1)).indicator (gFun S) t) = 0 := by
            intro lam hl
            have hnotIcc : t ∉ Set.Icc (a - lam.1.1) (a + L - lam.1.1) := by
              intro hI
              have hmem_St : lam ∈ S_t := hTt_fin.mem_toFinset.mpr ⟨by linarith [hI.1], by linarith [hI.2]⟩
              exact hl hmem_St
            rw [Set.indicator_of_notMem hnotIcc, ENNReal.ofReal_zero]
          rw [tsum_eq_sum hsupp]
          have hSt_card : (S_t.card : ℝ) ≤ L / δ + 1 := by
            have h1 : S_t.card ≤ hfin_t.1.toFinset.card := by
              have hinj : Function.Injective (fun lam : ↥(Gset : Set Λ)ᶜ => lam.1.1) :=
                fun x y h => Subtype.ext (Subtype.ext h)
              rw [← Finset.card_image_of_injective S_t hinj]
              refine Finset.card_le_card fun r hr => ?_
              rcases Finset.mem_image.mp hr with ⟨lam, hlam, rfl⟩
              exact hfin_t.1.mem_toFinset.mpr ⟨lam.1.2, hTt_fin.mem_toFinset.mp hlam⟩
            have h2 : hfin_t.1.toFinset.card ≤ Nat.floor (L / δ) + 1 := by
              have hmax : max 0 ((a + L - t) - (a - t)) = L := by
                have : (a + L - t) - (a - t) = L := by ring
                rw [this, max_eq_right hL.le]
              have hcard := hfin_t.2
              rw [hmax, Set.ncard_eq_toFinset_card _ hfin_t.1] at hcard
              exact hcard
            have h3 : (S_t.card : ℝ) ≤ ((Nat.floor (L / δ) + 1 : ℕ) : ℝ) := by
              exact_mod_cast le_trans h1 h2
            exact le_trans h3 hK_le
          calc
            ∑ lam ∈ S_t, ENNReal.ofReal ((Set.Icc (a - lam.1.1) (a + L - lam.1.1)).indicator (gFun S) t)
                ≤ ∑ _lam ∈ S_t, ENNReal.ofReal (gFun S t) := by
                  apply Finset.sum_le_sum
                  intro lam _
                  apply ENNReal.ofReal_le_ofReal
                  by_cases h : t ∈ Set.Icc (a - lam.1.1) (a + L - lam.1.1)
                  · rw [Set.indicator_of_mem h]
                  · rw [Set.indicator_of_notMem h]; exact gFun_nonneg S t
            _ = (S_t.card : ENNReal) * ENNReal.ofReal (gFun S t) := by simp
            _ = ENNReal.ofReal ((S_t.card : ℝ) * gFun S t) := by
                  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
            _ ≤ ENNReal.ofReal ((L / δ + 1) * gFun S t) := by
                  apply ENNReal.ofReal_le_ofReal
                  exact mul_le_mul_of_nonneg_right hSt_card (gFun_nonneg S t)
        · -- If |t| ≤ M, then no lam ∉ [a - M, a + L + M] can satisfy t ∈ [a - lam, a + L - lam]
          have hall0 : ∀ lam : ↥(Gset : Set Λ)ᶜ,
              ENNReal.ofReal ((Set.Icc (a - lam.1.1) (a + L - lam.1.1)).indicator (gFun S) t) = 0 := by
            intro lam
            have hnotI : t ∉ Set.Icc (a - lam.1.1) (a + L - lam.1.1) := by
              intro hI
              have htle : |t| ≤ M := le_of_not_gt ht
              have ⟨ht1, ht2⟩ := abs_le.mp htle
              exact hnot_in lam ⟨by linarith [hI.1], by linarith [hI.2]⟩
            rw [Set.indicator_of_notMem hnotI, ENNReal.ofReal_zero]
          simp_rw [hall0, tsum_zero]
          exact bot_le
      -- Integrate pointwise bound via lintegral_tsum
      have hton_tail :
          ∑' lam : ↥(Gset : Set Λ)ᶜ,
            ENNReal.ofReal (∫ t in Set.Icc (a - lam.1.1) (a + L - lam.1.1), gFun S t) ≤
          ENNReal.ofReal ((L / δ + 1) * ∫ t in {t : ℝ | M < |t|}, gFun S t) := by
        simp_rw [← hterm_tail]
        have hmeas_lam : ∀ lam : ↥(Gset : Set Λ)ᶜ,
            AEMeasurable (fun t : ℝ => ENNReal.ofReal
              ((Set.Icc (a - lam.1.1) (a + L - lam.1.1)).indicator (gFun S) t)) volume := fun lam =>
          (ENNReal.measurable_ofReal.comp
            ((continuous_gFun hS_bdd hS_meas).measurable.indicator measurableSet_Icc)).aemeasurable
        rw [← lintegral_tsum hmeas_lam]
        calc
          ∫⁻ t, ∑' lam : ↥(Gset : Set Λ)ᶜ,
              ENNReal.ofReal ((Set.Icc (a - lam.1.1) (a + L - lam.1.1)).indicator (gFun S) t)
              ≤ ∫⁻ t, ENNReal.ofReal ((L / δ + 1) * ({t : ℝ | M < |t|}).indicator (gFun S) t) :=
                lintegral_mono hpt_le
          _ = ENNReal.ofReal (∫ t, (L / δ + 1) * ({t : ℝ | M < |t|}).indicator (gFun S) t) := by
                refine (ofReal_integral_eq_lintegral_ofReal
                  ((hg_int.indicator hmeas_tail).const_mul (L / δ + 1)) ?_).symm
                filter_upwards with t
                exact mul_nonneg (by positivity)
                  (Set.indicator_nonneg (fun _ _ => gFun_nonneg S _) t)
          _ = ENNReal.ofReal ((L / δ + 1) * ∫ t in {t : ℝ | M < |t|}, gFun S t) := by
                rw [integral_const_mul, integral_indicator hmeas_tail]
      have hsumm_tail : Summable (fun lam : ↥(Gset : Set Λ)ᶜ =>
          ∫ t in Set.Icc (a - lam.1.1) (a + L - lam.1.1), gFun S t) :=
        hsummable.subtype _
      have htail_nn : ∀ lam : ↥(Gset : Set Λ)ᶜ,
          0 ≤ ∫ t in Set.Icc (a - lam.1.1) (a + L - lam.1.1), gFun S t := fun lam => hterm_nn lam.1
      rw [← ENNReal.ofReal_tsum_of_nonneg htail_nn hsumm_tail] at hton_tail
      have hle_real := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by positivity)
        (setIntegral_nonneg hmeas_tail fun _ _ => gFun_nonneg S _))).mp hton_tail
      have hpos_coef : 0 < L / δ + 1 := by positivity
      exact le_trans hle_real (mul_le_mul_of_nonneg_left htail.le hpos_coef.le)
    rw [← hG_card]
    linarith

lemma exists_bounded_gaps {S Λ : Set ℝ} {δ : ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (hδ : 0 < δ)
    (hsep : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → δ ≤ |x - y|)
    (htile : ∀ t : ℝ, HasSum (fun lam : Λ => gFun S (t - lam.1)) 1) :
    ∃ Δ > 0, δ ≤ Δ ∧ ∀ a : ℝ, (Λ ∩ Set.Ioc a (a + Δ)).Nonempty := by
  obtain ⟨M, hM_pos, hbounds⟩ :=
    tiling_card_bounds hS_bdd hS_meas hS_vol hδ hsep htile (ε := δ / 4) (by linarith)
  refine ⟨2 * M + δ + 1, by positivity, by linarith, fun a => ?_⟩
  have hlow := (hbounds (a + M + 1 / 2) δ hδ).2
  have hcalc : (δ / δ + 1) * (δ / 4) = δ / 2 := by
    field_simp [hδ.ne']
    ring
  rw [hcalc] at hlow
  have hcard_pos : (0 : ℝ) < ((Λ ∩ Set.Icc (a + M + 1 / 2 - M) (a + M + 1 / 2 + δ + M)).ncard : ℝ) := by
    linarith
  have hncard_ne : (Λ ∩ Set.Icc (a + 1 / 2) (a + 2 * M + δ + 1 / 2)).ncard ≠ 0 := by
    intro h0
    have hset : Set.Icc (a + M + 1 / 2 - M) (a + M + 1 / 2 + δ + M) =
        Set.Icc (a + 1 / 2) (a + 2 * M + δ + 1 / 2) := by congr 1 <;> ring
    rw [hset, h0, Nat.cast_zero] at hcard_pos
    exact lt_irrefl 0 hcard_pos
  obtain ⟨x, hxΛ, hxIcc⟩ := Set.nonempty_of_ncard_ne_zero hncard_ne
  exact ⟨x, hxΛ, by linarith [hxIcc.1], by linarith [hxIcc.2]⟩

lemma period_eq_card_Ico {S Λ : Set ℝ} {δ T : ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (hδ : 0 < δ)
    (hsep : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → δ ≤ |x - y|)
    (htile : ∀ t : ℝ, HasSum (fun lam : Λ => gFun S (t - lam.1)) 1)
    (hT : 0 < T) (hper : ∀ x, x ∈ Λ ↔ x + T ∈ Λ) :
    ((Λ ∩ Set.Ico 0 T).ncard : ℝ) = T := by
  set p : ℕ := (Λ ∩ Set.Ico 0 T).ncard
  have hper_int : ∀ (m : ℤ) (x : ℝ), x ∈ Λ ↔ x + (m : ℝ) * T ∈ Λ := by
    intro m
    induction m using Int.induction_on with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have h1 : x + (((k : ℤ) + 1 : ℤ) : ℝ) * T = (x + ((k : ℤ) : ℝ) * T) + T := by push_cast; ring
      rw [h1, ← hper, ← ih]
    | pred k ih =>
      intro x
      have h1 : x + (((-(k : ℤ) - 1 : ℤ) : ℝ) * T) + T = x + ((-(k : ℤ) : ℤ) : ℝ) * T := by
        push_cast; ring
      rw [hper (x + ((-(k : ℤ) - 1 : ℤ) : ℝ) * T), h1, ← ih]
  have hcard_mul : ∀ k : ℕ, (Λ ∩ Set.Ico 0 ((k : ℝ) * T)).ncard = k * p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hsplit : Λ ∩ Set.Ico 0 (((k + 1 : ℕ) : ℝ) * T) =
          (Λ ∩ Set.Ico 0 ((k : ℝ) * T)) ∪ (Λ ∩ Set.Ico ((k : ℝ) * T) (((k + 1 : ℕ) : ℝ) * T)) := by
        ext x
        simp only [mem_inter_iff, mem_union, mem_Ico]
        constructor
        · rintro ⟨hx, h0, hlt⟩
          by_cases h : x < (k : ℝ) * T
          · left; exact ⟨hx, h0, h⟩
          · right; exact ⟨hx, le_of_not_gt h, hlt⟩
        · rintro (⟨hx, h0, hlt⟩ | ⟨hx, hge, hlt⟩)
          · exact ⟨hx, h0, lt_trans hlt (by push_cast; nlinarith)⟩
          · exact ⟨hx, le_trans (by positivity) hge, hlt⟩
      have hdisj : Disjoint (Λ ∩ Set.Ico 0 ((k : ℝ) * T))
          (Λ ∩ Set.Ico ((k : ℝ) * T) (((k + 1 : ℕ) : ℝ) * T)) := by
        rw [Set.disjoint_left]
        rintro x ⟨_, _, hlt⟩ ⟨_, hge, _⟩
        linarith
      have hfin1 : (Λ ∩ Set.Ico 0 ((k : ℝ) * T)).Finite :=
        ((separated_inter_Icc_finite_and_card_le hδ hsep 0 ((k : ℝ) * T)).1).subset
          (Set.inter_subset_inter_right _ Set.Ico_subset_Icc_self)
      have hfin2 : (Λ ∩ Set.Ico ((k : ℝ) * T) (((k + 1 : ℕ) : ℝ) * T)).Finite :=
        ((separated_inter_Icc_finite_and_card_le hδ hsep ((k : ℝ) * T) (((k + 1 : ℕ) : ℝ) * T)).1).subset
          (Set.inter_subset_inter_right _ Set.Ico_subset_Icc_self)
      have hbij : (Λ ∩ Set.Ico ((k : ℝ) * T) (((k + 1 : ℕ) : ℝ) * T)).ncard = p := by
        have himg : (fun x => x + (k : ℝ) * T) '' (Λ ∩ Set.Ico 0 T) =
            Λ ∩ Set.Ico ((k : ℝ) * T) (((k + 1 : ℕ) : ℝ) * T) := by
          ext y
          simp only [mem_image, mem_inter_iff, mem_Ico]
          constructor
          · rintro ⟨x, ⟨hx, h0, hlt⟩, rfl⟩
            refine ⟨(hper_int k x).mp (by simpa using hx), by linarith, by push_cast; linarith⟩
          · rintro ⟨hy, hge, hlt⟩
            refine ⟨y - (k : ℝ) * T, ⟨?_, by linarith, by push_cast at hlt; linarith⟩, by ring⟩
            have := (hper_int k (y - (k : ℝ) * T)).mpr (by simpa [sub_add_cancel] using hy)
            exact this
        rw [← himg, Set.ncard_image_of_injective _ (add_left_injective _)]
      rw [hsplit, Set.ncard_union_eq hdisj hfin1 hfin2, ih, hbij]
      ring
  -- Show both p ≤ T and T ≤ p using arbitrary ε ∈ (0, 1/2)
  have hle : (p : ℝ) ≤ T := by
    by_contra hgt; push Not at hgt
    set ε : ℝ := min (1 / 2) ((p - T) / (2 * (p : ℝ)))
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have hε : 0 < ε := lt_min (by norm_num) (div_pos (by linarith) (by linarith))
    have hε_lt1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    obtain ⟨M, hM_pos, hbounds⟩ :=
      tiling_card_bounds hS_bdd hS_meas hS_vol hδ hsep htile hε
    set C : ℕ := Nat.floor (M / δ) + 1
    have hC_bound : ∀ u : ℝ, (Λ ∩ Set.Icc u (u + M)).ncard ≤ C := by
      intro u
      have h1 := (separated_inter_Icc_finite_and_card_le hδ hsep u (u + M)).2
      simpa [add_sub_cancel_left, max_eq_right hM_pos.le, C] using h1
    -- Pick k large enough
    obtain ⟨k, hk⟩ := exists_nat_gt ((2 * (C : ℝ) + 1) / ((1 - ε) * (p : ℝ) - T) + 2 * M / T + 1)
    have h1ep : T < (1 - ε) * (p : ℝ) := by
      have hε_le : ε ≤ (p - T) / (2 * (p : ℝ)) := min_le_right _ _
      have hmul : ε * (p : ℝ) ≤ (p - T) / 2 := by
        have h1 := mul_le_mul_of_nonneg_right hε_le hp_pos.le
        have h2 : ((p : ℝ) - T) / (2 * (p : ℝ)) * (p : ℝ) = ((p : ℝ) - T) / 2 := by
          field_simp [hp_pos.ne']
        linarith
      linarith
    have hk_pos : 0 < k := by
      have hden : 0 < (1 - ε) * (p : ℝ) - T := by linarith
      have hpos_rhs : 0 < (2 * (C : ℝ) + 1) / ((1 - ε) * (p : ℝ) - T) + 2 * M / T + 1 := by
        positivity
      have : (0 : ℝ) < (k : ℝ) := lt_trans hpos_rhs hk
      exact_mod_cast this
    have hkT_pos : 0 < (k : ℝ) * T := by positivity
    have hup := (hbounds 0 ((k : ℝ) * T) hkT_pos).1
    simp only [zero_add] at hup
    -- Relate k*p = |Λ ∩ [0, kT)| to |Λ ∩ [M, kT - M]| + 2C
    have hsub : Λ ∩ Set.Ico 0 ((k : ℝ) * T) ⊆
        (Λ ∩ Set.Icc 0 (0 + M)) ∪
        ((Λ ∩ Set.Icc M ((k : ℝ) * T - M)) ∪ (Λ ∩ Set.Icc ((k : ℝ) * T - M) ((k : ℝ) * T - M + M))) := by
      intro x ⟨hx, h0, hlt⟩
      by_cases h1 : x ≤ M
      · left; exact ⟨hx, h0, by linarith⟩
      · right
        by_cases h2 : x ≤ (k : ℝ) * T - M
        · left; exact ⟨hx, by linarith, h2⟩
        · right; exact ⟨hx, by linarith, by linarith⟩
    have hf1 := (separated_inter_Icc_finite_and_card_le hδ hsep 0 (0 + M)).1
    have hf2 := (separated_inter_Icc_finite_and_card_le hδ hsep M ((k : ℝ) * T - M)).1
    have hf3 := (separated_inter_Icc_finite_and_card_le hδ hsep ((k : ℝ) * T - M) ((k : ℝ) * T - M + M)).1
    have hcard_le : k * p ≤ (Λ ∩ Set.Icc M ((k : ℝ) * T - M)).ncard + 2 * C := by
      rw [← hcard_mul k]
      have h1 := Set.ncard_le_ncard hsub (hf1.union (hf2.union hf3))
      have h2 := Set.ncard_union_le (Λ ∩ Set.Icc 0 (0 + M))
        ((Λ ∩ Set.Icc M ((k : ℝ) * T - M)) ∪ (Λ ∩ Set.Icc ((k : ℝ) * T - M) ((k : ℝ) * T - M + M)))
      have h3 := Set.ncard_union_le (Λ ∩ Set.Icc M ((k : ℝ) * T - M))
        (Λ ∩ Set.Icc ((k : ℝ) * T - M) ((k : ℝ) * T - M + M))
      have hc1 := hC_bound 0
      have hc3 := hC_bound ((k : ℝ) * T - M)
      omega
    have hcard_leR : (k : ℝ) * (p : ℝ) ≤
        ((Λ ∩ Set.Icc M ((k : ℝ) * T - M)).ncard : ℝ) + 2 * (C : ℝ) := by
      exact_mod_cast hcard_le
    have hcomb : (1 - ε) * ((k : ℝ) * (p : ℝ) - 2 * (C : ℝ)) ≤ (k : ℝ) * T := by
      have h1 : (k : ℝ) * (p : ℝ) - 2 * (C : ℝ) ≤ ((Λ ∩ Set.Icc M ((k : ℝ) * T - M)).ncard : ℝ) := by
        linarith
      exact le_trans (mul_le_mul_of_nonneg_left h1 (by linarith)) hup
    have hden : 0 < (1 - ε) * (p : ℝ) - T := by linarith
    have hk_gt : (2 * (C : ℝ) + 1) / ((1 - ε) * (p : ℝ) - T) < (k : ℝ) := by
      have : 0 ≤ 2 * M / T + 1 := by positivity
      linarith
    have hk_mul : 2 * (C : ℝ) + 1 < (k : ℝ) * ((1 - ε) * (p : ℝ) - T) :=
      (div_lt_iff₀ hden).mp hk_gt
    have h2C : (1 - ε) * (2 * (C : ℝ)) ≤ 2 * (C : ℝ) := by
      have : 0 ≤ 2 * (C : ℝ) := by positivity
      nlinarith
    nlinarith
  have hge : T ≤ (p : ℝ) := by
    by_contra hlt; push Not at hlt
    set ε : ℝ := (T - (p : ℝ)) / (2 * (T / δ + 1))
    have hε : 0 < ε := div_pos (by linarith) (by positivity)
    obtain ⟨M, hM_pos, hbounds⟩ :=
      tiling_card_bounds hS_bdd hS_meas hS_vol hδ hsep htile hε
    set C : ℕ := Nat.floor (M / δ) + 1
    have hC_bound : ∀ u : ℝ, (Λ ∩ Set.Icc u (u + M)).ncard ≤ C := by
      intro u
      have h1 := (separated_inter_Icc_finite_and_card_le hδ hsep u (u + M)).2
      simpa [add_sub_cancel_left, max_eq_right hM_pos.le, C] using h1
    have hgap : (0 : ℝ) < T - (p : ℝ) - (T / δ) * ε := by
      have h1 : (T / δ) * ε ≤ (T / δ + 1) * ε := by nlinarith
      have h2 : (T / δ + 1) * ε = (T - (p : ℝ)) / 2 := by
        unfold ε
        field_simp [show (T / δ + 1 : ℝ) ≠ 0 by positivity]
      linarith
    obtain ⟨k, hk⟩ := exists_nat_gt ((2 * (C : ℝ) + ε + 1) / (T - (p : ℝ) - (T / δ) * ε) + 1)
    have hk_pos : 0 < k := by
      have : (0 : ℝ) < (k : ℝ) := lt_trans (by positivity) hk
      exact_mod_cast this
    have hkT_pos : 0 < (k : ℝ) * T := by positivity
    have hlow := (hbounds 0 ((k : ℝ) * T) hkT_pos).2
    simp only [zero_sub, zero_add] at hlow
    have hsub : Λ ∩ Set.Icc (-M) ((k : ℝ) * T + M) ⊆
        (Λ ∩ Set.Icc (-M) (-M + M)) ∪
        ((Λ ∩ Set.Ico 0 ((k : ℝ) * T)) ∪ (Λ ∩ Set.Icc ((k : ℝ) * T) ((k : ℝ) * T + M))) := by
      intro x ⟨hx, h1, h2⟩
      by_cases hx0 : x < 0
      · left; exact ⟨hx, h1, by linarith⟩
      · right
        by_cases hxk : x < (k : ℝ) * T
        · left; exact ⟨hx, le_of_not_gt hx0, hxk⟩
        · right; exact ⟨hx, le_of_not_gt hxk, h2⟩
    have hf1 := (separated_inter_Icc_finite_and_card_le hδ hsep (-M) (-M + M)).1
    have hf2 : (Λ ∩ Set.Ico 0 ((k : ℝ) * T)).Finite :=
      ((separated_inter_Icc_finite_and_card_le hδ hsep 0 ((k : ℝ) * T)).1).subset
        (Set.inter_subset_inter_right _ Set.Ico_subset_Icc_self)
    have hf3 := (separated_inter_Icc_finite_and_card_le hδ hsep ((k : ℝ) * T) ((k : ℝ) * T + M)).1
    have hcard_le : (Λ ∩ Set.Icc (-M) ((k : ℝ) * T + M)).ncard ≤ k * p + 2 * C := by
      have h1 := Set.ncard_le_ncard hsub (hf1.union (hf2.union hf3))
      have h2 := Set.ncard_union_le (Λ ∩ Set.Icc (-M) (-M + M))
        ((Λ ∩ Set.Ico 0 ((k : ℝ) * T)) ∪ (Λ ∩ Set.Icc ((k : ℝ) * T) ((k : ℝ) * T + M)))
      have h3 := Set.ncard_union_le (Λ ∩ Set.Ico 0 ((k : ℝ) * T))
        (Λ ∩ Set.Icc ((k : ℝ) * T) ((k : ℝ) * T + M))
      rw [hcard_mul k] at h3
      have hc1 := hC_bound (-M)
      have hc3 := hC_bound ((k : ℝ) * T)
      omega
    have hcard_leR : ((Λ ∩ Set.Icc (-M) ((k : ℝ) * T + M)).ncard : ℝ) ≤
        (k : ℝ) * (p : ℝ) + 2 * (C : ℝ) := by
      exact_mod_cast hcard_le
    have hk_gt : (2 * (C : ℝ) + ε + 1) / (T - (p : ℝ) - (T / δ) * ε) < (k : ℝ) := by linarith
    have hk_mul : 2 * (C : ℝ) + ε + 1 < (k : ℝ) * (T - (p : ℝ) - (T / δ) * ε) :=
      (div_lt_iff₀ hgap).mp hk_gt
    have hrew : ((k : ℝ) * T / δ + 1) * ε = (k : ℝ) * ((T / δ) * ε) + ε := by ring
    rw [hrew] at hlow
    linarith
  exact le_antisymm hle hge

/- ## Section 3: Explicit Box Convolutions, Neumann Series, and Spectral Gap -/

noncomputable def boxFn (r : ℝ) : ℝ → ℂ :=
  (Set.Icc (-r) r).indicator (fun _ => (1 : ℂ))

lemma integrable_boxFn (r : ℝ) : Integrable (boxFn r) volume := by
  unfold boxFn
  rw [integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_const (by simp [Real.volume_Icc])

lemma fourier_boxFn (r : ℝ) (hr : 0 < r) (ξ : ℝ) :
    𝓕 (boxFn r) ξ =
      if ξ = 0 then ((2 * r : ℝ) : ℂ)
      else ((Real.sin (2 * Real.pi * r * ξ) / (Real.pi * ξ) : ℝ) : ℂ) := by
  rw [fourier_real_eq]
  unfold boxFn
  have hind : (fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (ξ : ℂ)) *
      (Set.Icc (-r) r).indicator (fun _ => (1 : ℂ)) v) =
      (Set.Icc (-r) r).indicator (fun v => Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (v : ℂ))) := by
    funext v
    by_cases hv : v ∈ Set.Icc (-r) r
    · simp only [Set.indicator_of_mem hv, mul_one]
      congr 1; ring
    · simp [Set.indicator_of_notMem hv]
  rw [hind, integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  split_ifs with hξ
  · subst hξ
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, Complex.real_smul, mul_one]
    push_cast; ring
  · set c : ℂ := -2 * Real.pi * Complex.I * (ξ : ℂ)
    have hc : c ≠ 0 := by
      simp only [c, ne_eq, mul_eq_zero, neg_eq_zero, OfNat.ofNat_ne_zero,
        Complex.ofReal_eq_zero, Real.pi_ne_zero, Complex.I_ne_zero, hξ, or_self, not_false_eq_true]
    have hderiv : ∀ x ∈ Set.uIcc (-r) r,
        HasDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ)) / c)
          (Complex.exp (c * (x : ℂ))) x := by
      intro x _
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c
      have h2 := h1.cexp.div_const c
      simpa [mul_div_cancel_right₀ _ hc] using h2
    have hcont : IntervalIntegrable (fun v : ℝ => Complex.exp (c * (v : ℂ))) volume (-r) r :=
      (Continuous.intervalIntegrable (by fun_prop) _ _)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
    have heq_fn : (fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (ξ : ℂ) * (v : ℂ))) =
        fun v : ℝ => Complex.exp (c * (v : ℂ)) := rfl
    rw [heq_fn, hftc]
    have hsin : ((Real.sin (2 * Real.pi * r * ξ) : ℝ) : ℂ) =
        (Complex.exp (2 * Real.pi * r * ξ * Complex.I) -
          Complex.exp (-(2 * Real.pi * r * ξ * Complex.I))) / (2 * Complex.I) := by
      rw [Complex.ofReal_sin, Complex.sin]
      have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
      field_simp [hI]
      have hsq : Complex.I ^ 2 = -1 := Complex.I_sq
      push_cast
      have he1 : Complex.I * 2 * (Real.pi : ℂ) * (r : ℂ) * (ξ : ℂ) = 2 * Real.pi * r * ξ * Complex.I := by ring
      rw [he1]
      linear_combination (Complex.exp (-(2 * Real.pi * r * ξ * Complex.I)) -
        Complex.exp (2 * Real.pi * r * ξ * Complex.I)) * hsq
    rw [Complex.ofReal_div, hsin]
    push_cast
    have hexp1 : c * (r : ℂ) = -(2 * Real.pi * r * ξ * Complex.I) := by
      simp only [c]; push_cast; ring
    have hexp2 : c * -(r : ℂ) = 2 * Real.pi * r * ξ * Complex.I := by
      simp only [c]; push_cast; ring
    rw [hexp1, hexp2]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hξC : (ξ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hξ
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    simp only [c]
    field_simp [hpi, hξC, hI]
    ring

lemma fourier_boxFn_even (r : ℝ) (hr : 0 < r) (ξ : ℝ) :
    𝓕 (boxFn r) (-ξ) = 𝓕 (boxFn r) ξ := by
  rw [fourier_boxFn r hr (-ξ), fourier_boxFn r hr ξ]
  by_cases h : ξ = 0
  · subst h; simp
  · have hneg : -ξ ≠ 0 := neg_ne_zero.mpr h
    simp only [h, hneg, ↓reduceIte]
    congr 1
    have h1 : 2 * Real.pi * r * -ξ = -(2 * Real.pi * r * ξ) := by ring
    rw [h1, Real.sin_neg]
    ring

lemma norm_fourier_boxFn_le (r : ℝ) (hr : 0 < r) (ξ : ℝ) :
    ‖𝓕 (boxFn r) ξ‖ ≤ 2 * r ∧ (ξ ≠ 0 → ‖𝓕 (boxFn r) ξ‖ ≤ 1 / (Real.pi * |ξ|)) := by
  constructor
  · rw [fourier_real_eq]
    calc
      ‖∫ v : ℝ, Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (ξ : ℂ)) * boxFn r v‖
          ≤ ∫ v : ℝ, ‖Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (ξ : ℂ)) * boxFn r v‖ :=
            norm_integral_le_integral_norm _
      _ = ∫ v : ℝ, (Set.Icc (-r) r).indicator (fun _ => (1 : ℝ)) v := by
            congr 1; funext v
            rw [norm_mul]
            have he : ‖Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (ξ : ℂ))‖ = 1 := by
              have h1 : -2 * Real.pi * Complex.I * (v : ℂ) * (ξ : ℂ) =
                  Complex.I * ((-2 * Real.pi * (v * ξ) : ℝ) : ℂ) := by push_cast; ring
              rw [h1, Complex.norm_exp_I_mul_ofReal]
            rw [he, one_mul]
            unfold boxFn
            by_cases hv : v ∈ Set.Icc (-r) r <;> simp [hv]
      _ = 2 * r := by
            rw [integral_indicator measurableSet_Icc]
            simp [Real.volume_Icc, Measure.real]
            rw [ENNReal.toReal_ofReal (by linarith)]
            ring
  · intro hξ
    rw [fourier_boxFn r hr ξ, if_neg hξ, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_mul, abs_of_pos Real.pi_pos]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

lemma box_conv_box (r₁ r₂ : ℝ) (y : ℝ) :
    ((boxFn r₁) ⋆[ContinuousLinearMap.mul ℂ ℂ] (boxFn r₂)) y =
      ((max 0 (min r₁ (y + r₂) - max (-r₁) (y - r₂)) : ℝ) : ℂ) := by
  simp only [convolution_def, ContinuousLinearMap.mul_apply', boxFn]
  have hmul : (fun x : ℝ => (Set.Icc (-r₁) r₁).indicator (fun _ => (1 : ℂ)) x *
      (Set.Icc (-r₂) r₂).indicator (fun _ => (1 : ℂ)) (y - x)) =
      (Set.Icc (max (-r₁) (y - r₂)) (min r₁ (y + r₂))).indicator (fun _ => (1 : ℂ)) := by
    funext x
    by_cases h1 : x ∈ Set.Icc (-r₁) r₁ <;> by_cases h2 : y - x ∈ Set.Icc (-r₂) r₂
    · have h3 : x ∈ Set.Icc (max (-r₁) (y - r₂)) (min r₁ (y + r₂)) :=
        ⟨max_le h1.1 (by linarith [h2.2]), le_min h1.2 (by linarith [h2.1])⟩
      simp [h1, h2, h3]
    · have h3 : x ∉ Set.Icc (max (-r₁) (y - r₂)) (min r₁ (y + r₂)) := fun h =>
        h2 ⟨by linarith [(le_min_iff.mp h.2).2], by linarith [(max_le_iff.mp h.1).2]⟩
      simp [h1, h2, h3]
    · have h3 : x ∉ Set.Icc (max (-r₁) (y - r₂)) (min r₁ (y + r₂)) := fun h =>
        h1 ⟨(max_le_iff.mp h.1).1, (le_min_iff.mp h.2).1⟩
      simp [h1, h2, h3]
    · have h3 : x ∉ Set.Icc (max (-r₁) (y - r₂)) (min r₁ (y + r₂)) := fun h =>
        h1 ⟨(max_le_iff.mp h.1).1, (le_min_iff.mp h.2).1⟩
      simp [h1, h2, h3]
  rw [hmul, integral_indicator measurableSet_Icc]
  simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    Complex.real_smul, mul_one]
  by_cases h : max (-r₁) (y - r₂) ≤ min r₁ (y + r₂)
  · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr h), max_eq_right (sub_nonneg.mpr h)]
  · push Not at h
    rw [ENNReal.ofReal_of_nonpos (by linarith : min r₁ (y + r₂) - max (-r₁) (y - r₂) ≤ 0),
      ENNReal.toReal_zero, max_eq_left (by linarith : min r₁ (y + r₂) - max (-r₁) (y - r₂) ≤ 0)]

noncomputable def chi0 : ℝ → ℂ :=
  (boxFn (3 / 2)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (boxFn (1 / 2))

lemma chi0_apply (y : ℝ) :
    chi0 y = ((max 0 (min (3 / 2) (y + 1 / 2) - max (-3 / 2) (y - 1 / 2)) : ℝ) : ℂ) := by
  have h := box_conv_box (3 / 2) (1 / 2) y
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring]
  exact h

lemma continuous_chi0 : Continuous chi0 := by
  have heq : chi0 = fun y =>
      ((max 0 (min (3 / 2) (y + 1 / 2) - max (-3 / 2) (y - 1 / 2)) : ℝ) : ℂ) :=
    funext chi0_apply
  rw [heq]
  fun_prop

lemma integrable_chi0 : Integrable chi0 volume :=
  (integrable_boxFn (3 / 2)).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_boxFn (1 / 2))

lemma chi0_eq_one_of_abs_le_one {y : ℝ} (hy : |y| ≤ 1) : chi0 y = 1 := by
  rw [chi0_apply]
  have ⟨h1, h2⟩ := abs_le.mp hy
  have hmin : min (3 / 2 : ℝ) (y + 1 / 2) = y + 1 / 2 := min_eq_right (by linarith)
  have hmax : max (-3 / 2 : ℝ) (y - 1 / 2) = y - 1 / 2 := max_eq_right (by linarith)
  rw [hmin, hmax]
  norm_num

noncomputable def k0 : ℝ → ℂ := 𝓕 chi0

lemma k0_eq (ξ : ℝ) : k0 ξ = 𝓕 (boxFn (3 / 2)) ξ * 𝓕 (boxFn (1 / 2)) ξ := by
  unfold k0 chi0
  exact Real.fourier_mul_convolution_eq (integrable_boxFn (3 / 2)) (integrable_boxFn (1 / 2)) ξ

lemma k0_even (ξ : ℝ) : k0 (-ξ) = k0 ξ := by
  rw [k0_eq, k0_eq, fourier_boxFn_even (3 / 2) (by norm_num),
    fourier_boxFn_even (1 / 2) (by norm_num)]

lemma continuous_k0 : Continuous k0 :=
  continuous_fourier_real integrable_chi0

lemma norm_k0_le_three (ξ : ℝ) : ‖k0 ξ‖ ≤ 3 := by
  rw [k0_eq, norm_mul]
  have h1 := (norm_fourier_boxFn_le (3 / 2) (by norm_num) ξ).1
  have h2 := (norm_fourier_boxFn_le (1 / 2) (by norm_num) ξ).1
  have hn1 := norm_nonneg (𝓕 (boxFn (3 / 2)) ξ)
  have hn2 := norm_nonneg (𝓕 (boxFn (1 / 2)) ξ)
  nlinarith

lemma norm_k0_le_inv_sq (ξ : ℝ) : ‖k0 ξ‖ ≤ 6 * (1 + ξ ^ 2)⁻¹ := by
  by_cases h1 : |ξ| ≤ 1
  · have hsq : ξ ^ 2 ≤ 1 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
    have hpos : 0 < 1 + ξ ^ 2 := by positivity
    have h3 : ‖k0 ξ‖ ≤ 3 := norm_k0_le_three ξ
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    nlinarith
  · push Not at h1
    have hne : ξ ≠ 0 := by intro h0; subst h0; simp at h1; linarith
    rw [k0_eq, norm_mul]
    have hb1 := (norm_fourier_boxFn_le (3 / 2) (by norm_num) ξ).2 hne
    have hb2 := (norm_fourier_boxFn_le (1 / 2) (by norm_num) ξ).2 hne
    have hmul : ‖𝓕 (boxFn (3 / 2)) ξ‖ * ‖𝓕 (boxFn (1 / 2)) ξ‖ ≤
        (1 / (Real.pi * |ξ|)) * (1 / (Real.pi * |ξ|)) :=
      mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hsq_gt : 1 < ξ ^ 2 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
    have hstep : (1 / (Real.pi * |ξ|)) * (1 / (Real.pi * |ξ|)) ≤ 6 * (1 + ξ ^ 2)⁻¹ := by
      have hrew : (1 / (Real.pi * |ξ|)) * (1 / (Real.pi * |ξ|)) = 1 / (Real.pi ^ 2 * ξ ^ 2) := by
        rw [one_div_mul_one_div]
        congr 1
        nlinarith [sq_abs ξ]
      rw [hrew, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
      have hpi2 : 1 ≤ Real.pi ^ 2 := by nlinarith
      nlinarith
    exact le_trans hmul hstep

lemma integrable_k0 : Integrable k0 volume := by
  refine (integrable_inv_one_add_sq.const_mul 6).mono' continuous_k0.aestronglyMeasurable ?_
  filter_upwards with ξ
  exact norm_k0_le_inv_sq ξ

lemma fourier_k0_eq_chi0 (y : ℝ) : 𝓕 k0 y = chi0 y := by
  have hinv := continuous_chi0.fourierInv_fourier_eq integrable_chi0 integrable_k0
  have hinv_y : 𝓕⁻ k0 y = chi0 y := congrFun hinv y
  rw [← hinv_y, Real.fourierInv_eq_fourier_neg, fourier_real_eq, fourier_real_eq]
  rw [← integral_comp_neg_real (fun v =>
    Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * ((-y : ℝ) : ℂ)) * k0 v)]
  congr 1; funext v
  rw [k0_even]
  congr 1; push_cast; ring

lemma young_L1_convolution {f g : ℝ → ℂ} (hf : Integrable f volume) (hg : Integrable g volume) :
    Integrable (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) volume ∧
    ∫ y, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) y‖ ≤ (∫ x, ‖f x‖) * (∫ u, ‖g u‖) := by
  have hconv : Integrable (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) volume :=
    hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hg
  refine ⟨hconv, ?_⟩
  have hprod : Integrable (Function.uncurry fun y x : ℝ => ‖f x‖ * ‖g (y - x)‖) (volume.prod volume) := by
    change Integrable (fun p : ℝ × ℝ => ‖f p.2‖ * ‖g (p.1 - p.2)‖) (volume.prod volume)
    simpa [ContinuousLinearMap.mul_apply'] using
      hf.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg.norm
  have hswap := MeasureTheory.integral_integral_swap hprod
  have hrhs : (∫ x, ∫ y, ‖f x‖ * ‖g (y - x)‖) = (∫ x, ‖f x‖) * (∫ u, ‖g u‖) := by
    have hinner : ∀ x : ℝ, (∫ y, ‖f x‖ * ‖g (y - x)‖) = ‖f x‖ * (∫ u, ‖g u‖) := by
      intro x
      rw [integral_const_mul, integral_sub_right_eq_self (fun u => ‖g u‖) x]
    simp_rw [hinner, integral_mul_const]
  rw [← hrhs, ← hswap]
  apply integral_mono hconv.norm hprod.integral_prod_left
  intro y
  dsimp only
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  calc
    ‖∫ x, f x * g (y - x)‖ ≤ ∫ x, ‖f x * g (y - x)‖ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g (y - x)‖ := by congr 1; funext x; exact norm_mul _ _


/- ## Section 3b: Neumann Series and Shifted Tent Annihilation -/

noncomputable def kScale (a x : ℝ) : ℂ := (a : ℂ) * k0 (a * x)

lemma integrable_kScale {a : ℝ} (ha : 0 < a) : Integrable (kScale a) volume := by
  unfold kScale
  exact (integrable_k0.comp_mul_left' ha.ne').const_mul (a : ℂ)

lemma continuous_kScale (a : ℝ) : Continuous (kScale a) := by
  unfold kScale
  exact continuous_const.mul (continuous_k0.comp (continuous_const.mul continuous_id))

lemma norm_kScale_le {a : ℝ} (ha : 0 < a) (x : ℝ) : ‖kScale a x‖ ≤ 3 * a := by
  unfold kScale
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
  have h := norm_k0_le_three (a * x)
  nlinarith

lemma fourier_kScale {a : ℝ} (ha : 0 < a) (y : ℝ) :
    𝓕 (kScale a) y = chi0 (y / a) := by
  rw [fourier_real_eq]
  unfold kScale
  have h1 : (fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (y : ℂ)) *
      ((a : ℂ) * k0 (a * v))) =
      fun v : ℝ => (a : ℂ) * (Complex.exp (-2 * Real.pi * Complex.I * ((a * v : ℝ) : ℂ) * ((y / a : ℝ) : ℂ)) *
        k0 (a * v)) := by
    funext v
    have hexp : -2 * Real.pi * Complex.I * (v : ℂ) * (y : ℂ) =
        -2 * Real.pi * Complex.I * ((a * v : ℝ) : ℂ) * ((y / a : ℝ) : ℂ) := by
      push_cast
      have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
      field_simp [haC]
    rw [hexp]; ring
  rw [h1, integral_const_mul]
  have hsub := Measure.integral_comp_mul_left
    (fun u : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (u : ℂ) * ((y / a : ℝ) : ℂ)) * k0 u) a
  rw [hsub]
  rw [abs_inv, abs_of_pos ha, Complex.real_smul, Complex.ofReal_inv]
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  rw [← mul_assoc, mul_inv_cancel₀ haC, one_mul, ← fourier_real_eq]
  exact fourier_k0_eq_chi0 (y / a)

noncomputable def rhoScale (S : Set ℝ) (a : ℝ) : ℝ → ℂ :=
  fun x => kScale a x - ((fun ξ => ((gFun S ξ : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (kScale a)) x

lemma integrable_rhoScale {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) {a : ℝ} (ha : 0 < a) :
    Integrable (rhoScale S a) volume := by
  unfold rhoScale
  have hg : Integrable (fun ξ => ((gFun S ξ : ℝ) : ℂ)) volume :=
    (integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol).1.ofReal
  exact (integrable_kScale ha).sub
    (hg.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_kScale ha))

lemma norm_rhoScale_le {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    ‖rhoScale S a x‖ ≤ 6 * a := by
  unfold rhoScale
  have ⟨hg_int, hg_one⟩ := integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol
  have hconv_le : ‖((fun ξ => ((gFun S ξ : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (kScale a)) x‖ ≤
      3 * a := by
    simp only [convolution_def, ContinuousLinearMap.mul_apply']
    calc
      ‖∫ ξ, ((gFun S ξ : ℝ) : ℂ) * kScale a (x - ξ)‖
          ≤ ∫ ξ, ‖((gFun S ξ : ℝ) : ℂ) * kScale a (x - ξ)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ, gFun S ξ * (3 * a) := by
            apply integral_mono
            · refine (hg_int.mul_const (3 * a)).mono' ?_ ?_
              · exact (hg_int.ofReal.aestronglyMeasurable.mul
                  ((continuous_kScale a).comp (continuous_const.sub continuous_id)).aestronglyMeasurable).norm
              · filter_upwards with ξ
                rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
                  Real.norm_of_nonneg (gFun_nonneg S ξ)]
                exact mul_le_mul_of_nonneg_left (norm_kScale_le ha _) (gFun_nonneg S ξ)
            · exact hg_int.mul_const (3 * a)
            · intro ξ
              dsimp only
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gFun_nonneg S ξ)]
              exact mul_le_mul_of_nonneg_left (norm_kScale_le ha _) (gFun_nonneg S ξ)
      _ = 3 * a := by rw [integral_mul_const, hg_one, one_mul]
  calc
    ‖kScale a x - ((fun ξ => ((gFun S ξ : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (kScale a)) x‖
        ≤ ‖kScale a x‖ + ‖((fun ξ => ((gFun S ξ : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (kScale a)) x‖ :=
          norm_sub_le _ _
    _ ≤ 3 * a + 3 * a := add_le_add (norm_kScale_le ha x) hconv_le
    _ = 6 * a := by ring

lemma fourier_rhoScale {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) {a : ℝ} (ha : 0 < a) (y : ℝ) :
    𝓕 (rhoScale S a) y = (1 - hAuto S y) * chi0 (y / a) := by
  have hg : Integrable (fun ξ => ((gFun S ξ : ℝ) : ℂ)) volume :=
    (integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol).1.ofReal
  have hk : Integrable (kScale a) volume := integrable_kScale ha
  have hconv : Integrable ((fun ξ => ((gFun S ξ : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (kScale a)) volume :=
    hg.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hk
  have hsub : 𝓕 (rhoScale S a) y = 𝓕 (kScale a) y -
      𝓕 ((fun ξ => ((gFun S ξ : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (kScale a)) y := by
    unfold rhoScale
    rw [fourier_real_eq, fourier_real_eq, fourier_real_eq]
    have hexp_norm : ∀ v : ℝ, ‖Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (y : ℂ))‖ = 1 := by
      intro v
      have h : -2 * Real.pi * Complex.I * (v : ℂ) * (y : ℂ) =
          Complex.I * ((-2 * Real.pi * v * y : ℝ) : ℂ) := by push_cast; ring
      rw [h, Complex.norm_exp_I_mul_ofReal]
    have hcont_exp : Continuous (fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (y : ℂ))) := by
      fun_prop
    have h1 : Integrable (fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (y : ℂ)) * kScale a v) volume := by
      refine hk.norm.mono' (hcont_exp.aestronglyMeasurable.mul hk.aestronglyMeasurable) ?_
      filter_upwards with v; rw [norm_mul, hexp_norm, one_mul]
    have h2 : Integrable (fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (y : ℂ)) *
        ((fun ξ => ((gFun S ξ : ℝ) : ℂ)) ⋆[ContinuousLinearMap.mul ℂ ℂ] (kScale a)) v) volume := by
      refine hconv.norm.mono' (hcont_exp.aestronglyMeasurable.mul hconv.aestronglyMeasurable) ?_
      filter_upwards with v; rw [norm_mul, hexp_norm, one_mul]
    rw [← integral_sub h1 h2]
    congr 1; funext v; ring
  rw [hsub, Real.fourier_mul_convolution_eq hg hk, fourier_kScale ha y,
    fourier_gFun_eq_hAuto hS_bdd hS_meas hS_vol y]
  ring

lemma tendsto_k0_translation :
    Tendsto (fun v : ℝ => ∫ u : ℝ, ‖k0 u - k0 (u - v)‖) (𝓝 0) (𝓝 0) := by
  have h0 : (0 : ℝ) = ∫ _u : ℝ, (0 : ℝ) := by simp
  conv_rhs => rw [h0]
  -- Dominator for |v| ≤ 1: 6 / (1 + u^2) + 24 / (1 + u^2) = 30 / (1 + u^2)
  have hdom : ∀ u v : ℝ, |v| ≤ 1 → ‖k0 (u - v)‖ ≤ 24 * (1 + u ^ 2)⁻¹ := by
    intro u v hv
    by_cases hu : |u| ≤ 2
    · have hsq : u ^ 2 ≤ 4 := by nlinarith [sq_abs u, abs_nonneg u]
      have hpos : 0 < 1 + u ^ 2 := by positivity
      have h3 := norm_k0_le_three (u - v)
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      nlinarith
    · push Not at hu
      have h1 : |u| / 2 ≤ |u - v| := by
        have := abs_sub_abs_le_abs_sub u v
        linarith
      have hsq : u ^ 2 / 4 ≤ (u - v) ^ 2 := by
        have hpos : 0 ≤ |u| / 2 := by positivity
        nlinarith [sq_abs u, sq_abs (u - v)]
      have hbound := norm_k0_le_inv_sq (u - v)
      have hpos1 : 0 < 1 + (u - v) ^ 2 := by positivity
      have hpos2 : 0 < 1 + u ^ 2 := by positivity
      have hineq : 6 * (1 + (u - v) ^ 2)⁻¹ ≤ 24 * (1 + u ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ hpos1 hpos2]
        nlinarith
      exact le_trans hbound hineq
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => 30 * (1 + u ^ 2)⁻¹) ?_ ?_ (integrable_inv_one_add_sq.const_mul 30) ?_
  · exact Eventually.of_forall fun v =>
      (continuous_k0.sub (continuous_k0.comp (continuous_id.sub continuous_const))).norm.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with v hv
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hv
    filter_upwards with u
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    calc
      ‖k0 u - k0 (u - v)‖ ≤ ‖k0 u‖ + ‖k0 (u - v)‖ := norm_sub_le _ _
      _ ≤ 6 * (1 + u ^ 2)⁻¹ + 24 * (1 + u ^ 2)⁻¹ :=
        add_le_add (norm_k0_le_inv_sq u) (hdom u v hv.le)
      _ = 30 * (1 + u ^ 2)⁻¹ := by ring
  · filter_upwards with u
    have h1 : Tendsto (fun v : ℝ => k0 u - k0 (u - v)) (𝓝 0) (𝓝 (k0 u - k0 (u - 0))) :=
      tendsto_const_nhds.sub ((continuous_k0.tendsto (u - 0)).comp (tendsto_const_nhds.sub tendsto_id))
    rw [sub_zero, sub_self] at h1
    simpa using h1.norm

lemma exists_a_neumann_small {S : Set ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) :
    ∃ a > 0, ∫ x, ‖rhoScale S a x‖ ≤ 1 / 2 := by
  have ⟨hg_int, hg_one⟩ := integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol
  let I : ℝ → ℝ := fun v => ∫ u : ℝ, ‖k0 u - k0 (u - v)‖
  have hI_le : ∀ v : ℝ, I v ≤ 2 * ∫ u : ℝ, ‖k0 u‖ := by
    intro v
    unfold I
    have htri : ∫ u : ℝ, ‖k0 u - k0 (u - v)‖ ≤
        ∫ u : ℝ, (‖k0 u‖ + ‖k0 (u - v)‖) := by
      apply integral_mono ((integrable_k0.sub (integrable_k0.comp_sub_right v)).norm)
        (integrable_k0.norm.add (integrable_k0.comp_sub_right v).norm)
      intro u; exact norm_sub_le _ _
    rw [integral_add integrable_k0.norm (integrable_k0.comp_sub_right v).norm,
      integral_sub_right_eq_self (fun u => ‖k0 u‖) v] at htri
    linarith
  have hI_cont : Continuous I := by
    rw [continuous_iff_continuousAt]
    intro v₀
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hlim := Metric.tendsto_nhds.mp tendsto_k0_translation ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hlim
    refine ⟨δ, hδ_pos, fun v hv => ?_⟩
    rw [Real.dist_eq] at hv ⊢
    have hdiff_le : |I v - I v₀| ≤ I (v - v₀) := by
      have hi_v : Integrable (fun u : ℝ => ‖k0 u - k0 (u - v)‖) volume :=
        (integrable_k0.sub (integrable_k0.comp_sub_right v)).norm
      have hi_v0 : Integrable (fun u : ℝ => ‖k0 u - k0 (u - v₀)‖) volume :=
        (integrable_k0.sub (integrable_k0.comp_sub_right v₀)).norm
      have hi_diff : Integrable (fun u : ℝ => ‖k0 (u - v₀) - k0 (u - v)‖) volume :=
        ((integrable_k0.comp_sub_right v₀).sub (integrable_k0.comp_sub_right v)).norm
      have hshift : ∫ u, ‖k0 u - k0 (u - (v - v₀))‖ = ∫ u, ‖k0 (u - v₀) - k0 (u - v)‖ := by
        rw [← integral_sub_right_eq_self (fun u => ‖k0 u - k0 (u - (v - v₀))‖) v₀]
        congr 1; funext u; ring_nf
      have h1 : I v - I v₀ ≤ I (v - v₀) := by
        unfold I
        rw [← integral_sub hi_v hi_v0, hshift]
        apply integral_mono (hi_v.sub hi_v0) hi_diff
        intro u
        dsimp only
        calc
          ‖k0 u - k0 (u - v)‖ - ‖k0 u - k0 (u - v₀)‖
              ≤ ‖(k0 u - k0 (u - v)) - (k0 u - k0 (u - v₀))‖ := norm_sub_norm_le _ _
          _ = ‖k0 (u - v₀) - k0 (u - v)‖ := by ring_nf
      have h2 : I v₀ - I v ≤ I (v - v₀) := by
        unfold I
        rw [← integral_sub hi_v0 hi_v, hshift]
        apply integral_mono (hi_v0.sub hi_v) hi_diff
        intro u
        dsimp only
        calc
          ‖k0 u - k0 (u - v₀)‖ - ‖k0 u - k0 (u - v)‖
              ≤ ‖(k0 u - k0 (u - v₀)) - (k0 u - k0 (u - v))‖ := norm_sub_norm_le _ _
          _ = ‖k0 (u - v) - k0 (u - v₀)‖ := by ring_nf
          _ = ‖k0 (u - v₀) - k0 (u - v)‖ := norm_sub_rev _ _
      exact abs_le.mpr ⟨by linarith, h1⟩
    have hlt := hδ (by rw [Real.dist_eq, sub_zero]; exact hv)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at hlt
    exact lt_of_le_of_lt hdiff_le hlt
  -- Dominated convergence as a → 0+
  have hlim : Tendsto (fun a : ℝ => ∫ ξ : ℝ, gFun S ξ * I (a * ξ)) (𝓝 0) (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ξ : ℝ, (0 : ℝ) := by simp
    conv_rhs => rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => gFun S ξ * (2 * ∫ u : ℝ, ‖k0 u‖)) ?_ ?_ (hg_int.mul_const _) ?_
    · exact Eventually.of_forall fun a =>
        ((continuous_gFun hS_bdd hS_meas).mul
          (hI_cont.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    · refine Eventually.of_forall fun a => Eventually.of_forall fun ξ => ?_
      have hI_nn : 0 ≤ I (a * ξ) := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg (mul_nonneg (gFun_nonneg S ξ) hI_nn)]
      exact mul_le_mul_of_nonneg_left (hI_le _) (gFun_nonneg S ξ)
    · filter_upwards with ξ
      have h1 : Tendsto (fun a : ℝ => a * ξ) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id.mul_const ξ : Tendsto (fun a : ℝ => a * ξ) (𝓝 0) (𝓝 (0 * ξ)))
      have h2 := tendsto_k0_translation.comp h1
      simpa using h2.const_mul (gFun S ξ)
  have hmem := (Metric.tendsto_nhds.mp hlim) (1 / 2) (by norm_num)
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hmem
  set a : ℝ := δ / 2
  have ha : 0 < a := by positivity
  refine ⟨a, ha, ?_⟩
  have hlt : ∫ ξ : ℝ, gFun S ξ * I (a * ξ) < 1 / 2 := by
    have h := hδ (by rw [Real.dist_eq, sub_zero, abs_of_pos ha]; dsimp only [a]; linarith)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun ξ =>
      mul_nonneg (gFun_nonneg S ξ) (integral_nonneg fun _ => norm_nonneg _))] at h
    exact h
  -- Relate ∫ ‖rhoScale S a x‖ ≤ ∫ ξ, gFun S ξ * I (a * ξ)
  have hbound : ∫ x, ‖rhoScale S a x‖ ≤ ∫ ξ, gFun S ξ * I (a * ξ) := by
    -- Express rhoScale S a x = ∫ ξ, gFun S ξ * (kScale a x - kScale a (x - ξ))
    have hrepr : ∀ x : ℝ, rhoScale S a x =
        ∫ ξ, ((gFun S ξ : ℝ) : ℂ) * (kScale a x - kScale a (x - ξ)) := by
      intro x
      unfold rhoScale
      simp only [convolution_def, ContinuousLinearMap.mul_apply']
      have h1 : Integrable (fun ξ => ((gFun S ξ : ℝ) : ℂ) * kScale a x) volume :=
        hg_int.ofReal.mul_const _
      have h2 : Integrable (fun ξ => ((gFun S ξ : ℝ) : ℂ) * kScale a (x - ξ)) volume := by
        refine (hg_int.mul_const (3 * a)).mono' ?_ ?_
        · exact hg_int.ofReal.aestronglyMeasurable.mul
            ((continuous_kScale a).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        · filter_upwards with ξ
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gFun_nonneg S ξ)]
          exact mul_le_mul_of_nonneg_left (norm_kScale_le ha _) (gFun_nonneg S ξ)
      have hsub := integral_sub h1 h2
      have hmul_sub : (fun ξ => ((gFun S ξ : ℝ) : ℂ) * (kScale a x - kScale a (x - ξ))) =
          fun ξ => ((gFun S ξ : ℝ) : ℂ) * kScale a x - ((gFun S ξ : ℝ) : ℂ) * kScale a (x - ξ) := by
        funext ξ; ring
      rw [hmul_sub, hsub, integral_mul_const, integral_complex_ofReal, hg_one]
      simp
    -- Product integrability of (x, ξ) ↦ gFun S ξ * ‖kScale a x - kScale a (x - ξ)‖
    have hprod1 : Integrable (fun p : ℝ × ℝ => gFun S p.2 * ‖kScale a p.1‖) (volume.prod volume) := by
      have := (integrable_kScale ha).norm.mul_prod hg_int
      exact this.congr (Eventually.of_forall fun p => by ring)
    have hprod2 : Integrable (fun p : ℝ × ℝ => gFun S p.2 * ‖kScale a (p.1 - p.2)‖) (volume.prod volume) := by
      simpa [ContinuousLinearMap.mul_apply'] using
        hg_int.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) (integrable_kScale ha).norm
    have hprod : Integrable (Function.uncurry fun x ξ : ℝ =>
        gFun S ξ * ‖kScale a x - kScale a (x - ξ)‖) (volume.prod volume) := by
      refine (hprod1.add hprod2).mono' ?_ ?_
      · exact ((continuous_gFun hS_bdd hS_meas).comp continuous_snd |>.mul
          (((continuous_kScale a).comp continuous_fst).sub
            ((continuous_kScale a).comp (continuous_fst.sub continuous_snd))).norm).aestronglyMeasurable
      · filter_upwards with p
        dsimp only [Function.uncurry, Pi.add_apply]
        rw [Real.norm_of_nonneg (mul_nonneg (gFun_nonneg S p.2) (norm_nonneg _))]
        calc
          gFun S p.2 * ‖kScale a p.1 - kScale a (p.1 - p.2)‖
              ≤ gFun S p.2 * (‖kScale a p.1‖ + ‖kScale a (p.1 - p.2)‖) :=
                mul_le_mul_of_nonneg_left (norm_sub_le _ _) (gFun_nonneg S p.2)
          _ = gFun S p.2 * ‖kScale a p.1‖ + gFun S p.2 * ‖kScale a (p.1 - p.2)‖ := by ring
    have hstep1 : ∫ x, ‖rhoScale S a x‖ ≤
        ∫ x, ∫ ξ, gFun S ξ * ‖kScale a x - kScale a (x - ξ)‖ := by
      apply integral_mono (integrable_rhoScale hS_bdd hS_meas hS_vol ha).norm hprod.integral_prod_left
      intro x
      dsimp only
      rw [hrepr x]
      calc
        ‖∫ ξ, ((gFun S ξ : ℝ) : ℂ) * (kScale a x - kScale a (x - ξ))‖
            ≤ ∫ ξ, ‖((gFun S ξ : ℝ) : ℂ) * (kScale a x - kScale a (x - ξ))‖ :=
              norm_integral_le_integral_norm _
        _ = ∫ ξ, gFun S ξ * ‖kScale a x - kScale a (x - ξ)‖ := by
              congr 1; funext ξ
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (gFun_nonneg S ξ)]
    have hswap := MeasureTheory.integral_integral_swap hprod
    have hinner : ∀ ξ : ℝ, ∫ x, gFun S ξ * ‖kScale a x - kScale a (x - ξ)‖ =
        gFun S ξ * I (a * ξ) := by
      intro ξ
      rw [integral_const_mul]
      congr 1
      unfold kScale I
      have hfactor : (fun x : ℝ => ‖(a : ℂ) * k0 (a * x) - (a : ℂ) * k0 (a * (x - ξ))‖) =
          fun x : ℝ => a * ‖k0 (a * x) - k0 (a * x - a * ξ)‖ := by
        funext x
        rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg ha.le]
        congr 2; ring
      rw [hfactor, integral_const_mul]
      have hsub := Measure.integral_comp_mul_left (fun u : ℝ => ‖k0 u - k0 (u - a * ξ)‖) a
      rw [hsub, abs_inv, abs_of_pos ha, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    rw [hswap] at hstep1
    simpa only [hinner] using hstep1
  linarith

lemma spectral_gap_annihilation {S Λ : Set ℝ} {a : ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (hΛ_cnt : Λ.Countable)
    (htile : ∀ t : ℝ, HasSum (fun lam : Λ => gFun S (t - lam.1)) 1)
    (ha : 0 < a) (hrho_small : ∫ x, ‖rhoScale S a x‖ ≤ 1 / 2)
    {w : ℝ → ℂ} (hw_cont : Continuous w) (hw_int : Integrable w volume)
    (hFw_int : Integrable (𝓕 w) volume)
    (hFw_supp : ∀ y : ℝ, y ∉ Set.Ioo 0 a → 𝓕 w y = 0) :
    ∑' lam : Λ, w lam.1 = 0 := by
  haveI : Countable Λ := hΛ_cnt.to_subtype
  have ⟨hg_int, hg_one⟩ := integrable_gFun_and_integral_one hS_bdd hS_meas hS_vol
  have hrho_int : Integrable (rhoScale S a) volume := integrable_rhoScale hS_bdd hS_meas hS_vol ha
  set W : ℝ := ∫ x, ‖w x‖
  have hW_nn : 0 ≤ W := integral_nonneg fun _ => norm_nonneg _
  -- Define Neumann iterates qSeq m
  let qSeq : ℕ → ℝ → ℂ := fun m =>
    Nat.recOn m w (fun _ prev => prev ⋆[ContinuousLinearMap.mul ℂ ℂ] (rhoScale S a))
  have hq_props : ∀ m : ℕ,
      Integrable (qSeq m) volume ∧
      ∫ x, ‖qSeq m x‖ ≤ W * (1 / 2 : ℝ) ^ m ∧
      (∀ y : ℝ, 𝓕 (qSeq m) y = 𝓕 w y * (𝓕 (rhoScale S a) y) ^ m) := by
    intro m
    induction m with
    | zero =>
      refine ⟨hw_int, by simp [qSeq, W], fun y => by simp [qSeq]⟩
    | succ m ih =>
      rcases ih with ⟨hint_m, hnorm_m, hF_m⟩
      have hy := young_L1_convolution hint_m hrho_int
      refine ⟨hy.1, ?_, ?_⟩
      · calc
          ∫ x, ‖qSeq (m + 1) x‖ ≤ (∫ x, ‖qSeq m x‖) * (∫ x, ‖rhoScale S a x‖) := hy.2
          _ ≤ (W * (1 / 2 : ℝ) ^ m) * (1 / 2 : ℝ) :=
            mul_le_mul hnorm_m hrho_small (integral_nonneg fun _ => norm_nonneg _) (by positivity)
          _ = W * (1 / 2 : ℝ) ^ (m + 1) := by ring
      · intro y
        change 𝓕 ((qSeq m) ⋆[ContinuousLinearMap.mul ℂ ℂ] (rhoScale S a)) y = _
        rw [Real.fourier_mul_convolution_eq hint_m hrho_int, hF_m y]
        ring
  -- Uniform pointwise bound for m ≥ 1 so q x = ∑' m, qSeq m x converges uniformly everywhere
  have hq_pt_bound : ∀ m : ℕ, ∀ x : ℝ,
      ‖qSeq (m + 1) x‖ ≤ (6 * a * W) * (1 / 2 : ℝ) ^ m := by
    intro m x
    change ‖((qSeq m) ⋆[ContinuousLinearMap.mul ℂ ℂ] (rhoScale S a)) x‖ ≤ _
    simp only [convolution_def, ContinuousLinearMap.mul_apply']
    have hint_m := (hq_props m).1
    have hnorm_m := (hq_props m).2.1
    calc
      ‖∫ t, qSeq m t * rhoScale S a (x - t)‖
          ≤ ∫ t, ‖qSeq m t * rhoScale S a (x - t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t, ‖qSeq m t‖ * (6 * a) := by
            apply integral_mono
            · refine (hint_m.norm.mul_const (6 * a)).mono' ?_ ?_
              · exact (hint_m.aestronglyMeasurable.mul
                  (hrho_int.comp_sub_left x).aestronglyMeasurable).norm
              · filter_upwards with t
                rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
                exact mul_le_mul_of_nonneg_left
                  (norm_rhoScale_le hS_bdd hS_meas hS_vol ha _) (norm_nonneg _)
            · exact hint_m.norm.mul_const (6 * a)
            · intro t
              dsimp only
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left
                (norm_rhoScale_le hS_bdd hS_meas hS_vol ha _) (norm_nonneg _)
      _ = (∫ t, ‖qSeq m t‖) * (6 * a) := integral_mul_const _ _
      _ ≤ (W * (1 / 2 : ℝ) ^ m) * (6 * a) :=
            mul_le_mul_of_nonneg_right hnorm_m (by positivity)
      _ = (6 * a * W) * (1 / 2 : ℝ) ^ m := by ring
  let q : ℝ → ℂ := fun x => ∑' m : ℕ, qSeq m x
  have hsum_L1 : Summable (fun m : ℕ => ∫ x, ‖qSeq m x‖) := by
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _)
      (fun m => (hq_props m).2.1) ?_
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left W
  have hq_int : Integrable q volume := by
    have hmeas_q : AEStronglyMeasurable q volume := by
      have hlim : ∀ x : ℝ, Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, qSeq m x)
          atTop (𝓝 (q x)) := by
        intro x
        have hs : Summable (fun m : ℕ => qSeq m x) := by
          rw [← summable_nat_add_iff 1]
          refine Summable.of_norm_bounded (g := fun m : ℕ => (6 * a * W) * (1 / 2 : ℝ) ^ m) ?_
            (fun m => hq_pt_bound m x)
          exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
        exact hs.hasSum.tendsto_sum_nat
      refine aestronglyMeasurable_of_tendsto_ae (f := fun N x => ∑ m ∈ Finset.range N, qSeq m x) atTop
        (fun N => Finset.aestronglyMeasurable_fun_sum _ fun m _ => (hq_props m).1.aestronglyMeasurable)
        (Eventually.of_forall hlim)
    refine ⟨hmeas_q, ?_⟩
    unfold HasFiniteIntegral
    have hle : ∫⁻ x, ‖q x‖ₑ ≤ ∑' m : ℕ, ∫⁻ x, ‖qSeq m x‖ₑ := by
      rw [← lintegral_tsum (fun m => (hq_props m).1.aestronglyMeasurable.enorm)]
      apply lintegral_mono
      intro x
      exact enorm_tsum_le_tsum_enorm
    have hfin : ∑' m : ℕ, ∫⁻ x, ‖qSeq m x‖ₑ < ⊤ := by
      have heq : (fun m : ℕ => ∫⁻ x, ‖qSeq m x‖ₑ) = fun m => ENNReal.ofReal (∫ x, ‖qSeq m x‖) := by
        funext m; exact (ofReal_integral_norm_eq_lintegral_enorm (hq_props m).1).symm
      rw [heq, ← ENNReal.ofReal_tsum_of_nonneg (fun m => integral_nonneg fun _ => norm_nonneg _) hsum_L1]
      exact ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt hle hfin
  -- Fourier transform of q: 𝓕 q y = 𝓕 w y * (1 - 𝓕 (rhoScale S a) y)⁻¹
  have hFq : ∀ y : ℝ, 𝓕 q y = 𝓕 w y * (1 - 𝓕 (rhoScale S a) y)⁻¹ := by
    intro y
    rw [fourier_real_eq]
    have hexp_norm : ∀ x : ℝ, ‖Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ))‖ = 1 := by
      intro x
      have h1 : -2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ) =
          Complex.I * ((-2 * Real.pi * x * y : ℝ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_exp_I_mul_ofReal]
    have htsum_eq : ∀ x : ℝ,
        Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * q x =
        ∑' m : ℕ, Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * qSeq m x := by
      intro x
      have hs : Summable (fun m : ℕ => qSeq m x) := by
        rw [← summable_nat_add_iff 1]
        refine Summable.of_norm_bounded (g := fun m : ℕ => (6 * a * W) * (1 / 2 : ℝ) ^ m) ?_
          (fun m => hq_pt_bound m x)
        exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
      simp only [q]
      exact (hs.tsum_mul_left _).symm
    simp_rw [htsum_eq]
    have hF_int_m : ∀ m : ℕ, Integrable (fun x : ℝ =>
        Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * qSeq m x) volume := by
      intro m
      refine (hq_props m).1.norm.mono'
        ((Continuous.aestronglyMeasurable (by fun_prop)).mul (hq_props m).1.aestronglyMeasurable) ?_
      filter_upwards with x; rw [norm_mul, hexp_norm, one_mul]
    have hF_sum : Summable (fun m : ℕ => ∫ x : ℝ,
        ‖Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * qSeq m x‖) := by
      have heq : ∀ (m : ℕ) (x : ℝ), ‖Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * qSeq m x‖ =
          ‖qSeq m x‖ := by
        intro m x; rw [norm_mul, hexp_norm x, one_mul]
      simp_rw [heq]
      exact hsum_L1
    rw [← integral_tsum_of_summable_integral_norm hF_int_m hF_sum]
    have hterm : ∀ m : ℕ, ∫ x : ℝ,
        Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * qSeq m x =
        𝓕 w y * (𝓕 (rhoScale S a) y) ^ m := by
      intro m
      rw [← fourier_real_eq, (hq_props m).2.2 y]
    simp_rw [hterm, tsum_mul_left]
    congr 1
    have hnorm_lt : ‖𝓕 (rhoScale S a) y‖ < 1 := by
      have h1 : ‖𝓕 (rhoScale S a) y‖ ≤ ∫ x : ℝ, ‖rhoScale S a x‖ := by
        rw [fourier_real_eq]
        calc
          ‖∫ x : ℝ, Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * rhoScale S a x‖
              ≤ ∫ x : ℝ, ‖Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * rhoScale S a x‖ :=
                norm_integral_le_integral_norm _
          _ = ∫ x : ℝ, ‖rhoScale S a x‖ := by
                congr 1; funext x; rw [norm_mul, hexp_norm x, one_mul]
      linarith
    exact tsum_geometric_of_norm_lt_one hnorm_lt
  -- Deduce 𝓕 (q ⋆ gC) = 𝓕 w everywhere
  let gC : ℝ → ℂ := fun ξ => ((gFun S ξ : ℝ) : ℂ)
  have hgC_int : Integrable gC volume := hg_int.ofReal
  have hF_conv : 𝓕 (q ⋆[ContinuousLinearMap.mul ℂ ℂ] gC) = 𝓕 w := by
    funext y
    rw [Real.fourier_mul_convolution_eq hq_int hgC_int, hFq y,
      fourier_gFun_eq_hAuto hS_bdd hS_meas hS_vol y]
    by_cases hy : y ∈ Set.Ioo 0 a
    · have hy_abs : |y / a| ≤ 1 := by
        rw [abs_div, abs_of_pos ha, abs_of_pos hy.1, div_le_one ha]
        exact hy.2.le
      have hchi : chi0 (y / a) = 1 := chi0_eq_one_of_abs_le_one hy_abs
      have h1m : 1 - 𝓕 (rhoScale S a) y = hAuto S y := by
        rw [fourier_rhoScale hS_bdd hS_meas hS_vol ha y, hchi, mul_one]
        ring
      have hh_ne : hAuto S y ≠ 0 := by
        intro h0
        rw [h0] at h1m
        have hnorm_lt : ‖𝓕 (rhoScale S a) y‖ < 1 := by
          have h1 : ‖𝓕 (rhoScale S a) y‖ ≤ ∫ x, ‖rhoScale S a x‖ := by
            rw [fourier_real_eq]
            calc
              ‖∫ x : ℝ, Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * rhoScale S a x‖
                  ≤ ∫ x : ℝ, ‖Complex.exp (-2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ)) * rhoScale S a x‖ :=
                    norm_integral_le_integral_norm _
              _ = ∫ x : ℝ, ‖rhoScale S a x‖ := by
                    congr 1; funext x
                    rw [norm_mul]
                    have h2 : -2 * Real.pi * Complex.I * (x : ℂ) * (y : ℂ) =
                        Complex.I * ((-2 * Real.pi * x * y : ℝ) : ℂ) := by push_cast; ring
                    rw [h2, Complex.norm_exp_I_mul_ofReal, one_mul]
          linarith
        have h1 : 𝓕 (rhoScale S a) y = 1 := sub_eq_zero.mp h1m |>.symm
        rw [h1, norm_one] at hnorm_lt
        exact lt_irrefl 1 hnorm_lt
      rw [h1m, mul_assoc, inv_mul_cancel₀ hh_ne, mul_one]
    · rw [hFw_supp y hy, zero_mul, zero_mul]
  -- Continuity of q ⋆ gC by dominated convergence (since gC is continuous and |gC| ≤ 1)
  have hqg_cont : Continuous (q ⋆[ContinuousLinearMap.mul ℂ ℂ] gC) := by
    rw [continuous_iff_continuousAt]
    intro x₀
    change Tendsto (fun x => ∫ t, q t * gC (x - t)) (𝓝 x₀) (𝓝 (∫ t, q t * gC (x₀ - t)))
    refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖q t‖) ?_ ?_ hq_int.norm ?_
    · exact Eventually.of_forall fun x =>
        hq_int.aestronglyMeasurable.mul
          (((Complex.continuous_ofReal.comp (continuous_gFun hS_bdd hS_meas)).comp
            (continuous_const.sub continuous_id))).aestronglyMeasurable
    · refine Eventually.of_forall fun x => Eventually.of_forall fun t => ?_
      rw [norm_mul]
      have hg1 : ‖gC (x - t)‖ ≤ 1 := by
        simp only [gC, Complex.norm_real, Real.norm_of_nonneg (gFun_nonneg S _)]
        exact gFun_le_one hS_vol _
      simpa using mul_le_mul_of_nonneg_left hg1 (norm_nonneg (q t))
    · filter_upwards with t
      have hg_cont : Continuous gC :=
        Complex.continuous_ofReal.comp (continuous_gFun hS_bdd hS_meas)
      exact tendsto_const_nhds.mul ((hg_cont.tendsto (x₀ - t)).comp (tendsto_id.sub tendsto_const_nhds))
  -- Fourier inversion gives q ⋆ gC = w everywhere
  have hqg_eq_w : q ⋆[ContinuousLinearMap.mul ℂ ℂ] gC = w := by
    have h1 := hqg_cont.fourierInv_fourier_eq
      (hq_int.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hgC_int)
      (by rw [hF_conv]; exact hFw_int)
    have h2 := hw_cont.fourierInv_fourier_eq hw_int hFw_int
    rw [hF_conv] at h1
    rw [← h1, h2]
  -- Integral of q is 0 (from 𝓕 q 0 = 0)
  have hq_zero : ∫ x, q x = 0 := by
    have h0 := hFq 0
    have h0_supp : 𝓕 w 0 = 0 := hFw_supp 0 (by simp [Set.mem_Ioo])
    rw [h0_supp, zero_mul, fourier_real_eq] at h0
    simpa using h0
  -- Sum over Λ via integral_tsum_of_summable_integral_norm
  have hw_eval : ∀ lam : Λ, w lam.1 = ∫ x, q x * gC (x - lam.1) := by
    intro lam
    have h := congrFun hqg_eq_w lam.1
    rw [← h]
    simp only [convolution_def, ContinuousLinearMap.mul_apply', gC]
    congr 1; funext x
    rw [show lam.1 - x = -(x - lam.1) by ring, gFun_even]
  simp_rw [hw_eval]
  have hint_lam : ∀ lam : Λ, Integrable (fun x => q x * gC (x - lam.1)) volume := by
    intro lam
    refine hq_int.norm.mono' ?_ ?_
    · exact hq_int.aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.comp (continuous_gFun hS_bdd hS_meas)).comp
          (continuous_id.sub continuous_const)).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul]
      have hg1 : ‖gC (x - lam.1)‖ ≤ 1 := by
        simp only [gC, Complex.norm_real, Real.norm_of_nonneg (gFun_nonneg S _)]
        exact gFun_le_one hS_vol _
      simpa using mul_le_mul_of_nonneg_left hg1 (norm_nonneg (q x))
  have hsum_norm : Summable (fun lam : Λ => ∫ x, ‖q x * gC (x - lam.1)‖) := by
    have hlint_eq : ∑' lam : Λ, ∫⁻ x, ‖q x * gC (x - lam.1)‖ₑ = ∫⁻ x, ‖q x‖ₑ := by
      rw [← lintegral_tsum (fun lam => (hint_lam lam).aestronglyMeasurable.enorm)]
      congr 1; funext x
      have h1 : ∀ lam : Λ, ‖q x * gC (x - lam.1)‖ₑ = ‖q x‖ₑ * ENNReal.ofReal (gFun S (x - lam.1)) := by
        intro lam
        rw [enorm_mul]
        congr 1
        rw [← ofReal_norm_eq_enorm]
        simp only [gC, Complex.norm_real, Real.norm_of_nonneg (gFun_nonneg S _)]
      simp_rw [h1, ENNReal.tsum_mul_left]
      have htile_en : ∑' lam : Λ, ENNReal.ofReal (gFun S (x - lam.1)) = 1 := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun lam => gFun_nonneg S _) (htile x).summable,
          (htile x).tsum_eq, ENNReal.ofReal_one]
      rw [htile_en, mul_one]
    have hne : ∑' lam : Λ, ENNReal.ofReal (∫ x, ‖q x * gC (x - lam.1)‖) ≠ ⊤ := by
      have heq : (fun lam : Λ => ENNReal.ofReal (∫ x, ‖q x * gC (x - lam.1)‖)) =
          fun lam => ∫⁻ x, ‖q x * gC (x - lam.1)‖ₑ := by
        funext lam; exact ofReal_integral_norm_eq_lintegral_enorm (hint_lam lam)
      rw [heq, hlint_eq]
      exact hq_int.hasFiniteIntegral.ne
    exact (ENNReal.summable_toReal hne).congr fun lam =>
      ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)
  rw [integral_tsum_of_summable_integral_norm hint_lam hsum_norm]
  have hinner_eq : ∀ x : ℝ, (∑' lam : Λ, q x * gC (x - lam.1)) = q x := by
    intro x
    rw [tsum_mul_left]
    have hsum1 : ∑' lam : Λ, gC (x - lam.1) = 1 := by
      simpa [gC] using (Complex.ofRealCLM.hasSum (htile x)).tsum_eq
    rw [hsum1, mul_one]
  simp_rw [hinner_eq]
  exact hq_zero

noncomputable def tentFn (s : ℝ) : ℝ → ℂ :=
  (boxFn s) ⋆[ContinuousLinearMap.mul ℂ ℂ] (boxFn s)

lemma tentFn_apply (s y : ℝ) :
    tentFn s y = ((max 0 (min s (y + s) - max (-s) (y - s)) : ℝ) : ℂ) := by
  simpa [tentFn] using box_conv_box s s y

lemma continuous_tentFn (s : ℝ) : Continuous (tentFn s) := by
  have heq : tentFn s = fun y => ((max 0 (min s (y + s) - max (-s) (y - s)) : ℝ) : ℂ) :=
    funext (tentFn_apply s)
  rw [heq]; fun_prop

lemma integrable_tentFn (s : ℝ) : Integrable (tentFn s) volume :=
  (integrable_boxFn s).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_boxFn s)

lemma tentFn_even (s y : ℝ) : tentFn s (-y) = tentFn s y := by
  rw [tentFn_apply, tentFn_apply]
  congr 1; congr 1
  have h1 : min s (-y + s) = - max (-s) (y - s) := by
    rw [← min_neg_neg]; congr 1 <;> ring
  have h2 : max (-s) (-y - s) = - min s (y + s) := by
    rw [← max_neg_neg]; congr 1 <;> ring
  rw [h1, h2]; ring

lemma tentFn_eq_zero_of_two_mul_le_abs {s y : ℝ} (hs : 0 < s) (hy : 2 * s ≤ |y|) :
    tentFn s y = 0 := by
  rw [tentFn_apply]
  have hle : min s (y + s) - max (-s) (y - s) ≤ 0 := by
    rcases le_abs.mp hy with h | h
    · have h1 : max (-s) (y - s) = y - s := max_eq_right (by linarith)
      have h2 : min s (y + s) ≤ s := min_le_left _ _
      linarith
    · have h1 : min s (y + s) = y + s := min_eq_right (by linarith)
      have h2 : -s ≤ max (-s) (y - s) := le_max_left _ _
      linarith
  rw [max_eq_left hle, Complex.ofReal_zero]

noncomputable def weightFn (s : ℝ) (ξ : ℝ) : ℝ := (𝓕 (boxFn s) ξ).re ^ 2

lemma weightFn_nonneg (s ξ : ℝ) : 0 ≤ weightFn s ξ := sq_nonneg _

lemma weightFn_ofReal_eq (s : ℝ) (hs : 0 < s) (ξ : ℝ) :
    ((weightFn s ξ : ℝ) : ℂ) = 𝓕 (tentFn s) ξ := by
  unfold weightFn tentFn
  rw [Real.fourier_mul_convolution_eq (integrable_boxFn s) (integrable_boxFn s)]
  have hreal : ((𝓕 (boxFn s) ξ).re : ℂ) = 𝓕 (boxFn s) ξ := by
    rw [fourier_boxFn s hs ξ]
    split_ifs <;> simp only [Complex.ofReal_re]
  push_cast
  rw [hreal, sq]

lemma weightFn_even (s : ℝ) (hs : 0 < s) (ξ : ℝ) : weightFn s (-ξ) = weightFn s ξ := by
  unfold weightFn
  rw [fourier_boxFn_even s hs ξ]

lemma weightFn_le (s : ℝ) (hs : 0 < s) (ξ : ℝ) : weightFn s ξ ≤ 4 * s ^ 2 := by
  unfold weightFn
  have h := (norm_fourier_boxFn_le s hs ξ).1
  have habs : |(𝓕 (boxFn s) ξ).re| ≤ 2 * s := le_trans (Complex.abs_re_le_norm _) h
  nlinarith [sq_abs ((𝓕 (boxFn s) ξ).re), abs_nonneg ((𝓕 (boxFn s) ξ).re)]

lemma weightFn_le_inv_sq (s : ℝ) (hs : 0 < s) {ξ : ℝ} (hξ : ξ ≠ 0) :
    weightFn s ξ ≤ 1 / (Real.pi ^ 2 * ξ ^ 2) := by
  unfold weightFn
  have h := (norm_fourier_boxFn_le s hs ξ).2 hξ
  have habs : |(𝓕 (boxFn s) ξ).re| ≤ 1 / (Real.pi * |ξ|) := le_trans (Complex.abs_re_le_norm _) h
  have hsq : |(𝓕 (boxFn s) ξ).re| ^ 2 ≤ (1 / (Real.pi * |ξ|)) ^ 2 := by
    nlinarith [abs_nonneg ((𝓕 (boxFn s) ξ).re)]
  rw [sq_abs] at hsq
  have heq : (1 / (Real.pi * |ξ|)) ^ 2 = 1 / (Real.pi ^ 2 * ξ ^ 2) := by
    rw [div_pow, one_pow, mul_pow, sq_abs]
  rwa [heq] at hsq

lemma continuous_weightFn (s : ℝ) : Continuous (weightFn s) := by
  unfold weightFn
  have hc := continuous_fourier_real (integrable_boxFn s)
  fun_prop

lemma integrable_weightFn (s : ℝ) (hs : 0 < s) : Integrable (weightFn s) volume := by
  have hdom : ∀ ξ : ℝ, ‖weightFn s ξ‖ ≤ (8 * s ^ 2 + 2) * (1 + ξ ^ 2)⁻¹ := by
    intro ξ
    rw [Real.norm_of_nonneg (weightFn_nonneg s ξ)]
    by_cases h1 : |ξ| ≤ 1
    · have hsq : ξ ^ 2 ≤ 1 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
      have hpos : 0 < 1 + ξ ^ 2 := by positivity
      have hb := weightFn_le s hs ξ
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]
      nlinarith
    · push Not at h1
      have hne : ξ ≠ 0 := by intro h0; subst h0; simp at h1; linarith
      have hb := weightFn_le_inv_sq s hs hne
      have hsq : 1 < ξ ^ 2 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
      have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
      have hpi2 : 1 ≤ Real.pi ^ 2 := by nlinarith
      have hstep : 1 / (Real.pi ^ 2 * ξ ^ 2) ≤ (8 * s ^ 2 + 2) * (1 + ξ ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
        have h2 : 2 ≤ 8 * s ^ 2 + 2 := by nlinarith [sq_nonneg s]
        have h3 : 1 + ξ ^ 2 ≤ 2 * ξ ^ 2 := by linarith
        have h4 : 2 * ξ ^ 2 ≤ (8 * s ^ 2 + 2) * (Real.pi ^ 2 * ξ ^ 2) := by
          have : ξ ^ 2 ≤ Real.pi ^ 2 * ξ ^ 2 := by nlinarith
          nlinarith
        linarith
      exact le_trans hb hstep
  refine (integrable_inv_one_add_sq.const_mul (8 * s ^ 2 + 2)).mono'
    (continuous_weightFn s).aestronglyMeasurable (Eventually.of_forall hdom)

lemma exists_s_weightFn_pos {a : ℝ} (ha : 0 < a) (r : ℝ) :
    ∃ s ∈ Set.Ioc 0 (a / 10), 0 < weightFn s r := by
  by_cases hr : r = 0
  · subst hr
    refine ⟨a / 10, ⟨by positivity, le_rfl⟩, ?_⟩
    unfold weightFn
    rw [fourier_boxFn (a / 10) (by positivity) 0, if_pos rfl]
    simp only [Complex.ofReal_re]
    positivity
  · set s : ℝ := min (a / 10) (1 / (4 * |r|))
    have hs_pos : 0 < s := lt_min (by positivity) (div_pos zero_lt_one (by positivity))
    refine ⟨s, ⟨hs_pos, min_le_left _ _⟩, ?_⟩
    unfold weightFn
    rw [fourier_boxFn s hs_pos r, if_neg hr, Complex.ofReal_re]
    apply sq_pos_of_ne_zero
    apply div_ne_zero _ (mul_ne_zero Real.pi_ne_zero hr)
    have habs_le : 2 * Real.pi * s * |r| ≤ Real.pi / 2 := by
      have hs_le : s ≤ 1 / (4 * |r|) := min_le_right _ _
      have hr_pos : 0 < |r| := abs_pos.mpr hr
      have h1 : s * |r| ≤ 1 / 4 := by
        have hmul := mul_le_mul_of_nonneg_right hs_le hr_pos.le
        have heq : 1 / (4 * |r|) * |r| = 1 / 4 := by field_simp [hr_pos.ne']
        linarith
      nlinarith [Real.pi_pos]
    have habs_pos : 0 < 2 * Real.pi * s * |r| := by positivity
    have hsin_pos : 0 < Real.sin (2 * Real.pi * s * |r|) :=
      Real.sin_pos_of_pos_of_lt_pi habs_pos (by linarith [Real.pi_pos])
    rcases lt_or_gt_of_ne hr with hr_neg | hr_pos
    · have h1 : 2 * Real.pi * s * r = -(2 * Real.pi * s * |r|) := by
        rw [abs_of_neg hr_neg]; ring
      rw [h1, Real.sin_neg]
      linarith
    · have h1 : 2 * Real.pi * s * r = 2 * Real.pi * s * |r| := by
        rw [abs_of_pos hr_pos]
      rw [h1]
      linarith

lemma spectral_sum_shifted_tent_eq_zero {S Λ : Set ℝ} {a : ℝ} (hS_bdd : Bornology.IsBounded S)
    (hS_meas : MeasurableSet S) (hS_vol : volume S = 1) (hΛ_cnt : Λ.Countable)
    (htile : ∀ t : ℝ, HasSum (fun lam : Λ => gFun S (t - lam.1)) 1)
    (ha : 0 < a) (hrho_small : ∫ x, ‖rhoScale S a x‖ ≤ 1 / 2)
    (c : ℝ) {s t : ℝ} (hs : s ∈ Set.Ioc 0 (a / 10)) (ht : t ∈ Set.Ioo (3 * a / 10) (7 * a / 10)) :
    ∑' lam : Λ, ((weightFn s (lam.1 - c) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * ((lam.1 - c : ℝ) : ℂ)) = 0 := by
  let w : ℝ → ℂ := fun ξ =>
    ((weightFn s (ξ - c) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * ((ξ - c : ℝ) : ℂ))
  have hw_cont : Continuous w := by
    have h1 : Continuous (fun ξ : ℝ => ((weightFn s (ξ - c) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((continuous_weightFn s).comp (continuous_id.sub continuous_const))
    have h2 : Continuous (fun ξ : ℝ =>
        Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * ((ξ - c : ℝ) : ℂ))) := by
      fun_prop
    exact h1.mul h2
  have hw_int : Integrable w volume := by
    refine ((integrable_weightFn s hs.1).comp_sub_right c).mono' hw_cont.aestronglyMeasurable ?_
    filter_upwards with ξ
    simp only [w, norm_mul, Complex.norm_real, Real.norm_of_nonneg (weightFn_nonneg s _)]
    have he : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * ((ξ - c : ℝ) : ℂ))‖ = 1 := by
      have h1 : 2 * Real.pi * Complex.I * (t : ℂ) * ((ξ - c : ℝ) : ℂ) =
          Complex.I * ((2 * Real.pi * t * (ξ - c) : ℝ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_exp_I_mul_ofReal]
    rw [he, mul_one]
  -- Compute 𝓕 w y = cexp (-2π i c y) * tentFn s (y - t)
  have hFw_eq : ∀ y : ℝ, 𝓕 w y =
      Complex.exp (-2 * Real.pi * Complex.I * (c : ℂ) * (y : ℂ)) * tentFn s (y - t) := by
    intro y
    rw [fourier_real_eq]
    have hshift := integral_sub_right_eq_self (μ := volume)
      (fun u : ℝ => Complex.exp (-2 * Real.pi * Complex.I * ((u + c : ℝ) : ℂ) * (y : ℂ)) *
        (((weightFn s u : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (u : ℂ)))) c
    have hrew : (fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (v : ℂ) * (y : ℂ)) * w v) =
        fun v : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (((v - c) + c : ℝ) : ℂ) * (y : ℂ)) *
          (((weightFn s (v - c) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * ((v - c : ℝ) : ℂ))) := by
      funext v; simp [w]
    rw [hrew, hshift]
    have hfac : (fun u : ℝ => Complex.exp (-2 * Real.pi * Complex.I * ((u + c : ℝ) : ℂ) * (y : ℂ)) *
        (((weightFn s u : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (u : ℂ)))) =
        fun u : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (c : ℂ) * (y : ℂ)) *
          (Complex.exp (2 * Real.pi * Complex.I * (u : ℂ) * ((t - y : ℝ) : ℂ)) * 𝓕 (tentFn s) u) := by
      funext u
      rw [← weightFn_ofReal_eq s hs.1 u]
      have hexp : Complex.exp (-2 * Real.pi * Complex.I * ((u + c : ℝ) : ℂ) * (y : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (u : ℂ)) =
          Complex.exp (-2 * Real.pi * Complex.I * (c : ℂ) * (y : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * (u : ℂ) * ((t - y : ℝ) : ℂ)) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1; push_cast; ring
      calc
        Complex.exp (-2 * Real.pi * Complex.I * ((u + c : ℝ) : ℂ) * (y : ℂ)) *
            (((weightFn s u : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (u : ℂ)))
            = (Complex.exp (-2 * Real.pi * Complex.I * ((u + c : ℝ) : ℂ) * (y : ℂ)) *
                Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * (u : ℂ))) * ((weightFn s u : ℝ) : ℂ) := by ring
        _ = (Complex.exp (-2 * Real.pi * Complex.I * (c : ℂ) * (y : ℂ)) *
                Complex.exp (2 * Real.pi * Complex.I * (u : ℂ) * ((t - y : ℝ) : ℂ))) * ((weightFn s u : ℝ) : ℂ) := by
            rw [hexp]
        _ = _ := by ring
    rw [hfac, integral_const_mul]
    congr 1
    have hinv_tent : 𝓕⁻ (𝓕 (tentFn s)) (t - y) = tentFn s (t - y) := by
      have hFt_int : Integrable (𝓕 (tentFn s)) volume := by
        have heq : 𝓕 (tentFn s) = fun u => ((weightFn s u : ℝ) : ℂ) := by
          funext u; exact (weightFn_ofReal_eq s hs.1 u).symm
        rw [heq]; exact (integrable_weightFn s hs.1).ofReal
      exact congrFun ((continuous_tentFn s).fourierInv_fourier_eq (integrable_tentFn s) hFt_int) (t - y)
    rw [fourierInv_real_eq] at hinv_tent
    rw [hinv_tent, show t - y = -(y - t) by ring, tentFn_even]
  have hFw_int : Integrable (𝓕 w) volume := by
    have heq : 𝓕 w = fun y : ℝ =>
        Complex.exp (-2 * Real.pi * Complex.I * (c : ℂ) * (y : ℂ)) * tentFn s (y - t) :=
      funext hFw_eq
    rw [heq]
    refine ((integrable_tentFn s).comp_sub_right t).norm.mono' ?_ ?_
    · have hc1 : Continuous (fun y : ℝ => Complex.exp (-2 * Real.pi * Complex.I * (c : ℂ) * (y : ℂ))) := by
        fun_prop
      have hc2 : Continuous (fun y : ℝ => tentFn s (y - t)) :=
        (continuous_tentFn s).comp (continuous_id.sub continuous_const)
      exact hc1.aestronglyMeasurable.mul hc2.aestronglyMeasurable
    · filter_upwards with y
      rw [norm_mul]
      have he : ‖Complex.exp (-2 * Real.pi * Complex.I * (c : ℂ) * (y : ℂ))‖ = 1 := by
        have h1 : -2 * Real.pi * Complex.I * (c : ℂ) * (y : ℂ) =
            Complex.I * ((-2 * Real.pi * c * y : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_exp_I_mul_ofReal]
      rw [he, one_mul]
  have hFw_supp : ∀ y : ℝ, y ∉ Set.Ioo 0 a → 𝓕 w y = 0 := by
    intro y hy
    rw [hFw_eq y]
    have hdist : 2 * s ≤ |y - t| := by
      rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hy
      rcases hy with hle | hge
      · have h1 : t - y ≥ 3 * a / 10 := by linarith [ht.1]
        have h2 : |y - t| = t - y := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith [hs.2]
      · have h1 : y - t ≥ 3 * a / 10 := by linarith [ht.2]
        have h2 : |y - t| = y - t := abs_of_nonneg (by linarith)
        linarith [hs.2]
    rw [tentFn_eq_zero_of_two_mul_le_abs hs.1 hdist, mul_zero]
  exact spectral_gap_annihilation hS_bdd hS_meas hS_vol hΛ_cnt htile ha hrho_small
    hw_cont hw_int hFw_int hFw_supp


/- ## Section 4: Cayley Transform, Maximum Modulus, and Bohr Uniqueness -/

lemma exp_sum_coeff_eq_zero_of_vanish_Ioo {ι : Type*} [Countable ι]
    {x : ι → ℝ} {c : ι → ℂ} {u v : ℝ} (huv : u < v)
    (hx_nn : ∀ i, 0 ≤ x i) (hx_inj : Function.Injective x)
    (hc : Summable fun i => ‖c i‖)
    (hvan : ∀ t ∈ Set.Ioo u v,
      ∑' i : ι, c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * (t : ℂ)) = 0) :
    ∀ i : ι, c i = 0 := by
  classical
  let G : ℂ → ℂ := fun z =>
    ∑' i : ι, c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * z)
  have hre_exp : ∀ (i : ι) (z : ℂ),
      (2 * Real.pi * Complex.I * (x i : ℂ) * z).re = -2 * Real.pi * x i * z.im := by
    intro i z
    simp [Complex.mul_re, Complex.mul_im]
  have hterm_norm : ∀ (i : ι) (z : ℂ),
      ‖c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * z)‖ =
        ‖c i‖ * Real.exp (-2 * Real.pi * x i * z.im) := by
    intro i z
    rw [norm_mul, Complex.norm_exp, hre_exp]
  have hterm_le : ∀ (i : ι) (z : ℂ), 0 ≤ z.im →
      ‖c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * z)‖ ≤ ‖c i‖ := by
    intro i z hz
    rw [hterm_norm]
    have h1 : Real.exp (-2 * Real.pi * x i * z.im) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ 2 * Real.pi * x i * z.im := by
        have hpi : 0 ≤ 2 * Real.pi := by positivity
        have hxi := hx_nn i
        positivity
      linarith
    simpa using mul_le_mul_of_nonneg_left h1 (norm_nonneg (c i))
  -- 4.1: Continuity and boundedness of G on closed upper half-plane
  have hG_cont : ContinuousOn G {z : ℂ | 0 ≤ z.im} := by
    refine continuousOn_tsum (u := fun i => ‖c i‖) (fun i => ?_) hc
      (fun i z hz => hterm_le i z hz)
    exact (Continuous.continuousOn (by fun_prop))
  set M_G : ℝ := ∑' i : ι, ‖c i‖
  have hG_bdd : ∀ z : ℂ, 0 ≤ z.im → ‖G z‖ ≤ M_G := by
    intro z hz
    have hsum_z : Summable (fun i : ι =>
        ‖c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * z)‖) :=
      hc.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hterm_le i z hz)
    calc
      ‖G z‖ ≤ ∑' i : ι, ‖c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * z)‖ :=
        norm_tsum_le_tsum_norm hsum_z
      _ ≤ ∑' i : ι, ‖c i‖ := hsum_z.tsum_le_tsum (fun i => hterm_le i z hz) hc
  -- 4.2: Differentiability of G on open upper half-plane
  have hG_diff : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} := by
    intro z₀ hz₀
    set r : ℝ := z₀.im / 2
    have hr : 0 < r := half_pos hz₀
    let U : Set ℂ := {z : ℂ | r < z.im}
    have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
    have hU_conv : Convex ℝ U := by
      intro z hz w hw a b ha hb hab
      change r < (a • z + b • w).im
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      have hz' : r < z.im := hz
      have hw' : r < w.im := hw
      have h1 : a * r ≤ a * z.im := mul_le_mul_of_nonneg_left hz'.le ha
      have h2 : b * r ≤ b * w.im := mul_le_mul_of_nonneg_left hw'.le hb
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        rw [ha0, hb1]; linarith
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have h1' : a * r < a * z.im := mul_lt_mul_of_pos_left hz' ha_pos
        nlinarith
    have hz₀U : z₀ ∈ U := by
      change r < z₀.im
      dsimp only [r]
      have hz₀' : 0 < z₀.im := hz₀
      linarith
    let g' : ι → ℂ → ℂ := fun i z =>
      c i * (2 * Real.pi * Complex.I * (x i : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * z)
    have hderiv_i : ∀ i z, z ∈ U →
        HasDerivAt (fun w => c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * w))
          (g' i z) z := by
      intro i z _
      have h1 : HasDerivAt (fun w : ℂ => 2 * Real.pi * Complex.I * (x i : ℂ) * w)
          (2 * Real.pi * Complex.I * (x i : ℂ)) z := by
        simpa using (hasDerivAt_id z).const_mul (2 * Real.pi * Complex.I * (x i : ℂ))
      have h2 := h1.cexp.const_mul (c i)
      have heq : c i * (Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * z) *
          (2 * Real.pi * Complex.I * (x i : ℂ))) = g' i z := by
        simp only [g']; ring
      rwa [heq] at h2
    have hbound_i : ∀ i z, z ∈ U → ‖g' i z‖ ≤ (1 / r) * ‖c i‖ := by
      intro i z hz
      change r < z.im at hz
      have hxi : 0 ≤ x i := hx_nn i
      set y : ℝ := 2 * Real.pi * x i
      have hy : 0 ≤ y := by positivity
      have hnorm_g' : ‖g' i z‖ = ‖c i‖ * (y * Real.exp (-y * z.im)) := by
        simp only [g', norm_mul, Complex.norm_exp, hre_exp, Complex.norm_ofNat,
          Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one,
          Real.norm_of_nonneg hxi]
        simp only [y]; ring_nf
      rw [hnorm_g']
      have hexp_le : y * Real.exp (-y * z.im) ≤ 1 / r := by
        have h1 : Real.exp (-y * z.im) ≤ Real.exp (-r * y) := by
          apply Real.exp_le_exp.mpr; nlinarith
        have h2 : r * y ≤ Real.exp (r * y) := by
          have := Real.add_one_le_exp (r * y); linarith
        have h3 : y * Real.exp (-r * y) ≤ 1 / r := by
          rw [show -r * y = -(r * y) by ring, Real.exp_neg, ← div_eq_mul_inv,
            div_le_div_iff₀ (Real.exp_pos _) hr]
          linarith
        exact le_trans (mul_le_mul_of_nonneg_left h1 hy) h3
      have := mul_le_mul_of_nonneg_left hexp_le (norm_nonneg (c i))
      linarith
    have hsum0 : Summable (fun i : ι =>
        c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * z₀)) :=
      Summable.of_norm_bounded hc (fun i => hterm_le i z₀ (le_of_lt hz₀))
    have hhd := hasDerivAt_tsum_of_isPreconnected (hc.mul_left (1 / r)) hU_open
      hU_conv.isPreconnected hderiv_i hbound_i hz₀U hsum0 hz₀U
    exact hhd.differentiableAt.differentiableWithinAt
  -- 4.3: Cayley map Φ from unit disk to upper half-plane
  set m : ℝ := (u + v) / 2
  set s₀ : ℝ := (v - u) / 2
  have hs₀ : 0 < s₀ := by unfold s₀; linarith
  let Φ : ℂ → ℂ := fun w => (m : ℂ) + (s₀ : ℂ) * Complex.I * ((1 + w) / (1 - w))
  have hΦ_im : ∀ w : ℂ, w ≠ 1 →
      (Φ w).im = s₀ * (1 - (w.re ^ 2 + w.im ^ 2)) / ((1 - w.re) ^ 2 + w.im ^ 2) := by
    intro w hw
    have hden : 0 < (1 - w.re) ^ 2 + w.im ^ 2 := by
      have hne : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw.symm
      have hns := Complex.normSq_pos.mpr hne
      simpa [Complex.normSq_apply, sq] using hns
    have h1 : (1 - w).normSq = (1 - w.re) ^ 2 + w.im ^ 2 := by
      simp [Complex.normSq_apply, sq]
    simp only [Φ, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
      mul_one, zero_mul, add_zero, Complex.div_re, h1]
    simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
      Complex.sub_im, zero_add, zero_sub]
    ring
  have hΦ_re : ∀ w : ℂ, w ≠ 1 →
      (Φ w).re = m - s₀ * (2 * w.im) / ((1 - w.re) ^ 2 + w.im ^ 2) := by
    intro w hw
    have h1 : (1 - w).normSq = (1 - w.re) ^ 2 + w.im ^ 2 := by
      simp [Complex.normSq_apply, sq]
    simp only [Φ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one,
      zero_mul, add_zero, zero_sub, Complex.div_im, h1]
    simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
      Complex.sub_im, zero_add, zero_sub]
    ring
  have hnorm_sq_eq : ∀ w : ℂ, w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
    intro w
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq, sq]
  have hΦ_ball : ∀ w ∈ Metric.ball (0 : ℂ) 1, 0 < (Φ w).im := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hw1 : w ≠ 1 := by intro h; subst h; simp at hw
    rw [hΦ_im w hw1, hnorm_sq_eq]
    have hden : 0 < (1 - w.re) ^ 2 + w.im ^ 2 := by
      have hns := Complex.normSq_pos.mpr (sub_ne_zero.mpr hw1.symm)
      simpa [Complex.normSq_apply, sq] using hns
    have hnum : 0 < 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    exact div_pos (mul_pos hs₀ hnum) hden
  have hΦ_closedBall : ∀ w ∈ Metric.closedBall (0 : ℂ) 1, w ≠ 1 → 0 ≤ (Φ w).im := by
    intro w hw hw1
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    rw [hΦ_im w hw1, hnorm_sq_eq]
    have hden : 0 < (1 - w.re) ^ 2 + w.im ^ 2 := by
      have hns := Complex.normSq_pos.mpr (sub_ne_zero.mpr hw1.symm)
      simpa [Complex.normSq_apply, sq] using hns
    have hnum : 0 ≤ 1 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    exact div_nonneg (mul_nonneg hs₀.le hnum) hden.le
  have hΦ_left_arc : ∀ w : ℂ, ‖w‖ = 1 → w.re < 0 →
      Φ w = ((Φ w).re : ℂ) ∧ (Φ w).re ∈ Set.Ioo u v := by
    intro w hw hre
    have hw1 : w ≠ 1 := by intro h; subst h; simp at hre; linarith
    have him0 : (Φ w).im = 0 := by
      rw [hΦ_im w hw1, hnorm_sq_eq, hw]; ring
    refine ⟨Complex.ext rfl (by simp [him0]), ?_⟩
    rw [hΦ_re w hw1]
    have hden_eq : (1 - w.re) ^ 2 + w.im ^ 2 = 2 - 2 * w.re := by
      have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by rw [hnorm_sq_eq, hw, one_pow]
      nlinarith
    have hden_gt : 2 < (1 - w.re) ^ 2 + w.im ^ 2 := by linarith
    have him_le : |w.im| ≤ 1 := by
      rw [← hw]; exact Complex.abs_im_le_norm w
    have hquot : |s₀ * (2 * w.im) / ((1 - w.re) ^ 2 + w.im ^ 2)| < s₀ := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos hs₀, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by linarith : 0 < (1 - w.re) ^ 2 + w.im ^ 2)]
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    have habs := abs_lt.mp hquot
    constructor <;> dsimp only [m, s₀] at * <;> linarith
  -- 4.4: Bounded holomorphic H on ball 0 1, continuous on closedBall 0 1
  let H : ℂ → ℂ := fun w => if w = 1 then 0 else (w - 1) * G (Φ w)
  have hΦ_diff : DifferentiableOn ℂ Φ {w : ℂ | w ≠ 1} := by
    intro w hw
    have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr hw.symm
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (1 + z) / (1 - z)) w :=
      ((differentiableAt_const (1 : ℂ)).add differentiableAt_id).div
        ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) hden
    exact (((differentiableAt_const _).add ((differentiableAt_const _).mul h1))).differentiableWithinAt
  have hH_diff : DifferentiableOn ℂ H (Metric.ball (0 : ℂ) 1) := by
    have hEq : Set.EqOn H (fun w => (w - 1) * G (Φ w)) (Metric.ball (0 : ℂ) 1) := by
      intro w hw
      have hw1 : w ≠ 1 := by
        intro h; subst h; rw [Metric.mem_ball, dist_zero_right, norm_one] at hw; exact lt_irrefl 1 hw
      simp [H, hw1]
    refine DifferentiableOn.congr ?_ hEq
    intro w hw
    have hw1 : w ≠ 1 := by
      intro h; subst h; rw [Metric.mem_ball, dist_zero_right, norm_one] at hw; exact lt_irrefl 1 hw
    have hΦ_at : DifferentiableAt ℂ Φ w :=
      (hΦ_diff w hw1).differentiableAt (isOpen_ne.mem_nhds hw1)
    have hG_at : DifferentiableAt ℂ G (Φ w) :=
      (hG_diff (Φ w) (hΦ_ball w hw)).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds (hΦ_ball w hw))
    exact ((differentiableAt_id.sub (differentiableAt_const 1)).mul (hG_at.comp w hΦ_at)).differentiableWithinAt
  have hH_cont : ContinuousOn H (Metric.closedBall (0 : ℂ) 1) := by
    intro w₀ hw₀
    by_cases hw1 : w₀ = 1
    · subst hw1
      rw [ContinuousWithinAt, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      have hM_nn : 0 ≤ M_G := tsum_nonneg fun _ => norm_nonneg _
      refine ⟨ε / (M_G + 1), div_pos hε (by linarith), fun w hw hdist => ?_⟩
      simp only [H, ↓reduceIte, dist_zero_right]
      split_ifs with h
      · simpa using hε
      · rw [norm_mul]
        have hG_le : ‖G (Φ w)‖ ≤ M_G := hG_bdd (Φ w) (hΦ_closedBall w hw h)
        have h1 : ‖w - 1‖ * ‖G (Φ w)‖ ≤ ‖w - 1‖ * M_G :=
          mul_le_mul_of_nonneg_left hG_le (norm_nonneg _)
        rw [dist_eq_norm] at hdist
        have h2 : ‖w - 1‖ * M_G < (ε / (M_G + 1)) * (M_G + 1) := by
          have : ‖w - 1‖ * M_G ≤ ‖w - 1‖ * (M_G + 1) := by nlinarith [norm_nonneg (w - 1)]
          have : ‖w - 1‖ * (M_G + 1) < (ε / (M_G + 1)) * (M_G + 1) :=
            mul_lt_mul_of_pos_right hdist (by linarith)
          linarith
        rw [div_mul_cancel₀ _ (by linarith : M_G + 1 ≠ 0)] at h2
        linarith
    · have hΦ_cont_at : ContinuousAt Φ w₀ :=
        (hΦ_diff w₀ hw1).differentiableAt (isOpen_ne.mem_nhds hw1) |>.continuousAt
      have hmaps : MapsTo Φ (Metric.closedBall (0 : ℂ) 1 ∩ {w | w ≠ 1}) {z : ℂ | 0 ≤ z.im} :=
        fun w hw => hΦ_closedBall w hw.1 hw.2
      have hG_at : ContinuousWithinAt (fun w => (w - 1) * G (Φ w))
          (Metric.closedBall (0 : ℂ) 1 ∩ {w | w ≠ 1}) w₀ := by
        refine ((continuousAt_id.sub continuousAt_const).continuousWithinAt).mul ?_
        exact (hG_cont (Φ w₀) (hΦ_closedBall w₀ hw₀ hw1)).comp hΦ_cont_at.continuousWithinAt hmaps
      have hnhds : Metric.closedBall (0 : ℂ) 1 ∩ {w | w ≠ 1} ∈ 𝓝[Metric.closedBall (0 : ℂ) 1] w₀ :=
        inter_mem_nhdsWithin _ (isOpen_ne.mem_nhds hw1)
      have hcont_raw : ContinuousWithinAt (fun w => (w - 1) * G (Φ w)) (Metric.closedBall (0 : ℂ) 1) w₀ :=
        hG_at.mono_of_mem_nhdsWithin hnhds
      refine hcont_raw.congr_of_eventuallyEq ?_ (by simp [H, hw1])
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hw1)] with w _ hne
      simp [H, hne]
  -- 4-fold rotated product P vanishes identically on frontier (ball 0 1) = sphere 0 1
  let P : ℂ → ℂ := fun w => H w * H (-w) * H (Complex.I * w) * H (-Complex.I * w)
  have hrot_maps_ball : ∀ c : ℂ, ‖c‖ = 1 →
      MapsTo (fun w : ℂ => c * w) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro c hc w hw
    rw [Metric.mem_ball, dist_zero_right] at hw ⊢
    rw [norm_mul, hc, one_mul]; exact hw
  have hrot_maps_cl : ∀ c : ℂ, ‖c‖ = 1 →
      MapsTo (fun w : ℂ => c * w) (Metric.closedBall (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) := by
    intro c hc w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw ⊢
    rw [norm_mul, hc, one_mul]; exact hw
  have hP_diff : DifferentiableOn ℂ P (Metric.ball (0 : ℂ) 1) := by
    have h1 : DifferentiableOn ℂ (fun w => H (-w)) (Metric.ball (0 : ℂ) 1) :=
      hH_diff.comp differentiableOn_id.neg (by simpa using hrot_maps_ball (-1) (by simp))
    have h2 : DifferentiableOn ℂ (fun w => H (Complex.I * w)) (Metric.ball (0 : ℂ) 1) :=
      hH_diff.comp ((differentiableOn_const _).mul differentiableOn_id) (hrot_maps_ball Complex.I (by simp))
    have h3 : DifferentiableOn ℂ (fun w => H (-Complex.I * w)) (Metric.ball (0 : ℂ) 1) :=
      hH_diff.comp ((differentiableOn_const _).mul differentiableOn_id) (hrot_maps_ball (-Complex.I) (by simp))
    exact ((hH_diff.mul h1).mul h2).mul h3
  have hP_cont : ContinuousOn P (Metric.closedBall (0 : ℂ) 1) := by
    have h1 : ContinuousOn (fun w => H (-w)) (Metric.closedBall (0 : ℂ) 1) :=
      hH_cont.comp continuousOn_id.neg (by simpa using hrot_maps_cl (-1) (by simp))
    have h2 : ContinuousOn (fun w => H (Complex.I * w)) (Metric.closedBall (0 : ℂ) 1) :=
      hH_cont.comp ((continuousOn_const.mul continuousOn_id)) (hrot_maps_cl Complex.I (by simp))
    have h3 : ContinuousOn (fun w => H (-Complex.I * w)) (Metric.closedBall (0 : ℂ) 1) :=
      hH_cont.comp ((continuousOn_const.mul continuousOn_id)) (hrot_maps_cl (-Complex.I) (by simp))
    exact ((hH_cont.mul h1).mul h2).mul h3
  have hH_van_left : ∀ w : ℂ, ‖w‖ = 1 → w.re < 0 → H w = 0 := by
    intro w hw hre
    have hw1 : w ≠ 1 := by intro h; subst h; simp at hre; linarith
    obtain ⟨hΦ_eq, hΦ_Ioo⟩ := hΦ_left_arc w hw hre
    simp only [H, hw1, ↓reduceIte]
    rw [hΦ_eq]
    dsimp only [G]
    rw [hvan (Φ w).re hΦ_Ioo, mul_zero]
  have hP_frontier : ∀ w ∈ frontier (Metric.ball (0 : ℂ) 1), ‖P w‖ ≤ 0 := by
    intro w hw
    rw [frontier_ball (0 : ℂ) one_ne_zero, Metric.mem_sphere, dist_zero_right] at hw
    have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by rw [hnorm_sq_eq, hw, one_pow]
    have hP0 : P w = 0 := by
      unfold P
      by_cases h1 : w.re < 0
      · rw [hH_van_left w hw h1]; ring
      · by_cases h2 : 0 < w.re
        · have hneg : (-w).re < 0 := by simp; linarith
          rw [hH_van_left (-w) (by simp [hw]) hneg]; ring
        · have hre0 : w.re = 0 := by linarith
          by_cases h3 : 0 < w.im
          · have hI : (Complex.I * w).re < 0 := by simp [Complex.mul_re]; linarith
            rw [hH_van_left (Complex.I * w) (by simp [hw]) hI]; ring
          · have h4 : w.im < 0 := by
              by_contra hge; push Not at hge
              have him0 : w.im = 0 := by linarith
              rw [hre0, him0] at hsq; norm_num at hsq
            have hnI : (-Complex.I * w).re < 0 := by simp [Complex.mul_re]; linarith
            rw [hH_van_left (-Complex.I * w) (by simp [hw]) hnI]; ring
    rw [hP0, norm_zero]
  have hP_zero_ball : ∀ w ∈ Metric.ball (0 : ℂ) 1, P w = 0 := by
    intro w hw
    have hdiffcl : DiffContOnCl ℂ P (Metric.ball (0 : ℂ) 1) :=
      ⟨hP_diff, by rwa [closure_ball (0 : ℂ) one_ne_zero]⟩
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
      hdiffcl hP_frontier (subset_closure hw)
    exact norm_le_zero_iff.mp hle
  -- Identity theorem: H vanishes identically on ball 0 1
  have hH_zero_ball : Set.EqOn H 0 (Metric.ball (0 : ℂ) 1) := by
    by_contra hne
    have hU_conn : IsPreconnected (Metric.ball (0 : ℂ) 1) := (convex_ball (0 : ℂ) 1).isPreconnected
    have h0U : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self zero_lt_one
    have hH_an : AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) 1) :=
      (Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball).mpr hH_diff
    have hev : ∀ c : ℂ, ‖c‖ = 1 → ∀ᶠ w in 𝓝[≠] (0 : ℂ), H (c * w) ≠ 0 := by
      intro c hc
      have hc0 : c ≠ 0 := by intro h; subst h; simp at hc
      have hHc_an : AnalyticOnNhd ℂ (fun w => H (c * w)) (Metric.ball (0 : ℂ) 1) := by
        rw [Complex.analyticOnNhd_iff_differentiableOn Metric.isOpen_ball]
        exact hH_diff.comp ((differentiableOn_const c).mul differentiableOn_id) (hrot_maps_ball c hc)
      by_contra hnot
      rw [Filter.not_eventually] at hnot
      have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), H (c * w) = 0 :=
        hnot.mono fun _ h => Classical.not_not.mp h
      have hzero := hHc_an.eqOn_zero_of_preconnected_of_frequently_eq_zero hU_conn h0U hfreq
      apply hne
      intro w hw
      have hcw : c⁻¹ * w ∈ Metric.ball (0 : ℂ) 1 :=
        hrot_maps_ball c⁻¹ (by rw [norm_inv, hc, inv_one]) hw
      have h0w := hzero hcw
      dsimp only [Pi.zero_apply] at h0w ⊢
      rwa [mul_inv_cancel_left₀ hc0] at h0w
    have hev1 := hev 1 (by simp)
    have hev2 := hev (-1) (by simp)
    have hev3 := hev Complex.I (by simp)
    have hev4 := hev (-Complex.I) (by simp)
    have hball_ev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ Metric.ball (0 : ℂ) 1 :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 zero_lt_one)
    have hall := hball_ev.and (hev1.and (hev2.and (hev3.and hev4)))
    obtain ⟨w, hw_ball, h1, h2, h3, h4⟩ := hall.exists
    have hPw := hP_zero_ball w hw_ball
    simp only [P, one_mul, neg_one_mul] at hPw h1 h2 h3 h4
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4 hPw
  -- Surjectivity of Φ onto open upper half-plane -> G = 0 on open upper half-plane
  have hG_uhp : ∀ z : ℂ, 0 < z.im → G z = 0 := by
    intro z hz
    set ζ : ℂ := (z - (m : ℂ)) / ((s₀ : ℂ) * Complex.I)
    have hζ_re : 0 < ζ.re := by
      have hsI : ((s₀ : ℂ) * Complex.I).normSq = s₀ ^ 2 := by
        simp [Complex.normSq_apply, sq]
      have hre_calc : ζ.re = z.im / s₀ := by
        simp only [ζ, Complex.div_re, hsI, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, sub_zero, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, zero_mul, add_zero]
        field_simp [hs₀.ne']
        ring
      rw [hre_calc]
      exact div_pos hz hs₀
    have hζ1 : ζ + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this; linarith
    set w : ℂ := (ζ - 1) / (ζ + 1)
    have hw_ball : w ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, norm_div, div_lt_one (norm_pos_iff.mpr hζ1)]
      have hsq_lt : ‖ζ - 1‖ ^ 2 < ‖ζ + 1‖ ^ 2 := by
        rw [← hnorm_sq_eq, ← hnorm_sq_eq]
        simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero,
          Complex.add_re, Complex.add_im, add_zero]
        nlinarith
      nlinarith [norm_nonneg (ζ - 1), norm_nonneg (ζ + 1)]
    have hw1 : w ≠ 1 := by
      intro h; rw [h, Metric.mem_ball, dist_zero_right, norm_one] at hw_ball; exact lt_irrefl 1 hw_ball
    have hΦw : Φ w = z := by
      have h1mw : 1 - w = 2 / (ζ + 1) := by
        dsimp only [w]; field_simp [hζ1]; ring
      have h1pw : 1 + w = (2 * ζ) / (ζ + 1) := by
        dsimp only [w]; field_simp [hζ1]; ring
      have hquot : (1 + w) / (1 - w) = ζ := by
        rw [h1pw, h1mw]
        field_simp [hζ1]
      simp only [Φ, hquot, ζ]
      have hs₀C : (s₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs₀.ne'
      have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
      field_simp [hs₀C, hI]
      ring
    have hHw : H w = 0 := hH_zero_ball hw_ball
    simp only [H, hw1, ↓reduceIte, hΦw] at hHw
    exact (mul_eq_zero.mp hHw).resolve_left (sub_ne_zero.mpr hw1)
  -- Continuity onto real axis: G t = 0 for ALL t : ℝ
  have hG_real : ∀ t : ℝ, G (t : ℂ) = 0 := by
    intro t
    let seq : ℕ → ℂ := fun n => (t : ℂ) + ((((n : ℝ) + 1)⁻¹ : ℝ) : ℂ) * Complex.I
    have hseq_im : ∀ n : ℕ, 0 < (seq n).im := by
      intro n
      simp only [seq, Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero]
      positivity
    have hseq_lim : Tendsto seq atTop (𝓝[ {z : ℂ | 0 ≤ z.im} ] (t : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => (hseq_im n).le⟩
      have h1 : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹ : ℝ)) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1 |>.mul_const Complex.I
      simpa [seq] using tendsto_const_nhds.add h2
    have hG_lim := (hG_cont (t : ℂ) (by simp)).tendsto.comp hseq_lim
    have hG_zero_seq : ∀ n : ℕ, G (seq n) = 0 := fun n => hG_uhp (seq n) (hseq_im n)
    have hconst : Tendsto (fun n : ℕ => G (seq n)) atTop (𝓝 0) := by
      simp_rw [hG_zero_seq]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hG_lim hconst |>.symm |> Eq.symm
  -- 4.5: Bohr mean value extraction
  intro i₀
  let avg : ℝ → ι → ℂ := fun T i =>
    ((2 * T : ℝ) : ℂ)⁻¹ *
      ∫ t in Set.Icc (-T) T, Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ))
  have havg_sum_zero : ∀ T : ℝ, 0 < T → ∑' i : ι, c i * avg T i = 0 := by
    intro T hT
    have h0 : ∫ t in Set.Icc (-T) T,
        Complex.exp (-2 * Real.pi * Complex.I * (x i₀ : ℂ) * (t : ℂ)) * G (t : ℂ) = 0 := by
      have : ∀ t : ℝ, Complex.exp (-2 * Real.pi * Complex.I * (x i₀ : ℂ) * (t : ℂ)) * G (t : ℂ) = 0 := by
        intro t; rw [hG_real t, mul_zero]
      simp_rw [this, integral_zero]
    have htsum_in : ∀ t : ℝ,
        Complex.exp (-2 * Real.pi * Complex.I * (x i₀ : ℂ) * (t : ℂ)) * G (t : ℂ) =
        ∑' i : ι, c i * Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ)) := by
      intro t
      have hs : Summable (fun i : ι =>
          c i * Complex.exp (2 * Real.pi * Complex.I * (x i : ℂ) * (t : ℂ))) :=
        Summable.of_norm_bounded hc (fun i => hterm_le i (t : ℂ) (by simp))
      simp only [G]
      rw [← hs.tsum_mul_left]
      congr 1; funext i
      rw [← mul_assoc, mul_comm (Complex.exp _) (c i), mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    simp_rw [htsum_in] at h0
    have hint_i : ∀ i : ι, Integrable (fun t : ℝ =>
        c i * Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ)))
        (volume.restrict (Set.Icc (-T) T)) := by
      intro i
      exact (Continuous.integrableOn_Icc (by fun_prop))
    have hnorm_int : ∀ i : ι, ∫ t in Set.Icc (-T) T,
        ‖c i * Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ))‖ =
        (2 * T) * ‖c i‖ := by
      intro i
      have h1 : ∀ t : ℝ,
          ‖c i * Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ))‖ = ‖c i‖ := by
        intro t
        rw [norm_mul]
        have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ))‖ = 1 := by
          have : 2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ) =
              Complex.I * ((2 * Real.pi * (x i - x i₀) * t : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.norm_exp_I_mul_ofReal]
        rw [he, mul_one]
      simp_rw [h1]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ T - -T), smul_eq_mul]
      ring
    have hsum_norm : Summable (fun i : ι => ∫ t in Set.Icc (-T) T,
        ‖c i * Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ))‖) := by
      simp_rw [hnorm_int]
      exact hc.mul_left (2 * T)
    rw [← integral_tsum_of_summable_integral_norm hint_i hsum_norm] at h0
    have hpull : ∑' i : ι, c i * avg T i =
        ((2 * T : ℝ) : ℂ)⁻¹ * ∑' i : ι, ∫ t in Set.Icc (-T) T,
          c i * Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ)) := by
      rw [← tsum_mul_left]
      congr 1; funext i
      simp only [avg, integral_const_mul]
      ring
    rw [hpull, h0, mul_zero]
  have havg_bound : ∀ T : ℝ, 0 < T → ∀ i : ι, ‖c i * avg T i‖ ≤ ‖c i‖ := by
    intro T hT i
    rw [norm_mul]
    have havg_le : ‖avg T i‖ ≤ 1 := by
      simp only [avg, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ 2 * T)]
      have hint_le : ‖∫ t in Set.Icc (-T) T,
          Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ))‖ ≤ 2 * T := by
        calc
          ‖∫ t in Set.Icc (-T) T, Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ))‖
              ≤ ∫ t in Set.Icc (-T) T, ‖Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ))‖ :=
                norm_integral_le_integral_norm _
          _ = ∫ _t in Set.Icc (-T) T, (1 : ℝ) := by
                congr 1; funext t
                have : 2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ) =
                    Complex.I * ((2 * Real.pi * (x i - x i₀) * t : ℝ) : ℂ) := by push_cast; ring
                rw [this, Complex.norm_exp_I_mul_ofReal]
          _ = 2 * T := by
                simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
                  ENNReal.toReal_ofReal (by linarith : 0 ≤ T - -T), smul_eq_mul, mul_one]
                ring
      rw [inv_mul_le_iff₀ (by positivity)]
      linarith
    simpa using mul_le_mul_of_nonneg_left havg_le (norm_nonneg (c i))
  have havg_lim : ∀ i : ι, Tendsto (fun T : ℝ => c i * avg T i) atTop
      (𝓝 (if i = i₀ then c i₀ else 0)) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      rw [if_pos rfl]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
      simp only [avg, sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ T - -T),
        Complex.real_smul, mul_one]
      have h2T : ((2 * T : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      have heq : ((T - -T : ℝ) : ℂ) = ((2 * T : ℝ) : ℂ) := by push_cast; ring
      rw [heq, inv_mul_cancel₀ h2T, mul_one]
    · rw [if_neg hi]
      have hne : x i - x i₀ ≠ 0 := sub_ne_zero.mpr (fun h => hi (hx_inj h))
      have hlim0 : Tendsto (fun T : ℝ => ‖c i * avg T i‖) atTop (𝓝 0) := by
        refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
          (show Tendsto (fun T : ℝ => ‖c i‖ / (2 * Real.pi * |x i - x i₀|) * T⁻¹) atTop (𝓝 0) by
            simpa using tendsto_inv_atTop_zero.const_mul (‖c i‖ / (2 * Real.pi * |x i - x i₀|)))
        filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T (hT : 0 < T)
        have hbox : ∫ t in Set.Icc (-T) T,
            Complex.exp (2 * Real.pi * Complex.I * ((x i - x i₀ : ℝ) : ℂ) * (t : ℂ)) =
            𝓕 (boxFn T) (-(x i - x i₀)) := by
          rw [fourier_real_eq]
          unfold boxFn
          rw [← integral_indicator measurableSet_Icc]
          congr 1; funext t
          by_cases ht : t ∈ Set.Icc (-T) T
          · simp only [Set.indicator_of_mem ht, mul_one]
            congr 1; push_cast; ring
          · simp [Set.indicator_of_notMem ht]
        have hbn := (norm_fourier_boxFn_le T hT (-(x i - x i₀))).2 (neg_ne_zero.mpr hne)
        rw [abs_neg] at hbn
        have h2T_norm : ‖((2 * T : ℝ) : ℂ)‖ = 2 * T := by
          rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        simp only [avg, norm_mul, norm_inv, h2T_norm, hbox]
        calc
          ‖c i‖ * ((2 * T)⁻¹ * ‖𝓕 (boxFn T) (-(x i - x i₀))‖)
              ≤ ‖c i‖ * ((2 * T)⁻¹ * (1 / (Real.pi * |x i - x i₀|))) := by gcongr
          _ = ‖c i‖ / (2 * Real.pi * |x i - x i₀|) * T⁻¹ := by
                field_simp [hT.ne', Real.pi_ne_zero, (abs_pos.mpr hne).ne']
      exact tendsto_zero_iff_norm_tendsto_zero.mpr hlim0
  have htsum_lim := tendsto_tsum_of_dominated_convergence hc havg_lim
    (by filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T hT; exact havg_bound T hT)
  have htsum_zero : Tendsto (fun T : ℝ => ∑' i : ι, c i * avg T i) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with T hT
    exact (havg_sum_zero T hT).symm
  have heq := tendsto_nhds_unique htsum_lim htsum_zero
  simpa [tsum_ite_eq] using heq


/- ## Section 5: Symbolic Space, Shift-Invariance, Compactness, and Pigeonhole -/

def symPos {SigmaSet : Finset ℝ} (x : ℤ → {σ : ℝ // σ ∈ SigmaSet}) : ℤ → ℝ
  | Int.ofNat n => ∑ k ∈ Finset.range n, (x (k : ℤ)).1
  | Int.negSucc n => - ∑ k ∈ Finset.range (n + 1), (x (-(k : ℤ) - 1)).1

lemma symPos_zero {SigmaSet : Finset ℝ} (x : ℤ → {σ : ℝ // σ ∈ SigmaSet}) :
    symPos x 0 = 0 := by
  simp [symPos]

lemma symPos_succ {SigmaSet : Finset ℝ} (x : ℤ → {σ : ℝ // σ ∈ SigmaSet}) (n : ℤ) :
    symPos x (n + 1) = symPos x n + (x n).1 := by
  cases n with
  | ofNat k =>
    change symPos x (Int.ofNat (k + 1)) = symPos x (Int.ofNat k) + (x (k : ℤ)).1
    simp [symPos, Finset.sum_range_succ]
  | negSucc k =>
    cases k with
    | zero =>
      change symPos x 0 = symPos x (Int.negSucc 0) + (x (-1 : ℤ)).1
      simp [symPos]
    | succ m =>
      have hsucc : Int.negSucc (m + 1) + 1 = Int.negSucc m := by omega
      rw [hsucc]
      simp only [symPos, Finset.sum_range_succ]
      have hidx : (-(↑(m + 1) : ℤ) - 1) = Int.negSucc (m + 1) := by omega
      rw [hidx]
      ring

lemma symPos_shift {SigmaSet : Finset ℝ} (x : ℤ → {σ : ℝ // σ ∈ SigmaSet}) (n : ℤ) :
    symPos (fun k => x (k + 1)) n = symPos x (n + 1) - symPos x 1 := by
  induction n using Int.induction_on with
  | zero => simp [symPos_zero]
  | succ k ih =>
    rw [symPos_succ, ih, show (k : ℤ) + 1 + 1 = ((k : ℤ) + 1) + 1 by ring, symPos_succ x ((k : ℤ) + 1)]
    ring
  | pred k ih =>
    have h1 : symPos (fun m => x (m + 1)) (-(k : ℤ)) =
        symPos (fun m => x (m + 1)) (-(k : ℤ) - 1) + (x (-(k : ℤ) - 1 + 1)).1 := by
      have := symPos_succ (fun m => x (m + 1)) (-(k : ℤ) - 1)
      simpa [sub_add_cancel] using this
    have h2 : symPos x (-(k : ℤ) + 1) = symPos x (-(k : ℤ)) + (x (-(k : ℤ))).1 :=
      symPos_succ x (-(k : ℤ))
    have hidx : -(k : ℤ) - 1 + 1 = -(k : ℤ) := by omega
    rw [hidx] at h1
    have h3 : (-(k : ℤ) - 1) + 1 = -(k : ℤ) := by omega
    rw [h3]
    linarith

lemma symPos_strictMono {SigmaSet : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hSigma_lo : ∀ σ ∈ SigmaSet, δ ≤ σ) (x : ℤ → {σ : ℝ // σ ∈ SigmaSet}) :
    StrictMono (symPos x) := by
  have hstep : ∀ n : ℤ, symPos x n < symPos x (n + 1) := by
    intro n
    rw [symPos_succ]
    linarith [hSigma_lo (x n).1 (x n).2]
  intro m n hmn
  have hdiff : ∃ k : ℕ, n = m + (k + 1 : ℕ) := by
    refine ⟨(n - m - 1).toNat, ?_⟩
    omega
  rcases hdiff with ⟨k, rfl⟩
  induction k with
  | zero => simpa using hstep m
  | succ k ih =>
    have hlt := hstep (m + (k + 1 : ℕ))
    have hrew : m + ((k + 1 + 1 : ℕ) : ℤ) = (m + ((k + 1 : ℕ) : ℤ)) + 1 := by omega
    rw [hrew]
    exact lt_trans (ih (by omega)) hlt

lemma symPos_abs_ge {SigmaSet : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hSigma_lo : ∀ σ ∈ SigmaSet, δ ≤ σ) (x : ℤ → {σ : ℝ // σ ∈ SigmaSet}) (n : ℤ) :
    δ * |(n : ℝ)| ≤ |symPos x n| := by
  cases n with
  | ofNat k =>
    have hge : (k : ℝ) * δ ≤ symPos x (Int.ofNat k) := by
      simp only [symPos]
      calc
        (k : ℝ) * δ = ∑ _j ∈ Finset.range k, δ := by simp
        _ ≤ ∑ j ∈ Finset.range k, (x (j : ℤ)).1 :=
            Finset.sum_le_sum fun j _ => hSigma_lo (x (j : ℤ)).1 (x (j : ℤ)).2
    have hnn : 0 ≤ symPos x (Int.ofNat k) := le_trans (by positivity) hge
    rw [abs_of_nonneg hnn]
    change δ * |(k : ℝ)| ≤ symPos x (Int.ofNat k)
    rw [abs_of_nonneg (Nat.cast_nonneg k)]
    linarith
  | negSucc k =>
    have hge : ((k + 1 : ℕ) : ℝ) * δ ≤ ∑ j ∈ Finset.range (k + 1), (x (-(j : ℤ) - 1)).1 := by
      calc
        ((k + 1 : ℕ) : ℝ) * δ = ∑ _j ∈ Finset.range (k + 1), δ := by simp
        _ ≤ ∑ j ∈ Finset.range (k + 1), (x (-(j : ℤ) - 1)).1 :=
            Finset.sum_le_sum fun j _ => hSigma_lo _ (x _).2
    have hnn : 0 ≤ ∑ j ∈ Finset.range (k + 1), (x (-(j : ℤ) - 1)).1 := le_trans (by positivity) hge
    simp only [symPos, abs_neg, abs_of_nonneg hnn]
    have hcast : ((Int.negSucc k : ℤ) : ℝ) = -((k + 1 : ℕ) : ℝ) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [hcast, abs_neg, abs_of_nonneg (Nat.cast_nonneg (k + 1))]
    linarith

lemma continuous_symPos {SigmaSet : Finset ℝ} (n : ℤ) :
    Continuous (fun x : ℤ → {σ : ℝ // σ ∈ SigmaSet} => symPos x n) := by
  cases n with
  | ofNat k =>
    change Continuous (fun x : ℤ → {σ : ℝ // σ ∈ SigmaSet} => ∑ j ∈ Finset.range k, (x (j : ℤ)).1)
    exact continuous_finsetSum _ fun j _ => continuous_subtype_val.comp (continuous_apply (j : ℤ))
  | negSucc k =>
    change Continuous (fun x : ℤ → {σ : ℝ // σ ∈ SigmaSet} =>
      - ∑ j ∈ Finset.range (k + 1), (x (-(j : ℤ) - 1)).1)
    exact Continuous.neg <| continuous_finsetSum _ fun j _ =>
      continuous_subtype_val.comp (continuous_apply (-(j : ℤ) - 1))

lemma strictMono_nat_eq_of_range_eq {f g : ℕ → ℝ} (hf : StrictMono f) (hg : StrictMono g)
    (hrange : Set.range f = Set.range g) : f = g := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hf_mem : f n ∈ Set.range g := by rw [← hrange]; exact ⟨n, rfl⟩
    obtain ⟨m, hm⟩ := hf_mem
    have hg_mem : g n ∈ Set.range f := by rw [hrange]; exact ⟨n, rfl⟩
    obtain ⟨k, hk⟩ := hg_mem
    have hnm : n ≤ m := by
      by_contra hlt; push Not at hlt
      have heq := ih m hlt
      have : f m < f n := hf hlt
      linarith
    have hnk : n ≤ k := by
      by_contra hlt; push Not at hlt
      have heq := ih k hlt
      have : g k < g n := hg hlt
      linarith
    have h1 : g n ≤ g m := hg.monotone hnm
    have h2 : f n ≤ f k := hf.monotone hnk
    linarith

lemma symPos_eq_of_nat_pos_range_eq {SigmaSet : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hSigma_lo : ∀ σ ∈ SigmaSet, δ ≤ σ) {x y : ℤ → {σ : ℝ // σ ∈ SigmaSet}}
    (hneg : ∀ n < 0, x n = y n)
    (hrange : Set.range (fun n : ℕ => symPos x ((n + 1 : ℕ) : ℤ)) =
              Set.range (fun n : ℕ => symPos y ((n + 1 : ℕ) : ℤ))) :
    x = y := by
  have hpos_eq : ∀ n : ℕ, symPos x ((n + 1 : ℕ) : ℤ) = symPos y ((n + 1 : ℕ) : ℤ) := by
    have hf : StrictMono (fun n : ℕ => symPos x ((n + 1 : ℕ) : ℤ)) :=
      fun a b hab => symPos_strictMono hδ hSigma_lo x (by omega)
    have hg : StrictMono (fun n : ℕ => symPos y ((n + 1 : ℕ) : ℤ)) :=
      fun a b hab => symPos_strictMono hδ hSigma_lo y (by omega)
    exact congrFun (strictMono_nat_eq_of_range_eq hf hg hrange)
  have hpos_nn : ∀ n : ℕ, symPos x (n : ℤ) = symPos y (n : ℤ) := by
    intro n
    cases n with
    | zero => simp [symPos_zero]
    | succ k => exact hpos_eq k
  funext n
  by_cases hn : n < 0
  · exact hneg n hn
  · push Not at hn
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have h1 := symPos_succ x (k : ℤ)
    have h2 := symPos_succ y (k : ℤ)
    have heq1 := hpos_nn k
    have heq2 := hpos_nn (k + 1)
    apply Subtype.ext
    have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
    rw [hcast] at heq2
    linarith

lemma symPos_eq_of_nat_neg_range_eq {SigmaSet : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hSigma_lo : ∀ σ ∈ SigmaSet, δ ≤ σ) {x y : ℤ → {σ : ℝ // σ ∈ SigmaSet}}
    (hnonneg : ∀ n : ℤ, 0 ≤ n → x n = y n)
    (hrange : Set.range (fun n : ℕ => -symPos x (Int.negSucc n)) =
              Set.range (fun n : ℕ => -symPos y (Int.negSucc n))) :
    x = y := by
  have hneg_eq : ∀ n : ℕ, symPos x (Int.negSucc n) = symPos y (Int.negSucc n) := by
    have hf : StrictMono (fun n : ℕ => -symPos x (Int.negSucc n)) := by
      intro a b hab
      have hlt : Int.negSucc b < Int.negSucc a := by omega
      have := symPos_strictMono hδ hSigma_lo x hlt
      linarith
    have hg : StrictMono (fun n : ℕ => -symPos y (Int.negSucc n)) := by
      intro a b hab
      have hlt : Int.negSucc b < Int.negSucc a := by omega
      have := symPos_strictMono hδ hSigma_lo y hlt
      linarith
    intro n
    have h := congrFun (strictMono_nat_eq_of_range_eq hf hg hrange) n
    linarith
  funext n
  by_cases hn : 0 ≤ n
  · exact hnonneg n hn
  · push Not at hn
    cases n with
    | ofNat k => exact absurd (Int.ofNat_nonneg k) (not_le.mpr hn)
    | negSucc k =>
      cases k with
      | zero =>
        have h1 := symPos_succ x (Int.negSucc 0)
        have h2 := symPos_succ y (Int.negSucc 0)
        have h0 : Int.negSucc 0 + 1 = 0 := by omega
        rw [h0, symPos_zero] at h1 h2
        have heq := hneg_eq 0
        apply Subtype.ext; linarith
      | succ m =>
        have h1 := symPos_succ x (Int.negSucc (m + 1))
        have h2 := symPos_succ y (Int.negSucc (m + 1))
        have hs : Int.negSucc (m + 1) + 1 = Int.negSucc m := by omega
        rw [hs] at h1 h2
        have heq1 := hneg_eq (m + 1)
        have heq2 := hneg_eq m
        apply Subtype.ext; linarith

lemma enumerate_separated_set {Λ : Set ℝ} {δ Δ : ℝ} {SigmaSet : Finset ℝ}
    (h0Λ : (0 : ℝ) ∈ Λ) (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hsep : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → δ ≤ |x - y|)
    (hgap : ∀ a : ℝ, (Λ ∩ Set.Ioc a (a + Δ)).Nonempty)
    (hSigma_lo : ∀ σ ∈ SigmaSet, δ ≤ σ)
    (hdiff_mem : ∀ x ∈ Λ, ∀ y ∈ Λ, x < y → y - x ≤ Δ → y - x ∈ SigmaSet) :
    ∃ x₀ : ℤ → {σ : ℝ // σ ∈ SigmaSet}, Set.range (symPos x₀) = Λ := by
  classical
  have hsucc_fin : ∀ y : ℝ, (Λ ∩ Set.Ioc y (y + Δ)).Finite := fun y =>
    ((separated_inter_Icc_finite_and_card_le hδ hsep y (y + Δ)).1).subset
      (Set.inter_subset_inter_right _ Set.Ioc_subset_Icc_self)
  have hsucc_ne : ∀ y : ℝ, ((hsucc_fin y).toFinset).Nonempty := fun y =>
    (Set.Finite.toFinset_nonempty (hsucc_fin y)).mpr (hgap y)
  let succΛ : ℝ → ℝ := fun y => ((hsucc_fin y).toFinset).min' (hsucc_ne y)
  have hsucc_spec : ∀ y : ℝ, succΛ y ∈ Λ ∧ y < succΛ y ∧ succΛ y ≤ y + Δ ∧
      ∀ z ∈ Λ, ¬ (y < z ∧ z < succΛ y) := by
    intro y
    have hmem := ((hsucc_fin y).mem_toFinset).mp (Finset.min'_mem _ (hsucc_ne y))
    refine ⟨hmem.1, hmem.2.1, hmem.2.2, fun z hz ⟨h1, h2⟩ => ?_⟩
    have hz_mem : z ∈ (hsucc_fin y).toFinset :=
      ((hsucc_fin y).mem_toFinset).mpr ⟨hz, h1, le_trans h2.le hmem.2.2⟩
    have hle := Finset.min'_le _ z hz_mem
    linarith
  have hpred_fin : ∀ y : ℝ, (Λ ∩ Set.Ico (y - (Δ + δ)) y).Finite := fun y =>
    ((separated_inter_Icc_finite_and_card_le hδ hsep (y - (Δ + δ)) y).1).subset
      (Set.inter_subset_inter_right _ Set.Ico_subset_Icc_self)
  have hpred_ne : ∀ y : ℝ, ((hpred_fin y).toFinset).Nonempty := by
    intro y
    rw [Set.Finite.toFinset_nonempty]
    obtain ⟨w, hwΛ, hw1, hw2⟩ := hgap (y - (Δ + δ / 2))
    exact ⟨w, hwΛ, by linarith, by linarith⟩
  let predΛ : ℝ → ℝ := fun y => ((hpred_fin y).toFinset).max' (hpred_ne y)
  have hpred_spec : ∀ y : ℝ, predΛ y ∈ Λ ∧ predΛ y < y ∧ y - predΛ y ≤ Δ ∧
      ∀ z ∈ Λ, ¬ (predΛ y < z ∧ z < y) := by
    intro y
    have hmem := ((hpred_fin y).mem_toFinset).mp (Finset.max'_mem _ (hpred_ne y))
    have hno : ∀ z ∈ Λ, ¬ (predΛ y < z ∧ z < y) := by
      intro z hz ⟨h1, h2⟩
      have hz_mem : z ∈ (hpred_fin y).toFinset :=
        ((hpred_fin y).mem_toFinset).mpr ⟨hz, le_trans hmem.2.1 h1.le, h2⟩
      have hle := Finset.le_max' _ z hz_mem
      linarith
    have hgap_le : y - predΛ y ≤ Δ := by
      by_contra hgt; push Not at hgt
      obtain ⟨w, hwΛ, hw1, hw2⟩ := hgap (predΛ y)
      exact hno w hwΛ ⟨hw1, by linarith⟩
    exact ⟨hmem.1, hmem.2.2, hgap_le, hno⟩
  let enumPos : ℕ → ℝ := fun k => Nat.recOn k 0 (fun _ prev => succΛ prev)
  let enumNeg : ℕ → ℝ := fun k => Nat.recOn k (predΛ 0) (fun _ prev => predΛ prev)
  let enumΛ : ℤ → ℝ
    | Int.ofNat k => enumPos k
    | Int.negSucc k => enumNeg k
  have henum_mem : ∀ n : ℤ, enumΛ n ∈ Λ := by
    intro n
    cases n with
    | ofNat k =>
      induction k with
      | zero => exact h0Λ
      | succ k _ => exact (hsucc_spec _).1
    | negSucc k =>
      induction k with
      | zero => exact (hpred_spec 0).1
      | succ k _ => exact (hpred_spec _).1
  have henum_step : ∀ n : ℤ,
      enumΛ n < enumΛ (n + 1) ∧ enumΛ (n + 1) - enumΛ n ≤ Δ ∧
      ∀ z ∈ Λ, ¬ (enumΛ n < z ∧ z < enumΛ (n + 1)) := by
    intro n
    cases n with
    | ofNat k =>
      have h := hsucc_spec (enumPos k)
      change enumPos k < succΛ (enumPos k) ∧ succΛ (enumPos k) - enumPos k ≤ Δ ∧
        ∀ z ∈ Λ, ¬ (enumPos k < z ∧ z < succΛ (enumPos k))
      exact ⟨h.2.1, by linarith [h.2.2.1], h.2.2.2⟩
    | negSucc k =>
      cases k with
      | zero =>
        have h := hpred_spec 0
        change predΛ 0 < 0 ∧ 0 - predΛ 0 ≤ Δ ∧ ∀ z ∈ Λ, ¬ (predΛ 0 < z ∧ z < 0)
        exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
      | succ m =>
        have hrew : Int.negSucc (m + 1) + 1 = Int.negSucc m := by omega
        rw [hrew]
        have h := hpred_spec (enumNeg m)
        change predΛ (enumNeg m) < enumNeg m ∧ enumNeg m - predΛ (enumNeg m) ≤ Δ ∧
          ∀ z ∈ Λ, ¬ (predΛ (enumNeg m) < z ∧ z < enumNeg m)
        exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
  let x₀ : ℤ → {σ : ℝ // σ ∈ SigmaSet} := fun n =>
    ⟨enumΛ (n + 1) - enumΛ n,
      hdiff_mem (enumΛ n) (henum_mem n) (enumΛ (n + 1)) (henum_mem (n + 1))
        (henum_step n).1 (henum_step n).2.1⟩
  have hpos_eq : ∀ n : ℤ, symPos x₀ n = enumΛ n := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [symPos_zero, enumΛ, enumPos]
    | succ k ih =>
      rw [symPos_succ, ih]
      change enumΛ (k : ℤ) + (enumΛ ((k : ℤ) + 1) - enumΛ (k : ℤ)) = enumΛ ((k : ℤ) + 1)
      ring
    | pred k ih =>
      have h1 := symPos_succ x₀ (-(k : ℤ) - 1)
      have hidx : (-(k : ℤ) - 1) + 1 = -(k : ℤ) := by omega
      rw [hidx, ih] at h1
      change enumΛ (-(k : ℤ)) = symPos x₀ (-(k : ℤ) - 1) + (enumΛ (-(k : ℤ) - 1 + 1) - enumΛ (-(k : ℤ) - 1)) at h1
      rw [hidx] at h1
      linarith
  refine ⟨x₀, ?_⟩
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    rw [hpos_eq n]
    exact henum_mem n
  · intro hzΛ
    set N : ℕ := Nat.floor (|z| / δ) + 1
    have hN_gt : |z| < (N : ℝ) * δ := by
      have hlt : |z| / δ < (N : ℝ) := by
        dsimp only [N]; push_cast; exact Nat.lt_floor_add_one _
      exact (div_lt_iff₀ hδ).mp hlt
    have hlo : enumΛ (-(N : ℤ)) ≤ z := by
      have h1 := symPos_abs_ge hδ hSigma_lo x₀ (-(N : ℤ))
      rw [hpos_eq] at h1
      have hneg : enumΛ (-(N : ℤ)) ≤ 0 := by
        have hlt : (-(N : ℤ)) ≤ 0 := by omega
        have hmono := (symPos_strictMono hδ hSigma_lo x₀).monotone hlt
        rw [hpos_eq, hpos_eq, show enumΛ 0 = 0 by rfl] at hmono
        exact hmono
      rw [abs_of_nonpos hneg] at h1
      have habs : |((-(N : ℤ) : ℤ) : ℝ)| = (N : ℝ) := by
        push_cast; rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg N)]
      rw [habs] at h1
      have hz_ge : -|z| ≤ z := neg_abs_le z
      linarith
    have hhi : z < enumΛ (N : ℤ) := by
      have h1 := symPos_abs_ge hδ hSigma_lo x₀ (N : ℤ)
      rw [hpos_eq] at h1
      have hnn : 0 ≤ enumΛ (N : ℤ) := by
        have hle : (0 : ℤ) ≤ (N : ℤ) := by omega
        have hmono := (symPos_strictMono hδ hSigma_lo x₀).monotone hle
        rw [hpos_eq, hpos_eq, show enumΛ 0 = 0 by rfl] at hmono
        exact hmono
      rw [abs_of_nonneg hnn] at h1
      have habs : |((N : ℤ) : ℝ)| = (N : ℝ) := by
        push_cast; exact abs_of_nonneg (Nat.cast_nonneg N)
      rw [habs] at h1
      have hz_le : z ≤ |z| := le_abs_self z
      linarith
    let S_z : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun k => enumΛ k ≤ z)
    have hSz_ne : S_z.Nonempty := by
      refine ⟨-(N : ℤ), Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, hlo⟩⟩
    set m : ℤ := S_z.max' hSz_ne
    have hm_mem : m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ∧ enumΛ m ≤ z :=
      Finset.mem_filter.mp (Finset.max'_mem S_z hSz_ne)
    have hm_lo : -(N : ℤ) ≤ m := (Finset.mem_Icc.mp hm_mem.1).1
    have hm_lt_N : m < (N : ℤ) := by
      by_contra hge; push Not at hge
      have hm_eq : m = (N : ℤ) := le_antisymm (Finset.mem_Icc.mp hm_mem.1).2 hge
      have hle_z : enumΛ (N : ℤ) ≤ z := by rw [← hm_eq]; exact hm_mem.2
      linarith
    have hm1_gt : z < enumΛ (m + 1) := by
      by_contra hle; push Not at hle
      have hm1_in : m + 1 ∈ S_z := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hle⟩
      have hmax := Finset.le_max' S_z (m + 1) hm1_in
      omega
    have hzeq : enumΛ m = z := by
      by_contra hne
      have hlt : enumΛ m < z := lt_of_le_of_ne hm_mem.2 hne
      exact (henum_step m).2.2 z hzΛ ⟨hlt, hm1_gt⟩
    exact ⟨m, by rw [hpos_eq m, hzeq]⟩

lemma summable_sym_term {SigmaSet : Finset ℝ} {δ s : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hSigma_lo : ∀ σ ∈ SigmaSet, δ ≤ σ) (c t : ℝ) :
    ∃ u : ℤ → ℝ, Summable u ∧
      ∀ (n : ℤ) (x : ℤ → {σ : ℝ // σ ∈ SigmaSet}),
        ‖((weightFn s (symPos x n - c) : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * ((symPos x n - c : ℝ) : ℂ))‖ ≤ u n := by
  set N₀ : ℕ := Nat.floor (2 * |c| / δ) + 1
  let u : ℤ → ℝ := fun n =>
    if n.natAbs ≤ N₀ then 4 * s ^ 2
    else 4 / (Real.pi ^ 2 * δ ^ 2 * (n.natAbs : ℝ) ^ 2)
  have hu_sum : Summable u := by
    have hnat_sum : Summable (fun k : ℕ => 4 / (Real.pi ^ 2 * δ ^ 2 * (k : ℝ) ^ 2)) := by
      have h1 : Summable (fun k : ℕ => 1 / (k : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have h2 := h1.mul_left (4 / (Real.pi ^ 2 * δ ^ 2))
      refine h2.congr fun k => ?_
      ring
    have hint_base : Summable (fun n : ℤ => 4 / (Real.pi ^ 2 * δ ^ 2 * (n.natAbs : ℝ) ^ 2)) := by
      rw [summable_int_iff_summable_nat_and_neg]
      refine ⟨?_, ?_⟩
      · exact hnat_sum.congr fun k => by simp
      · exact hnat_sum.congr fun k => by simp
    refine hint_base.congr_cofinite ?_
    rw [Filter.EventuallyEq, Filter.eventually_cofinite]
    have hsub : {n : ℤ | 4 / (Real.pi ^ 2 * δ ^ 2 * (n.natAbs : ℝ) ^ 2) ≠ u n} ⊆
        (Finset.Icc (-(N₀ : ℤ)) (N₀ : ℤ) : Set ℤ) := by
      intro n hn
      simp only [Set.mem_setOf_eq, u] at hn
      have hle : n.natAbs ≤ N₀ := by
        by_contra hgt
        rw [if_neg hgt] at hn
        exact hn rfl
      simp only [Finset.coe_Icc, Set.mem_Icc]
      omega
    exact (Finset.finite_toSet _).subset hsub
  refine ⟨u, hu_sum, fun n x => ?_⟩
  have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * ((symPos x n - c : ℝ) : ℂ))‖ = 1 := by
    have h1 : 2 * Real.pi * Complex.I * (t : ℂ) * ((symPos x n - c : ℝ) : ℂ) =
        Complex.I * ((2 * Real.pi * t * (symPos x n - c) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_exp_I_mul_ofReal]
  rw [norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_of_nonneg (weightFn_nonneg s _)]
  simp only [u]
  split_ifs with hn
  · exact weightFn_le s hs _
  · push Not at hn
    have hpos_n : 0 < (n.natAbs : ℝ) := by
      have : 0 < n.natAbs := lt_of_le_of_lt (Nat.zero_le N₀) hn
      exact_mod_cast this
    have hn_gt : 2 * |c| / δ < (n.natAbs : ℝ) := by
      have h1 : 2 * |c| / δ < (N₀ : ℝ) := by
        dsimp only [N₀]; push_cast; exact Nat.lt_floor_add_one _
      have h2 : (N₀ : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast hn
      linarith
    have hδn : 2 * |c| < δ * (n.natAbs : ℝ) := by
      have := (div_lt_iff₀ hδ).mp hn_gt
      linarith
    have habs_n : |(n : ℝ)| = (n.natAbs : ℝ) := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hpos_ge : δ * (n.natAbs : ℝ) ≤ |symPos x n| := by
      rw [← habs_n]; exact symPos_abs_ge hδ hSigma_lo x n
    have hdiff_ge : (δ / 2) * (n.natAbs : ℝ) ≤ |symPos x n - c| := by
      have := abs_sub_abs_le_abs_sub (symPos x n) c
      linarith
    have hdiff_pos : 0 < |symPos x n - c| := lt_of_lt_of_le (by positivity) hdiff_ge
    have hdiff_ne : symPos x n - c ≠ 0 := abs_pos.mp hdiff_pos
    have hwb := weightFn_le_inv_sq s hs hdiff_ne
    have hsq_ge : (δ / 2 * (n.natAbs : ℝ)) ^ 2 ≤ (symPos x n - c) ^ 2 := by
      rw [← sq_abs (symPos x n - c)]
      exact pow_le_pow_left₀ (by positivity) hdiff_ge 2
    have hstep : 1 / (Real.pi ^ 2 * (symPos x n - c) ^ 2) ≤
        4 / (Real.pi ^ 2 * δ ^ 2 * (n.natAbs : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hpi2 : 0 < Real.pi ^ 2 := by positivity
      have hrew : (δ / 2 * (n.natAbs : ℝ)) ^ 2 = δ ^ 2 * (n.natAbs : ℝ) ^ 2 / 4 := by ring
      rw [hrew] at hsq_ge
      nlinarith
    exact le_trans hwb hstep

lemma exists_periodic_in_closed_shift_space {SigmaSet : Finset ℝ}
    {X : Set (ℤ → {σ : ℝ // σ ∈ SigmaSet})} (hX_closed : IsClosed X)
    (hX_shift : ∀ x, x ∈ X ↔ (fun n => x (n + 1)) ∈ X)
    (hX_left : ∀ x ∈ X, ∀ y ∈ X, (∀ n < 0, x n = y n) → x = y)
    (hX_right : ∀ x ∈ X, ∀ y ∈ X, (∀ n : ℤ, 0 ≤ n → x n = y n) → x = y)
    {x₀ : ℤ → {σ : ℝ // σ ∈ SigmaSet}} (hx₀ : x₀ ∈ X) :
    ∃ q : ℕ, 0 < q ∧ ∀ n : ℤ, x₀ (n + (q : ℤ)) = x₀ n := by
  let Sym := {σ : ℝ // σ ∈ SigmaSet}
  haveI : DiscreteTopology Sym := Finite.instDiscreteTopology
  have hisClosed_ne : ∀ n : ℤ, IsClosed {q : (ℤ → Sym) × (ℤ → Sym) | q.1 n ≠ q.2 n} := by
    intro n
    have hopen : IsOpen {q : (ℤ → Sym) × (ℤ → Sym) | q.1 n = q.2 n} := by
      have heq : {q : (ℤ → Sym) × (ℤ → Sym) | q.1 n = q.2 n} =
          ⋃ a : Sym, (((fun q : (ℤ → Sym) × (ℤ → Sym) => q.1 n) ⁻¹' {a}) ∩
            ((fun q : (ℤ → Sym) × (ℤ → Sym) => q.2 n) ⁻¹' {a})) := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
          Set.mem_singleton_iff]
        exact ⟨fun h => ⟨q.1 n, rfl, h.symm⟩, fun ⟨_, h1, h2⟩ => h1.trans h2.symm⟩
      rw [heq]
      exact isOpen_iUnion fun a =>
        ((isOpen_discrete {a}).preimage ((continuous_apply n).comp continuous_fst)).inter
          ((isOpen_discrete {a}).preimage ((continuous_apply n).comp continuous_snd))
    exact hopen.isClosed_compl
  -- Helper: shift by arbitrary integer preserves X
  have hX_shift_int : ∀ (k : ℤ) (x : ℤ → Sym), x ∈ X ↔ (fun n => x (n + k)) ∈ X := by
    intro k
    induction k using Int.induction_on with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      have hrew : (fun n : ℤ => x (n + ((m : ℤ) + 1))) = fun n => (fun j => x (j + (m : ℤ))) (n + 1) := by
        funext n; congr 1; ring
      rw [hrew, ← hX_shift (fun j => x (j + (m : ℤ))), ← ih]
    | pred m ih =>
      intro x
      have hrew : (fun n : ℤ => x (n + (-(m : ℤ)))) = fun n => (fun j => x (j + (-(m : ℤ) - 1))) (n + 1) := by
        funext n; congr 1; ring
      rw [ih x, hrew, ← hX_shift (fun j => x (j + (-(m : ℤ) - 1)))]
  -- Compactness gives N_L determining x 0 from [-N_L, 0)
  have hNL : ∃ N_L : ℕ, ∀ x ∈ X, ∀ y ∈ X,
      (∀ n : ℤ, -(N_L : ℤ) ≤ n → n < 0 → x n = y n) → x 0 = y 0 := by
    by_contra hnot; push Not at hnot
    choose xSeq hxSeq ySeq hySeq hagree hdiff using hnot
    let u : ℕ → (ℤ → Sym) × (ℤ → Sym) := fun k => (xSeq k, ySeq k)
    obtain ⟨p, hp⟩ := exists_clusterPt_of_compactSpace (Filter.map u atTop)
    have hmem_closed : ∀ (S : Set ((ℤ → Sym) × (ℤ → Sym))),
        IsClosed S → (∀ᶠ k in atTop, u k ∈ S) → p ∈ S := by
      intro S hS hev
      have hle : Filter.map u atTop ≤ 𝓟 S := by
        rw [Filter.le_principal_iff]
        exact hev
      exact isClosed_iff_clusterPt.mp hS p (hp.mono hle)
    have hp1 : p.1 ∈ X :=
      hmem_closed {q | q.1 ∈ X} (hX_closed.preimage continuous_fst)
        (Eventually.of_forall hxSeq)
    have hp2 : p.2 ∈ X :=
      hmem_closed {q | q.2 ∈ X} (hX_closed.preimage continuous_snd)
        (Eventually.of_forall hySeq)
    have hpagree : ∀ n < 0, p.1 n = p.2 n := by
      intro n hn
      have hcl : IsClosed {q : (ℤ → Sym) × (ℤ → Sym) | q.1 n = q.2 n} :=
        isClosed_eq ((continuous_apply n).comp continuous_fst)
          ((continuous_apply n).comp continuous_snd)
      have hev : ∀ᶠ k : ℕ in atTop, u k ∈ {q : (ℤ → Sym) × (ℤ → Sym) | q.1 n = q.2 n} := by
        refine eventually_atTop.mpr ⟨(-n).toNat, fun k hk => ?_⟩
        exact hagree k n (by omega) hn
      exact hmem_closed _ hcl hev
    have hpdiff : p.1 0 ≠ p.2 0 :=
      hmem_closed _ (hisClosed_ne 0) (Eventually.of_forall hdiff)
    exact hpdiff (congrFun (hX_left p.1 hp1 p.2 hp2 hpagree) 0)
  -- Symmetrically, compactness gives N_R determining x (-1) from [0, N_R)
  have hNR : ∃ N_R : ℕ, ∀ x ∈ X, ∀ y ∈ X,
      (∀ n : ℤ, 0 ≤ n → n < (N_R : ℤ) → x n = y n) → x (-1) = y (-1) := by
    by_contra hnot; push Not at hnot
    choose xSeq hxSeq ySeq hySeq hagree hdiff using hnot
    let u : ℕ → (ℤ → Sym) × (ℤ → Sym) := fun k => (xSeq k, ySeq k)
    obtain ⟨p, hp⟩ := exists_clusterPt_of_compactSpace (Filter.map u atTop)
    have hmem_closed : ∀ (S : Set ((ℤ → Sym) × (ℤ → Sym))),
        IsClosed S → (∀ᶠ k in atTop, u k ∈ S) → p ∈ S := by
      intro S hS hev
      exact isClosed_iff_clusterPt.mp hS p (hp.mono (Filter.le_principal_iff.mpr hev))
    have hp1 : p.1 ∈ X :=
      hmem_closed {q | q.1 ∈ X} (hX_closed.preimage continuous_fst) (Eventually.of_forall hxSeq)
    have hp2 : p.2 ∈ X :=
      hmem_closed {q | q.2 ∈ X} (hX_closed.preimage continuous_snd) (Eventually.of_forall hySeq)
    have hpagree : ∀ n : ℤ, 0 ≤ n → p.1 n = p.2 n := by
      intro n hn
      have hcl : IsClosed {q : (ℤ → Sym) × (ℤ → Sym) | q.1 n = q.2 n} :=
        isClosed_eq ((continuous_apply n).comp continuous_fst)
          ((continuous_apply n).comp continuous_snd)
      have hev : ∀ᶠ k : ℕ in atTop, u k ∈ {q : (ℤ → Sym) × (ℤ → Sym) | q.1 n = q.2 n} := by
        refine eventually_atTop.mpr ⟨n.toNat + 1, fun k hk => ?_⟩
        exact hagree k n hn (by omega)
      exact hmem_closed _ hcl hev
    have hpdiff : p.1 (-1) ≠ p.2 (-1) :=
      hmem_closed _ (hisClosed_ne (-1)) (Eventually.of_forall hdiff)
    exact hpdiff (congrFun (hX_right p.1 hp1 p.2 hp2 hpagree) (-1))
  rcases hNL with ⟨N_L, hNL⟩
  rcases hNR with ⟨N_R, hNR⟩
  set W : ℕ := max N_L N_R
  -- Window [0, W) determines all of x ∈ X!
  have hwindow : ∀ x ∈ X, ∀ y ∈ X,
      (∀ j : Fin W, x (j : ℤ) = y (j : ℤ)) → x = y := by
    intro x hx y hy hwin
    have hpos_all : ∀ k : ℕ, x (k : ℤ) = y (k : ℤ) := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih =>
        by_cases hk : k < W
        · exact hwin ⟨k, hk⟩
        · have hkx : (fun n => x (n + (k : ℤ))) ∈ X := (hX_shift_int (k : ℤ) x).mp hx
          have hky : (fun n => y (n + (k : ℤ))) ∈ X := (hX_shift_int (k : ℤ) y).mp hy
          have hstep := hNL _ hkx _ hky (fun n hn1 hn2 => by
            have hidx_nn : 0 ≤ n + (k : ℤ) := by omega
            have hidx_lt : (n + (k : ℤ)).toNat < k := by omega
            have hcast : ((n + (k : ℤ)).toNat : ℤ) = n + (k : ℤ) := Int.toNat_of_nonneg hidx_nn
            simpa [hcast] using ih (n + (k : ℤ)).toNat hidx_lt)
          simpa using hstep
    exact hX_right x hx y hy fun n hn => by
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      exact hpos_all k
  -- Pigeonhole on windows of length W in x₀
  let f : Fin (Fintype.card (Fin W → Sym) + 1) → (Fin W → Sym) :=
    fun k j => x₀ ((k.1 : ℤ) + (j.1 : ℤ))
  have hlt_card : Fintype.card (Fin W → Sym) < Fintype.card (Fin (Fintype.card (Fin W → Sym) + 1)) := by
    simp
  obtain ⟨k₁, k₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt_card
  have hne_val : k₁.1 ≠ k₂.1 := fun h => hne (Fin.ext h)
  wlog hlt : k₁.1 < k₂.1 generalizing k₁ k₂
  · exact this k₂ k₁ hne.symm heq.symm hne_val.symm (lt_of_le_of_ne (le_of_not_gt hlt) hne_val.symm)
  set q : ℕ := k₂.1 - k₁.1
  have hq_pos : 0 < q := Nat.sub_pos_of_lt hlt
  have hx1 : (fun n => x₀ (n + (k₁.1 : ℤ))) ∈ X := (hX_shift_int (k₁.1 : ℤ) x₀).mp hx₀
  have hx2 : (fun n => x₀ (n + (k₂.1 : ℤ))) ∈ X := (hX_shift_int (k₂.1 : ℤ) x₀).mp hx₀
  have hseq_eq : (fun n => x₀ (n + (k₁.1 : ℤ))) = (fun n => x₀ (n + (k₂.1 : ℤ))) := by
    refine hwindow _ hx1 _ hx2 fun j => ?_
    have hj := congrFun heq j
    dsimp only [f] at hj
    have h1 : (j.1 : ℤ) + (k₁.1 : ℤ) = (k₁.1 : ℤ) + (j.1 : ℤ) := by ring
    have h2 : (j.1 : ℤ) + (k₂.1 : ℤ) = (k₂.1 : ℤ) + (j.1 : ℤ) := by ring
    rw [h1, h2]
    exact hj
  refine ⟨q, hq_pos, fun n => ?_⟩
  have hn := congrFun hseq_eq (n - (k₁.1 : ℤ))
  have h1 : (n - (k₁.1 : ℤ)) + (k₁.1 : ℤ) = n := by ring
  have h2 : (n - (k₁.1 : ℤ)) + (k₂.1 : ℤ) = n + (q : ℤ) := by omega
  rw [h1, h2] at hn
  exact hn.symm

/- ## Section 6: Putting Everything Together (`H3`) -/

theorem main_H3 : OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1.H3 := by
  classical
  intro Ω hΩ_bdd hΩ_meas hΩ_vol hspec
  rcases hspec with ⟨Λ₀, hsp₀⟩
  obtain ⟨ξ₀, hξ₀⟩ := spectrum_nonempty hsp₀
  have hsp : spectralPair Ω {ξ : Fin 1 → ℝ | ξ + ξ₀ ∈ Λ₀} :=
    spectralPair_translate hsp₀ ξ₀
  let S : Set ℝ := {t : ℝ | (fun _ : Fin 1 => t) ∈ Ω}
  have hΩ_eq : Ω = {x : Fin 1 → ℝ | x 0 ∈ S} := by
    ext x
    simp only [Set.mem_setOf_eq, S]
    have hx : (fun _ : Fin 1 => x 0) = x := by ext i; fin_cases i; rfl
    rw [hx]
  have hS_meas : MeasurableSet S :=
    hΩ_meas.preimage (continuous_pi fun _ => continuous_id).measurable
  have hS_bdd : Bornology.IsBounded S := by
    obtain ⟨R, hR⟩ := hΩ_bdd.subset_closedBall (0 : Fin 1 → ℝ)
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℝ)]
    refine ⟨R, fun t ht => ?_⟩
    have hmem : (fun _ : Fin 1 => t) ∈ Metric.closedBall (0 : Fin 1 → ℝ) R := hR ht
    rw [Metric.mem_closedBall, dist_zero_right] at hmem ⊢
    have h0 := norm_le_pi_norm (fun _ : Fin 1 => t) (0 : Fin 1)
    exact le_trans h0 hmem
  have hS_vol : volume S = 1 := by
    rw [← volume_preimage_apply0 S, ← hΩ_eq, hΩ_vol]
  let Λ : Set ℝ := {lam : ℝ | (fun _ : Fin 1 => lam) + ξ₀ ∈ Λ₀}
  have hΛ_eq : {ξ : Fin 1 → ℝ | ξ 0 ∈ Λ} = {ξ : Fin 1 → ℝ | ξ + ξ₀ ∈ Λ₀} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Λ]
    have hξ : (fun _ : Fin 1 => ξ 0) = ξ := by ext i; fin_cases i; rfl
    rw [hξ]
  have hspΛ : spectralPair Ω {ξ : Fin 1 → ℝ | ξ 0 ∈ Λ} := by
    rw [hΛ_eq]; exact hsp
  have h0Λ : (0 : ℝ) ∈ Λ := by
    change (fun _ : Fin 1 => (0 : ℝ)) + ξ₀ ∈ Λ₀
    have h0 : (fun _ : Fin 1 => (0 : ℝ)) + ξ₀ = ξ₀ := by ext i; simp
    rw [h0]; exact hξ₀
  -- Step 1: Parseval tiling and separation δ > 0
  obtain ⟨hortho, htile⟩ := parseval_and_ortho hΩ_eq hS_vol hspΛ
  obtain ⟨δ, hδ_pos, hδ_gap⟩ := exists_min_gap hS_bdd hS_meas hS_vol
  have hsep : ∀ x ∈ Λ, ∀ y ∈ Λ, x ≠ y → δ ≤ |x - y| :=
    fun x hx y hy hne => hδ_gap (x - y) (hortho x hx y hy hne)
  have hΛ_cnt : Λ.Countable := separated_countable hδ_pos hsep
  -- Step 2: Bounded gaps Δ > 0
  obtain ⟨Δ, hΔ_pos, hδ_le_Δ, hgap⟩ :=
    exists_bounded_gaps hS_bdd hS_meas hS_vol hδ_pos hsep htile
  -- Step 3: Small a > 0 with Neumann series spectral gap
  obtain ⟨a, ha_pos, hrho_small⟩ := exists_a_neumann_small hS_bdd hS_meas hS_vol
  -- Step 4 & 5: Finite alphabet SigmaSet and symbolic space X
  have hZ_fin : ({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc (-Δ) Δ).Finite :=
    zero_set_inter_Icc_finite hS_bdd hS_meas hS_vol Δ
  have hSigma_fin : ({ξ : ℝ | F S (ξ : ℂ) = 0} ∩ Set.Icc δ Δ).Finite :=
    hZ_fin.subset (Set.inter_subset_inter_right _ (Set.Icc_subset_Icc_left (by linarith)))
  set SigmaSet : Finset ℝ := hSigma_fin.toFinset
  have hSigma_lo : ∀ σ ∈ SigmaSet, δ ≤ σ := fun σ hσ => ((hSigma_fin.mem_toFinset).mp hσ).2.1
  have hdiff_mem : ∀ x ∈ Λ, ∀ y ∈ Λ, x < y → y - x ≤ Δ → y - x ∈ SigmaSet := by
    intro x hx y hy hlt hle
    rw [hSigma_fin.mem_toFinset]
    have hne : y ≠ x := ne_of_gt hlt
    have hF0 : F S ((y - x : ℝ) : ℂ) = 0 := hortho y hy x hx hne
    have hge : δ ≤ y - x := by
      have := hsep y hy x hx hne
      rwa [abs_of_pos (sub_pos.mpr hlt)] at this
    exact ⟨hF0, hge, hle⟩
  obtain ⟨x₀, hx₀_range⟩ :=
    enumerate_separated_set h0Λ hδ_pos hΔ_pos hsep hgap hSigma_lo hdiff_mem
  let Sym := {σ : ℝ // σ ∈ SigmaSet}
  let term : ℝ → ℝ → ℝ → ℤ → (ℤ → Sym) → ℂ := fun c s t n x =>
    ((weightFn s (symPos x n - c) : ℝ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (t : ℂ) * ((symPos x n - c : ℝ) : ℂ))
  let X : Set (ℤ → Sym) :=
    {x | ∀ c : ℝ, ∀ s ∈ Set.Ioc 0 (a / 10), ∀ t ∈ Set.Ioo (3 * a / 10) (7 * a / 10),
      ∑' n : ℤ, term c s t n x = 0}
  -- x₀ ∈ X via spectral_sum_shifted_tent_eq_zero
  have hx₀_X : x₀ ∈ X := by
    intro c s hs t ht
    have hsum_Λ := spectral_sum_shifted_tent_eq_zero hS_bdd hS_meas hS_vol hΛ_cnt htile
      ha_pos hrho_small c hs ht
    -- Bijection ℤ ≃ Λ via symPos x₀
    have hinj : Function.Injective (symPos x₀) := (symPos_strictMono hδ_pos hSigma_lo x₀).injective
    let e : ℤ ≃ Λ := Equiv.ofBijective
      (fun n => ⟨symPos x₀ n, by rw [← hx₀_range]; exact ⟨n, rfl⟩⟩)
      ⟨fun n m h => hinj (congrArg Subtype.val h),
       fun ⟨y, hy⟩ => by
         rw [← hx₀_range] at hy
         rcases hy with ⟨n, rfl⟩
         exact ⟨n, rfl⟩⟩
    rw [← e.tsum_eq] at hsum_Λ
    exact hsum_Λ
  -- X is closed (by continuous_tsum with uniform M-test)
  have hX_closed : IsClosed X := by
    have hrew : X = ⋂ c : ℝ, ⋂ s : {s : ℝ // s ∈ Set.Ioc 0 (a / 10)},
        ⋂ t : {t : ℝ // t ∈ Set.Ioo (3 * a / 10) (7 * a / 10)},
        (fun x : ℤ → Sym => ∑' n : ℤ, term c s.1 t.1 n x) ⁻¹' {0} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, Subtype.forall, X,
        Set.mem_setOf_eq]
    rw [hrew]
    refine isClosed_iInter fun c => isClosed_iInter fun s => isClosed_iInter fun t => ?_
    obtain ⟨u, hu_sum, hu_bound⟩ := summable_sym_term hδ_pos s.2.1 hSigma_lo c t.1
    have hcont : Continuous (fun x : ℤ → Sym => ∑' n : ℤ, term c s.1 t.1 n x) := by
      refine continuous_tsum (u := u) (fun n => ?_) hu_sum (fun n x => hu_bound n x)
      have h1 : Continuous (fun x : ℤ → Sym => ((weightFn s.1 (symPos x n - c) : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp
          ((continuous_weightFn s.1).comp ((continuous_symPos n).sub continuous_const))
      have h2 : Continuous (fun x : ℤ → Sym =>
          Complex.exp (2 * Real.pi * Complex.I * (t.1 : ℂ) * ((symPos x n - c : ℝ) : ℂ))) :=
        Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_symPos n).sub continuous_const)))
      exact h1.mul h2
    exact isClosed_singleton.preimage hcont
  -- X is shift-invariant
  have hX_shift : ∀ x : ℤ → Sym, x ∈ X ↔ (fun n => x (n + 1)) ∈ X := by
    intro x
    constructor
    · intro hx c s hs t ht
      have h1 := hx (c + symPos x 1) s hs t ht
      have hrew : ∀ n : ℤ, term c s t n (fun k => x (k + 1)) =
          term (c + symPos x 1) s t (n + 1) x := by
        intro n
        simp only [term, symPos_shift x n]
        congr 2 <;> ring_nf
      simp_rw [hrew]
      rw [← (Equiv.addRight (1 : ℤ)).tsum_eq (fun m => term (c + symPos x 1) s t m x)] at h1
      exact h1
    · intro hx c s hs t ht
      have h1 := hx (c - symPos x 1) s hs t ht
      have hrew : ∀ n : ℤ, term (c - symPos x 1) s t n (fun k => x (k + 1)) =
          term c s t (n + 1) x := by
        intro n
        simp only [term, symPos_shift x n]
        congr 2 <;> ring_nf
      simp_rw [hrew] at h1
      have hshift : (∑' n : ℤ, term c s t (n + 1) x) = ∑' m : ℤ, term c s t m x :=
        (Equiv.addRight (1 : ℤ)).tsum_eq (fun m => term c s t m x)
      rw [hshift] at h1
      exact h1
  -- Left half-line determination (via Section 4)
  have hX_left : ∀ x ∈ X, ∀ y ∈ X, (∀ n < 0, x n = y n) → x = y := by
    intro x hx y hy hneg
    have hpos_le0 : ∀ n : ℤ, n ≤ 0 → symPos x n = symPos y n := by
      intro n hn
      cases n with
      | ofNat k =>
        have hk0 : k = 0 := by change (k : ℤ) ≤ 0 at hn; omega
        subst hk0; simp [symPos_zero]
      | negSucc k =>
        simp only [symPos]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hneg (-(j : ℤ) - 1) (by omega)]
    let A : Set ℝ := Set.range (fun k : ℕ => symPos x ((k + 1 : ℕ) : ℤ))
    let B : Set ℝ := Set.range (fun k : ℕ => symPos y ((k + 1 : ℕ) : ℤ))
    have hAB_eq : A = B := by
      have hAB_cnt : (A ∪ B).Countable := (Set.countable_range _).union (Set.countable_range _)
      haveI : Countable (A ∪ B : Set ℝ) := hAB_cnt.to_subtype
      have hpoint : ∀ (s : ℝ), s ∈ Set.Ioc 0 (a / 10) → ∀ r : (A ∪ B : Set ℝ),
          ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) -
          ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) = 0 := by
        intro s hs
        let cFn : (A ∪ B : Set ℝ) → ℂ := fun r =>
          ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) -
          ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ)
        have hx_nn : ∀ r : (A ∪ B : Set ℝ), 0 ≤ r.1 := by
          rintro ⟨r, (⟨k, rfl⟩ | ⟨k, rfl⟩)⟩
          · exact le_of_lt (by simpa [symPos_zero] using symPos_strictMono hδ_pos hSigma_lo x (show (0 : ℤ) < ((k + 1 : ℕ) : ℤ) by omega))
          · exact le_of_lt (by simpa [symPos_zero] using symPos_strictMono hδ_pos hSigma_lo y (show (0 : ℤ) < ((k + 1 : ℕ) : ℤ) by omega))
        -- Summability of weightFn s on A and on B
        obtain ⟨u, hu_sum, hu_bound⟩ := summable_sym_term hδ_pos hs.1 hSigma_lo 0 (a / 2)
        have hsum_x_nat : Summable (fun k : ℕ => weightFn s (symPos x ((k + 1 : ℕ) : ℤ))) := by
          have h1 : Summable (fun k : ℕ => u ((k + 1 : ℕ) : ℤ)) :=
            hu_sum.comp_injective fun a b h => by omega
          refine Summable.of_nonneg_of_le (fun _ => weightFn_nonneg s _) (fun k => ?_) h1
          have hb := hu_bound ((k + 1 : ℕ) : ℤ) x
          have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((a / 2 : ℝ) : ℂ) * ((symPos x ((k + 1 : ℕ) : ℤ) - 0 : ℝ) : ℂ))‖ = 1 := by
            have : 2 * Real.pi * Complex.I * ((a / 2 : ℝ) : ℂ) * ((symPos x ((k + 1 : ℕ) : ℤ) - 0 : ℝ) : ℂ) =
                Complex.I * ((2 * Real.pi * (a / 2) * (symPos x ((k + 1 : ℕ) : ℤ) - 0) : ℝ) : ℂ) := by push_cast; ring
            rw [this, Complex.norm_exp_I_mul_ofReal]
          rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg (weightFn_nonneg s _), sub_zero] at hb
          exact hb
        have hsum_y_nat : Summable (fun k : ℕ => weightFn s (symPos y ((k + 1 : ℕ) : ℤ))) := by
          have h1 : Summable (fun k : ℕ => u ((k + 1 : ℕ) : ℤ)) :=
            hu_sum.comp_injective fun a b h => by omega
          refine Summable.of_nonneg_of_le (fun _ => weightFn_nonneg s _) (fun k => ?_) h1
          have hb := hu_bound ((k + 1 : ℕ) : ℤ) y
          have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((a / 2 : ℝ) : ℂ) * ((symPos y ((k + 1 : ℕ) : ℤ) - 0 : ℝ) : ℂ))‖ = 1 := by
            have : 2 * Real.pi * Complex.I * ((a / 2 : ℝ) : ℂ) * ((symPos y ((k + 1 : ℕ) : ℤ) - 0 : ℝ) : ℂ) =
                Complex.I * ((2 * Real.pi * (a / 2) * (symPos y ((k + 1 : ℕ) : ℤ) - 0) : ℝ) : ℂ) := by push_cast; ring
            rw [this, Complex.norm_exp_I_mul_ofReal]
          rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg (weightFn_nonneg s _), sub_zero] at hb
          exact hb
        let eA : ℕ ≃ A := Equiv.ofBijective
          (fun k => ⟨symPos x ((k + 1 : ℕ) : ℤ), ⟨k, rfl⟩⟩)
          ⟨fun a b h => by
            have hval : symPos x ((a + 1 : ℕ) : ℤ) = symPos x ((b + 1 : ℕ) : ℤ) := congrArg Subtype.val h
            have := (symPos_strictMono hδ_pos hSigma_lo x).injective hval
            omega,
           fun ⟨r, k, hk⟩ => ⟨k, Subtype.ext hk⟩⟩
        let eB : ℕ ≃ B := Equiv.ofBijective
          (fun k => ⟨symPos y ((k + 1 : ℕ) : ℤ), ⟨k, rfl⟩⟩)
          ⟨fun a b h => by
            have hval : symPos y ((a + 1 : ℕ) : ℤ) = symPos y ((b + 1 : ℕ) : ℤ) := congrArg Subtype.val h
            have := (symPos_strictMono hδ_pos hSigma_lo y).injective hval
            omega,
           fun ⟨r, k, hk⟩ => ⟨k, Subtype.ext hk⟩⟩
        have hsum_A_sub : Summable (fun r : (A ∪ B : Set ℝ) => if r.1 ∈ A then weightFn s r.1 else 0) := by
          have h1 : Summable (fun r : A => weightFn s r.1) := (eA.summable_iff).mp hsum_x_nat
          let inc : A → (A ∪ B : Set ℝ) := fun r => ⟨r.1, Or.inl r.2⟩
          have hinc_inj : Function.Injective inc :=
            fun a b h => Subtype.ext (congrArg (fun z : (A ∪ B : Set ℝ) => z.1) h)
          rw [← Function.Injective.summable_iff hinc_inj]
          · exact h1.congr fun r => by simp [inc, r.2]
          · intro r hr
            have hnot : r.1 ∉ A := fun h => hr ⟨⟨r.1, h⟩, rfl⟩
            simp [hnot]
        have hsum_B_sub : Summable (fun r : (A ∪ B : Set ℝ) => if r.1 ∈ B then weightFn s r.1 else 0) := by
          have h1 : Summable (fun r : B => weightFn s r.1) := (eB.summable_iff).mp hsum_y_nat
          let inc : B → (A ∪ B : Set ℝ) := fun r => ⟨r.1, Or.inr r.2⟩
          have hinc_inj : Function.Injective inc :=
            fun a b h => Subtype.ext (congrArg (fun z : (A ∪ B : Set ℝ) => z.1) h)
          rw [← Function.Injective.summable_iff hinc_inj]
          · exact h1.congr fun r => by simp [inc, r.2]
          · intro r hr
            have hnot : r.1 ∉ B := fun h => hr ⟨⟨r.1, h⟩, rfl⟩
            simp [hnot]
        have hc_sum : Summable (fun r : (A ∪ B : Set ℝ) => ‖cFn r‖) := by
          refine (hsum_A_sub.add hsum_B_sub).of_nonneg_of_le (fun _ => norm_nonneg _) fun r => ?_
          dsimp only [cFn]
          calc
            ‖((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) - ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ)‖
                ≤ ‖((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ)‖ +
                  ‖((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ)‖ := norm_sub_le _ _
            _ = (if r.1 ∈ A then weightFn s r.1 else 0) + (if r.1 ∈ B then weightFn s r.1 else 0) := by
                  congr 1
                  · split_ifs <;> simp [Real.norm_of_nonneg (weightFn_nonneg s _)]
                  · split_ifs <;> simp [Real.norm_of_nonneg (weightFn_nonneg s _)]
        have hvan : ∀ t ∈ Set.Ioo (3 * a / 10) (7 * a / 10),
            ∑' r : (A ∪ B : Set ℝ), cFn r * Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ)) = 0 := by
          intro t ht
          obtain ⟨ut, hut_sum, hut_bound⟩ := summable_sym_term hδ_pos hs.1 hSigma_lo 0 t
          have hsum_tx : Summable (fun n : ℤ => term 0 s t n x) :=
            Summable.of_norm_bounded hut_sum (fun n => hut_bound n x)
          have hsum_ty : Summable (fun n : ℤ => term 0 s t n y) :=
            Summable.of_norm_bounded hut_sum (fun n => hut_bound n y)
          have hzero_x := hx 0 s hs t ht
          have hzero_y := hy 0 s hs t ht
          -- Split ℤ into PosZ = {n | 0 < n} and PosZᶜ
          let PosZ : Set ℤ := {n : ℤ | 0 < n}
          have hsp_x := hsum_tx.tsum_subtype_add_tsum_subtype_compl PosZ
          have hsp_y := hsum_ty.tsum_subtype_add_tsum_subtype_compl PosZ
          rw [hzero_x] at hsp_x
          rw [hzero_y] at hsp_y
          have hcompl_eq :
              (∑' n : ↥PosZᶜ, term 0 s t n.1 x) =
              (∑' n : ↥PosZᶜ, term 0 s t n.1 y) := by
            congr 1; funext n
            have hn_le : n.1 ≤ 0 := by
              have hnot : ¬ (0 < n.1) := n.2
              omega
            simp only [term, hpos_le0 n.1 hn_le]
          have hpos_eq_sum :
              (∑' n : PosZ, term 0 s t n.1 x) -
              (∑' n : PosZ, term 0 s t n.1 y) = 0 := by
            have h1 := eq_neg_of_add_eq_zero_left hsp_x
            have h2 := eq_neg_of_add_eq_zero_left hsp_y
            rw [h1, h2, hcompl_eq, sub_self]
          -- Relate ∑' r : A ∪ B to difference of sums over PosZ
          let ePos : ℕ ≃ PosZ :=
            ⟨fun k => ⟨((k + 1 : ℕ) : ℤ), by simp only [PosZ, Set.mem_setOf_eq]; omega⟩,
             fun n => (n.1 - 1).toNat,
             fun k => by dsimp only; omega,
             fun ⟨n, hn⟩ => Subtype.ext (by
               have hgt : 0 < n := hn
               dsimp only; omega)⟩
          have hterm_A :
              ∑' r : (A ∪ B : Set ℝ),
                ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ)) =
              ∑' n : PosZ, term 0 s t n.1 x := by
            let inc : A → (A ∪ B : Set ℝ) := fun r => ⟨r.1, Or.inl r.2⟩
            have hinc_inj : Function.Injective inc :=
              fun a b h => Subtype.ext (congrArg (fun z : (A ∪ B : Set ℝ) => z.1) h)
            have hsupp : ∀ r : (A ∪ B : Set ℝ), r ∉ Set.range inc →
                ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ)) = 0 := by
              intro r hr
              have hnot : r.1 ∉ A := fun h => hr ⟨⟨r.1, h⟩, rfl⟩
              simp [hnot]
            rw [← hinc_inj.tsum_eq (Function.support_subset_iff'.mpr hsupp)]
            simp only [inc, Subtype.coe_prop, ↓reduceIte]
            rw [← eA.tsum_eq, ← ePos.tsum_eq]
            have heA_val : ∀ k : ℕ, (eA k).1 = symPos x ((k + 1 : ℕ) : ℤ) := fun _ => rfl
            congr 1; funext k
            simp only [heA_val, ePos, term, Equiv.coe_fn_mk, sub_zero]
            congr 2; ring
          have hterm_B :
              ∑' r : (A ∪ B : Set ℝ),
                ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ)) =
              ∑' n : PosZ, term 0 s t n.1 y := by
            let inc : B → (A ∪ B : Set ℝ) := fun r => ⟨r.1, Or.inr r.2⟩
            have hinc_inj : Function.Injective inc :=
              fun a b h => Subtype.ext (congrArg (fun z : (A ∪ B : Set ℝ) => z.1) h)
            have hsupp : ∀ r : (A ∪ B : Set ℝ), r ∉ Set.range inc →
                ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ)) = 0 := by
              intro r hr
              have hnot : r.1 ∉ B := fun h => hr ⟨⟨r.1, h⟩, rfl⟩
              simp [hnot]
            rw [← hinc_inj.tsum_eq (Function.support_subset_iff'.mpr hsupp)]
            simp only [inc, Subtype.coe_prop, ↓reduceIte]
            rw [← eB.tsum_eq, ← ePos.tsum_eq]
            have heB_val : ∀ k : ℕ, (eB k).1 = symPos y ((k + 1 : ℕ) : ℤ) := fun _ => rfl
            congr 1; funext k
            simp only [heB_val, ePos, term, Equiv.coe_fn_mk, sub_zero]
            congr 2; ring
          have hsum_tA : Summable (fun r : (A ∪ B : Set ℝ) =>
              ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) *
                Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ))) := by
            refine Summable.of_norm_bounded hsum_A_sub fun r => ?_
            have he : ‖Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ))‖ = 1 := by
              have : 2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ) =
                  Complex.I * ((2 * Real.pi * r.1 * t : ℝ) : ℂ) := by push_cast; ring
              rw [this, Complex.norm_exp_I_mul_ofReal]
            rw [norm_mul, he, mul_one]
            split_ifs <;> simp [Real.norm_of_nonneg (weightFn_nonneg s _)]
          have hsum_tB : Summable (fun r : (A ∪ B : Set ℝ) =>
              ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) *
                Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ))) := by
            refine Summable.of_norm_bounded hsum_B_sub fun r => ?_
            have he : ‖Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ))‖ = 1 := by
              have : 2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ) =
                  Complex.I * ((2 * Real.pi * r.1 * t : ℝ) : ℂ) := by push_cast; ring
              rw [this, Complex.norm_exp_I_mul_ofReal]
            rw [norm_mul, he, mul_one]
            split_ifs <;> simp [Real.norm_of_nonneg (weightFn_nonneg s _)]
          have hsub_dist : (fun r : (A ∪ B : Set ℝ) =>
              cFn r * Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ))) =
              fun r =>
                ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ)) -
                ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t : ℂ)) := by
            funext r; dsimp only [cFn]; ring
          rw [hsub_dist, hsum_tA.tsum_sub hsum_tB, hterm_A, hterm_B, hpos_eq_sum]
        exact exp_sum_coeff_eq_zero_of_vanish_Ioo (by linarith : 3 * a / 10 < 7 * a / 10)
          hx_nn Subtype.val_injective hc_sum hvan
      ext r
      constructor
      · intro hrA
        obtain ⟨s, hs, hpos⟩ := exists_s_weightFn_pos ha_pos r
        have h0 := hpoint s hs ⟨r, Or.inl hrA⟩
        by_contra hrB
        simp only [hrA, hrB, ↓reduceIte, Complex.ofReal_zero, sub_zero, Complex.ofReal_eq_zero] at h0
        linarith
      · intro hrB
        obtain ⟨s, hs, hpos⟩ := exists_s_weightFn_pos ha_pos r
        have h0 := hpoint s hs ⟨r, Or.inr hrB⟩
        by_contra hrA
        simp only [hrA, hrB, ↓reduceIte, Complex.ofReal_zero, zero_sub, neg_eq_zero,
          Complex.ofReal_eq_zero] at h0
        linarith
    exact symPos_eq_of_nat_pos_range_eq hδ_pos hSigma_lo hneg hAB_eq
  -- Right half-line determination (symmetric via Section 4 on (-7a/10, -3a/10))
  have hX_right : ∀ x ∈ X, ∀ y ∈ X, (∀ n : ℤ, 0 ≤ n → x n = y n) → x = y := by
    intro x hx y hy hnonneg
    have hpos_ge0 : ∀ n : ℤ, 0 ≤ n → symPos x n = symPos y n := by
      intro n hn
      obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      simp only [symPos]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hnonneg (j : ℤ) (by omega)]
    let A : Set ℝ := Set.range (fun k : ℕ => -symPos x (Int.negSucc k))
    let B : Set ℝ := Set.range (fun k : ℕ => -symPos y (Int.negSucc k))
    have hAB_eq : A = B := by
      have hAB_cnt : (A ∪ B).Countable := (Set.countable_range _).union (Set.countable_range _)
      haveI : Countable (A ∪ B : Set ℝ) := hAB_cnt.to_subtype
      have hpoint : ∀ (s : ℝ), s ∈ Set.Ioc 0 (a / 10) → ∀ r : (A ∪ B : Set ℝ),
          ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) -
          ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) = 0 := by
        intro s hs
        let cFn : (A ∪ B : Set ℝ) → ℂ := fun r =>
          ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) -
          ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ)
        have hx_nn : ∀ r : (A ∪ B : Set ℝ), 0 ≤ r.1 := by
          rintro ⟨r, (⟨k, rfl⟩ | ⟨k, rfl⟩)⟩
          · have hlt := symPos_strictMono hδ_pos hSigma_lo x (show Int.negSucc k < 0 by omega)
            rw [symPos_zero] at hlt; linarith
          · have hlt := symPos_strictMono hδ_pos hSigma_lo y (show Int.negSucc k < 0 by omega)
            rw [symPos_zero] at hlt; linarith
        obtain ⟨u, hu_sum, hu_bound⟩ := summable_sym_term hδ_pos hs.1 hSigma_lo 0 (a / 2)
        have hsum_x_nat : Summable (fun k : ℕ => weightFn s (-symPos x (Int.negSucc k))) := by
          have h1 : Summable (fun k : ℕ => u (Int.negSucc k)) :=
            hu_sum.comp_injective fun a b h => by omega
          refine Summable.of_nonneg_of_le (fun _ => weightFn_nonneg s _) (fun k => ?_) h1
          rw [weightFn_even s hs.1]
          have hb := hu_bound (Int.negSucc k) x
          have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((a / 2 : ℝ) : ℂ) * ((symPos x (Int.negSucc k) - 0 : ℝ) : ℂ))‖ = 1 := by
            have : 2 * Real.pi * Complex.I * ((a / 2 : ℝ) : ℂ) * ((symPos x (Int.negSucc k) - 0 : ℝ) : ℂ) =
                Complex.I * ((2 * Real.pi * (a / 2) * (symPos x (Int.negSucc k) - 0) : ℝ) : ℂ) := by push_cast; ring
            rw [this, Complex.norm_exp_I_mul_ofReal]
          rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg (weightFn_nonneg s _), sub_zero] at hb
          exact hb
        have hsum_y_nat : Summable (fun k : ℕ => weightFn s (-symPos y (Int.negSucc k))) := by
          have h1 : Summable (fun k : ℕ => u (Int.negSucc k)) :=
            hu_sum.comp_injective fun a b h => by omega
          refine Summable.of_nonneg_of_le (fun _ => weightFn_nonneg s _) (fun k => ?_) h1
          rw [weightFn_even s hs.1]
          have hb := hu_bound (Int.negSucc k) y
          have he : ‖Complex.exp (2 * Real.pi * Complex.I * ((a / 2 : ℝ) : ℂ) * ((symPos y (Int.negSucc k) - 0 : ℝ) : ℂ))‖ = 1 := by
            have : 2 * Real.pi * Complex.I * ((a / 2 : ℝ) : ℂ) * ((symPos y (Int.negSucc k) - 0 : ℝ) : ℂ) =
                Complex.I * ((2 * Real.pi * (a / 2) * (symPos y (Int.negSucc k) - 0) : ℝ) : ℂ) := by push_cast; ring
            rw [this, Complex.norm_exp_I_mul_ofReal]
          rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg (weightFn_nonneg s _), sub_zero] at hb
          exact hb
        let eA : ℕ ≃ A := Equiv.ofBijective
          (fun k => ⟨-symPos x (Int.negSucc k), ⟨k, rfl⟩⟩)
          ⟨fun a b h => by
            have h0 : -symPos x (Int.negSucc a) = -symPos x (Int.negSucc b) := congrArg Subtype.val h
            have h1 := neg_injective h0
            have h2 := (symPos_strictMono hδ_pos hSigma_lo x).injective h1
            exact Int.negSucc.inj h2,
           fun ⟨r, k, hk⟩ => ⟨k, Subtype.ext hk⟩⟩
        let eB : ℕ ≃ B := Equiv.ofBijective
          (fun k => ⟨-symPos y (Int.negSucc k), ⟨k, rfl⟩⟩)
          ⟨fun a b h => by
            have h0 : -symPos y (Int.negSucc a) = -symPos y (Int.negSucc b) := congrArg Subtype.val h
            have h1 := neg_injective h0
            have h2 := (symPos_strictMono hδ_pos hSigma_lo y).injective h1
            exact Int.negSucc.inj h2,
           fun ⟨r, k, hk⟩ => ⟨k, Subtype.ext hk⟩⟩
        have hsum_A_sub : Summable (fun r : (A ∪ B : Set ℝ) => if r.1 ∈ A then weightFn s r.1 else 0) := by
          have h1 : Summable (fun r : A => weightFn s r.1) := (eA.summable_iff).mp hsum_x_nat
          let inc : A → (A ∪ B : Set ℝ) := fun r => ⟨r.1, Or.inl r.2⟩
          have hinc_inj : Function.Injective inc :=
            fun a b h => Subtype.ext (congrArg (fun z : (A ∪ B : Set ℝ) => z.1) h)
          rw [← Function.Injective.summable_iff hinc_inj]
          · exact h1.congr fun r => by simp [inc, r.2]
          · intro r hr
            have hnot : r.1 ∉ A := fun h => hr ⟨⟨r.1, h⟩, rfl⟩
            simp [hnot]
        have hsum_B_sub : Summable (fun r : (A ∪ B : Set ℝ) => if r.1 ∈ B then weightFn s r.1 else 0) := by
          have h1 : Summable (fun r : B => weightFn s r.1) := (eB.summable_iff).mp hsum_y_nat
          let inc : B → (A ∪ B : Set ℝ) := fun r => ⟨r.1, Or.inr r.2⟩
          have hinc_inj : Function.Injective inc :=
            fun a b h => Subtype.ext (congrArg (fun z : (A ∪ B : Set ℝ) => z.1) h)
          rw [← Function.Injective.summable_iff hinc_inj]
          · exact h1.congr fun r => by simp [inc, r.2]
          · intro r hr
            have hnot : r.1 ∉ B := fun h => hr ⟨⟨r.1, h⟩, rfl⟩
            simp [hnot]
        have hc_sum : Summable (fun r : (A ∪ B : Set ℝ) => ‖cFn r‖) := by
          refine (hsum_A_sub.add hsum_B_sub).of_nonneg_of_le (fun _ => norm_nonneg _) fun r => ?_
          dsimp only [cFn]
          calc
            ‖((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) - ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ)‖
                ≤ ‖((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ)‖ +
                  ‖((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ)‖ := norm_sub_le _ _
            _ = (if r.1 ∈ A then weightFn s r.1 else 0) + (if r.1 ∈ B then weightFn s r.1 else 0) := by
                  congr 1
                  · split_ifs <;> simp [Real.norm_of_nonneg (weightFn_nonneg s _)]
                  · split_ifs <;> simp [Real.norm_of_nonneg (weightFn_nonneg s _)]
        have hvan : ∀ t' ∈ Set.Ioo (-(7 * a / 10)) (-(3 * a / 10)),
            ∑' r : (A ∪ B : Set ℝ), cFn r * Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ)) = 0 := by
          intro t' ht'
          set t : ℝ := -t'
          have ht : t ∈ Set.Ioo (3 * a / 10) (7 * a / 10) := ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
          obtain ⟨ut, hut_sum, hut_bound⟩ := summable_sym_term hδ_pos hs.1 hSigma_lo 0 t
          have hsum_tx : Summable (fun n : ℤ => term 0 s t n x) :=
            Summable.of_norm_bounded hut_sum (fun n => hut_bound n x)
          have hsum_ty : Summable (fun n : ℤ => term 0 s t n y) :=
            Summable.of_norm_bounded hut_sum (fun n => hut_bound n y)
          let NegZ : Set ℤ := {n : ℤ | n < 0}
          have hsp_x := hsum_tx.tsum_subtype_add_tsum_subtype_compl NegZ
          have hsp_y := hsum_ty.tsum_subtype_add_tsum_subtype_compl NegZ
          rw [hx 0 s hs t ht] at hsp_x
          rw [hy 0 s hs t ht] at hsp_y
          have hcompl_eq :
              (∑' n : ↥NegZᶜ, term 0 s t n.1 x) =
              (∑' n : ↥NegZᶜ, term 0 s t n.1 y) := by
            congr 1; funext n
            have hn_ge : 0 ≤ n.1 := by
              have hnot : ¬ (n.1 < 0) := n.2
              omega
            simp only [term, hpos_ge0 n.1 hn_ge]
          have hneg_eq_sum :
              (∑' n : NegZ, term 0 s t n.1 x) -
              (∑' n : NegZ, term 0 s t n.1 y) = 0 := by
            have h1 := eq_neg_of_add_eq_zero_left hsp_x
            have h2 := eq_neg_of_add_eq_zero_left hsp_y
            rw [h1, h2, hcompl_eq, sub_self]
          let eNeg : ℕ ≃ NegZ :=
            ⟨fun k => ⟨Int.negSucc k, by simp only [NegZ, Set.mem_setOf_eq]; rw [Int.negSucc_eq]; omega⟩,
             fun n => (-n.1 - 1).toNat,
             fun k => by dsimp only; rw [Int.negSucc_eq]; omega,
             fun ⟨n, hn⟩ => Subtype.ext (by
               have hlt : n < 0 := hn
               dsimp only; rw [Int.negSucc_eq]; omega)⟩
          have hterm_A :
              ∑' r : (A ∪ B : Set ℝ),
                ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ)) =
              ∑' n : NegZ, term 0 s t n.1 x := by
            let inc : A → (A ∪ B : Set ℝ) := fun r => ⟨r.1, Or.inl r.2⟩
            have hinc_inj : Function.Injective inc :=
              fun a b h => Subtype.ext (congrArg (fun z : (A ∪ B : Set ℝ) => z.1) h)
            have hsupp : ∀ r : (A ∪ B : Set ℝ), r ∉ Set.range inc →
                ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ)) = 0 := by
              intro r hr
              have hnot : r.1 ∉ A := fun h => hr ⟨⟨r.1, h⟩, rfl⟩
              simp [hnot]
            rw [← hinc_inj.tsum_eq (Function.support_subset_iff'.mpr hsupp)]
            simp only [inc, Subtype.coe_prop, ↓reduceIte]
            rw [← eA.tsum_eq, ← eNeg.tsum_eq]
            have heA_val : ∀ k : ℕ, (eA k).1 = -symPos x (Int.negSucc k) := fun _ => rfl
            congr 1; funext k
            simp only [heA_val, eNeg, term, Equiv.coe_fn_mk, sub_zero, t]
            rw [weightFn_even s hs.1]
            congr 2; push_cast; ring
          have hterm_B :
              ∑' r : (A ∪ B : Set ℝ),
                ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ)) =
              ∑' n : NegZ, term 0 s t n.1 y := by
            let inc : B → (A ∪ B : Set ℝ) := fun r => ⟨r.1, Or.inr r.2⟩
            have hinc_inj : Function.Injective inc :=
              fun a b h => Subtype.ext (congrArg (fun z : (A ∪ B : Set ℝ) => z.1) h)
            have hsupp : ∀ r : (A ∪ B : Set ℝ), r ∉ Set.range inc →
                ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ)) = 0 := by
              intro r hr
              have hnot : r.1 ∉ B := fun h => hr ⟨⟨r.1, h⟩, rfl⟩
              simp [hnot]
            rw [← hinc_inj.tsum_eq (Function.support_subset_iff'.mpr hsupp)]
            simp only [inc, Subtype.coe_prop, ↓reduceIte]
            rw [← eB.tsum_eq, ← eNeg.tsum_eq]
            have heB_val : ∀ k : ℕ, (eB k).1 = -symPos y (Int.negSucc k) := fun _ => rfl
            congr 1; funext k
            simp only [heB_val, eNeg, term, Equiv.coe_fn_mk, sub_zero, t]
            rw [weightFn_even s hs.1]
            congr 2; push_cast; ring
          have hsum_tA : Summable (fun r : (A ∪ B : Set ℝ) =>
              ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) *
                Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ))) := by
            refine Summable.of_norm_bounded hsum_A_sub fun r => ?_
            have he : ‖Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ))‖ = 1 := by
              have : 2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ) =
                  Complex.I * ((2 * Real.pi * r.1 * t' : ℝ) : ℂ) := by push_cast; ring
              rw [this, Complex.norm_exp_I_mul_ofReal]
            rw [norm_mul, he, mul_one]
            split_ifs <;> simp [Real.norm_of_nonneg (weightFn_nonneg s _)]
          have hsum_tB : Summable (fun r : (A ∪ B : Set ℝ) =>
              ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) *
                Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ))) := by
            refine Summable.of_norm_bounded hsum_B_sub fun r => ?_
            have he : ‖Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ))‖ = 1 := by
              have : 2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ) =
                  Complex.I * ((2 * Real.pi * r.1 * t' : ℝ) : ℂ) := by push_cast; ring
              rw [this, Complex.norm_exp_I_mul_ofReal]
            rw [norm_mul, he, mul_one]
            split_ifs <;> simp [Real.norm_of_nonneg (weightFn_nonneg s _)]
          have hsub_dist : (fun r : (A ∪ B : Set ℝ) =>
              cFn r * Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ))) =
              fun r =>
                ((if r.1 ∈ A then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ)) -
                ((if r.1 ∈ B then weightFn s r.1 else 0) : ℂ) *
                  Complex.exp (2 * Real.pi * Complex.I * (r.1 : ℂ) * (t' : ℂ)) := by
            funext r; dsimp only [cFn]; ring
          rw [hsub_dist, hsum_tA.tsum_sub hsum_tB, hterm_A, hterm_B, hneg_eq_sum]
        exact exp_sum_coeff_eq_zero_of_vanish_Ioo (by linarith : -(7 * a / 10) < -(3 * a / 10))
          hx_nn Subtype.val_injective hc_sum hvan
      ext r
      constructor
      · intro hrA
        obtain ⟨s, hs, hpos⟩ := exists_s_weightFn_pos ha_pos r
        have h0 := hpoint s hs ⟨r, Or.inl hrA⟩
        by_contra hrB
        simp only [hrA, hrB, ↓reduceIte, Complex.ofReal_zero, sub_zero, Complex.ofReal_eq_zero] at h0
        linarith
      · intro hrB
        obtain ⟨s, hs, hpos⟩ := exists_s_weightFn_pos ha_pos r
        have h0 := hpoint s hs ⟨r, Or.inr hrB⟩
        by_contra hrA
        simp only [hrA, hrB, ↓reduceIte, Complex.ofReal_zero, zero_sub, neg_eq_zero,
          Complex.ofReal_eq_zero] at h0
        linarith
    exact symPos_eq_of_nat_neg_range_eq hδ_pos hSigma_lo hnonneg hAB_eq
  -- Compactness + Pigeonhole gives period q > 0 for x₀
  obtain ⟨q, hq_pos, hq_per⟩ :=
    exists_periodic_in_closed_shift_space hX_closed hX_shift hX_left hX_right hx₀_X
  -- Step 6: Convert periodicity of x₀ into Γ + qℤ and verify T = q via density 1
  set T : ℝ := symPos x₀ (q : ℤ)
  have hT_pos : 0 < T := by
    have h := symPos_strictMono hδ_pos hSigma_lo x₀ (show (0 : ℤ) < (q : ℤ) by omega)
    simpa [symPos_zero, T] using h
  have hpos_per : ∀ n : ℤ, symPos x₀ (n + (q : ℤ)) = symPos x₀ n + T := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [symPos_zero, T]
    | succ k ih =>
      have h1 : (k : ℤ) + 1 + (q : ℤ) = ((k : ℤ) + (q : ℤ)) + 1 := by ring
      rw [h1, symPos_succ, ih, symPos_succ, hq_per (k : ℤ)]
      ring
    | pred k ih =>
      have h1 : (-(k : ℤ) - 1) + (q : ℤ) + 1 = -(k : ℤ) + (q : ℤ) := by ring
      have h2 := symPos_succ x₀ (-(k : ℤ) - 1 + (q : ℤ))
      rw [h1, ih] at h2
      have h3 := symPos_succ x₀ (-(k : ℤ) - 1)
      have h4 : (-(k : ℤ) - 1) + 1 = -(k : ℤ) := by omega
      rw [h4] at h3
      rw [hq_per (-(k : ℤ) - 1)] at h2
      linarith
  have hpos_per_mul : ∀ (m : ℤ) (n : ℤ), symPos x₀ (n + (q : ℤ) * m) = symPos x₀ n + (m : ℝ) * T := by
    intro m
    induction m using Int.induction_on with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      have h1 : n + (q : ℤ) * ((k : ℤ) + 1) = (n + (q : ℤ) * (k : ℤ)) + (q : ℤ) := by ring
      rw [h1, hpos_per, ih]
      push_cast; ring
    | pred k ih =>
      intro n
      have h1 : (n + (q : ℤ) * (-(k : ℤ) - 1)) + (q : ℤ) = n + (q : ℤ) * (-(k : ℤ)) := by ring
      have h2 := hpos_per (n + (q : ℤ) * (-(k : ℤ) - 1))
      rw [h1, ih] at h2
      push_cast at h2 ⊢; linarith
  have hΛ_per : ∀ x : ℝ, x ∈ Λ ↔ x + T ∈ Λ := by
    intro x
    rw [← hx₀_range]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n + (q : ℤ), hpos_per n⟩
    · rintro ⟨n, hn⟩
      refine ⟨n - (q : ℤ), ?_⟩
      have h1 := hpos_per (n - (q : ℤ))
      rw [sub_add_cancel] at h1
      linarith
  let Γ : Finset ℝ := (Finset.range q).image (fun k : ℕ => symPos x₀ (k : ℤ))
  have hΓ_card : Γ.card = q := by
    rw [Finset.card_image_of_injective _ (fun a b h => by
      have := (symPos_strictMono hδ_pos hSigma_lo x₀).injective h
      omega), Finset.card_range]
  have hΓ_eq_Ico : (Γ : Set ℝ) = Λ ∩ Set.Ico 0 T := by
    ext y
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
      Set.mem_inter_iff, Set.mem_Ico, Γ]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨by rw [← hx₀_range]; exact ⟨(k : ℤ), rfl⟩, ?_, ?_⟩
      · have h := (symPos_strictMono hδ_pos hSigma_lo x₀).monotone (show (0 : ℤ) ≤ (k : ℤ) by omega)
        simpa [symPos_zero] using h
      · exact symPos_strictMono hδ_pos hSigma_lo x₀ (show (k : ℤ) < (q : ℤ) by omega)
    · rintro ⟨hyΛ, h0, hlt⟩
      rw [← hx₀_range] at hyΛ
      rcases hyΛ with ⟨n, rfl⟩
      have hn_ge : 0 ≤ n := by
        by_contra hlt0; push Not at hlt0
        have := symPos_strictMono hδ_pos hSigma_lo x₀ hlt0
        rw [symPos_zero] at this; linarith
      have hn_lt : n < (q : ℤ) := by
        by_contra hge; push Not at hge
        have := (symPos_strictMono hδ_pos hSigma_lo x₀).monotone hge
        linarith
      exact ⟨n.toNat, by omega, by rw [Int.toNat_of_nonneg hn_ge]⟩
  have hT_eq_q : (q : ℝ) = T := by
    have hcard_ico := period_eq_card_Ico hS_bdd hS_meas hS_vol hδ_pos hsep htile hT_pos hΛ_per
    rw [← hΓ_eq_Ico, Set.ncard_coe_finset, hΓ_card] at hcard_ico
    exact hcard_ico
  refine ⟨q, Γ, hq_pos, hΓ_card, ?_, ?_⟩
  · intro γ hγ
    have hmem : γ ∈ (Γ : Set ℝ) := hγ
    rw [hΓ_eq_Ico, ← hT_eq_q] at hmem
    exact hmem.2
  · have hset_eq : {ξ : Fin 1 → ℝ | ∃ γ ∈ Γ, ∃ m : ℤ, ξ 0 = γ + (q : ℝ) * (m : ℝ)} =
        {ξ : Fin 1 → ℝ | ξ 0 ∈ Λ} := by
      ext ξ
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨γ, hγ, m, hξ⟩
        rcases Finset.mem_image.mp hγ with ⟨k, hk, rfl⟩
        rw [← hx₀_range]
        refine ⟨(k : ℤ) + (q : ℤ) * m, ?_⟩
        rw [hpos_per_mul m (k : ℤ), ← hT_eq_q, hξ]
        ring
      · intro hξΛ
        rw [← hx₀_range] at hξΛ
        rcases hξΛ with ⟨n, hn⟩
        set m : ℤ := n / (q : ℤ)
        set r : ℤ := n % (q : ℤ)
        have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq_pos
        have hr_nn : 0 ≤ r := Int.emod_nonneg n hqZ.ne'
        have hr_lt : r < (q : ℤ) := Int.emod_lt_of_pos n hqZ
        have hdiv : r + (q : ℤ) * m = n := Int.emod_add_mul_ediv n (q : ℤ)
        refine ⟨symPos x₀ r, ?_, m, ?_⟩
        · exact Finset.mem_image.mpr ⟨r.toNat, Finset.mem_range.mpr (by omega), by
            rw [Int.toNat_of_nonneg hr_nn]⟩
        · rw [← hn, ← hdiv, hpos_per_mul m r, ← hT_eq_q]
          ring
    rw [hset_eq]
    exact hspΛ

end FugledeR1H3

theorem OMA.solution : OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1.H3 :=
  FugledeR1H3.main_H3
