import FormalConjectures.Arxiv.«2209.04540».SpectralSetsAndWeakTiling
import Mathlib
section
open MeasureTheory Complex Real
open scoped InnerProductSpace ComplexConjugate
namespace FCBridge
variable {d : ℕ}
noncomputable def aa (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) : ℂ :=
  ∫ x in Ω, exponentialCharacter ξ x
lemma ab (ξ η x : Fin d → ℝ) : exponentialCharacter (ξ + η) x = exponentialCharacter ξ x * exponentialCharacter η x := by
  unfold exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  push_cast
  ring
lemma ad (ξ x : Fin d → ℝ) : conj (exponentialCharacter ξ x) = exponentialCharacter (-ξ) x := by
  unfold exponentialCharacter
  rw [← Complex.exp_conj]
  congr 1
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring
lemma af (x : Fin d → ℝ) : exponentialCharacter 0 x = 1 := by
  simp [exponentialCharacter]
lemma ag (ξ₁ ξ₂ x : Fin d → ℝ) : conj (exponentialCharacter ξ₁ x) * exponentialCharacter ξ₂ x = exponentialCharacter (ξ₂ - ξ₁) x := by
  rw [ad, ← ab, neg_add_eq_sub]
lemma ah {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ₁ ξ₂ : Fin d → ℝ) : ⟪MemLp.toLp (exponentialCharacter ξ₁) (exponentialCharacter_memLp hΩ ξ₁), MemLp.toLp (exponentialCharacter ξ₂) (exponentialCharacter_memLp hΩ ξ₂)⟫_ℂ = aa Ω (ξ₂ - ξ₁) := by
  rw [MeasureTheory.L2.inner_def]
  unfold aa
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (exponentialCharacter_memLp hΩ ξ₁),
    MemLp.coeFn_toLp (exponentialCharacter_memLp hΩ ξ₂)] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', ag]
lemma ai (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) : aa Ω (-ξ) = conj (aa Ω ξ) := by
  unfold aa
  rw [← integral_conj]
  simp_rw [ad]
lemma aj (Ω : Set (Fin d → ℝ)) : aa Ω 0 = (volume.real Ω : ℂ) := by
  simp [aa, af]
lemma ak {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} (v : ι → H) : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ ↔ ∀ f : H, (∀ i, ⟪v i, f⟫_ℂ = 0) → f = 0 := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  refine forall_congr' fun f => ?_
  have : f ∈ (Submodule.span ℂ (Set.range v))ᗮ ↔ ∀ i, ⟪v i, f⟫_ℂ = 0 := by
    rw [Submodule.mem_orthogonal]
    constructor
    · intro h i
      exact h _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro h u hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact h i
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
  rw [this]
lemma al {Ω Λ : Set (Fin d → ℝ)} : spectralPair Ω Λ ↔ NullMeasurableSet Ω volume ∧ 0 < volume Ω ∧ ∃ hΩ : volume Ω ≠ ⊤, (∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ → aa Ω (ξ₂ - ξ₁) = 0) ∧ ∀ f : Lp ℂ 2 (volume.restrict Ω), (∀ ξ ∈ Λ, ⟪MemLp.toLp (exponentialCharacter ξ) (exponentialCharacter_memLp hΩ ξ), f⟫_ℂ = 0) → f = 0 := by
  unfold spectralPair
  refine and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun hΩ => ?_))
  simp only [ah hΩ]
  refine and_congr Iff.rfl ?_
  rw [ak]
  simp only [Subtype.forall]
def productSet {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) :
    Set (Fin (n + m) → ℝ) :=
  {x | (fun i ↦ x (Fin.castAdd m i)) ∈ A ∧ (fun j ↦ x (Fin.natAdd n j)) ∈ B}
noncomputable def am (n m : ℕ) : (Fin (n + m) → ℝ) ≃ᵐ (Fin n → ℝ) × (Fin m → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))
lemma splitEquiv_apply {n m : ℕ} (x : Fin (n + m) → ℝ) : am n m x = (fun i => x (Fin.castAdd m i), fun j => x (Fin.natAdd n j)) := by
  ext i <;> simp [am, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
lemma an (n m : ℕ) :
    MeasurePreserving (am n m) volume volume :=
  ((volume_measurePreserving_piCongrLeft (fun _ => ℝ) finSumFinEquiv).symm _).trans
    (volume_measurePreserving_sumPiEquivProdPi (fun _ => ℝ))
lemma ao {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) : productSet A B = am n m ⁻¹' (A ×ˢ B) := by
  ext x
  simp [productSet, splitEquiv_apply]
lemma ap {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) : volume (productSet A B) = volume A * volume B := by
  rw [ao, (an n m).measure_preimage_equiv, Measure.volume_eq_prod, Measure.prod_prod]
lemma aq {n m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)} (h : isSpectral (productSet A B)) : 0 < volume A ∧ 0 < volume B := by
  obtain ⟨Λ, -, hpos, -⟩ := h
  rw [ap] at hpos
  refine ⟨pos_iff_ne_zero.mpr fun h0 => ?_, pos_iff_ne_zero.mpr fun h0 => ?_⟩ <;>
    simp [h0] at hpos
lemma ar {n m : ℕ} (ξ : Fin n → ℝ) (η : Fin m → ℝ) (x : Fin (n + m) → ℝ) : exponentialCharacter (Fin.append ξ η) x = exponentialCharacter ξ (fun i => x (Fin.castAdd m i)) * exponentialCharacter η (fun j => x (Fin.natAdd n j)) := by
  unfold exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  push_cast
  ring
lemma as {n m : ℕ} (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) (ξ : Fin n → ℝ) (η : Fin m → ℝ) : aa (productSet A B) (Fin.append ξ η) = aa A ξ * aa B η := by
  unfold aa
  let g : (Fin n → ℝ) × (Fin m → ℝ) → ℂ := fun p =>
    exponentialCharacter ξ p.1 * exponentialCharacter η p.2
  have key := (an n m).setIntegral_preimage_emb
    (am n m).measurableEmbedding g (A ×ˢ B)
  rw [← ao] at key
  have hint : ∫ x in productSet A B, exponentialCharacter (Fin.append ξ η) x =
      ∫ x in productSet A B, g (am n m x) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [g]
    rw [ar, splitEquiv_apply]
  rw [hint, key, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_mul (fun a => exponentialCharacter ξ a) (fun b => exponentialCharacter η b)
section Affine
open Matrix
lemma au (ξ x b : Fin d → ℝ) : exponentialCharacter ξ (x + b) = exponentialCharacter ξ x * exponentialCharacter ξ b := by
  unfold exponentialCharacter
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  push_cast
  ring
lemma av (T : Matrix (Fin d) (Fin d) ℝ) (ξ y : Fin d → ℝ) : exponentialCharacter (Tᵀ *ᵥ ξ) y = exponentialCharacter ξ (T *ᵥ y) := by
  have h : (Tᵀ *ᵥ ξ) ⬝ᵥ y = ξ ⬝ᵥ (T *ᵥ y) := by
    rw [mulVec_transpose, dotProduct_mulVec]
  unfold exponentialCharacter
  change Complex.exp (2 * π * Complex.I * ((Tᵀ *ᵥ ξ) ⬝ᵥ y : ℝ)) =
    Complex.exp (2 * π * Complex.I * (ξ ⬝ᵥ (T *ᵥ y) : ℝ))
  rw [h]
lemma aw (ξ x : Fin d → ℝ) : exponentialCharacter (-ξ) x * exponentialCharacter ξ x = 1 := by
  rw [← ab, neg_add_cancel, af]
noncomputable def matLinEquiv (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin d)) T hT
lemma matLinEquiv_apply (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (y : Fin d → ℝ) : matLinEquiv T hT y = T *ᵥ y := by
  simp [matLinEquiv, Matrix.toLin_eq_toLin']
noncomputable def affEquiv (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (b : Fin d → ℝ) : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  ((matLinEquiv T hT).toContinuousLinearEquiv.toHomeomorph.trans
    (Homeomorph.addRight b)).toMeasurableEquiv
lemma affEquiv_apply (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b y : Fin d → ℝ) : affEquiv T hT b y = T *ᵥ y + b := by
  simp [affEquiv, matLinEquiv_apply]
lemma measurePreserving_affEquiv (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b : Fin d → ℝ) : MeasurePreserving (affEquiv T hT b) volume (ENNReal.ofReal |T.det|⁻¹ • volume) := by
  refine ⟨(affEquiv T hT b).measurable, ?_⟩
  have hdet : LinearMap.det ((matLinEquiv T hT : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) = T.det := by
    rw [show ((matLinEquiv T hT : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) =
      Matrix.toLin (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d)) T from rfl,
      LinearMap.det_toLin]
  have hlin : Measure.map (matLinEquiv T hT) volume =
      ENNReal.ofReal |T.det|⁻¹ • (volume : Measure (Fin d → ℝ)) := by
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin d → ℝ)))
      (f := (matLinEquiv T hT : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) (by rw [hdet]; exact hT.ne_zero)
    rw [hdet, abs_inv] at h
    exact h
  have hcomp : (affEquiv T hT b : (Fin d → ℝ) → (Fin d → ℝ)) =
      (fun x => x + b) ∘ (matLinEquiv T hT) := by
    funext y
    simp [affEquiv_apply, matLinEquiv_apply]
  have hmeas : Measurable (matLinEquiv T hT) :=
    (matLinEquiv T hT).toLinearMap.continuous_of_finiteDimensional.measurable
  rw [hcomp, ← Measure.map_map (measurable_add_const b) hmeas, hlin, Measure.map_smul, map_add_right_eq_self]
lemma ax (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b : Fin d → ℝ) (Ω : Set (Fin d → ℝ)) : volume (affEquiv T hT b ⁻¹' Ω) = ENNReal.ofReal |T.det|⁻¹ * volume Ω := by
  rw [(measurePreserving_affEquiv T hT b).measure_preimage_equiv, Measure.smul_apply, smul_eq_mul]
lemma ay (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b : Fin d → ℝ) (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) : aa (affEquiv T hT b ⁻¹' Ω) (Tᵀ *ᵥ ξ) = ((|T.det|⁻¹ : ℝ) : ℂ) * (exponentialCharacter (-ξ) b * aa Ω ξ) := by
  unfold aa
  have hpt : ∀ y, exponentialCharacter (Tᵀ *ᵥ ξ) y =
      exponentialCharacter (-ξ) b * exponentialCharacter ξ (affEquiv T hT b y) := by
    intro y
    rw [affEquiv_apply, au, av]
    rw [mul_comm (exponentialCharacter ξ (T *ᵥ y)), ← mul_assoc, aw, one_mul]
  simp_rw [hpt]
  rw [integral_const_mul, (measurePreserving_affEquiv T hT b).setIntegral_preimage_emb (affEquiv T hT b).measurableEmbedding (exponentialCharacter ξ) Ω, Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]
  rw [Complex.real_smul]
  ring
lemma az (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b : Fin d → ℝ) (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) : aa (affEquiv T hT b ⁻¹' Ω) (Tᵀ *ᵥ ξ) = 0 ↔ aa Ω ξ = 0 := by
  rw [ay]
  have h1 : ((|T.det|⁻¹ : ℝ) : ℂ) ≠ 0 := by
    simpa using hT.ne_zero
  have h2 : exponentialCharacter (-ξ) b ≠ 0 := by
    intro h
    have := norm_exponentialCharacter (-ξ) b
    rw [h, norm_zero] at this
    exact zero_ne_one this
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h h1
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h h2
    · exact h
  · intro h
    rw [h, mul_zero, mul_zero]
lemma aA {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b : Fin d → ℝ) : spectralPair (affEquiv T hT b ⁻¹' Ω) ((fun ξ => Tᵀ *ᵥ ξ) '' Λ) := by
  rw [al] at h ⊢
  obtain ⟨hmeas, hpos, hfin, horth, hcomp⟩ := h
  set S := affEquiv T hT b with hS
  set c : ENNReal := ENNReal.ofReal |T.det|⁻¹ with hc
  have hc0 : c ≠ 0 := by
    simpa [hc, ENNReal.ofReal_eq_zero, not_le] using hT.ne_zero
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmp : MeasurePreserving S volume (c • volume) := measurePreserving_affEquiv T hT b
  have hvol : volume (S ⁻¹' Ω) = c * volume Ω := ax T hT b Ω
  refine ⟨hmeas.mono_ac Measure.smul_absolutelyContinuous |>.preimage hmp.quasiMeasurePreserving,
    ?_, ?_, ?_⟩
  · rw [hvol]
    exact ENNReal.mul_pos hc0 hpos.ne'
  · rw [hvol]
    exact ENNReal.mul_ne_top hct hfin
  refine ⟨?_, ?_⟩
  · rintro _ ⟨ξ₁, h₁, rfl⟩ _ ⟨ξ₂, h₂, rfl⟩ hne
    have hne' : ξ₁ ≠ ξ₂ := fun h => hne (by rw [h])
    rw [← mulVec_sub, az]
    exact horth ξ₁ h₁ ξ₂ h₂ hne'
  · intro g hg
    have za : MeasurePreserving S (volume.restrict (S ⁻¹' Ω)) ((c • volume).restrict Ω) :=
      hmp.restrict_preimage_emb S.measurableEmbedding Ω
    have hmpR' : MeasurePreserving S.symm ((c • volume).restrict Ω)
        (volume.restrict (S ⁻¹' Ω)) := za.symm S
    set G : (Fin d → ℝ) → ℂ := ⇑g with hGdef
    have hF' : MemLp (G ∘ S.symm) 2 ((c • volume).restrict Ω) :=
      (Lp.memLp g).comp_measurePreserving hmpR'
    have hF : MemLp (G ∘ S.symm) 2 (volume.restrict Ω) := by
      rw [Measure.restrict_smul] at hF'
      refine hF'.of_measure_le_smul (c := c⁻¹) (ENNReal.inv_ne_top.mpr hc0) ?_
      rw [smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]
    have zb : ∀ ξ ∈ Λ, ⟪MemLp.toLp (exponentialCharacter ξ) (exponentialCharacter_memLp hfin ξ),
        hF.toLp (G ∘ S.symm)⟫_ℂ = 0 := by
      intro ξ hξ
      have h1 := hg (Tᵀ *ᵥ ξ) ⟨ξ, hξ, rfl⟩
      rw [MeasureTheory.L2.inner_def] at h1 ⊢
      have h1' : ∫ y in S ⁻¹' Ω, conj (exponentialCharacter (Tᵀ *ᵥ ξ) y) * G y = 0 := by
        rw [← h1]
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (exponentialCharacter_memLp
          (by rw [hvol]; exact ENNReal.mul_ne_top hct hfin) (Tᵀ *ᵥ ξ))] with y hy
        rw [hy, RCLike.inner_apply']
      have zc : ∫ x, ⟪(MemLp.toLp (exponentialCharacter ξ)
          (exponentialCharacter_memLp hfin ξ)) x, (hF.toLp (G ∘ S.symm)) x⟫_ℂ
            ∂volume.restrict Ω =
          ∫ x in Ω, conj (exponentialCharacter ξ x) * G (S.symm x) := by
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (exponentialCharacter_memLp hfin ξ),
          MemLp.coeFn_toLp hF] with x hx1 hx2
        rw [hx1, hx2, RCLike.inner_apply']
        rfl
      rw [zc]
      have hcv := hmp.setIntegral_preimage_emb S.measurableEmbedding
        (fun x => conj (exponentialCharacter ξ x) * G (S.symm x)) Ω
      rw [Measure.restrict_smul, integral_smul_measure] at hcv
      have hpt : ∀ y, conj (exponentialCharacter ξ (S y)) * G (S.symm (S y)) =
          exponentialCharacter (-ξ) b *
            (conj (exponentialCharacter (Tᵀ *ᵥ ξ) y) * G y) := by
        intro y
        rw [S.symm_apply_apply, hS, affEquiv_apply, au, map_mul, ad, ← av, ad]
        rw [ad, mulVec_neg]
        ring
      simp only [hpt] at hcv
      rw [integral_const_mul, h1', mul_zero] at hcv
      have hcr : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩
      exact (smul_eq_zero.mp hcv.symm).resolve_left hcr
    have hf0 := hcomp (hF.toLp (G ∘ S.symm)) zb
    have hF0 : (G ∘ S.symm) =ᵐ[volume.restrict Ω] 0 := by
      have h := MemLp.coeFn_toLp hF
      rw [hf0] at h
      exact h.symm.trans (Lp.coeFn_zero _ _ _)
    have hF0' : (G ∘ S.symm) =ᵐ[(c • volume).restrict Ω] 0 := by
      rw [Measure.restrict_smul]
      exact Measure.ae_smul_measure hF0 c
    have hG0 : G =ᵐ[volume.restrict (S ⁻¹' Ω)] 0 := by
      have := za.quasiMeasurePreserving.ae_eq_comp hF0'
      filter_upwards [this] with y hy
      simpa [Function.comp_def] using hy
    exact Lp.eq_zero_iff_ae_eq_zero.mpr hG0
lemma isSpectral_affEquiv_preimage {Ω : Set (Fin d → ℝ)} (h : isSpectral Ω)
    (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b : Fin d → ℝ) :
    isSpectral (affEquiv T hT b ⁻¹' Ω) :=
  let ⟨_, hΛ⟩ := h
  ⟨_, aA hΛ T hT b⟩
end Affine
end FCBridge
end
section
open MeasureTheory Complex Real Filter Topology Matrix
open scoped InnerProductSpace ComplexConjugate
namespace FCBridge
variable {d : ℕ}
noncomputable def aB {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ : Fin d → ℝ) :
    Lp ℂ 2 (volume.restrict Ω) :=
  MemLp.toLp (exponentialCharacter ξ) (exponentialCharacter_memLp hΩ ξ)
lemma aC {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ : Fin d → ℝ) :
    ⇑(aB hΩ ξ) =ᵐ[volume.restrict Ω] exponentialCharacter ξ :=
  MemLp.coeFn_toLp _
lemma aD {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ₁ ξ₂ : Fin d → ℝ) :
    ⟪aB hΩ ξ₁, aB hΩ ξ₂⟫_ℂ = aa Ω (ξ₂ - ξ₁) :=
  ah hΩ ξ₁ ξ₂
lemma aE {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ : Fin d → ℝ) : ‖aB hΩ ξ‖ ^ 2 = volume.real Ω := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), aD, sub_self, aj]
  simp
lemma aF (ξ x : Fin d → ℝ) : exponentialCharacter ξ x = exponentialCharacter x ξ := by
  unfold exponentialCharacter
  change Complex.exp (2 * π * Complex.I * ((ξ ⬝ᵥ x : ℝ) : ℂ)) =
    Complex.exp (2 * π * Complex.I * ((x ⬝ᵥ ξ : ℝ) : ℂ))
  rw [dotProduct_comm]
lemma aG {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) : Continuous (aa Ω) := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ
  unfold aa
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
    (fun ξ => (continuous_exponentialCharacter ξ).aestronglyMeasurable)
    (fun ξ => Eventually.of_forall fun x => (norm_exponentialCharacter ξ x).le)
    (integrable_const 1) (Eventually.of_forall fun x => ?_)
  simp_rw [aF _ x]
  exact continuous_exponentialCharacter x
lemma aH {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (G : Lp ℂ 2 (volume.restrict Ω)) : Continuous fun ξ => ⟪G, aB hΩ ξ⟫_ℂ := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ
  have hrepr : ∀ ξ, ⟪G, aB hΩ ξ⟫_ℂ =
      ∫ x in Ω, conj (G x) * exponentialCharacter ξ x := by
    intro ξ
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [aC hΩ ξ] with x hx
    rw [hx, RCLike.inner_apply']
  simp_rw [hrepr]
  have hGint : Integrable (fun x => ‖G x‖) (volume.restrict Ω) :=
    ((Lp.memLp G).integrable (by norm_num)).norm
  refine continuous_of_dominated (bound := fun x => ‖G x‖) (fun ξ => ?_) (fun ξ => ?_) hGint ?_
  · exact (continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable G)).mul
      (continuous_exponentialCharacter ξ).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [norm_mul, norm_exponentialCharacter, mul_one, RCLike.norm_conj]
  · refine Eventually.of_forall fun x => ?_
    simp_rw [aF _ x]
    exact continuous_const.mul (continuous_exponentialCharacter x)
def aI (Ω Λ : Set (Fin d → ℝ)) : Prop :=
  ∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ → aa Ω (ξ₂ - ξ₁) = 0
lemma aI.countable {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) (horth : aI Ω Λ) : Λ.Countable := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  set ρ := Real.sqrt (volume.real Ω) / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hdist : ∀ ξ₁ ∈ Λ, ∀ ξ₂ ∈ Λ, ξ₁ ≠ ξ₂ → ρ + ρ ≤ dist (aB hΩ ξ₁) (aB hΩ ξ₂) := by
    intro ξ₁ h₁ ξ₂ h₂ hne
    rw [dist_eq_norm]
    have hsq : ‖aB hΩ ξ₁ - aB hΩ ξ₂‖ ^ 2 = 2 * volume.real Ω := by
      rw [norm_sub_sq (𝕜 := ℂ), aD, horth ξ₁ h₁ ξ₂ h₂ hne, aE, aE]
      simp only [map_zero, mul_zero, sub_zero]
      ring
    have : Real.sqrt (volume.real Ω) ≤ ‖aB hΩ ξ₁ - aB hΩ ξ₂‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), hsq]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  refine Set.PairwiseDisjoint.countable_of_isOpen
    (s := fun ξ => Metric.ball (aB hΩ ξ) ρ) ?_ (fun _ _ => Metric.isOpen_ball)
    (fun ξ _ => ⟨_, Metric.mem_ball_self hρpos⟩)
  intro ξ₁ h₁ ξ₂ h₂ hne
  exact Metric.ball_disjoint_ball (hdist ξ₁ h₁ ξ₂ h₂ hne)
noncomputable def aJ {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (Λ : Set (Fin d → ℝ)) :
    Λ → Lp ℂ 2 (volume.restrict Ω) :=
  fun ξ => ((Real.sqrt (volume.real Ω))⁻¹ : ℂ) • aB hΩ ξ
lemma aK {a : ℝ} (ha : 0 < a) : ((Real.sqrt a)⁻¹ : ℂ) * ((Real.sqrt a)⁻¹ : ℂ) * (a : ℂ) = 1 := by
  have h2 : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have h3 : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2
  have h4 : ((a : ℝ) : ℂ) = ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ha.le]
  rw [h4]
  field_simp
lemma aL {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) (horth : aI Ω Λ) : Orthonormal ℂ (aJ hΩ Λ) := by
  classical
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  rw [orthonormal_iff_ite]
  intro i j
  simp only [aJ, inner_smul_left, inner_smul_right, aD, Complex.conj_ofReal, map_inv₀]
  split_ifs with hij
  · subst hij
    rw [sub_self, aj, ← mul_assoc]
    exact aK hr
  · have : (i : Fin d → ℝ) ≠ j := fun h => hij (Subtype.ext h)
    rw [horth i i.2 j j.2 this]
    simp
lemma aM {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) (i : Λ) (ξ : Fin d → ℝ) : ‖⟪aJ hΩ Λ i, aB hΩ ξ⟫_ℂ‖ ^ 2 = ‖aa Ω (ξ - i)‖ ^ 2 / volume.real Ω := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  simp only [aJ, inner_smul_left, aD, norm_mul, RCLike.norm_conj]
  rw [mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hr), inv_pow, Real.sq_sqrt hr.le]
  ring
lemma aI.summable_tsum_le {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) (horth : aI Ω Λ) (ξ : Fin d → ℝ) : Summable (fun i : Λ => ‖aa Ω (ξ - i)‖ ^ 2) ∧ ∑' i : Λ, ‖aa Ω (ξ - i)‖ ^ 2 ≤ volume.real Ω ^ 2 := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  have hv := aL hΩ hpos horth
  have hs := hv.inner_products_summable (x := aB hΩ ξ)
  have hb := hv.tsum_inner_products_le (x := aB hΩ ξ)
  simp_rw [aM hΩ hpos] at hs hb
  rw [aE] at hb
  have hs' : Summable (fun i : Λ => ‖aa Ω (ξ - i)‖ ^ 2) := by
    simpa [div_mul_cancel₀ _ hr.ne'] using hs.mul_right (volume.real Ω)
  refine ⟨hs', ?_⟩
  rw [tsum_div_const] at hb
  rw [div_le_iff₀ hr] at hb
  nlinarith
lemma aN {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) : Submodule.span ℂ (Set.range (aJ hΩ Λ)) = Submodule.span ℂ (Set.range fun ξ : Λ => aB hΩ ξ) := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  have hc : ((Real.sqrt (volume.real Ω))⁻¹ : ℂ) ≠ 0 := by
    simp [(Real.sqrt_pos.mpr hr).ne']
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    dsimp only
    have : aB hΩ i = ((Real.sqrt (volume.real Ω))⁻¹ : ℂ)⁻¹ • aJ hΩ Λ i := by
      simp only [aJ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
noncomputable def aO {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (h : spectralPair Ω Λ) : HilbertBasis Λ ℂ (Lp ℂ 2 (volume.restrict Ω)) :=
  HilbertBasis.mk (aL hΩ h.2.1 (by
      obtain ⟨-, -, hΩ', horth, -⟩ := al.mp h
      exact horth))
    (by
      obtain ⟨-, hpos, hΩ', -, hcomp⟩ := h
      rw [aN hΩ hpos]
      exact hcomp.ge)
lemma aP {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤)
    (h : spectralPair Ω Λ) : ⇑(aO hΩ h) = aJ hΩ Λ :=
  HilbertBasis.coe_mk _ _
lemma aQ {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (h : spectralPair Ω Λ) (G : Lp ℂ 2 (volume.restrict Ω)) : HasSum (fun i : Λ => ‖⟪aJ hΩ Λ i, G⟫_ℂ‖ ^ 2) (‖G‖ ^ 2) := by
  set b := aO hΩ h
  have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  have := lp.hasSum_norm hp (b.repr G)
  simp only [HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map] at this
  rw [aP] at this
  simpa [Real.rpow_two] using this
lemma aR {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (ξ : Fin d → ℝ) : HasSum (fun i : Λ => ‖aa Ω (ξ - i)‖ ^ 2) (volume.real Ω ^ 2) := by
  have hh := h
  obtain ⟨-, hpos, hΩ, -⟩ := hh
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  have hs := aQ hΩ h (aB hΩ ξ)
  simp_rw [aM hΩ hpos] at hs
  rw [aE] at hs
  have := hs.mul_right (volume.real Ω)
  simp only [div_mul_cancel₀ _ hr.ne'] at this
  rw [sq]
  exact this
lemma aS {Ω Λ : Set (Fin d → ℝ)} (hmeas : NullMeasurableSet Ω volume) (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) (horth : aI Ω Λ) (htot : ∀ G : Lp ℂ 2 (volume.restrict Ω), (∀ ξ, ⟪aB hΩ ξ, G⟫_ℂ = 0) → G = 0) (htile : ∀ᵐ ξ ∂volume, ∑' i : Λ, ‖aa Ω (ξ - i)‖ ^ 2 = volume.real Ω ^ 2) : spectralPair Ω Λ := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  rw [al]
  refine ⟨hmeas, hpos, hΩ, horth, fun G hG => ?_⟩
  have hG' : ∀ i : Λ, ⟪aJ hΩ Λ i, G⟫_ℂ = 0 := by
    intro i
    simp only [aJ, inner_smul_left]
    rw [show ⟪aB hΩ (i : Fin d → ℝ), G⟫_ℂ = 0 from hG i i.2, mul_zero]
  apply htot
  have hφae : ∀ᵐ ξ ∂volume, ⟪G, aB hΩ ξ⟫_ℂ = 0 := by
    filter_upwards [htile] with ξ hξ
    by_cases hG0 : G = 0
    · simp [hG0]
    have hGn : ‖G‖ ≠ 0 := norm_ne_zero_iff.mpr hG0
    let w : Unit ⊕ Λ → Lp ℂ 2 (volume.restrict Ω) :=
      Sum.elim (fun _ => ((‖G‖⁻¹ : ℝ) : ℂ) • G) (aJ hΩ Λ)
    have hv := aL hΩ hpos horth
    have hw : Orthonormal ℂ w := by
      refine ⟨?_, ?_⟩
      · rintro (u | i)
        · simp only [w, Sum.elim_inl, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_inv, abs_norm]
          exact inv_mul_cancel₀ hGn
        · exact hv.1 i
      · rintro (u | i) (u' | j) hne
        · exact absurd (by cases u; cases u'; rfl) hne
        · simp only [w, Sum.elim_inl, Sum.elim_inr, inner_smul_left]
          rw [← inner_conj_symm, hG' j, map_zero, mul_zero]
        · simp only [w, Sum.elim_inl, Sum.elim_inr, inner_smul_right, hG' i, mul_zero]
        · exact hv.2 (fun h => hne (congrArg Sum.inr h))
    have hsum := hw.inner_products_summable (x := aB hΩ ξ)
    have za := hw.tsum_inner_products_le (x := aB hΩ ξ)
    rw [Summable.tsum_sum (hsum.comp_injective Sum.inl_injective) (hsum.comp_injective Sum.inr_injective)] at za
    simp only [w, Sum.elim_inl, Sum.elim_inr, tsum_const, Nat.card_unique, one_smul] at za
    simp_rw [aM hΩ hpos] at za
    rw [tsum_div_const, hξ, aE] at za
    have hle : ‖⟪((‖G‖⁻¹ : ℝ) : ℂ) • G, aB hΩ ξ⟫_ℂ‖ ^ 2 ≤ 0 := by
      have : volume.real Ω ^ 2 / volume.real Ω = volume.real Ω := by
        field_simp
      linarith
    have h0 : ⟪((‖G‖⁻¹ : ℝ) : ℂ) • G, aB hΩ ξ⟫_ℂ = 0 := by
      have := le_antisymm hle (sq_nonneg _)
      simpa using this
    rw [inner_smul_left] at h0
    simpa [hGn] using h0
  have hφ0 := (Continuous.ae_eq_iff_eq volume (aH hΩ G)
    continuous_const).mp hφae
  intro ξ
  have := congrFun hφ0 ξ
  rw [← inner_conj_symm]
  simp [this]
lemma aT (L : StrongDual ℝ (Fin d → ℝ)) : ∃ ξ : Fin d → ℝ, ∀ x, Complex.exp (L x * Complex.I) = exponentialCharacter ξ x := by
  classical
  set c : Fin d → ℝ := fun i => L (fun j => if i = j then 1 else 0) with hc
  refine ⟨fun i => c i / (2 * π), fun x => ?_⟩
  have hL : L x = ∑ i, x i * c i := by
    conv_lhs => rw [pi_eq_sum_univ x]
    simp [map_sum, map_smul, hc, smul_eq_mul]
  unfold exponentialCharacter
  rw [hL]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
lemma aU {μ : Measure (Fin d → ℝ)} {g : (Fin d → ℝ) → ℂ}
    (hg : Integrable g μ) (ξ : Fin d → ℝ) :
    Integrable (fun x => g x * exponentialCharacter ξ x) μ :=
  hg.mul_bdd (continuous_exponentialCharacter ξ).aestronglyMeasurable
    (Eventually.of_forall fun x => (norm_exponentialCharacter ξ x).le)
lemma aV {μ : Measure (Fin d → ℝ)} [IsFiniteMeasure μ] {w : (Fin d → ℝ) → ℝ} (hw : Integrable w μ) (h : ∀ ξ, ∫ x, (w x : ℂ) * exponentialCharacter ξ x ∂μ = 0) : w =ᵐ[μ] 0 := by
  set fp : (Fin d → ℝ) → ENNReal := fun x => ENNReal.ofReal (w x) with hfp_def
  set fm : (Fin d → ℝ) → ENNReal := fun x => ENNReal.ofReal (-w x) with hfm_def
  have hfp : AEMeasurable fp μ := hw.aemeasurable.ennreal_ofReal
  have hfm : AEMeasurable fm μ := hw.neg.aemeasurable.ennreal_ofReal
  have za : ∫⁻ x, fp x ∂μ ≠ ⊤ := hw.lintegral_lt_top.ne
  have zb : ∫⁻ x, fm x ∂μ ≠ ⊤ := hw.neg.lintegral_lt_top.ne
  have : IsFiniteMeasure (μ.withDensity fp) := isFiniteMeasure_withDensity za
  have : IsFiniteMeasure (μ.withDensity fm) := isFiniteMeasure_withDensity zb
  have zc : ∀ (v : (Fin d → ℝ) → ℝ), Integrable v μ → ∀ ξ,
      ∫ x, exponentialCharacter ξ x ∂μ.withDensity (fun x => ENNReal.ofReal (v x)) =
        ∫ x, ((max (v x) 0 : ℝ) : ℂ) * exponentialCharacter ξ x ∂μ := by
    intro v hv ξ
    rw [integral_withDensity_eq_integral_toReal_smul₀ hv.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofReal', Complex.real_smul]
  have hchar : charFunDual (μ.withDensity fp) = charFunDual (μ.withDensity fm) := by
    funext L
    obtain ⟨ξ, hξ⟩ := aT L
    rw [charFunDual_apply, charFunDual_apply]
    simp_rw [hξ]
    have hwn : Integrable (fun x => -w x) μ := hw.neg
    rw [zc w hw ξ, zc (fun x => -w x) hwn ξ, ← sub_eq_zero]
    calc _ = ∫ x, (((max (w x) 0 : ℝ) : ℂ) * exponentialCharacter ξ x -
            ((max (-w x) 0 : ℝ) : ℂ) * exponentialCharacter ξ x) ∂μ :=
          (integral_sub (aU hw.pos_part.ofReal ξ)
            (aU hwn.pos_part.ofReal ξ)).symm
      _ = ∫ x, (w x : ℂ) * exponentialCharacter ξ x ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          have hm : max (w x) 0 - max (-w x) 0 = w x := by
            rcases le_total 0 (w x) with h0 | h0
            · rw [max_eq_left h0, max_eq_right (by linarith)]
              ring
            · rw [max_eq_right h0, max_eq_left (by linarith)]
              ring
          simp only
          rw [← sub_mul, ← Complex.ofReal_sub, hm]
      _ = 0 := h ξ
  have hae := (withDensity_eq_iff hfp hfm za).mp (Measure.ext_of_charFunDual hchar)
  filter_upwards [hae] with x hx
  simp only [hfp_def, hfm_def] at hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : ENNReal.ofReal (w x) = 0 := ENNReal.ofReal_of_nonpos hlt.le
    have h2 : 0 < ENNReal.ofReal (-w x) := ENNReal.ofReal_pos.mpr (by simpa using hlt)
    rw [hx] at h1
    exact h2.ne' h1
  · have h1 : 0 < ENNReal.ofReal (w x) := ENNReal.ofReal_pos.mpr hgt
    have h2 : ENNReal.ofReal (-w x) = 0 := ENNReal.ofReal_of_nonpos (by simp at hgt ⊢; linarith)
    rw [hx] at h1
    exact h1.ne' h2
lemma aW {μ : Measure (Fin d → ℝ)} [IsFiniteMeasure μ] {g : (Fin d → ℝ) → ℂ} (hg : Integrable g μ) (h : ∀ ξ, ∫ x, g x * exponentialCharacter ξ x ∂μ = 0) : g =ᵐ[μ] 0 := by
  have za : ∀ ξ, conj (∫ x, g x * exponentialCharacter (-ξ) x ∂μ) =
      ∫ x, conj (g x) * exponentialCharacter ξ x ∂μ := by
    intro ξ
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_mul, ad, neg_neg]
  have hgc : Integrable (fun x => conj (g x)) μ :=
    hg.mono (continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
      (Eventually.of_forall fun x => by rw [RCLike.norm_conj])
  have hre : (fun x => (g x).re) =ᵐ[μ] 0 := by
    refine aV hg.re fun ξ => ?_
    have hsplit : ∫ x, ((g x).re : ℂ) * exponentialCharacter ξ x ∂μ =
        (∫ x, g x * exponentialCharacter ξ x ∂μ +
          ∫ x, conj (g x) * exponentialCharacter ξ x ∂μ) / 2 := by
      rw [← integral_add (aU hg ξ) (aU hgc ξ), ← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [Complex.re_eq_add_conj]
      ring
    rw [hsplit, h ξ, ← za, h (-ξ), map_zero]
    simp
  have him : (fun x => (g x).im) =ᵐ[μ] 0 := by
    refine aV hg.im fun ξ => ?_
    have hsplit : ∫ x, ((g x).im : ℂ) * exponentialCharacter ξ x ∂μ =
        (∫ x, g x * exponentialCharacter ξ x ∂μ -
          ∫ x, conj (g x) * exponentialCharacter ξ x ∂μ) / (2 * Complex.I) := by
      rw [← integral_sub (aU hg ξ) (aU hgc ξ), ← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [Complex.im_eq_sub_conj]
      ring
    rw [hsplit, h ξ, ← za, h (-ξ), map_zero]
    simp
  filter_upwards [hre, him] with x h1 h2
  apply Complex.ext
  · simpa using h1
  · simpa using h2
lemma aX {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (G : Lp ℂ 2 (volume.restrict Ω)) (h : ∀ ξ, ⟪aB hΩ ξ, G⟫_ℂ = 0) : G = 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ
  have hGint : Integrable (⇑G) (volume.restrict Ω) := (Lp.memLp G).integrable (by norm_num)
  have hrepr : ∀ ξ, ⟪aB hΩ ξ, G⟫_ℂ =
      ∫ x, G x * exponentialCharacter (-ξ) x ∂(volume.restrict Ω) := by
    intro ξ
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [aC hΩ ξ] with x hx
    rw [hx, RCLike.inner_apply', ad, mul_comm]
  have hae := aW hGint fun ξ => by
    rw [← neg_neg ξ, ← hrepr (-ξ), h]
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae
lemma aY {Ω Λ : Set (Fin d → ℝ)}
    (hmeas : NullMeasurableSet Ω volume) (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω)
    (horth : aI Ω Λ)
    (htile : ∀ᵐ ξ ∂volume, ∑' i : Λ, ‖aa Ω (ξ - i)‖ ^ 2 = volume.real Ω ^ 2) :
    spectralPair Ω Λ :=
  aS hmeas hΩ hpos horth (aX hΩ) htile
end FCBridge
end
section
open MeasureTheory Complex Real Filter Topology Matrix
open scoped InnerProductSpace ComplexConjugate
namespace FCBridge
variable {d : ℕ}
def aZ (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi fun _ => Set.Ico (0 : ℝ) 1
def a3 (d : ℕ) : Set (Fin d → ℝ) := Set.range fun k : Fin d → ℤ => fun i => (k i : ℝ)
lemma a4 (ξ x : Fin d → ℝ) : exponentialCharacter ξ x = ∏ i, Complex.exp (2 * π * Complex.I * ((ξ i : ℂ) * (x i : ℂ))) := by
  unfold exponentialCharacter
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
lemma a5 (k : ℤ) (hk : k ≠ 0) : ∫ t in Set.Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * (((k : ℝ) : ℂ) * (t : ℂ))) = 0 := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hc : (2 * π * Complex.I * (k : ℂ)) ≠ 0 := by
    simp [Real.pi_ne_zero, hk, Complex.I_ne_zero]
  have hpt : ∀ t : ℝ, Complex.exp (2 * π * Complex.I * (((k : ℝ) : ℂ) * (t : ℂ))) =
      Complex.exp ((2 * π * Complex.I * (k : ℂ)) * t) := by
    intro t
    push_cast
    ring_nf
  simp_rw [hpt]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((2 * π * Complex.I * (k : ℂ)) * ((1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.ofReal_one, mul_one,
      show 2 * (π : ℂ) * Complex.I * k = k * (2 * π * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [h1]
  simp
lemma a6 {k : Fin d → ℤ} (hk : k ≠ 0) : aa (aZ d) (fun i => (k i : ℝ)) = 0 := by
  unfold aa aZ
  rw [volume_pi, Measure.restrict_pi_pi]
  simp_rw [a4]
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) => Complex.exp (2 * π * Complex.I * (((k i : ℝ) : ℂ) * (t : ℂ))))]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  exact Finset.prod_eq_zero (Finset.mem_univ i) (a5 (k i) hi)
lemma a7 : aI (aZ d) (a3 d) := by
  rintro _ ⟨k₁, rfl⟩ _ ⟨k₂, rfl⟩ hne
  have hk : k₂ - k₁ ≠ 0 := by
    intro h
    apply hne
    funext i
    have := congrFun h i
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    simp [this]
  have := a6 hk
  convert this using 2
  funext i
  simp
lemma a8 : volume (aZ d) = 1 := by
  rw [aZ, volume_pi_pi]
  simp [Real.volume_Ico]
lemma aI.affEquiv_preimage {Ω Λ : Set (Fin d → ℝ)} (h : aI Ω Λ) (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (b : Fin d → ℝ) : aI (affEquiv T hT b ⁻¹' Ω) ((fun ξ => Tᵀ *ᵥ ξ) '' Λ) := by
  rintro _ ⟨ξ₁, h₁, rfl⟩ _ ⟨ξ₂, h₂, rfl⟩ hne
  have hne' : ξ₁ ≠ ξ₂ := fun h => hne (by rw [h])
  rw [← mulVec_sub, az]
  exact h ξ₁ h₁ ξ₂ h₂ hne'
lemma aI.tsum_normSq_ftInd_le_of_subset {Ω Q Γ : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩQ : Ω ⊆ Q) (hQ : volume Q ≠ ⊤) (hQpos : 0 < volume Q) (horth : aI Q Γ) (x : Fin d → ℝ) : Summable (fun γ : Γ => ‖aa Ω (x - γ)‖ ^ 2) ∧ ∑' γ : Γ, ‖aa Ω (x - γ)‖ ^ 2 ≤ volume.real Q * volume.real Ω := by
  have hr : 0 < volume.real Q := ENNReal.toReal_pos hQpos.ne' hQ
  have : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hQ
  have hv := aL hQ hQpos horth
  have hmem : MemLp (Ω.indicator (exponentialCharacter x)) 2 (volume.restrict Q) := by
    refine MemLp.of_bound
      ((continuous_exponentialCharacter x).aestronglyMeasurable.indicator hΩm) 1
      (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Ω
    · simp [Set.indicator_of_mem hy, norm_exponentialCharacter]
    · simp [Set.indicator_of_notMem hy]
  set v := hmem.toLp (Ω.indicator (exponentialCharacter x)) with hvdef
  have hpt : ∀ γ : Fin d → ℝ, ∀ y, conj (exponentialCharacter γ y) *
      Ω.indicator (exponentialCharacter x) y = Ω.indicator (exponentialCharacter (x - γ)) y := by
    intro γ y
    by_cases hy : y ∈ Ω
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ag]
    · simp [Set.indicator_of_notMem hy]
  have za : ∀ γ : Fin d → ℝ, ⟪aB hQ γ, v⟫_ℂ = aa Ω (x - γ) := by
    intro γ
    rw [MeasureTheory.L2.inner_def]
    calc _ = ∫ y in Q, Ω.indicator (exponentialCharacter (x - γ)) y := by
          refine integral_congr_ae ?_
          filter_upwards [aC hQ γ, MemLp.coeFn_toLp hmem] with y h1 h2
          rw [h1, h2, RCLike.inner_apply', hpt]
      _ = ∫ y in Q ∩ Ω, exponentialCharacter (x - γ) y := setIntegral_indicator hΩm
      _ = aa Ω (x - γ) := by rw [Set.inter_eq_right.mpr hΩQ]; rfl
  have zb : ‖v‖ ^ 2 = volume.real Ω := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def]
    have : ∫ y, ⟪v y, v y⟫_ℂ ∂(volume.restrict Q) = ∫ y in Q, Ω.indicator (fun _ => (1 : ℂ)) y := by
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hmem] with y h
      rw [h, RCLike.inner_apply']
      by_cases hy : y ∈ Ω
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ag,
          sub_self, af]
      · simp [Set.indicator_of_notMem hy]
    rw [this, setIntegral_indicator hΩm, Set.inter_eq_right.mpr hΩQ]
    simp [measureReal_def]
  have hterm : ∀ γ : Γ, ‖⟪aJ hQ Γ γ, v⟫_ℂ‖ ^ 2 = ‖aa Ω (x - γ)‖ ^ 2 / volume.real Q := by
    intro γ
    simp only [aJ, inner_smul_left, za, norm_mul, RCLike.norm_conj]
    rw [mul_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hr), inv_pow, Real.sq_sqrt hr.le]
    ring
  have hs := hv.inner_products_summable (x := v)
  have hb := hv.tsum_inner_products_le (x := v)
  simp_rw [hterm] at hs hb
  rw [zb, tsum_div_const, div_le_iff₀ hr] at hb
  refine ⟨?_, by linarith⟩
  simpa [div_mul_cancel₀ _ hr.ne'] using hs.mul_right (volume.real Q)
lemma a9 {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) : ∫⁻ ξ, ENNReal.ofReal (‖aa Ω ξ‖ ^ 2) ≤ volume Ω := by
  classical
  have hΩfin : volume Ω ≠ ⊤ := hΩb.measure_lt_top.ne
  obtain ⟨r, hr⟩ := hΩb.subset_closedBall 0
  set R : ℝ := |r| + 1 with hR
  have hRpos : 0 < R := by positivity
  set c : ℝ := (2 * R)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcR : c * R = 1 / 2 := by rw [hc]; field_simp
  set T : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal fun _ => c with hTdef
  have za : T.det = c ^ d := by
    simp [hTdef, Matrix.det_diagonal, Finset.prod_const]
  have hT : IsUnit T.det := by rw [za]; exact (pow_pos hcpos d).ne'.isUnit
  have hTt : Tᵀ = T := Matrix.diagonal_transpose _
  have zb : ∀ v, T *ᵥ v = c • v := by
    intro v; ext i; simp [hTdef, Matrix.mulVec_diagonal]
  set b : Fin d → ℝ := fun _ => 1 / 2 with hb
  set Q := affEquiv T hT b ⁻¹' aZ d with hQdef
  have hΩQ : Ω ⊆ Q := by
    intro y hy
    have hyb : ‖y‖ ≤ r := mem_closedBall_zero_iff.mp (hr hy)
    simp only [hQdef, Set.mem_preimage, affEquiv_apply, aZ, Set.mem_univ_pi, Set.mem_Ico, zb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb]
    intro i
    have hyi : |y i| ≤ r := by
      have := norm_le_pi_norm y i
      rw [Real.norm_eq_abs] at this
      linarith
    have hlt : |y i| < R := by linarith [le_abs_self r]
    rw [abs_lt] at hlt
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hlt.1 hcpos]
    · nlinarith [mul_lt_mul_of_pos_left hlt.2 hcpos]
  have zc : volume Q = ENNReal.ofReal (c ^ d)⁻¹ := by
    rw [hQdef, ax, a8, mul_one, za, abs_of_pos (pow_pos hcpos d)]
  have hQfin : volume Q ≠ ⊤ := by rw [zc]; exact ENNReal.ofReal_ne_top
  have hQpos : 0 < volume Q := by
    rw [zc]; exact ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hcpos d))
  have zd : volume.real Q = (c ^ d)⁻¹ := by
    rw [measureReal_def, zc, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos hcpos d).le)]
  set bs := (Pi.basisFun ℝ (Fin d)).isUnitSMul (w := fun _ => c) (fun _ => hcpos.ne'.isUnit)
    with hbs
  have ze : ∀ i, bs i = c • Pi.single i (1 : ℝ) := by
    intro i; simp [hbs, Module.Basis.isUnitSMul_apply]
  set L := Submodule.span ℤ (Set.range bs) with hLdef
  have hL : ∀ v ∈ L, ∃ k : Fin d → ℤ, v = T *ᵥ (fun i => (k i : ℝ)) := by
    intro v hv
    obtain ⟨k, hk⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
    refine ⟨k, ?_⟩
    rw [← hk, zb]
    ext j
    simp [ze, Finset.sum_apply, Pi.single_apply, mul_comm]
  have zf : aI Q (L : Set (Fin d → ℝ)) := by
    have ho := (a7 (d := d)).affEquiv_preimage T hT b
    intro ξ₁ h₁ ξ₂ h₂ hne
    obtain ⟨k₁, rfl⟩ := hL ξ₁ h₁
    obtain ⟨k₂, rfl⟩ := hL ξ₂ h₂
    exact ho _ ⟨_, ⟨k₁, rfl⟩, by rw [hTt]⟩ _ ⟨_, ⟨k₂, rfl⟩, by rw [hTt]⟩ hne
  have hfd := ZSpan.isAddFundamentalDomain bs volume
  have : MeasurableVAdd L (Fin d → ℝ) :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup (Fin d → ℝ))
  have : VAddInvariantMeasure L (Fin d → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin d → ℝ) volume)
  set F : (Fin d → ℝ) → ENNReal := fun ξ => ENNReal.ofReal (‖aa Ω ξ‖ ^ 2) with hFdef
  have hFmeas : Measurable F :=
    (((aG hΩfin).norm.pow 2).measurable).ennreal_ofReal
  have hbound : ∀ x, ∑' g : L, F (g +ᵥ x) ≤
      ENNReal.ofReal (volume.real Q * volume.real Ω) := by
    intro x
    obtain ⟨hsum, hle⟩ := zf.tsum_normSq_ftInd_le_of_subset hΩm hΩQ hQfin hQpos (-x)
    have heq : ∀ g : L, F (g +ᵥ x) = ENNReal.ofReal (‖aa Ω (-x - g)‖ ^ 2) := by
      intro g
      simp only [hFdef, Submodule.vadd_def, vadd_eq_add]
      rw [show -x - (g : Fin d → ℝ) = -((g : Fin d → ℝ) + x) by abel, ai,
        RCLike.norm_conj]
    calc ∑' g : L, F (g +ᵥ x) = ∑' g : L, ENNReal.ofReal (‖aa Ω (-x - g)‖ ^ 2) :=
          tsum_congr heq
      _ = ENNReal.ofReal (∑' γ : (L : Set (Fin d → ℝ)), ‖aa Ω (-x - γ)‖ ^ 2) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hsum).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hle
  have zg : ∀ g : L, AEMeasurable (fun x => F (g +ᵥ x))
      (volume.restrict (ZSpan.fundamentalDomain bs)) := by
    intro g
    exact (hFmeas.comp (measurable_const_add (g : Fin d → ℝ))).aemeasurable
  have zh : (Matrix.of bs).det = c ^ d := by
    have : Matrix.of bs = Matrix.diagonal fun _ => c := by
      ext i j
      simp [ze, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
    rw [this]
    simp [Matrix.det_diagonal, Finset.prod_const]
  calc ∫⁻ ξ, ENNReal.ofReal (‖aa Ω ξ‖ ^ 2)
      = ∑' g : L, ∫⁻ x in ZSpan.fundamentalDomain bs, F (g +ᵥ x) :=
        hfd.lintegral_eq_tsum'' F
    _ = ∫⁻ x in ZSpan.fundamentalDomain bs, ∑' g : L, F (g +ᵥ x) :=
        (lintegral_tsum zg).symm
    _ ≤ ∫⁻ _ in ZSpan.fundamentalDomain bs, ENNReal.ofReal (volume.real Q * volume.real Ω) :=
        lintegral_mono hbound
    _ = volume (ZSpan.fundamentalDomain bs) *
          ENNReal.ofReal (volume.real Q * volume.real Ω) := by
        rw [setLIntegral_const, mul_comm]
    _ = volume Ω := by
        rw [ZSpan.volume_fundamentalDomain, zh, abs_of_pos (pow_pos hcpos d), zd, ← ENNReal.ofReal_mul (pow_pos hcpos d).le, ← mul_assoc, mul_inv_cancel₀ (pow_pos hcpos d).ne', one_mul, measureReal_def, ENNReal.ofReal_toReal hΩfin]
end FCBridge
end
section
open MeasureTheory Filter Complex Real
open scoped ComplexConjugate
namespace FCBridge
variable {d : ℕ}
lemma ba {Λ : Set (Fin d → ℝ)} (hΛ : Λ.Countable) {f g : (Fin d → ℝ) → ENNReal} (hf : Measurable f) (hg : Measurable g) (hF : ∀ᵐ x ∂volume, ∑' l : Λ, f (x - l) = 1) (x : Fin d → ℝ) : ∫⁻ y, g y = ∫⁻ w, f (x - w) * ∑' l : Λ, g (w - l) := by
  have : Countable Λ := hΛ.to_subtype
  calc ∫⁻ y, g y = ∫⁻ y, g (x - y) := (lintegral_sub_left_eq_self g x).symm
    _ = ∫⁻ y, g (x - y) * ∑' l : Λ, f (y - l) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hF] with y hy
        rw [hy, mul_one]
    _ = ∑' l : Λ, ∫⁻ y, g (x - y) * f (y - l) := by
        have hm : ∀ l : Λ, Measurable fun y => g (x - y) * f (y - l) := fun l =>
          (hg.comp (measurable_const_sub x)).mul (hf.comp (measurable_sub_const _))
        rw [← lintegral_tsum fun l => (hm l).aemeasurable]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.tsum_mul_left]
    _ = ∑' l : Λ, ∫⁻ w, f (x - w) * g (w - l) := by
        refine tsum_congr fun l => ?_
        rw [← lintegral_sub_left_eq_self (fun y => g (x - y) * f (y - l)) (x + l)]
        refine lintegral_congr fun w => ?_
        rw [show x - (x + (l : Fin d → ℝ) - w) = w - l by abel,
          show x + (l : Fin d → ℝ) - w - l = x - w by abel, mul_comm]
    _ = ∫⁻ w, f (x - w) * ∑' l : Λ, g (w - l) := by
        have hm : ∀ l : Λ, Measurable fun w => f (x - w) * g (w - l) := fun l =>
          (hf.comp (measurable_const_sub x)).mul (hg.comp (measurable_sub_const _))
        rw [← lintegral_tsum fun l => (hm l).aemeasurable]
        refine lintegral_congr fun w => ?_
        rw [ENNReal.tsum_mul_left]
lemma bb {Λ : Set (Fin d → ℝ)} (hΛ : Λ.Countable) {f g : (Fin d → ℝ) → ENNReal} (hf : Measurable f) (hg : Measurable g) (hF : ∀ᵐ x ∂volume, ∑' l : Λ, f (x - l) = 1) (hG : ∀ᵐ x ∂volume, ∑' l : Λ, g (x - l) ≤ 1) : ∫⁻ y, g y ≤ ∫⁻ y, f y := by
  rw [ba hΛ hf hg hF 0]
  calc ∫⁻ w, f (0 - w) * ∑' l : Λ, g (w - l) ≤ ∫⁻ w, f (0 - w) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hG] with w hw
        calc f (0 - w) * ∑' l : Λ, g (w - l) ≤ f (0 - w) * 1 := by gcongr
          _ = f (0 - w) := mul_one _
    _ = ∫⁻ y, f y := lintegral_sub_left_eq_self f 0
lemma bc {Λ : Set (Fin d → ℝ)} (hΛ : Λ.Countable) {f : (Fin d → ℝ) → ENNReal} (hf : Measurable f) (hF : ∀ᵐ x ∂volume, ∑' l : Λ, f (x - l) = 1) : ∫⁻ y, f y ≠ 0 := by
  have : Countable Λ := hΛ.to_subtype
  intro h0
  have hf0 : f =ᵐ[volume] 0 := (lintegral_eq_zero_iff hf).mp h0
  have za : ∀ l : Λ, ∀ᵐ x ∂volume, f (x - l) = 0 := fun l =>
    (measurePreserving_sub_right volume (l : Fin d → ℝ)).quasiMeasurePreserving.ae hf0
  have hall : ∀ᵐ x ∂volume, ∀ l : Λ, f (x - l) = 0 := ae_all_iff.mpr za
  obtain ⟨x, hx1, hx0⟩ := (hF.and hall).exists
  rw [tsum_congr hx0, tsum_zero] at hx1
  exact zero_ne_one hx1
lemma be {Λ : Set (Fin d → ℝ)} (hΛ : Λ.Countable) {f g : (Fin d → ℝ) → ENNReal} (hf : Measurable f) (hg : Measurable g) (hftop : ∀ x, f x ≠ ⊤) (hF : ∀ᵐ x ∂volume, ∑' l : Λ, f (x - l) = 1) (hG : ∀ᵐ x ∂volume, ∑' l : Λ, g (x - l) ≤ 1) (hfin : ∫⁻ y, f y ≠ ⊤) (hle : ∫⁻ y, f y ≤ ∫⁻ y, g y) : ∀ᵐ x ∂volume, ∑' l : Λ, g (x - l) = 1 := by
  have : Countable Λ := hΛ.to_subtype
  set G : (Fin d → ℝ) → ENNReal := fun w => ∑' l : Λ, g (w - l) with hGdef
  have za : Measurable G :=
    Measurable.tsum fun l => hg.comp (measurable_sub_const _)
  have hgf : ∫⁻ y, g y = ∫⁻ y, f y :=
    le_antisymm (bb hΛ hf hg hF hG) hle
  have hkey : ∀ x, ∀ᵐ w ∂volume, f (x - w) * G w = f (x - w) := by
    intro x
    have hle' : (fun w => f (x - w) * G w) ≤ᵐ[volume] fun w => f (x - w) := by
      filter_upwards [hG] with w hw
      calc f (x - w) * G w ≤ f (x - w) * 1 := by gcongr
        _ = f (x - w) := mul_one _
    have zb : ∫⁻ w, f (x - w) = ∫⁻ y, f y := lintegral_sub_left_eq_self f x
    have hint2 : ∫⁻ w, f (x - w) * G w = ∫⁻ y, g y :=
      (ba hΛ hf hg hF x).symm
    exact ae_eq_of_ae_le_of_lintegral_le hle' (by rw [hint2, hgf]; exact hfin)
      (hf.comp (measurable_const_sub x)).aemeasurable (by rw [zb, hint2, hgf])
  set E : Set (Fin d → ℝ) := {w | G w < 1} with hEdef
  have hEm : MeasurableSet E := measurableSet_lt za measurable_const
  have hzero : ∀ x, ∫⁻ w, f (x - w) * E.indicator 1 w = 0 := by
    intro x
    have hm : Measurable fun w => f (x - w) * E.indicator 1 w :=
      (hf.comp (measurable_const_sub x)).mul (measurable_one.indicator hEm)
    refine (lintegral_eq_zero_iff hm).mpr ?_
    filter_upwards [hkey x] with w hw
    show f (x - w) * E.indicator 1 w = 0
    by_cases hwE : w ∈ E
    · rw [Set.indicator_of_mem hwE, Pi.one_apply, mul_one]
      by_contra hne
      have hlt : G w * f (x - w) < 1 * f (x - w) := ENNReal.mul_lt_mul_left hne (hftop _) hwE
      rw [one_mul, mul_comm, hw] at hlt
      exact lt_irrefl _ hlt
    · simp [Set.indicator_of_notMem hwE]
  have hmeas2 : AEMeasurable (Function.uncurry fun x w => f (x - w) * E.indicator 1 w)
      (volume.prod volume) :=
    ((hf.comp measurable_sub).mul ((measurable_one.indicator hEm).comp measurable_snd)).aemeasurable
  have zc : volume E * ∫⁻ y, f y = 0 := by
    have hswap := lintegral_lintegral_swap hmeas2
    simp only [hzero, lintegral_zero] at hswap
    rw [eq_comm] at hswap
    calc volume E * ∫⁻ y, f y = ∫⁻ w, E.indicator 1 w * ∫⁻ y, f y := by
          have hm : Measurable fun w => E.indicator (1 : (Fin d → ℝ) → ENNReal) w :=
            measurable_one.indicator hEm
          rw [lintegral_mul_const _ hm, lintegral_indicator_one hEm]
      _ = ∫⁻ w, ∫⁻ x, f (x - w) * E.indicator 1 w := by
          refine lintegral_congr fun w => ?_
          have hm : Measurable fun y => f (y - w) := hf.comp (measurable_sub_const w)
          rw [lintegral_mul_const _ hm, lintegral_sub_right_eq_self f w, mul_comm]
      _ = 0 := hswap
  have zd := bc hΛ hf hF
  have hE0 : volume E = 0 := (mul_eq_zero.mp zc).resolve_right zd
  filter_upwards [hG, measure_eq_zero_iff_ae_notMem.mp hE0] with w hw hwE
  exact le_antisymm hw (not_lt.mp hwE)
section FNorm
variable {k : ℕ}
noncomputable def bf (S : Set (Fin k → ℝ)) (ξ : Fin k → ℝ) : ENNReal :=
  ENNReal.ofReal (‖aa S ξ‖ ^ 2 / volume.real S ^ 2)
lemma bg {S : Set (Fin k → ℝ)} (hS : volume S ≠ ⊤) : Measurable (bf S) :=
  ((((aG hS).norm.pow 2).div_const _).measurable).ennreal_ofReal
lemma bh (S : Set (Fin k → ℝ)) (ξ : Fin k → ℝ) : bf S ξ ≠ ⊤ :=
  ENNReal.ofReal_ne_top
lemma bi {S Λ : Set (Fin k → ℝ)} (h : spectralPair S Λ) (z : Fin k → ℝ) : ∑' l : Λ, bf S (z - l) = 1 := by
  have hh := h
  obtain ⟨-, hpos, hS, -⟩ := hh
  have hr : 0 < volume.real S := ENNReal.toReal_pos hpos.ne' hS
  have hs := (aR h z).div_const (volume.real S ^ 2)
  rw [div_self (pow_pos hr 2).ne'] at hs
  unfold bf
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs.summable, hs.tsum_eq,
    ENNReal.ofReal_one]
lemma bj {S Γ : Set (Fin k → ℝ)} (hS : volume S ≠ ⊤) (hpos : 0 < volume S) (horth : aI S Γ) (z : Fin k → ℝ) : ∑' v : Γ, bf S (z - v) ≤ 1 := by
  have hr : 0 < volume.real S := ENNReal.toReal_pos hpos.ne' hS
  obtain ⟨hsum, hle⟩ := horth.summable_tsum_le hS hpos z
  unfold bf
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hsum.div_const _),
    tsum_div_const, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal ((div_le_one (pow_pos hr 2)).mpr hle)
lemma bk {S Γ : Set (Fin k → ℝ)} (hmeas : NullMeasurableSet S volume) (hS : volume S ≠ ⊤) (hpos : 0 < volume S) (horth : aI S Γ) (htile : ∀ᵐ z ∂volume, ∑' v : Γ, bf S (z - v) = 1) : spectralPair S Γ := by
  have hr : 0 < volume.real S := ENNReal.toReal_pos hpos.ne' hS
  have hc : volume.real S ^ 2 ≠ 0 := (pow_pos hr 2).ne'
  refine aY hmeas hS hpos horth ?_
  filter_upwards [htile] with z hz
  obtain ⟨hsum, -⟩ := horth.summable_tsum_le hS hpos z
  unfold bf at hz
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (hsum.div_const _),
    tsum_div_const, ENNReal.ofReal_eq_one, div_eq_one_iff_eq hc] at hz
  exact hz
lemma bl {S : Set (Fin k → ℝ)} (hSm : MeasurableSet S) (hSb : Bornology.IsBounded S) (hpos : 0 < volume S) : ∫⁻ ξ, bf S ξ ≤ (volume S)⁻¹ := by
  have hS : volume S ≠ ⊤ := hSb.measure_lt_top.ne
  have hr : 0 < volume.real S := ENNReal.toReal_pos hpos.ne' hS
  have hpt : ∀ ξ, bf S ξ = ENNReal.ofReal (‖aa S ξ‖ ^ 2) *
      ENNReal.ofReal ((volume.real S ^ 2)⁻¹) := by
    intro ξ
    unfold bf
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (sq_nonneg _)]
  simp_rw [hpt]
  have hm : Measurable fun ξ => ENNReal.ofReal (‖aa S ξ‖ ^ 2) :=
    ((aG hS).norm.pow 2).measurable.ennreal_ofReal
  rw [lintegral_mul_const _ hm]
  have hvol : volume S = ENNReal.ofReal (volume.real S) := (ENNReal.ofReal_toReal hS).symm
  calc (∫⁻ ξ, ENNReal.ofReal (‖aa S ξ‖ ^ 2)) * ENNReal.ofReal ((volume.real S ^ 2)⁻¹)
      ≤ volume S * ENNReal.ofReal ((volume.real S ^ 2)⁻¹) := by
        gcongr
        exact a9 hSm hSb
    _ = (volume S)⁻¹ := by
        have hr0 : volume.real S ≠ 0 := hr.ne'
        rw [hvol, ← ENNReal.ofReal_mul hr.le, ← ENNReal.ofReal_inv_of_pos hr]
        congr 1
        field_simp
end FNorm
section Product
variable {n m : ℕ}
def proj₁ (z : Fin (n + m) → ℝ) : Fin n → ℝ := fun i => z (Fin.castAdd m i)
def proj₂ (z : Fin (n + m) → ℝ) : Fin m → ℝ := fun j => z (Fin.natAdd n j)
theorem proj₁_sub (z w : Fin (n + m) → ℝ) : proj₁ (z - w) = proj₁ z - proj₁ w := rfl
theorem proj₂_sub (z w : Fin (n + m) → ℝ) : proj₂ (z - w) = proj₂ z - proj₂ w := rfl
theorem proj₁_append (x : Fin n → ℝ) (y : Fin m → ℝ) : proj₁ (Fin.append x y) = x := by
  funext i; simp [proj₁]
theorem proj₂_append (x : Fin n → ℝ) (y : Fin m → ℝ) : proj₂ (Fin.append x y) = y := by
  funext j; simp [proj₂]
theorem measurable_proj₁ : Measurable (proj₁ : (Fin (n + m) → ℝ) → Fin n → ℝ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
theorem measurable_proj₂ : Measurable (proj₂ : (Fin (n + m) → ℝ) → Fin m → ℝ) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _
lemma splitEquiv_apply' (z : Fin (n + m) → ℝ) : am n m z = (proj₁ z, proj₂ z) :=
  splitEquiv_apply z
lemma bn (x : Fin n → ℝ) (y : Fin m → ℝ) : (am n m).symm (x, y) = Fin.append x y := by
  apply (am n m).injective
  rw [MeasurableEquiv.apply_symm_apply, splitEquiv_apply', proj₁_append, proj₂_append]
lemma bo (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) (z : Fin (n + m) → ℝ) : bf (productSet A B) z = bf A (proj₁ z) * bf B (proj₂ z) := by
  have hz : z = Fin.append (proj₁ z) (proj₂ z) := Fin.append_castAdd_natAdd.symm
  unfold bf
  rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  congr 1
  have hvol : volume.real (productSet A B) = volume.real A * volume.real B := by
    rw [measureReal_def, ap, ENNReal.toReal_mul]
    rfl
  conv_lhs => rw [hz]
  rw [as, hvol, norm_mul, mul_pow, mul_pow, mul_div_mul_comm]
lemma bp {F : (Fin n → ℝ) → ENNReal} {G : (Fin m → ℝ) → ENNReal} (hF : Measurable F) (hG : Measurable G) : ∫⁻ z, F (proj₁ z) * G (proj₂ z) = (∫⁻ x, F x) * ∫⁻ y, G y := by
  have key := (an n m).lintegral_comp_emb
    (am n m).measurableEmbedding (fun p => F p.1 * G p.2)
  simp only [splitEquiv_apply'] at key
  rw [key, Measure.volume_eq_prod]
  exact lintegral_prod_mul hF.aemeasurable hG.aemeasurable
theorem ae_proj₁_notMem {N : Set (Fin n → ℝ)} (hN : volume N = 0) : ∀ᵐ z ∂(volume : Measure (Fin (n + m) → ℝ)), proj₁ z ∉ N := by
  rw [ae_iff]
  simp only [not_not]
  refine measure_mono_null (t := am n m ⁻¹' (N ×ˢ Set.univ)) ?_ ?_
  · intro z hz
    have hz' : proj₁ z ∈ N := hz
    simp [splitEquiv_apply', hz']
  · rw [(an n m).measure_preimage_equiv, Measure.volume_eq_prod,
      Measure.prod_prod, hN, zero_mul]
lemma ae_ae_of_ae_append {P : (Fin (n + m) → ℝ) → Prop} (h : ∀ᵐ z ∂volume, P z) : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), P (Fin.append x y) := by
  have h1 : ∀ᵐ p ∂(volume : Measure ((Fin n → ℝ) × (Fin m → ℝ))),
      P ((am n m).symm p) :=
    ((an n m).symm _).quasiMeasurePreserving.ae h
  rw [Measure.volume_eq_prod] at h1
  filter_upwards [Measure.ae_ae_of_ae_prod h1] with x hx
  filter_upwards [hx] with y hy
  rwa [bn] at hy
end Product
lemma bq {n m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)} (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A) (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B) {Λ : Set (Fin (n + m) → ℝ)} (hΛ : spectralPair (productSet A B) Λ) {W : Set (Fin n → ℝ)} (hWm : MeasurableSet W) (hWvol : (volume A)⁻¹ ≤ volume W) (hcompat : ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → volume {x | proj₁ l - x ∈ W ∧ proj₁ l' - x ∈ W} = 0 ∨ aa B (proj₂ l' - proj₂ l) = 0) : isSpectral B := by
  classical
  have hΛ' := hΛ
  obtain ⟨-, hΩpos, hΩfin, -⟩ := hΛ'
  obtain ⟨hApos, hBpos⟩ := aq ⟨Λ, hΛ⟩
  have hAfin : volume A ≠ ⊤ := hAb.measure_lt_top.ne
  have hBfin : volume B ≠ ⊤ := hBb.measure_lt_top.ne
  have hBr : 0 < volume.real B := ENNReal.toReal_pos hBpos.ne' hBfin
  have horthΩ : aI (productSet A B) Λ := by
    obtain ⟨-, -, -, horth, -⟩ := al.mp hΛ
    exact horth
  have hΛc : Λ.Countable := horthΩ.countable hΩfin hΩpos
  have : Countable Λ := hΛc.to_subtype
  let bad : Λ → Λ → Set (Fin n → ℝ) := fun l l' =>
    if (l : Fin (n + m) → ℝ) ≠ l' ∧
        aa B (proj₂ (l' : Fin (n + m) → ℝ) - proj₂ (l : Fin (n + m) → ℝ)) ≠ 0 then
      {x | proj₁ (l : Fin (n + m) → ℝ) - x ∈ W ∧ proj₁ (l' : Fin (n + m) → ℝ) - x ∈ W}
    else ∅
  set N := ⋃ l : Λ, ⋃ l' : Λ, bad l l' with hNdef
  have hN : volume N = 0 := by
    refine measure_iUnion_null fun l => measure_iUnion_null fun l' => ?_
    simp only [bad]
    split_ifs with h
    · rcases hcompat l l.2 l' l'.2 h.1 with h0 | h0
      · exact h0
      · exact absurd h0 h.2
    · exact measure_empty
  have hgood : ∀ x ∉ N, ∀ l l' : Λ, (l : Fin (n + m) → ℝ) ≠ l' →
      proj₁ (l : Fin (n + m) → ℝ) - x ∈ W → proj₁ (l' : Fin (n + m) → ℝ) - x ∈ W →
      aa B (proj₂ (l' : Fin (n + m) → ℝ) - proj₂ (l : Fin (n + m) → ℝ)) = 0 := by
    intro x hx l l' hne h1 h2
    by_contra hne0
    apply hx
    refine Set.mem_iUnion.mpr ⟨l, Set.mem_iUnion.mpr ⟨l', ?_⟩⟩
    simp only [bad]
    rw [if_pos ⟨hne, hne0⟩]
    exact ⟨h1, h2⟩
  let S : (Fin n → ℝ) → Set Λ := fun x => {l | proj₁ (l : Fin (n + m) → ℝ) - x ∈ W}
  let prj : (x : Fin n → ℝ) → S x → Fin m → ℝ := fun x s =>
    proj₂ ((s : Λ) : Fin (n + m) → ℝ)
  have za : ∀ x ∉ N, Function.Injective (prj x) := by
    intro x hx s₁ s₂ h
    by_contra hne
    have hne' : ((s₁ : Λ) : Fin (n + m) → ℝ) ≠ s₂ := fun e =>
      hne (Subtype.ext (Subtype.ext e))
    have h0 := hgood x hx s₁ s₂ hne' s₁.2 s₂.2
    have h' : proj₂ ((s₂ : Λ) : Fin (n + m) → ℝ) = proj₂ ((s₁ : Λ) : Fin (n + m) → ℝ) := h.symm
    rw [h', sub_self, aj] at h0
    exact hBr.ne' (by exact_mod_cast h0)
  let Γ : (Fin n → ℝ) → Set (Fin m → ℝ) := fun x => Set.range (prj x)
  have hΓorth : ∀ x ∉ N, aI B (Γ x) := by
    rintro x hx _ ⟨s₁, rfl⟩ _ ⟨s₂, rfl⟩ hne
    have hne' : ((s₁ : Λ) : Fin (n + m) → ℝ) ≠ s₂ := fun e => hne (by simp [prj, e])
    exact hgood x hx s₁ s₂ hne' s₁.2 s₂.2
  set fB := bf B with hfB
  have hsum : ∀ x ∉ N, ∀ y : Fin m → ℝ,
      ∑' l : Λ, W.indicator (1 : (Fin n → ℝ) → ENNReal) (proj₁ (l : Fin (n + m) → ℝ) - x) *
        fB (y - proj₂ (l : Fin (n + m) → ℝ)) = ∑' v : Γ x, fB (y - v) := by
    intro x hx y
    have h1 : ∀ l : Λ, W.indicator (1 : (Fin n → ℝ) → ENNReal)
        (proj₁ (l : Fin (n + m) → ℝ) - x) * fB (y - proj₂ (l : Fin (n + m) → ℝ)) =
          (S x).indicator (fun l : Λ => fB (y - proj₂ (l : Fin (n + m) → ℝ))) l := by
      intro l
      by_cases hl : proj₁ (l : Fin (n + m) → ℝ) - x ∈ W
      · rw [Set.indicator_of_mem hl, Set.indicator_of_mem (show l ∈ S x from hl),
          Pi.one_apply, one_mul]
      · rw [Set.indicator_of_notMem hl, Set.indicator_of_notMem (show l ∉ S x from hl),
          zero_mul]
    simp_rw [h1]
    rw [← tsum_subtype (S x) (fun l : Λ => fB (y - proj₂ (l : Fin (n + m) → ℝ)))]
    exact (Equiv.ofInjective _ (za x hx)).tsum_eq
      (fun v : Set.range (prj x) => fB (y - (v : Fin m → ℝ)))
  set g : (Fin (n + m) → ℝ) → ENNReal := fun z =>
    W.indicator (1 : (Fin n → ℝ) → ENNReal) (-proj₁ z) * fB (proj₂ z) with hgdef
  have zb : Measurable g :=
    ((measurable_one.indicator hWm).comp measurable_proj₁.neg).mul
      ((bg hBfin).comp measurable_proj₂)
  have zc : ∀ (z : Fin (n + m) → ℝ) (l : Λ), g (z - l) =
      W.indicator (1 : (Fin n → ℝ) → ENNReal) (proj₁ (l : Fin (n + m) → ℝ) - proj₁ z) *
        fB (proj₂ z - proj₂ (l : Fin (n + m) → ℝ)) := by
    intro z l
    simp only [hgdef, proj₁_sub, proj₂_sub, neg_sub]
  have zd : ∀ᵐ z ∂volume, ∑' l : Λ, g (z - l) ≤ 1 := by
    filter_upwards [ae_proj₁_notMem (m := m) hN] with z hz
    simp_rw [zc]
    rw [hsum (proj₁ z) hz (proj₂ z)]
    exact bj hBfin hBpos (hΓorth _ hz) _
  have htile : ∀ᵐ z ∂volume, ∑' l : Λ, bf (productSet A B) (z - l) = 1 :=
    Eventually.of_forall (bi hΛ)
  have hIg : ∫⁻ z, g z = volume W * ∫⁻ y, fB y := by
    have hF : Measurable fun x : Fin n → ℝ => W.indicator (1 : (Fin n → ℝ) → ENNReal) (-x) :=
      (measurable_one.indicator hWm).comp measurable_neg
    have key := bp hF (bg hBfin)
    rw [lintegral_neg_eq_self (W.indicator (1 : (Fin n → ℝ) → ENNReal)), lintegral_indicator_one hWm] at key
    exact key
  have hIf : ∫⁻ z, bf (productSet A B) z = (∫⁻ x, bf A x) * ∫⁻ y, fB y := by
    simp_rw [bo]
    exact bp (bg hAfin) (bg hBfin)
  have hfA := bl hAm hAb hApos
  have ze := bl hBm hBb hBpos
  have hle : ∫⁻ z, bf (productSet A B) z ≤ ∫⁻ z, g z := by
    rw [hIf, hIg]
    gcongr
    exact hfA.trans hWvol
  have hfin : ∫⁻ z, bf (productSet A B) z ≠ ⊤ := by
    rw [hIf]
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr hApos.ne') hfA)
      (ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr hBpos.ne') ze)
  have zf : ∀ᵐ z ∂volume, ∑' l : Λ, g (z - l) = 1 :=
    be hΛc (bg hΩfin) zb
      (bh _) htile zd hfin hle
  have hae := ae_ae_of_ae_append zf
  obtain ⟨x, hx, hxN⟩ := (hae.and (measure_eq_zero_iff_ae_notMem.mp hN)).exists
  refine ⟨Γ x, bk hBm.nullMeasurableSet hBfin hBpos
    (hΓorth x hxN) ?_⟩
  filter_upwards [hx] with y hy
  simp_rw [zc, proj₁_append, proj₂_append] at hy
  rw [hsum x hxN y] at hy
  exact hy
end FCBridge
end
section
namespace GraphicVoronoiPrototype
lemma br (k : ℤ) : |(k : ℝ)| ≤ (k : ℝ) ^ 2 := by
  by_cases hk : k = 0
  · simp [hk]
  · have za : (1 : ℤ) ≤ |k| := by
      rcases lt_trichotomy k 0 with hneg | hzero | hpos
      · rw [abs_of_neg hneg]
        omega
      · exact (hk hzero).elim
      · rw [abs_of_pos hpos]
        omega
    have zb : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast za
    have zc : |(k : ℝ)| ^ 2 = (k : ℝ) ^ 2 := by
      rw [sq_abs]
    rw [← zc]
    nlinarith [sq_nonneg (|(k : ℝ)| - 1)]
lemma bt {a x : ℝ} (ha : |a| ≤ 1 / 2) : 2 * a * x ≤ |x| := by
  have ha' : 0 ≤ 1 - 2 * |a| := by linarith
  have hprod : 0 ≤ (1 - 2 * |a|) * |x| := mul_nonneg ha' (abs_nonneg x)
  have habs : |2 * a * x| = 2 * |a| * |x| := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (le_abs_self _).trans (by rw [habs]; nlinarith)
lemma bu {E : Type*} [Fintype E] (c a : E → ℝ) (k : E → ℤ) (hc : ∀ e, 0 ≤ c e) (ha : ∀ e, |a e| ≤ 1 / 2) : 2 * ∑ e, c e * a e * (k e : ℝ) ≤ ∑ e, c e * (k e : ℝ) ^ 2 := by
  calc
    2 * ∑ e, c e * a e * (k e : ℝ) =
        ∑ e, c e * (2 * a e * (k e : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e he
          ring
    _ ≤ ∑ e, c e * |(k e : ℝ)| := by
          apply Finset.sum_le_sum
          intro e he
          exact mul_le_mul_of_nonneg_left (bt (ha e)) (hc e)
    _ ≤ ∑ e, c e * (k e : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro e he
          exact mul_le_mul_of_nonneg_left (br (k e)) (hc e)
def cutBit {V : Type*} [DecidableEq V] (S : Finset V) (v : V) : ℤ :=
  if v ∈ S then 1 else 0
def crosses {V : Type*} [DecidableEq V] (S : Finset V) (u v : V) : Prop :=
  (u ∈ S) ≠ (v ∈ S)
noncomputable def cutCapacity {V E : Type*} [DecidableEq V] [Fintype E] (S : Finset V) (src dst : E → V) (c : E → ℝ) : ℝ := by
  classical
  exact ∑ e, if crosses S (src e) (dst e) then c e else 0
lemma bv {V E : Type*} [DecidableEq V] [Fintype E] (S : Finset V) (src dst : E → V) (c : E → ℝ) : (∑ e, c e * ((cutBit S (src e) : ℝ) - (cutBit S (dst e) : ℝ)) ^ 2) = cutCapacity S src dst c := by
  classical
  rw [cutCapacity]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hu : src e ∈ S <;> by_cases hv : dst e ∈ S <;>
    simp [cutBit, crosses, hu, hv]
lemma bw {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (src dst : E → V) (c : E → ℝ) (y : V → ℝ) (hy : ∑ v, y v = 0) (φ : V → ℝ) (hφ : ∀ v w, φ v = φ w) : 2 * ∑ v, y v * φ v ≤ ∑ e, c e * |φ (src e) - φ (dst e)| := by
  rcases isEmpty_or_nonempty V with hV | ⟨⟨v₀⟩⟩
  · have : IsEmpty E := ⟨fun e => hV.false (src e)⟩
    simp
  · have hl : ∑ v, y v * φ v = 0 := by
      simp_rw [hφ _ v₀, ← Finset.sum_mul, hy, zero_mul]
    have hr : ∑ e, c e * |φ (src e) - φ (dst e)| = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      rw [hφ (src e) (dst e), sub_self, abs_zero, mul_zero]
    rw [hl, hr, mul_zero]
lemma bx {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] (src dst : E → V) (c : E → ℝ) (y : V → ℝ) (hy : ∑ v, y v = 0) (hcut : ∀ S : Finset V, 2 * ∑ v, y v * (cutBit S v : ℝ) ≤ cutCapacity S src dst c) (φ : V → ℝ) : 2 * ∑ v, y v * φ v ≤ ∑ e, c e * |φ (src e) - φ (dst e)| := by
  classical
  suffices h : ∀ n : ℕ, ∀ φ : V → ℝ, (Finset.univ.image φ).card ≤ n →
      2 * ∑ v, y v * φ v ≤ ∑ e, c e * |φ (src e) - φ (dst e)| from
    h _ φ le_rfl
  intro n
  induction n with
  | zero =>
    intro φ hφ
    apply bw src dst c y hy φ
    intro v w
    have h0 : Finset.univ.image φ = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hφ)
    have : φ v ∈ Finset.univ.image φ := Finset.mem_image_of_mem φ (Finset.mem_univ v)
    simp [h0] at this
  | succ n ih =>
    intro φ hφ
    by_cases hone : (Finset.univ.image φ).card ≤ 1
    · apply bw src dst c y hy φ
      intro v w
      exact Finset.card_le_one.mp hone _ (Finset.mem_image_of_mem φ (Finset.mem_univ v))
        _ (Finset.mem_image_of_mem φ (Finset.mem_univ w))
    rw [not_le] at hone
    have hne : (Finset.univ.image φ).Nonempty := Finset.card_pos.mp (by omega)
    set m := (Finset.univ.image φ).min' hne with hm
    have hmin : ∀ v, m ≤ φ v := fun v =>
      Finset.min'_le _ _ (Finset.mem_image_of_mem φ (Finset.mem_univ v))
    set S : Finset V := Finset.univ.filter (fun v => φ v ≠ m) with hS
    have za : (S.image φ).Nonempty := by
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hone
      obtain ⟨va, -, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨vb, -, rfl⟩ := Finset.mem_image.mp hb
      by_cases hva : φ va = m
      · refine ⟨φ vb, Finset.mem_image_of_mem φ ?_⟩
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        intro h; exact hab (hva.trans h.symm)
      · exact ⟨φ va, Finset.mem_image_of_mem φ (by simp [hS, hva])⟩
    set m' := (S.image φ).min' za with hm'
    have hmin' : ∀ v, φ v ≠ m → m' ≤ φ v := fun v hv =>
      Finset.min'_le _ _ (Finset.mem_image_of_mem φ (by simp [hS, hv]))
    have hlt : m < m' := by
      obtain ⟨v₀, hv₀, hv₀eq⟩ := Finset.mem_image.mp ((S.image φ).min'_mem za)
      have hv₀' : φ v₀ ≠ m := by simpa [hS] using hv₀
      rw [← hm'] at hv₀eq
      rw [← hv₀eq]
      exact lt_of_le_of_ne (hmin v₀) (Ne.symm hv₀')
    set δ := m' - m with hδ
    have hδpos : 0 ≤ δ := by linarith
    let φ' : V → ℝ := fun v => if φ v = m then m' else φ v
    have hcard : (Finset.univ.image φ').card ≤ n := by
      have hsub : Finset.univ.image φ' ⊆ (Finset.univ.image φ).erase m := by
        intro t ht
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ht
        rw [Finset.mem_erase]
        by_cases hv : φ v = m
        · simp only [φ', hv, if_true]
          refine ⟨ne_of_gt hlt, ?_⟩
          obtain ⟨v₀, -, hv₀eq⟩ := Finset.mem_image.mp ((S.image φ).min'_mem za)
          rw [← hm'] at hv₀eq
          rw [← hv₀eq]
          exact Finset.mem_image_of_mem φ (Finset.mem_univ v₀)
        · simp only [φ', hv, if_false]
          exact ⟨hv, Finset.mem_image_of_mem φ (Finset.mem_univ v)⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem ((Finset.univ.image φ).min'_mem hne)] at this
      omega
    have hdecomp : ∀ v, φ v = (φ' v - δ) + δ * (cutBit S v : ℝ) := by
      intro v
      by_cases hv : φ v = m
      · simp [φ', cutBit, hS, hv, hδ]
      · simp [φ', cutBit, hS, hv]
    have zb : ∑ v, y v * φ v =
        ∑ v, y v * φ' v + δ * ∑ v, y v * (cutBit S v : ℝ) := by
      simp_rw [hdecomp]
      have : ∀ v, y v * (φ' v - δ + δ * (cutBit S v : ℝ)) =
          y v * φ' v - δ * y v + δ * (y v * (cutBit S v : ℝ)) := fun v => by ring
      simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hy]
      ring
    have hedge : ∀ u w, |φ u - φ w| =
        |φ' u - φ' w| + δ * (if crosses S u w then 1 else 0) := by
      intro u w
      by_cases hu : φ u = m <;> by_cases hw : φ w = m
      · have : ¬ crosses S u w := by simp [crosses, hS, hu, hw]
        simp [φ', hu, hw, this]
      · have : crosses S u w := by simp [crosses, hS, hu, hw]
        simp only [φ', hu, hw, if_true, if_false, this, mul_one]
        have h1 := hmin' w hw
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), hδ]
        ring
      · have : crosses S u w := by simp [crosses, hS, hu, hw]
        simp only [φ', hu, hw, if_true, if_false, this, mul_one]
        have h1 := hmin' u hu
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), hδ]
        ring
      · have : ¬ crosses S u w := by simp [crosses, hS, hu, hw]
        simp [φ', hu, hw, this]
    have zc : ∑ e, c e * |φ (src e) - φ (dst e)| =
        ∑ e, c e * |φ' (src e) - φ' (dst e)| + δ * cutCapacity S src dst c := by
      rw [cutCapacity, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rw [hedge]
      by_cases hx : crosses S (src e) (dst e)
      · rw [if_pos hx, if_pos hx]; ring
      · rw [if_neg hx, if_neg hx]; ring
    rw [zb, zc]
    have h1 := ih φ' hcard
    have h2 := mul_le_mul_of_nonneg_left (hcut S) hδpos
    nlinarith
section VoronoiVolume
open Matrix MeasureTheory Submodule Module Pointwise
variable {n : ℕ}
def zr (z : Fin n → ℤ) : Fin n → ℝ := fun i => (z i : ℝ)
lemma bz : zr (0 : Fin n → ℤ) = 0 := by
  ext i; simp [zr]
lemma bA (z w : Fin n → ℤ) : zr (z + w) = zr z + zr w := by
  ext i; simp [zr]
lemma bB (z w : Fin n → ℤ) : zr (z - w) = zr z - zr w := by
  ext i; simp [zr]
lemma bC (z : Fin n → ℤ) : zr (-z) = -zr z := by
  ext i; simp [zr]
lemma bD {z : Fin n → ℤ} (hz : z ≠ 0) : zr z ≠ 0 := by
  intro h
  apply hz
  ext i
  have := congrFun h i
  simpa [zr] using this
def bE (N : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ z : Fin n → ℤ, 2 * (x ⬝ᵥ zr z) ≤ zr z ⬝ᵥ (N *ᵥ zr z)}
def bF (N : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ z : Fin n → ℤ, z ≠ 0 → 2 * (x ⬝ᵥ zr z) < zr z ⬝ᵥ (N *ᵥ zr z)}
lemma bG (N : Matrix (Fin n) (Fin n) ℝ) : bF N ⊆ bE N := by
  intro x hx z
  by_cases hz : z = 0
  · subst hz; simp [bz]
  · exact (hx z hz).le
lemma bH {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) : Nᵀ = N := by
  have h := hpd.isHermitian
  rwa [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
lemma bI {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) {y : Fin n → ℝ} (hy : y ≠ 0) : 0 < y ⬝ᵥ (N *ᵥ y) := by
  simpa [star_trivial] using hpd.dotProduct_mulVec_pos hy
lemma bJ {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) : IsUnit N.det :=
  (Matrix.isUnit_iff_isUnit_det N).mp hpd.isUnit
lemma bK {N : Matrix (Fin n) (Fin n) ℝ} (hN : Nᵀ = N) (a b : Fin n → ℝ) : a ⬝ᵥ (N *ᵥ b) = b ⬝ᵥ (N *ᵥ a) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hN, dotProduct_comm]
lemma bL {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) : ∃ l > 0, ∀ y : Fin n → ℝ, l * ‖y‖ ^ 2 ≤ y ⬝ᵥ (N *ᵥ y) := by
  rcases isEmpty_or_nonempty (Fin n) with hE | hE
  · refine ⟨1, one_pos, fun y => ?_⟩
    have : y = 0 := Subsingleton.elim _ _
    subst this
    simp
  · have hcont : Continuous fun y : Fin n → ℝ => y ⬝ᵥ (N *ᵥ y) := by
      fun_prop
    have hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty := by
      refine ⟨fun _ => 1, ?_⟩
      simp
    obtain ⟨u, hu, hmin⟩ :=
      (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hne hcont.continuousOn
    have hu1 : ‖u‖ = 1 := by simpa using hu
    have hu0 : u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hu1
      exact zero_ne_one hu1
    refine ⟨u ⬝ᵥ (N *ᵥ u), bI hpd hu0, fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      simp
    · have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hmem : ‖y‖⁻¹ • y ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyn.ne']
      have h1 := isMinOn_iff.mp hmin _ hmem
      have h2 : (‖y‖⁻¹ • y) ⬝ᵥ (N *ᵥ (‖y‖⁻¹ • y)) = ‖y‖⁻¹ ^ 2 * (y ⬝ᵥ (N *ᵥ y)) := by
        rw [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        ring
      rw [h2] at h1
      have h3 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖y‖)
      calc u ⬝ᵥ (N *ᵥ u) * ‖y‖ ^ 2 ≤ ‖y‖⁻¹ ^ 2 * (y ⬝ᵥ (N *ᵥ y)) * ‖y‖ ^ 2 := h3
        _ = y ⬝ᵥ (N *ᵥ y) := by field_simp
lemma bM (x y : Fin n → ℝ) : |x ⬝ᵥ y| ≤ n * (‖x‖ * ‖y‖) := by
  calc |x ⬝ᵥ y| = |∑ i, x i * y i| := rfl
    _ ≤ ∑ i, |x i * y i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖x‖ * ‖y‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        have hx : |x i| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
        have hy : |y i| ≤ ‖y‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm y i
        exact mul_le_mul hx hy (abs_nonneg _) (norm_nonneg _)
    _ = n * (‖x‖ * ‖y‖) := by simp
lemma bN {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) (x : Fin n → ℝ) : ∃ z : Fin n → ℤ, x - N *ᵥ zr z ∈ bE N := by
  obtain ⟨l, hl, hcoer⟩ := bL hpd
  have hN := bH hpd
  let g : (Fin n → ℤ) → ℝ := fun z => zr z ⬝ᵥ (N *ᵥ zr z) - 2 * (x ⬝ᵥ zr z)
  let R : ℕ := ⌈2 * n * ‖x‖ / l⌉₊
  let F : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R
  have h0F : (0 : Fin n → ℤ) ∈ F := by
    simp [F]
  obtain ⟨z₀, -, hz₀⟩ := F.exists_min_image g ⟨0, h0F⟩
  have hg0 : g 0 = 0 := by
    simp [g, bz]
  have za : ∀ z, g z₀ ≤ g z := by
    intro z
    by_cases hz : z ∈ F
    · exact hz₀ z hz
    · have hle : g z₀ ≤ 0 := hg0 ▸ hz₀ 0 h0F
      simp only [F, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      have hzi : (R : ℤ) < |z i| := by
        rcases le_or_gt 0 (z i) with h | h
        · rw [abs_of_nonneg h]; omega
        · rw [abs_of_neg h]; omega
      have hbig : (R : ℝ) < ‖zr z‖ := by
        have h1 : ((R : ℤ) : ℝ) < |(z i : ℝ)| := by exact_mod_cast hzi
        calc (R : ℝ) = ((R : ℤ) : ℝ) := by norm_cast
          _ < |(z i : ℝ)| := h1
          _ = ‖zr z i‖ := by simp [zr, Real.norm_eq_abs]
          _ ≤ ‖zr z‖ := norm_le_pi_norm _ i
      have hR : 2 * n * ‖x‖ / l ≤ R := Nat.le_ceil _
      have htpos : 0 < ‖zr z‖ := lt_of_le_of_lt (Nat.cast_nonneg R) hbig
      have hlt : 2 * n * ‖x‖ < l * ‖zr z‖ := by
        have := lt_of_le_of_lt hR hbig
        rw [div_lt_iff₀ hl] at this
        linarith [mul_comm l ‖zr z‖]
      have hq := hcoer (zr z)
      have hd : x ⬝ᵥ zr z ≤ n * (‖x‖ * ‖zr z‖) := (le_abs_self _).trans (bM x (zr z))
      have h3 := mul_lt_mul_of_pos_left hlt htpos
      have : 0 < g z := by
        simp only [g]
        nlinarith
      linarith
  refine ⟨z₀, fun z => ?_⟩
  have key := za (z₀ + z)
  simp only [g, bA, mulVec_add, add_dotProduct, dotProduct_add] at key
  have hs := bK hN (zr z₀) (zr z)
  have hc : (N *ᵥ zr z₀) ⬝ᵥ zr z = zr z ⬝ᵥ (N *ᵥ zr z₀) := dotProduct_comm _ _
  rw [sub_dotProduct, hc]
  linarith
def bO (w : Fin n → ℝ) (c : ℝ) : AffineSubspace ℝ (Fin n → ℝ) where
  carrier := {x | x ⬝ᵥ w = c}
  smul_vsub_vadd_mem' := by
    intro t p₁ p₂ p₃ h₁ h₂ h₃
    change (t • (p₁ - p₂) + p₃) ⬝ᵥ w = c
    change p₁ ⬝ᵥ w = c at h₁
    change p₂ ⬝ᵥ w = c at h₂
    change p₃ ⬝ᵥ w = c at h₃
    rw [add_dotProduct, smul_dotProduct, sub_dotProduct, h₁, h₂, h₃]
    simp
lemma bP {w : Fin n → ℝ} (hw : w ≠ 0) (c : ℝ) : volume {x : Fin n → ℝ | x ⬝ᵥ w = c} = 0 := by
  have hww : w ⬝ᵥ w ≠ 0 := fun h => hw (dotProduct_self_eq_zero.mp h)
  have hne : bO w c ≠ ⊤ := by
    intro h
    have hmem : ((c + 1) / (w ⬝ᵥ w)) • w ∈ bO w c := by
      rw [h]; exact AffineSubspace.mem_top _ _ _
    change (((c + 1) / (w ⬝ᵥ w)) • w) ⬝ᵥ w = c at hmem
    rw [smul_dotProduct, smul_eq_mul, div_mul_cancel₀ _ hww] at hmem
    linarith
  exact Measure.addHaar_affineSubspace volume (bO w c) hne
noncomputable def bQ (N : Matrix (Fin n) (Fin n) ℝ) (hN : IsUnit N.det) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  (Pi.basisFun ℝ (Fin n)).map (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin n)) N hN)
lemma bR (N : Matrix (Fin n) (Fin n) ℝ) (hN : IsUnit N.det) (i : Fin n) : bQ N hN i = N *ᵥ Pi.single i 1 := by
  simp [bQ, Matrix.toLin_eq_toLin']
lemma bS (N : Matrix (Fin n) (Fin n) ℝ) (hN : IsUnit N.det) (v : Fin n → ℝ) : v ∈ span ℤ (Set.range (bQ N hN)) ↔ ∃ z : Fin n → ℤ, N *ᵥ zr z = v := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun z => ?_
  have : ∑ i, z i • bQ N hN i = N *ᵥ zr z := by
    ext k
    simp [bR, mulVec, dotProduct, zr, Finset.sum_apply, mul_comm]
  rw [this]
lemma bT (N : Matrix (Fin n) (Fin n) ℝ) : IsClosed (bE N) := by
  have : bE N = ⋂ z : Fin n → ℤ, {x | 2 * (x ⬝ᵥ zr z) ≤ zr z ⬝ᵥ (N *ᵥ zr z)} := by
    ext x; simp [bE]
  rw [this]
  exact isClosed_iInter fun z => isClosed_le (by fun_prop) continuous_const
lemma bU {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) : IsAddFundamentalDomain (span ℤ (Set.range (bQ N (bJ hpd)))) (bE N) volume := by
  set hN := bJ hpd
  refine ⟨(bT N).measurableSet.nullMeasurableSet, ?_, ?_⟩
  · refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨z, hz⟩ := bN hpd x
    refine ⟨⟨-(N *ᵥ zr z), neg_mem ((bS N hN _).mpr ⟨z, rfl⟩)⟩, ?_⟩
    rw [Submodule.vadd_def, vadd_eq_add]
    simpa [sub_eq_neg_add] using hz
  · intro g₁ g₂ hne
    obtain ⟨z₁, hz₁⟩ := (bS N hN g₁).mp g₁.2
    obtain ⟨z₂, hz₂⟩ := (bS N hN g₂).mp g₂.2
    have hz : z₂ - z₁ ≠ 0 := by
      intro h
      apply hne
      ext1
      rw [← hz₁, ← hz₂, sub_eq_zero.mp h]
    set b := zr (z₂ - z₁) with hb_def
    have hb : b ≠ 0 := bD hz
    show volume ((g₁ +ᵥ bE N) ∩ (g₂ +ᵥ bE N)) = 0
    refine measure_mono_null ?_
      (bP hb ((b ⬝ᵥ (N *ᵥ b) + 2 * ((N *ᵥ zr z₁) ⬝ᵥ b)) / 2))
    rintro x ⟨hx₁, hx₂⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg, ← hz₁] at hx₁
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg, ← hz₂] at hx₂
    have h1 := hx₁ (z₂ - z₁)
    have h2 := hx₂ (z₁ - z₂)
    have e1 : zr (z₁ - z₂) = -b := by
      rw [hb_def, bB, bB]; abel
    have e2 : zr z₂ = zr z₁ + b := by
      rw [hb_def, bB]; abel
    rw [e1, e2] at h2
    rw [← hb_def] at h1
    simp only [mulVec_neg, mulVec_add, neg_dotProduct, dotProduct_neg, add_dotProduct, neg_add_rev, neg_neg] at h1 h2
    have hs : (N *ᵥ b) ⬝ᵥ b = b ⬝ᵥ (N *ᵥ b) := dotProduct_comm _ _
    show x ⬝ᵥ b = _
    linarith
lemma bV {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) : volume (bE N) = ENNReal.ofReal |N.det| := by
  set hN := bJ hpd
  set L := span ℤ (Set.range (bQ N hN))
  have : MeasurableVAdd L (Fin n → ℝ) :=
    (inferInstance : MeasurableVAdd L.toAddSubgroup (Fin n → ℝ))
  have : VAddInvariantMeasure L (Fin n → ℝ) volume :=
    (inferInstance : VAddInvariantMeasure L.toAddSubgroup (Fin n → ℝ) volume)
  rw [(bU hpd).measure_eq (ZSpan.isAddFundamentalDomain (bQ N hN) volume), ZSpan.volume_fundamentalDomain]
  have : Matrix.of (bQ N hN) = Nᵀ := by
    ext i j
    simp [bR, Matrix.of_apply, Matrix.transpose_apply]
  rw [this, det_transpose]
lemma bW {N : Matrix (Fin n) (Fin n) ℝ} : volume (bF N) = volume (bE N) := by
  apply le_antisymm (measure_mono (bG N))
  let H : {z : Fin n → ℤ // z ≠ 0} → Set (Fin n → ℝ) := fun z =>
    {x | x ⬝ᵥ zr z.1 = (zr z.1 ⬝ᵥ (N *ᵥ zr z.1)) / 2}
  have hsub : bE N ⊆ bF N ∪ ⋃ z, H z := by
    intro x hx
    by_cases h : x ∈ bF N
    · exact Or.inl h
    · right
      simp only [bF, Set.mem_ofPred_eq, not_forall, not_lt, exists_prop] at h
      obtain ⟨z, hz, hle⟩ := h
      refine Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ?_⟩
      have := hx z
      show x ⬝ᵥ zr z = (zr z ⬝ᵥ (N *ᵥ zr z)) / 2
      linarith
  have hnull : volume (⋃ z, H z) = 0 :=
    measure_iUnion_null fun z => bP (bD z.2) _
  calc volume (bE N) ≤ volume (bF N ∪ ⋃ z, H z) := measure_mono hsub
    _ ≤ volume (bF N) + volume (⋃ z, H z) := measure_union_le _ _
    _ = volume (bF N) := by rw [hnull, add_zero]
lemma bX {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) : IsOpen (bF N) := by
  obtain ⟨l, hl, hcoer⟩ := bL hpd
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  let R : ℕ := ⌈2 * n * (‖x‖ + 1) / l⌉₊
  let F : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(R : ℤ)) R
  let U : Set (Fin n → ℝ) := Metric.ball x 1 ∩
    ⋂ z ∈ F, {y | z ≠ 0 → 2 * (y ⬝ᵥ zr z) < zr z ⬝ᵥ (N *ᵥ zr z)}
  refine ⟨U, ?_, ?_, ?_⟩
  · rintro y ⟨hyb, hyF⟩ z hz
    by_cases hzF : z ∈ F
    · exact (Set.mem_iInter₂.mp hyF z hzF) hz
    · simp only [F, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hzF
      obtain ⟨i, hi⟩ := hzF
      have hzi : (R : ℤ) < |z i| := by
        rcases le_or_gt 0 (z i) with h | h
        · rw [abs_of_nonneg h]; omega
        · rw [abs_of_neg h]; omega
      have hbig : (R : ℝ) < ‖zr z‖ := by
        have h1 : ((R : ℤ) : ℝ) < |(z i : ℝ)| := by exact_mod_cast hzi
        calc (R : ℝ) = ((R : ℤ) : ℝ) := by norm_cast
          _ < |(z i : ℝ)| := h1
          _ = ‖zr z i‖ := by simp [zr, Real.norm_eq_abs]
          _ ≤ ‖zr z‖ := norm_le_pi_norm _ i
      have hR : 2 * n * (‖x‖ + 1) / l ≤ R := Nat.le_ceil _
      have htpos : 0 < ‖zr z‖ := lt_of_le_of_lt (Nat.cast_nonneg R) hbig
      have hlt : 2 * n * (‖x‖ + 1) < l * ‖zr z‖ := by
        have := lt_of_le_of_lt hR hbig
        rw [div_lt_iff₀ hl] at this
        linarith [mul_comm l ‖zr z‖]
      have hy : ‖y‖ ≤ ‖x‖ + 1 := by
        have h1 : dist y x < 1 := hyb
        have h2 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
          simpa using norm_add_le x (y - x)
        rw [dist_eq_norm] at h1
        linarith
      have hq := hcoer (zr z)
      have hd : y ⬝ᵥ zr z ≤ n * (‖y‖ * ‖zr z‖) :=
        (le_abs_self _).trans (bM y (zr z))
      have h3 := mul_lt_mul_of_pos_left hlt htpos
      have h4 : (n : ℝ) * (‖y‖ * ‖zr z‖) ≤ n * ((‖x‖ + 1) * ‖zr z‖) := by gcongr
      nlinarith
  · refine Metric.isOpen_ball.inter (isOpen_biInter_finset fun z _ => ?_)
    by_cases hz : z = 0
    · simp [hz]
    · have : {y : Fin n → ℝ | z ≠ 0 → 2 * (y ⬝ᵥ zr z) < zr z ⬝ᵥ (N *ᵥ zr z)} =
          {y | 2 * (y ⬝ᵥ zr z) < zr z ⬝ᵥ (N *ᵥ zr z)} := by
        ext y; simp [hz]
      rw [this]
      exact isOpen_lt (by fun_prop) continuous_const
  · exact ⟨Metric.mem_ball_self one_pos, Set.mem_iInter₂.mpr fun z _ hz => hx z hz⟩
lemma bY {N : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ} (hx : x ∈ bF N) : -x ∈ bF N := by
  intro z hz
  have := hx (-z) (neg_ne_zero.mpr hz)
  simp only [bC, mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg] at this ⊢
  linarith
lemma bZ (N : Matrix (Fin n) (Fin n) ℝ) : Convex ℝ (bF N) := by
  intro x hx y hy a b ha hb hab z hz
  have h1 := hx z hz
  have h2 := hy z hz
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hq : a * (zr z ⬝ᵥ (N *ᵥ zr z)) + b * (zr z ⬝ᵥ (N *ᵥ zr z)) =
      zr z ⬝ᵥ (N *ᵥ zr z) := by
    rw [← add_mul, hab, one_mul]
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    linarith
  · have := mul_lt_mul_of_pos_left h1 ha'
    have := mul_le_mul_of_nonneg_left h2.le hb
    linarith
lemma b7 (N : Matrix (Fin n) (Fin n) ℝ) : bF N - bF N = (2 : ℝ) • bF N := by
  ext v
  simp only [Set.mem_sub, Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    refine ⟨(1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-y),
      bZ N hx (bY hy) (by norm_num) (by norm_num)
        (by norm_num), ?_⟩
    module
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, -w, bY hw, by rw [sub_neg_eq_add, two_smul]⟩
lemma b8 {N : Matrix (Fin n) (Fin n) ℝ} (hpd : N.PosDef) :
    MeasurableSet (bF N) :=
  (bX hpd).measurableSet
lemma b9 {N : Matrix (Fin n) (Fin n) ℝ} {z : Fin n → ℤ} (h : N *ᵥ zr z ∈ (2 : ℝ) • bF N) : z = 0 := by
  obtain ⟨y, hy, hyz⟩ := h
  have hyz' : (2 : ℝ) • y = N *ᵥ zr z := hyz
  by_contra hz
  have h1 := hy z hz
  have h2 : 2 * (y ⬝ᵥ zr z) = zr z ⬝ᵥ (N *ᵥ zr z) := by
    rw [← smul_eq_mul, ← smul_dotProduct, hyz', dotProduct_comm]
  linarith
end VoronoiVolume
def ca (x : ℝ) : Prop := ∃ n : ℤ, x = n
end GraphicVoronoiPrototype
end
section
open MeasureTheory Filter Topology Metric
namespace FCBridge
variable {d : ℕ}
lemma cb {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) : ∃ δ > 0, ∀ t : Fin d → ℝ, ‖t‖ < δ → aa Ω t ≠ 0 := by
  have h0 : aa Ω 0 ≠ 0 := by
    rw [aj]
    exact_mod_cast (ENNReal.toReal_pos hpos.ne' hΩ).ne'
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_ne_fun (aG hΩ) continuous_const) 0 h0
  exact ⟨δ, hδ, fun t ht => hball (mem_ball_zero_iff.mpr ht)⟩
def cc (δ : ℝ) (Λ : Set (Fin d → ℝ)) : Prop :=
  ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → δ ≤ ‖l' - l‖
lemma aI.separated {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) : ∃ δ > 0, ∀ Λ : Set (Fin d → ℝ), aI Ω Λ → cc δ Λ := by
  obtain ⟨δ, hδ, h⟩ := cb hΩ hpos
  refine ⟨δ, hδ, fun Λ horth l hl l' hl' hne => ?_⟩
  by_contra hlt
  exact h _ (lt_of_not_ge hlt) (horth l hl l' hl' hne)
def cd (Λs : ℕ → Set (Fin d → ℝ)) (Λ : Set (Fin d → ℝ)) : Prop :=
  ∀ ε > 0, ∀ R : ℝ, ∀ᶠ k in atTop,
    (∀ l ∈ Λs k, ‖l‖ < R → ∃ l' ∈ Λ, ‖l - l'‖ < ε) ∧
      (∀ l ∈ Λ, ‖l‖ < R → ∃ l' ∈ Λs k, ‖l - l'‖ < ε)
lemma aI.of_weakTendsto {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) {Λs : ℕ → Set (Fin d → ℝ)} {Λ : Set (Fin d → ℝ)} (horth : ∀ k, aI Ω (Λs k)) (hlim : cd Λs Λ) : aI Ω Λ := by
  intro l hl l' hl' hne
  have hcont := (aG hΩ).continuousAt (x := l' - l)
  by_contra hne0
  have hpos : 0 < ‖aa Ω (l' - l)‖ := norm_pos_iff.mpr hne0
  obtain ⟨η, hη, hball⟩ := Metric.continuousAt_iff.mp hcont _ hpos
  set ε := min (η / 2) (‖l' - l‖ / 4) with hε
  have hεpos : 0 < ε := by
    have : 0 < ‖l' - l‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
    positivity
  obtain ⟨k, hk⟩ := ((hlim ε hεpos (max ‖l‖ ‖l'‖ + 1)).and (Eventually.of_forall fun _ => trivial)).exists
  obtain ⟨-, hk2⟩ := hk.1
  obtain ⟨m, hm, hlm⟩ := hk2 l hl (by linarith [le_max_left ‖l‖ ‖l'‖])
  obtain ⟨m', hm', hlm'⟩ := hk2 l' hl' (by linarith [le_max_right ‖l‖ ‖l'‖])
  have hmne : m ≠ m' := by
    intro h
    rw [← h] at hlm'
    have : ‖l' - l‖ ≤ ‖l - m‖ + ‖l' - m‖ := by
      calc ‖l' - l‖ = ‖(l' - m) - (l - m)‖ := by congr 1; abel
        _ ≤ ‖l' - m‖ + ‖l - m‖ := norm_sub_le _ _
        _ = ‖l - m‖ + ‖l' - m‖ := add_comm _ _
    have h1 : ε ≤ ‖l' - l‖ / 4 := min_le_right _ _
    linarith
  have hzero := horth k m hm m' hm' hmne
  have za : dist (m' - m) (l' - l) < η := by
    rw [dist_eq_norm]
    calc ‖m' - m - (l' - l)‖ = ‖(l - m) - (l' - m')‖ := by congr 1; abel
      _ ≤ ‖l - m‖ + ‖l' - m'‖ := norm_sub_le _ _
      _ < ε + ε := add_lt_add hlm hlm'
      _ ≤ η := by linarith [min_le_left (η / 2) (‖l' - l‖ / 4)]
  have := hball za
  rw [hzero, dist_eq_norm, zero_sub, norm_neg] at this
  exact lt_irrefl _ this
lemma cc.card_le {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ) (c : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) (T : Finset (Fin d → ℝ)) (hT : ↑T ⊆ Λ ∩ closedBall c r) : (T.card : ℝ) ≤ ((2 * r + δ) / δ) ^ d := by
  have hdisj : (T : Set (Fin d → ℝ)).PairwiseDisjoint fun l => ball l (δ / 2) := by
    intro l hl l' hl' hne
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    have hsep := hΛ l (hT hl).1 l' (hT hl').1 hne
    rw [mem_ball, dist_eq_norm] at hz hz'
    have : ‖l' - l‖ < δ := by
      calc ‖l' - l‖ = ‖(z - l) - (z - l')‖ := by congr 1; abel
        _ ≤ ‖z - l‖ + ‖z - l'‖ := norm_sub_le _ _
        _ < δ / 2 + δ / 2 := add_lt_add hz hz'
        _ = δ := by ring
    linarith
  have hsub : (⋃ l ∈ T, ball l (δ / 2)) ⊆ ball c (r + δ / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨l, hl, hzl⟩ := hz
    have hlc : dist l c ≤ r := mem_closedBall.mp (hT hl).2
    rw [mem_ball] at hzl ⊢
    calc dist z c ≤ dist z l + dist l c := dist_triangle _ _ _
      _ < δ / 2 + r := by linarith
      _ = r + δ / 2 := by ring
  have hvol := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => isOpen_ball.measurableSet)] at hvol
  simp only [Real.volume_pi_ball _ (half_pos hδ), Real.volume_pi_ball _ (by positivity : 0 < r + δ / 2), Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] at hvol
  rw [show 2 * (δ / 2) = δ by ring, show 2 * (r + δ / 2) = 2 * r + δ by ring] at hvol
  have h1 : ENNReal.ofReal ((T.card : ℝ) * δ ^ d) ≤ ENNReal.ofReal ((2 * r + δ) ^ d) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    exact hvol
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact h2
lemma cc.finite_inter_closedBall {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ) (c : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) : (Λ ∩ closedBall c r).Finite := by
  by_contra hinf
  obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
    (⌈((2 * r + δ) / δ) ^ d⌉₊ + 1)
  have h := hΛ.card_le hδ c hr T hT
  rw [hcard] at h
  push_cast at h
  linarith [Nat.le_ceil (((2 * r + δ) / δ) ^ d)]
lemma cc.countable {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ) : Λ.Countable := by
  have : Λ = ⋃ n : ℕ, Λ ∩ closedBall 0 n := by
    ext l
    simp only [Set.mem_iUnion, Set.mem_inter_iff, mem_closedBall_zero_iff]
    exact ⟨fun h => ⟨⌈‖l‖⌉₊, h, Nat.le_ceil _⟩, fun ⟨_, h, _⟩ => h⟩
  rw [this]
  exact Set.countable_iUnion fun n =>
    (hΛ.finite_inter_closedBall hδ 0 (Nat.cast_nonneg n)).countable
lemma cc.tsum_indicator_le {δ : ℝ} (hδ : 0 < δ) {S : Set (Fin d → ℝ)} (hS : cc δ S) (c : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) (P : (Fin d → ℝ) → Prop) [DecidablePred P] (hP : ∀ l ∈ S, P l → l ∈ closedBall c r) : ∑' l : S, (if P l then (1 : ENNReal) else 0) ≤ ENNReal.ofReal (((2 * r + δ) / δ) ^ d) := by
  classical
  set T : Set S := {l | P l} with hTdef
  have hfin : T.Finite := by
    have hF := hS.finite_inter_closedBall hδ c hr
    refine (hF.preimage (f := fun l : S => (l : Fin d → ℝ)) Subtype.val_injective.injOn).subset ?_
    intro l hl
    exact ⟨l.2, hP l l.2 hl⟩
  have hsum : ∑' l : S, (if P l then (1 : ENNReal) else 0) = ∑' l : T, (1 : ENNReal) := by
    rw [tsum_subtype T (fun _ => (1 : ENNReal))]
    refine tsum_congr fun l => ?_
    by_cases h : P l
    · simp [hTdef, h]
    · simp [hTdef, h]
  rw [hsum]
  have : Fintype T := hfin.fintype
  rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  set U : Finset (Fin d → ℝ) := Finset.univ.image fun l : T => ((l : S) : Fin d → ℝ)
  have hU : ↑U ⊆ S ∩ closedBall c r := by
    intro x hx
    simp only [U, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨(l : S).2, hP _ (l : S).2 l.2⟩
  have hcard : U.card = Fintype.card T := by
    rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext (Subtype.ext h)), Finset.card_univ]
  have h := hS.card_le hδ c hr U hU
  rw [hcard] at h
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h
lemma cc.tsum_far_le {δ : ℝ} (hδ : 0 < δ) {S : Set (Fin d → ℝ)} (hS : cc δ S) {f : (Fin d → ℝ) → ENNReal} (hf : Measurable f) {Q : Set (Fin d → ℝ)} (hQm : MeasurableSet Q) {a : Fin d → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hQ : Q ⊆ closedBall a ρ) (R : ℝ) : ∑' l : S, (if R ≤ ‖(l : Fin d → ℝ)‖ then ∫⁻ x in Q, f (x - l) else 0) ≤ ENNReal.ofReal (((2 * ρ + δ) / δ) ^ d) * ∫⁻ y in {y : Fin d → ℝ | R - ‖a‖ - ρ ≤ ‖y‖}, f y := by
  classical
  have : Countable S := (hS.countable hδ).to_subtype
  set M := ENNReal.ofReal (((2 * ρ + δ) / δ) ^ d) with hM
  set E : Set (Fin d → ℝ) := {y | R - ‖a‖ - ρ ≤ ‖y‖} with hE
  have hEm : MeasurableSet E := measurableSet_le measurable_const measurable_norm
  have hterm : ∀ l : S, (if R ≤ ‖(l : Fin d → ℝ)‖ then ∫⁻ x in Q, f (x - l) else 0) =
      ∫⁻ y, (if R ≤ ‖(l : Fin d → ℝ)‖ ∧ y + (l : Fin d → ℝ) ∈ Q then f y else 0) := by
    intro l
    by_cases hR : R ≤ ‖(l : Fin d → ℝ)‖
    · rw [if_pos hR, ← lintegral_indicator hQm,
        ← lintegral_add_right_eq_self _ (l : Fin d → ℝ)]
      refine lintegral_congr fun y => ?_
      by_cases hy : y + (l : Fin d → ℝ) ∈ Q
      · rw [Set.indicator_of_mem hy, if_pos ⟨hR, hy⟩, add_sub_cancel_right]
      · rw [Set.indicator_of_notMem hy, if_neg (fun h => hy h.2)]
    · simp [hR]
  simp_rw [hterm]
  have hmeas : ∀ l : S, Measurable fun y : Fin d → ℝ =>
      (if R ≤ ‖(l : Fin d → ℝ)‖ ∧ y + (l : Fin d → ℝ) ∈ Q then f y else 0) := by
    intro l
    by_cases hR : R ≤ ‖(l : Fin d → ℝ)‖
    · have : (fun y : Fin d → ℝ => if R ≤ ‖(l : Fin d → ℝ)‖ ∧ y + (l : Fin d → ℝ) ∈ Q then f y else 0) =
          ((fun y => y + (l : Fin d → ℝ)) ⁻¹' Q).indicator f := by
        funext y
        by_cases hy : y + (l : Fin d → ℝ) ∈ Q
        · simp [hR, hy]
        · simp [hy]
      rw [this]
      exact hf.indicator (measurable_add_const _ hQm)
    · simp only [hR, false_and, if_false]
      exact measurable_const
  rw [← lintegral_tsum fun l => (hmeas l).aemeasurable, ← lintegral_indicator hEm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ E
  · rw [Set.indicator_of_mem hy]
    calc ∑' l : S, (if R ≤ ‖(l : Fin d → ℝ)‖ ∧ y + (l : Fin d → ℝ) ∈ Q then f y else 0)
        ≤ ∑' l : S, f y * (if y + (l : Fin d → ℝ) ∈ Q then (1 : ENNReal) else 0) := by
          refine ENNReal.tsum_le_tsum fun l => ?_
          by_cases h : R ≤ ‖(l : Fin d → ℝ)‖ ∧ y + (l : Fin d → ℝ) ∈ Q
          · simp [h]
          · simp [h]
      _ = f y * ∑' l : S, (if y + (l : Fin d → ℝ) ∈ Q then (1 : ENNReal) else 0) :=
          ENNReal.tsum_mul_left
      _ ≤ f y * M := by
          gcongr
          refine hS.tsum_indicator_le hδ (a - y) hρ (fun l => y + (l : Fin d → ℝ) ∈ Q) fun l _ hl => ?_
          have := hQ hl
          rw [mem_closedBall, dist_eq_norm] at this ⊢
          calc ‖l - (a - y)‖ = ‖y + l - a‖ := by congr 1; abel
            _ ≤ ρ := this
      _ = M * f y := mul_comm _ _
  · rw [Set.indicator_of_notMem hy, mul_zero]
    have hy' : ‖y‖ < R - ‖a‖ - ρ := lt_of_not_ge hy
    refine le_of_eq (ENNReal.tsum_eq_zero.mpr fun l => ?_)
    rw [if_neg]
    rintro ⟨hR, hl⟩
    have hlQ := hQ hl
    rw [mem_closedBall, dist_eq_norm] at hlQ
    have : ‖(l : Fin d → ℝ)‖ ≤ ‖a‖ + ρ + ‖y‖ := by
      calc ‖(l : Fin d → ℝ)‖ = ‖(y + (l : Fin d → ℝ) - a) + a - y‖ := by congr 1; abel
        _ ≤ ‖(y + (l : Fin d → ℝ) - a) + a‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ ‖y + (l : Fin d → ℝ) - a‖ + ‖a‖ + ‖y‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ρ + ‖a‖ + ‖y‖ := by gcongr
        _ = ‖a‖ + ρ + ‖y‖ := by ring
    linarith
lemma cc.of_weakTendsto {δ : ℝ} {Λs : ℕ → Set (Fin d → ℝ)} {Λ : Set (Fin d → ℝ)} (hsep : ∀ k, cc δ (Λs k)) (hlim : cd Λs Λ) : cc δ Λ := by
  intro l hl l' hl' hne
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖l' - l‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  set ε := min ((δ - ‖l' - l‖) / 2) (‖l' - l‖ / 2) with hε
  have hεpos : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨k, hk⟩ := (hlim ε hεpos (max ‖l‖ ‖l'‖ + 1)).exists
  obtain ⟨m, hm, hlm⟩ := hk.2 l hl (by linarith [le_max_left ‖l‖ ‖l'‖])
  obtain ⟨m', hm', hlm'⟩ := hk.2 l' hl' (by linarith [le_max_right ‖l‖ ‖l'‖])
  have h1 : ε ≤ (δ - ‖l' - l‖) / 2 := min_le_left _ _
  have h2 : ε ≤ ‖l' - l‖ / 2 := min_le_right _ _
  have hmne : m ≠ m' := by
    intro h
    rw [← h] at hlm'
    have : ‖l' - l‖ ≤ ‖l - m‖ + ‖l' - m‖ := by
      calc ‖l' - l‖ = ‖(l' - m) - (l - m)‖ := by congr 1; abel
        _ ≤ ‖l' - m‖ + ‖l - m‖ := norm_sub_le _ _
        _ = ‖l - m‖ + ‖l' - m‖ := add_comm _ _
    linarith
  have za := hsep k m hm m' hm' hmne
  have : ‖m' - m‖ ≤ ‖l' - l‖ + ‖l - m‖ + ‖l' - m'‖ := by
    calc ‖m' - m‖ = ‖(l' - l) + (l - m) - (l' - m')‖ := by congr 1; abel
      _ ≤ ‖(l' - l) + (l - m)‖ + ‖l' - m'‖ := norm_sub_le _ _
      _ ≤ ‖l' - l‖ + ‖l - m‖ + ‖l' - m'‖ := by gcongr; exact norm_add_le _ _
  linarith
lemma ce {δ : ℝ} (hδ : 0 < δ) {Λs : ℕ → Set (Fin d → ℝ)} {Λ : Set (Fin d → ℝ)} (hsep : ∀ k, cc δ (Λs k)) (hlim : cd Λs Λ) {ψ : (Fin d → ℝ) → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {η : ℝ} (hη : 0 < η) : ∀ᶠ k in atTop, ∑' l : Λs k, ENNReal.ofReal (ψ l) ≤ ∑' l : Λ, ENNReal.ofReal (ψ l) + ENNReal.ofReal η := by
  classical
  obtain ⟨r, hr⟩ := hψs.isBounded.subset_closedBall 0
  set R₀ := max r 0 with hR₀
  have hR₀0 : 0 ≤ R₀ := le_max_right _ _
  have hsupp : ∀ x, R₀ < ‖x‖ → ψ x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
    have := hr hxs
    rw [mem_closedBall_zero_iff] at this
    linarith [le_max_left r 0]
  set N : ℝ := ((2 * R₀ + δ) / δ) ^ d with hN
  have za : 0 < N := by positivity
  set η' := η / N with hη'
  have hη'pos : 0 < η' := div_pos hη za
  obtain ⟨ε₀, hε₀, hunif⟩ := Metric.uniformContinuous_iff.mp
    (hψs.uniformContinuous_of_continuous hψc) η' hη'pos
  set ε := min ε₀ (δ / 2) with hε
  have hεpos : 0 < ε := lt_min hε₀ (half_pos hδ)
  filter_upwards [hlim ε hεpos (R₀ + 1)] with k hk
  obtain ⟨hk1, -⟩ := hk
  let p : Λs k → Fin d → ℝ := fun l =>
    if h : ‖(l : Fin d → ℝ)‖ < R₀ + 1 then (hk1 l l.2 h).choose else l
  have hp : ∀ l : Λs k, ‖(l : Fin d → ℝ)‖ ≤ R₀ →
      p l ∈ Λ ∧ ‖(l : Fin d → ℝ) - p l‖ < ε := by
    intro l hl
    have h : ‖(l : Fin d → ℝ)‖ < R₀ + 1 := by linarith
    simp only [p, dif_pos h]
    exact (hk1 l l.2 h).choose_spec
  set T : Set (Λs k) := {l | ‖(l : Fin d → ℝ)‖ ≤ R₀} with hT
  have hpt : ∀ l : Λs k, ENNReal.ofReal (ψ l) ≤
      T.indicator (fun l => ENNReal.ofReal (ψ (p l))) l +
        T.indicator (fun _ => ENNReal.ofReal η') l := by
    intro l
    by_cases hl : l ∈ T
    · rw [Set.indicator_of_mem hl, Set.indicator_of_mem hl, ← ENNReal.ofReal_add (hψ0 _)
        hη'pos.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hd : dist (l : Fin d → ℝ) (p l) < ε₀ := by
        rw [dist_eq_norm]
        exact (hp l hl).2.trans_le (min_le_left _ _)
      have := hunif hd
      rw [Real.dist_eq, abs_lt] at this
      linarith
    · rw [hsupp _ (lt_of_not_ge hl), ENNReal.ofReal_zero]
      exact zero_le
  calc ∑' l : Λs k, ENNReal.ofReal (ψ l)
      ≤ ∑' l : Λs k, (T.indicator (fun l => ENNReal.ofReal (ψ (p l))) l +
          T.indicator (fun _ => ENNReal.ofReal η') l) := ENNReal.tsum_le_tsum hpt
    _ = ∑' l : T, ENNReal.ofReal (ψ (p l)) + ∑' l : T, ENNReal.ofReal η' := by
        rw [ENNReal.tsum_add, ← tsum_subtype T, ← tsum_subtype T]
    _ ≤ ∑' l : Λ, ENNReal.ofReal (ψ l) + ENNReal.ofReal η := by
        gcongr
        ·
          let q : T → Λ := fun t => ⟨p t, (hp t t.2).1⟩
          have hq : Function.Injective q := by
            intro t₁ t₂ h
            have hpp : p t₁ = p t₂ := congrArg Subtype.val h
            by_contra hne
            have hne' : ((t₁ : Λs k) : Fin d → ℝ) ≠ t₂ := fun e =>
              hne (Subtype.ext (Subtype.ext e))
            have hs := hsep k _ (t₁ : Λs k).2 _ (t₂ : Λs k).2 hne'
            have h1 := (hp t₁ t₁.2).2
            have h2 := (hp t₂ t₂.2).2
            have : ‖((t₂ : Λs k) : Fin d → ℝ) - t₁‖ < δ := by
              calc ‖((t₂ : Λs k) : Fin d → ℝ) - t₁‖ =
                  ‖(((t₂ : Λs k) : Fin d → ℝ) - p t₂) - (((t₁ : Λs k) : Fin d → ℝ) - p t₁)‖ := by
                    rw [hpp]; congr 1; abel
                _ ≤ ‖((t₂ : Λs k) : Fin d → ℝ) - p t₂‖ + ‖((t₁ : Λs k) : Fin d → ℝ) - p t₁‖ :=
                    norm_sub_le _ _
                _ < ε + ε := add_lt_add h2 h1
                _ ≤ δ := by linarith [min_le_right ε₀ (δ / 2)]
            linarith
          exact ENNReal.tsum_comp_le_tsum_of_injective hq (fun l : Λ => ENNReal.ofReal (ψ l))
        ·
          have zb := (hsep k).tsum_indicator_le hδ 0 hR₀0
            (fun x => ‖x‖ ≤ R₀) fun x _ hx => mem_closedBall_zero_iff.mpr hx
          calc ∑' _ : T, ENNReal.ofReal η'
              = ∑' l : Λs k, ENNReal.ofReal η' *
                  (if ‖(l : Fin d → ℝ)‖ ≤ R₀ then (1 : ENNReal) else 0) := by
                rw [tsum_subtype T (fun _ => ENNReal.ofReal η')]
                refine tsum_congr fun l => ?_
                by_cases hl : ‖(l : Fin d → ℝ)‖ ≤ R₀
                · simp [hT, hl]
                · simp [hT, hl]
            _ = ENNReal.ofReal η' *
                  ∑' l : Λs k, (if ‖(l : Fin d → ℝ)‖ ≤ R₀ then (1 : ENNReal) else 0) :=
                ENNReal.tsum_mul_left
            _ ≤ ENNReal.ofReal η' * ENNReal.ofReal N := by gcongr
            _ = ENNReal.ofReal η := by
                rw [← ENNReal.ofReal_mul hη'pos.le, hη', div_mul_cancel₀ _ za.ne']
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
namespace FCBridge
variable {d : ℕ}
def cf (a : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Set.Ico ((a i : ℝ)) ((a i : ℝ) + 1)
lemma cg (a : Fin d → ℤ) : MeasurableSet (cf a) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ico
lemma ch (a : Fin d → ℤ) : volume (cf a) = 1 := by
  rw [cf, volume_pi_pi]
  simp [Real.volume_Ico]
lemma ci (z : Fin d → ℝ) : z ∈ cf (fun i => ⌊z i⌋) := by
  simp only [cf, Set.mem_univ_pi, Set.mem_Ico]
  exact fun i => ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
lemma cj (a : Fin d → ℤ) : cf a ⊆ closedBall (fun i => (a i : ℝ)) 1 := by
  intro x hx
  simp only [cf, Set.mem_univ_pi, Set.mem_Ico] at hx
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [(hx i).1, (hx i).2]
lemma ck {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) (ξ : Fin d → ℝ) : ‖aa Ω ξ‖ ^ 2 / volume.real Ω ^ 2 ≤ 1 := by
  have hr : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  have hle : ‖aa Ω ξ‖ ≤ volume.real Ω := by
    have := norm_setIntegral_le_of_norm_le_const_ae (μ := volume) (s := Ω)
      (f := exponentialCharacter ξ) (C := 1) hΩ.lt_top
      (Eventually.of_forall fun x => (norm_exponentialCharacter ξ x).le)
    simpa [aa] using this
  rw [div_le_one (pow_pos hr 2)]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2
lemma cl {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) {Λs : ℕ → Set (Fin d → ℝ)} {Λ : Set (Fin d → ℝ)} (hspec : ∀ k, spectralPair Ω (Λs k)) (hlim : cd Λs Λ) {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ k, cc δ (Λs k)) (a : Fin d → ℤ) : volume (cf a) ≤ ∑' v : Λ, ∫⁻ z in cf a, bf Ω (z - v) := by
  classical
  have hΩfin : volume Ω ≠ ⊤ := hΩb.measure_lt_top.ne
  have hΩpos : 0 < volume Ω := (hspec 0).2.1
  set Q := cf a with hQdef
  have hQm : MeasurableSet Q := cg a
  have hQfin : volume Q ≠ ⊤ := by rw [hQdef, ch]; exact ENNReal.one_ne_top
  have : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hQfin
  set ac : Fin d → ℝ := fun i => (a i : ℝ) with hac
  have za : Q ⊆ closedBall ac 1 := cj a
  set fr : (Fin d → ℝ) → ℝ := fun ξ => ‖aa Ω ξ‖ ^ 2 / volume.real Ω ^ 2 with hfr
  have zb : Continuous fr := ((aG hΩfin).norm.pow 2).div_const _
  have zc : ∀ ξ, 0 ≤ fr ξ := fun ξ => by positivity
  have zd : ∀ ξ, fr ξ ≤ 1 := ck hΩfin hΩpos
  have ze : ∀ v : Fin d → ℝ, Integrable (fun z => fr (z - v)) (volume.restrict Q) := by
    intro v
    refine (integrable_const (1 : ℝ)).mono' (zb.comp (continuous_sub_right v)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (zc _)]
    exact zd _
  set φr : (Fin d → ℝ) → ℝ := fun v => ∫ z in Q, fr (z - v) with hφr
  have hφ : ∀ v, ∫⁻ z in Q, bf Ω (z - v) = ENNReal.ofReal (φr v) := by
    intro v
    rw [hφr, ofReal_integral_eq_lintegral_ofReal (ze v)
      (Eventually.of_forall fun z => zc _)]
    rfl
  have hφr_nn : ∀ v, 0 ≤ φr v := fun v => integral_nonneg fun z => zc _
  have hφr_cont : Continuous φr := by
    refine continuous_of_dominated (bound := fun _ => (1 : ℝ))
      (fun v => (zb.comp (continuous_sub_right v)).aestronglyMeasurable)
      (fun v => Eventually.of_forall fun z => ?_) (integrable_const 1)
      (Eventually.of_forall fun z => zb.comp (continuous_const.sub continuous_id))
    rw [Real.norm_eq_abs, abs_of_nonneg (zc _)]
    exact zd _
  set f := bf Ω with hfdef
  have zf : Measurable f := bg hΩfin
  have zg : ∫⁻ y, f y ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.inv_ne_top.mpr hΩpos.ne')
    (bl hΩm hΩb hΩpos)
  set ν := volume.withDensity f with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity zg
  set E : ℕ → Set (Fin d → ℝ) := fun n => {y | (n : ℝ) ≤ ‖y‖} with hE
  have hEm : ∀ n, MeasurableSet (E n) := fun n => measurableSet_le measurable_const measurable_norm
  have zh : Antitone E := by
    intro m n hmn y hy
    simp only [hE, Set.mem_ofPred_eq] at hy ⊢
    exact le_trans (by exact_mod_cast hmn) hy
  have zi : (⋂ n, E n) = ∅ := by
    ext y
    simp only [hE, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    exact ⟨n, hn⟩
  have zj : Tendsto (ν ∘ E) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := ν) (fun n => (hEm n).nullMeasurableSet) zh
      ⟨0, measure_ne_top _ _⟩
    rwa [zi, measure_empty] at this
  set Mr : ℝ := ((2 * 1 + δ) / δ) ^ d with hMr
  have zk : 0 < Mr := by positivity
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεr : (0 : ℝ) < ε := hε
  have hpos' : 0 < ENNReal.ofReal ((ε : ℝ) / 2 / Mr) :=
    ENNReal.ofReal_pos.mpr (div_pos (half_pos hεr) zk)
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.mp zj _ hpos').exists
  set R : ℝ := N + ‖ac‖ + 1 with hR
  have zl : 0 ≤ R := by positivity
  set χ : (Fin d → ℝ) → ℝ := fun v => max 0 (min 1 (R + 1 - ‖v‖)) with hχ
  set ψ : (Fin d → ℝ) → ℝ := fun v => φr v * χ v with hψ
  have hχ_cont : Continuous χ :=
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hχ01 : ∀ v, 0 ≤ χ v ∧ χ v ≤ 1 := fun v =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hψ_cont : Continuous ψ := hφr_cont.mul hχ_cont
  have hψ_nn : ∀ v, 0 ≤ ψ v := fun v => mul_nonneg (hφr_nn v) (hχ01 v).1
  have hψ_le : ∀ v, ψ v ≤ φr v := fun v => by
    have := mul_le_mul_of_nonneg_left (hχ01 v).2 (hφr_nn v)
    simpa [hψ] using this
  have hψ_supp : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 (R + 1)) fun v hv => ?_
    rw [mem_closedBall_zero_iff, not_le] at hv
    have : χ v = 0 := by
      simp only [hχ]
      exact max_eq_left (le_trans (min_le_right _ _) (by linarith))
    simp [hψ, this]
  have hχ_one : ∀ v : Fin d → ℝ, ‖v‖ < R → χ v = 1 := by
    intro v hv
    simp only [hχ]
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  obtain ⟨k, hk⟩ := (ce hδ hsep hlim hψ_cont hψ_supp hψ_nn
    (half_pos hεr)).exists
  have : Countable (Λs k) := ((hsep k).countable hδ).to_subtype
  have zm : ∑' v : Λs k, ∫⁻ z in Q, f (z - v) = volume Q := by
    rw [← lintegral_tsum (f := fun (v : Λs k) (z : Fin d → ℝ) => f (z - v))
      fun v => (zf.comp (measurable_sub_const _)).aemeasurable]
    simp_rw [hfdef, bi (hspec k)]
    simp
  have hfar := (hsep k).tsum_far_le hδ zf hQm zero_le_one za R
  have zn : {y : Fin d → ℝ | R - ‖ac‖ - 1 ≤ ‖y‖} = E N := by
    ext y
    simp only [hE, Set.mem_ofPred_eq, hR]
    constructor <;> intro h <;> linarith
  rw [zn, ← withDensity_apply f (hEm N)] at hfar
  have hfar' : ENNReal.ofReal Mr * ν (E N) ≤ ENNReal.ofReal ((ε : ℝ) / 2) := by
    calc ENNReal.ofReal Mr * ν (E N) ≤ ENNReal.ofReal Mr * ENNReal.ofReal ((ε : ℝ) / 2 / Mr) := by
          gcongr
          exact hN
      _ = ENNReal.ofReal ((ε : ℝ) / 2) := by
          rw [← ENNReal.ofReal_mul zk.le, mul_div_cancel₀ _ zk.ne']
  have hsplit : ∀ v : Λs k, ∫⁻ z in Q, f (z - v) ≤ ENNReal.ofReal (ψ v) +
      (if R ≤ ‖(v : Fin d → ℝ)‖ then ∫⁻ x in Q, f (x - v) else 0) := by
    intro v
    by_cases hv : R ≤ ‖(v : Fin d → ℝ)‖
    · rw [if_pos hv]
      exact le_add_self
    · rw [if_neg hv, add_zero, hφ, hψ]
      simp only
      rw [hχ_one _ (lt_of_not_ge hv), mul_one]
  have hΛ : ∑' v : Λ, ENNReal.ofReal (ψ v) ≤ ∑' v : Λ, ∫⁻ z in Q, f (z - v) :=
    ENNReal.tsum_le_tsum fun v => by rw [hφ]; exact ENNReal.ofReal_le_ofReal (hψ_le v)
  calc volume Q = ∑' v : Λs k, ∫⁻ z in Q, f (z - v) := zm.symm
    _ ≤ ∑' v : Λs k, (ENNReal.ofReal (ψ v) +
          (if R ≤ ‖(v : Fin d → ℝ)‖ then ∫⁻ x in Q, f (x - v) else 0)) :=
        ENNReal.tsum_le_tsum hsplit
    _ = ∑' v : Λs k, ENNReal.ofReal (ψ v) +
          ∑' v : Λs k, (if R ≤ ‖(v : Fin d → ℝ)‖ then ∫⁻ x in Q, f (x - v) else 0) :=
        ENNReal.tsum_add
    _ ≤ (∑' v : Λ, ENNReal.ofReal (ψ v) + ENNReal.ofReal ((ε : ℝ) / 2)) +
          ENNReal.ofReal Mr * ν (E N) := add_le_add hk hfar
    _ ≤ ((∑' v : Λ, ∫⁻ z in Q, f (z - v)) + ENNReal.ofReal ((ε : ℝ) / 2)) +
          ENNReal.ofReal ((ε : ℝ) / 2) :=
        add_le_add (add_le_add hΛ le_rfl) hfar'
    _ = (∑' v : Λ, ∫⁻ z in Q, f (z - v)) + ε := by
        rw [add_assoc, ← ENNReal.ofReal_add (half_pos hεr).le (half_pos hεr).le, add_halves, ENNReal.ofReal_coe_nnreal]
lemma cm {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) {Λs : ℕ → Set (Fin d → ℝ)} {Λ : Set (Fin d → ℝ)} (hspec : ∀ k, spectralPair Ω (Λs k)) (hlim : cd Λs Λ) : spectralPair Ω Λ := by
  classical
  have hΩfin : volume Ω ≠ ⊤ := hΩb.measure_lt_top.ne
  have hΩpos : 0 < volume Ω := (hspec 0).2.1
  have za : ∀ k, aI Ω (Λs k) := by
    intro k
    obtain ⟨-, -, -, horth, -⟩ := al.mp (hspec k)
    exact horth
  obtain ⟨δ, hδ, hsepO⟩ := aI.separated hΩfin hΩpos
  have hsep : ∀ k, cc δ (Λs k) := fun k => hsepO _ (za k)
  have horth : aI Ω Λ := aI.of_weakTendsto hΩfin za hlim
  have hsepΛ : cc δ Λ := cc.of_weakTendsto hsep hlim
  have : Countable Λ := (hsepΛ.countable hδ).to_subtype
  refine bk hΩm.nullMeasurableSet hΩfin hΩpos horth ?_
  set F : (Fin d → ℝ) → ENNReal := fun z => ∑' v : Λ, bf Ω (z - v) with hF
  have hFmeas : Measurable F :=
    Measurable.tsum fun v => (bg hΩfin).comp (measurable_sub_const _)
  have zb : ∀ z, F z ≤ 1 := bj hΩfin hΩpos horth
  have zc : ∀ a : Fin d → ℤ, ∀ᵐ z ∂volume, z ∈ cf a → F z = 1 := by
    intro a
    have hQm := cg (d := d) a
    have hQfin : volume (cf a) ≠ ⊤ := by rw [ch]; exact ENNReal.one_ne_top
    have hsum : ∫⁻ z in cf a, F z =
        ∑' v : Λ, ∫⁻ z in cf a, bf Ω (z - v) :=
      lintegral_tsum (f := fun (v : Λ) (z : Fin d → ℝ) => bf Ω (z - v))
        fun v => ((bg hΩfin).comp (measurable_sub_const _)).aemeasurable
    have hint : volume (cf a) ≤ ∫⁻ z in cf a, F z := by
      rw [hsum]
      exact cl hΩm hΩb hspec hlim hδ hsep a
    have hone : ∫⁻ _ in cf a, (1 : ENNReal) = volume (cf a) := by
      rw [lintegral_const, Measure.restrict_apply_univ, one_mul]
    have zd : ∫⁻ _ in cf a, (1 : ENNReal) ≠ ⊤ := by
      rw [hone]
      exact hQfin
    have hae : F =ᵐ[volume.restrict (cf a)] fun _ => 1 := by
      refine ae_eq_of_ae_le_of_lintegral_le (Eventually.of_forall zb)
        (ne_top_of_le_ne_top zd (lintegral_mono zb)) aemeasurable_const ?_
      rw [hone]
      exact hint
    exact (ae_restrict_iff' hQm).mp hae
  filter_upwards [ae_all_iff.mpr zc] with z hz
  exact hz _ (ci z)
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
namespace FCBridge
variable {d : ℕ}
def cn (q : Fin d → ℚ) : Fin d → ℝ := fun i => (q i : ℝ)
lemma co (y : Fin d → ℝ) {r : ℝ} (hr : 0 < r) : ∃ q : Fin d → ℚ, ‖y - cn q‖ < r := by
  have h : ∀ i, ∃ q : ℚ, y i - r < q ∧ (q : ℝ) < y i + r := fun i =>
    exists_rat_btwn (by linarith)
  choose q hq using h
  refine ⟨q, (pi_norm_lt_iff hr).2 fun i => ?_⟩
  simp only [Pi.sub_apply, cn, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [(hq i).1, (hq i).2]
lemma cp (Λs : ℕ → Set (Fin d → ℝ)) : ∃ Λ : Set (Fin d → ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧ cd (fun k => Λs (φ k)) Λ := by
  classical
  let x : ℕ → ((Fin d → ℚ) × ℚ) → Bool := fun k p =>
    decide (∃ l ∈ Λs k, ‖l - cn p.1‖ < (p.2 : ℝ))
  obtain ⟨a, φ, hφ, htend⟩ := CompactSpace.tendsto_subseq x
  have hev : ∀ p, ∀ᶠ k in atTop, x (φ k) p = a p := fun p => by
    have h := tendsto_pi_nhds.1 htend p
    rw [nhds_discrete, tendsto_pure] at h
    exact h
  let Λ : Set (Fin d → ℝ) :=
    {y | ∀ p : (Fin d → ℚ) × ℚ, ‖y - cn p.1‖ < (p.2 : ℝ) → a p = true}
  have key : ∀ p, a p = true → ∃ y ∈ Λ, ‖y - cn p.1‖ ≤ (p.2 : ℝ) := by
    intro p hp
    obtain ⟨K, hK⟩ := (hev p).exists_forall_of_atTop
    have hz : ∀ n, ∃ l ∈ Λs (φ (n + K)), ‖l - cn p.1‖ < (p.2 : ℝ) := fun n => by
      have h := hK (n + K) (by omega)
      rw [hp] at h
      simpa [x] using h
    choose z hzΛ hzb using hz
    have za : ∀ n, z n ∈ closedBall (cn p.1) (p.2 : ℝ) := fun n => by
      rw [mem_closedBall, dist_eq_norm]
      exact (hzb n).le
    obtain ⟨y, hy, ψ, hψ, hlim⟩ := (isCompact_closedBall _ _).tendsto_subseq za
    rw [mem_closedBall, dist_eq_norm] at hy
    refine ⟨y, fun p' hp' => ?_, hy⟩
    have h1 : ∀ᶠ n in atTop, ‖z (ψ n) - cn p'.1‖ < (p'.2 : ℝ) :=
      ((hlim.sub_const (cn p'.1)).norm).eventually_lt_const hp'
    have h2 : ∀ᶠ n in atTop, x (φ (ψ n + K)) p' = a p' := by
      have ht : Tendsto (fun n => ψ n + K) atTop atTop :=
        tendsto_atTop_mono (fun n => Nat.le_add_right (ψ n) K) hψ.tendsto_atTop
      exact ht.eventually (hev p')
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    rw [← hn2]
    simpa [x] using ⟨z (ψ n), hzΛ (ψ n), hn1⟩
  refine ⟨Λ, φ, hφ, fun ε hε R => ?_⟩
  obtain ⟨r0, hr0, hr0ε⟩ := exists_rat_btwn (half_pos hε)
  have hr0' : (0 : ℝ) < r0 := hr0
  have zb : closedBall (0 : Fin d → ℝ) R ⊆ ⋃ q : Fin d → ℚ, ball (cn q) (r0 : ℝ) := by
    intro y _
    obtain ⟨q, hq⟩ := co y hr0'
    exact Set.mem_iUnion.2 ⟨q, by rwa [mem_ball, dist_eq_norm]⟩
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : Fin d → ℝ) R).elim_finite_subcover _
    (fun _ => isOpen_ball) zb
  have hall : ∀ᶠ k in atTop, ∀ q ∈ t, x (φ k) (q, r0) = a (q, r0) :=
    t.eventually_all.2 fun q _ => hev (q, r0)
  filter_upwards [hall] with k hk
  have hcover : ∀ l : Fin d → ℝ, ‖l‖ < R → ∃ q ∈ t, ‖l - cn q‖ < (r0 : ℝ) := by
    intro l hlR
    have hlmem : l ∈ closedBall (0 : Fin d → ℝ) R := mem_closedBall_zero_iff.2 hlR.le
    obtain ⟨q, hqt, hq⟩ := Set.mem_iUnion₂.1 (ht hlmem)
    rw [mem_ball, dist_eq_norm] at hq
    exact ⟨q, hqt, hq⟩
  constructor
  · intro l hl hlR
    obtain ⟨q, hqt, hq⟩ := hcover l hlR
    have zc : x (φ k) (q, r0) = true := by simpa [x] using ⟨l, hl, hq⟩
    rw [hk q hqt] at zc
    obtain ⟨y, hyΛ, hy⟩ := key (q, r0) zc
    have hy' : ‖y - cn q‖ ≤ (r0 : ℝ) := hy
    refine ⟨y, hyΛ, ?_⟩
    calc ‖l - y‖ = ‖(l - cn q) - (y - cn q)‖ := by congr 1; abel
      _ ≤ ‖l - cn q‖ + ‖y - cn q‖ := norm_sub_le _ _
      _ < ε := by linarith
  · intro l hl hlR
    obtain ⟨q, hqt, hq⟩ := hcover l hlR
    have ha : a (q, r0) = true := hl (q, r0) hq
    rw [← hk q hqt] at ha
    have hex : ∃ l' ∈ Λs (φ k), ‖l' - cn q‖ < (r0 : ℝ) := by simpa [x] using ha
    obtain ⟨l', hl', hl'q⟩ := hex
    refine ⟨l', hl', ?_⟩
    calc ‖l - l'‖ = ‖(l - cn q) - (l' - cn q)‖ := by congr 1; abel
      _ ≤ ‖l - cn q‖ + ‖l' - cn q‖ := norm_sub_le _ _
      _ < ε := by linarith
lemma cq {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (v : Fin d → ℝ) : spectralPair Ω {l | l + v ∈ Λ} := by
  have hh := h
  obtain ⟨hmeas, hpos, hS, -⟩ := hh
  obtain ⟨-, -, -, horth, -⟩ := al.1 h
  refine bk hmeas hS hpos ?_ (Eventually.of_forall fun z => ?_)
  · intro ξ₁ h₁ ξ₂ h₂ hne
    have h' := horth (ξ₁ + v) h₁ (ξ₂ + v) h₂ (fun h => hne (add_right_cancel h))
    rwa [add_sub_add_right_eq_sub] at h'
  · let e : {l | l + v ∈ Λ} ≃ Λ := (Equiv.addRight v).subtypeEquiv fun _ => Iff.rfl
    calc ∑' l : {l | l + v ∈ Λ}, bf Ω (z - l)
        = ∑' l : {l | l + v ∈ Λ}, bf Ω ((z + v) - (e l : Fin d → ℝ)) := by
          refine tsum_congr fun l => ?_
          show bf Ω (z - l) = bf Ω ((z + v) - ((l : Fin d → ℝ) + v))
          rw [add_sub_add_right_eq_sub]
      _ = ∑' μ : Λ, bf Ω ((z + v) - μ) := e.tsum_eq (fun μ : Λ => bf Ω ((z + v) - μ))
      _ = 1 := bi h (z + v)
lemma cr {Λ C : Set (Fin d → ℝ)} (hΛ : ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → l' - l ∈ C) (v : Fin d → ℝ) : ∀ l ∈ {l | l + v ∈ Λ}, ∀ l' ∈ {l | l + v ∈ Λ}, l ≠ l' → l' - l ∈ C := by
  intro l hl l' hl' hne
  have h' := hΛ (l + v) hl (l' + v) hl' (fun h => hne (add_right_cancel h))
  rwa [add_sub_add_right_eq_sub] at h'
lemma cs {Ω Λ : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) (h : spectralPair Ω Λ) (v : ℕ → Fin d → ℝ) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Λ' : Set (Fin d → ℝ), cd (fun k => {l | l + v (φ k) ∈ Λ}) Λ' ∧ spectralPair Ω Λ' := by
  obtain ⟨Λ', φ, hφ, hlim⟩ := cp (fun k => {l | l + v k ∈ Λ})
  exact ⟨φ, hφ, Λ', hlim,
    cm hΩm hΩb (fun k => cq h _) hlim⟩
lemma ct {Λs : ℕ → Set (Fin d → ℝ)} {Λ : Set (Fin d → ℝ)} (hlim : cd Λs Λ) {C : Set (Fin d → ℝ)} (hC : IsClosed C) (hΛs : ∀ᶠ k in atTop, ∀ l ∈ Λs k, ∀ l' ∈ Λs k, l ≠ l' → l' - l ∈ C) : ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → l' - l ∈ C := by
  intro l hl l' hl' hne
  have hd : 0 < ‖l' - l‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  rw [← hC.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hηpos : 0 < min (ε / 2) (‖l' - l‖ / 2) := lt_min (half_pos hε) (half_pos hd)
  have hη1 := min_le_left (ε / 2) (‖l' - l‖ / 2)
  have hη2 := min_le_right (ε / 2) (‖l' - l‖ / 2)
  obtain ⟨k, hk, hCk⟩ := ((hlim _ hηpos (max ‖l‖ ‖l'‖ + 1)).and hΛs).exists
  obtain ⟨m, hm, hlm⟩ := hk.2 l hl (by have := le_max_left ‖l‖ ‖l'‖; linarith)
  obtain ⟨m', hm', hlm'⟩ := hk.2 l' hl' (by have := le_max_right ‖l‖ ‖l'‖; linarith)
  have za : ‖l' - l - (m' - m)‖ ≤ ‖l' - m'‖ + ‖l - m‖ := by
    calc ‖l' - l - (m' - m)‖ = ‖(l' - m') - (l - m)‖ := by congr 1; abel
      _ ≤ ‖l' - m'‖ + ‖l - m‖ := norm_sub_le _ _
  have hmm : m ≠ m' := by
    rintro rfl
    have h3 : ‖l' - l‖ ≤ ‖l' - m‖ + ‖l - m‖ := by simpa using za
    linarith
  refine ⟨m' - m, hCk m hm m' hm' hmm, ?_⟩
  rw [dist_eq_norm]
  linarith
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Real
namespace FCBridge
section Step
variable {n m : ℕ}
lemma measurableSet_productSet {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) : MeasurableSet (productSet A B) :=
  show MeasurableSet (proj₁ ⁻¹' A ∩ proj₂ ⁻¹' B) from
    (measurable_proj₁ hA).inter (measurable_proj₂ hB)
lemma isBounded_productSet {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)} (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B) : Bornology.IsBounded (productSet A B) := by
  obtain ⟨RA, hRA⟩ := hA.subset_closedBall 0
  obtain ⟨RB, hRB⟩ := hB.subset_closedBall 0
  refine (isBounded_closedBall (x := (0 : Fin (n + m) → ℝ)) (r := max RA RB)).subset ?_
  intro x hx
  have h1 : ‖proj₁ x‖ ≤ RA := mem_closedBall_zero_iff.1 (hRA hx.1)
  have h2 : ‖proj₂ x‖ ≤ RB := mem_closedBall_zero_iff.1 (hRB hx.2)
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg
    ((norm_nonneg _).trans (h1.trans (le_max_left _ _)))).2 fun i => ?_
  refine Fin.addCases (motive := fun i => ‖x i‖ ≤ max RA RB) (fun i₁ => ?_) (fun i₂ => ?_) i
  · exact (norm_le_pi_norm (proj₁ x) i₁).trans (h1.trans (le_max_left _ _))
  · exact (norm_le_pi_norm (proj₂ x) i₂).trans (h2.trans (le_max_right _ _))
def cu (w : Fin n → ℝ) : Fin (n + m) → ℝ := Fin.append w 0
theorem proj₁_blockVec (w : Fin n → ℝ) : proj₁ (cu (m := m) w) = w := proj₁_append _ _
theorem proj₂_blockVec (w : Fin n → ℝ) : proj₂ (cu (m := m) w) = 0 := proj₂_append _ _
theorem proj₁_add (z z' : Fin (n + m) → ℝ) : proj₁ (z + z') = proj₁ z + proj₁ z' := rfl
theorem proj₂_add (z z' : Fin (n + m) → ℝ) : proj₂ (z + z') = proj₂ z + proj₂ z' := rfl
theorem proj₁_smul (a : ℝ) (z : Fin (n + m) → ℝ) : proj₁ (a • z) = a • proj₁ z := rfl
theorem proj₂_smul (a : ℝ) (z : Fin (n + m) → ℝ) : proj₂ (a • z) = a • proj₂ z := rfl
theorem proj₁_zero : proj₁ (0 : Fin (n + m) → ℝ) = 0 := rfl
theorem continuous_proj₁ : Continuous (proj₁ : (Fin (n + m) → ℝ) → Fin n → ℝ) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_proj₂ : Continuous (proj₂ : (Fin (n + m) → ℝ) → Fin m → ℝ) :=
  continuous_pi fun _ => continuous_apply _
end Step
lemma cv {d : ℕ} {Λ Λ' : Set (Fin d → ℝ)} {W : Fin d → ℝ} {φ : ℕ → ℕ} (hφ : StrictMono φ) (hlim : cd (fun k => {l | l + (φ k : ℝ) • W ∈ Λ}) Λ') {l l' : Fin d → ℝ} (hl : l ∈ Λ') (hl' : l' ∈ Λ') : ∃ a b : ℕ → Fin d → ℝ, ∃ N : ℕ → ℕ, (∀ j, a j ∈ Λ) ∧ (∀ j, b j ∈ Λ) ∧ Tendsto N atTop atTop ∧ Tendsto (fun j => b j - a j - (N j : ℝ) • W) atTop (𝓝 (l' - l)) := by
  have hev : ∀ j : ℕ, ∀ᶠ k in atTop,
      (∃ x ∈ {x | x + (φ k : ℝ) • W ∈ Λ}, ‖l - x‖ < 1 / ((j : ℝ) + 1)) ∧
      (∃ y ∈ {y | y + (φ k : ℝ) • W ∈ Λ}, ‖l' - y‖ < 1 / ((j : ℝ) + 1)) := by
    intro j
    have hε : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    filter_upwards [hlim _ hε (max ‖l‖ ‖l'‖ + 1)] with k hk
    exact ⟨hk.2 l hl (by have := le_max_left ‖l‖ ‖l'‖; linarith),
      hk.2 l' hl' (by have := le_max_right ‖l‖ ‖l'‖; linarith)⟩
  choose K hK using fun j => (hev j).exists_forall_of_atTop
  have h1 : ∀ j, ∃ x, x + (φ (K j) : ℝ) • W ∈ Λ ∧ ‖l - x‖ < 1 / ((j : ℝ) + 1) := fun j => by
    obtain ⟨⟨x, hx, hxl⟩, -⟩ := hK j (K j) le_rfl
    exact ⟨x, hx, hxl⟩
  have h2 : ∀ j, ∃ y, y + (φ (j + 1 + K j) : ℝ) • W ∈ Λ ∧ ‖l' - y‖ < 1 / ((j : ℝ) + 1) :=
    fun j => by
      obtain ⟨-, ⟨y, hy, hyl⟩⟩ := hK j (j + 1 + K j) (Nat.le_add_left _ _)
      exact ⟨y, hy, hyl⟩
  choose x hxΛ hxl using h1
  choose y hyΛ hyl using h2
  have hle : ∀ j, j + 1 + φ (K j) ≤ φ (j + 1 + K j) := fun j => hφ.add_le_nat (j + 1) (K j)
  refine ⟨fun j => x j + (φ (K j) : ℝ) • W, fun j => y j + (φ (j + 1 + K j) : ℝ) • W,
    fun j => φ (j + 1 + K j) - φ (K j), hxΛ, hyΛ, ?_, ?_⟩
  · refine tendsto_atTop_mono (fun j => ?_) tendsto_id
    have := hle j
    show j ≤ φ (j + 1 + K j) - φ (K j)
    omega
  · have za : ∀ j, ((φ (j + 1 + K j) - φ (K j) : ℕ) : ℝ) =
        (φ (j + 1 + K j) : ℝ) - (φ (K j) : ℝ) := fun j =>
      Nat.cast_sub (by have := hle j; omega)
    have heq : ∀ j, y j - x j = (y j + (φ (j + 1 + K j) : ℝ) • W) - (x j + (φ (K j) : ℝ) • W) -
        ((φ (j + 1 + K j) - φ (K j) : ℕ) : ℝ) • W := fun j => by
      rw [za, sub_smul]; abel
    have hx : Tendsto x atTop (𝓝 l) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_sub_rev]
      exact (hxl j).le
    have hy : Tendsto y atTop (𝓝 l') := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [norm_sub_rev]
      exact (hyl j).le
    exact (hy.sub hx).congr' (Eventually.of_forall heq)
section Step
variable {n m : ℕ}
lemma cw {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)}
    (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
    {Λ : Set (Fin (n + m) → ℝ)} (hΛ : spectralPair (productSet A B) Λ)
    (w : Fin n → ℝ) (ρ : (Fin n → ℝ) →L[ℝ] ℝ) (hρw : ρ w = 1)
    (Φ Ψ : (Fin n → ℝ) → ℂ) (hΨ : Continuous Ψ) (hΨw : ∀ ξ (s : ℝ), Ψ (ξ + s • w) = Ψ ξ)
    (hasymp : ∀ ζ : Fin n → ℝ, Tendsto (fun p : (Fin n → ℝ) × ℝ =>
        ((π * ρ (p.1 + p.2 • w) : ℝ) : ℂ) * Φ (p.1 + p.2 • w) -
          (Real.sin (π * ρ (p.1 + p.2 • w)) : ℂ) * Ψ (p.1 + p.2 • w))
        (𝓝 ζ ×ˢ atTop) (𝓝 0))
    (Q : Set (Fin (n + m) → ℝ)) (hQ : IsClosed Q)
    (hQW : ∀ t, ∀ k : ℕ, t + (k : ℝ) • cu (m := m) w ∈ Q → t ∈ Q)
    (hcond : ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' →
      l' - l ∈ Q ∨ Φ (proj₁ (l' - l)) = 0 ∨ aa B (proj₂ (l' - l)) = 0) :
    ∃ Λ', spectralPair (productSet A B) Λ' ∧
      (∀ C : Set (Fin (n + m) → ℝ), IsClosed C →
        (∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → l' - l ∈ C) →
          ∀ l ∈ Λ', ∀ l' ∈ Λ', l ≠ l' → l' - l ∈ C) ∧
      ∀ l ∈ Λ', ∀ l' ∈ Λ', l ≠ l' →
        l' - l ∈ Q ∨ (∃ k : ℤ, ρ (proj₁ (l' - l)) = k) ∨ Ψ (proj₁ (l' - l)) = 0 ∨
          aa B (proj₂ (l' - l)) = 0 := by
  classical
  obtain ⟨φ, hφ, Λ', hlim, hΛ'⟩ := cs
    (measurableSet_productSet hAm hBm) (isBounded_productSet hAb hBb) hΛ
    (fun k => (k : ℝ) • cu (m := m) w)
  refine ⟨Λ', hΛ', fun C hC hCΛ => ct hlim hC
    (Eventually.of_forall fun k => cr hCΛ _), ?_⟩
  intro l hl l' hl' _
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hQn, hZn, hΨn, hBn⟩ := hcon
  obtain ⟨a, b, N, ha, hb, hN, hconv⟩ := cv hφ hlim hl hl'
  set ζ : ℕ → Fin (n + m) → ℝ := fun j => b j - a j - (N j : ℝ) • cu (m := m) w
    with hζdef
  have hconv' : Tendsto ζ atTop (𝓝 (l' - l)) := hconv
  have hD : ∀ j, b j - a j = ζ j + (N j : ℝ) • cu (m := m) w := fun j => by
    simp only [hζdef]; abel
  have hp₁ : ∀ j, proj₁ (b j - a j) = proj₁ (ζ j) + (N j : ℝ) • w := fun j => by
    rw [hD, proj₁_add, proj₁_smul, proj₁_blockVec]
  have hp₂ : ∀ j, proj₂ (b j - a j) = proj₂ (ζ j) := fun j => by
    rw [hD, proj₂_add, proj₂_smul, proj₂_blockVec, smul_zero, add_zero]
  have hζ₁ : Tendsto (fun j => proj₁ (ζ j)) atTop (𝓝 (proj₁ (l' - l))) :=
    (continuous_proj₁.tendsto _).comp hconv'
  have hζ₂ : Tendsto (fun j => proj₂ (ζ j)) atTop (𝓝 (proj₂ (l' - l))) :=
    (continuous_proj₂.tendsto _).comp hconv'
  have za : ∀ᶠ j in atTop, b j - a j ∉ Q := by
    filter_upwards [hconv' (hQ.isOpen_compl.mem_nhds hQn)] with j hj hmem
    exact hj (hQW (ζ j) (N j) (by rw [← hD]; exact hmem))
  have zb : ∀ᶠ j in atTop, aa B (proj₂ (b j - a j)) ≠ 0 := by
    have ht : Tendsto (fun j => aa B (proj₂ (ζ j))) atTop (𝓝 (aa B (proj₂ (l' - l)))) :=
      ((aG hBb.measure_lt_top.ne).tendsto _).comp hζ₂
    filter_upwards [ht.eventually_ne hBn] with j hj
    rwa [hp₂]
  have hρD : ∀ j, ρ (proj₁ (b j - a j)) = ρ (proj₁ (ζ j)) + N j := fun j => by
    rw [hp₁, map_add, map_smul, hρw, smul_eq_mul, mul_one]
  have hρζ : Tendsto (fun j => ρ (proj₁ (ζ j))) atTop (𝓝 (ρ (proj₁ (l' - l)))) :=
    (ρ.continuous.tendsto _).comp hζ₁
  have zc : ∀ᶠ j in atTop, a j ≠ b j := by
    have h1 : ∀ᶠ j in atTop, |ρ (proj₁ (ζ j)) - ρ (proj₁ (l' - l))| < 1 := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hρζ).eventually (gt_mem_nhds one_pos)
      simpa [Real.norm_eq_abs] using this
    have h2 : ∀ᶠ j in atTop, (|ρ (proj₁ (l' - l))| + 2 : ℝ) < N j :=
      (tendsto_natCast_atTop_atTop.comp hN).eventually (eventually_gt_atTop _)
    filter_upwards [h1, h2] with j hj1 hj2 hab
    have h0 : ρ (proj₁ (b j - a j)) = 0 := by
      rw [hab, sub_self, proj₁_zero, map_zero]
    rw [hρD] at h0
    have h3 := abs_lt.1 hj1
    have h4 := neg_abs_le (ρ (proj₁ (l' - l)))
    linarith [h3.1]
  have hΦev : ∀ᶠ j in atTop, Φ (proj₁ (b j - a j)) = 0 := by
    filter_upwards [za, zb, zc] with j hj1 hj2 hj3
    rcases hcond (a j) (ha j) (b j) (hb j) hj3 with h | h | h
    · exact absurd h hj1
    · exact h
    · exact absurd h hj2
  have hp : Tendsto (fun j => (proj₁ (ζ j), (N j : ℝ))) atTop
      (𝓝 (proj₁ (l' - l)) ×ˢ atTop) :=
    hζ₁.prodMk (tendsto_natCast_atTop_atTop.comp hN)
  have hA := (hasymp (proj₁ (l' - l))).comp hp
  have hS : Tendsto (fun j => -((Real.sin (π * ρ (proj₁ (b j - a j))) : ℂ) *
      Ψ (proj₁ (ζ j)))) atTop (𝓝 0) := by
    refine hA.congr' ?_
    filter_upwards [hΦev] with j hj
    show ((π * ρ (proj₁ (ζ j) + (N j : ℝ) • w) : ℝ) : ℂ) * Φ (proj₁ (ζ j) + (N j : ℝ) • w) -
        (Real.sin (π * ρ (proj₁ (ζ j) + (N j : ℝ) • w)) : ℂ) *
          Ψ (proj₁ (ζ j) + (N j : ℝ) • w) = _
    rw [hΨw, ← hp₁, hj, mul_zero, zero_sub]
  have hS' : Tendsto (fun j => (Real.sin (π * ρ (proj₁ (b j - a j))) : ℂ) *
      Ψ (proj₁ (ζ j))) atTop (𝓝 0) := by
    simpa using hS.neg
  have hΨt : Tendsto (fun j => Ψ (proj₁ (ζ j))) atTop (𝓝 (Ψ (proj₁ (l' - l)))) :=
    (hΨ.tendsto _).comp hζ₁
  have zd : Tendsto (fun j => (Real.sin (π * ρ (proj₁ (b j - a j))) : ℂ)) atTop (𝓝 0) := by
    have ze := hS'.div hΨt hΨn
    rw [zero_div] at ze
    refine ze.congr' ?_
    filter_upwards [hΨt.eventually_ne hΨn] with j hj
    exact mul_div_cancel_right₀ _ hj
  have zf : Tendsto (fun j => Real.sin (π * ρ (proj₁ (b j - a j)))) atTop (𝓝 0) := by
    have h := (Complex.continuous_re.tendsto _).comp zd
    rw [Complex.zero_re] at h
    exact h.congr fun j => Complex.ofReal_re _
  have habs : ∀ j, |Real.sin (π * ρ (proj₁ (ζ j)))| =
      |Real.sin (π * ρ (proj₁ (b j - a j)))| := fun j => by
    rw [hρD, mul_add, mul_comm π (N j : ℝ), Real.sin_add_nat_mul_pi, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have zg : Tendsto (fun j => |Real.sin (π * ρ (proj₁ (ζ j)))|) atTop (𝓝 0) := by
    simp_rw [habs]
    simpa using zf.abs
  have zh : Tendsto (fun j => |Real.sin (π * ρ (proj₁ (ζ j)))|) atTop
      (𝓝 |Real.sin (π * ρ (proj₁ (l' - l)))|) :=
    (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).abs).tendsto _).comp hρζ
  have h0 : Real.sin (π * ρ (proj₁ (l' - l))) = 0 :=
    abs_eq_zero.1 (tendsto_nhds_unique zh zg)
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 h0
  exact hZn ⟨k, (mul_left_cancel₀ Real.pi_ne_zero (by rw [← hk]; ring))⟩
end Step
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Real
namespace FCBridge
def cx : Set (Fin 1 → ℝ) := {x | x 0 ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)}
lemma cy : MeasurableSet cx :=
  measurableSet_Icc.preimage (measurable_pi_apply 0)
lemma cz {t a b : ℝ} (ht : t ≠ 0) (hab : a ≤ b) : ∫ s in Set.Icc a b, Complex.exp (2 * π * Complex.I * (t * s)) = (Complex.exp (2 * π * Complex.I * (t * b)) - Complex.exp (2 * π * Complex.I * (t * a))) / (2 * π * Complex.I * t) := by
  have hc : (2 * π * Complex.I * t : ℂ) ≠ 0 := by
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp_all
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have h := integral_exp_mul_complex (a := a) (b := b) hc
  simp only [mul_assoc] at h ⊢
  exact h
lemma cA (t : ℝ) : ((π * t : ℝ) : ℂ) * aa cx (fun _ => t) = (Real.sin (π * t) : ℂ) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have he : ∀ x : Fin 1 → ℝ, e x = x 0 := fun _ => rfl
  have hmp : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have hset : cx = e ⁻¹' Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := rfl
  let g : ℝ → ℂ := fun s => Complex.exp (2 * π * Complex.I * (t * s))
  have hchar : ∀ x : Fin 1 → ℝ, exponentialCharacter (fun _ => t) x = g (e x) := by
    intro x
    simp only [exponentialCharacter, Fin.sum_univ_one, he, g]
    push_cast
    ring_nf
  have hft : aa cx (fun _ => t) = ∫ s in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), g s := by
    unfold aa
    rw [← hmp.setIntegral_preimage_emb e.measurableEmbedding g, ← hset]
    exact setIntegral_congr_fun cy fun x _ => hchar x
  rw [hft, cz ht (by norm_num), Complex.ofReal_sin, Complex.sin]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e1 : Complex.exp (2 * π * Complex.I * (t * ((1 / 2 : ℝ) : ℂ))) =
      Complex.exp (((π * t : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  have e2 : Complex.exp (2 * π * Complex.I * (t * ((-(1 / 2) : ℝ) : ℂ))) =
      Complex.exp (-((π * t : ℝ) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  rw [e1, e2]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring
noncomputable def cB {k : ℕ} (η : Fin k → ℝ) : StrongDual ℝ (Fin k → ℝ) :=
  -(∑ i, η i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i)
lemma cC {k : ℕ} (η v : Fin k → ℝ) : cB η v = -(∑ i, η i * v i) := by
  simp [cB]
lemma cD {k : ℕ} (η : Fin k → ℝ) : ‖η‖ ≤ ‖cB η‖ := by
  classical
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 : cB η (Pi.single i 1) = -η i := by
    rw [cC]
    simp [Pi.single_apply]
  have h2 := (cB η).le_opNorm (Pi.single i 1)
  rw [h1, norm_neg] at h2
  have h3 : ‖(Pi.single i (1 : ℝ) : Fin k → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  calc ‖η i‖ ≤ ‖cB η‖ * ‖(Pi.single i (1 : ℝ) : Fin k → ℝ)‖ := h2
    _ ≤ ‖cB η‖ * 1 := by gcongr
    _ = ‖cB η‖ := mul_one _
lemma cE {k : ℕ} {G : Set (Fin k → ℝ)} (hG : MeasurableSet G) : Tendsto (aa G) (Bornology.cobounded (Fin k → ℝ)) (𝓝 0) := by
  have hι : Tendsto (cB (k := k)) (Bornology.cobounded (Fin k → ℝ))
      (cocompact (StrongDual ℝ (Fin k → ℝ))) := by
    rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop (E := StrongDual ℝ (Fin k → ℝ)), tendsto_comap_iff]
    exact tendsto_atTop_mono (fun η => cD η) tendsto_norm_cobounded_atTop
  have hRL := (tendsto_integral_exp_smul_cocompact
    (G.indicator fun _ => (1 : ℂ)) (volume : Measure (Fin k → ℝ))).comp hι
  refine hRL.congr fun η => ?_
  simp only [Function.comp_apply, aa]
  rw [← integral_indicator hG]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  by_cases hv : v ∈ G
  · simp only [Set.indicator_of_mem hv, Circle.smul_def, smul_eq_mul, mul_one, cC,
      neg_neg, Real.fourierChar_apply, exponentialCharacter]
    congr 1
    push_cast
    ring
  · simp [Set.indicator_of_notMem hv]
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Real
namespace FCBridge
section Coordinates
variable {k : ℕ}
def nH (v : Fin (k + 1) → ℝ) : Fin k → ℝ := fun i => v (Fin.castAdd 1 i)
def nV (v : Fin (k + 1) → ℝ) : ℝ := v (Fin.natAdd k 0)
def pt (y' : Fin k → ℝ) (s : ℝ) : Fin (k + 1) → ℝ := Fin.append y' (fun _ : Fin 1 => s)
lemma dotProduct_pt (v : Fin (k + 1) → ℝ) (y' : Fin k → ℝ) (s : ℝ) : v ⬝ᵥ pt y' s = nH v ⬝ᵥ y' + nV v * s := by
  simp [dotProduct, Fin.sum_univ_add, nH, nV, pt]
lemma nV_pt (y' : Fin k → ℝ) (s : ℝ) : nV (pt y' s) = s := by
  simp [nV, pt]
lemma norm_le_norm_pt (y' : Fin k → ℝ) (s : ℝ) : ‖y'‖ ≤ ‖pt y' s‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (pt y' s) (Fin.castAdd 1 i)
  simpa [pt] using this
lemma continuous_pt (y' : Fin k → ℝ) : Continuous fun s : ℝ => pt y' s := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (motive := fun i => Continuous fun s : ℝ => pt y' s i)
    (fun i₁ => ?_) (fun i₂ => ?_) i
  · simp only [pt, Fin.append_left]; exact continuous_const
  · simp only [pt, Fin.append_right]; exact continuous_id
lemma cF (η y' : Fin k → ℝ) (t s : ℝ) : exponentialCharacter (pt η t) (pt y' s) = exponentialCharacter η y' * Complex.exp (2 * π * Complex.I * (t * s)) := by
  rw [pt, ar]
  congr 1
  · congr 1
    funext i
    simp [pt]
  · simp [exponentialCharacter, pt]
lemma cG {S : Set (Fin (k + 1) → ℝ)} (hSm : MeasurableSet S) (hSb : Bornology.IsBounded S) (η : Fin k → ℝ) (t : ℝ) : aa S (pt η t) = ∫ y', exponentialCharacter η y' * ∫ s in {s | pt y' s ∈ S}, Complex.exp (2 * π * Complex.I * (t * s)) := by
  set F : (Fin (k + 1) → ℝ) → ℂ := S.indicator (exponentialCharacter (pt η t)) with hF
  have za : Integrable F := by
    rw [hF, integrable_indicator_iff hSm]
    exact ((continuous_exponentialCharacter _).continuousOn.integrableOn_compact
      hSb.isCompact_closure).mono_set subset_closure
  have hmp := (an k 1).symm
  have h1 : aa S (pt η t) = ∫ y, F y := (integral_indicator hSm).symm
  have h2 : ∫ y, F y = ∫ p, F ((am k 1).symm p) := (hmp.integral_comp' F).symm
  have hint2 : Integrable (fun p => F ((am k 1).symm p)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hmp.integrable_comp_emb (am k 1).symm.measurableEmbedding).2 za
  rw [h1, h2, Measure.volume_eq_prod, integral_prod _ hint2]
  refine integral_congr_ae (Eventually.of_forall fun y' => ?_)
  have zb := (volume_preserving_funUnique (Fin 1) ℝ).symm
  have hsymm : ∀ s : ℝ, (MeasurableEquiv.funUnique (Fin 1) ℝ).symm s = fun _ => s :=
    fun s => (MeasurableEquiv.symm_apply_eq _).2 rfl
  have h3 : ∫ u : Fin 1 → ℝ, F ((am k 1).symm (y', u)) = ∫ s : ℝ, F (pt y' s) := by
    have h5 := zb.integral_comp' (fun u => F ((am k 1).symm (y', u)))
    calc ∫ u : Fin 1 → ℝ, F ((am k 1).symm (y', u))
        = ∫ s : ℝ, F ((am k 1).symm (y', (MeasurableEquiv.funUnique (Fin 1) ℝ).symm s)) :=
          h5.symm
      _ = ∫ s : ℝ, F (pt y' s) := by
          refine integral_congr_ae (Eventually.of_forall fun s => ?_)
          simp only [hsymm, bn, pt]
  have zc : MeasurableSet {s | pt y' s ∈ S} := hSm.preimage (continuous_pt y').measurable
  have h4 : ∀ s, F (pt y' s) = {s | pt y' s ∈ S}.indicator
      (fun s => exponentialCharacter η y' * Complex.exp (2 * π * Complex.I * (t * s))) s := by
    intro s
    by_cases hs : pt y' s ∈ S
    · rw [hF, Set.indicator_of_mem hs, Set.indicator_of_mem (show s ∈ {s | pt y' s ∈ S} from hs),
        cF]
    · rw [hF, Set.indicator_of_notMem hs,
        Set.indicator_of_notMem (show s ∉ {s | pt y' s ∈ S} from hs)]
  show ∫ u : Fin 1 → ℝ, F ((am k 1).symm (y', u)) = _
  rw [h3, integral_congr_ae (Eventually.of_forall h4), integral_indicator zc, integral_const_mul]
end Coordinates
section Fibers
variable {k r : ℕ} (N : Fin r → Fin (k + 1) → ℝ) (h : Fin r → ℝ)
def cH (y' : Fin k → ℝ) (s : ℝ) : Prop := ∀ j, nH (N j) ⬝ᵥ y' + nV (N j) * s ≤ h j
noncomputable def bd (j : Fin r) (y' : Fin k → ℝ) : ℝ := (h j - nH (N j) ⬝ᵥ y') / nV (N j)
def Gp (Sg : Set (Fin k → ℝ)) (j : Fin r) : Set (Fin k → ℝ) :=
  {y' | y' ∉ Sg ∧ 0 < nV (N j) ∧ cH N h y' (bd N h j y') ∧
    ∀ i, i < j → 0 < nV (N i) → ¬ cH N h y' (bd N h i y')}
def Gm (Sg : Set (Fin k → ℝ)) (j : Fin r) : Set (Fin k → ℝ) :=
  {y' | y' ∉ Sg ∧ nV (N j) < 0 ∧ cH N h y' (bd N h j y') ∧
    ∀ i, i < j → nV (N i) < 0 → ¬ cH N h y' (bd N h i y')}
variable {N h}
lemma continuous_dotProduct_left (v : Fin k → ℝ) : Continuous fun y' : Fin k → ℝ => v ⬝ᵥ y' :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_apply i)
lemma cI (j : Fin r) : IsClosed {y' : Fin k → ℝ | cH N h y' (bd N h j y')} := by
  simp only [cH, Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_le ?_ continuous_const
  exact (continuous_dotProduct_left _).add (continuous_const.mul
    ((continuous_const.sub (continuous_dotProduct_left _)).div_const _))
lemma cJ {Sg : Set (Fin k → ℝ)} (hSg : MeasurableSet Sg) (j : Fin r) : MeasurableSet (Gp N h Sg j) := by
  have : Gp N h Sg j = Sgᶜ ∩ ({_y' | 0 < nV (N j)} ∩ ({y' | cH N h y' (bd N h j y')} ∩
      ⋂ i, ⋂ (_ : i < j), ⋂ (_ : 0 < nV (N i)), {y' | cH N h y' (bd N h i y')}ᶜ)) := by
    ext y'; simp [Gp]
  rw [this]
  refine hSg.compl.inter (MeasurableSet.const _ |>.inter ((cI j).measurableSet.inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      (cI i).measurableSet.compl)))
lemma cK {Sg : Set (Fin k → ℝ)} (hSg : MeasurableSet Sg) (j : Fin r) : MeasurableSet (Gm N h Sg j) := by
  have : Gm N h Sg j = Sgᶜ ∩ ({_y' | nV (N j) < 0} ∩ ({y' | cH N h y' (bd N h j y')} ∩
      ⋂ i, ⋂ (_ : i < j), ⋂ (_ : nV (N i) < 0), {y' | cH N h y' (bd N h i y')}ᶜ)) := by
    ext y'; simp [Gm]
  rw [this]
  refine hSg.compl.inter (MeasurableSet.const _ |>.inter ((cI j).measurableSet.inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      (cI i).measurableSet.compl)))
lemma cH.of_between {y' : Fin k → ℝ} {a b s : ℝ} (ha : cH N h y' a) (hb : cH N h y' b) (has : a ≤ s) (hsb : s ≤ b) : cH N h y' s := by
  intro j
  rcases le_or_gt 0 (nV (N j)) with hj | hj
  · have := mul_le_mul_of_nonneg_left hsb hj
    linarith [hb j]
  · have := mul_le_mul_of_nonpos_left has hj.le
    linarith [ha j]
lemma cH.le_bd {y' : Fin k → ℝ} {s : ℝ} (hs : cH N h y' s) {j : Fin r} (hj : 0 < nV (N j)) : s ≤ bd N h j y' := by
  rw [bd, le_div_iff₀ hj]
  linarith [hs j]
lemma cH.bd_le {y' : Fin k → ℝ} {s : ℝ} (hs : cH N h y' s) {j : Fin r} (hj : nV (N j) < 0) : bd N h j y' ≤ s := by
  rw [bd, div_le_iff_of_neg hj]
  linarith [hs j]
lemma cL (j : Fin r) (y' : Fin k → ℝ) (hj : nV (N j) ≠ 0) : nH (N j) ⬝ᵥ y' + nV (N j) * bd N h j y' = h j := by
  rw [bd, mul_div_cancel₀ _ hj]
  ring
lemma cM {y' : Fin k → ℝ} {s₀ : ℝ} (hs₀ : cH N h y' s₀) (hpos : ∃ j, 0 < nV (N j)) : ∃ j, 0 < nV (N j) ∧ cH N h y' (bd N h j y') := by
  classical
  obtain ⟨j₀, hj₀⟩ := hpos
  obtain ⟨j, hjmem, hjmin⟩ := (Finset.univ.filter fun j => 0 < nV (N j)).exists_min_image
    (fun j => bd N h j y') ⟨j₀, by simp [hj₀]⟩
  have hj : 0 < nV (N j) := by simpa using hjmem
  refine ⟨j, hj, fun i => ?_⟩
  rcases lt_or_ge 0 (nV (N i)) with hi | hi
  · have hle : bd N h j y' ≤ bd N h i y' := hjmin i (by simp [hi])
    have := mul_le_mul_of_nonneg_left hle hi.le
    linarith [cL (N := N) (h := h) i y' hi.ne']
  · have hle : s₀ ≤ bd N h j y' := hs₀.le_bd hj
    have := mul_le_mul_of_nonpos_left hle hi
    linarith [hs₀ i]
lemma cN {y' : Fin k → ℝ} {s₀ : ℝ} (hs₀ : cH N h y' s₀) (hneg : ∃ j, nV (N j) < 0) : ∃ j, nV (N j) < 0 ∧ cH N h y' (bd N h j y') := by
  classical
  obtain ⟨j₀, hj₀⟩ := hneg
  obtain ⟨j, hjmem, hjmax⟩ := (Finset.univ.filter fun j => nV (N j) < 0).exists_max_image
    (fun j => bd N h j y') ⟨j₀, by simp [hj₀]⟩
  have hj : nV (N j) < 0 := by simpa using hjmem
  refine ⟨j, hj, fun i => ?_⟩
  rcases lt_or_ge (nV (N i)) 0 with hi | hi
  · have hle : bd N h i y' ≤ bd N h j y' := hjmax i (by simp [hi])
    have := mul_le_mul_of_nonpos_left hle hi.le
    linarith [cL (N := N) (h := h) i y' hi.ne]
  · have hle : bd N h j y' ≤ s₀ := hs₀.bd_le hj
    have := mul_le_mul_of_nonneg_left hle hi
    linarith [hs₀ i]
lemma cO {Sg : Set (Fin k → ℝ)} {y' : Fin k → ℝ} {j j' : Fin r} (hj : y' ∈ Gp N h Sg j) (hj' : y' ∈ Gp N h Sg j') : j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd hj.2.2.1 (hj'.2.2.2 j hlt hj.2.1)
  · exact heq
  · exact absurd hj'.2.2.1 (hj.2.2.2 j' hgt hj'.2.1)
lemma cP {Sg : Set (Fin k → ℝ)} {y' : Fin k → ℝ} {j j' : Fin r} (hj : y' ∈ Gm N h Sg j) (hj' : y' ∈ Gm N h Sg j') : j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd hj.2.2.1 (hj'.2.2.2 j hlt hj.2.1)
  · exact heq
  · exact absurd hj'.2.2.1 (hj.2.2.2 j' hgt hj'.2.1)
lemma cQ {Sg : Set (Fin k → ℝ)} {y' : Fin k → ℝ} (hy : y' ∉ Sg) {s₀ : ℝ} (hs₀ : cH N h y' s₀) (hpos : ∃ j, 0 < nV (N j)) : ∃ j, y' ∈ Gp N h Sg j := by
  classical
  obtain ⟨j₀, hj₀, hj₀f⟩ := cM hs₀ hpos
  set T := Finset.univ.filter fun j => 0 < nV (N j) ∧ cH N h y' (bd N h j y') with hT
  have hTne : T.Nonempty := ⟨j₀, by simp [hT, hj₀, hj₀f]⟩
  have hmem := T.min'_mem hTne
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨T.min' hTne, hy, hmem.1, hmem.2, fun i hi hipos hif => ?_⟩
  have : T.min' hTne ≤ i := T.min'_le i (by simp [hT, hipos, hif])
  exact absurd hi (not_lt.2 this)
lemma cR {Sg : Set (Fin k → ℝ)} {y' : Fin k → ℝ} (hy : y' ∉ Sg) {s₀ : ℝ} (hs₀ : cH N h y' s₀) (hneg : ∃ j, nV (N j) < 0) : ∃ j, y' ∈ Gm N h Sg j := by
  classical
  obtain ⟨j₀, hj₀, hj₀f⟩ := cN hs₀ hneg
  set T := Finset.univ.filter fun j => nV (N j) < 0 ∧ cH N h y' (bd N h j y') with hT
  have hTne : T.Nonempty := ⟨j₀, by simp [hT, hj₀, hj₀f]⟩
  have hmem := T.min'_mem hTne
  simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨T.min' hTne, hy, hmem.1, hmem.2, fun i hi hineg hif => ?_⟩
  have : T.min' hTne ≤ i := T.min'_le i (by simp [hT, hineg, hif])
  exact absurd hi (not_lt.2 this)
lemma cS {Sg : Set (Fin k → ℝ)} {y' : Fin k → ℝ} {jp jm : Fin r} (hp : y' ∈ Gp N h Sg jp) (hm : y' ∈ Gm N h Sg jm) : {s | cH N h y' s} = Set.Icc (bd N h jm y') (bd N h jp y') := by
  ext s
  constructor
  · intro hs
    exact ⟨cH.bd_le hs hm.2.1, cH.le_bd hs hp.2.1⟩
  · rintro ⟨h1, h2⟩
    exact cH.of_between hm.2.2.1 hp.2.2.1 h1 h2
end Fibers
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Real
namespace FCBridge
section Limit
variable {k r : ℕ}
lemma continuous_pt_left (s : ℝ) : Continuous fun y' : Fin k → ℝ => pt y' s := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (motive := fun i => Continuous fun y' : Fin k → ℝ => pt y' s i)
    (fun i₁ => ?_) (fun i₂ => ?_) i
  · simp only [pt, Fin.append_left]; exact continuous_apply i₁
  · simp only [pt, Fin.append_right]; exact continuous_const
lemma pt_nH_nV (y : Fin (k + 1) → ℝ) : pt (nH y) (nV y) = y := by
  funext i
  refine Fin.addCases (motive := fun i => pt (nH y) (nV y) i = y i) (fun i₁ => ?_)
    (fun i₂ => ?_) i
  · simp [pt, nH]
  · rw [Fin.fin_one_eq_zero i₂]; simp [pt, nV]
lemma cT (Sg : Set (Fin k → ℝ)) (y' : Fin k → ℝ) (s : ℝ) : pt y' s ∈ productSet Sg cx ↔ y' ∈ Sg ∧ s ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
  have h1 : (fun i => pt y' s (Fin.castAdd 1 i)) = y' := by funext i; simp [pt]
  have h2 : (fun j => pt y' s (Fin.natAdd k j)) = fun _ => s := by funext j; simp [pt]
  show (fun i => pt y' s (Fin.castAdd 1 i)) ∈ Sg ∧ (fun j => pt y' s (Fin.natAdd k j)) ∈ cx ↔ _
  rw [h1, h2]
  rfl
lemma cU (ξ x : Fin k → ℝ) : exponentialCharacter ξ x = Complex.exp (2 * π * Complex.I * ((ξ ⬝ᵥ x : ℝ) : ℂ)) := by
  unfold exponentialCharacter dotProduct
  push_cast
  rfl
def cV (P : Set (Fin (k + 1) → ℝ)) : Set (Fin k → ℝ) := {y' | pt y' (1 / 2) ∈ P}
structure FacetData (N : Fin r → Fin (k + 1) → ℝ) (h : Fin r → ℝ) (P : Set (Fin (k + 1) → ℝ)) :
    Prop where
  mem_iff : ∀ y, y ∈ P ↔ ∀ j, N j ⬝ᵥ y ≤ h j
  bounded : Bornology.IsBounded P
  height_le : ∀ y ∈ P, |nV y| ≤ 1 / 2
  bot_iff : ∀ y', pt y' (-(1 / 2)) ∈ P ↔ pt y' (1 / 2) ∈ P
  nonempty : ∃ y', pt y' (1 / 2) ∈ P
  prism : ∀ y', pt y' (1 / 2) ∈ P → ∀ s ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2), pt y' s ∈ P
variable {N : Fin r → Fin (k + 1) → ℝ} {h : Fin r → ℝ} {P : Set (Fin (k + 1) → ℝ)}
lemma cW (η y' : Fin k → ℝ) (j : Fin r) (t : ℝ) : exponentialCharacter η y' * Complex.exp (2 * π * Complex.I * (t * bd N h j y')) = Complex.exp (((2 * π * (t * (h j / nV (N j))) : ℝ) : ℂ) * Complex.I) * exponentialCharacter (η - (t / nV (N j)) • nH (N j)) y' := by
  have key : (η - (t / nV (N j)) • nH (N j)) ⬝ᵥ y' =
      η ⬝ᵥ y' - t / nV (N j) * (nH (N j) ⬝ᵥ y') := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [cU, cU, key, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [bd]
  push_cast
  ring
lemma cX {v : Fin k → ℝ} (hv : v ≠ 0) {c : ℝ} (hc : c ≠ 0) (ζ : Fin k → ℝ) : Tendsto (fun q : (Fin k → ℝ) × ℝ => q.1 - (q.2 / c) • v) (𝓝 ζ ×ˢ atTop) (Bornology.cobounded (Fin k → ℝ)) := by
  rw [← comap_norm_atTop, tendsto_comap_iff]
  have za : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hcpos : 0 < |c| := abs_pos.2 hc
  have h1 : ∀ᶠ q : (Fin k → ℝ) × ℝ in 𝓝 ζ ×ˢ atTop, ‖q.1‖ < ‖ζ‖ + 1 :=
    tendsto_fst.eventually ((continuous_norm.tendsto ζ).eventually (gt_mem_nhds (lt_add_one _)))
  have h2 : Tendsto (fun q : (Fin k → ℝ) × ℝ => |q.2| / |c| * ‖v‖ + -(‖ζ‖ + 1))
      (𝓝 ζ ×ˢ atTop) atTop :=
    (((tendsto_abs_atTop_atTop.comp tendsto_snd).atTop_div_const hcpos).atTop_mul_const
      za).atTop_add tendsto_const_nhds
  refine tendsto_atTop_mono' _ ?_ h2
  filter_upwards [h1] with q hq
  have h3 : ‖(q.2 / c) • v‖ = |q.2| / |c| * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div]
  have h4 := norm_sub_norm_le ((q.2 / c) • v) q.1
  rw [norm_sub_rev] at h4
  simp only [Function.comp]
  linarith
namespace FacetData
variable (hF : FacetData N h P)
include hF
lemma pt_mem_iff (y' : Fin k → ℝ) (s : ℝ) : pt y' s ∈ P ↔ cH N h y' s := by
  rw [hF.mem_iff]
  simp only [cH, dotProduct_pt]
lemma isClosed : IsClosed P := by
  have : P = ⋂ j, {y | N j ⬝ᵥ y ≤ h j} := by ext y; simp [hF.mem_iff]
  rw [this]
  exact isClosed_iInter fun j => isClosed_le (continuous_dotProduct_left _) continuous_const
lemma measurableSet : MeasurableSet P := hF.isClosed.measurableSet
lemma measurableSet_topSlice : MeasurableSet (cV P) :=
  hF.measurableSet.preimage (continuous_pt_left _).measurable
lemma subset_closedBall : ∃ R, ∀ y' s, pt y' s ∈ P → ‖y'‖ ≤ R := by
  obtain ⟨R, hR⟩ := hF.bounded.subset_closedBall 0
  exact ⟨R, fun y' s hs => (norm_le_norm_pt y' s).trans (mem_closedBall_zero_iff.1 (hR hs))⟩
lemma isBounded_topSlice : Bornology.IsBounded (cV P) := by
  obtain ⟨R, hR⟩ := hF.subset_closedBall
  exact (isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := R)).subset fun y' hy' =>
    mem_closedBall_zero_iff.2 (hR y' _ hy')
lemma isBounded_Gp (j : Fin r) : Bornology.IsBounded (Gp N h (cV P) j) := by
  obtain ⟨R, hR⟩ := hF.subset_closedBall
  exact (isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := R)).subset fun y' hy' =>
    mem_closedBall_zero_iff.2 (hR y' _ ((hF.pt_mem_iff _ _).2 hy'.2.2.1))
lemma isBounded_Gm (j : Fin r) : Bornology.IsBounded (Gm N h (cV P) j) := by
  obtain ⟨R, hR⟩ := hF.subset_closedBall
  exact (isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := R)).subset fun y' hy' =>
    mem_closedBall_zero_iff.2 (hR y' _ ((hF.pt_mem_iff _ _).2 hy'.2.2.1))
lemma exists_pos : ∃ j, 0 < nV (N j) := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  obtain ⟨y₀, hy₀⟩ := hF.nonempty
  have h1 : cH N h y₀ (1 / 2) := (hF.pt_mem_iff _ _).1 hy₀
  have h2 : cH N h y₀ (3 / 2) := fun j => by
    have := h1 j
    have := mul_le_mul_of_nonpos_left (show (1 / 2 : ℝ) ≤ 3 / 2 by norm_num) (hcon j)
    linarith
  have h3 := hF.height_le _ ((hF.pt_mem_iff _ _).2 h2)
  rw [nV_pt] at h3
  linarith [(abs_le.1 h3).2]
lemma exists_neg : ∃ j, nV (N j) < 0 := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  obtain ⟨y₀, hy₀⟩ := hF.nonempty
  have h1 : cH N h y₀ (-(1 / 2)) := (hF.pt_mem_iff _ _).1 ((hF.bot_iff y₀).2 hy₀)
  have h2 : cH N h y₀ (-(3 / 2)) := fun j => by
    have := h1 j
    have := mul_le_mul_of_nonneg_left (show -(3 / 2 : ℝ) ≤ -(1 / 2) by norm_num) (hcon j)
    linarith
  have h3 := hF.height_le _ ((hF.pt_mem_iff _ _).2 h2)
  rw [nV_pt] at h3
  linarith [(abs_le.1 h3).1]
lemma nH_ne_zero_of_Gp {j : Fin r} (hne : (Gp N h (cV P) j).Nonempty) : nH (N j) ≠ 0 := by
  obtain ⟨y', hyS, hpos, hin, -⟩ := hne
  intro hz
  obtain ⟨y₀, hy₀⟩ := hF.nonempty
  have h0 : cH N h y₀ (1 / 2) := (hF.pt_mem_iff _ _).1 hy₀
  have hc : bd N h j y' = h j / nV (N j) := by simp [bd, hz]
  have hle : bd N h j y' ≤ 1 / 2 := by
    have := hF.height_le _ ((hF.pt_mem_iff _ _).2 hin)
    rw [nV_pt] at this
    exact (abs_le.1 this).2
  have hge : 1 / 2 ≤ bd N h j y' := by
    rw [hc, le_div_iff₀ hpos]
    have := h0 j
    rw [hz, zero_dotProduct] at this
    linarith
  have hhalf : bd N h j y' = 1 / 2 := le_antisymm hle hge
  exact hyS ((hF.pt_mem_iff _ _).2 (hhalf ▸ hin))
lemma nH_ne_zero_of_Gm {j : Fin r} (hne : (Gm N h (cV P) j).Nonempty) : nH (N j) ≠ 0 := by
  obtain ⟨y', hyS, hneg, hin, -⟩ := hne
  intro hz
  obtain ⟨y₀, hy₀⟩ := hF.nonempty
  have h0 : cH N h y₀ (-(1 / 2)) := (hF.pt_mem_iff _ _).1 ((hF.bot_iff y₀).2 hy₀)
  have hc : bd N h j y' = h j / nV (N j) := by simp [bd, hz]
  have hge : -(1 / 2) ≤ bd N h j y' := by
    have := hF.height_le _ ((hF.pt_mem_iff _ _).2 hin)
    rw [nV_pt] at this
    exact (abs_le.1 this).1
  have hle : bd N h j y' ≤ -(1 / 2) := by
    rw [hc, div_le_iff_of_neg hneg]
    have := h0 j
    rw [hz, zero_dotProduct] at this
    linarith
  have hhalf : bd N h j y' = -(1 / 2) := le_antisymm hle hge
  exact hyS ((hF.bot_iff y').1 ((hF.pt_mem_iff _ _).2 (hhalf ▸ hin)))
lemma prism_subset : productSet (cV P) cx ⊆ P := by
  intro y hy
  have hy' : pt (nH y) (nV y) ∈ productSet (cV P) cx := by rwa [pt_nH_nV]
  rw [cT] at hy'
  rw [← pt_nH_nV y]
  exact hF.prism _ hy'.1 _ hy'.2
lemma fiber_identity {t : ℝ} (ht : t ≠ 0) (y' : Fin k → ℝ) : ((π * t : ℝ) : ℂ) * ∫ s in {s | pt y' s ∈ P \ productSet (cV P) cx}, Complex.exp (2 * π * Complex.I * (t * s)) = (1 / (2 * Complex.I)) * (∑ j, (Gp N h (cV P) j).indicator (fun y' => Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y' - ∑ j, (Gm N h (cV P) j).indicator (fun y' => Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y') := by
  classical
  by_cases hyS : y' ∈ cV P
  · have hempty : {s | pt y' s ∈ P \ productSet (cV P) cx} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun s hs => ?_
      obtain ⟨hsP, hsn⟩ := hs
      apply hsn
      rw [cT]
      refine ⟨hyS, ?_⟩
      have := hF.height_le _ hsP
      rw [nV_pt] at this
      exact abs_le.1 this
    have hp : ∀ j, (Gp N h (cV P) j).indicator
        (fun y' => Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y' = 0 :=
      fun j => Set.indicator_of_notMem (fun hj => hj.1 hyS) _
    have hm : ∀ j, (Gm N h (cV P) j).indicator
        (fun y' => Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y' = 0 :=
      fun j => Set.indicator_of_notMem (fun hj => hj.1 hyS) _
    simp only [hempty, hp, hm, Measure.restrict_empty, integral_zero_measure, mul_zero, Finset.sum_const_zero, sub_zero]
  · by_cases hfib : ∃ s₀, cH N h y' s₀
    · obtain ⟨s₀, hs₀⟩ := hfib
      obtain ⟨jp, hjp⟩ := cQ hyS hs₀ hF.exists_pos
      obtain ⟨jm, hjm⟩ := cR hyS hs₀ hF.exists_neg
      have hR : {s | pt y' s ∈ P \ productSet (cV P) cx} =
          Set.Icc (bd N h jm y') (bd N h jp y') := by
        rw [← cS hjp hjm]
        ext s
        simp only [Set.mem_sdiff, cT, hF.pt_mem_iff, Set.mem_ofPred_eq]
        tauto
      have hab : bd N h jm y' ≤ bd N h jp y' :=
        (cH.bd_le hs₀ hjm.2.1).trans (cH.le_bd hs₀ hjp.2.1)
      have hsp : ∑ j, (Gp N h (cV P) j).indicator
          (fun y' => Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y' =
            Complex.exp (2 * π * Complex.I * (t * bd N h jp y')) := by
        rw [Finset.sum_eq_single jp]
        · exact Set.indicator_of_mem hjp _
        · intro j _ hj
          exact Set.indicator_of_notMem (fun hmem => hj (cO hmem hjp)) _
        · intro hj
          exact absurd (Finset.mem_univ jp) hj
      have hsm : ∑ j, (Gm N h (cV P) j).indicator
          (fun y' => Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y' =
            Complex.exp (2 * π * Complex.I * (t * bd N h jm y')) := by
        rw [Finset.sum_eq_single jm]
        · exact Set.indicator_of_mem hjm _
        · intro j _ hj
          exact Set.indicator_of_notMem (fun hmem => hj (cP hmem hjm)) _
        · intro hj
          exact absurd (Finset.mem_univ jm) hj
      rw [hR, cz ht hab, hsp, hsm]
      have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      have hπc : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    · have hempty : {s | pt y' s ∈ P \ productSet (cV P) cx} = ∅ :=
        Set.eq_empty_of_forall_notMem fun s hs => hfib ⟨s, (hF.pt_mem_iff _ _).1 hs.1⟩
      have hp : ∀ j, (Gp N h (cV P) j).indicator
          (fun y' => Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y' = 0 :=
        fun j => Set.indicator_of_notMem (fun hj => hfib ⟨_, hj.2.2.1⟩) _
      have hm : ∀ j, (Gm N h (cV P) j).indicator
          (fun y' => Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y' = 0 :=
        fun j => Set.indicator_of_notMem (fun hj => hfib ⟨_, hj.2.2.1⟩) _
      simp only [hempty, hp, hm, Measure.restrict_empty, integral_zero_measure, mul_zero, Finset.sum_const_zero, sub_zero]
omit hF in
lemma cY {G : Set (Fin k → ℝ)} (hGm : MeasurableSet G) (hGb : Bornology.IsBounded G) (η : Fin k → ℝ) (j : Fin r) (t : ℝ) : Integrable (G.indicator fun y' => exponentialCharacter η y' * Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) := by
  rw [integrable_indicator_iff hGm]
  have hcont : Continuous fun y' : Fin k → ℝ => exponentialCharacter η y' *
      Complex.exp (2 * π * Complex.I * (t * bd N h j y')) := by
    refine (continuous_exponentialCharacter η).mul (Complex.continuous_exp.comp ?_)
    refine continuous_const.mul (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact (continuous_const.sub (continuous_dotProduct_left _)).div_const _
  exact (hcont.continuousOn.integrableOn_compact hGb.isCompact_closure).mono_set subset_closure
lemma integrated_identity {t : ℝ} (ht : t ≠ 0) (η : Fin k → ℝ) : ((π * t : ℝ) : ℂ) * aa (P \ productSet (cV P) cx) (pt η t) = (1 / (2 * Complex.I)) * (∑ j, Complex.exp (((2 * π * (t * (h j / nV (N j))) : ℝ) : ℂ) * Complex.I) * aa (Gp N h (cV P) j) (η - (t / nV (N j)) • nH (N j)) - ∑ j, Complex.exp (((2 * π * (t * (h j / nV (N j))) : ℝ) : ℂ) * Complex.I) * aa (Gm N h (cV P) j) (η - (t / nV (N j)) • nH (N j))) := by
  have hRm : MeasurableSet (P \ productSet (cV P) cx) :=
    hF.measurableSet.diff (measurableSet_productSet hF.measurableSet_topSlice cy)
  have hRb : Bornology.IsBounded (P \ productSet (cV P) cx) :=
    hF.bounded.subset Set.sdiff_subset
  rw [cG hRm hRb, ← integral_const_mul]
  set gp : Fin r → (Fin k → ℝ) → ℂ := fun j => (Gp N h (cV P) j).indicator fun y' =>
    exponentialCharacter η y' * Complex.exp (2 * π * Complex.I * (t * bd N h j y')) with hgp
  set gm : Fin r → (Fin k → ℝ) → ℂ := fun j => (Gm N h (cV P) j).indicator fun y' =>
    exponentialCharacter η y' * Complex.exp (2 * π * Complex.I * (t * bd N h j y')) with hgm
  have hpt : ∀ y', ((π * t : ℝ) : ℂ) * (exponentialCharacter η y' *
      ∫ s in {s | pt y' s ∈ P \ productSet (cV P) cx},
        Complex.exp (2 * π * Complex.I * (t * s))) =
      (1 / (2 * Complex.I)) * (∑ j, gp j y' - ∑ j, gm j y') := by
    intro y'
    rw [mul_left_comm, hF.fiber_identity ht y', mul_left_comm, mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 2
    · exact Finset.sum_congr rfl fun j _ => (Set.indicator_mul_right _ _ _).symm
    · exact Finset.sum_congr rfl fun j _ => (Set.indicator_mul_right _ _ _).symm
  have za : ∀ j, Integrable (gp j) := fun j =>
    cY (cJ hF.measurableSet_topSlice j) (hF.isBounded_Gp j) η j t
  have zb : ∀ j, Integrable (gm j) := fun j =>
    cY (cK hF.measurableSet_topSlice j) (hF.isBounded_Gm j) η j t
  have zc : ∀ (G : Set (Fin k → ℝ)), MeasurableSet G → ∀ j,
      ∫ y', G.indicator (fun y' => exponentialCharacter η y' *
        Complex.exp (2 * π * Complex.I * (t * bd N h j y'))) y' =
      Complex.exp (((2 * π * (t * (h j / nV (N j))) : ℝ) : ℂ) * Complex.I) *
        aa G (η - (t / nV (N j)) • nH (N j)) := by
    intro G hGm j
    rw [integral_indicator hGm, aa, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y' => cW η y' j t)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul,
    integral_sub (integrable_finsetSum _ fun j _ => za j)
      (integrable_finsetSum _ fun j _ => zb j),
    integral_finsetSum _ fun j _ => za j, integral_finsetSum _ fun j _ => zb j]
  congr 2
  · exact Finset.sum_congr rfl fun j _ =>
      zc _ (cJ hF.measurableSet_topSlice j) j
  · exact Finset.sum_congr rfl fun j _ =>
      zc _ (cK hF.measurableSet_topSlice j) j
omit hF in
lemma cZ {G : Set (Fin k → ℝ)} (hGm : MeasurableSet G) (j : Fin r) (hGne : G.Nonempty → nH (N j) ≠ 0 ∧ nV (N j) ≠ 0) (ζ : Fin k → ℝ) : Tendsto (fun q : (Fin k → ℝ) × ℝ => Complex.exp (((2 * π * (q.2 * (h j / nV (N j))) : ℝ) : ℂ) * Complex.I) * aa G (q.1 - (q.2 / nV (N j)) • nH (N j))) (𝓝 ζ ×ˢ atTop) (𝓝 0) := by
  rcases G.eq_empty_or_nonempty with hG | hG
  · simp [hG, aa]
  · obtain ⟨hn, hv⟩ := hGne hG
    have h0 := (cE hGm).comp (cX hn hv ζ)
    refine squeeze_zero_norm (fun q => ?_) (by simpa using h0.norm)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
lemma tendsto_facet (ζ : Fin k → ℝ) : Tendsto (fun q : (Fin k → ℝ) × ℝ => ((π * q.2 : ℝ) : ℂ) * aa P (pt q.1 q.2) - (Real.sin (π * q.2) : ℂ) * aa (cV P) q.1) (𝓝 ζ ×ˢ atTop) (𝓝 0) := by
  have za : ∀ ξ : Fin (k + 1) → ℝ, IntegrableOn (exponentialCharacter ξ) P :=
    fun ξ => (continuous_exponentialCharacter ξ).continuousOn.integrableOn_compact
      (Metric.isCompact_of_isClosed_isBounded hF.isClosed hF.bounded)
  have hdecomp : ∀ q : (Fin k → ℝ) × ℝ, ((π * q.2 : ℝ) : ℂ) * aa P (pt q.1 q.2) -
      (Real.sin (π * q.2) : ℂ) * aa (cV P) q.1 =
      ((π * q.2 : ℝ) : ℂ) * aa (P \ productSet (cV P) cx) (pt q.1 q.2) := by
    intro q
    have hsub : aa (P \ productSet (cV P) cx) (pt q.1 q.2) =
        aa P (pt q.1 q.2) - aa (productSet (cV P) cx) (pt q.1 q.2) :=
      setIntegral_sdiff (measurableSet_productSet hF.measurableSet_topSlice cy)
        (za _) hF.prism_subset
    have zb : aa (productSet (cV P) cx) (pt q.1 q.2) =
        aa (cV P) q.1 * aa cx (fun _ => q.2) :=
      as _ _ _ _
    rw [hsub, zb]
    linear_combination (aa (cV P) q.1) * cA q.2
  have hev : ∀ᶠ q : (Fin k → ℝ) × ℝ in 𝓝 ζ ×ˢ atTop, q.2 ≠ 0 :=
    (tendsto_snd.eventually (eventually_gt_atTop 0)).mono fun q hq => hq.ne'
  have hp : ∀ j, Tendsto (fun q : (Fin k → ℝ) × ℝ =>
      Complex.exp (((2 * π * (q.2 * (h j / nV (N j))) : ℝ) : ℂ) * Complex.I) *
        aa (Gp N h (cV P) j) (q.1 - (q.2 / nV (N j)) • nH (N j))) (𝓝 ζ ×ˢ atTop)
      (𝓝 0) := fun j =>
    cZ (cJ hF.measurableSet_topSlice j) j
      (fun hne => ⟨hF.nH_ne_zero_of_Gp hne, (hne.some_mem.2.1).ne'⟩) ζ
  have hm : ∀ j, Tendsto (fun q : (Fin k → ℝ) × ℝ =>
      Complex.exp (((2 * π * (q.2 * (h j / nV (N j))) : ℝ) : ℂ) * Complex.I) *
        aa (Gm N h (cV P) j) (q.1 - (q.2 / nV (N j)) • nH (N j))) (𝓝 ζ ×ˢ atTop)
      (𝓝 0) := fun j =>
    cZ (cK hF.measurableSet_topSlice j) j
      (fun hne => ⟨hF.nH_ne_zero_of_Gm hne, (hne.some_mem.2.1).ne⟩) ζ
  have hsum := ((tendsto_finsetSum Finset.univ fun j _ => hp j).sub
    (tendsto_finsetSum Finset.univ fun j _ => hm j)).const_mul (1 / (2 * Complex.I))
  simp only [Finset.sum_const_zero, sub_zero, mul_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [hev] with q hq
  rw [hdecomp q, hF.integrated_identity hq q.1]
end FacetData
end Limit
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Real
namespace FCBridge
section Transfer
variable {n k r : ℕ}
lemma nH_pt (y' : Fin k → ℝ) (s : ℝ) : nH (pt y' s) = y' := by
  funext i; simp [nH, pt]
lemma continuous_nH : Continuous (nH : (Fin (k + 1) → ℝ) → Fin k → ℝ) :=
  continuous_pi fun _ => continuous_apply _
lemma continuous_nV : Continuous (nV : (Fin (k + 1) → ℝ) → ℝ) := continuous_apply _
lemma c4 (y : Fin (k + 1) → ℝ) (s : ℝ) : y + s • pt (0 : Fin k → ℝ) 1 = pt (nH y) (nV y + s) := by
  funext i
  refine Fin.addCases
    (motive := fun i => (y + s • pt (0 : Fin k → ℝ) 1 : Fin (k + 1) → ℝ) i =
      pt (nH y) (nV y + s) i)
    (fun i₁ => ?_) (fun i₂ => ?_) i
  · simp [pt, nH]
  · rw [Fin.fin_one_eq_zero i₂]; simp [pt, nV]
def c5 (L : (Fin n → ℝ) →L[ℝ] (Fin (k + 1) → ℝ)) : (Fin n → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + 1) => ℝ) (Fin.natAdd k 0)).comp L
lemma c6 (L : (Fin n → ℝ) →L[ℝ] (Fin (k + 1) → ℝ)) (ξ : Fin n → ℝ) :
    c5 L ξ = nV (L ξ) := rfl
variable {N : Fin r → Fin (k + 1) → ℝ} {h : Fin r → ℝ} {S : Set (Fin (k + 1) → ℝ)}
lemma c7 (hF : FacetData N h S) (L : (Fin n → ℝ) →L[ℝ] (Fin (k + 1) → ℝ)) (w : Fin n → ℝ) (hw : L w = pt 0 1) (c : ℂ) (ζ : Fin n → ℝ) : Tendsto (fun p : (Fin n → ℝ) × ℝ => ((π * c5 L (p.1 + p.2 • w) : ℝ) : ℂ) * (c * aa S (L (p.1 + p.2 • w))) - (Real.sin (π * c5 L (p.1 + p.2 • w)) : ℂ) * (c * aa (cV S) (nH (L (p.1 + p.2 • w))))) (𝓝 ζ ×ˢ atTop) (𝓝 0) := by
  have hL : ∀ p : (Fin n → ℝ) × ℝ,
      L (p.1 + p.2 • w) = pt (nH (L p.1)) (nV (L p.1) + p.2) := fun p => by
    rw [map_add, map_smul, hw, c4]
  have hg : Tendsto (fun p : (Fin n → ℝ) × ℝ => (nH (L p.1), nV (L p.1) + p.2))
      (𝓝 ζ ×ˢ atTop) (𝓝 (nH (L ζ)) ×ˢ atTop) :=
    (((continuous_nH.comp L.continuous).tendsto ζ).comp tendsto_fst).prodMk
      ((((continuous_nV.comp L.continuous).tendsto ζ).comp tendsto_fst).add_atTop tendsto_snd)
  have za := ((hF.tendsto_facet (nH (L ζ))).comp hg).const_mul c
  rw [mul_zero] at za
  refine za.congr fun p => ?_
  simp only [Function.comp, c6, hL, nV_pt, nH_pt]
  ring
lemma c8 {m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)}
    (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
    {Λ : Set (Fin (n + m) → ℝ)} (hΛ : spectralPair (productSet A B) Λ)
    (hF : FacetData N h S) (L : (Fin n → ℝ) →L[ℝ] (Fin (k + 1) → ℝ))
    (w : Fin n → ℝ) (hw : L w = pt 0 1) (c : ℂ)
    (Q : Set (Fin (n + m) → ℝ)) (hQ : IsClosed Q)
    (hQW : ∀ t, ∀ k : ℕ, t + (k : ℝ) • cu (m := m) w ∈ Q → t ∈ Q)
    (hcond : ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' →
      l' - l ∈ Q ∨ c * aa S (L (proj₁ (l' - l))) = 0 ∨ aa B (proj₂ (l' - l)) = 0) :
    ∃ Λ', spectralPair (productSet A B) Λ' ∧
      (∀ C : Set (Fin (n + m) → ℝ), IsClosed C →
        (∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → l' - l ∈ C) →
          ∀ l ∈ Λ', ∀ l' ∈ Λ', l ≠ l' → l' - l ∈ C) ∧
      ∀ l ∈ Λ', ∀ l' ∈ Λ', l ≠ l' →
        l' - l ∈ Q ∨ (∃ k : ℤ, nV (L (proj₁ (l' - l))) = k) ∨
          c * aa (cV S) (nH (L (proj₁ (l' - l)))) = 0 ∨
            aa B (proj₂ (l' - l)) = 0 := by
  have hρw : c5 L w = 1 := by rw [c6, hw, nV_pt]
  have hΨ : Continuous fun ξ => c * aa (cV S) (nH (L ξ)) :=
    continuous_const.mul ((aG hF.isBounded_topSlice.measure_lt_top.ne).comp
      (continuous_nH.comp L.continuous))
  have hΨw : ∀ ξ (s : ℝ), c * aa (cV S) (nH (L (ξ + s • w))) =
      c * aa (cV S) (nH (L ξ)) := fun ξ s => by
    rw [map_add, map_smul, hw, c4, nH_pt]
  exact cw hAm hAb hBm hBb hΛ w (c5 L) hρw
    (fun ξ => c * aa S (L ξ)) (fun ξ => c * aa (cV S) (nH (L ξ))) hΨ hΨw
    (c7 hF L w hw c) Q hQ hQW hcond
end Transfer
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Real Matrix
open GraphicVoronoiPrototype FCBridge
namespace ZonotopeFacets
lemma c9 {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det) (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) : aa Ω ξ = ((|T.det| : ℝ) : ℂ) * aa (affEquiv T hT 0 ⁻¹' Ω) (Tᵀ *ᵥ ξ) := by
  rw [ay]
  have h1 : exponentialCharacter (-ξ) 0 = 1 := by simp [exponentialCharacter]
  have hd : |T.det| ≠ 0 := abs_ne_zero.2 hT.ne_zero
  rw [h1, one_mul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hd, Complex.ofReal_one, one_mul]
noncomputable def da {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)
lemma db {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (ξ : Fin d → ℝ) :
    da M ξ = M *ᵥ ξ := rfl
lemma dc {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : IsUnit T.det)
    (v : Fin d → ℝ) : ∃ w, Tᵀ *ᵥ w = v :=
  ⟨(Tᵀ)⁻¹ *ᵥ v, by
    rw [mulVec_mulVec, mul_nonsing_inv _ (by rwa [det_transpose]), one_mulVec]⟩
lemma dd (a b : ℝ) : nV ![a, b] = b := rfl
lemma de (a b : ℝ) : nH ![a, b] = fun _ => a := by
  funext i; fin_cases i; rfl
lemma pt_eq_vec2 (u : Fin 1 → ℝ) (s : ℝ) : pt u s = ![u 0, s] := by
  funext i; fin_cases i <;> rfl
lemma df : volume cx = 1 := by
  have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume :=
    volume_preserving_funUnique (Fin 1) ℝ
  have : cx = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Icc (-(1 / 2 : ℝ)) (1 / 2) := rfl
  rw [this, hmp.measure_preimage_equiv, Real.volume_Icc]
  norm_num
lemma dg (v : ℝ) : aa cx (fun _ => v) = 0 ↔ v ≠ 0 ∧ ca v := by
  have hmul := cA v
  constructor
  · intro h0
    have hv : v ≠ 0 := by
      rintro rfl
      have h1 : aa cx (fun _ => (0 : ℝ)) = 1 := by
        rw [show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl, aj, measureReal_def, df]
        simp
      rw [h1] at h0
      exact one_ne_zero h0
    refine ⟨hv, ?_⟩
    rw [h0, mul_zero] at hmul
    have hs : Real.sin (π * v) = 0 := by exact_mod_cast hmul.symm
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
    exact ⟨n, mul_left_cancel₀ Real.pi_ne_zero (by rw [← hn]; ring)⟩
  · rintro ⟨hv, n, rfl⟩
    have hs : Real.sin (π * n) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi n
    rw [hs, Complex.ofReal_zero] at hmul
    have hne : ((π * n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero Real.pi_ne_zero hv
    exact (mul_eq_zero.1 hmul).resolve_left hne
lemma dh {n m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)} {Λ : Set (Fin (n + m) → ℝ)} (hΛ : spectralPair (productSet A B) Λ) : ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → aa A (proj₁ (l' - l)) = 0 ∨ aa B (proj₂ (l' - l)) = 0 := by
  obtain ⟨-, -, -, horth, -⟩ := al.1 hΛ
  intro l hl l' hl' hne
  have h := horth l hl l' hl' hne
  have hz : l' - l = Fin.append (proj₁ (l' - l)) (proj₂ (l' - l)) :=
    Fin.append_castAdd_natAdd.symm
  rw [hz, as] at h
  exact mul_eq_zero.1 h
lemma di : IsClosed {x : ℝ | ca x} := by
  have : {x : ℝ | ca x} = Set.range ((↑) : ℤ → ℝ) := by
    ext x; simp [ca, eq_comm]
  rw [this]
  exact Int.isClosedEmbedding_coe_real.isClosed_range
lemma dj : IsClosed {x : ℝ | ca x ∧ x ≠ 0} := by
  have : {x : ℝ | ca x ∧ x ≠ 0} = ((↑) : ℤ → ℝ) '' {n | n ≠ 0} := by
    ext x
    constructor
    · rintro ⟨⟨n, rfl⟩, hx⟩
      exact ⟨n, by exact_mod_cast hx, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, rfl⟩, by exact_mod_cast hn⟩
  rw [this]
  exact Int.isClosedEmbedding_coe_real.isClosedMap _ (isClosed_discrete _)
end ZonotopeFacets
end
section
open MeasureTheory Filter Topology Metric Real
open FCBridge
namespace ProductInterval
def ivl (a b : ℝ) : Set (Fin 1 → ℝ) := {x | x 0 ∈ Set.Icc a b}
lemma measurableSet_ivl (a b : ℝ) : MeasurableSet (ivl a b) :=
  measurableSet_Icc.preimage (measurable_pi_apply 0)
lemma dk (a b : ℝ) : volume (ivl a b) = ENNReal.ofReal (b - a) := by
  have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume :=
    volume_preserving_funUnique (Fin 1) ℝ
  have : ivl a b = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Icc a b := rfl
  rw [this, hmp.measure_preimage_equiv, Real.volume_Icc]
lemma norm_fin_one (x : Fin 1 → ℝ) : ‖x‖ = |x 0| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun i => ?_) ?_
  · rw [Fin.fin_one_eq_zero i, Real.norm_eq_abs]
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm x 0
lemma isBounded_ivl (a b : ℝ) : Bornology.IsBounded (ivl a b) := by
  refine (isBounded_closedBall (x := (0 : Fin 1 → ℝ)) (r := |a| + |b|)).subset fun x hx => ?_
  rw [mem_closedBall_zero_iff, norm_fin_one, abs_le]
  obtain ⟨h1, h2⟩ := hx
  constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith
lemma dl {a b t : ℝ} (hab : a ≤ b) (ht : t ≠ 0) : aa (ivl a b) (fun _ => t) = (Complex.exp (2 * π * Complex.I * (t * b)) - Complex.exp (2 * π * Complex.I * (t * a))) / (2 * π * Complex.I * t) := by
  let e := MeasurableEquiv.funUnique (Fin 1) ℝ
  have hmp : MeasurePreserving e volume volume := volume_preserving_funUnique (Fin 1) ℝ
  have hset : ivl a b = e ⁻¹' Set.Icc a b := rfl
  let g : ℝ → ℂ := fun s => Complex.exp (2 * π * Complex.I * (t * s))
  have hchar : ∀ x : Fin 1 → ℝ, exponentialCharacter (fun _ => t) x = g (e x) := by
    intro x
    simp only [exponentialCharacter, Fin.sum_univ_one, g]
    push_cast
    rfl
  have hft : aa (ivl a b) (fun _ => t) = ∫ s in Set.Icc a b, g s := by
    unfold aa
    rw [← hmp.setIntegral_preimage_emb e.measurableEmbedding g, ← hset]
    exact setIntegral_congr_fun (measurableSet_ivl a b) fun x _ => hchar x
  rw [hft]
  exact cz ht hab
lemma dm {a b t : ℝ} (hab : a < b) (h : aa (ivl a b) (fun _ => t) = 0) : 1 ≤ |t| * (b - a) := by
  have ht : t ≠ 0 := by
    rintro rfl
    rw [show (fun _ : Fin 1 => (0 : ℝ)) = 0 from rfl, aj, measureReal_def, dk, ENNReal.toReal_ofReal (by linarith)] at h
    have : (b - a : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.2 hab).ne'
    exact this (by exact_mod_cast h)
  rw [dl hab.le ht] at h
  have hden : (2 * π * Complex.I * t : ℂ) ≠ 0 := by
    have : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp_all
  have hnum := (div_eq_zero_iff.1 h).resolve_right hden
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 (sub_eq_zero.1 hnum)
  have h2 : (2 * π * Complex.I : ℂ) * ((t * (b - a) : ℝ) - n) = 0 := by
    push_cast
    linear_combination hn
  have h2π : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp_all
  have h3 : t * (b - a) = n := by
    have := (mul_eq_zero.1 h2).resolve_left h2π
    exact_mod_cast sub_eq_zero.1 this
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : t * (b - a) = 0 := by exact_mod_cast h3
    exact (mul_ne_zero ht (sub_pos.2 hab).ne') this
  have h4 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
  rw [← h3, abs_mul, abs_of_pos (sub_pos.2 hab)] at h4
  exact h4
lemma isSpectral_right_of_ivl {m : ℕ} {a b : ℝ} (hab : a < b) {B : Set (Fin m → ℝ)} (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B) (hspec : isSpectral (productSet (ivl a b) B)) : isSpectral B := by
  obtain ⟨Λ, hΛ⟩ := hspec
  have hba : 0 < b - a := sub_pos.2 hab
  let W : Set (Fin 1 → ℝ) := {w | |w 0| < 1 / (2 * (b - a))}
  have hW : W = (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
      Set.Ioo (-(1 / (2 * (b - a)))) (1 / (2 * (b - a))) := by
    ext w
    simp only [W, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioo, abs_lt]
    rfl
  refine bq (measurableSet_ivl a b) (isBounded_ivl a b) hBm hBb hΛ (W := W)
    ?_ ?_ ?_
  · rw [hW]
    exact measurableSet_Ioo.preimage (MeasurableEquiv.funUnique (Fin 1) ℝ).measurable
  · have hmp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ) volume volume :=
      volume_preserving_funUnique (Fin 1) ℝ
    rw [hW, hmp.measure_preimage_equiv, Real.volume_Ioo, dk, ← ENNReal.ofReal_inv_of_pos hba]
    apply le_of_eq
    congr 1
    field_simp
    ring
  · intro l hl l' hl' hne
    rcases ZonotopeFacets.dh hΛ l hl l' hl' hne with h0 | h0
    · left
      have hfun : proj₁ (l' - l) = fun _ => proj₁ (l' - l) 0 := by
        funext i; rw [Fin.fin_one_eq_zero i]
      rw [hfun] at h0
      have key := dm hab h0
      have hempty : {x : Fin 1 → ℝ | proj₁ l - x ∈ W ∧ proj₁ l' - x ∈ W} = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x hx => ?_
        obtain ⟨h1, h2⟩ := hx
        have h1' : |proj₁ l 0 - x 0| < 1 / (2 * (b - a)) := h1
        have h2' : |proj₁ l' 0 - x 0| < 1 / (2 * (b - a)) := h2
        have hsub : proj₁ (l' - l) 0 = (proj₁ l' 0 - x 0) - (proj₁ l 0 - x 0) := by
          rw [proj₁_sub]; simp
        have habs : |proj₁ (l' - l) 0| < 1 / (b - a) := by
          rw [hsub]
          calc |(proj₁ l' 0 - x 0) - (proj₁ l 0 - x 0)|
              ≤ |proj₁ l' 0 - x 0| + |proj₁ l 0 - x 0| := abs_sub _ _
            _ < 1 / (2 * (b - a)) + 1 / (2 * (b - a)) := add_lt_add h2' h1'
            _ = 1 / (b - a) := by field_simp; ring
        have : |proj₁ (l' - l) 0| * (b - a) < 1 := by
          rwa [lt_div_iff₀ hba] at habs
        linarith
      rw [hempty, measure_empty]
    · right
      rwa [← proj₂_sub]
end ProductInterval
end
section
open MeasureTheory Filter Topology Metric Real Matrix Pointwise
open GraphicVoronoiPrototype FCBridge
namespace Hexagon
def k3Src (e : Fin 3) : Fin 3 := ![0, 0, 1] e
def k3Dst (e : Fin 3) : Fin 3 := ![1, 2, 2] e
def k3Point (c a : Fin 3 → ℝ) : Fin 2 → ℝ := ![c 0 * a 0 + c 1 * a 1, -(c 0 * a 0) + c 2 * a 2]
def k3Zonotope (c : Fin 3 → ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∃ a : Fin 3 → ℝ, (∀ e, |a e| ≤ 1 / 2) ∧ k3Point c a = x}
def dn (c : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c 0 + c 1, -(c 0); -(c 0), c 0 + c 2]
def dp (e : Fin 3) : Fin 2 → ℤ := ![![1, -1], ![1, 0], ![0, 1]] e
def dq (e : Fin 3) : Fin 2 → ℝ := zr (dp e)
def dr (c : Fin 3 → ℝ) (e : Fin 3) : Fin 2 → ℝ := c e • dq e
lemma ds (c a : Fin 3 → ℝ) (u : Fin 2 → ℝ) : u ⬝ᵥ k3Point c a = c 0 * a 0 * (u 0 - u 1) + c 1 * a 1 * u 0 + c 2 * a 2 * u 1 := by
  simp [dotProduct, Fin.sum_univ_two, k3Point]; ring
lemma dt (c : Fin 3 → ℝ) (y : Fin 2 → ℝ) : y ⬝ᵥ (dn c *ᵥ y) = c 0 * (y 0 - y 1) ^ 2 + c 1 * y 0 ^ 2 + c 2 * y 1 ^ 2 := by
  simp [dotProduct, mulVec, Fin.sum_univ_two, dn]; ring
lemma du (c : Fin 3 → ℝ) : (dn c)ᵀ = dn c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dn]
lemma dv (c : Fin 3 → ℝ) : (dn c).det = c 0 * c 1 + c 0 * c 2 + c 1 * c 2 := by
  rw [det_fin_two]; simp [dn]; ring
lemma dw {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) (h1 : 0 < c 1) (h2 : 0 < c 2) : (dn c).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> simp [dn, Matrix.conjTranspose_apply]
  · intro y hy
    rw [star_trivial, dt]
    by_contra hle
    rw [not_lt] at hle
    have ha := mul_nonneg (hc 0) (sq_nonneg (y 0 - y 1))
    have hb := mul_nonneg (hc 1) (sq_nonneg (y 0))
    have hd := mul_nonneg (hc 2) (sq_nonneg (y 1))
    have e1 : c 1 * y 0 ^ 2 = 0 := by linarith
    have e2 : c 2 * y 1 ^ 2 = 0 := by linarith
    have hy0 : y 0 = 0 := (pow_eq_zero_iff two_ne_zero).1 ((mul_eq_zero.1 e1).resolve_left h1.ne')
    have hy1 : y 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 ((mul_eq_zero.1 e2).resolve_left h2.ne')
    exact hy (funext fun i => by fin_cases i <;> simp [hy0, hy1])
lemma dx {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) {x : Fin 2 → ℝ} (hx : x ∈ k3Zonotope c) (z : Fin 2 → ℤ) : 2 * (x ⬝ᵥ zr z) ≤ zr z ⬝ᵥ (dn c *ᵥ zr z) := by
  obtain ⟨a, ha, rfl⟩ := hx
  rw [dotProduct_comm, ds, dt]
  have h := bu c a ![z 0 - z 1, z 0, z 1] hc ha
  simp [Fin.sum_univ_three, zr] at h ⊢
  linarith
lemma dy (c : Fin 3 → ℝ) : Convex ℝ (k3Zonotope c) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ s t hs ht hst
  refine ⟨fun e => s * a e + t * b e, fun e => ?_, ?_⟩
  · calc |s * a e + t * b e| ≤ |s * a e| + |t * b e| := abs_add_le _ _
      _ = s * |a e| + t * |b e| := by rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * (1 / 2) + t * (1 / 2) := by gcongr; exacts [ha e, hb e]
      _ = 1 / 2 := by rw [← add_mul, hst, one_mul]
  · funext i; fin_cases i <;> simp [k3Point] <;> ring
lemma dz (c : Fin 3 → ℝ) : k3Zonotope c = k3Point c '' Set.univ.pi (fun _ => Set.Icc (-(1 / 2)) (1 / 2)) := by
  ext x
  simp only [k3Zonotope, Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ_pi, Set.mem_Icc, abs_le]
lemma dA (c : Fin 3 → ℝ) : Continuous (k3Point c) := by
  unfold k3Point
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp <;> fun_prop
lemma dB (c : Fin 3 → ℝ) : IsCompact (k3Zonotope c) := by
  rw [dz]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (dA c)
lemma dC {c : Fin 3 → ℝ} (x : Fin 2 → ℝ) (hsupp : ∀ u : Fin 2 → ℝ, 2 * (u ⬝ᵥ x) ≤ c 0 * |u 0 - u 1| + c 1 * |u 0| + c 2 * |u 1|) : x ∈ k3Zonotope c := by
  by_contra hx
  obtain ⟨f, r, hfx, hfb⟩ := geometric_hahn_banach_point_closed (dy c)
    (dB c).isClosed hx
  let w : Fin 2 → ℝ := fun i => f fun j => if i = j then 1 else 0
  have hf : ∀ p : Fin 2 → ℝ, f p = ∑ i, p i * w i := by
    intro p
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) p
    simpa [w, smul_eq_mul] using this
  let u : Fin 2 → ℝ := fun i => -w i
  let tt : Fin 3 → ℝ := ![u 0 - u 1, u 0, u 1]
  let a : Fin 3 → ℝ := fun e => if 0 ≤ tt e then 1 / 2 else -(1 / 2)
  have ha : ∀ e, |a e| ≤ 1 / 2 := by
    intro e; by_cases h : 0 ≤ tt e <;> simp [a, h, abs_of_pos]
  have hb := hfb _ ⟨a, ha, rfl⟩
  have hae : ∀ e, 2 * (a e * tt e) = |tt e| := by
    intro e
    by_cases h : 0 ≤ tt e
    · simp only [a, if_pos h, abs_of_nonneg h]; ring
    · simp only [a, if_neg h, abs_of_neg (lt_of_not_ge h)]; ring
  have hub : 2 * (u ⬝ᵥ k3Point c a) = c 0 * |u 0 - u 1| + c 1 * |u 0| + c 2 * |u 1| := by
    rw [ds]
    have h0 := hae 0; have h1 := hae 1; have h2 := hae 2
    simp only [tt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    linear_combination c 0 * h0 + c 1 * h1 + c 2 * h2
  have hux := hsupp u
  rw [hf] at hfx hb
  have e1 : u ⬝ᵥ x = -∑ i, x i * w i := by
    simp [dotProduct, u, Fin.sum_univ_two]; ring
  have e2 : u ⬝ᵥ k3Point c a = -∑ i, k3Point c a i * w i := by
    simp [dotProduct, u, Fin.sum_univ_two]; ring
  linarith
def cutVec2 (S : Finset (Fin 3)) : Fin 2 → ℤ :=
  fun i => cutBit S (Fin.castSucc i) - cutBit S (Fin.last 2)
lemma dD (c : Fin 3 → ℝ) (S : Finset (Fin 3)) : zr (cutVec2 S) ⬝ᵥ (dn c *ᵥ zr (cutVec2 S)) = cutCapacity S k3Src k3Dst c := by
  rw [dt, ← bv]
  simp [Fin.sum_univ_three, zr, cutVec2, k3Src, k3Dst]
lemma dE {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) : bE (dn c) = k3Zonotope c := by
  ext x
  constructor
  · intro hx
    refine dC x fun u => ?_
    let y : Fin 3 → ℝ := ![x 0, x 1, -(x 0 + x 1)]
    have hy : ∑ v, y v = 0 := by simp [y, Fin.sum_univ_three]
    have hcut : ∀ S : Finset (Fin 3), 2 * ∑ v, y v * (cutBit S v : ℝ) ≤
        cutCapacity S k3Src k3Dst c := by
      intro S
      have h := hx (cutVec2 S)
      rw [dD] at h
      have : ∑ v, y v * (cutBit S v : ℝ) = x ⬝ᵥ zr (cutVec2 S) := by
        simp [y, Fin.sum_univ_three, dotProduct, Fin.sum_univ_two, zr, cutVec2]
        ring
      rw [this]; exact h
    have key := bx k3Src k3Dst c y hy hcut ![u 0, u 1, 0]
    have hl : ∑ v, y v * ![u 0, u 1, 0] v = u ⬝ᵥ x := by
      simp [y, Fin.sum_univ_three, dotProduct, Fin.sum_univ_two]; ring
    have hr : ∑ e, c e * |![u 0, u 1, 0] (k3Src e) - ![u 0, u 1, 0] (k3Dst e)| =
        c 0 * |u 0 - u 1| + c 1 * |u 0| + c 2 * |u 1| := by
      simp [Fin.sum_univ_three, k3Src, k3Dst]
    rw [hl, hr] at key
    exact key
  · intro hx z
    exact dx hc hx z
lemma dF {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) (h1 : 0 < c 1) (h2 : 0 < c 2) : volume (k3Zonotope c) = ENNReal.ofReal (c 0 * c 1 + c 0 * c 2 + c 1 * c 2) := by
  rw [← dE hc, bV (dw hc h1 h2), dv,
    abs_of_nonneg (by nlinarith [hc 0, hc 1, hc 2])]
def dG (c : Fin 3 → ℝ) : Set (Fin 2 → ℝ) := bF (dn c)⁻¹
lemma dH {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) (h1 : 0 < c 1) (h2 : 0 < c 2) : volume (dG c) = ENNReal.ofReal (c 0 * c 1 + c 0 * c 2 + c 1 * c 2)⁻¹ := by
  have hpd := dw hc h1 h2
  rw [dG, bW, bV hpd.inv, det_nonsing_inv, dv,
    Ring.inverse_eq_inv', abs_inv, abs_of_nonneg (by nlinarith [hc 0, hc 1, hc 2])]
lemma dI (c : Fin 3 → ℝ) (hc : ∀ e, 0 ≤ c e) (y : Fin 2 → ℝ) (e : Fin 3) : c e * (dq e ⬝ᵥ y) ^ 2 ≤ y ⬝ᵥ (dn c *ᵥ y) := by
  rw [dt]
  have ha := mul_nonneg (hc 0) (sq_nonneg (y 0 - y 1))
  have hb := mul_nonneg (hc 1) (sq_nonneg (y 0))
  have hd := mul_nonneg (hc 2) (sq_nonneg (y 1))
  fin_cases e <;> simp [dq, dp, zr, dotProduct, Fin.sum_univ_two] <;> nlinarith
lemma dJ {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) (h1 : 0 < c 1) (h2 : 0 < c 2) {t : Fin 2 → ℝ} (ht : t ∈ (2 : ℝ) • dG c) (e : Fin 3) (hce : 0 < c e) : |t ⬝ᵥ dr c e| < 1 := by
  have hpd := dw hc h1 h2
  have hdet := bJ hpd
  set M := dn c
  set R := dq e ⬝ᵥ (M⁻¹ *ᵥ dq e) with hR
  have hne : dp e ≠ 0 := by
    fin_cases e <;> intro h <;> have := congrFun h 0 <;> have := congrFun h 1 <;>
      simp_all [dp]
  have hRpos : 0 < R := bI hpd.inv (bD hne)
  obtain ⟨y, hy, rfl⟩ := ht
  have za := hy (dp e) hne
  have zb := hy (-dp e) (neg_ne_zero.2 hne)
  rw [bC] at zb
  simp only [mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg] at zb
  have zc : zr (dp e) = dq e := rfl
  rw [zc] at za zb
  set v := M⁻¹ *ᵥ dq e with hv
  have hMv : M *ᵥ v = dq e := by rw [hv, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have zd := dI c hc v e
  have hRv : v ⬝ᵥ (M *ᵥ v) = R := by rw [hMv, dotProduct_comm]
  rw [hRv] at zd
  have hcR : c e * R ≤ 1 := by
    have : c e * R ^ 2 ≤ R := by rwa [show dq e ⬝ᵥ v = R from rfl] at zd
    nlinarith
  rw [dr, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos hce]
  have hlt : |(2 : ℝ) • y ⬝ᵥ dq e| < R := by
    rw [smul_dotProduct, smul_eq_mul, abs_lt]
    constructor <;> linarith
  calc c e * |(2 : ℝ) • y ⬝ᵥ dq e| < c e * R := mul_lt_mul_of_pos_left hlt hce
    _ ≤ 1 := hcR
def dK (τ g t : Fin 2 → ℝ) : Prop := ca (t ⬝ᵥ τ) ∨ (ca (t ⬝ᵥ g) ∧ t ⬝ᵥ g ≠ 0)
def dL (c : Fin 3 → ℝ) (t : Fin 2 → ℝ) : Prop :=
  t ≠ 0 ∧ dK (dn c *ᵥ zr ![1, 0]) (dr c 2) t ∧
    dK (dn c *ᵥ zr ![0, 1]) (dr c 1) t
lemma dM {x : ℝ} (hx : |x| < 1) : ¬ (ca x ∧ x ≠ 0) := by
  rintro ⟨⟨n, rfl⟩, hn⟩
  have hn' : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn'
  linarith
lemma dN {c : Fin 3 → ℝ} (hpos : ∀ e, 0 < c e) {t : Fin 2 → ℝ} (ht : t ∈ (2 : ℝ) • dG c) (hH : dL c t) : False := by
  have hc : ∀ e, 0 ≤ c e := fun e => (hpos e).le
  obtain ⟨ht0, hA, hB⟩ := hH
  have hA' := hA.resolve_right
    (dM (dJ hc (hpos 1) (hpos 2) ht 2 (hpos 2)))
  have hB' := hB.resolve_right
    (dM (dJ hc (hpos 1) (hpos 2) ht 1 (hpos 1)))
  have hpd := dw hc (hpos 1) (hpos 2)
  have hq : ∀ i, ca ((dn c *ᵥ t) i) := by
    intro i
    have hsym : ∀ z : Fin 2 → ℝ, t ⬝ᵥ (dn c *ᵥ z) = (dn c *ᵥ t) ⬝ᵥ z := by
      intro z; rw [bK (du c), dotProduct_comm]
    fin_cases i
    · obtain ⟨n, hn⟩ := hA'; refine ⟨n, ?_⟩
      rw [hsym] at hn; simpa [dotProduct, Fin.sum_univ_two, zr] using hn
    · obtain ⟨n, hn⟩ := hB'; refine ⟨n, ?_⟩
      rw [hsym] at hn; simpa [dotProduct, Fin.sum_univ_two, zr] using hn
  choose z hz using hq
  have hMt : dn c *ᵥ t = zr z := funext hz
  have htz : t = (dn c)⁻¹ *ᵥ zr z := by
    rw [← hMt, mulVec_mulVec, nonsing_inv_mul _ (bJ hpd), one_mulVec]
  rw [htz] at ht
  have hz0 := b9 ht
  exact ht0 (by rw [htz, hz0, bz, mulVec_zero])
end Hexagon
end
section
open MeasureTheory Filter Topology Metric Real Matrix Pointwise
open GraphicVoronoiPrototype FCBridge ZonotopeFacets
namespace Hexagon
lemma dO (c a b : Fin 3 → ℝ) : k3Point c (a - b) = k3Point c a - k3Point c b := by
  funext i; fin_cases i <;> simp [k3Point] <;> ring
lemma dP (c a : Fin 3 → ℝ) (r : ℝ) : k3Point c (r • a) = r • k3Point c a := by
  funext i; fin_cases i <;> simp [k3Point] <;> ring
lemma dQ {c : Fin 3 → ℝ} {x : Fin 2 → ℝ} (hx : x ∈ k3Zonotope c) : -x ∈ k3Zonotope c := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨(-1 : ℝ) • a, fun e => by simpa [abs_neg] using ha e, ?_⟩
  rw [dP, neg_one_smul]
def dR (z : Fin 2 → ℤ) : Fin 3 → ℝ := ![(z 0 : ℝ) - z 1, z 0, z 1]
lemma dS (c : Fin 3 → ℝ) (z : Fin 2 → ℤ) : dn c *ᵥ zr z = k3Point c (dR z) := by
  funext i; fin_cases i <;> simp [dn, mulVec, dotProduct, Fin.sum_univ_two, k3Point,
    dR, zr] <;> ring
lemma dT {c : Fin 3 → ℝ} (x : Fin 2 → ℝ) (hcut : ∀ S : Finset (Fin 3), 2 * (x ⬝ᵥ zr (cutVec2 S)) ≤ cutCapacity S k3Src k3Dst c) : x ∈ k3Zonotope c := by
  refine dC x fun u => ?_
  let y : Fin 3 → ℝ := ![x 0, x 1, -(x 0 + x 1)]
  have hy : ∑ v, y v = 0 := by simp [y, Fin.sum_univ_three]
  have hcut' : ∀ S : Finset (Fin 3), 2 * ∑ v, y v * (cutBit S v : ℝ) ≤
      cutCapacity S k3Src k3Dst c := by
    intro S
    have : ∑ v, y v * (cutBit S v : ℝ) = x ⬝ᵥ zr (cutVec2 S) := by
      simp [y, Fin.sum_univ_three, dotProduct, Fin.sum_univ_two, zr, cutVec2]
      ring
    rw [this]; exact hcut S
  have key := bx k3Src k3Dst c y hy hcut' ![u 0, u 1, 0]
  have hl : ∑ v, y v * ![u 0, u 1, 0] v = u ⬝ᵥ x := by
    simp [y, Fin.sum_univ_three, dotProduct, Fin.sum_univ_two]; ring
  have hr : ∑ e, c e * |![u 0, u 1, 0] (k3Src e) - ![u 0, u 1, 0] (k3Dst e)| =
      c 0 * |u 0 - u 1| + c 1 * |u 0| + c 2 * |u 1| := by
    simp [Fin.sum_univ_three, k3Src, k3Dst]
  rw [hl, hr] at key
  exact key
lemma mem_k3Zonotope_iff_cuts {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) (x : Fin 2 → ℝ) : x ∈ k3Zonotope c ↔ ∀ S : Finset (Fin 3), 2 * (x ⬝ᵥ zr (cutVec2 S)) ≤ cutCapacity S k3Src k3Dst c := by
  refine ⟨fun hx S => ?_, dT x⟩
  have := dx hc hx (cutVec2 S)
  rwa [dD] at this
lemma dU {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) (z : Fin 2 → ℤ) {x : Fin 2 → ℝ} (hx : x ∈ k3Zonotope c) (heq : 2 * (x ⬝ᵥ zr z) = zr z ⬝ᵥ (dn c *ᵥ zr z)) : dn c *ᵥ zr z - x ∈ k3Zonotope c := by
  obtain ⟨a, ha, rfl⟩ := hx
  have za : k3Point c a ⬝ᵥ zr z =
      c 0 * a 0 * dR z 0 + c 1 * a 1 * dR z 1 + c 2 * a 2 * dR z 2 := by
    rw [dotProduct_comm, ds]; simp [dR, zr]
  have zb : zr z ⬝ᵥ (dn c *ᵥ zr z) =
      c 0 * dR z 0 ^ 2 + c 1 * dR z 1 ^ 2 + c 2 * dR z 2 ^ 2 := by
    rw [dt]; simp [dR, zr]
  have hint : ∀ e, ∃ n : ℤ, dR z e = n := by
    intro e; fin_cases e
    · exact ⟨z 0 - z 1, by simp [dR]⟩
    · exact ⟨z 0, by simp [dR]⟩
    · exact ⟨z 1, by simp [dR]⟩
  have hterm : ∀ e, 0 ≤ c e * (dR z e ^ 2 - 2 * a e * dR z e) := by
    intro e
    refine mul_nonneg (hc e) ?_
    obtain ⟨n, hn⟩ := hint e
    have h1 : |dR z e| ≤ dR z e ^ 2 := by rw [hn]; exact br n
    have h3 : a e * dR z e ≤ |a e| * |dR z e| := by
      rw [← abs_mul]; exact le_abs_self _
    have h4 : |a e| * |dR z e| ≤ 1 / 2 * |dR z e| :=
      mul_le_mul_of_nonneg_right (ha e) (abs_nonneg _)
    linarith
  rw [za, zb] at heq
  have h0 := hterm 0; have h1 := hterm 1; have h2 := hterm 2
  have hz : ∀ e, c e * (dR z e ^ 2 - 2 * a e * dR z e) = 0 := by
    intro e; fin_cases e
    · simp only [Fin.zero_eta]; linarith
    · simp only [Fin.mk_one]; linarith
    · show c 2 * (dR z 2 ^ 2 - 2 * a 2 * dR z 2) = 0; linarith
  refine ⟨fun e => if c e = 0 then 0 else dR z e - a e, fun e => ?_, ?_⟩
  · by_cases hce : c e = 0
    · simp [hce]
    · simp only [hce, if_false]
      have hq : dR z e ^ 2 - 2 * a e * dR z e = 0 :=
        (mul_eq_zero.1 (hz e)).resolve_left hce
      by_cases hd : dR z e = 0
      · rw [hd, zero_sub, abs_neg]; exact ha e
      · have : dR z e = 2 * a e := by
          have h5 : dR z e * (dR z e - 2 * a e) = 0 := by linear_combination hq
          exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left hd)
        rw [this, show 2 * a e - a e = a e by ring]; exact ha e
  · rw [dS, ← dO]
    funext i
    fin_cases i <;> by_cases h0 : c 0 = 0 <;> by_cases h1 : c 1 = 0 <;> by_cases h2 : c 2 = 0 <;>
      simp [k3Point, h0, h1, h2]
def dV (u w : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => ![u, w] j i
lemma dW (u w : Fin 2 → ℝ) (y' : Fin 1 → ℝ) (s : ℝ) : dV u w *ᵥ pt y' s = y' 0 • u + s • w := by
  rw [pt_eq_vec2]
  funext i
  simp [dV, mulVec, dotProduct, Fin.sum_univ_two]
  ring
lemma dX (u w t : Fin 2 → ℝ) : (dV u w)ᵀ *ᵥ t = ![u ⬝ᵥ t, w ⬝ᵥ t] := by
  funext i
  fin_cases i <;> simp [dV, mulVec, dotProduct, Fin.sum_univ_two]
noncomputable def dY : Finset (Fin 3) ≃ Fin (Fintype.card (Finset (Fin 3))) :=
  Fintype.equivFin _
noncomputable def dZ (T : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin (Fintype.card (Finset (Fin 3)))) :
    Fin 2 → ℝ :=
  (2 : ℝ) • (Tᵀ *ᵥ zr (cutVec2 (dY.symm j)))
noncomputable def d0 (c : Fin 3 → ℝ) (j : Fin (Fintype.card (Finset (Fin 3)))) : ℝ :=
  cutCapacity (dY.symm j) k3Src k3Dst c
section FacetDataK3
variable {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) (z : Fin 2 → ℤ)
  (hz : ∀ e, |dR z e| ≤ 1) (hκ : 0 < zr z ⬝ᵥ (dn c *ᵥ zr z))
  {u : Fin 2 → ℝ} (hu : u ⬝ᵥ zr z = 0)
include hc hz hκ hu in
lemma d3 (hT : IsUnit (dV u (dn c *ᵥ zr z)).det) : FacetData (dZ (dV u (dn c *ᵥ zr z))) (d0 c) (affEquiv (dV u (dn c *ᵥ zr z)) hT 0 ⁻¹' k3Zonotope c) := by
  set τ := dn c *ᵥ zr z with hτ
  set κ := zr z ⬝ᵥ (dn c *ᵥ zr z) with hκdef
  set T := dV u τ with hTdef
  have hmem : ∀ y, y ∈ affEquiv T hT 0 ⁻¹' k3Zonotope c ↔ T *ᵥ y ∈ k3Zonotope c := fun y => by
    rw [Set.mem_preimage, affEquiv_apply, add_zero]
  have hτz : τ ⬝ᵥ zr z = κ := by rw [hτ, dotProduct_comm]
  have hdot : ∀ (y' : Fin 1 → ℝ) (s : ℝ), (T *ᵥ pt y' s) ⬝ᵥ zr z = s * κ := by
    intro y' s
    rw [hTdef, dW, add_dotProduct, smul_dotProduct, smul_dotProduct, hu, hτz]
    simp
  have hrefl : ∀ y' : Fin 1 → ℝ, T *ᵥ pt y' (1 / 2) ∈ k3Zonotope c →
      T *ᵥ pt (-y') (1 / 2) ∈ k3Zonotope c := by
    intro y' hy
    have heq : 2 * ((T *ᵥ pt y' (1 / 2)) ⬝ᵥ zr z) = κ := by rw [hdot]; ring
    have := dU hc z hy heq
    have hid : τ - T *ᵥ pt y' (1 / 2) = T *ᵥ pt (-y') (1 / 2) := by
      rw [hTdef, dW, dW]
      simp only [Pi.neg_apply, neg_smul]
      module
    rwa [← hτ, hid] at this
  have hneg : ∀ y' : Fin 1 → ℝ, T *ᵥ pt y' (-(1 / 2)) = -(T *ᵥ pt (-y') (1 / 2)) := by
    intro y'
    rw [hTdef, dW, dW]
    simp only [Pi.neg_apply, neg_smul]
    module
  refine ⟨fun y => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem, mem_k3Zonotope_iff_cuts hc, ← dY.symm.forall_congr_right]
    refine forall_congr' fun j => ?_
    have : dZ T j ⬝ᵥ y = 2 * ((T *ᵥ y) ⬝ᵥ zr (cutVec2 (dY.symm j))) := by
      rw [dZ, smul_dotProduct, smul_eq_mul, mulVec_transpose, ← dotProduct_mulVec, dotProduct_comm]
    rw [this, d0]
  · have hsub : affEquiv T hT 0 ⁻¹' k3Zonotope c ⊆ (fun x => T⁻¹ *ᵥ x) '' k3Zonotope c := by
      intro y hy
      refine ⟨T *ᵥ y, (hmem y).1 hy, ?_⟩
      simp only [mulVec_mulVec, nonsing_inv_mul T hT, one_mulVec]
    have hcont : Continuous fun x : Fin 2 → ℝ => T⁻¹ *ᵥ x :=
      (Matrix.mulVecLin T⁻¹).continuous_of_finiteDimensional
    exact ((dB c).image hcont).isBounded.subset hsub
  · intro y hy
    have hx := (hmem y).1 hy
    have hyp : y = pt (nH y) (nV y) := (pt_nH_nV y).symm
    have h1 := dx hc hx z
    have h2 := dx hc hx (-z)
    rw [bC, dotProduct_neg, mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg] at h2
    rw [hyp, hdot] at h1 h2
    rw [abs_le]
    constructor <;> nlinarith
  · intro y'
    rw [hmem, hmem]
    constructor
    · intro h
      have h' : T *ᵥ pt (-y') (1 / 2) ∈ k3Zonotope c := by
        have := dQ h
        rwa [hneg, neg_neg] at this
      simpa using hrefl (-y') h'
    · intro h
      rw [hneg]
      exact dQ (hrefl y' h)
  · refine ⟨0, (hmem _).2 ?_⟩
    refine ⟨(1 / 2 : ℝ) • dR z, fun e => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      nlinarith [hz e, abs_nonneg (dR z e)]
    · rw [dP, ← dS, hTdef, dW]
      simp [hτ]
  · intro y' hy' s hs
    have htop := (hmem _).1 hy'
    have za : T *ᵥ pt y' (-(1 / 2)) ∈ k3Zonotope c := by
      rw [hneg]; exact dQ (hrefl y' htop)
    rw [hmem]
    have hcomb := dy c htop za (by linarith [hs.1] : (0 : ℝ) ≤ 1 / 2 + s)
      (by linarith [hs.2] : (0 : ℝ) ≤ 1 / 2 - s) (by ring)
    have hid : (1 / 2 + s) • (T *ᵥ pt y' (1 / 2)) + (1 / 2 - s) • (T *ᵥ pt y' (-(1 / 2))) =
        T *ᵥ pt y' s := by
      rw [hTdef, dW, dW, dW]
      module
    rwa [hid] at hcomb
end FacetDataK3
section Step
variable {c : Fin 3 → ℝ} (hc : ∀ e, 0 ≤ c e) {m : ℕ} {B : Set (Fin m → ℝ)}
  (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
  {Λ : Set (Fin (2 + m) → ℝ)} (hΛ : spectralPair (productSet (k3Zonotope c) B) Λ)
  (z : Fin 2 → ℤ) (hz : ∀ e, |dR z e| ≤ 1)
  (hκ : 0 < zr z ⬝ᵥ (dn c *ᵥ zr z))
  {u : Fin 2 → ℝ} (hu : u ⬝ᵥ zr z = 0)
  (hT : IsUnit (dV u (dn c *ᵥ zr z)).det)
include hc hBm hBb hΛ hz hκ hu hT in
lemma d4 (hedge : ∀ a : ℝ, dV u (dn c *ᵥ zr z) *ᵥ ![a, 1 / 2] ∈ k3Zonotope c ↔ |a| ≤ 1 / 2) : ∃ Λ', spectralPair (productSet (k3Zonotope c) B) Λ' ∧ (∀ C : Set (Fin (2 + m) → ℝ), IsClosed C → (∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → l' - l ∈ C) → ∀ l ∈ Λ', ∀ l' ∈ Λ', l ≠ l' → l' - l ∈ C) ∧ ∀ l ∈ Λ', ∀ l' ∈ Λ', l ≠ l' → dK (dn c *ᵥ zr z) u (proj₁ (l' - l)) ∨ aa B (proj₂ (l' - l)) = 0 := by
  have hF := d3 hc z hz hκ hu hT
  set T := dV u (dn c *ᵥ zr z) with hTdef
  obtain ⟨w, hw⟩ := dc T hT (pt 0 1)
  have hL : da Tᵀ w = pt 0 1 := hw
  have hcond : ∀ l ∈ Λ, ∀ l' ∈ Λ, l ≠ l' → l' - l ∈ (∅ : Set (Fin (2 + m) → ℝ)) ∨
      ((|T.det| : ℝ) : ℂ) * aa (affEquiv T hT 0 ⁻¹' k3Zonotope c)
        (da Tᵀ (proj₁ (l' - l))) = 0 ∨ aa B (proj₂ (l' - l)) = 0 := by
    intro l hl l' hl' hne
    rcases dh hΛ l hl l' hl' hne with h | h
    · right; left
      rw [db, ← c9]
      exact h
    · right; right; exact h
  have hmeas : MeasurableSet (k3Zonotope c) := (dB c).isClosed.measurableSet
  obtain ⟨Λ', hΛ', hpres, hnew⟩ := c8 hmeas (dB c).isBounded hBm hBb
    hΛ hF (da Tᵀ) w hL (((|T.det| : ℝ) : ℂ)) ∅ isClosed_empty
    (fun _ _ h => absurd h (Set.notMem_empty _)) hcond
  have hsl : cV (affEquiv T hT 0 ⁻¹' k3Zonotope c) = cx := by
    ext u'
    show affEquiv T hT 0 (pt u' (1 / 2)) ∈ k3Zonotope c ↔ u' 0 ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
    rw [affEquiv_apply, add_zero, pt_eq_vec2, hedge, Set.mem_Icc, abs_le]
  have hdet : ((|T.det| : ℝ) : ℂ) ≠ 0 := by
    have : |T.det| ≠ 0 := abs_ne_zero.2 hT.ne_zero
    exact_mod_cast this
  refine ⟨Λ', hΛ', hpres, fun l hl l' hl' hne => ?_⟩
  have hTt : da Tᵀ (proj₁ (l' - l)) =
      ![u ⬝ᵥ proj₁ (l' - l), (dn c *ᵥ zr z) ⬝ᵥ proj₁ (l' - l)] := by
    rw [db, hTdef, dX]
  rcases hnew l hl l' hl' hne with h | h | h | h
  · exact absurd h (Set.notMem_empty _)
  · obtain ⟨k, hk⟩ := h
    rw [hTt, dd] at hk
    exact Or.inl (Or.inl ⟨k, by rw [dotProduct_comm]; exact hk⟩)
  · rw [hsl, hTt, de] at h
    have h' := (mul_eq_zero.1 h).resolve_left hdet
    rw [dg] at h'
    exact Or.inl (Or.inr ⟨by rw [dotProduct_comm]; exact h'.2, by rw [dotProduct_comm]; exact h'.1⟩)
  · exact Or.inr h
end Step
lemma d5 {m : ℕ} {B : Set (Fin m → ℝ)} (hB : volume B ≠ ⊤) (τ g : Fin 2 → ℝ) : IsClosed {Δ : Fin (2 + m) → ℝ | dK τ g (proj₁ Δ) ∨ aa B (proj₂ Δ) = 0} := by
  have hc1 : Continuous fun Δ : Fin (2 + m) → ℝ => proj₁ Δ ⬝ᵥ τ :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_proj₁).mul
      continuous_const
  have hc2 : Continuous fun Δ : Fin (2 + m) → ℝ => proj₁ Δ ⬝ᵥ g :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_proj₁).mul
      continuous_const
  have h1 := di.preimage hc1
  have h2 := dj.preimage hc2
  have h4 := (isClosed_singleton (x := (0 : ℂ))).preimage
    ((aG hB).comp (continuous_proj₂ (n := 2) (m := m)))
  have : {Δ : Fin (2 + m) → ℝ | dK τ g (proj₁ Δ) ∨ aa B (proj₂ Δ) = 0} =
      ((fun Δ : Fin (2 + m) → ℝ => proj₁ Δ ⬝ᵥ τ) ⁻¹' {x | ca x} ∪
        (fun Δ : Fin (2 + m) → ℝ => proj₁ Δ ⬝ᵥ g) ⁻¹' {x | ca x ∧ x ≠ 0}) ∪
      (aa B ∘ proj₂) ⁻¹' {0} := by
    ext Δ
    simp [dK, or_assoc]
  rw [this]
  exact (h1.union h2).union h4
lemma isSpectral_right_hexagon {c : Fin 3 → ℝ} (hpos : ∀ e, 0 < c e) {m : ℕ} {B : Set (Fin m → ℝ)} (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B) (hspec : isSpectral (productSet (k3Zonotope c) B)) : isSpectral B := by
  have hc : ∀ e, 0 ≤ c e := fun e => (hpos e).le
  have h0 := hpos 0; have h1 := hpos 1; have h2 := hpos 2
  have hB : volume B ≠ ⊤ := hBb.measure_lt_top.ne
  obtain ⟨Λ₀, hΛ₀⟩ := hspec
  have za : ∀ (z : Fin 2 → ℤ), (∀ i, z i = 0 ∨ z i = 1) → ∀ e, |dR z e| ≤ 1 := by
    intro z hz01 e
    rcases hz01 0 with h0' | h0' <;> rcases hz01 1 with h1' | h1' <;> fin_cases e <;>
      simp [dR, h0', h1']
  have hA := d4 (u := dr c 2) hc hBm hBb hΛ₀ ![1, 0]
    (za _ (fun i => by fin_cases i <;> simp))
    (by rw [dt]; simp [zr]; linarith)
    (by simp [dr, dq, dp, zr, dotProduct, Fin.sum_univ_two])
    (by
      have hdet : (dV (dr c 2) (dn c *ᵥ zr ![1, 0])).det =
          -(c 2 * (c 0 + c 1)) := by
        rw [det_fin_two]
        simp [dV, dr, dq, dp, zr, dn, mulVec, dotProduct, Fin.sum_univ_two]
        ring
      rw [isUnit_iff_ne_zero, hdet]
      exact neg_ne_zero.2 (mul_pos h2 (by linarith)).ne')
    (by
      intro a
      have hx : dV (dr c 2) (dn c *ᵥ zr ![1, 0]) *ᵥ ![a, 1 / 2] =
          ![1 / 2 * (c 0 + c 1), a * c 2 - 1 / 2 * c 0] := by
        funext i; fin_cases i <;> simp [dV, dr, dq, dp, zr, dn,
          mulVec, dotProduct, Fin.sum_univ_two] <;> ring
      rw [hx]
      constructor
      · intro hmem
        have k1 := dx hc hmem ![1, 1]
        have k2 := dx hc hmem ![0, -1]
        rw [dt] at k1 k2
        simp [zr, dotProduct, Fin.sum_univ_two] at k1 k2
        rw [abs_le]; constructor <;> nlinarith
      · intro ha
        rw [abs_le] at ha
        refine ⟨![1 / 2, 1 / 2, a], fun e => ?_, ?_⟩
        · fin_cases e <;> simp [abs_le] <;> constructor <;> linarith [ha.1, ha.2]
        · funext i; fin_cases i <;> simp [k3Point] <;> ring)
  obtain ⟨Λ₁, h₁, p₁, c₁⟩ := hA
  have hB' := d4 (u := dr c 1) hc hBm hBb h₁ ![0, 1]
    (za _ (fun i => by fin_cases i <;> simp))
    (by rw [dt]; simp [zr]; linarith)
    (by simp [dr, dq, dp, zr, dotProduct, Fin.sum_univ_two])
    (by
      have hdet : (dV (dr c 1) (dn c *ᵥ zr ![0, 1])).det =
          c 1 * (c 0 + c 2) := by
        rw [det_fin_two]
        simp [dV, dr, dq, dp, zr, dn, mulVec, dotProduct, Fin.sum_univ_two]
      rw [isUnit_iff_ne_zero, hdet]
      exact (mul_pos h1 (by linarith)).ne')
    (by
      intro a
      have hx : dV (dr c 1) (dn c *ᵥ zr ![0, 1]) *ᵥ ![a, 1 / 2] =
          ![a * c 1 - 1 / 2 * c 0, 1 / 2 * (c 0 + c 2)] := by
        funext i; fin_cases i <;> simp [dV, dr, dq, dp, zr, dn,
          mulVec, dotProduct, Fin.sum_univ_two] <;> ring
      rw [hx]
      constructor
      · intro hmem
        have k1 := dx hc hmem ![1, 1]
        have k2 := dx hc hmem ![-1, 0]
        rw [dt] at k1 k2
        simp [zr, dotProduct, Fin.sum_univ_two] at k1 k2
        rw [abs_le]; constructor <;> nlinarith
      · intro ha
        rw [abs_le] at ha
        refine ⟨![-(1 / 2), a, 1 / 2], fun e => ?_, ?_⟩
        · fin_cases e <;> simp [abs_le] <;> constructor <;> linarith [ha.1, ha.2]
        · funext i; fin_cases i <;> simp [k3Point] <;> ring)
  obtain ⟨Λ₂, h₂, p₂, c₂⟩ := hB'
  have c₁' := p₂ _ (d5 hB _ _) c₁
  have hmeas : MeasurableSet (k3Zonotope c) := (dB c).isClosed.measurableSet
  have hpd := dw hc h1 h2
  have hD : 0 < c 0 * c 1 + c 0 * c 2 + c 1 * c 2 := by positivity
  refine bq hmeas (dB c).isBounded hBm hBb h₂
    (W := dG c) (b8 hpd.inv) ?_ ?_
  · rw [dF hc h1 h2, dH hc h1 h2, ENNReal.ofReal_inv_of_pos hD]
  · intro l hl l' hl' hne
    by_cases hBz : aa B (proj₂ (l' - l)) = 0
    · right; rwa [← proj₂_sub]
    · left
      have hZ := (dh h₂ l hl l' hl' hne).resolve_right hBz
      have ht0 : proj₁ (l' - l) ≠ 0 := by
        have zb := (aq ⟨Λ₂, h₂⟩).1
        intro h0'
        rw [h0', aj] at hZ
        have : volume.real (k3Zonotope c) ≠ 0 :=
          (ENNReal.toReal_pos zb.ne' (dB c).isBounded.measure_lt_top.ne).ne'
        exact this (by exact_mod_cast hZ)
      have hH : dL c (proj₁ (l' - l)) := ⟨ht0, Or.resolve_right (c₁' l hl l' hl' hne) hBz,
        Or.resolve_right (c₂ l hl l' hl' hne) hBz⟩
      have hempty : {x : Fin 2 → ℝ | proj₁ l - x ∈ dG c ∧ proj₁ l' - x ∈ dG c} =
          ∅ := by
        refine Set.eq_empty_of_forall_notMem fun x hx => ?_
        have hdiff : proj₁ (l' - l) ∈ (2 : ℝ) • dG c := by
          rw [dG, ← b7]
          refine ⟨proj₁ l' - x, hx.2, proj₁ l - x, hx.1, ?_⟩
          rw [proj₁_sub]; abel_nf
        exact dN hpos hdiff hH
      rw [hempty, measure_empty]
end Hexagon
end
section
open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate CompactlySupported
namespace FCBridge
variable {d : ℕ}
noncomputable def d6 (F : Finset (Fin d → ℝ)) (y : Fin d → ℝ) : ℝ :=
  ‖∑ l ∈ F, exponentialCharacter l y‖ ^ 2 / F.card
lemma d7 (F : Finset (Fin d → ℝ)) (y : Fin d → ℝ) : 0 ≤ d6 F y := by
  unfold d6; positivity
lemma d8 (F : Finset (Fin d → ℝ)) : Continuous (d6 F) := by
  unfold d6
  exact ((continuous_finsetSum _ fun l _ => continuous_exponentialCharacter l).norm.pow 2).div_const
    _
lemma d9 (F : Finset (Fin d → ℝ)) (y : Fin d → ℝ) : d6 F y ≤ F.card := by
  unfold d6
  rcases Nat.eq_zero_or_pos F.card with h | h
  · simp [h]
  have hc : (0 : ℝ) < F.card := by exact_mod_cast h
  have hn : ‖∑ l ∈ F, exponentialCharacter l y‖ ≤ F.card := by
    calc ‖∑ l ∈ F, exponentialCharacter l y‖ ≤ ∑ l ∈ F, ‖exponentialCharacter l y‖ :=
          norm_sum_le _ _
      _ = F.card := by simp [norm_exponentialCharacter]
  rw [div_le_iff₀ hc]
  nlinarith [norm_nonneg (∑ l ∈ F, exponentialCharacter l y)]
lemma ec (F : Finset (Fin d → ℝ)) (y : Fin d → ℝ) : ((‖∑ l ∈ F, exponentialCharacter l y‖ ^ 2 : ℝ) : ℂ) = ∑ l ∈ F, ∑ l' ∈ F, exponentialCharacter (l' - l) y := by
  rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ =>
    ag l l' y
lemma ed (ξ x z : Fin d → ℝ) : exponentialCharacter ξ (x - z) = exponentialCharacter ξ x * exponentialCharacter (-ξ) z := by
  rw [sub_eq_add_neg, au]
  congr 1
  unfold exponentialCharacter
  congr 1
  simp
lemma ee {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (ξ : Fin d → ℝ) {g : (Fin d → ℝ) → (Fin d → ℝ)} (hg : Continuous g) : IntegrableOn (fun z => exponentialCharacter ξ (g z)) Ω := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((continuous_exponentialCharacter ξ).comp hg).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  simp [norm_exponentialCharacter]
lemma ef (Ω : Set (Fin d → ℝ)) (ξ x : Fin d → ℝ) : ∫ z in Ω, exponentialCharacter ξ (x - z) = exponentialCharacter ξ x * aa Ω (-ξ) := by
  simp_rw [ed]
  rw [integral_const_mul]
  rfl
lemma eg {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (horth : aI Ω Λ) {F : Finset (Fin d → ℝ)} (hF : (F : Set (Fin d → ℝ)) ⊆ Λ) (hFne : F.Nonempty) (x : Fin d → ℝ) : ∫ z in Ω, d6 F (x - z) = volume.real Ω := by
  classical
  have hc : (F.card : ℂ) ≠ 0 := by exact_mod_cast hFne.card_pos.ne'
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp only [d6, Complex.ofReal_div, ec, Complex.ofReal_natCast]
  have hint : ∀ ξ : Fin d → ℝ, IntegrableOn (fun z => exponentialCharacter ξ (x - z)) Ω :=
    fun ξ => ee hΩ ξ (continuous_sub_left x)
  rw [integral_div, integral_finsetSum _ fun l _ =>
    integrable_finsetSum _ fun l' _ => hint (l' - l)]
  have hterm : ∀ l ∈ F, ∫ z in Ω, ∑ l' ∈ F, exponentialCharacter (l' - l) (x - z) =
      (volume.real Ω : ℂ) := by
    intro l hl
    rw [integral_finsetSum _ fun l' _ => hint (l' - l)]
    simp_rw [ef]
    rw [Finset.sum_eq_single l]
    · simp [aj, af]
    · intro l' hl' hne
      have h0 := horth l' (hF hl') l (hF hl) hne
      rw [neg_sub, h0, mul_zero]
    · intro h; exact absurd hl h
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_div_cancel_left₀ _ hc]
lemma eh {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (F : Finset (Fin d → ℝ)) {g : (Fin d → ℝ) → (Fin d → ℝ)} (hg : Continuous g) : IntegrableOn (fun z => d6 F (g z)) Ω := by
  have : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hΩ
  refine Integrable.mono' (integrable_const (F.card : ℝ))
    ((d8 F).comp hg).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (d7 F _)]
  exact d9 F _
lemma ei {Ω Λ : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (horth : aI Ω Λ) {F : Finset (Fin d → ℝ)} (hF : (F : Set (Fin d → ℝ)) ⊆ Λ) (hFne : F.Nonempty) (x : Fin d → ℝ) : ∫⁻ z in Ω, ENNReal.ofReal (d6 F (x - z)) = volume Ω := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (eh hΩ F (continuous_sub_left x))
    (Eventually.of_forall fun z => d7 F _),
    eg hΩ horth hF hFne x, ofReal_measureReal hΩ]
lemma ej {Ω Λ : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (horth : aI Ω Λ) {F : Finset (Fin d → ℝ)} (hF : (F : Set (Fin d → ℝ)) ⊆ Λ) (hFne : F.Nonempty) (c : Fin d → ℝ) (r : ℝ) : ∫⁻ y in closedBall c r, ENNReal.ofReal (d6 F y) ≤ volume (closedBall c (r + R₀)) := by
  set g : (Fin d → ℝ) → ENNReal := fun y => ENNReal.ofReal (d6 F y) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp (d8 F).measurable
  set Q := closedBall c (r + R₀) with hQ
  have h2 : ∫⁻ x in Q, ∫⁻ z in Ω, g (x - z) = volume Q * volume Ω := by
    simp_rw [hg, ei hΩ horth hF hFne]
    rw [setLIntegral_const, mul_comm]
  have h3 : ∫⁻ x in Q, ∫⁻ z in Ω, g (x - z) = ∫⁻ z in Ω, ∫⁻ x in Q, g (x - z) :=
    lintegral_lintegral_swap ((hgm.comp measurable_sub).aemeasurable)
  have h4 : ∀ z ∈ Ω, ∫⁻ y in closedBall c r, g y ≤ ∫⁻ x in Q, g (x - z) := by
    intro z hz
    have hz' : ‖z‖ ≤ R₀ := mem_closedBall_zero_iff.mp (hΩR hz)
    calc ∫⁻ y in closedBall c r, g y = ∫⁻ x, (closedBall c r).indicator g (x - z) := by
          rw [lintegral_sub_right_eq_self (fun y => (closedBall c r).indicator g y) z, lintegral_indicator measurableSet_closedBall]
      _ ≤ ∫⁻ x, Q.indicator (fun x => g (x - z)) x := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x - z ∈ closedBall c r
          · have hxQ : x ∈ Q := by
              rw [mem_closedBall] at hx
              rw [hQ, mem_closedBall]
              calc dist x c ≤ dist (x - z) c + ‖z‖ := by
                    rw [dist_eq_norm, dist_eq_norm]
                    calc ‖x - c‖ = ‖(x - z - c) + z‖ := by congr 1; abel
                      _ ≤ ‖x - z - c‖ + ‖z‖ := norm_add_le _ _
                _ ≤ r + R₀ := add_le_add hx hz'
            rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxQ]
          · rw [Set.indicator_of_notMem hx]; exact zero_le
      _ = ∫⁻ x in Q, g (x - z) := lintegral_indicator measurableSet_closedBall _
  have h5 : volume Ω * ∫⁻ y in closedBall c r, g y ≤ volume Q * volume Ω :=
    calc volume Ω * ∫⁻ y in closedBall c r, g y = ∫⁻ z in Ω, ∫⁻ y in closedBall c r, g y := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ z in Ω, ∫⁻ x in Q, g (x - z) := setLIntegral_mono' hΩm h4
      _ = volume Q * volume Ω := by rw [← h3, h2]
  rw [mul_comm (volume Q)] at h5
  exact (ENNReal.mul_le_mul_iff_right hpos.ne' hΩ).mp h5
lemma ek {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (I : ℕ → C_c(X, ℝ) →ₚ[ℝ] ℝ) (U : Ultrafilter ℕ) (hb : ∀ φ : C_c(X, ℝ), ∃ M, ∀ j, |I j φ| ≤ M) : ∃ ν : Measure X, ν.Regular ∧ ∀ φ : C_c(X, ℝ), Tendsto (fun j => I j φ) U (𝓝 (∫ x, φ x ∂ν)) := by
  have hlim : ∀ φ : C_c(X, ℝ), ∃ a, Tendsto (fun j => I j φ) U (𝓝 a) := by
    intro φ
    obtain ⟨M, hM⟩ := hb φ
    obtain ⟨a, -, ha⟩ := (isCompact_Icc (a := -M) (b := M)).ultrafilter_le_nhds
      (U.map fun j => I j φ) (by
        rw [Ultrafilter.coe_map, le_principal_iff]
        exact Filter.mem_map.mpr (Filter.univ_mem' fun j => abs_le.mp (hM j)))
    exact ⟨a, ha⟩
  choose a ha using hlim
  have za : ∀ φ ψ, a (φ + ψ) = a φ + a ψ := fun φ ψ =>
    tendsto_nhds_unique (ha (φ + ψ)) (by simpa only [map_add] using (ha φ).add (ha ψ))
  have zb : ∀ (c : ℝ) φ, a (c • φ) = c • a φ := fun c φ =>
    tendsto_nhds_unique (ha (c • φ)) (by simpa only [map_smul] using (ha φ).const_smul c)
  let L : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := a, map_add' := za, map_smul' := zb }
  have hpos : ∀ φ, 0 ≤ φ → 0 ≤ L φ := by
    intro φ hφ
    refine ge_of_tendsto (ha φ) (Eventually.of_forall fun j => ?_)
    have := (I j).monotone' hφ
    simpa using this
  refine ⟨RealRMK.rieszMeasure (PositiveLinearMap.mk₀ L hpos), inferInstance, fun φ => ?_⟩
  rw [RealRMK.integral_rieszMeasure]
  exact ha φ
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate CompactlySupported symmDiff
namespace FCBridge
variable {d : ℕ}
noncomputable def xcorr (E Ω : Set (Fin d → ℝ)) (y : Fin d → ℝ) : ℝ :=
  volume.real (E ∩ {x | x - y ∈ Ω})
lemma el (E Ω : Set (Fin d → ℝ)) (y : Fin d → ℝ) : 0 ≤ xcorr E Ω y :=
  measureReal_nonneg
lemma em {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (y : Fin d → ℝ) :
    volume {x : Fin d → ℝ | x - y ∈ Ω} = volume Ω :=
  (measurePreserving_sub_right volume y).measure_preimage hΩm.nullMeasurableSet
lemma en {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (x : Fin d → ℝ) :
    volume {y : Fin d → ℝ | x - y ∈ Ω} = volume Ω :=
  (Measure.measurePreserving_sub_left volume x).measure_preimage hΩm.nullMeasurableSet
lemma eo {α : Type*} [MeasurableSpace α] {μ : Measure α} {E A A' : Set α} (hA : μ A ≠ ⊤) (hA' : μ A' ≠ ⊤) : |μ.real (E ∩ A) - μ.real (E ∩ A')| ≤ μ.real (A ∆ A') := by
  have key : ∀ {B B' : Set α}, μ B ≠ ⊤ → μ B' ≠ ⊤ →
      μ.real (E ∩ B) ≤ μ.real (E ∩ B') + μ.real (B ∆ B') := by
    intro B B' hB hB'
    have hsub : E ∩ B ⊆ (E ∩ B') ∪ (B ∆ B') := by
      intro x ⟨hxE, hxB⟩
      by_cases hx : x ∈ B'
      · exact Or.inl ⟨hxE, hx⟩
      · exact Or.inr (Or.inl ⟨hxB, hx⟩)
    have za : μ (E ∩ B') ≠ ⊤ := measure_ne_top_of_subset Set.inter_subset_right hB'
    have zb : μ (B ∆ B') ≠ ⊤ := measure_symmDiff_ne_top hB hB'
    have hle := measure_mono (μ := μ) hsub
    have zc := hle.trans (measure_union_le (E ∩ B') (B ∆ B'))
    rw [measureReal_def, measureReal_def, measureReal_def, ← ENNReal.toReal_add za zb]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨za, zb⟩) zc
  rw [abs_sub_le_iff]
  constructor
  · linarith [key hA hA']
  · have := key hA' hA
    rw [symmDiff_comm] at this
    linarith
lemma continuous_xcorr (E : Set (Fin d → ℝ)) {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) : Continuous (xcorr E Ω) := by
  let g : C((Fin d → ℝ) × (Fin d → ℝ), Fin d → ℝ) := ⟨fun p => p.2 - p.1, by fun_prop⟩
  have hmp : ∀ y : Fin d → ℝ, MeasurePreserving (g.curry y) volume volume :=
    fun y => measurePreserving_sub_right volume y
  have hpre : ∀ y, (g.curry y) ⁻¹' Ω = {x | x - y ∈ Ω} := fun y => rfl
  have hfin : ∀ y, volume {x : Fin d → ℝ | x - y ∈ Ω} ≠ ⊤ := fun y => by
    rw [em hΩm]; exact hΩ
  rw [continuous_iff_continuousAt]
  intro y₀
  have hT := tendsto_measure_symmDiff_preimage_nhds_zero (g.curry.continuous.tendsto y₀)
    (Eventually.of_forall hmp) (hmp y₀) hΩm.nullMeasurableSet hΩ
  simp only [hpre] at hT
  have hT' : Tendsto (fun y => volume.real ({x | x - y ∈ Ω} ∆ {x | x - y₀ ∈ Ω})) (𝓝 y₀)
      (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT
    simpa [measureReal_def, Function.comp_def] using this
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (fun y => ?_) hT'
  rw [Real.norm_eq_abs]
  exact eo (hfin y) (hfin y₀)
lemma ep {E Ω : Set (Fin d → ℝ)} {R₁ R₀ : ℝ} (hE : E ⊆ closedBall 0 R₁) (hΩ : Ω ⊆ closedBall 0 R₀) {y : Fin d → ℝ} (hy : R₁ + R₀ < ‖y‖) : xcorr E Ω y = 0 := by
  unfold xcorr
  have : E ∩ {x | x - y ∈ Ω} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x ⟨hx, hxy⟩ => ?_
    have h1 := mem_closedBall_zero_iff.mp (hE hx)
    have h2 := mem_closedBall_zero_iff.mp (hΩ hxy)
    have h3 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      calc ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
    linarith
  rw [this, measureReal_empty]
lemma er {E Ω : Set (Fin d → ℝ)} {R₁ R₀ : ℝ}
    (hE : E ⊆ closedBall 0 R₁) (hΩ : Ω ⊆ closedBall 0 R₀) : HasCompactSupport (xcorr E Ω) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (R₁ + R₀)) fun y hy =>
    ep hE hΩ (by simpa [mem_closedBall_zero_iff] using hy)
lemma es {E Ω : Set (Fin d → ℝ)} (hE : volume E ≠ ⊤) (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) {f : (Fin d → ℝ) → ℂ} (hf : Continuous f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) : ∫ y, f y * (xcorr E Ω y : ℂ) = ∫ x in E, ∫ z in Ω, f (x - z) := by
  set S : Set ((Fin d → ℝ) × (Fin d → ℝ)) := {p | p.1 - p.2 ∈ Ω} with hSdef
  have hSm : MeasurableSet S := hΩm.preimage (measurable_fst.sub measurable_snd)
  have za : ∀ p : (Fin d → ℝ) × (Fin d → ℝ), p ∈ S ↔ p.1 - p.2 ∈ Ω := fun p => Iff.rfl
  set K : (Fin d → ℝ) → (Fin d → ℝ) → ℂ := fun x y => S.indicator (fun p => f p.2) (x, y)
    with hKdef
  have h1 : ∀ x, ∫ z in Ω, f (x - z) = ∫ y, K x y := by
    intro x
    rw [← integral_indicator hΩm]
    rw [← integral_sub_left_eq_self (fun y => K x y) volume x]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ Ω
    · simp [hKdef, Set.indicator, za, hz]
    · simp [hKdef, Set.indicator, za, hz]
  have hSfin : ((volume.restrict E).prod volume) S ≠ ⊤ := by
    rw [Measure.prod_apply hSm]
    have : ∀ x, volume (Prod.mk x ⁻¹' S) = volume Ω := fun x => en hΩm x
    simp_rw [this]
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact ENNReal.mul_ne_top hΩ hE
  have hint : Integrable (Function.uncurry K) ((volume.restrict E).prod volume) := by
    have hbound : Integrable (S.indicator fun _ => C) ((volume.restrict E).prod volume) :=
      (integrableOn_const hSfin).integrable_indicator hSm
    refine hbound.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hf.measurable.comp measurable_snd).indicator hSm).aestronglyMeasurable
    · simp only [Function.uncurry, hKdef]
      by_cases hp : p ∈ S
      · have hp' : (p.1, p.2) ∈ S := hp
        rw [Set.indicator_of_mem hp', Set.indicator_of_mem hp]
        exact hC _
      · have hp' : (p.1, p.2) ∉ S := hp
        rw [Set.indicator_of_notMem hp', Set.indicator_of_notMem hp, norm_zero]
  calc ∫ y, f y * (xcorr E Ω y : ℂ) = ∫ y, ∫ x in E, K x y := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        have hK : (fun x => K x y) = {x | x - y ∈ Ω}.indicator fun _ => f y := by
          funext x
          by_cases h : x - y ∈ Ω
          · simp [hKdef, Set.indicator, za, h]
          · simp [hKdef, Set.indicator, za, h]
        show f y * (xcorr E Ω y : ℂ) = ∫ x in E, K x y
        have hSy : MeasurableSet {x : Fin d → ℝ | x - y ∈ Ω} :=
          hΩm.preimage (measurable_id.sub_const y)
        rw [hK, integral_indicator_const _ hSy, Measure.real, Measure.restrict_apply hSy, xcorr, Set.inter_comm, Complex.real_smul, mul_comm]
        rfl
    _ = ∫ x in E, ∫ y, K x y := (integral_integral_swap hint).symm
    _ = ∫ x in E, ∫ z in Ω, f (x - z) := by simp_rw [h1]
noncomputable def et (Λ : Set (Fin d → ℝ)) (R : ℝ) : ℕ := (Λ ∩ closedBall 0 R).ncard
lemma cc.finite_ball {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ) (R : ℝ) : (Λ ∩ closedBall 0 R).Finite := by
  rcases le_or_gt 0 R with hR | hR
  · exact hΛ.finite_inter_closedBall hδ 0 hR
  · rw [closedBall_eq_empty.mpr hR, Set.inter_empty]
    exact Set.finite_empty
lemma eu {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ)
    {R R' : ℝ} (h : R ≤ R') : et Λ R ≤ et Λ R' :=
  Set.ncard_le_ncard (Set.inter_subset_inter_right _ (closedBall_subset_closedBall h))
    (hΛ.finite_ball hδ R')
lemma ew {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ) {R : ℝ} (hR : 0 ≤ R) : (et Λ R : ℝ) ≤ ((2 * R + δ) / δ) ^ d := by
  have hfin := hΛ.finite_ball hδ R
  have h := hΛ.card_le hδ 0 hR hfin.toFinset (by simp)
  rw [et, Set.ncard_eq_toFinset_card _ hfin]
  exact h
lemma ex {Λ : Set (Fin d → ℝ)} {δ : ℝ} (hδ : 0 < δ) (hΛ : cc δ Λ) {l : Fin d → ℝ} (hl : l ∈ Λ) {R : ℝ} (hR : ‖l‖ ≤ R) : 1 ≤ et Λ R := by
  rw [et, Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (hΛ.finite_ball hδ R)]
  exact Set.nonempty_iff_ne_empty.mp ⟨l, hl, mem_closedBall_zero_iff.mpr hR⟩
lemma ey {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ) (hne : Λ.Nonempty) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {T : ℝ} (hT : 0 < T) (R₀ : ℝ) : ∃ R, R₀ ≤ R ∧ 0 < et Λ R ∧ (et Λ R : ℝ) - et Λ (R - T) ≤ ε * et Λ R := by
  by_contra H
  push Not at H
  obtain ⟨l₀, hl₀⟩ := hne
  set R₁ := max (max R₀ ‖l₀‖) 0 with hR₁
  have hR₁0 : 0 ≤ R₁ := le_max_right _ _
  have hR₁R₀ : R₀ ≤ R₁ := (le_max_left _ _).trans (le_max_left _ _)
  have hR₁l : ‖l₀‖ ≤ R₁ := (le_max_right _ _).trans (le_max_left _ _)
  set r : ℝ := 1 / (1 - ε) with hr
  have h1ε : 0 < 1 - ε := by linarith
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ h1ε]; linarith
  have za : ∀ k : ℕ, r ^ k ≤ et Λ (R₁ + k * T) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero]
      exact_mod_cast ex hδ hΛ hl₀ hR₁l
    | succ k ih =>
      have hRk : R₀ ≤ R₁ + ((k + 1 : ℕ) : ℝ) * T := by
        have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * T := by positivity
        linarith
      have hpos : 0 < et Λ (R₁ + ((k + 1 : ℕ) : ℝ) * T) :=
        ex hδ hΛ hl₀ (by
          have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * T := by positivity
          linarith)
      have h := H _ hRk hpos
      have hsub : R₁ + ((k + 1 : ℕ) : ℝ) * T - T = R₁ + (k : ℝ) * T := by push_cast; ring
      rw [hsub] at h
      set N := (et Λ (R₁ + ((k + 1 : ℕ) : ℝ) * T) : ℝ)
      have hlt : (et Λ (R₁ + (k : ℝ) * T) : ℝ) < (1 - ε) * N := by linarith
      calc r ^ (k + 1) = r ^ k * r := pow_succ _ _
        _ ≤ (et Λ (R₁ + (k : ℝ) * T) : ℝ) * r := by gcongr
        _ ≤ ((1 - ε) * N) * r := by gcongr
        _ = N := by rw [hr]; field_simp
  set M : ℝ := (2 * R₁ + δ + 2 * T) / δ with hM
  have hM0 : 0 < M := by positivity
  have zb : ∀ k : ℕ, r ^ k ≤ M ^ d * ((k : ℝ) + 1) ^ d := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc r ^ k ≤ et Λ (R₁ + k * T) := za k
      _ ≤ ((2 * (R₁ + k * T) + δ) / δ) ^ d := ew hδ hΛ (by positivity)
      _ ≤ (M * ((k : ℝ) + 1)) ^ d := by
          gcongr
          rw [hM, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hδ]
          nlinarith
      _ = M ^ d * ((k : ℝ) + 1) ^ d := mul_pow _ _ _
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt d hr1
  have hc : 0 < 1 / (M ^ d * r) := by positivity
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hc)).exists_forall_of_atTop
  have hn1 := hn (n + 1) (Nat.le_succ n)
  have hpk := zb n
  have zc : 0 < r ^ (n + 1) := by positivity
  rw [div_lt_div_iff₀ zc (by positivity), one_mul, pow_succ] at hn1
  push_cast at hn1
  nlinarith [pow_pos hM0 d]
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate CompactlySupported Pointwise
namespace FCBridge
variable {d : ℕ}
lemma ez (L : ℝ) (hL : 0 ≤ L) : volume (closedBall (0 : Fin d → ℝ) L) = ENNReal.ofReal ((2 * L) ^ d) := by
  rw [Real.volume_pi_closedBall _ hL, Fintype.card_fin]
lemma eA (L : ℝ) (hL : 0 ≤ L) : volume.real (closedBall (0 : Fin d → ℝ) L) = (2 * L) ^ d := by
  rw [measureReal_def, ez L hL, ENNReal.toReal_ofReal (by positivity)]
noncomputable def eB (L : ℝ) (y : Fin d → ℝ) : ℂ :=
  (((2 * L) ^ d)⁻¹ : ℝ) * aa (closedBall (0 : Fin d → ℝ) L) (-y)
lemma eC (y u : Fin d → ℝ) : exponentialCharacter (-y) u = exponentialCharacter (-u) y := by
  have h : (∑ i, (-y) i * u i) = ∑ i, (-u) i * y i := by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_inj]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  unfold exponentialCharacter
  rw [h]
lemma eD (L : ℝ) (y : Fin d → ℝ) : aa (closedBall (0 : Fin d → ℝ) L) (-y) = ∫ u in closedBall (0 : Fin d → ℝ) L, exponentialCharacter (-u) y := by
  unfold aa
  exact integral_congr_ae (Eventually.of_forall fun u => eC y u)
lemma eE {L : ℝ} (hL : 0 < L) : eB L (0 : Fin d → ℝ) = 1 := by
  rw [eB, neg_zero, aj, eA L hL.le, ← Complex.ofReal_mul, inv_mul_cancel₀ (by positivity), Complex.ofReal_one]
lemma eF (Ω : Set (Fin d → ℝ)) (ξ : Fin d → ℝ) : ‖aa Ω ξ‖ ≤ volume.real Ω := by
  unfold aa
  calc ‖∫ x in Ω, exponentialCharacter ξ x‖ ≤ ∫ x in Ω, ‖exponentialCharacter ξ x‖ :=
        norm_integral_le_integral_norm _
    _ = volume.real Ω := by simp [norm_exponentialCharacter]
lemma eG {L : ℝ} (hL : 0 < L) (y : Fin d → ℝ) : ‖eB L y‖ ≤ 1 := by
  rw [eB, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc ((2 * L) ^ d)⁻¹ * ‖aa (closedBall (0 : Fin d → ℝ) L) (-y)‖
      ≤ ((2 * L) ^ d)⁻¹ * volume.real (closedBall (0 : Fin d → ℝ) L) := by
        gcongr; exact eF _ _
    _ = 1 := by rw [eA L hL.le, inv_mul_cancel₀ (by positivity)]
lemma eH (L : ℝ) : Continuous (eB (d := d) L) := by
  unfold eB
  have hfin : volume (closedBall (0 : Fin d → ℝ) L) ≠ ⊤ := measure_closedBall_lt_top.ne
  exact continuous_const.mul ((aG hfin).comp continuous_neg)
lemma eI {L : ℝ} (hL : 0 < L) (ξ : Fin d → ℝ) : aa (closedBall (0 : Fin d → ℝ) L) ξ = ((L ^ d : ℝ) : ℂ) * aa (closedBall (0 : Fin d → ℝ) 1) (L • ξ) := by
  have hs : L • closedBall (0 : Fin d → ℝ) 1 = closedBall (0 : Fin d → ℝ) L := by
    rw [smul_closedBall L (0 : Fin d → ℝ) zero_le_one, smul_zero, Real.norm_of_nonneg hL.le, mul_one]
  have h := Measure.setIntegral_comp_smul_of_pos volume (exponentialCharacter ξ)
    (closedBall (0 : Fin d → ℝ) 1) hL
  rw [hs, Module.finrank_fin_fun] at h
  have hc : ∀ v : Fin d → ℝ, exponentialCharacter ξ (L • v) = exponentialCharacter (L • ξ) v := by
    intro v
    have h : (∑ i, ξ i * (L • v) i) = ∑ i, (L • ξ) i * v i := by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    unfold exponentialCharacter
    rw [h]
  simp_rw [hc] at h
  unfold aa
  rw [h, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity), Complex.ofReal_one, one_mul]
lemma eJ {L : ℝ} (hL : 0 < L) (y : Fin d → ℝ) : eB L y = (((2 : ℝ) ^ d)⁻¹ : ℝ) * aa (closedBall (0 : Fin d → ℝ) 1) (-(L • y)) := by
  rw [eB, eI hL, smul_neg, ← mul_assoc, ← Complex.ofReal_mul]
  congr 2
  rw [mul_pow]
  field_simp
lemma eK {y : Fin d → ℝ} (hy : y ≠ 0) : Tendsto (fun n : ℕ => eB ((n : ℝ) + 1) y) atTop (𝓝 0) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < n + 1 := fun n => by positivity
  simp_rw [eJ (hpos _)]
  rw [show (0 : ℂ) = (((2 : ℝ) ^ d)⁻¹ : ℝ) * 0 by ring]
  refine Tendsto.const_mul _ ((cE measurableSet_closedBall).comp ?_)
  rw [← comap_norm_atTop (E := Fin d → ℝ), tendsto_comap_iff]
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have : (fun n : ℕ => ‖-(((n : ℝ) + 1) • y)‖) = fun n : ℕ => ((n : ℝ) + 1) * ‖y‖ := by
    funext n; rw [norm_neg, norm_smul, Real.norm_of_nonneg (hpos n).le]
  simp only [Function.comp_def, this]
  exact Tendsto.atTop_mul_const hny (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
lemma eL {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) (ζ : Fin d → ℝ) : ∫ y, exponentialCharacter ζ y * (xcorr Ω Ω y : ℂ) = ((‖aa Ω ζ‖ ^ 2 : ℝ) : ℂ) := by
  rw [es hΩ hΩm hΩ (continuous_exponentialCharacter ζ) (C := 1) (fun y => (norm_exponentialCharacter ζ y).le)]
  simp_rw [ef]
  rw [integral_mul_const, ai, Complex.ofReal_pow, ← Complex.mul_conj']
  rfl
noncomputable def eM (Ω : Set (Fin d → ℝ)) (L : ℝ) (ξ : Fin d → ℝ) : ENNReal :=
  ∫⁻ u in closedBall (0 : Fin d → ℝ) L, ENNReal.ofReal (‖aa Ω (ξ - u)‖ ^ 2)
lemma eN {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) :
    Continuous fun ξ => ‖aa Ω ξ‖ ^ 2 :=
  ((aG hΩ).norm).pow 2
lemma eO {Ω : Set (Fin d → ℝ)} (L : ℝ) (ξ : Fin d → ℝ) : eM Ω L ξ ≠ ⊤ := by
  unfold eM
  refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono_ae (g := fun _ => ENNReal.ofReal
    (volume.real Ω ^ 2)) (by fun_prop) (Eventually.of_forall fun u _ => ?_)) ?_)
  · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (eF _ _) 2)
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
lemma eP {Ω : Set (Fin d → ℝ)} (hΩ : volume Ω ≠ ⊤) (L : ℝ) (ξ : Fin d → ℝ) : ∫ u in closedBall (0 : Fin d → ℝ) L, ‖aa Ω (ξ - u)‖ ^ 2 = (eM Ω L ξ).toReal := by
  unfold eM
  have : IsFiniteMeasure (volume.restrict (closedBall (0 : Fin d → ℝ) L)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun u => ‖aa Ω (ξ - u)‖ ^ 2)
    (Eventually.of_forall fun u => by positivity)
    ((eN hΩ).comp (continuous_sub_left ξ)).aestronglyMeasurable]
lemma eQ {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (L : ℝ) (ξ : Fin d → ℝ) : ∫ y, eB L y * (xcorr Ω Ω y : ℂ) * exponentialCharacter ξ y = ((((2 * L) ^ d)⁻¹ * (eM Ω L ξ).toReal : ℝ) : ℂ) := by
  set B := closedBall (0 : Fin d → ℝ) L with hB
  have hBfin : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  have hxint : Integrable (fun y => (xcorr Ω Ω y : ℂ)) :=
    ((Complex.continuous_ofReal.comp (continuous_xcorr Ω hΩm hΩ)).integrable_of_hasCompactSupport
      ((er hΩR hΩR).comp_left Complex.ofReal_zero))
  set F : (Fin d → ℝ) → (Fin d → ℝ) → ℂ := fun y u =>
    exponentialCharacter (ξ - u) y * (xcorr Ω Ω y : ℂ) with hF
  have hint : Integrable (Function.uncurry F) (volume.prod (volume.restrict B)) := by
    have hb : Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => (xcorr Ω Ω p.1 : ℂ))
        (volume.prod (volume.restrict B)) := hxint.comp_fst _
    refine hb.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hc : Continuous (Function.uncurry F) := by
        simp only [hF]
        refine Continuous.mul ?_ (Complex.continuous_ofReal.comp
          ((continuous_xcorr Ω hΩm hΩ).comp continuous_fst))
        unfold exponentialCharacter
        fun_prop
      exact hc.aestronglyMeasurable
    · simp only [Function.uncurry, hF, norm_mul, norm_exponentialCharacter, one_mul]
      exact le_rfl
  have hpt : ∀ y, eB L y * (xcorr Ω Ω y : ℂ) * exponentialCharacter ξ y =
      ((((2 * L) ^ d)⁻¹ : ℝ) : ℂ) * ∫ u in B, F y u := by
    intro y
    rw [eB, eD, ← hB, mul_assoc, mul_assoc]
    congr 1
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hF]
    rw [show ξ - u = -u + ξ by abel, ab]
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_integral_swap hint]
  have hin : ∀ u, ∫ y, F y u = ((‖aa Ω (ξ - u)‖ ^ 2 : ℝ) : ℂ) := fun u =>
    eL hΩm hΩ (ξ - u)
  simp_rw [hin]
  rw [integral_complex_ofReal, eP hΩ L ξ, ← Complex.ofReal_mul]
lemma eR {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) {L : ℝ} (hL : 0 < L) (F : Finset (Fin d → ℝ)) : ∫ y, (eB L y).re * xcorr Ω Ω y * d6 F y = (F.card : ℝ)⁻¹ * ((2 * L) ^ d)⁻¹ * ∑ l ∈ F, ∑ l' ∈ F, (eM Ω L (l' - l)).toReal := by
  have hxint : Integrable (fun y => (xcorr Ω Ω y : ℂ)) :=
    ((Complex.continuous_ofReal.comp (continuous_xcorr Ω hΩm hΩ)).integrable_of_hasCompactSupport
      ((er hΩR hΩR).comp_left Complex.ofReal_zero))
  have hterm : ∀ ξ : Fin d → ℝ,
      Integrable (fun y => eB L y * (xcorr Ω Ω y : ℂ) * exponentialCharacter ξ y) := by
    intro ξ
    refine hxint.norm.mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (((eH L).mul (Complex.continuous_ofReal.comp
        (continuous_xcorr Ω hΩm hΩ))).mul (continuous_exponentialCharacter ξ)).aestronglyMeasurable
    · rw [norm_mul, norm_mul, norm_exponentialCharacter, mul_one]
      calc ‖eB L y‖ * ‖(xcorr Ω Ω y : ℂ)‖ ≤ 1 * ‖(xcorr Ω Ω y : ℂ)‖ := by
            gcongr; exact eG hL y
        _ = _ := one_mul _
  have hcx : ∫ y, eB L y * (xcorr Ω Ω y : ℂ) * ((d6 F y : ℝ) : ℂ) =
      (((F.card : ℝ)⁻¹ * ((2 * L) ^ d)⁻¹ *
        ∑ l ∈ F, ∑ l' ∈ F, (eM Ω L (l' - l)).toReal : ℝ) : ℂ) := by
    simp only [d6, Complex.ofReal_div, ec, Complex.ofReal_natCast]
    have e1 : ∀ y, eB L y * (xcorr Ω Ω y : ℂ) *
        ((∑ l ∈ F, ∑ l' ∈ F, exponentialCharacter (l' - l) y) / (F.card : ℂ)) =
        (F.card : ℂ)⁻¹ * ∑ l ∈ F, ∑ l' ∈ F,
          eB L y * (xcorr Ω Ω y : ℂ) * exponentialCharacter (l' - l) y := by
      intro y
      simp only [div_eq_inv_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_finsetSum _ fun l _ =>
      integrable_finsetSum _ fun l' _ => hterm (l' - l)]
    simp_rw [integral_finsetSum _ fun l' _ => hterm _]
    simp_rw [eQ hΩm hΩ hΩR L]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l' _ => by ring
  have hint' : Integrable
      (fun y => eB L y * (xcorr Ω Ω y : ℂ) * ((d6 F y : ℝ) : ℂ)) := by
    refine (hxint.norm.mul_const (F.card : ℝ)).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (((eH L).mul (Complex.continuous_ofReal.comp
        (continuous_xcorr Ω hΩm hΩ))).mul (Complex.continuous_ofReal.comp
        (d8 F))).aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_real]
      rw [Real.norm_of_nonneg (d7 F y)]
      calc ‖eB L y‖ * ‖xcorr Ω Ω y‖ * d6 F y
          ≤ 1 * ‖xcorr Ω Ω y‖ * F.card :=
            mul_le_mul (mul_le_mul_of_nonneg_right (eG hL y) (norm_nonneg _))
              (d9 F y) (d7 F y) (by positivity)
        _ = ‖xcorr Ω Ω y‖ * F.card := by ring
  have hre : ∫ y, (eB L y).re * xcorr Ω Ω y * d6 F y =
      (∫ y, eB L y * (xcorr Ω Ω y : ℂ) * ((d6 F y : ℝ) : ℂ)).re := by
    have h := integral_re hint'
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [Complex.mul_re]
  rw [hre, hcx, Complex.ofReal_re]
lemma eS (Ω : Set (Fin d → ℝ)) (L : ℝ) (l l' : Fin d → ℝ) : eM Ω L (l' - l) = ∫⁻ x in closedBall l L, ENNReal.ofReal (‖aa Ω (x - l')‖ ^ 2) := by
  unfold eM
  rw [← lintegral_indicator measurableSet_closedBall, ← lintegral_indicator measurableSet_closedBall, ← lintegral_sub_right_eq_self _ l]
  refine lintegral_congr fun x => ?_
  have hmem : x - l ∈ closedBall (0 : Fin d → ℝ) L ↔ x ∈ closedBall l L := by
    rw [mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm, sub_zero]
  by_cases hx : x ∈ closedBall l L
  · rw [Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx]
    congr 2
    rw [show l' - l - (x - l) = -(x - l') by abel, ai, RCLike.norm_conj]
  · rw [Set.indicator_of_notMem (fun h => hx (hmem.mp h)), Set.indicator_of_notMem hx]
lemma eT {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (L : ℝ) (l : Fin d → ℝ) : ∑' l' : Λ, eM Ω L ((l' : Fin d → ℝ) - l) = ENNReal.ofReal (volume.real Ω ^ 2) * volume (closedBall (0 : Fin d → ℝ) L) := by
  have hh := h
  obtain ⟨-, -, hΩ, -⟩ := hh
  have hΛc : Countable Λ := by
    obtain ⟨-, hpos, hΩ', horth, -⟩ := al.mp h
    exact (aI.countable hΩ' hpos horth).to_subtype
  unfold eM
  have hmeas : ∀ l' : Λ, AEMeasurable (fun u => ENNReal.ofReal
      (‖aa Ω ((l' : Fin d → ℝ) - l - u)‖ ^ 2)) (volume.restrict (closedBall 0 L)) :=
    fun l' => (((eN hΩ).comp
      (continuous_sub_left _)).measurable.ennreal_ofReal).aemeasurable
  rw [← lintegral_tsum hmeas]
  rw [← setLIntegral_const]
  refine setLIntegral_congr_fun measurableSet_closedBall fun u _ => ?_
  have hs := aR h (l + u)
  have heq : ∀ l' : Λ, ‖aa Ω ((l' : Fin d → ℝ) - l - u)‖ ^ 2 =
      ‖aa Ω (l + u - (l' : Fin d → ℝ))‖ ^ 2 := by
    intro l'
    rw [show (l' : Fin d → ℝ) - l - u = -(l + u - l') by abel, ai, RCLike.norm_conj]
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs.summable, hs.tsum_eq]
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate CompactlySupported Classical
namespace FCBridge
variable {d : ℕ}
noncomputable def eU {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ)
    (R : ℝ) : Finset (Fin d → ℝ) :=
  (hΛ.finite_ball hδ R).toFinset
section Trunc
variable {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ)
lemma eV (R : ℝ) : (eU hδ hΛ R : Set (Fin d → ℝ)) = Λ ∩ closedBall 0 R :=
  Set.Finite.coe_toFinset _
lemma eW {R : ℝ} {l : Fin d → ℝ} : l ∈ eU hδ hΛ R ↔ l ∈ Λ ∧ ‖l‖ ≤ R := by
  rw [← Finset.mem_coe, eV, Set.mem_inter_iff, mem_closedBall_zero_iff]
lemma eX (R : ℝ) : (eU hδ hΛ R).card = et Λ R := by
  rw [eU, et, Set.ncard_eq_toFinset_card _ (hΛ.finite_ball hδ R)]
lemma eY (R : ℝ) : (eU hδ hΛ R : Set (Fin d → ℝ)) ⊆ Λ := by
  rw [eV]; exact Set.inter_subset_left
lemma eZ (R : ℝ) (g : (Fin d → ℝ) → ENNReal) : ∑' l' : Λ, (if (l' : Fin d → ℝ) ∈ closedBall 0 R then g l' else 0) = ∑ l' ∈ eU hδ hΛ R, g l' := by
  classical
  rw [tsum_subtype Λ (fun x => if x ∈ closedBall 0 R then g x else 0), ← Finset.tsum_subtype' (eU hδ hΛ R) g, tsum_subtype]
  congr 1
  funext x
  by_cases hx : x ∈ Λ <;> by_cases hb : x ∈ closedBall (0 : Fin d → ℝ) R <;>
    simp [Set.indicator, hx, hb, eV]
end Trunc
noncomputable def e5 (Ω : Set (Fin d → ℝ)) (s : ℝ) : ENNReal :=
  ∫⁻ y in {y : Fin d → ℝ | s ≤ ‖y‖}, ENNReal.ofReal (‖aa Ω y‖ ^ 2)
noncomputable def e6 {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ)
    (Ω : Set (Fin d → ℝ)) (L R : ℝ) : ENNReal :=
  ∑ l ∈ eU hδ hΛ R, ∑' l' : Λ,
    (if (l' : Fin d → ℝ) ∈ closedBall 0 R then 0 else eM Ω L ((l' : Fin d → ℝ) - l))
lemma e7 {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) {δ : ℝ} (hδ : 0 < δ) (hΛ : cc δ Λ) (L R : ℝ) : ∑ l ∈ eU hδ hΛ R, ∑ l' ∈ eU hδ hΛ R, eM Ω L (l' - l) + e6 hδ hΛ Ω L R = (eU hδ hΛ R).card * (ENNReal.ofReal (volume.real Ω ^ 2) * volume (closedBall (0 : Fin d → ℝ) L)) := by
  rw [e6, ← Finset.sum_add_distrib, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← eT h L l, ← eZ hδ hΛ R (fun l' => eM Ω L (l' - l)), ← ENNReal.tsum_add]
  refine tsum_congr fun l' => ?_
  split_ifs <;> simp
lemma e8 {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) {δ : ℝ} (hδ : 0 < δ) (hΛ : cc δ Λ) {L : ℝ} (hL : 0 ≤ L) (R : ℝ) {T : ℝ} (hT : 0 ≤ T) : e6 hδ hΛ Ω L R ≤ (eU hδ hΛ R).card * (ENNReal.ofReal (((2 * L + δ) / δ) ^ d) * e5 Ω (T - L)) + (((eU hδ hΛ R).card - (eU hδ hΛ (R - T)).card : ℕ) : ENNReal) * (ENNReal.ofReal (volume.real Ω ^ 2) * volume (closedBall (0 : Fin d → ℝ) L)) := by
  classical
  have hh := h
  obtain ⟨-, -, hΩ, -⟩ := hh
  set F := eU hδ hΛ R with hF
  set K := ENNReal.ofReal (volume.real Ω ^ 2) * volume (closedBall (0 : Fin d → ℝ) L) with hK
  set C := ENNReal.ofReal (((2 * L + δ) / δ) ^ d) * e5 Ω (T - L) with hC
  set f : (Fin d → ℝ) → ENNReal := fun w => ENNReal.ofReal (‖aa Ω w‖ ^ 2) with hf
  have hfm : Measurable f :=
    ((eN hΩ).measurable).ennreal_ofReal
  set a : (Fin d → ℝ) → ENNReal := fun l => ∑' l' : Λ,
    (if (l' : Fin d → ℝ) ∈ closedBall 0 R then 0 else eM Ω L ((l' : Fin d → ℝ) - l)) with ha
  have za : ∀ l, ‖l‖ ≤ R - T → a l ≤ C := by
    intro l hl
    calc a l ≤ ∑' l' : Λ, (if R ≤ ‖(l' : Fin d → ℝ)‖ then
            ∫⁻ x in closedBall l L, f (x - (l' : Fin d → ℝ)) else 0) := by
          refine ENNReal.tsum_le_tsum fun l' => ?_
          by_cases h1 : (l' : Fin d → ℝ) ∈ closedBall 0 R
          · rw [if_pos h1]; exact zero_le
          · have h2 : R ≤ ‖(l' : Fin d → ℝ)‖ := by
              rw [mem_closedBall_zero_iff, not_le] at h1; exact h1.le
            rw [if_neg h1, if_pos h2, eS]
      _ ≤ ENNReal.ofReal (((2 * L + δ) / δ) ^ d) *
            ∫⁻ y in {y : Fin d → ℝ | R - ‖l‖ - L ≤ ‖y‖}, f y :=
          hΛ.tsum_far_le hδ hfm measurableSet_closedBall hL subset_rfl R
      _ ≤ C := by
          rw [hC, e5]
          refine mul_le_mul_right (lintegral_mono_set fun (y : Fin d → ℝ) hy => ?_) _
          have hy' : R - ‖l‖ - L ≤ ‖y‖ := hy
          show T - L ≤ ‖y‖
          linarith
  have hshell : ∀ l, a l ≤ K := by
    intro l
    calc a l ≤ ∑' l' : Λ, eM Ω L ((l' : Fin d → ℝ) - l) := by
          refine ENNReal.tsum_le_tsum fun l' => ?_
          split_ifs
          · exact zero_le
          · exact le_rfl
      _ = K := eT h L l
  have zb : F.filter (fun l => ‖l‖ ≤ R - T) = eU hδ hΛ (R - T) := by
    ext l
    rw [Finset.mem_filter, eW, eW]
    constructor
    · rintro ⟨⟨hl, -⟩, h2⟩; exact ⟨hl, h2⟩
    · rintro ⟨hl, h2⟩; exact ⟨⟨hl, by linarith⟩, h2⟩
  have hcard : (F.filter fun l => ¬ ‖l‖ ≤ R - T).card = F.card - (eU hδ hΛ (R - T)).card := by
    have := Finset.card_filter_add_card_filter_not (s := F) (fun l => ‖l‖ ≤ R - T)
    rw [zb] at this
    omega
  unfold e6
  show ∑ l ∈ F, a l ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not F (fun l => ‖l‖ ≤ R - T)]
  gcongr ?_ + ?_
  · calc ∑ l ∈ F.filter (fun l => ‖l‖ ≤ R - T), a l
        ≤ ∑ l ∈ F.filter (fun l => ‖l‖ ≤ R - T), C :=
          Finset.sum_le_sum fun l hl => za l (Finset.mem_filter.mp hl).2
      _ = (F.filter (fun l => ‖l‖ ≤ R - T)).card * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ F.card * C := by
          gcongr
          exact Finset.filter_subset _ _
  · calc ∑ l ∈ F.filter (fun l => ¬ ‖l‖ ≤ R - T), a l
        ≤ ∑ l ∈ F.filter (fun l => ¬ ‖l‖ ≤ R - T), K :=
          Finset.sum_le_sum fun l _ => hshell l
      _ = ((F.card - (eU hδ hΛ (R - T)).card : ℕ) : ENNReal) * K := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate CompactlySupported Classical
namespace FCBridge
variable {d : ℕ}
lemma e9 {δ : ℝ} (hδ : 0 < δ) {Λ : Set (Fin d → ℝ)} (hΛ : cc δ Λ) (hne : Λ.Nonempty) : ∃ R : ℕ → ℝ, (∀ j : ℕ, (j : ℝ) ≤ R j) ∧ (∀ j, 0 < et Λ (R j)) ∧ ∀ j : ℕ, (et Λ (R j) : ℝ) - et Λ (R j - ((j : ℝ) + 1)) ≤ et Λ (R j) / ((j : ℝ) + 2) := by
  have key : ∀ j : ℕ, ∃ R, (j : ℝ) ≤ R ∧ 0 < et Λ R ∧
      (et Λ R : ℝ) - et Λ (R - ((j : ℝ) + 1)) ≤
        (1 / ((j : ℝ) + 2)) * et Λ R := by
    intro j
    refine ey hδ hΛ hne (by positivity) ?_ (by positivity) (j : ℝ)
    rw [div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  choose R hR1 hR2 hR3 using key
  refine ⟨R, hR1, hR2, fun j => ?_⟩
  calc (et Λ (R j) : ℝ) - et Λ (R j - ((j : ℝ) + 1))
      ≤ (1 / ((j : ℝ) + 2)) * et Λ (R j) := hR3 j
    _ = et Λ (R j) / ((j : ℝ) + 2) := by ring
lemma fa {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) : Tendsto (fun n : ℕ => e5 Ω n) atTop (𝓝 0) := by
  have hΩ : volume Ω ≠ ⊤ := hΩb.measure_lt_top.ne
  set f : (Fin d → ℝ) → ENNReal := fun w => ENNReal.ofReal (‖aa Ω w‖ ^ 2) with hf
  have hfm : Measurable f := ((eN hΩ).measurable).ennreal_ofReal
  have hfin : ∫⁻ y, f y ≠ ⊤ := ((a9 hΩm hΩb).trans_lt hΩb.measure_lt_top).ne
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n : ℕ => {y : Fin d → ℝ | (n : ℝ) ≤ ‖y‖}.indicator f) (f := fun _ => (0 : ENNReal)) f
    (fun n => hfm.indicator (measurableSet_le measurable_const measurable_norm))
    (fun n => Eventually.of_forall fun y => Set.indicator_le_self _ _ y) hfin
    (Eventually.of_forall fun y => ?_)
  · simp only [lintegral_zero] at hlim
    refine hlim.congr fun n => ?_
    rw [e5, lintegral_indicator (measurableSet_le measurable_const measurable_norm)]
  · obtain ⟨n, hn⟩ := exists_nat_gt ‖y‖
    refine tendsto_atTop_of_eventually_const (i₀ := n) fun m hm => ?_
    have hmy : y ∉ {y' : Fin d → ℝ | (m : ℝ) ≤ ‖y'‖} := by
      have : (n : ℝ) ≤ m := by exact_mod_cast hm
      show ¬ ((m : ℝ) ≤ ‖y‖)
      linarith
    show {y' : Fin d → ℝ | (m : ℝ) ≤ ‖y'‖}.indicator f y = 0
    exact Set.indicator_of_notMem hmy f
lemma fb {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (s : ℝ) : e5 Ω s ≠ ⊤ :=
  ((setLIntegral_le_lintegral _ _).trans_lt
    ((a9 hΩm hΩb).trans_lt hΩb.measure_lt_top)).ne
lemma fc {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (hΩm : MeasurableSet Ω) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) {δ : ℝ} (hδ : 0 < δ) (hΛ : cc δ Λ) {L : ℝ} (hL : 0 < L) (R : ℝ) (hN : 0 < (eU hδ hΛ R).card) : ∫ y, (eB L y).re * xcorr Ω Ω y * d6 (eU hδ hΛ R) y = volume.real Ω ^ 2 - ((2 * L) ^ d)⁻¹ * (e6 hδ hΛ Ω L R).toReal / (eU hδ hΛ R).card := by
  have hh := h
  obtain ⟨-, -, hΩ, -⟩ := hh
  set F := eU hδ hΛ R with hF
  set K := ENNReal.ofReal (volume.real Ω ^ 2) * volume (closedBall (0 : Fin d → ℝ) L) with hK
  have hsplit := e7 h hδ hΛ L R
  rw [← hF, ← hK] at hsplit
  have za : ∀ l ∈ F, ∀ l' ∈ F, eM Ω L (l' - l) ≠ ⊤ := fun _ _ _ _ => eO _ _
  have hSfin : ∑ l ∈ F, ∑ l' ∈ F, eM Ω L (l' - l) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun l hl => ENNReal.sum_ne_top.mpr fun l' hl' => za l hl l' hl'
  have hKfin : K ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have zb : (F.card : ENNReal) * K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hKfin
  have hEfin : e6 hδ hΛ Ω L R ≠ ⊤ := by
    intro htop; rw [htop, add_top] at hsplit; exact zb hsplit.symm
  have hsum : ∑ l ∈ F, ∑ l' ∈ F, (eM Ω L (l' - l)).toReal =
      (F.card : ℝ) * (volume.real Ω ^ 2 * (2 * L) ^ d) - (e6 hδ hΛ Ω L R).toReal := by
    have e1 : ∑ l ∈ F, ∑ l' ∈ F, (eM Ω L (l' - l)).toReal =
        (∑ l ∈ F, ∑ l' ∈ F, eM Ω L (l' - l)).toReal := by
      rw [ENNReal.toReal_sum fun l hl => ENNReal.sum_ne_top.mpr fun l' hl' => za l hl l' hl']
      exact Finset.sum_congr rfl fun l hl => (ENNReal.toReal_sum fun l' hl' => za l hl l' hl').symm
    have e2 := congrArg ENNReal.toReal hsplit
    rw [ENNReal.toReal_add hSfin hEfin, ENNReal.toReal_mul, ENNReal.toReal_natCast, hK, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ez L hL.le, ENNReal.toReal_ofReal (by positivity)] at e2
    rw [e1]
    linarith
  rw [eR hΩm hΩ hΩR hL F, hsum]
  have hNr : (0 : ℝ) < F.card := by exact_mod_cast hN
  have hLr : (0 : ℝ) < (2 * L) ^ d := by positivity
  field_simp
lemma fd {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (hΩm : MeasurableSet Ω) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) {δ : ℝ} (hδ : 0 < δ) (hΛ : cc δ Λ) {L : ℝ} (hL : 0 < L) {R : ℕ → ℝ} (hRpos : ∀ j, 0 < et Λ (R j)) (hRshell : ∀ j : ℕ, (et Λ (R j) : ℝ) - et Λ (R j - ((j : ℝ) + 1)) ≤ et Λ (R j) / ((j : ℝ) + 2)) : Tendsto (fun j => ∫ y, (eB L y).re * xcorr Ω Ω y * d6 (eU hδ hΛ (R j)) y) atTop (𝓝 (volume.real Ω ^ 2)) := by
  have hΩb : Bornology.IsBounded Ω := isBounded_closedBall.subset hΩR
  have hL0 : 0 ≤ L := hL.le
  set M : ℝ := ((2 * L) ^ d)⁻¹ * (((2 * L + δ) / δ) ^ d) with hM
  set K' : ℝ := ((2 * L) ^ d)⁻¹ * (volume.real Ω ^ 2 * (2 * L) ^ d) with hK'
  have za : 0 ≤ M := by positivity
  have zb : 0 ≤ K' := by positivity
  have hbound : ∀ (T : ℝ), 0 ≤ T → ∀ j : ℕ, T ≤ (j : ℝ) + 1 →
      volume.real Ω ^ 2 - ∫ y, (eB L y).re * xcorr Ω Ω y * d6 (eU hδ hΛ (R j)) y
        ≤ M * (e5 Ω (T - L)).toReal + K' / ((j : ℝ) + 2) := by
    intro T hT j hTj
    have hN : 0 < (eU hδ hΛ (R j)).card := by rw [eX]; exact hRpos j
    rw [fc h hΩm hΩR hδ hΛ hL (R j) hN, sub_sub_cancel]
    set N := (eU hδ hΛ (R j)).card with hNdef
    set N' := (eU hδ hΛ (R j - T)).card with hN'def
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have zc := e8 h hδ hΛ hL0 (R j) hT
    have zd := fb hΩm hΩb (T - L)
    have hKfin : ENNReal.ofReal (volume.real Ω ^ 2) * volume (closedBall (0 : Fin d → ℝ) L) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
    have ze : (N : ENNReal) * (ENNReal.ofReal (((2 * L + δ) / δ) ^ d) * e5 Ω (T - L)) +
        ((N - N' : ℕ) : ENNReal) *
          (ENNReal.ofReal (volume.real Ω ^ 2) * volume (closedBall (0 : Fin d → ℝ) L)) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top zd),
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hKfin⟩
    have zf := ENNReal.toReal_mono ze zc
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top zd))
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hKfin),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal
        (by positivity), ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), ez L hL0,
      ENNReal.toReal_ofReal (by positivity)] at zf
    have hshell : ((N - N' : ℕ) : ℝ) ≤ N / ((j : ℝ) + 2) := by
      have zg : N' ≤ N := by
        rw [hNdef, hN'def, eX, eX]
        exact eu hδ hΛ (by linarith)
      have hle : R j - ((j : ℝ) + 1) ≤ R j - T := by linarith
      have zh : (et Λ (R j - ((j : ℝ) + 1)) : ℝ) ≤ N' := by
        rw [hN'def, eX]; exact_mod_cast eu hδ hΛ hle
      have := hRshell j
      rw [← eX hδ hΛ (R j)] at this
      rw [Nat.cast_sub zg]
      linarith
    have zi : 0 ≤ (e5 Ω (T - L)).toReal := ENNReal.toReal_nonneg
    have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    calc ((2 * L) ^ d)⁻¹ * (e6 hδ hΛ Ω L (R j)).toReal / N
        ≤ ((2 * L) ^ d)⁻¹ * (N * (((2 * L + δ) / δ) ^ d * (e5 Ω (T - L)).toReal) +
            ((N - N' : ℕ) : ℝ) * (volume.real Ω ^ 2 * (2 * L) ^ d)) / N := by
          gcongr
      _ ≤ ((2 * L) ^ d)⁻¹ * (N * (((2 * L + δ) / δ) ^ d * (e5 Ω (T - L)).toReal) +
            (N / ((j : ℝ) + 2)) * (volume.real Ω ^ 2 * (2 * L) ^ d)) / N := by
          gcongr
      _ = M * (e5 Ω (T - L)).toReal + K' / ((j : ℝ) + 2) := by
          rw [hM, hK']
          field_simp
  have zj : ∀ j, ∫ y, (eB L y).re * xcorr Ω Ω y * d6 (eU hδ hΛ (R j)) y ≤
      volume.real Ω ^ 2 := by
    intro j
    have hN : 0 < (eU hδ hΛ (R j)).card := by rw [eX]; exact hRpos j
    rw [fc h hΩm hΩR hδ hΛ hL (R j) hN, sub_le_self_iff]
    positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htl := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (fa hΩm hΩb)
  simp only [ENNReal.toReal_zero] at htl
  obtain ⟨n, hn⟩ := (htl.eventually (gt_mem_nhds (show 0 < ε / (2 * (M + 1)) by positivity))).exists
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (2 * K' / ε + (n : ℝ) + L)
  refine ⟨j₀, fun j hj => ?_⟩
  have hjr : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
  set T : ℝ := (n : ℝ) + L with hT
  have hT0 : 0 ≤ T := by positivity
  have hTj : T ≤ (j : ℝ) + 1 := by
    have : (0 : ℝ) ≤ 2 * K' / ε := by positivity
    linarith
  have hb := hbound T hT0 j hTj
  rw [hT, add_sub_cancel_right] at hb
  have hn' : (e5 Ω n).toReal < ε / (2 * (M + 1)) := hn
  have h1 : M * (e5 Ω n).toReal ≤ ε / 2 := by
    have hM1 : 0 < M + 1 := by linarith
    calc M * (e5 Ω n).toReal ≤ (M + 1) * (ε / (2 * (M + 1))) :=
          mul_le_mul (by linarith) hn'.le ENNReal.toReal_nonneg hM1.le
      _ = ε / 2 := by field_simp
  have h2 : K' / ((j : ℝ) + 2) < ε / 2 := by
    have hj2 : (0 : ℝ) < (j : ℝ) + 2 := by positivity
    rw [div_lt_iff₀ hj2]
    have : 2 * K' / ε < (j : ℝ) + 2 := by linarith
    rw [div_lt_iff₀ hε] at this
    nlinarith
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (zj j))]
  linarith
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate CompactlySupported Classical
namespace FCBridge
variable {d : ℕ}
lemma fe (φ : C_c(Fin d → ℝ, ℝ)) (F : Finset (Fin d → ℝ)) :
    Integrable (fun y => φ y * d6 F y) :=
  (φ.continuous.mul (d8 F)).integrable_of_hasCompactSupport
    φ.hasCompactSupport.mul_right
noncomputable def ff (F : Finset (Fin d → ℝ)) : C_c(Fin d → ℝ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun φ => ∫ y, φ y * d6 F y
      map_add' := fun φ ψ => by
        simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply, add_mul]
        exact integral_add (fe φ F) (fe ψ F)
      map_smul' := fun c φ => by
        simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
    (fun φ hφ => integral_nonneg fun y => mul_nonneg (hφ y) (d7 F y))
lemma fg (F : Finset (Fin d → ℝ)) (φ : C_c(Fin d → ℝ, ℝ)) :
    ff F φ = ∫ y, φ y * d6 F y := rfl
lemma fh {Ω Λ : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (horth : aI Ω Λ) {F : Finset (Fin d → ℝ)} (hF : (F : Set (Fin d → ℝ)) ⊆ Λ) (hFne : F.Nonempty) (c : Fin d → ℝ) (r : ℝ) : ∫ y in closedBall c r, d6 F y ≤ volume.real (closedBall c (r + R₀)) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => d7 F y)
    (d8 F).aestronglyMeasurable, measureReal_def]
  exact ENNReal.toReal_mono measure_closedBall_lt_top.ne
    (ej hΩm hΩ hpos hΩR horth hF hFne c r)
lemma fi {Ω Λ : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (horth : aI Ω Λ) (φ : C_c(Fin d → ℝ, ℝ)) : ∃ M, ∀ F : Finset (Fin d → ℝ), (F : Set (Fin d → ℝ)) ⊆ Λ → F.Nonempty → |ff F φ| ≤ M := by
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  obtain ⟨r, hr⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  refine ⟨C * volume.real (closedBall (0 : Fin d → ℝ) (r + R₀)), fun F hF hFne => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hint : Integrable ((closedBall (0 : Fin d → ℝ) r).indicator (d6 F)) :=
    ((d8 F).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 r)).integrable_indicator measurableSet_closedBall
  rw [fg]
  calc |∫ y, φ y * d6 F y| = ‖∫ y, φ y * d6 F y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖φ y * d6 F y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, C * (closedBall (0 : Fin d → ℝ) r).indicator (d6 F) y := by
        refine integral_mono (fe φ F).norm (hint.const_mul C) fun y => ?_
        rw [norm_mul, Real.norm_of_nonneg (d7 F y)]
        by_cases hy : y ∈ closedBall (0 : Fin d → ℝ) r
        · rw [Set.indicator_of_mem hy]
          exact mul_le_mul_of_nonneg_right (hC y) (d7 F y)
        · have : φ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hr h)
          rw [this, norm_zero, zero_mul, Set.indicator_of_notMem hy, mul_zero]
    _ = C * ∫ y in closedBall (0 : Fin d → ℝ) r, d6 F y := by
        rw [integral_const_mul, integral_indicator measurableSet_closedBall]
    _ ≤ C * volume.real (closedBall (0 : Fin d → ℝ) (r + R₀)) := by
        gcongr
        exact fh hΩm hΩ hpos hΩR horth hF hFne 0 r
lemma fj {Ω Λ : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) (hpos : 0 < volume Ω) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (horth : aI Ω Λ) (F : ℕ → Finset (Fin d → ℝ)) (hF : ∀ j, (F j : Set (Fin d → ℝ)) ⊆ Λ) (hFne : ∀ j, (F j).Nonempty) : ∃ ν : Measure (Fin d → ℝ), ν.Regular ∧ ∀ φ : C_c(Fin d → ℝ, ℝ), Tendsto (fun j => ∫ y, φ y * d6 (F j) y) (hyperfilter ℕ) (𝓝 (∫ y, φ y ∂ν)) := by
  refine ek (fun j => ff (F j)) (hyperfilter ℕ)
    fun φ => ?_
  obtain ⟨M, hM⟩ := fi hΩm hΩ hpos hΩR horth φ
  exact ⟨M, fun j => hM (F j) (hF j) (hFne j)⟩
lemma fk {E Ω : Set (Fin d → ℝ)} (hE : volume E ≠ ⊤) (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) {C : ℝ} (hC : ∀ y, |f y| ≤ C) : ∫ y, f y * xcorr E Ω y = ∫ x in E, ∫ z in Ω, f (x - z) := by
  have h := es hE hΩm hΩ (f := fun y => (f y : ℂ))
    (Complex.continuous_ofReal.comp hf) (C := C) (fun y => by simpa using hC y)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  rw [h, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  exact integral_complex_ofReal
noncomputable def fl {E Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤)
    {R₁ R₀ : ℝ} (hE : E ⊆ closedBall 0 R₁) (hΩR : Ω ⊆ closedBall 0 R₀) :
    C_c(Fin d → ℝ, ℝ) :=
  ⟨⟨xcorr E Ω, continuous_xcorr E hΩm hΩ⟩, er hE hΩR⟩
lemma fn {Ω Λ : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (horth : aI Ω Λ) (F : ℕ → Finset (Fin d → ℝ)) (hF : ∀ j, (F j : Set (Fin d → ℝ)) ⊆ Λ) (hFne : ∀ j, (F j).Nonempty) {ν : Measure (Fin d → ℝ)} [ν.Regular] (hν : ∀ φ : C_c(Fin d → ℝ, ℝ), Tendsto (fun j => ∫ y, φ y * d6 (F j) y) (hyperfilter ℕ) (𝓝 (∫ y, φ y ∂ν))) : ∀ᵐ x, ν {y | x - y ∈ Ω} = volume Ω := by
  set S : Set ((Fin d → ℝ) × (Fin d → ℝ)) := {p | p.1 - p.2 ∈ Ω} with hSdef
  have hSm : MeasurableSet S := hΩm.preimage (measurable_fst.sub measurable_snd)
  have hmeas : Measurable fun x => ν {y | x - y ∈ Ω} := measurable_measure_prodMk_left hSm
  have za : ∀ n : ℕ, ∀ E : Set (Fin d → ℝ), MeasurableSet E → E ⊆ closedBall 0 n →
      ∫⁻ x in E, ν {y | x - y ∈ Ω} = volume E * volume Ω := by
    intro n E hEm hEn
    have hEfin : volume E ≠ ⊤ := (measure_mono hEn).trans_lt measure_closedBall_lt_top |>.ne
    set g := fl hΩm hΩ hEn hΩR with hg
    have hconst : ∀ j, ∫ y, g y * d6 (F j) y = volume.real E * volume.real Ω := by
      intro j
      have hC : ∀ y, |d6 (F j) y| ≤ (F j).card := fun y => by
        rw [abs_of_nonneg (d7 _ y)]; exact d9 _ y
      calc ∫ y, g y * d6 (F j) y = ∫ y, d6 (F j) y * xcorr E Ω y := by
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            show xcorr E Ω y * d6 (F j) y = _
            ring
        _ = ∫ x in E, ∫ z in Ω, d6 (F j) (x - z) :=
            fk hEfin hΩm hΩ (d8 _) hC
        _ = ∫ x in E, volume.real Ω := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_)
            exact eg hΩ horth (hF j) (hFne j) x
        _ = volume.real E * volume.real Ω := by
            rw [setIntegral_const, smul_eq_mul]
    have hlim : ∫ y, g y ∂ν = volume.real E * volume.real Ω := by
      have h1 := hν g
      simp_rw [hconst] at h1
      exact tendsto_nhds_unique h1 tendsto_const_nhds
    have hswap : ∫⁻ x in E, ν {y | x - y ∈ Ω} = ∫⁻ y, ENNReal.ofReal (xcorr E Ω y) ∂ν := by
      have hi : ∀ x, ν {y | x - y ∈ Ω} = ∫⁻ y, S.indicator 1 (x, y) ∂ν := by
        intro x
        have hmx : MeasurableSet {y : Fin d → ℝ | x - y ∈ Ω} :=
          hΩm.preimage (measurable_const.sub measurable_id)
        rw [← lintegral_indicator_one hmx]
        rfl
      simp_rw [hi]
      rw [lintegral_lintegral_swap
        (f := fun x y => S.indicator (1 : (Fin d → ℝ) × (Fin d → ℝ) → ENNReal) (x, y))
        ((measurable_one.indicator hSm).aemeasurable)]
      refine lintegral_congr fun y => ?_
      have hy : (fun x => S.indicator (1 : (Fin d → ℝ) × (Fin d → ℝ) → ENNReal) (x, y)) =
          {x | x - y ∈ Ω}.indicator 1 := rfl
      have hmy : MeasurableSet {x : Fin d → ℝ | x - y ∈ Ω} :=
        hΩm.preimage (measurable_id.sub measurable_const)
      rw [hy, lintegral_indicator_one hmy, Measure.restrict_apply hmy, xcorr, measureReal_def, ENNReal.ofReal_toReal, Set.inter_comm]
      exact measure_ne_top_of_subset Set.inter_subset_right (by
        rw [em hΩm]; exact hΩ)
    have zb : Integrable (fun y => g y) ν :=
      g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
    rw [hswap]
    have : ∫⁻ y, ENNReal.ofReal (xcorr E Ω y) ∂ν = ENNReal.ofReal (∫ y, g y ∂ν) :=
      (ofReal_integral_eq_lintegral_ofReal zb
        (Eventually.of_forall fun y => el E Ω y)).symm
    rw [this, hlim, ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal hEfin, ofReal_measureReal hΩ]
  have hloc : ∀ n : ℕ, ∀ᵐ x ∂volume.restrict (closedBall (0 : Fin d → ℝ) n),
      ν {y | x - y ∈ Ω} = volume Ω := by
    intro n
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hmeas measurable_const
      fun s hs _ => ?_
    rw [Measure.restrict_restrict hs, setLIntegral_const, mul_comm]
    exact za n _ (hs.inter measurableSet_closedBall) Set.inter_subset_right
  have hall : ∀ᵐ x ∂volume.restrict (⋃ n : ℕ, closedBall (0 : Fin d → ℝ) n),
      ν {y | x - y ∈ Ω} = volume Ω :=
    (ae_restrict_iUnion_iff _ _).mpr hloc
  rwa [iUnion_closedBall_nat, Measure.restrict_univ] at hall
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate CompactlySupported Classical
namespace FCBridge
variable {d : ℕ}
noncomputable def fo {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤)
    {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (L : ℝ) : C_c(Fin d → ℝ, ℝ) :=
  ⟨⟨fun y => (eB L y).re * xcorr Ω Ω y,
    (Complex.continuous_re.comp (eH L)).mul (continuous_xcorr Ω hΩm hΩ)⟩,
    (er hΩR hΩR).mul_left⟩
lemma fq {Ω : Set (Fin d → ℝ)} (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤)
    {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (L : ℝ) (y : Fin d → ℝ) :
    fo hΩm hΩ hΩR L y = (eB L y).re * xcorr Ω Ω y := rfl
lemma fs (Ω : Set (Fin d → ℝ)) : xcorr Ω Ω 0 = volume.real Ω := by
  simp [xcorr]
lemma ft {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (hΩm : MeasurableSet Ω) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) {δ : ℝ} (hδ : 0 < δ) (hΛ : cc δ Λ) {R : ℕ → ℝ} (hRpos : ∀ j, 0 < et Λ (R j)) (hRshell : ∀ j : ℕ, (et Λ (R j) : ℝ) - et Λ (R j - ((j : ℝ) + 1)) ≤ et Λ (R j) / ((j : ℝ) + 2)) {ν : Measure (Fin d → ℝ)} [ν.Regular] (hν : ∀ φ : C_c(Fin d → ℝ, ℝ), Tendsto (fun j => ∫ y, φ y * d6 (eU hδ hΛ (R j)) y) (hyperfilter ℕ) (𝓝 (∫ y, φ y ∂ν))) : ν {0} = volume Ω := by
  have hh := h
  obtain ⟨-, hpos, hΩ, -⟩ := hh
  have hvol : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  set φ : ℕ → C_c(Fin d → ℝ, ℝ) := fun n => fo hΩm hΩ hΩR ((n : ℝ) + 1) with hφ
  have za : ∀ n, ∫ y, φ n y ∂ν = volume.real Ω ^ 2 := by
    intro n
    have h1 := hν (φ n)
    have h2 := fd h hΩm hΩR hδ hΛ (L := (n : ℝ) + 1) (by positivity) hRpos
      hRshell
    have hU : (↑(hyperfilter ℕ) : Filter ℕ) ≤ atTop :=
      (hyperfilter_le_cofinite).trans Nat.cofinite_eq_atTop.le
    exact tendsto_nhds_unique h1 (h2.mono_left hU)
  have zb : Integrable (fun y => xcorr Ω Ω y) ν :=
    (continuous_xcorr Ω hΩm hΩ).integrable_of_hasCompactSupport (er hΩR hΩR)
  have zc := tendsto_integral_of_dominated_convergence (μ := ν) (F := fun n y => φ n y)
    (f := ({0} : Set (Fin d → ℝ)).indicator fun _ => volume.real Ω) (fun y => xcorr Ω Ω y)
    (fun n => (φ n).continuous.aestronglyMeasurable) zb
    (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · simp_rw [za] at zc
    have hlim := tendsto_nhds_unique tendsto_const_nhds zc
    rw [integral_indicator_const _ (measurableSet_singleton 0), smul_eq_mul] at hlim
    have zd : ν.real {0} = volume.real Ω := by
      have : volume.real Ω * volume.real Ω = ν.real {0} * volume.real Ω := by rw [← hlim]; ring
      exact (mul_right_cancel₀ hvol.ne' this).symm
    have hfin : ν {0} ≠ ⊤ := (isCompact_singleton (x := (0 : Fin d → ℝ))).measure_lt_top.ne
    rw [← ofReal_measureReal hfin, zd, ofReal_measureReal hΩ]
  ·
    rw [hφ, fq, norm_mul, Real.norm_of_nonneg (el Ω Ω y)]
    calc ‖(eB ((n : ℝ) + 1) y).re‖ * xcorr Ω Ω y ≤ 1 * xcorr Ω Ω y := by
          gcongr
          · exact el Ω Ω y
          · rw [Real.norm_eq_abs]
            exact (Complex.abs_re_le_norm _).trans (eG (by positivity) y)
      _ = xcorr Ω Ω y := one_mul _
  ·
    by_cases hy : y = 0
    · subst hy
      have hconst : ∀ n : ℕ, φ n 0 = volume.real Ω := by
        intro n
        rw [hφ, fq, eE (by positivity), Complex.one_re, one_mul, fs]
      rw [Set.indicator_of_mem (Set.mem_singleton (0 : Fin d → ℝ))]
      simp only [hconst]
      exact tendsto_const_nhds
    · rw [Set.indicator_of_notMem (show y ∉ ({0} : Set (Fin d → ℝ)) from hy)]
      have hc := (Complex.continuous_re.tendsto 0).comp (eK hy)
      rw [Complex.zero_re] at hc
      have := hc.mul_const (xcorr Ω Ω y)
      rw [zero_mul] at this
      simpa [hφ, fq, Function.comp_def] using this
lemma fu {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) : Λ.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  subst hne
  have hs := aR h 0
  have h0 : volume.real Ω ^ 2 = 0 := hs.unique hasSum_empty
  obtain ⟨-, hpos, hΩ, -⟩ := h
  have : 0 < volume.real Ω := ENNReal.toReal_pos hpos.ne' hΩ
  exact (pow_pos this 2).ne' h0
lemma fv {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) : ∃ μ : Measure (Fin d → ℝ), IsFiniteMeasureOnCompacts μ ∧ ∀ᵐ x, μ {t | x - t ∈ Ω} = Ωᶜ.indicator 1 x := by
  have hh := h
  obtain ⟨-, hpos, hΩ, -⟩ := hh
  obtain ⟨-, -, -, horth, -⟩ := al.mp h
  obtain ⟨δ, hδ, hsep⟩ := aI.separated hΩ hpos
  have hΛ := hsep Λ horth
  obtain ⟨R₀, hΩR⟩ := hΩb.subset_closedBall 0
  obtain ⟨R, -, hRpos, hRshell⟩ := e9 hδ hΛ (fu h)
  have hFne : ∀ j, (eU hδ hΛ (R j)).Nonempty := fun j => by
    rw [← Finset.card_pos, eX]; exact hRpos j
  obtain ⟨ν, hνreg, hν⟩ := fj hΩm hΩ hpos hΩR horth
    (fun j => eU hδ hΛ (R j)) (fun j => eY hδ hΛ (R j)) hFne
  have hP1 := fn hΩm hΩ hΩR horth (fun j => eU hδ hΛ (R j))
    (fun j => eY hδ hΛ (R j)) hFne hν
  have hatom := ft h hΩm hΩR hδ hΛ hRpos hRshell hν
  refine ⟨(volume Ω)⁻¹ • ν.restrict {0}ᶜ, ⟨fun K hK => ?_⟩, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr hpos)
      ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)
  · filter_upwards [hP1] with x hx
    have hSm : MeasurableSet {t : Fin d → ℝ | x - t ∈ Ω} :=
      hΩm.preimage (measurable_const.sub measurable_id)
    have za : ν ({t : Fin d → ℝ | x - t ∈ Ω} ∩ {0}) ≠ ⊤ :=
      measure_ne_top_of_subset Set.inter_subset_right
        (isCompact_singleton (x := (0 : Fin d → ℝ))).measure_lt_top.ne
    have hdiff : {t : Fin d → ℝ | x - t ∈ Ω} ∩ {0}ᶜ =
        {t | x - t ∈ Ω} \ ({t | x - t ∈ Ω} ∩ {0}) := by
      ext t; simp
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hSm, hdiff, measure_sdiff Set.inter_subset_left (hSm.inter (measurableSet_singleton 0)).nullMeasurableSet za, hx]
    by_cases hxΩ : x ∈ Ω
    · have h0 : {t : Fin d → ℝ | x - t ∈ Ω} ∩ {0} = {0} := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨-, ht⟩; exact ht
        · rintro rfl; exact ⟨by simpa using hxΩ, rfl⟩
      rw [h0, hatom, tsub_self, mul_zero, Set.indicator_of_notMem (by simpa using hxΩ)]
    · have h0 : {t : Fin d → ℝ | x - t ∈ Ω} ∩ {0} = ∅ := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro ht h0
        subst h0
        exact hxΩ (by simpa using ht)
      rw [h0, measure_empty, tsub_zero, ENNReal.inv_mul_cancel hpos.ne' hΩ, Set.indicator_of_mem (by simpa using hxΩ), Pi.one_apply]
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
namespace FCBridge
section Product
variable {n m : ℕ}
lemma ae_ae_of_ae_append' {P : (Fin (n + m) → ℝ) → Prop} (h : ∀ᵐ z ∂volume, P z) : ∀ᵐ y ∂(volume : Measure (Fin m → ℝ)), ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), P (Fin.append x y) := by
  have h1 : ∀ᵐ p ∂(volume : Measure ((Fin n → ℝ) × (Fin m → ℝ))),
      P ((am n m).symm p) :=
    ((an n m).symm _).quasiMeasurePreserving.ae h
  rw [Measure.volume_eq_prod] at h1
  have h2 : ∀ᵐ q ∂((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin n → ℝ))),
      P ((am n m).symm q.swap) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure (Fin m → ℝ)))
      (ν := (volume : Measure (Fin n → ℝ)))).quasiMeasurePreserving.ae h1
  filter_upwards [Measure.ae_ae_of_ae_prod h2] with y hy
  filter_upwards [hy] with x hx
  rwa [Prod.swap_prod_mk, bn] at hx
lemma fw {z : Fin (n + m) → ℝ} {r : ℝ} (h1 : ‖proj₁ z‖ ≤ r) (h2 : ‖proj₂ z‖ ≤ r) : ‖z‖ ≤ r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans h1
  refine (pi_norm_le_iff_of_nonneg hr).mpr fun k => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact (norm_le_pi_norm (proj₁ z) i).trans h1
  · exact (norm_le_pi_norm (proj₂ z) j).trans h2
lemma fx {K : Set (Fin n → ℝ)} (hK : IsCompact K) {c : Fin m → ℝ} (r : ℝ) : IsCompact {t : Fin (n + m) → ℝ | proj₁ t ∈ K ∧ proj₂ t ∈ closedBall c r} := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (hK.isClosed.preimage continuous_proj₁).inter
      (isClosed_closedBall.preimage continuous_proj₂)
  · refine (isBounded_closedBall (x := (0 : Fin (n + m) → ℝ)) (r := max R (‖c‖ + r))).subset
      fun t ⟨ht1, ht2⟩ => ?_
    rw [mem_closedBall_zero_iff]
    refine fw ?_ ?_
    · exact (mem_closedBall_zero_iff.mp (hR ht1)).trans (le_max_left _ _)
    · have : ‖proj₂ t - c‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.mp ht2
      calc ‖proj₂ t‖ = ‖(proj₂ t - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖proj₂ t - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ ‖c‖ + r := by linarith
        _ ≤ max R (‖c‖ + r) := le_max_right _ _
lemma fy {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)} (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B) (hBpos : 0 < volume B) {μ : Measure (Fin (n + m) → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ z, μ {t | z - t ∈ productSet A B} = (productSet A B)ᶜ.indicator 1 z) : ∃ μA : Measure (Fin n → ℝ), IsFiniteMeasureOnCompacts μA ∧ ∀ᵐ x, μA {s | x - s ∈ A} = Aᶜ.indicator 1 x := by
  have h2 := ae_ae_of_ae_append' hμ
  obtain ⟨y, hyB, hy⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hBpos.ne'
    (ae_restrict_of_ae h2)
  set S : Set (Fin (n + m) → ℝ) := {t | y - proj₂ t ∈ B} with hS
  have hSm : MeasurableSet S := hBm.preimage (measurable_const.sub measurable_proj₂)
  refine ⟨Measure.map proj₁ (μ.restrict S), ⟨fun K hK => ?_⟩, ?_⟩
  · obtain ⟨r, hr⟩ := hBb.subset_closedBall 0
    rw [Measure.map_apply measurable_proj₁ hK.isClosed.measurableSet, Measure.restrict_apply (hK.isClosed.measurableSet.preimage measurable_proj₁)]
    have hsub : proj₁ ⁻¹' K ∩ S ⊆
        {t : Fin (n + m) → ℝ | proj₁ t ∈ K ∧ proj₂ t ∈ closedBall y r} := by
      rintro t ⟨ht1, ht2⟩
      refine ⟨ht1, ?_⟩
      have h := mem_closedBall_zero_iff.mp (hr ht2)
      rw [mem_closedBall, dist_eq_norm]
      calc ‖proj₂ t - y‖ = ‖y - proj₂ t‖ := norm_sub_rev _ _
        _ ≤ r := h
    exact (measure_mono hsub).trans_lt (fx hK (c := y) r).measure_lt_top
  · filter_upwards [hy] with x hx
    have hxm : MeasurableSet {s : Fin n → ℝ | x - s ∈ A} :=
      hAm.preimage (measurable_const.sub measurable_id)
    rw [Measure.map_apply measurable_proj₁ hxm, Measure.restrict_apply (hxm.preimage measurable_proj₁)]
    have hset : proj₁ ⁻¹' {s | x - s ∈ A} ∩ S = {t | Fin.append x y - t ∈ productSet A B} := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hS, productSet]
      rw [show (fun i => (Fin.append x y - t) (Fin.castAdd m i)) = x - proj₁ t from by
          funext i; simp [proj₁],
        show (fun j => (Fin.append x y - t) (Fin.natAdd n j)) = y - proj₂ t from by
          funext j; simp [proj₂]]
    rw [hset, hx]
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_notMem (by
          simp only [Set.mem_compl_iff, not_not, productSet, Set.mem_ofPred_eq]
          exact ⟨by simpa using hxA, by simpa using hyB⟩),
        Set.indicator_of_notMem (by simpa using hxA)]
    · rw [Set.indicator_of_mem (by
          simp only [Set.mem_compl_iff, productSet, Set.mem_ofPred_eq, not_and]
          intro h; exact absurd (by simpa using h) hxA),
        Set.indicator_of_mem (by simpa using hxA)]
      rfl
end Product
lemma exists_weakTiling_left_of_isSpectral_productSet {n m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)} (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A) (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B) (hspec : isSpectral (productSet A B)) : ∃ μA : Measure (Fin n → ℝ), IsFiniteMeasureOnCompacts μA ∧ ∀ᵐ x, μA {s | x - s ∈ A} = Aᶜ.indicator 1 x := by
  obtain ⟨Λ, hΛ⟩ := hspec
  obtain ⟨-, hBpos⟩ := aq ⟨Λ, hΛ⟩
  obtain ⟨μ, hμc, hμ⟩ := fv hΛ (measurableSet_productSet hAm hBm)
    (isBounded_productSet hAb hBb)
  exact fy hAm hBm hBb hBpos hμ
end FCBridge
end
section
open MeasureTheory Filter Topology Metric
open scoped ComplexConjugate CompactlySupported Classical
namespace FCBridge
variable {d : ℕ}
lemma fz {Ω Λ : Set (Fin d → ℝ)} (h : spectralPair Ω Λ) (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) : ∃ (ν : Measure (Fin d → ℝ)) (F : ℕ → Finset (Fin d → ℝ)), ν.Regular ∧ (∀ j, (F j : Set (Fin d → ℝ)) ⊆ Λ) ∧ (∀ j, (F j).Nonempty) ∧ (∀ φ : C_c(Fin d → ℝ, ℝ), Tendsto (fun j => ∫ y, φ y * d6 (F j) y) (hyperfilter ℕ) (𝓝 (∫ y, φ y ∂ν))) ∧ ν {0} = volume Ω := by
  have hh := h
  obtain ⟨-, hpos, hΩ, -⟩ := hh
  obtain ⟨-, -, -, horth, -⟩ := al.mp h
  obtain ⟨δ, hδ, hsep⟩ := aI.separated hΩ hpos
  have hΛ := hsep Λ horth
  obtain ⟨R₀, hΩR⟩ := hΩb.subset_closedBall 0
  obtain ⟨R, -, hRpos, hRshell⟩ := e9 hδ hΛ (fu h)
  have hFne : ∀ j, (eU hδ hΛ (R j)).Nonempty := fun j => by
    rw [← Finset.card_pos, eX]; exact hRpos j
  obtain ⟨ν, hνreg, hν⟩ := fj hΩm hΩ hpos hΩR horth
    (fun j => eU hδ hΛ (R j)) (fun j => eY hδ hΛ (R j)) hFne
  exact ⟨ν, fun j => eU hδ hΛ (R j), hνreg, fun j => eY hδ hΛ (R j), hFne, hν,
    ft h hΩm hΩR hδ hΛ hRpos hRshell hν⟩
lemma fA {g : (Fin d → ℝ) → ℝ} (hg : Integrable g) {G : (Fin d → ℝ) → ℝ} (hG : ∀ ξ, ∫ y, (g y : ℂ) * exponentialCharacter ξ y = (G ξ : ℂ)) (hG0 : ∀ ξ, 0 ≤ G ξ) {F : Finset (Fin d → ℝ)} (hF : F.Nonempty) : G 0 ≤ ∫ y, g y * d6 F y := by
  have hc : (F.card : ℝ) ≠ 0 := by exact_mod_cast hF.card_pos.ne'
  have hint : ∀ ξ : Fin d → ℝ, Integrable fun y => (g y : ℂ) * exponentialCharacter ξ y := by
    intro ξ
    refine hg.norm.mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable).mul
        (continuous_exponentialCharacter ξ).aestronglyMeasurable
    · rw [norm_mul, norm_exponentialCharacter, mul_one, Complex.norm_real]
  have heq : ∫ y, g y * d6 F y = (F.card : ℝ)⁻¹ * ∑ l ∈ F, ∑ l' ∈ F, G (l' - l) := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    simp only [d6, Complex.ofReal_mul, Complex.ofReal_div, ec, Complex.ofReal_natCast]
    have e1 : ∀ y, (g y : ℂ) * ((∑ l ∈ F, ∑ l' ∈ F, exponentialCharacter (l' - l) y) /
        (F.card : ℂ)) = (F.card : ℂ)⁻¹ * ∑ l ∈ F, ∑ l' ∈ F,
          (g y : ℂ) * exponentialCharacter (l' - l) y := by
      intro y
      simp only [div_eq_inv_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
      ring
    simp_rw [e1]
    rw [integral_const_mul, integral_finsetSum _ fun l _ =>
      integrable_finsetSum _ fun l' _ => hint (l' - l)]
    simp_rw [integral_finsetSum _ fun l' _ => hint _, hG]
    push_cast
    rfl
  rw [heq]
  have hN : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  rw [le_inv_mul_iff₀ hN]
  calc (F.card : ℝ) * G 0 = ∑ l ∈ F, G (l - l) := by
        simp only [sub_self, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ l ∈ F, ∑ l' ∈ F, G (l' - l) :=
        Finset.sum_le_sum fun l hl =>
          Finset.single_le_sum (f := fun l' => G (l' - l)) (fun l' _ => hG0 _) hl
section Diffraction
variable {Ω Λ : Set (Fin d → ℝ)} {ν : Measure (Fin d → ℝ)} {F : ℕ → Finset (Fin d → ℝ)}
lemma fC (hFne : ∀ j, (F j).Nonempty)
    (hν : ∀ φ : C_c(Fin d → ℝ, ℝ), Tendsto (fun j => ∫ y, φ y * d6 (F j) y) (hyperfilter ℕ)
      (𝓝 (∫ y, φ y ∂ν)))
    (φ : C_c(Fin d → ℝ, ℝ)) {G : (Fin d → ℝ) → ℝ}
    (hG : ∀ ξ, ∫ y, (φ y : ℂ) * exponentialCharacter ξ y = (G ξ : ℂ)) (hG0 : ∀ ξ, 0 ≤ G ξ) :
    G 0 ≤ ∫ y, φ y ∂ν :=
  ge_of_tendsto (hν φ) (Eventually.of_forall fun j =>
    fA (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)
      hG hG0 (hFne j))
lemma fD (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (horth : aI Ω Λ) (hF : ∀ j, (F j : Set (Fin d → ℝ)) ⊆ Λ) (hFne : ∀ j, (F j).Nonempty) (hν : ∀ φ : C_c(Fin d → ℝ, ℝ), Tendsto (fun j => ∫ y, φ y * d6 (F j) y) (hyperfilter ℕ) (𝓝 (∫ y, φ y ∂ν))) : ∫ y, xcorr Ω Ω y ∂ν = volume.real Ω ^ 2 := by
  set g := fl hΩm hΩ hΩR hΩR with hg
  have hconst : ∀ j, ∫ y, g y * d6 (F j) y = volume.real Ω ^ 2 := by
    intro j
    have hC : ∀ y, |d6 (F j) y| ≤ (F j).card := fun y => by
      rw [abs_of_nonneg (d7 _ y)]; exact d9 _ y
    calc ∫ y, g y * d6 (F j) y = ∫ y, d6 (F j) y * xcorr Ω Ω y := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          show xcorr Ω Ω y * d6 (F j) y = _
          ring
      _ = ∫ x in Ω, ∫ z in Ω, d6 (F j) (x - z) :=
          fk hΩ hΩm hΩ (d8 _) hC
      _ = ∫ x in Ω, volume.real Ω := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          exact eg hΩ horth (hF j) (hFne j) x
      _ = volume.real Ω ^ 2 := by rw [setIntegral_const, smul_eq_mul, sq]
  have h1 := hν g
  simp_rw [hconst] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds
lemma fE [ν.Regular] (hΩm : MeasurableSet Ω) (hΩ : volume Ω ≠ ⊤) {R₀ : ℝ} (hΩR : Ω ⊆ closedBall 0 R₀) (hint : ∫ y, xcorr Ω Ω y ∂ν = volume.real Ω ^ 2) (hatom : ν {0} = volume Ω) : ν ({y | 0 < xcorr Ω Ω y} \ {0}) = 0 := by
  have hcont := continuous_xcorr Ω hΩm hΩ
  have hxint : Integrable (fun y => xcorr Ω Ω y) ν :=
    hcont.integrable_of_hasCompactSupport (er hΩR hΩR)
  have hsplit := integral_add_compl (μ := ν) (measurableSet_singleton (0 : Fin d → ℝ)) hxint
  rw [integral_singleton, fs, measureReal_def, hatom, hint, smul_eq_mul] at hsplit
  have za : ∫ y in ({0} : Set (Fin d → ℝ))ᶜ, xcorr Ω Ω y ∂ν = 0 := by
    have : (volume Ω).toReal = volume.real Ω := rfl
    rw [this] at hsplit
    nlinarith
  have hzero := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun y => el Ω Ω y) hxint.integrableOn).mp za
  have hm : MeasurableSet {y : Fin d → ℝ | 0 < xcorr Ω Ω y} :=
    measurableSet_lt measurable_const hcont.measurable
  rw [EventuallyEq, ae_restrict_iff' (measurableSet_singleton 0).compl] at hzero
  refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hzero)
  obtain ⟨hy, hy0⟩ := hy
  have hy' : 0 < xcorr Ω Ω y := hy
  intro h
  have h' := h hy0
  simp only [Pi.zero_apply] at h'
  linarith
lemma fF (hnull : ν ({y | 0 < xcorr Ω Ω y} \ {0}) = 0) (hatom : ν {0} = volume Ω) (g : C_c(Fin d → ℝ, ℝ)) (hg : ∀ y, g y ≠ 0 → 0 < xcorr Ω Ω y) : ∫ y, g y ∂ν = g 0 * volume.real Ω := by
  have hae : (fun y => g y) =ᵐ[ν] ({0} : Set (Fin d → ℝ)).indicator (fun y => g y) := by
    refine measure_mono_null (fun y hy => ?_) hnull
    have hy' : g y ≠ ({0} : Set (Fin d → ℝ)).indicator (fun y => g y) y := hy
    by_cases h0 : y = 0
    · subst h0; simp at hy'
    · rw [Set.indicator_of_notMem (show y ∉ ({0} : Set (Fin d → ℝ)) from h0)] at hy'
      exact ⟨hg y hy', h0⟩
  rw [integral_congr_ae hae, integral_indicator (measurableSet_singleton 0), integral_singleton, measureReal_def, hatom, smul_eq_mul, mul_comm]
  rfl
end Diffraction
section Product
variable {n m : ℕ}
lemma fG (A : Set (Fin n → ℝ)) (B : Set (Fin m → ℝ)) (z : Fin (n + m) → ℝ) : xcorr (productSet A B) (productSet A B) z = xcorr A A (proj₁ z) * xcorr B B (proj₂ z) := by
  have hset : productSet A B ∩ {x | x - z ∈ productSet A B} =
      productSet (A ∩ {a | a - proj₁ z ∈ A}) (B ∩ {b | b - proj₂ z ∈ B}) := by
    ext x
    simp only [productSet, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
  rw [xcorr, hset, measureReal_def, ap, ENNReal.toReal_mul]
  rfl
lemma fH (Φ : (Fin n → ℝ) → ℂ) (Ψ : (Fin m → ℝ) → ℂ) : ∫ z, Φ (proj₁ z) * Ψ (proj₂ z) = (∫ x, Φ x) * ∫ y, Ψ y := by
  have key := (an n m).integral_comp
    (am n m).measurableEmbedding (fun p => Φ p.1 * Ψ p.2)
  simp only [splitEquiv_apply'] at key
  rw [key, Measure.volume_eq_prod]
  exact integral_prod_mul Φ Ψ
lemma fI (ξ z : Fin (n + m) → ℝ) : exponentialCharacter ξ z = exponentialCharacter (proj₁ ξ) (proj₁ z) * exponentialCharacter (proj₂ ξ) (proj₂ z) := by
  have hξ : ξ = Fin.append (proj₁ ξ) (proj₂ ξ) := Fin.append_castAdd_natAdd.symm
  conv_lhs => rw [hξ]
  rw [ar]
  rfl
lemma fJ {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)} (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A) (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B) (hspec : isSpectral (productSet A B)) {E : Set (Fin n → ℝ)} (hEm : MeasurableSet E) (hEb : Bornology.IsBounded E) (hE : ∀ z, 0 < xcorr E E z → 0 < xcorr A A z) : volume E ≤ volume A := by
  have hspec' := hspec
  obtain ⟨Λ, hΛ⟩ := hspec'
  have hΩm := measurableSet_productSet hAm hBm
  have hΩb := isBounded_productSet hAb hBb
  obtain ⟨ν, F, hνreg, hF, hFne, hν, hatom⟩ := fz hΛ hΩm hΩb
  have hΩ : volume (productSet A B) ≠ ⊤ := hΩb.measure_lt_top.ne
  obtain ⟨R₀, hΩR⟩ := hΩb.subset_closedBall 0
  obtain ⟨-, -, -, horth, -⟩ := al.mp hΛ
  have hint := fD hΩm hΩ hΩR horth hF hFne hν
  have hnull := fE hΩm hΩ hΩR hint hatom
  have hEfin : volume E ≠ ⊤ := hEb.measure_lt_top.ne
  have hBfin : volume B ≠ ⊤ := hBb.measure_lt_top.ne
  have hAfin : volume A ≠ ⊤ := hAb.measure_lt_top.ne
  obtain ⟨-, hBpos⟩ := aq hspec
  obtain ⟨RE, hRE⟩ := hEb.subset_closedBall 0
  obtain ⟨RB, hRB⟩ := hBb.subset_closedBall 0
  have hgc : Continuous fun z : Fin (n + m) → ℝ => xcorr E E (proj₁ z) * xcorr B B (proj₂ z) :=
    ((continuous_xcorr E hEm hEfin).comp continuous_proj₁).mul
      ((continuous_xcorr B hBm hBfin).comp continuous_proj₂)
  have hgs : HasCompactSupport fun z : Fin (n + m) → ℝ =>
      xcorr E E (proj₁ z) * xcorr B B (proj₂ z) := by
    refine HasCompactSupport.intro (isCompact_closedBall 0 (max (RE + RE) (RB + RB)))
      fun z hz => ?_
    rw [mem_closedBall_zero_iff, not_le] at hz
    by_cases h1 : ‖proj₁ z‖ ≤ max (RE + RE) (RB + RB)
    · have h2 : ¬ ‖proj₂ z‖ ≤ max (RE + RE) (RB + RB) := fun h2 =>
        (not_le.mpr hz) (fw h1 h2)
      rw [ep hRB hRB (lt_of_le_of_lt (le_max_right _ _) (not_le.mp h2)), mul_zero]
    · rw [ep hRE hRE (lt_of_le_of_lt (le_max_left _ _) (not_le.mp h1)),
        zero_mul]
  let g : C_c(Fin (n + m) → ℝ, ℝ) := ⟨⟨_, hgc⟩, hgs⟩
  have za : ∀ z, g z = xcorr E E (proj₁ z) * xcorr B B (proj₂ z) := fun z => rfl
  set G : (Fin (n + m) → ℝ) → ℝ := fun ξ =>
    ‖aa E (proj₁ ξ)‖ ^ 2 * ‖aa B (proj₂ ξ)‖ ^ 2 with hGdef
  have hG : ∀ ξ, ∫ z, (g z : ℂ) * exponentialCharacter ξ z = (G ξ : ℂ) := by
    intro ξ
    have hpt : ∀ z, (g z : ℂ) * exponentialCharacter ξ z =
        ((xcorr E E (proj₁ z) : ℂ) * exponentialCharacter (proj₁ ξ) (proj₁ z)) *
          ((xcorr B B (proj₂ z) : ℂ) * exponentialCharacter (proj₂ ξ) (proj₂ z)) := by
      intro z
      rw [za, fI]
      push_cast
      ring
    simp_rw [hpt]
    rw [fH (fun x => (xcorr E E x : ℂ) * exponentialCharacter (proj₁ ξ) x) (fun y => (xcorr B B y : ℂ) * exponentialCharacter (proj₂ ξ) y)]
    have hE' : ∫ x, (xcorr E E x : ℂ) * exponentialCharacter (proj₁ ξ) x =
        ((‖aa E (proj₁ ξ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [← eL hEm hEfin (proj₁ ξ)]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have hB' : ∫ y, (xcorr B B y : ℂ) * exponentialCharacter (proj₂ ξ) y =
        ((‖aa B (proj₂ ξ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [← eL hBm hBfin (proj₂ ξ)]
      exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    rw [hE', hB', hGdef]
    push_cast
    ring
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by positivity
  have hlow := fC hFne hν g hG hG0
  have hsupp : ∀ z, g z ≠ 0 → 0 < xcorr (productSet A B) (productSet A B) z := by
    intro z hz
    rw [za] at hz
    rw [fG]
    have h1 : xcorr E E (proj₁ z) ≠ 0 := left_ne_zero_of_mul hz
    have h2 : xcorr B B (proj₂ z) ≠ 0 := right_ne_zero_of_mul hz
    exact mul_pos (hE _ (lt_of_le_of_ne (el _ _ _) (Ne.symm h1)))
      (lt_of_le_of_ne (el _ _ _) (Ne.symm h2))
  have zb := fF hnull hatom g hsupp
  have zc : G 0 = volume.real E ^ 2 * volume.real B ^ 2 := by
    simp only [hGdef]
    rw [show proj₁ (0 : Fin (n + m) → ℝ) = 0 from rfl, show proj₂ (0 : Fin (n + m) → ℝ) = 0 from rfl, aj, aj, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg, Real.norm_of_nonneg measureReal_nonneg]
  have hg0 : g 0 = volume.real E * volume.real B := by
    rw [za, show proj₁ (0 : Fin (n + m) → ℝ) = 0 from rfl, show proj₂ (0 : Fin (n + m) → ℝ) = 0 from rfl, fs, fs]
  have hΩr : volume.real (productSet A B) = volume.real A * volume.real B := by
    rw [measureReal_def, ap, ENNReal.toReal_mul]; rfl
  rw [zb, zc, hg0, hΩr] at hlow
  have hBr : 0 < volume.real B := ENNReal.toReal_pos hBpos.ne' hBfin
  have hEr : 0 ≤ volume.real E := measureReal_nonneg
  have hkey : volume.real E ≤ volume.real A := by
    rcases hEr.lt_or_eq with hEpos | hE0
    · have h3 : volume.real E * volume.real B * (volume.real E * volume.real B) ≤
          volume.real E * volume.real B * (volume.real A * volume.real B) := by nlinarith
      have h4 := le_of_mul_le_mul_left h3 (by positivity)
      exact le_of_mul_le_mul_right h4 hBr
    · rw [← hE0]; exact measureReal_nonneg
  rw [← ofReal_measureReal hEfin, ← ofReal_measureReal hAfin]
  exact ENNReal.ofReal_le_ofReal hkey
end Product
end FCBridge
end
section
open MeasureTheory Filter Topology Set
namespace Transport
structure Density (f : ℝ → ℝ) (a b : ℝ) : Prop where
  lt : a < b
  meas : Measurable f
  nonneg : ∀ t, 0 ≤ f t
  pos : ∀ t ∈ Ioo a b, 0 < f t
  cont : ContinuousOn f (Ioo a b)
  bdd : ∃ C, ∀ t, f t ≤ C
noncomputable def fK (f : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ u in a..x, f u
noncomputable def mass (f : ℝ → ℝ) (a b : ℝ) : ℝ := ∫ u in a..b, f u
namespace Density
variable {f : ℝ → ℝ} {a b : ℝ} (hf : Density f a b)
include hf
lemma intervalIntegrable (x y : ℝ) : IntervalIntegrable f volume x y := by
  obtain ⟨C, hC⟩ := hf.bdd
  refine (intervalIntegrable_const (c := C)).mono_fun' hf.meas.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  show ‖f t‖ ≤ C
  rw [Real.norm_of_nonneg (hf.nonneg t)]; exact hC t
lemma cdf_sub {x y : ℝ} : fK f a y - fK f a x = ∫ u in x..y, f u := by
  rw [fK, fK, intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
lemma cdf_strictMonoOn : StrictMonoOn (fK f a) (Icc a b) := by
  intro x hx y hy hxy
  rw [← sub_pos, hf.cdf_sub]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable _ _)
    (fun t ht => hf.pos t ⟨lt_of_le_of_lt hx.1 ht.1, lt_of_lt_of_le ht.2 hy.2⟩) hxy
lemma mass_pos : 0 < mass f a b :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hf.intervalIntegrable _ _) hf.pos hf.lt
omit hf in
lemma fL : fK f a a = 0 := intervalIntegral.integral_same
omit hf in
lemma fM : fK f a b = mass f a b := rfl
lemma continuous_cdf : Continuous (fK f a) := by
  exact intervalIntegral.continuous_primitive (fun x y => hf.intervalIntegrable x y) a
lemma hasDerivAt_cdf {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt (fK f a) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
    (hf.cont.stronglyMeasurableAtFilter isOpen_Ioo t ht)
    (hf.cont.continuousAt (isOpen_Ioo.mem_nhds ht))
lemma exists_cdf_eq {y : ℝ} (hy : y ∈ Ioo 0 (mass f a b)) : ∃ x ∈ Ioo a b, fK f a x = y := by
  have h := intermediate_value_Ioo hf.lt.le hf.continuous_cdf.continuousOn
  rw [fL, fM] at h
  exact h hy
noncomputable def qtl (y : ℝ) : ℝ :=
  if h : y ∈ Ioo 0 (mass f a b) then Classical.choose (hf.exists_cdf_eq h) else a
lemma qtl_mem {y : ℝ} (hy : y ∈ Ioo 0 (mass f a b)) : hf.qtl y ∈ Ioo a b := by
  rw [qtl, dif_pos hy]; exact (Classical.choose_spec (hf.exists_cdf_eq hy)).1
lemma cdf_qtl {y : ℝ} (hy : y ∈ Ioo 0 (mass f a b)) : fK f a (hf.qtl y) = y := by
  rw [qtl, dif_pos hy]; exact (Classical.choose_spec (hf.exists_cdf_eq hy)).2
lemma qtl_cdf {x : ℝ} (hx : x ∈ Ioo a b) : fK f a x ∈ Ioo 0 (mass f a b) ∧ hf.qtl (fK f a x) = x := by
  have h1 : fK f a x ∈ Ioo 0 (mass f a b) := by
    constructor
    · rw [← fL]
      exact hf.cdf_strictMonoOn (left_mem_Icc.mpr hf.lt.le) (Ioo_subset_Icc_self hx) hx.1
    · rw [← fM]
      exact hf.cdf_strictMonoOn (Ioo_subset_Icc_self hx) (right_mem_Icc.mpr hf.lt.le) hx.2
  refine ⟨h1, ?_⟩
  exact hf.cdf_strictMonoOn.injOn (Ioo_subset_Icc_self (hf.qtl_mem h1)) (Ioo_subset_Icc_self hx)
    (hf.cdf_qtl h1)
lemma qtl_strictMonoOn : StrictMonoOn hf.qtl (Ioo 0 (mass f a b)) := by
  intro y hy y' hy' hyy'
  have h1 := hf.qtl_mem hy
  have h2 := hf.qtl_mem hy'
  by_contra hle
  push Not at hle
  have := hf.cdf_strictMonoOn.monotoneOn (Ioo_subset_Icc_self h2) (Ioo_subset_Icc_self h1) hle
  rw [hf.cdf_qtl hy, hf.cdf_qtl hy'] at this
  linarith
lemma image_qtl : hf.qtl '' Ioo 0 (mass f a b) = Ioo a b := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hf.qtl_mem hy
  · intro hx
    obtain ⟨h1, h2⟩ := hf.qtl_cdf hx
    exact ⟨_, h1, h2⟩
lemma continuousAt_qtl {y : ℝ} (hy : y ∈ Ioo 0 (mass f a b)) : ContinuousAt hf.qtl y := by
  refine hf.qtl_strictMonoOn.continuousAt_of_image_mem_nhds (isOpen_Ioo.mem_nhds hy) ?_
  rw [hf.image_qtl]
  exact isOpen_Ioo.mem_nhds (hf.qtl_mem hy)
lemma hasDerivAt_qtl {y : ℝ} (hy : y ∈ Ioo 0 (mass f a b)) : HasDerivAt hf.qtl (f (hf.qtl y))⁻¹ y := by
  refine HasDerivAt.of_local_left_inverse (hf.continuousAt_qtl hy)
    (hf.hasDerivAt_cdf (hf.qtl_mem hy)) (hf.pos _ (hf.qtl_mem hy)).ne' ?_
  filter_upwards [isOpen_Ioo.mem_nhds hy] with y' hy'
  exact hf.cdf_qtl hy'
end Density
lemma fN {P Q x y : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hx : 0 < x) (hy : 0 < y) : Real.sqrt (P * Q) ≤ (P / x + Q / y) / 2 * Real.sqrt (x * y) := by
  have hu := Real.sqrt_nonneg (P / x)
  have hv := Real.sqrt_nonneg (Q / y)
  have hu2 : Real.sqrt (P / x) ^ 2 = P / x := Real.sq_sqrt (by positivity)
  have hv2 : Real.sqrt (Q / y) ^ 2 = Q / y := Real.sq_sqrt (by positivity)
  have hprod : Real.sqrt (P / x) * Real.sqrt (Q / y) * Real.sqrt (x * y) = Real.sqrt (P * Q) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have za : Real.sqrt (P / x) * Real.sqrt (Q / y) ≤ (P / x + Q / y) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt (P / x) - Real.sqrt (Q / y))]
  rw [← hprod]
  exact mul_le_mul_of_nonneg_right za (Real.sqrt_nonneg _)
lemma fO {P x y : ℝ} (hP : 0 < P) (hx : 0 < x) (hy : 0 < y) (h : (P / x + P / y) / 2 * Real.sqrt (x * y) = P) : x = y := by
  have hxy : 0 < x * y := mul_pos hx hy
  have hs := Real.sq_sqrt hxy.le
  have hs0 : 0 < Real.sqrt (x * y) := Real.sqrt_pos.mpr hxy
  have h2 : (x + y) / 2 = Real.sqrt (x * y) := by
    have : (P / x + P / y) / 2 * Real.sqrt (x * y) = P * ((x + y) / 2) / Real.sqrt (x * y) := by
      field_simp
      nlinarith [hs]
    rw [this, div_eq_iff hs0.ne'] at h
    nlinarith [hP]
  have h3 : (x - y) ^ 2 = 0 := by nlinarith [hs]
  nlinarith [sq_nonneg (x - y), pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h3]
lemma fP {M l : ℝ} (hM : 0 < M) (hl : l ∈ Ioo (0 : ℝ) 1) : l * M ∈ Ioo 0 M :=
  ⟨mul_pos hl.1 hM, by nlinarith [hl.2]⟩
lemma Density.hasDerivAt_qtl_mul {f : ℝ → ℝ} {a b : ℝ} (hf : Density f a b) {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) : HasDerivAt (fun l => hf.qtl (l * mass f a b)) (mass f a b / f (hf.qtl (l * mass f a b))) l := by
  have h1 := hf.hasDerivAt_qtl (fP hf.mass_pos hl)
  have h2 := (hasDerivAt_id l).mul_const (mass f a b)
  have := h1.comp l h2
  rw [show mass f a b / f (hf.qtl (l * mass f a b)) =
    (f (hf.qtl (l * mass f a b)))⁻¹ * (1 * mass f a b) by ring]
  exact this
lemma Density.continuousOn_qtl_mul {h : ℝ → ℝ} {c' e' : ℝ} (hh : Density h c' e') : ContinuousOn (fun l => hh.qtl (l * mass h c' e')) (Ioo 0 1) := by
  intro l hl
  have h1 : ContinuousAt (fun l : ℝ => l * mass h c' e') l := (continuous_mul_const _).continuousAt
  exact (ContinuousAt.comp (f := fun l : ℝ => l * mass h c' e')
    (hh.continuousAt_qtl (fP hh.mass_pos hl)) h1).continuousWithinAt
lemma Density.continuousOn_comp_qtl {h : ℝ → ℝ} {c' e' : ℝ} (hh : Density h c' e') :
    ContinuousOn (fun l => h (hh.qtl (l * mass h c' e'))) (Ioo 0 1) :=
  hh.cont.comp hh.continuousOn_qtl_mul fun _ hl => hh.qtl_mem (fP hh.mass_pos hl)
section Main
variable {f g : ℝ → ℝ} {a b c e : ℝ} (hf : Density f a b) (hg : Density g c e)
include hf hg
noncomputable def mid (l : ℝ) : ℝ :=
  (hf.qtl (l * mass f a b) + hg.qtl (l * mass g c e)) / 2
noncomputable def mid' (l : ℝ) : ℝ :=
  (mass f a b / f (hf.qtl (l * mass f a b)) + mass g c e / g (hg.qtl (l * mass g c e))) / 2
lemma fQ {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) : HasDerivAt (mid hf hg) (mid' hf hg l) l := by
  have h := ((hf.hasDerivAt_qtl_mul hl).add (hg.hasDerivAt_qtl_mul hl)).div_const 2
  exact h
lemma fR : StrictMonoOn (mid hf hg) (Ioo 0 1) := by
  intro l hl l' hl' hll'
  have h1 := hf.qtl_strictMonoOn (fP hf.mass_pos hl) (fP hf.mass_pos hl')
    (mul_lt_mul_of_pos_right hll' hf.mass_pos)
  have h2 := hg.qtl_strictMonoOn (fP hg.mass_pos hl) (fP hg.mass_pos hl')
    (mul_lt_mul_of_pos_right hll' hg.mass_pos)
  simp only [mid]
  linarith
lemma fS {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) : 0 < mid' hf hg l := by
  have h1 := hf.pos _ (hf.qtl_mem (fP hf.mass_pos hl))
  have h2 := hg.pos _ (hg.qtl_mem (fP hg.mass_pos hl))
  have := hf.mass_pos
  have := hg.mass_pos
  simp only [mid']
  positivity
lemma fT {l : ℝ} (hl : l ∈ Ioo (0 : ℝ) 1) :
    Real.sqrt (mass f a b * mass g c e) ≤ mid' hf hg l *
      Real.sqrt (f (hf.qtl (l * mass f a b)) * g (hg.qtl (l * mass g c e))) :=
  fN hf.mass_pos hg.mass_pos (hf.pos _ (hf.qtl_mem (fP hf.mass_pos hl)))
    (hg.pos _ (hg.qtl_mem (fP hg.mass_pos hl)))
lemma fU {H : ℝ → ENNReal} :
    ∫⁻ z in mid hf hg '' Ioo 0 1, H z =
      ∫⁻ l in Ioo 0 1, ENNReal.ofReal (|mid' hf hg l|) * H (mid hf hg l) :=
  lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun _ hl => (fQ hf hg hl).hasDerivWithinAt) (fR hf hg).injOn H
lemma transport_ineq {H : ℝ → ENNReal} (hHfg : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c e, ENNReal.ofReal (Real.sqrt (f t * g s)) ≤ H ((t + s) / 2)) : ENNReal.ofReal (Real.sqrt (mass f a b * mass g c e)) ≤ ∫⁻ z, H z := by
  calc ENNReal.ofReal (Real.sqrt (mass f a b * mass g c e))
      = ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (mass f a b * mass g c e)) := by
        rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
    _ ≤ ∫⁻ l in Ioo 0 1, ENNReal.ofReal (|mid' hf hg l|) * H (mid hf hg l) := by
        refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
        rw [abs_of_pos (fS hf hg hl)]
        calc ENNReal.ofReal (Real.sqrt (mass f a b * mass g c e))
            ≤ ENNReal.ofReal (mid' hf hg l * Real.sqrt (f (hf.qtl (l * mass f a b)) *
                g (hg.qtl (l * mass g c e)))) := ENNReal.ofReal_le_ofReal (fT hf hg hl)
          _ = ENNReal.ofReal (mid' hf hg l) * ENNReal.ofReal (Real.sqrt
                (f (hf.qtl (l * mass f a b)) * g (hg.qtl (l * mass g c e)))) :=
              ENNReal.ofReal_mul (fS hf hg hl).le
          _ ≤ ENNReal.ofReal (mid' hf hg l) * H (mid hf hg l) := by
              gcongr
              exact hHfg _ (hf.qtl_mem (fP hf.mass_pos hl)) _
                (hg.qtl_mem (fP hg.mass_pos hl))
    _ = ∫⁻ z in mid hf hg '' Ioo 0 1, H z := (fU hf hg).symm
    _ ≤ ∫⁻ z, H z := setLIntegral_le_lintegral _ _
lemma transport_eq {H : ℝ → ENNReal} (hHfg : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c e, ENNReal.ofReal (Real.sqrt (f t * g s)) ≤ H ((t + s) / 2)) (hMN : mass f a b = mass g c e) (hle : ∫⁻ z, H z ≤ ENNReal.ofReal (mass f a b)) : ∃ C, ∀ t ∈ Ioo a b, t - C ∈ Ioo c e ∧ f t = g (t - C) := by
  have za : 0 < mass f a b := hf.mass_pos
  have hTc : ContinuousOn (fun l => f (hf.qtl (l * mass f a b))) (Ioo 0 1) :=
    hf.continuousOn_comp_qtl
  have hSc : ContinuousOn (fun l => g (hg.qtl (l * mass g c e))) (Ioo 0 1) :=
    hg.continuousOn_comp_qtl
  have hφc : ContinuousOn (fun l => ENNReal.ofReal (mid' hf hg l *
      Real.sqrt (f (hf.qtl (l * mass f a b)) * g (hg.qtl (l * mass g c e))))) (Ioo 0 1) := by
    refine ENNReal.continuous_ofReal.comp_continuousOn ?_
    refine ContinuousOn.mul ?_ ((hTc.mul hSc).sqrt)
    refine (ContinuousOn.add ?_ ?_).div_const 2
    · exact continuousOn_const.div hTc fun l hl =>
        (hf.pos _ (hf.qtl_mem (fP hf.mass_pos hl))).ne'
    · exact continuousOn_const.div hSc fun l hl =>
        (hg.pos _ (hg.qtl_mem (fP hg.mass_pos hl))).ne'
  have hlow : ∀ l ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (mass f a b) ≤ ENNReal.ofReal (mid' hf hg l *
      Real.sqrt (f (hf.qtl (l * mass f a b)) * g (hg.qtl (l * mass g c e)))) := by
    intro l hl
    have h := fT hf hg hl
    have h' : Real.sqrt (mass f a b * mass g c e) = mass f a b := by
      rw [← hMN, Real.sqrt_mul_self za.le]
    rw [h'] at h
    exact ENNReal.ofReal_le_ofReal h
  have hconst : ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (mass f a b) = ENNReal.ofReal (mass f a b) := by
    rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
  have hup : ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (mid' hf hg l *
      Real.sqrt (f (hf.qtl (l * mass f a b)) * g (hg.qtl (l * mass g c e)))) ≤
      ∫⁻ _ in Ioo (0 : ℝ) 1, ENNReal.ofReal (mass f a b) := by
    rw [hconst]
    calc ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (mid' hf hg l *
          Real.sqrt (f (hf.qtl (l * mass f a b)) * g (hg.qtl (l * mass g c e))))
        ≤ ∫⁻ l in Ioo 0 1, ENNReal.ofReal (|mid' hf hg l|) * H (mid hf hg l) := by
          refine setLIntegral_mono' measurableSet_Ioo fun l hl => ?_
          rw [abs_of_pos (fS hf hg hl), ENNReal.ofReal_mul (fS hf hg hl).le]
          gcongr
          exact hHfg _ (hf.qtl_mem (fP hf.mass_pos hl)) _
            (hg.qtl_mem (fP hg.mass_pos hl))
      _ = ∫⁻ z in mid hf hg '' Ioo 0 1, H z := (fU hf hg).symm
      _ ≤ ∫⁻ z, H z := setLIntegral_le_lintegral _ _
      _ ≤ ENNReal.ofReal (mass f a b) := hle
  have hae : (fun _ => ENNReal.ofReal (mass f a b)) =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      (fun l => ENNReal.ofReal (mid' hf hg l *
        Real.sqrt (f (hf.qtl (l * mass f a b)) * g (hg.qtl (l * mass g c e))))) := by
    refine ae_eq_of_ae_le_of_lintegral_le ((ae_restrict_iff' measurableSet_Ioo).mpr
      (Eventually.of_forall hlow)) ?_ (hφc.aemeasurable measurableSet_Ioo) hup
    rw [hconst]; exact ENNReal.ofReal_ne_top
  have heq := Measure.eqOn_Ioo_of_ae_eq (volume : Measure ℝ) hae continuousOn_const hφc
  have hfg : ∀ l ∈ Ioo (0 : ℝ) 1,
      f (hf.qtl (l * mass f a b)) = g (hg.qtl (l * mass g c e)) := by
    intro l hl
    have h := heq hl
    have hx := hf.pos _ (hf.qtl_mem (fP hf.mass_pos hl))
    have hy := hg.pos _ (hg.qtl_mem (fP hg.mass_pos hl))
    simp only at h
    rw [ENNReal.ofReal_eq_ofReal_iff za.le (mul_nonneg (fS hf hg hl).le (Real.sqrt_nonneg _))] at h
    refine fO za hx hy ?_
    have h' := h.symm
    have hnum : mass g c e / g (hg.qtl (l * mass g c e)) =
        mass f a b / g (hg.qtl (l * mass g c e)) := by rw [hMN]
    rw [mid', hnum] at h'
    exact h'
  obtain ⟨C, hC⟩ := isOpen_Ioo.exists_eq_add_of_deriv_eq isPreconnected_Ioo
    (fun l hl => (hf.hasDerivAt_qtl_mul hl).differentiableAt.differentiableWithinAt)
    (fun l hl => (hg.hasDerivAt_qtl_mul hl).differentiableAt.differentiableWithinAt)
    (fun l hl => by
      rw [(hf.hasDerivAt_qtl_mul hl).deriv, (hg.hasDerivAt_qtl_mul hl).deriv, hfg l hl, hMN])
  refine ⟨C, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hf.qtl_cdf ht
  have hlmem : fK f a t / mass f a b ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos h1.1 za, (div_lt_one za).mpr h1.2⟩
  have hTl : hf.qtl (fK f a t / mass f a b * mass f a b) = t := by
    rw [div_mul_cancel₀ _ za.ne']; exact h2
  have hSl : hg.qtl (fK f a t / mass f a b * mass g c e) = t - C := by
    have := hC hlmem
    simp only at this
    rw [hTl] at this
    linarith
  refine ⟨?_, ?_⟩
  · rw [← hSl]
    exact hg.qtl_mem (fP hg.mass_pos hlmem)
  · have := hfg _ hlmem
    rw [hTl, hSl] at this
    exact this
end Main
end Transport
end
section
open MeasureTheory Filter Topology Metric Set
open scoped Pointwise
namespace FCBridge
variable {k : ℕ}
def sect (X : Set (Fin (k + 1) → ℝ)) (s : ℝ) : Set (Fin k → ℝ) := {y' | pt y' s ∈ X}
structure IsCB {n : ℕ} (X : Set (Fin n → ℝ)) : Prop where
  convex : Convex ℝ X
  compact : IsCompact X
  interior_nonempty : (interior X).Nonempty
lemma pt_add (y₁ y₂ : Fin k → ℝ) (s₁ s₂ : ℝ) : pt y₁ s₁ + pt y₂ s₂ = pt (y₁ + y₂) (s₁ + s₂) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [pt]
lemma fV (c : ℝ) (y : Fin k → ℝ) (s : ℝ) : c • pt y s = pt (c • y) (c * s) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [pt]
lemma fW (y : Fin k → ℝ) (s : ℝ) : -pt y s = pt (-y) (-s) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [pt]
lemma continuous_pt_left' (s : ℝ) : Continuous fun y' : Fin k → ℝ => pt y' s := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (motive := fun i => Continuous fun y' : Fin k → ℝ => pt y' s i)
    (fun i₁ => ?_) (fun i₂ => ?_) i
  · simp only [pt, Fin.append_left]; exact continuous_apply i₁
  · simp only [pt, Fin.append_right]; exact continuous_const
lemma fX {X : Set (Fin (k + 1) → ℝ)} (hX : MeasurableSet X) (s : ℝ) :
    MeasurableSet (sect X s) :=
  hX.preimage (continuous_pt_left' s).measurable
lemma measurePreserving_pt : MeasurePreserving (fun p : (Fin k → ℝ) × ℝ => pt p.1 p.2) (volume.prod volume) volume := by
  have h1 : MeasurePreserving (Prod.map id (MeasurableEquiv.funUnique (Fin 1) ℝ).symm)
      ((volume : Measure (Fin k → ℝ)).prod (volume : Measure ℝ))
      ((volume : Measure (Fin k → ℝ)).prod (volume : Measure (Fin 1 → ℝ))) :=
    (MeasurePreserving.id volume).prod (volume_preserving_funUnique (Fin 1) ℝ).symm
  have h2 : MeasurePreserving (am k 1).symm
      ((volume : Measure (Fin k → ℝ)).prod (volume : Measure (Fin 1 → ℝ))) volume := by
    rw [← Measure.volume_eq_prod]; exact (an k 1).symm
  have hsymm : ∀ s : ℝ, (MeasurableEquiv.funUnique (Fin 1) ℝ).symm s = fun _ => s :=
    fun s => (MeasurableEquiv.symm_apply_eq _).2 rfl
  have heq : (fun p : (Fin k → ℝ) × ℝ => pt p.1 p.2) =
      (am k 1).symm ∘ Prod.map id (MeasurableEquiv.funUnique (Fin 1) ℝ).symm := by
    funext p
    show Fin.append p.1 (fun _ => p.2) =
      (am k 1).symm (p.1, (MeasurableEquiv.funUnique (Fin 1) ℝ).symm p.2)
    rw [hsymm, bn]
  rw [heq]
  exact h2.comp h1
lemma fY {X : Set (Fin (k + 1) → ℝ)} (hX : MeasurableSet X) : volume X = ∫⁻ s, volume (sect X s) := by
  have hm : MeasurableSet ((fun p : (Fin k → ℝ) × ℝ => pt p.1 p.2) ⁻¹' X) :=
    hX.preimage measurePreserving_pt.measurable
  rw [← measurePreserving_pt.measure_preimage hX.nullMeasurableSet, Measure.prod_apply_symm hm]
  rfl
lemma fZ {X : Set (Fin (k + 1) → ℝ)} (hX : MeasurableSet X) : Measurable fun s => volume (sect X s) := by
  have hm : MeasurableSet ((fun p : (Fin k → ℝ) × ℝ => pt p.1 p.2) ⁻¹' X) :=
    hX.preimage measurePreserving_pt.measurable
  exact measurable_measure_prodMk_right hm
lemma f0 {X : Set (Fin (k + 1) → ℝ)} (hX : Convex ℝ X) (s : ℝ) : Convex ℝ (sect X s) := by
  intro y₁ hy₁ y₂ hy₂ θ₁ θ₂ hθ₁ hθ₂ hθ
  show pt (θ₁ • y₁ + θ₂ • y₂) s ∈ X
  have h := hX hy₁ hy₂ hθ₁ hθ₂ hθ
  rw [fV, fV, pt_add] at h
  convert h using 2
  rw [← add_mul, hθ, one_mul]
lemma f1 {X : Set (Fin (k + 1) → ℝ)} (hX : Bornology.IsBounded X) (s : ℝ) : Bornology.IsBounded (sect X s) := by
  obtain ⟨R, hR⟩ := hX.subset_closedBall 0
  refine (isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := R)).subset fun y hy => ?_
  rw [mem_closedBall_zero_iff]
  exact (norm_le_norm_pt y s).trans (mem_closedBall_zero_iff.mp (hR hy))
lemma f2 {X : Set (Fin (k + 1) → ℝ)} (hX : IsClosed X) (s : ℝ) :
    IsClosed (sect X s) :=
  hX.preimage (continuous_pt_left' s)
lemma f3 {X : Set (Fin (k + 1) → ℝ)} (hX : Convex ℝ X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t t' : ℝ) : (1 - θ) • sect X t + θ • sect X t' ⊆ sect X ((1 - θ) * t + θ * t') := by
  rintro _ ⟨_, ⟨y, hy, rfl⟩, _, ⟨y', hy', rfl⟩, rfl⟩
  show pt ((1 - θ) • y + θ • y') ((1 - θ) * t + θ * t') ∈ X
  have h := hX hy hy' (by linarith : (0 : ℝ) ≤ 1 - θ) hθ0 (by ring)
  rw [fV, fV, pt_add] at h
  exact h
lemma f4 {X : Set (Fin (k + 1) → ℝ)} (hX : Convex ℝ X) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (t t' : ℝ) (hne : (sect X t').Nonempty) : ENNReal.ofReal ((1 - θ) ^ k) * volume (sect X t) ≤ volume (sect X ((1 - θ) * t + θ * t')) := by
  obtain ⟨q, hq⟩ := hne
  have hsub : (1 - θ) • sect X t + {θ • q} ⊆ sect X ((1 - θ) * t + θ * t') :=
    (Set.add_subset_add_left (Set.singleton_subset_iff.mpr (Set.smul_mem_smul_set hq))).trans
      (f3 hX hθ0 hθ1 t t')
  calc ENNReal.ofReal ((1 - θ) ^ k) * volume (sect X t)
      = volume ((1 - θ) • sect X t) := by
        rw [Measure.addHaar_smul_of_nonneg volume (by linarith : (0 : ℝ) ≤ 1 - θ), Module.finrank_fin_fun]
    _ = volume ((1 - θ) • sect X t + {θ • q}) := by
        rw [Set.add_singleton, Set.image_add_right, measure_preimage_add_right]
    _ ≤ volume (sect X ((1 - θ) * t + θ * t')) := measure_mono hsub
noncomputable def f5 (X : Set (Fin (k + 1) → ℝ)) (s : ℝ) : ℝ := volume.real (sect X s)
lemma nV_pt' (y' : Fin k → ℝ) (s : ℝ) : nV (pt y' s) = s := nV_pt y' s
lemma pt_sub (y₁ y₂ : Fin k → ℝ) (s₁ s₂ : ℝ) : pt y₁ s₁ - pt y₂ s₂ = pt (y₁ - y₂) (s₁ - s₂) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [pt]
lemma norm_pt_zero (y : Fin k → ℝ) : ‖pt y 0‖ = ‖y‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
    (norm_le_norm_pt y 0)
  refine Fin.addCases (motive := fun i => ‖pt y 0 i‖ ≤ ‖y‖) (fun i => ?_) (fun i => ?_) i
  · simp only [pt, Fin.append_left]; exact norm_le_pi_norm y i
  · simp only [pt, Fin.append_right, norm_zero]; exact norm_nonneg _
lemma pt_nH_nV' (v : Fin (k + 1) → ℝ) : pt (nH v) (nV v) = v := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [pt, nH]
  · have : i = 0 := Subsingleton.elim _ _
    subst this; simp [pt, nV]
lemma norm_pt_zero_left (s : ℝ) : ‖pt (0 : Fin k → ℝ) s‖ = |s| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg s)).2 fun i => ?_) ?_
  · refine Fin.addCases (motive := fun i => ‖pt (0 : Fin k → ℝ) s i‖ ≤ |s|)
      (fun i => ?_) (fun i => ?_) i
    · simp [pt]
    · simp [pt, Real.norm_eq_abs]
  · have := norm_le_pi_norm (pt (0 : Fin k → ℝ) s) (Fin.natAdd k 0)
    simpa [pt, Real.norm_eq_abs] using this
lemma f6 (x : Fin (k + 1) → ℝ) (c : ℝ) : nV (x + c • pt (0 : Fin k → ℝ) 1) = nV x + c := by
  simp [nV, pt]
structure Heights (X : Set (Fin (k + 1) → ℝ)) (a b : ℝ) : Prop where
  lt : a < b
  mem : ∀ x ∈ X, a ≤ nV x ∧ nV x ≤ b
  bot : (sect X a).Nonempty
  top : (sect X b).Nonempty
  ball : ∃ y₀ : Fin k → ℝ, ∃ s₀ ∈ Ioo a b, ∃ r > 0, Metric.ball y₀ r ⊆ sect X s₀
lemma IsCB.exists_heights {X : Set (Fin (k + 1) → ℝ)} (hX : IsCB X) : ∃ a b, Heights X a b := by
  obtain ⟨x₀, hx₀⟩ := hX.interior_nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x₀ hx₀
  have za : Continuous (nV (k := k)) := continuous_apply _
  have zb : X.Nonempty := ⟨x₀, interior_subset hx₀⟩
  obtain ⟨xm, hxm, hmin⟩ := hX.compact.exists_isMinOn zb za.continuousOn
  obtain ⟨xM, hxM, hmax⟩ := hX.compact.exists_isMaxOn zb za.continuousOn
  have hmem : ∀ c : ℝ, |c| < r → x₀ + c • pt (0 : Fin k → ℝ) 1 ∈ X := by
    intro c hc
    refine interior_subset (hball ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_pt_zero_left, abs_one, mul_one, Real.norm_eq_abs]
    exact hc
  have h1 := isMinOn_iff.mp hmin _ (hmem (-(r / 2)) (by
    rw [abs_neg, abs_of_pos (by positivity)]; linarith))
  have h2 := isMaxOn_iff.mp hmax _ (hmem (r / 2) (by
    rw [abs_of_pos (by positivity)]; linarith))
  rw [f6] at h1 h2
  refine ⟨nV xm, nV xM, ⟨by linarith, fun x hx => ⟨isMinOn_iff.mp hmin x hx,
    isMaxOn_iff.mp hmax x hx⟩, ⟨nH xm, ?_⟩, ⟨nH xM, ?_⟩,
    ⟨nH x₀, nV x₀, ⟨by linarith, by linarith⟩, r, hr, fun y hy => ?_⟩⟩⟩
  · show pt (nH xm) (nV xm) ∈ X
    rw [pt_nH_nV']; exact hxm
  · show pt (nH xM) (nV xM) ∈ X
    rw [pt_nH_nV']; exact hxM
  · show pt y (nV x₀) ∈ X
    refine interior_subset (hball ?_)
    have hdiff : pt y (nV x₀) - x₀ = pt (y - nH x₀) 0 := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp [pt, nH]
      · have : i = 0 := Subsingleton.elim _ _
        subst this; simp [pt, nV]
    rw [mem_ball, dist_eq_norm, hdiff, norm_pt_zero]
    exact mem_ball_iff_norm.mp hy
section Heights
variable {X : Set (Fin (k + 1) → ℝ)} {a b : ℝ}
lemma Heights.sect_eq_empty (hH : Heights X a b) {s : ℝ} (hs : s ∉ Icc a b) : sect X s = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y hy => hs ?_
  have := hH.mem _ hy
  rw [nV_pt] at this
  exact this
lemma Heights.sect_nonempty (hX : Convex ℝ X) (hH : Heights X a b) {s : ℝ} (hs : s ∈ Icc a b) : (sect X s).Nonempty := by
  obtain ⟨p, hp⟩ := hH.bot
  obtain ⟨q, hq⟩ := hH.top
  set θ := (s - a) / (b - a) with hθ
  have hba : 0 < b - a := sub_pos.mpr hH.lt
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hs.1]) hba.le
  have hθ1 : θ ≤ 1 := (div_le_one hba).mpr (by linarith [hs.2])
  have hcomb : (1 - θ) * a + θ * b = s := by rw [hθ]; field_simp; ring
  have := f3 hX hθ0 hθ1 a b
  rw [hcomb] at this
  exact ⟨_, this ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩⟩
lemma f7 (hXb : Bornology.IsBounded X) (s : ℝ) : volume (sect X s) ≠ ⊤ :=
  (f1 hXb s).measure_lt_top.ne
lemma Heights.secVol_ge (hX : Convex ℝ X) (hXb : Bornology.IsBounded X) (hH : Heights X a b) {s s' e : ℝ} (he : e ∈ Icc a b) (hs : s ≠ e) (hmid : s' ∈ Icc (min s e) (max s e)) : ((e - s') / (e - s)) ^ k * f5 X s ≤ f5 X s' := by
  set θ := (s' - s) / (e - s) with hθ
  have hes : e - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs)
  have hθ0 : 0 ≤ θ := by
    rw [hθ]
    rcases lt_or_gt_of_ne hs with h | h
    · have h1 : s ≤ s' := by simpa [min_eq_left h.le] using hmid.1
      exact div_nonneg (by linarith) (by linarith)
    · have h1 : s' ≤ s := by simpa [max_eq_left h.le] using hmid.2
      exact div_nonneg_of_nonpos (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := by
    rw [hθ]
    rcases lt_or_gt_of_ne hs with h | h
    · have h1 : s' ≤ e := by simpa [max_eq_right h.le] using hmid.2
      exact (div_le_one (by linarith)).mpr (by linarith)
    · have h1 : e ≤ s' := by simpa [min_eq_right h.le] using hmid.1
      rw [div_le_one_of_neg (by linarith)]
      linarith
  have hcomb : (1 - θ) * s + θ * e = s' := by rw [hθ]; field_simp; ring
  have h1θ : 1 - θ = (e - s') / (e - s) := by rw [hθ]; field_simp; ring
  have h := f4 hX hθ0 hθ1 s e (hH.sect_nonempty hX he)
  rw [hcomb] at h
  have hfin := f7 hXb s'
  have h' := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg (by linarith) k)] at h'
  rw [← h1θ]
  exact h'
lemma Heights.secVol_pos (hX : Convex ℝ X) (hXb : Bornology.IsBounded X) (hH : Heights X a b) {s : ℝ} (hs : s ∈ Ioo a b) : 0 < f5 X s := by
  obtain ⟨y₀, s₀, hs₀, r, hr, hball⟩ := hH.ball
  have h0 : 0 < f5 X s₀ := by
    have hpos : 0 < volume (sect X s₀) :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume y₀ hr) (measure_mono hball)
    exact ENNReal.toReal_pos hpos.ne' (f7 hXb s₀)
  rcases le_or_gt s₀ s with h | h
  · have hmid : s ∈ Icc (min s₀ b) (max s₀ b) := by
      rw [min_eq_left (by linarith [hs₀.2]), max_eq_right (by linarith [hs₀.2])]
      exact ⟨h, hs.2.le⟩
    have hge := hH.secVol_ge hX hXb (right_mem_Icc.mpr hH.lt.le) (ne_of_lt hs₀.2) hmid
    have hρ : 0 < ((b - s) / (b - s₀)) ^ k :=
      pow_pos (div_pos (by linarith [hs.2]) (by linarith [hs₀.2])) k
    exact lt_of_lt_of_le (mul_pos hρ h0) hge
  · have hmid : s ∈ Icc (min s₀ a) (max s₀ a) := by
      rw [min_eq_right (by linarith [hs₀.1]), max_eq_left (by linarith [hs₀.1])]
      exact ⟨hs.1.le, h.le⟩
    have hge := hH.secVol_ge hX hXb (left_mem_Icc.mpr hH.lt.le) (ne_of_gt hs₀.1) hmid
    have hρ : 0 < ((a - s) / (a - s₀)) ^ k :=
      pow_pos (div_pos_of_neg_of_neg (by linarith [hs.1]) (by linarith [hs₀.1])) k
    exact lt_of_lt_of_le (mul_pos hρ h0) hge
lemma Heights.secVol_squeeze (hX : Convex ℝ X) (hXb : Bornology.IsBounded X) (hH : Heights X a b) {s s' : ℝ} (hs : s ∈ Ioo a b) (hs' : s' ∈ Ioo a b) : min (((b - s') / (b - s)) ^ k) (((s' - a) / (s - a)) ^ k) * f5 X s ≤ f5 X s' ∧ f5 X s' ≤ max (((b - s') / (b - s)) ^ k) (((s' - a) / (s - a)) ^ k) * f5 X s := by
  have hbs : 0 < b - s := by linarith [hs.2]
  have hsa : 0 < s - a := by linarith [hs.1]
  have hbs' : 0 < b - s' := by linarith [hs'.2]
  have za : 0 < s' - a := by linarith [hs'.1]
  have hf : 0 ≤ f5 X s := measureReal_nonneg
  have hf' : 0 ≤ f5 X s' := measureReal_nonneg
  have hbI : b ∈ Icc a b := right_mem_Icc.mpr hH.lt.le
  have haI : a ∈ Icc a b := left_mem_Icc.mpr hH.lt.le
  rcases le_total s s' with h | h
  ·
    have hL := hH.secVol_ge hX hXb hbI (ne_of_lt hs.2) (by
      rw [min_eq_left (by linarith [hs.2]), max_eq_right (by linarith [hs.2])]
      exact ⟨h, hs'.2.le⟩)
    have hU := hH.secVol_ge hX hXb haI (ne_of_gt hs'.1) (s' := s) (by
      rw [min_eq_right (by linarith [hs'.1]), max_eq_left (by linarith [hs'.1])]
      exact ⟨hs.1.le, h⟩)
    have hr : (a - s) / (a - s') = (s - a) / (s' - a) := by
      rw [← neg_sub s a, ← neg_sub s' a, neg_div_neg_eq]
    rw [hr] at hU
    have hpos : 0 < ((s - a) / (s' - a)) ^ k := pow_pos (div_pos hsa za) k
    have hU' : f5 X s' ≤ ((s' - a) / (s - a)) ^ k * f5 X s := by
      rw [← le_div_iff₀' hpos] at hU
      calc f5 X s' ≤ f5 X s / ((s - a) / (s' - a)) ^ k := hU
        _ = ((s' - a) / (s - a)) ^ k * f5 X s := by
          rw [div_eq_mul_inv, ← inv_pow, inv_div, mul_comm]
    constructor
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hf) hL
    · exact le_trans hU' (mul_le_mul_of_nonneg_right (le_max_right _ _) hf)
  ·
    have hL := hH.secVol_ge hX hXb haI (ne_of_gt hs.1) (by
      rw [min_eq_right (by linarith [hs.1]), max_eq_left (by linarith [hs.1])]
      exact ⟨hs'.1.le, h⟩)
    have hr0 : (a - s') / (a - s) = (s' - a) / (s - a) := by
      rw [← neg_sub s' a, ← neg_sub s a, neg_div_neg_eq]
    rw [hr0] at hL
    have hU := hH.secVol_ge hX hXb hbI (ne_of_lt hs'.2) (s' := s) (by
      rw [min_eq_left (by linarith [hs'.2]), max_eq_right (by linarith [hs'.2])]
      exact ⟨h, hs.2.le⟩)
    have hpos : 0 < ((b - s) / (b - s')) ^ k := pow_pos (div_pos hbs hbs') k
    have hU' : f5 X s' ≤ ((b - s') / (b - s)) ^ k * f5 X s := by
      rw [← le_div_iff₀' hpos] at hU
      calc f5 X s' ≤ f5 X s / ((b - s) / (b - s')) ^ k := hU
        _ = ((b - s') / (b - s)) ^ k * f5 X s := by
          rw [div_eq_mul_inv, ← inv_pow, inv_div, mul_comm]
    constructor
    · exact le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hf) hL
    · exact le_trans hU' (mul_le_mul_of_nonneg_right (le_max_left _ _) hf)
lemma Heights.continuousOn_secVol (hX : Convex ℝ X) (hXb : Bornology.IsBounded X) (hH : Heights X a b) : ContinuousOn (f5 X) (Ioo a b) := by
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  have hbs : b - s ≠ 0 := by linarith [hs.2]
  have hsa : s - a ≠ 0 := by linarith [hs.1]
  have hL : Continuous fun s' : ℝ => ((b - s') / (b - s)) ^ k := by fun_prop
  have hM : Continuous fun s' : ℝ => ((s' - a) / (s - a)) ^ k := by fun_prop
  have hL1 : ((b - s) / (b - s)) ^ k = 1 := by rw [div_self hbs, one_pow]
  have hM1 : ((s - a) / (s - a)) ^ k = 1 := by rw [div_self hsa, one_pow]
  have hlow : Tendsto (fun s' => min (((b - s') / (b - s)) ^ k) (((s' - a) / (s - a)) ^ k) *
      f5 X s) (𝓝 s) (𝓝 (f5 X s)) := by
    have := ((hL.min hM).tendsto s).mul_const (f5 X s)
    simpa [hL1, hM1] using this
  have za : Tendsto (fun s' => max (((b - s') / (b - s)) ^ k) (((s' - a) / (s - a)) ^ k) *
      f5 X s) (𝓝 s) (𝓝 (f5 X s)) := by
    have := ((hL.max hM).tendsto s).mul_const (f5 X s)
    simpa [hL1, hM1] using this
  have hev : ∀ᶠ s' in 𝓝 s, s' ∈ Ioo a b := isOpen_Ioo.mem_nhds hs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow za
    (hev.mono fun s' hs' => (hH.secVol_squeeze hX hXb hs hs').1)
    (hev.mono fun s' hs' => (hH.secVol_squeeze hX hXb hs hs').2)
lemma f8 (hXm : MeasurableSet X) : Measurable (f5 X) :=
  (fZ hXm).ennreal_toReal
lemma f9 (hXb : Bornology.IsBounded X) : ∃ C, ∀ s, f5 X s ≤ C := by
  obtain ⟨R, hR⟩ := hXb.subset_closedBall 0
  refine ⟨volume.real (closedBall (0 : Fin k → ℝ) R), fun s => ?_⟩
  refine measureReal_mono (fun y hy => ?_) measure_closedBall_lt_top.ne
  rw [mem_closedBall_zero_iff]
  exact (norm_le_norm_pt y s).trans (mem_closedBall_zero_iff.mp (hR hy))
lemma Heights.density (hX : IsCB X) (hH : Heights X a b) : Transport.Density (f5 X) a b :=
  { lt := hH.lt
    meas := f8 hX.compact.isClosed.measurableSet
    nonneg := fun _ => measureReal_nonneg
    pos := fun _ hs => hH.secVol_pos hX.convex hX.compact.isBounded hs
    cont := hH.continuousOn_secVol hX.convex hX.compact.isBounded
    bdd := f9 hX.compact.isBounded }
lemma Heights.mass_eq (hX : IsCB X) (hH : Heights X a b) : Transport.mass (f5 X) a b = volume.real X := by
  have hXm : MeasurableSet X := hX.compact.isClosed.measurableSet
  have hXb := hX.compact.isBounded
  have hzero : ∀ s ∉ Icc a b, f5 X s = 0 := fun s hs => by
    rw [f5, hH.sect_eq_empty hs, measureReal_empty]
  have hint : Integrable (f5 X) := by
    obtain ⟨C, hC⟩ := f9 hXb (X := X)
    have hIcc : IntegrableOn (f5 X) (Icc a b) := by
      refine (integrableOn_const (C := C) (measure_Icc_lt_top.ne)).mono'
        (f8 hXm).aestronglyMeasurable ?_
      exact Eventually.of_forall fun s => by
        rw [Real.norm_of_nonneg (show 0 ≤ f5 X s from measureReal_nonneg)]; exact hC s
    exact (integrableOn_iff_integrable_of_support_subset (fun s hs => by
      by_contra h; exact hs (hzero s h))).mp hIcc
  rw [Transport.mass, intervalIntegral.integral_of_le hH.lt.le, ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_eq_lintegral_of_nonneg_ae (f := f5 X)
      (Eventually.of_forall fun _ => measureReal_nonneg)
      (f8 hXm).aestronglyMeasurable, measureReal_def,
    fY hXm]
  congr 1
  refine lintegral_congr fun s => ?_
  rw [f5, measureReal_def, ENNReal.ofReal_toReal (f7 hXb s)]
end Heights
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Set
open scoped Pointwise
namespace FCBridge
def ga (n : ℕ) : Prop :=
  ∀ X Y : Set (Fin n → ℝ), Convex ℝ X → IsCompact X → Convex ℝ Y → IsCompact Y →
    ∀ H : Set (Fin n → ℝ), (∀ x ∈ X, ∀ y ∈ Y, (2 : ℝ)⁻¹ • (x + y) ∈ H) →
      ENNReal.ofReal (Real.sqrt (volume.real X * volume.real Y)) ≤ volume H
lemma gb {n : ℕ} {X : Set (Fin n → ℝ)} (hX : Convex ℝ X) (hpos : volume X ≠ 0) : (interior X).Nonempty := by
  rw [hX.interior_nonempty_iff_affineSpan_eq_top]
  by_contra h
  exact hpos (measure_mono_null (subset_affineSpan ℝ X)
    (Measure.addHaar_affineSubspace volume (affineSpan ℝ X) h))
lemma IsCB.volume_pos {n : ℕ} {X : Set (Fin n → ℝ)} (hX : IsCB X) : 0 < volume X :=
  (isOpen_interior.measure_pos volume hX.interior_nonempty).trans_le
    (measure_mono interior_subset)
lemma IsCB.of_volume_ne_zero {n : ℕ} {X : Set (Fin n → ℝ)} (hc : Convex ℝ X)
    (hk : IsCompact X) (h0 : volume X ≠ 0) : IsCB X :=
  ⟨hc, hk, gb hc h0⟩
section Sect
variable {k : ℕ}
lemma gc {X : Set (Fin (k + 1) → ℝ)} (hX : IsCompact X) (s : ℝ) :
    IsCompact (sect X s) :=
  isCompact_of_isClosed_isBounded (f2 hX.isClosed s) (f1 hX.isBounded s)
lemma gd {X Y H : Set (Fin (k + 1) → ℝ)} (hH : ∀ x ∈ X, ∀ y ∈ Y, (2 : ℝ)⁻¹ • (x + y) ∈ H) {t s : ℝ} {x y : Fin k → ℝ} (hx : x ∈ sect X t) (hy : y ∈ sect Y s) : (2 : ℝ)⁻¹ • (x + y) ∈ sect H ((t + s) / 2) := by
  have h := hH _ hx _ hy
  rw [pt_add, fV] at h
  show pt ((2 : ℝ)⁻¹ • (x + y)) ((t + s) / 2) ∈ H
  rwa [div_eq_inv_mul]
end Sect
lemma gf : ga 0 := by
  intro X Y _ _ _ _ H hH
  rcases X.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  rcases Y.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp
  have hHu : H = univ := eq_univ_of_forall fun z => by
    rw [Subsingleton.elim z ((2 : ℝ)⁻¹ • (x + y))]; exact hH x hx y hy
  have hu : volume (univ : Set (Fin 0 → ℝ)) = 1 := by
    rw [volume_pi, Measure.pi_univ]; simp
  have h1 : ∀ S : Set (Fin 0 → ℝ), volume.real S ≤ 1 := fun S => by
    calc volume.real S ≤ volume.real (univ : Set (Fin 0 → ℝ)) :=
          measureReal_mono (subset_univ S) (by rw [hu]; exact ENNReal.one_ne_top)
      _ = 1 := by rw [measureReal_def, hu, ENNReal.toReal_one]
  rw [hHu, hu, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (mul_le_one₀ (h1 X) measureReal_nonneg (h1 Y))
lemma gg {k : ℕ} (ih : ga k) : ga (k + 1) := by
  intro X Y hXc hXk hYc hYk H hH
  by_cases hX0 : volume X = 0
  · simp [Measure.real, hX0]
  by_cases hY0 : volume Y = 0
  · simp [Measure.real, hY0]
  have hX : IsCB X := IsCB.of_volume_ne_zero hXc hXk hX0
  have hY : IsCB Y := IsCB.of_volume_ne_zero hYc hYk hY0
  obtain ⟨a, b, hHX⟩ := hX.exists_heights
  obtain ⟨c, e, hHY⟩ := hY.exists_heights
  have hH' : ∀ x ∈ X, ∀ y ∈ Y, (2 : ℝ)⁻¹ • (x + y) ∈ toMeasurable volume H :=
    fun x hx y hy => subset_toMeasurable volume H (hH x hx y hy)
  have hstep : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo c e,
      ENNReal.ofReal (Real.sqrt (f5 X t * f5 Y s)) ≤
        (fun z => volume (sect (toMeasurable volume H) z)) ((t + s) / 2) := fun t _ s _ =>
    ih (sect X t) (sect Y s) (f0 hXc t) (gc hXk t) (f0 hYc s)
      (gc hYk s) _ fun _ hx _ hy => gd hH' hx hy
  have key : ENNReal.ofReal (Real.sqrt (Transport.mass (f5 X) a b *
      Transport.mass (f5 Y) c e)) ≤ ∫⁻ z, volume (sect (toMeasurable volume H) z) :=
    Transport.transport_ineq (hHX.density hX) (hHY.density hY) hstep
  rwa [hHX.mass_eq hX, hHY.mass_eq hY, ← fY (measurableSet_toMeasurable _ _), measure_toMeasurable] at key
lemma bm : ∀ n, ga n
  | 0 => gf
  | n + 1 => gg (bm n)
section Neg
variable {k : ℕ}
lemma gh (X : Set (Fin (k + 1) → ℝ)) (s : ℝ) : sect (-X) s = -sect X (-s) := by
  ext y
  show pt y s ∈ -X ↔ pt (-y) (-s) ∈ X
  rw [Set.mem_neg, fW]
lemma gi (X : Set (Fin (k + 1) → ℝ)) (s : ℝ) : f5 (-X) s = f5 X (-s) := by
  rw [f5, f5, gh, measureReal_def, measureReal_def, Measure.measure_neg]
lemma nV_neg (x : Fin (k + 1) → ℝ) : nV (-x) = -nV x := rfl
lemma Heights.neg {X : Set (Fin (k + 1) → ℝ)} {a b : ℝ} (hH : Heights X a b) :
    Heights (-X) (-b) (-a) where
  lt := neg_lt_neg hH.lt
  mem x hx := by
    have := hH.mem _ (Set.mem_neg.mp hx)
    rw [nV_neg] at this
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  bot := by
    obtain ⟨q, hq⟩ := hH.top
    refine ⟨-q, ?_⟩
    rw [gh, Set.mem_neg, neg_neg, neg_neg]; exact hq
  top := by
    obtain ⟨q, hq⟩ := hH.bot
    refine ⟨-q, ?_⟩
    rw [gh, Set.mem_neg, neg_neg, neg_neg]; exact hq
  ball := by
    obtain ⟨y₀, s₀, hs₀, r, hr, hball⟩ := hH.ball
    refine ⟨-y₀, -s₀, ⟨neg_lt_neg hs₀.2, neg_lt_neg hs₀.1⟩, r, hr, fun y hy => ?_⟩
    rw [gh, Set.mem_neg, neg_neg]
    refine hball ?_
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have : -y - y₀ = -(y - -y₀) := by abel
    rw [this, norm_neg]; exact hy
end Neg
def gj {n : ℕ} (X : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (2 : ℝ)⁻¹ • (p.1 - p.2)) '' (X ×ˢ X)
lemma gk {n : ℕ} {X : Set (Fin n → ℝ)} (hX : IsCompact X) :
    IsCompact (gj X) :=
  (hX.prod hX).image (by fun_prop)
lemma gl {n : ℕ} {X : Set (Fin n → ℝ)} {x y : Fin n → ℝ} (hx : x ∈ X) (hy : y ∈ X) :
    (2 : ℝ)⁻¹ • (x - y) ∈ gj X :=
  ⟨(x, y), ⟨hx, hy⟩, rfl⟩
section Symm
variable {k : ℕ} {X : Set (Fin (k + 1) → ℝ)} {a b : ℝ}
lemma Heights.secVol_eq_zero (hH : Heights X a b) {s : ℝ} (hs : s ∉ Icc a b) : f5 X s = 0 := by
  rw [f5, hH.sect_eq_empty hs, measureReal_empty]
lemma Heights.integrable_secVol (hX : IsCB X) (hH : Heights X a b) : Integrable (f5 X) := by
  obtain ⟨C, hC⟩ := f9 hX.compact.isBounded (X := X)
  have hIcc : IntegrableOn (f5 X) (Icc a b) := by
    refine (integrableOn_const (C := C) measure_Icc_lt_top.ne).mono'
      (f8 hX.compact.isClosed.measurableSet).aestronglyMeasurable ?_
    exact Eventually.of_forall fun s => by
      rw [Real.norm_of_nonneg (show 0 ≤ f5 X s from measureReal_nonneg)]; exact hC s
  exact (integrableOn_iff_integrable_of_support_subset (fun s hs => by
    by_contra h; exact hs (hH.secVol_eq_zero h))).mp hIcc
lemma Heights.integral_secVol (hX : IsCB X) (hH : Heights X a b) : ∫ s, f5 X s = volume.real X := by
  rw [← hH.mass_eq hX, Transport.mass, intervalIntegral.integral_of_le hH.lt.le, ← integral_Icc_eq_integral_Ioc, setIntegral_eq_integral_of_forall_compl_eq_zero (fun s hs => hH.secVol_eq_zero hs)]
lemma Heights.secVol_symm (hX : IsCB X) (hH : Heights X a b) (hle : volume (gj X) ≤ volume X) : ∀ t ∈ Ioo a b, f5 X t = f5 X (a + b - t) := by
  have hXn : IsCB (-X) := IsCB.of_volume_ne_zero hX.convex.neg hX.compact.neg
    (by rw [Measure.measure_neg]; exact hX.volume_pos.ne')
  have hHn := hH.neg
  have hD := gk hX.compact
  have hmid : ∀ x ∈ X, ∀ y ∈ -X, (2 : ℝ)⁻¹ • (x + y) ∈ gj X := fun x hx y hy => by
    have := gl hx (Set.mem_neg.mp hy)
    rwa [sub_neg_eq_add] at this
  have hstep : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo (-b) (-a),
      ENNReal.ofReal (Real.sqrt (f5 X t * f5 (-X) s)) ≤
        (fun z => volume (sect (gj X) z)) ((t + s) / 2) := fun t _ s _ =>
    bm k (sect X t) (sect (-X) s) (f0 hX.convex t) (gc hX.compact t)
      (f0 hXn.convex s) (gc hXn.compact s) _
      fun _ hx _ hy => gd hmid hx hy
  have hMN : Transport.mass (f5 X) a b = Transport.mass (f5 (-X)) (-b) (-a) := by
    rw [hH.mass_eq hX, hHn.mass_eq hXn, measureReal_def, measureReal_def, Measure.measure_neg]
  have hle' : ∫⁻ z, volume (sect (gj X) z) ≤
      ENNReal.ofReal (Transport.mass (f5 X) a b) := by
    rw [← fY hD.isClosed.measurableSet, hH.mass_eq hX, measureReal_def, ENNReal.ofReal_toReal hX.compact.measure_lt_top.ne]
    exact hle
  obtain ⟨C, hC⟩ := Transport.transport_eq (hH.density hX) (hHn.density hXn) hstep hMN hle'
  have hab := hH.lt
  have za : C = a + b := by
    rcases lt_trichotomy C (a + b) with h | h | h
    · exfalso
      have ht : max (C - a) ((a + b) / 2) ∈ Ioo a b :=
        ⟨lt_max_of_lt_right (by linarith), max_lt (by linarith) (by linarith)⟩
      have h1 := (hC _ ht).1.2
      have h2 : C - a ≤ max (C - a) ((a + b) / 2) := le_max_left _ _
      linarith
    · exact h
    · exfalso
      have ht : min (C - b) ((a + b) / 2) ∈ Ioo a b :=
        ⟨lt_min (by linarith) (by linarith), min_lt_of_right_lt (by linarith)⟩
      have h1 := (hC _ ht).1.1
      have h2 : min (C - b) ((a + b) / 2) ≤ C - b := min_le_left _ _
      linarith
  intro t ht
  rw [(hC t ht).2, gi, za, neg_sub]
lemma gn (hX : IsCompact X) : ∫ x in X, nV x = ∫ s, s * f5 X s := by
  have hXm : MeasurableSet X := hX.isClosed.measurableSet
  have hcont : Continuous (nV (k := k)) := continuous_apply _
  set F : (Fin (k + 1) → ℝ) → ℝ := X.indicator nV with hF
  have hFm : Measurable F := hcont.measurable.indicator hXm
  have hFi : Integrable F :=
    (integrable_indicator_iff hXm).2 (hcont.continuousOn.integrableOn_compact hX)
  have hmp := measurePreserving_pt (k := k)
  have h1 : ∫ x in X, nV x = ∫ p : (Fin k → ℝ) × ℝ, F (pt p.1 p.2) ∂(volume.prod volume) := by
    rw [← integral_indicator hXm, ← hmp.map_eq, integral_map hmp.measurable.aemeasurable (hmp.map_eq ▸ hFm.aestronglyMeasurable)]
  have hFi' : Integrable (fun p : (Fin k → ℝ) × ℝ => F (pt p.1 p.2)) (volume.prod volume) :=
    (hmp.integrable_comp hFm.aestronglyMeasurable).2 hFi
  rw [h1, integral_prod_symm _ hFi']
  congr 1
  funext s
  show ∫ y, F (pt y s) = s * f5 X s
  have hin : ∀ y : Fin k → ℝ, F (pt y s) = (sect X s).indicator (fun _ => s) y := fun y => by
    by_cases hy : pt y s ∈ X
    · rw [hF, Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ sect X s from hy), nV_pt]
    · rw [hF, Set.indicator_of_notMem hy, Set.indicator_of_notMem (show y ∉ sect X s from hy)]
  simp_rw [hin]
  rw [integral_indicator_const s (fX hXm s), smul_eq_mul, mul_comm, f5]
lemma Heights.integral_nV (hX : IsCB X) (hH : Heights X a b) (hsym : ∀ t ∈ Ioo a b, f5 X t = f5 X (a + b - t)) : ∫ x in X, nV x = (a + b) / 2 * volume.real X := by
  have hint := hH.integrable_secVol hX
  have hint' : Integrable (fun s => s * f5 X s) := by
    have hon : IntegrableOn (fun s => s * f5 X s) (Icc a b) := by
      refine Integrable.bdd_mul (f := fun s => s) (c := max |a| |b|) hint.integrableOn
        continuous_id.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
      rw [Real.norm_eq_abs]
      exact abs_le_max_abs_abs hs.1 hs.2
    refine (integrableOn_iff_integrable_of_support_subset fun s hs => ?_).1 hon
    by_contra h
    exact hs (show s * f5 X s = 0 by rw [hH.secVol_eq_zero h, mul_zero])
  have hae : ∀ᵐ s, (a + b - s) * f5 X (a + b - s) = (a + b - s) * f5 X s := by
    have hfin : ({a, b} : Set ℝ).Countable := (Set.toFinite _).countable
    filter_upwards [hfin.ae_notMem volume] with s hs
    congr 1
    by_cases hs' : s ∈ Ioo a b
    · exact (hsym s hs').symm
    · have hne : s ≠ a ∧ s ≠ b := by simpa [not_or] using hs
      have h1 : s ∉ Icc a b := fun h =>
        hs' ⟨lt_of_le_of_ne h.1 (Ne.symm hne.1), lt_of_le_of_ne h.2 hne.2⟩
      have h2 : a + b - s ∉ Icc a b := fun h => h1 ⟨by linarith [h.2], by linarith [h.1]⟩
      rw [hH.secVol_eq_zero h1, hH.secVol_eq_zero h2]
  have hrefl : ∫ s, s * f5 X s = ∫ s, (a + b - s) * f5 X s := by
    rw [show (∫ s, s * f5 X s) = ∫ s, (a + b - s) * f5 X (a + b - s) from (integral_sub_left_eq_self (fun s => s * f5 X s) volume (a + b)).symm]
    exact integral_congr_ae hae
  have hsplit : ∫ s, (a + b - s) * f5 X s =
      (a + b) * (∫ s, f5 X s) - ∫ s, s * f5 X s := by
    simp_rw [sub_mul]
    rw [integral_sub (hint.const_mul _) hint', integral_const_mul]
  have h := hrefl.trans hsplit
  rw [gn hX.compact, ← hH.integral_secVol hX]
  linear_combination h / 2
end Symm
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Set
open scoped Pointwise
namespace FCBridge
lemma go {n : ℕ} {T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)}
    (hT : Function.Injective T) : LinearMap.det T ≠ 0 :=
  (LinearMap.isUnit_det T ((LinearMap.isUnit_iff_ker_eq_bot T).2
    (LinearMap.ker_eq_bot.2 hT))).ne_zero
lemma IsCB.image_linearMap {n : ℕ} {A : Set (Fin n → ℝ)} (hA : IsCB A)
    {T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hT : Function.Injective T) : IsCB (T '' A) :=
  IsCB.of_volume_ne_zero (hA.convex.linear_image T)
    (hA.compact.image (LinearMap.continuous_of_finiteDimensional T))
    (by
      rw [Measure.addHaar_image_linearMap]
      exact mul_ne_zero (ENNReal.ofReal_pos.2 (abs_pos.2 (go hT))).ne'
        hA.volume_pos.ne')
lemma gq {n : ℕ} (A : Set (Fin n → ℝ)) (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : gj (T '' A) ⊆ T '' gj A := by
  rintro _ ⟨⟨_, _⟩, ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩, rfl⟩
  exact ⟨(2 : ℝ)⁻¹ • (x - y), gl hx hy, by simp only [map_smul, map_sub]⟩
lemma gr {n : ℕ} {A : Set (Fin n → ℝ)}
    (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (hle : volume (gj A) ≤ volume A) :
    volume (gj (T '' A)) ≤ volume (T '' A) :=
  calc volume (gj (T '' A)) ≤ volume (T '' gj A) :=
        measure_mono (gq A T)
    _ = ENNReal.ofReal |LinearMap.det T| * volume (gj A) :=
        Measure.addHaar_image_linearMap volume T _
    _ ≤ ENNReal.ofReal |LinearMap.det T| * volume A := by gcongr
    _ = volume (T '' A) := (Measure.addHaar_image_linearMap volume T A).symm
lemma gs {n : ℕ} {T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)} (hT : Function.Injective T) {S : Set (Fin n → ℝ)} (hS : MeasurableSet S) (hTS : MeasurableSet (T '' S)) {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) : ∫ x in S, F (T x) = |LinearMap.det T|⁻¹ * ∫ z in T '' S, F z := by
  have hdet := go hT
  have hTm : Measurable T := (LinearMap.continuous_of_finiteDimensional T).measurable
  have za : ∀ x, S.indicator (fun x => F (T x)) x = (T '' S).indicator F (T x) := fun x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_image_of_mem T hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ?_)]
      obtain ⟨y, hy, hyx⟩ := h
      rwa [← hT hyx]
  rw [← integral_indicator hS, ← integral_indicator hTS]
  simp_rw [za]
  rw [← integral_map hTm.aemeasurable (hF.indicator hTS).aestronglyMeasurable, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul]
lemma gt {k : ℕ} {v : Fin (k + 1) → ℝ} (hv : v ≠ 0) : ∃ T : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ), Function.Injective T ∧ ∀ x, nV (T x) = ∑ i, v i * x i := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    exact hv (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin (k + 1)), σ = Equiv.swap j (Fin.natAdd k 0) :=
    ⟨_, rfl⟩
  have hσσ : ∀ m, σ (σ m) = m := fun m => by rw [hσ, Equiv.swap_apply_self]
  have hσj : σ (Fin.natAdd k 0) = j := by rw [hσ, Equiv.swap_apply_right]
  let T : (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ) :=
    { toFun := fun x => pt (fun i => x (σ (Fin.castAdd 1 i))) (∑ m, v m * x m)
      map_add' := fun x y => by
        rw [pt_add]
        congr 1
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, fV]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }
  have hT : ∀ x, T x = pt (fun i => x (σ (Fin.castAdd 1 i))) (∑ m, v m * x m) := fun x => rfl
  refine ⟨T, ?_, fun x => by rw [hT, nV_pt]⟩
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [hT] at hx
  have h1 : ∀ i, x (σ (Fin.castAdd 1 i)) = 0 := fun i => by
    have := congrArg nH hx
    rw [nH_pt] at this
    simpa [nH] using congrFun this i
  have h2 : ∑ m, v m * x m = 0 := by
    have := congrArg nV hx
    rwa [nV_pt] at this
  have za : ∀ t : Fin (k + 1), t ≠ Fin.natAdd k 0 → ∃ i, t = Fin.castAdd 1 i := by
    intro t ht
    refine Fin.addCases (motive := fun t => t ≠ Fin.natAdd k 0 → ∃ i, t = Fin.castAdd 1 i)
      (fun i _ => ⟨i, rfl⟩) (fun i h => absurd (by rw [Subsingleton.elim i 0]) h) t ht
  have h3 : ∀ m, m ≠ j → x m = 0 := by
    intro m hm
    have hσm : σ m ≠ Fin.natAdd k 0 := fun h => hm (by rw [← hσσ m, h, hσj])
    obtain ⟨i, hi⟩ := za _ hσm
    have := h1 i
    rwa [← hi, hσσ] at this
  have hxj : x j = 0 := by
    rw [Finset.sum_eq_single j (fun m _ hm => by rw [h3 m hm, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)] at h2
    exact (mul_eq_zero.mp h2).resolve_left hj
  funext m
  by_cases hm : m = j
  · rw [hm, hxj]; rfl
  · exact h3 m hm
lemma gu {k : ℕ} {A : Set (Fin (k + 1) → ℝ)} (hA : IsCB A) (hle : volume (gj A) ≤ volume A) : ∃ c, ∀ x ∈ A, c - x ∈ A := by
  classical
  have hV : 0 < volume.real A :=
    ENNReal.toReal_pos hA.volume_pos.ne' hA.compact.measure_lt_top.ne
  have hV0 : volume.real A ≠ 0 := hV.ne'
  have hAm : MeasurableSet A := hA.compact.isClosed.measurableSet
  obtain ⟨g, hg⟩ : ∃ g : Fin (k + 1) → ℝ, ∀ w : Fin (k + 1) → ℝ,
      ∫ x in A, ∑ i, w i * x i = volume.real A * ∑ i, w i * g i := by
    refine ⟨fun i => (∫ x in A, x i) / volume.real A, fun w => ?_⟩
    have hint : ∀ i, Integrable (fun x : Fin (k + 1) → ℝ => w i * x i) (volume.restrict A) :=
      fun i => (continuous_const.mul (continuous_apply i)).continuousOn.integrableOn_compact
        hA.compact
    rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    field_simp
  refine ⟨(2 : ℝ) • g, fun x hx => ?_⟩
  by_contra hy
  obtain ⟨φ, r, hφA, hφy⟩ := geometric_hahn_banach_closed_point hA.convex hA.compact.isClosed hy
  obtain ⟨v, hφ⟩ : ∃ v : Fin (k + 1) → ℝ, ∀ z, φ z = ∑ i, v i * z i := by
    refine ⟨fun i => φ (fun j => if i = j then 1 else 0), fun z => ?_⟩
    have h := LinearMap.pi_apply_eq_sum_univ (φ : (Fin (k + 1) → ℝ) →ₗ[ℝ] ℝ) z
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  have hv : v ≠ 0 := by
    rintro rfl
    have h1 := hφA x hx
    rw [hφ] at h1 hφy
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at h1 hφy
    linarith
  obtain ⟨T, hTinj, hTv⟩ := gt hv
  have hTA : IsCB (T '' A) := hA.image_linearMap hTinj
  obtain ⟨a, b, hH⟩ := hTA.exists_heights
  have za := hH.integral_nV hTA (hH.secVol_symm hTA (gr T hle))
  have hcv := gs hTinj hAm hTA.compact.isClosed.measurableSet
    (F := nV) (continuous_apply _).measurable
  have zb : volume.real (T '' A) = |LinearMap.det T| * volume.real A := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_image_linearMap, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  have hdet : |LinearMap.det T| ≠ 0 := abs_ne_zero.2 (go hTinj)
  have zc : ∫ x in A, ∑ i, v i * x i = (a + b) / 2 * volume.real A := by
    have : ∫ x in A, nV (T x) = ∫ x in A, ∑ i, v i * x i :=
      integral_congr_ae (Eventually.of_forall fun x => hTv x)
    rw [← this, hcv, za, zb]
    field_simp
  have hvg : ∑ i, v i * g i = (a + b) / 2 := by
    have := (hg v).symm.trans zc
    field_simp at this ⊢
    linarith
  have hxa : a ≤ φ x := by
    rw [hφ, ← hTv]; exact (hH.mem _ (Set.mem_image_of_mem T hx)).1
  obtain ⟨xb, hxb, hxbv⟩ : ∃ xb ∈ A, φ xb = b := by
    obtain ⟨y, hy⟩ := hH.top
    obtain ⟨xb, hxb, hTxb⟩ := hy
    refine ⟨xb, hxb, ?_⟩
    rw [hφ, ← hTv, hTxb, nV_pt]
  have hlin : φ ((2 : ℝ) • g - x) = 2 * ∑ i, v i * g i - φ x := by
    rw [hφ, hφ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 := hφA xb hxb
  linarith
lemma gv {n : ℕ} {A : Set (Fin n → ℝ)} (hA : IsCB A) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) {P Q : Fin n → ℝ} (hP : P ∈ A) (hQ : Q ∈ A) : 0 < xcorr A A (ρ • (P - Q)) := by
  obtain ⟨a₀, ha₀⟩ := hA.interior_nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a₀ ha₀
  have h1ρ : 0 < 1 - ρ := by linarith
  have hsub : ball (ρ • P + (1 - ρ) • a₀) ((1 - ρ) * r) ⊆ A ∩ {w | w - ρ • (P - Q) ∈ A} := by
    intro w hw
    have huA : a₀ + (1 - ρ)⁻¹ • (w - (ρ • P + (1 - ρ) • a₀)) ∈ A := by
      refine interior_subset (hball ?_)
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h1ρ, inv_mul_lt_iff₀ h1ρ, ← dist_eq_norm]
      exact hw
    have hw' : ρ • P + (1 - ρ) • (a₀ + (1 - ρ)⁻¹ • (w - (ρ • P + (1 - ρ) • a₀))) = w := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ h1ρ.ne', one_smul]; abel
    have hwz : ρ • Q + (1 - ρ) • (a₀ + (1 - ρ)⁻¹ • (w - (ρ • P + (1 - ρ) • a₀))) =
        w - ρ • (P - Q) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ h1ρ.ne', one_smul, smul_sub]; abel
    refine ⟨?_, ?_⟩
    · rw [← hw']; exact hA.convex hP huA hρ0 h1ρ.le (by ring)
    · show w - ρ • (P - Q) ∈ A
      rw [← hwz]; exact hA.convex hQ huA hρ0 h1ρ.le (by ring)
  have hpos : 0 < volume (ball (ρ • P + (1 - ρ) • a₀) ((1 - ρ) * r)) :=
    measure_ball_pos volume _ (mul_pos h1ρ hr)
  rw [xcorr, measureReal_def]
  exact ENNReal.toReal_pos (hpos.trans_le (measure_mono hsub)).ne'
    ((measure_mono Set.inter_subset_left).trans_lt hA.compact.measure_lt_top).ne
lemma gw {n m : ℕ} {A : Set (Fin n → ℝ)} {B : Set (Fin m → ℝ)} (hA : IsCB A) (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B) (hspec : isSpectral (productSet A B)) : volume (gj A) ≤ volume A := by
  have hAm : MeasurableSet A := hA.compact.isClosed.measurableSet
  have hD := gk hA.compact
  have za : ∀ p q, p ∈ A → q ∈ A → (2 : ℝ)⁻¹ • (p + q) ∈ A := fun p q hp hq => by
    rw [smul_add]
    exact hA.convex hp hq (by norm_num) (by norm_num) (by norm_num)
  have hρ : ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      ENNReal.ofReal (ρ ^ n) * volume (gj A) ≤ volume A := by
    intro ρ hρ0 hρ1
    have hE : IsCompact (ρ • gj A) := hD.image (continuous_const_smul ρ)
    calc ENNReal.ofReal (ρ ^ n) * volume (gj A) = volume (ρ • gj A) := by
          rw [Measure.addHaar_smul_of_nonneg volume hρ0.le, Module.finrank_fin_fun]
      _ ≤ volume A := by
          refine fJ hAm hA.compact.isBounded hBm hBb hspec
            hE.isClosed.measurableSet hE.isBounded fun z hz => ?_
          obtain ⟨w, hwE, hwz⟩ : (ρ • gj A ∩ {x | x - z ∈ ρ • gj A}).Nonempty := by
            by_contra h
            rw [Set.not_nonempty_iff_eq_empty] at h
            rw [xcorr, h, measureReal_empty] at hz
            exact lt_irrefl _ hz
          obtain ⟨d₁, ⟨⟨p, q⟩, ⟨hp, hq⟩, hd₁⟩, hw⟩ := hwE
          obtain ⟨d₂, ⟨⟨p', q'⟩, ⟨hp', hq'⟩, hd₂⟩, hwz'⟩ := (show w - z ∈ ρ • gj A from hwz)
          simp only at hd₁ hd₂ hw hwz'
          have hz' : z = ρ • ((2 : ℝ)⁻¹ • (p + q') - (2 : ℝ)⁻¹ • (q + p')) := by
            have h1 : z = w - (w - z) := by abel
            rw [h1, ← hwz', ← hw, ← hd₁, ← hd₂]
            simp only [smul_sub, smul_add]
            abel
          rw [hz']
          exact gv hA hρ0.le hρ1 (za _ _ hp hq') (za _ _ hq hp')
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (ρ ^ n) * volume (gj A)) (𝓝[<] 1)
      (𝓝 (volume (gj A))) := by
    have h1 : Tendsto (fun ρ : ℝ => ENNReal.ofReal (ρ ^ n)) (𝓝[<] 1) (𝓝 1) := by
      have h0 : Tendsto (fun ρ : ℝ => ρ ^ n) (𝓝[<] 1) (𝓝 1) := by
        have := ((continuous_pow n).tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
        rwa [one_pow] at this
      simpa using ENNReal.tendsto_ofReal h0
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ'
  exact hρ ρ hρ'.1 hρ'.2
lemma centrallySymmetric_of_isSpectral_productSet {k m : ℕ} {A : Set (Fin (k + 1) → ℝ)}
    {B : Set (Fin m → ℝ)} (hA : IsCB A) (hBm : MeasurableSet B) (hBb : Bornology.IsBounded B)
    (hspec : isSpectral (productSet A B)) : ∃ c, ∀ x ∈ A, c - x ∈ A :=
  gu hA
    (gw hA hBm hBb hspec)
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Set
open scoped Pointwise
namespace FCBridge
variable {n : ℕ}
lemma continuous_dotProduct_left' (ξ : Fin n → ℝ) : Continuous fun x : Fin n → ℝ => ξ ⬝ᵥ x :=
  continuous_const.dotProduct continuous_id
def suppSet (A : Set (Fin n → ℝ)) (ξ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ A ∧ ∀ y ∈ A, ξ ⬝ᵥ y ≤ ξ ⬝ᵥ x}
structure RegularAt (A : Set (Fin n → ℝ)) (x ξ : Fin n → ℝ) : Prop where
  mem : x ∈ A
  unit : ξ ⬝ᵥ ξ = 1
  supp : ∀ y ∈ A, ξ ⬝ᵥ y ≤ ξ ⬝ᵥ x
  uniq : ∀ w : Fin n → ℝ, w ≠ 0 → (∀ y ∈ A, w ⬝ᵥ y ≤ w ⬝ᵥ x) → ∃ c : ℝ, 0 < c ∧ w = c • ξ
lemma isCompact_suppSet {A : Set (Fin n → ℝ)} (hA : IsCompact A) (ξ : Fin n → ℝ) : IsCompact (suppSet A ξ) := by
  refine hA.of_isClosed_subset ?_ fun x hx => hx.1
  have : suppSet A ξ = A ∩ ⋂ y ∈ A, {x | ξ ⬝ᵥ y ≤ ξ ⬝ᵥ x} := by
    ext x; simp [suppSet]
  rw [this]
  exact hA.isClosed.inter (isClosed_biInter fun y _ =>
    isClosed_le continuous_const (continuous_dotProduct_left' ξ))
lemma gx (φ : StrongDual ℝ (Fin n → ℝ)) : ∃ w : Fin n → ℝ, ∀ z, φ z = w ⬝ᵥ z := by
  classical
  refine ⟨fun i => φ (fun j => if i = j then 1 else 0), fun z => ?_⟩
  have h := LinearMap.pi_apply_eq_sum_univ (φ : (Fin n → ℝ) →ₗ[ℝ] ℝ) z
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [h, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]
lemma measure_diff_eq_zero {A : Set (Fin n → ℝ)} (hA : IsCB A) {μ : Measure (Fin n → ℝ)} [SFinite μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ A} = Aᶜ.indicator 1 x) : μ (interior A - interior A) = 0 := by
  have hAm : MeasurableSet A := hA.compact.isClosed.measurableSet
  have h0 : ∫⁻ x, A.indicator (fun x => μ {s | x - s ∈ A}) x = 0 := by
    rw [lintegral_indicator hAm]
    refine (setLIntegral_congr_fun_ae hAm (hμ.mono fun x hx _ => hx)).trans ?_
    refine (setLIntegral_congr_fun hAm (g := fun _ => 0) fun x hx => ?_).trans (by simp)
    exact Set.indicator_of_notMem (by simpa using hx) _
  have hF : Measurable (Function.uncurry fun (x s : Fin n → ℝ) =>
      A.indicator (1 : (Fin n → ℝ) → ENNReal) x * A.indicator 1 (x - s)) := by
    refine ((measurable_one.indicator hAm).comp measurable_fst).mul
      ((measurable_one.indicator hAm).comp (measurable_fst.sub measurable_snd))
  have hswap := lintegral_lintegral_swap (μ := volume) (ν := μ) hF.aemeasurable
  have hin : ∀ x, ∫⁻ s, A.indicator (1 : (Fin n → ℝ) → ENNReal) x * A.indicator 1 (x - s) ∂μ =
      A.indicator (fun x => μ {s | x - s ∈ A}) x := fun x => by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp only [Pi.one_apply, one_mul]
      have hm : MeasurableSet {s : Fin n → ℝ | x - s ∈ A} :=
        hAm.preimage (measurable_const.sub measurable_id)
      rw [← lintegral_indicator_one hm]
      rfl
    · simp [Set.indicator_of_notMem hx]
  simp_rw [hin] at hswap
  rw [h0] at hswap
  have hae : ∀ᵐ s ∂μ, ∫⁻ x, A.indicator (1 : (Fin n → ℝ) → ENNReal) x *
      A.indicator 1 (x - s) = 0 := by
    have := (lintegral_eq_zero_iff hF.lintegral_prod_left').mp hswap.symm
    filter_upwards [this] with s hs
    exact hs
  have hpos : ∀ s ∈ interior A - interior A,
      ∫⁻ x, A.indicator (1 : (Fin n → ℝ) → ENNReal) x * A.indicator 1 (x - s) ≠ 0 := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have hU : IsOpen (interior A ∩ {x | x - (a - b) ∈ interior A}) :=
      isOpen_interior.inter (isOpen_interior.preimage (continuous_id.sub continuous_const))
    have hne : (interior A ∩ {x | x - (a - b) ∈ interior A}).Nonempty :=
      ⟨a, ha, by simpa using hb⟩
    refine (lt_of_lt_of_le (hU.measure_pos volume hne) ?_).ne'
    calc volume (interior A ∩ {x | x - (a - b) ∈ interior A})
        = ∫⁻ x, (interior A ∩ {x | x - (a - b) ∈ interior A}).indicator 1 x :=
          (lintegral_indicator_one hU.measurableSet).symm
      _ ≤ ∫⁻ x, A.indicator (1 : (Fin n → ℝ) → ENNReal) x * A.indicator 1 (x - (a - b)) := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ interior A ∩ {x | x - (a - b) ∈ interior A}
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (interior_subset hx.1),
              Set.indicator_of_mem (interior_subset hx.2)]
            simp
          · rw [Set.indicator_of_notMem hx]; exact zero_le
  exact measure_mono_null (fun s hs => hpos s hs) (ae_iff.mp hae)
lemma gy {A : Set (Fin n → ℝ)} (hA : IsCB A) : A ⊆ closure (interior A) := by
  rw [hA.convex.closure_interior_eq_closure_of_nonempty_interior hA.interior_nonempty, hA.compact.isClosed.closure_eq]
lemma gz {A : Set (Fin n → ℝ)} (hA : IsCB A) {t x : Fin n → ℝ} (ht : t ∉ interior A - interior A) (hx : x ∈ A) (hxt : x - t ∈ A) : ∃ w : Fin n → ℝ, w ≠ 0 ∧ (∀ y ∈ A, w ⬝ᵥ y ≤ w ⬝ᵥ x) ∧ ∀ y ∈ A, w ⬝ᵥ x ≤ w ⬝ᵥ (y + t) := by
  have hdisj : Disjoint (interior A) (interior A + {t}) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨a, ha, b, hb, rfl⟩
    exact ht ⟨a + b, hy, a, ha, by rw [Set.mem_singleton_iff.mp hb]; exact add_sub_cancel_left a t⟩
  obtain ⟨φ, u, h1, h2⟩ := geometric_hahn_banach_open_open hA.convex.interior isOpen_interior
    (hA.convex.interior.add (convex_singleton t)) isOpen_interior.add_right hdisj
  obtain ⟨w, hw⟩ := gx φ
  have hcont := continuous_dotProduct_left' w
  have hle : ∀ y ∈ A, w ⬝ᵥ y ≤ u := by
    intro y hy
    have hcl : IsClosed {z : Fin n → ℝ | w ⬝ᵥ z ≤ u} := isClosed_le hcont continuous_const
    exact (hcl.closure_subset_iff.mpr fun a ha => by
      show w ⬝ᵥ a ≤ u
      rw [← hw]; exact (h1 a ha).le)
      (gy hA hy)
  have hge : ∀ y ∈ A, u ≤ w ⬝ᵥ (y + t) := by
    intro y hy
    have hcl : IsClosed {z : Fin n → ℝ | u ≤ w ⬝ᵥ (z + t)} :=
      isClosed_le continuous_const (hcont.comp (continuous_id.add continuous_const))
    refine (hcl.closure_subset_iff.mpr fun a ha => ?_) (gy hA hy)
    show u ≤ w ⬝ᵥ (a + t)
    rw [← hw]; exact (h2 (a + t) ⟨a, ha, t, rfl, rfl⟩).le
  have hxu : w ⬝ᵥ x = u := le_antisymm (hle x hx) (by simpa using hge (x - t) hxt)
  refine ⟨w, fun h0 => ?_, fun y hy => hxu ▸ hle y hy, fun y hy => hxu ▸ hge y hy⟩
  obtain ⟨a, ha⟩ := hA.interior_nonempty
  have e1 := h1 a ha
  have e2 := h2 (a + t) ⟨a, ha, t, rfl, rfl⟩
  rw [hw, h0, zero_dotProduct] at e1 e2
  linarith
lemma RegularAt.ne_zero {A : Set (Fin n → ℝ)} {x ξ : Fin n → ℝ} (hx : RegularAt A x ξ) :
    ξ ≠ 0 := fun h => by simpa [h] using hx.unit
lemma gA {A : Set (Fin n → ℝ)} (hA : IsCB A) {x ξ t : Fin n → ℝ} (hx : RegularAt A x ξ) (ht : t ∉ interior A - interior A) (hxt : x - t ∈ A) : x - t ∈ suppSet A (-ξ) := by
  obtain ⟨w, hw0, hwx, hwt⟩ := gz hA ht hx.mem hxt
  obtain ⟨c, hc, rfl⟩ := hx.uniq w hw0 hwx
  refine ⟨hxt, fun y hy => ?_⟩
  have h := hwt y hy
  rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul, dotProduct_add, mul_add] at h
  have h' : ξ ⬝ᵥ x ≤ ξ ⬝ᵥ y + ξ ⬝ᵥ t := by
    by_contra hcon
    rw [not_le] at hcon
    have := mul_lt_mul_of_pos_left hcon hc
    rw [mul_add] at this
    linarith
  simp only [neg_dotProduct, dotProduct_sub]
  linarith
lemma gB {A : Set (Fin n → ℝ)} (hA : IsCB A) {x ξ : Fin n → ℝ} (hx : RegularAt A x ξ) {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hSU : ∀ y ∈ suppSet A (-ξ), x - y ∈ U) : ∃ r > 0, ∀ t, t ∉ interior A - interior A → ∀ z, dist z x < r → z - t ∈ A → t ∈ U := by
  obtain ⟨R, hR⟩ := hA.compact.isBounded.subset_closedBall 0
  set K : Set (Fin n → ℝ) := closedBall 0 (‖x‖ + 1 + R) ∩ (interior A - interior A)ᶜ ∩ Uᶜ
    with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).inter_right
      ((isOpen_interior.sub_left).isClosed_compl) |>.inter_right hU.isClosed_compl
  have za : A.Nonempty := hA.interior_nonempty.mono interior_subset
  have hpos : ∀ t ∈ K, 0 < infDist (x - t) A := by
    intro t ht
    refine lt_of_le_of_ne infDist_nonneg (fun h0 => ht.2 ?_)
    have hxt : x - t ∈ A :=
      (hA.compact.isClosed.mem_iff_infDist_zero za).mpr h0.symm
    have := hSU _ (gA hA hx ht.1.2 hxt)
    rwa [sub_sub_cancel] at this
  have hcont : Continuous fun t : Fin n → ℝ => infDist (x - t) A :=
    (continuous_infDist_pt A).comp (continuous_const.sub continuous_id)
  rcases K.eq_empty_or_nonempty with hK0 | hKne
  · refine ⟨1, one_pos, fun t ht z hz hzt => ?_⟩
    by_contra htU
    have htK : t ∈ K := by
      refine ⟨⟨?_, ht⟩, htU⟩
      rw [mem_closedBall, dist_zero_right]
      have h1 : ‖z - t‖ ≤ R := by simpa using hR hzt
      have h2 : ‖z‖ ≤ ‖x‖ + 1 := by
        have := norm_le_norm_add_norm_sub' z x
        rw [← dist_eq_norm] at this; linarith
      calc ‖t‖ = ‖z - (z - t)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖z‖ + ‖z - t‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + 1 + R := by linarith
    rw [hK0] at htK; exact htK
  obtain ⟨t₀, ht₀, hmin⟩ := hKc.exists_isMinOn hKne hcont.continuousOn
  refine ⟨min (infDist (x - t₀) A) 1, lt_min (hpos t₀ ht₀) one_pos, fun t ht z hz hzt => ?_⟩
  by_contra htU
  have htK : t ∈ K := by
    refine ⟨⟨?_, ht⟩, htU⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖z - t‖ ≤ R := by simpa using hR hzt
    have h2 : ‖z‖ ≤ ‖x‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z x
      rw [← dist_eq_norm] at this; linarith [min_le_right (infDist (x - t₀) A) 1]
    calc ‖t‖ = ‖z - (z - t)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖z‖ + ‖z - t‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + 1 + R := by linarith
  have h1 := isMinOn_iff.mp hmin t htK
  have h2 : infDist (x - t) A ≤ dist (x - t) (z - t) := infDist_le_dist_of_mem hzt
  rw [dist_sub_right, dist_comm] at h2
  linarith [min_le_left (infDist (x - t₀) A) 1]
lemma gC {A : Set (Fin n → ℝ)} (hA : IsCB A) (x ξ : Fin n → ℝ) :
    IsCompact {s : Fin n → ℝ | x - s ∈ suppSet A ξ} :=
  (Homeomorph.subLeft x).isCompact_preimage.mpr (isCompact_suppSet hA.compact ξ)
lemma gD {A : Set (Fin n → ℝ)} (hA : IsCB A) {μ : Measure (Fin n → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ A} = Aᶜ.indicator 1 x) {x ξ : Fin n → ℝ} (hx : RegularAt A x ξ) : 1 ≤ μ {s | x - s ∈ suppSet A (-ξ)} := by
  set E : Set (Fin n → ℝ) := {s | x - s ∈ suppSet A (-ξ)} with hE
  have hEc : IsCompact E := gC hA x (-ξ)
  by_contra hlt
  rw [not_le] at hlt
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), μ (cthickening r E) < 1 :=
    (tendsto_measure_cthickening_of_isCompact hEc).eventually (gt_mem_nhds hlt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set δ := ε / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hμU : μ (thickening δ E) < 1 :=
    (measure_mono (thickening_subset_cthickening δ E)).trans_lt
      (hball (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]; linarith))
  have hSU : ∀ y ∈ suppSet A (-ξ), x - y ∈ thickening δ E := fun y hy =>
    self_subset_thickening hδ0 E (show x - (x - y) ∈ suppSet A (-ξ) by rwa [sub_sub_cancel])
  obtain ⟨r, hr, hV⟩ := gB hA hx isOpen_thickening hSU
  have hD := measure_diff_eq_zero hA hμ
  have hbound : ∀ z, dist z x < r → μ {s | z - s ∈ A} < 1 := by
    intro z hz
    calc μ {s | z - s ∈ A} ≤ μ (thickening δ E ∪ (interior A - interior A)) := by
          refine measure_mono fun s hs => ?_
          by_cases hsD : s ∈ interior A - interior A
          · exact Or.inr hsD
          · exact Or.inl (hV s hsD z hz hs)
      _ ≤ μ (thickening δ E) + μ (interior A - interior A) := measure_union_le _ _
      _ < 1 := by rw [hD, add_zero]; exact hμU
  have hW : IsOpen (ball x r ∩ Aᶜ) := isOpen_ball.inter hA.compact.isClosed.isOpen_compl
  have hWne : (ball x r ∩ Aᶜ).Nonempty := by
    set s := r / (2 * (‖ξ‖ + 1)) with hs
    have hs0 : 0 < s := by positivity
    refine ⟨x + s • ξ, ?_, fun hmem => ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0.le]
      have : s * ‖ξ‖ < s * (‖ξ‖ + 1) := by nlinarith
      calc s * ‖ξ‖ < s * (‖ξ‖ + 1) := this
        _ = r / 2 := by rw [hs]; field_simp
        _ < r := by linarith
    · have h := hx.supp _ hmem
      rw [dotProduct_add, dotProduct_smul, hx.unit, smul_eq_mul, mul_one] at h
      linarith
  have za : volume (ball x r ∩ Aᶜ) ≠ 0 := (hW.measure_pos volume hWne).ne'
  obtain ⟨z, hz, hzeq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae za
    (ae_restrict_of_ae hμ)
  rw [Set.indicator_of_mem hz.2, Pi.one_apply] at hzeq
  have := hbound z hz.1
  rw [hzeq] at this
  exact lt_irrefl _ this
lemma gE {A : Set (Fin n → ℝ)} {x x' ξ ξ' : Fin n → ℝ} (hx : RegularAt A x ξ) (hx' : RegularAt A x' ξ') (hne : ξ ≠ ξ') : Disjoint {s | x - s ∈ suppSet A (-ξ)} {s | x' - s ∈ suppSet A (-ξ')} := by
  rw [Set.disjoint_left]
  intro s hs hs'
  have hlt : ξ ⬝ᵥ x' < ξ ⬝ᵥ x := by
    refine lt_of_le_of_ne (hx.supp x' hx'.mem) fun heq => hne ?_
    obtain ⟨c, hc, hcξ⟩ := hx'.uniq ξ hx.ne_zero fun y hy => heq ▸ hx.supp y hy
    have h1 : c * c = 1 := by
      have := hx.unit
      rw [hcξ, smul_dotProduct, dotProduct_smul, hx'.unit, smul_eq_mul, smul_eq_mul, mul_one] at this
      exact this
    have hc1 : c = 1 := by nlinarith
    rw [hcξ, hc1, one_smul]
  have h1 := hs.2 (x' - s) hs'.1
  simp only [neg_dotProduct, dotProduct_sub] at h1
  linarith
lemma dot_self_nonneg (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
lemma gF (v : Fin n → ℝ) : ‖v‖ ^ 2 ≤ v ⬝ᵥ v := by
  have h : ‖v‖ ≤ Real.sqrt (v ⬝ᵥ v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    have : v i * v i ≤ v ⬝ᵥ v :=
      Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
        (Finset.mem_univ i)
    rw [sq]; exact this
  calc ‖v‖ ^ 2 ≤ Real.sqrt (v ⬝ᵥ v) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = v ⬝ᵥ v := Real.sq_sqrt (dot_self_nonneg v)
lemma gG (v : Fin n → ℝ) : v ⬝ᵥ v ≤ n * ‖v‖ ^ 2 := by
  have : ∀ i, v i * v i ≤ ‖v‖ ^ 2 := fun i => by
    have h := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at h
    nlinarith [abs_nonneg (v i), abs_mul_abs_self (v i)]
  calc v ⬝ᵥ v = ∑ i, v i * v i := rfl
    _ ≤ ∑ _i : Fin n, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ => this i
    _ = n * ‖v‖ ^ 2 := by simp
lemma gH {A : Set (Fin n → ℝ)} {z c w : Fin n → ℝ} (hB : ∀ v, (v - c) ⬝ᵥ (v - c) < (z - c) ⬝ᵥ (z - c) → v ∈ A) (hzc : z ≠ c) (hw0 : w ≠ 0) (hw : ∀ y ∈ A, w ⬝ᵥ y ≤ w ⬝ᵥ z) : ∃ l : ℝ, 0 < l ∧ w = l • (z - c) := by
  obtain ⟨g, hg⟩ : ∃ g, g = z - c := ⟨_, rfl⟩
  rw [← hg] at hB ⊢
  have za : g ≠ 0 := by rw [hg]; exact sub_ne_zero.mpr hzc
  have hgg : 0 < g ⬝ᵥ g := lt_of_le_of_ne (dot_self_nonneg g) fun h =>
    za (dotProduct_self_eq_zero.mp h.symm)
  have key : ∀ d, g ⬝ᵥ d < 0 → w ⬝ᵥ d ≤ 0 := by
    intro d hd
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = -(g ⬝ᵥ d) / (d ⬝ᵥ d + 1) := ⟨_, rfl⟩
    have hdd := dot_self_nonneg d
    have hs0 : 0 < s := by rw [hs]; exact div_pos (by linarith) (by linarith)
    have hsd : s * (d ⬝ᵥ d + 1) = -(g ⬝ᵥ d) := by rw [hs]; field_simp
    have hmem : z + s • d ∈ A := by
      refine hB _ ?_
      have e : z + s • d - c = g + s • d := by rw [hg]; abel
      have e2 : (g + s • d) ⬝ᵥ (g + s • d) =
          g ⬝ᵥ g + 2 * s * (g ⬝ᵥ d) + s * s * (d ⬝ᵥ d) := by
        simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm d g]
        ring
      rw [e, e2]
      nlinarith
    have h := hw _ hmem
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h
    nlinarith
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (w ⬝ᵥ g) / (g ⬝ᵥ g) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Fin n → ℝ, h = w - l • g := ⟨_, rfl⟩
  have hhg : h ⬝ᵥ g = 0 := by
    rw [hh, sub_dotProduct, smul_dotProduct, smul_eq_mul, hl, div_mul_cancel₀ _ hgg.ne']
    ring
  have hgh : g ⬝ᵥ h = 0 := by rw [dotProduct_comm]; exact hhg
  have hw' : w = l • g + h := by rw [hh]; abel
  have hle : ∀ η : ℝ, 0 < η → h ⬝ᵥ h ≤ l * η * (g ⬝ᵥ g) := by
    intro η hη
    have hd : g ⬝ᵥ (h - η • g) < 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, hgh]; nlinarith
    have h1 := key _ hd
    have e : w ⬝ᵥ (h - η • g) = h ⬝ᵥ h - l * η * (g ⬝ᵥ g) := by
      rw [hw']
      simp only [add_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul, hgh, hhg]
      ring
    rw [e] at h1; linarith
  have hh0 : h ⬝ᵥ h = 0 := by
    refine le_antisymm ?_ (dot_self_nonneg h)
    by_contra hpos
    rw [not_le] at hpos
    obtain ⟨η, hη⟩ : ∃ η : ℝ, η = (h ⬝ᵥ h) / (2 * (|l| * (g ⬝ᵥ g) + 1)) := ⟨_, rfl⟩
    have hden : 0 < 2 * (|l| * (g ⬝ᵥ g) + 1) := by positivity
    have hη0 : 0 < η := by rw [hη]; exact div_pos hpos hden
    have h1 := hle η hη0
    have h2 : l * η * (g ⬝ᵥ g) ≤ |l| * η * (g ⬝ᵥ g) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self l) hη0.le) hgg.le
    have e : (|l| * (g ⬝ᵥ g) + 1) * η = (h ⬝ᵥ h) / 2 := by rw [hη]; field_simp
    have h3 : |l| * η * (g ⬝ᵥ g) < h ⬝ᵥ h := by nlinarith [abs_nonneg l]
    linarith
  have hh' : h = 0 := dotProduct_self_eq_zero.mp hh0
  rw [hh', add_zero] at hw'
  refine ⟨l, lt_of_le_of_ne ?_ fun hl0 => hw0 (by rw [hw', ← hl0, zero_smul]), hw'⟩
  have h1 := key (-g) (by rw [dotProduct_neg]; linarith)
  rw [hw', smul_dotProduct, dotProduct_neg, smul_eq_mul] at h1
  nlinarith
lemma exists_regular_near {A : Set (Fin n → ℝ)} (hA : IsCB A) {y : Fin n → ℝ} (hy : y ∈ frontier A) {ε : ℝ} (hε : 0 < ε) : ∃ z ξ, RegularAt A z ξ ∧ dist z y < ε := by
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = ε / (n + 2) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; positivity
  have hyA : y ∈ A := hA.compact.isClosed.frontier_subset hy
  obtain ⟨c, hc, hcy⟩ : ∃ c ∈ interior A, dist y c < κ := by
    have := gy hA hyA
    rw [Metric.mem_closure_iff] at this
    exact this κ hκ0
  have hqc : Continuous fun v : Fin n → ℝ => (v - c) ⬝ᵥ (v - c) :=
    (continuous_id.sub continuous_const).dotProduct (continuous_id.sub continuous_const)
  have hfr : IsCompact (frontier A) :=
    hA.compact.of_isClosed_subset isClosed_frontier hA.compact.isClosed.frontier_subset
  obtain ⟨z, hz, hzmin⟩ := hfr.exists_isMinOn ⟨y, hy⟩ hqc.continuousOn
  have hzmin' : ∀ v ∈ frontier A, (z - c) ⬝ᵥ (z - c) ≤ (v - c) ⬝ᵥ (v - c) :=
    fun v hv => isMinOn_iff.mp hzmin v hv
  have hzA : z ∈ A := hA.compact.isClosed.frontier_subset hz
  have za : z ∉ interior A := fun h => hz.2 h
  have hzc : z ≠ c := fun h => za (h ▸ hc)
  have hzz : 0 < (z - c) ⬝ᵥ (z - c) := lt_of_le_of_ne (dot_self_nonneg _) fun h =>
    hzc (sub_eq_zero.mp (dotProduct_self_eq_zero.mp h.symm))
  have hB : ∀ v, (v - c) ⬝ᵥ (v - c) < (z - c) ⬝ᵥ (z - c) → v ∈ A := by
    intro v hv
    have hconv : Convex ℝ {v | (v - c) ⬝ᵥ (v - c) < (z - c) ⬝ᵥ (z - c)} := by
      intro v₁ hv₁ v₂ hv₂ a b ha hb hab
      show (a • v₁ + b • v₂ - c) ⬝ᵥ (a • v₁ + b • v₂ - c) < (z - c) ⬝ᵥ (z - c)
      have e : a • v₁ + b • v₂ - c = a • (v₁ - c) + b • (v₂ - c) := by
        calc a • v₁ + b • v₂ - c = a • v₁ + b • v₂ - (a + b) • c := by rw [hab, one_smul]
          _ = a • (v₁ - c) + b • (v₂ - c) := by rw [add_smul, smul_sub, smul_sub]; abel
      have hv₁' : (v₁ - c) ⬝ᵥ (v₁ - c) < (z - c) ⬝ᵥ (z - c) := hv₁
      have hv₂' : (v₂ - c) ⬝ᵥ (v₂ - c) < (z - c) ⬝ᵥ (z - c) := hv₂
      rw [e]
      generalize (z - c) ⬝ᵥ (z - c) = R at hv₁' hv₂' ⊢
      generalize v₁ - c = u at hv₁' ⊢
      generalize v₂ - c = w at hv₂' ⊢
      have hUW := dot_self_nonneg (u - w)
      have e2 : (a • u + b • w) ⬝ᵥ (a • u + b • w) =
          a * a * (u ⬝ᵥ u) + 2 * a * b * (u ⬝ᵥ w) + b * b * (w ⬝ᵥ w) := by
        simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm w u]
        ring
      have e3 : (u - w) ⬝ᵥ (u - w) = u ⬝ᵥ u - 2 * (u ⬝ᵥ w) + w ⬝ᵥ w := by
        simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm w u]
        ring
      rw [e2]
      rw [e3] at hUW
      have hb' : b = 1 - a := by linarith
      subst hb'
      have hid : a * a * (u ⬝ᵥ u) + 2 * a * (1 - a) * (u ⬝ᵥ w) + (1 - a) * (1 - a) * (w ⬝ᵥ w) =
          a * (u ⬝ᵥ u) + (1 - a) * (w ⬝ᵥ w) -
            a * (1 - a) * (u ⬝ᵥ u - 2 * (u ⬝ᵥ w) + w ⬝ᵥ w) := by ring
      have hD := mul_nonneg (mul_nonneg ha hb) hUW
      have hlt : a * (u ⬝ᵥ u) + (1 - a) * (w ⬝ᵥ w) < R := by
        rcases eq_or_lt_of_le ha with h0 | hpos
        · rw [← h0]; linarith
        · have h1 : a * (u ⬝ᵥ u) < a * R := mul_lt_mul_of_pos_left hv₁' hpos
          have h2 : (1 - a) * (w ⬝ᵥ w) ≤ (1 - a) * R := mul_le_mul_of_nonneg_left hv₂'.le hb
          linarith
      rw [hid]; linarith
    have zb : IsOpen {v | (v - c) ⬝ᵥ (v - c) < (z - c) ⬝ᵥ (z - c)} :=
      isOpen_lt hqc continuous_const
    have hsub : {v | (v - c) ⬝ᵥ (v - c) < (z - c) ⬝ᵥ (z - c)} ⊆
        interior A ∪ (closure A)ᶜ := by
      intro v hv'
      by_cases hvi : v ∈ interior A
      · exact Or.inl hvi
      · refine Or.inr fun hvc => ?_
        have := hzmin' v ⟨hvc, hvi⟩
        exact absurd hv' (not_lt.mpr this)
    have hcq : c ∈ {v | (v - c) ⬝ᵥ (v - c) < (z - c) ⬝ᵥ (z - c)} := by
      show (c - c) ⬝ᵥ (c - c) < (z - c) ⬝ᵥ (z - c)
      rw [sub_self, zero_dotProduct]
      exact hzz
    have := hconv.isPreconnected.subset_left_of_subset_union isOpen_interior
      isClosed_closure.isOpen_compl (Set.disjoint_left.mpr fun a ha hac =>
        hac (subset_closure (interior_subset ha))) hsub ⟨c, hcq, hc⟩
    exact interior_subset (this hv)
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hA.convex.interior isOpen_interior za
  obtain ⟨w, hw⟩ := gx φ
  have zc : ∀ a ∈ A, w ⬝ᵥ a ≤ w ⬝ᵥ z := by
    intro a ha
    have hcl : IsClosed {v : Fin n → ℝ | w ⬝ᵥ v ≤ w ⬝ᵥ z} :=
      isClosed_le (continuous_dotProduct_left' w) continuous_const
    refine (hcl.closure_subset_iff.mpr fun b hb => ?_) (gy hA ha)
    show w ⬝ᵥ b ≤ w ⬝ᵥ z
    rw [← hw, ← hw]; exact (hφ b hb).le
  have hw0 : w ≠ 0 := by
    intro h0
    have := hφ c hc
    rw [hw, hw, h0, zero_dotProduct, zero_dotProduct] at this
    exact lt_irrefl _ this
  obtain ⟨l, hl, hwl⟩ := gH hB hzc hw0 zc
  obtain ⟨g, hg⟩ : ∃ g, g = z - c := ⟨_, rfl⟩
  rw [← hg] at hwl hzz
  have hsq : 0 < Real.sqrt (g ⬝ᵥ g) := Real.sqrt_pos.mpr hzz
  refine ⟨z, (Real.sqrt (g ⬝ᵥ g))⁻¹ • g, ⟨hzA, ?_, ?_, ?_⟩, ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      ← mul_inv, Real.mul_self_sqrt (dot_self_nonneg g), inv_mul_cancel₀ hzz.ne']
  · intro a ha
    have h := zc a ha
    rw [hwl, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h
    have h' : g ⬝ᵥ a ≤ g ⬝ᵥ z := le_of_mul_le_mul_left h hl
    rw [smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left h' (inv_nonneg.mpr hsq.le)
  · intro w' hw'0 hw'
    obtain ⟨l', hl', hw'l⟩ := gH hB hzc hw'0 hw'
    rw [← hg] at hw'l
    refine ⟨l' * Real.sqrt (g ⬝ᵥ g), mul_pos hl' hsq, ?_⟩
    rw [hw'l, smul_smul, mul_assoc, mul_inv_cancel₀ hsq.ne', mul_one]
  ·
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : (z - c) ⬝ᵥ (z - c) ≤ (y - c) ⬝ᵥ (y - c) := hzmin' y hy
    have h2 : (y - c) ⬝ᵥ (y - c) ≤ n * ‖y - c‖ ^ 2 := gG (y - c)
    have h3 : ‖z - c‖ ^ 2 ≤ (z - c) ⬝ᵥ (z - c) := gF (z - c)
    have h4 : ‖y - c‖ < κ := by rw [← dist_eq_norm]; exact hcy
    have hyy : ‖y - c‖ ^ 2 ≤ κ ^ 2 := by
      have := mul_le_mul h4.le h4.le (norm_nonneg _) hκ0.le
      nlinarith
    have hnk : (n : ℝ) * ‖y - c‖ ^ 2 ≤ n * κ ^ 2 := mul_le_mul_of_nonneg_left hyy hn
    have hlt : (n : ℝ) * κ ^ 2 < ((n + 1) * κ) ^ 2 := by
      have e : ((n + 1) * κ) ^ 2 - n * κ ^ 2 = ((n : ℝ) ^ 2 + n + 1) * κ ^ 2 := by ring
      have : 0 < ((n : ℝ) ^ 2 + n + 1) * κ ^ 2 := by positivity
      linarith
    have h5 : ‖z - c‖ < (n + 1) * κ := by
      have : ‖z - c‖ ^ 2 < ((n + 1) * κ) ^ 2 := by rw [← hg] at h1 h3 ⊢; linarith
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
    calc dist z y ≤ dist z c + dist c y := dist_triangle _ _ _
      _ = ‖z - c‖ + ‖y - c‖ := by rw [dist_eq_norm, dist_comm, dist_eq_norm]
      _ < (n + 1) * κ + κ := by linarith
      _ = ε := by rw [hκ]; field_simp; ring
lemma finite_normals {A : Set (Fin n → ℝ)} (hA : IsCB A) {μ : Measure (Fin n → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ A} = Aᶜ.indicator 1 x) : {ξ | ∃ x, RegularAt A x ξ}.Finite := by
  by_contra hinf
  have hinf' : {ξ | ∃ x, RegularAt A x ξ}.Infinite := hinf
  have := hinf'.to_subtype
  let e := Infinite.natEmbedding {ξ | ∃ x, RegularAt A x ξ}
  have hx : ∀ k, ∃ x, RegularAt A x (e k : Fin n → ℝ) := fun k => (e k).2
  choose x hx using hx
  obtain ⟨R, hR⟩ := hA.compact.isBounded.subset_closedBall 0
  let E : ℕ → Set (Fin n → ℝ) := fun k => {s | x k - s ∈ suppSet A (-(e k : Fin n → ℝ))}
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (gC hA _ _).isClosed.measurableSet
  have hdisj : Pairwise fun i j => Disjoint (E i) (E j) := fun i j hij =>
    gE (hx i) (hx j) fun h => hij (e.injective (Subtype.ext h))
  have hsub : ⋃ k, E k ⊆ closedBall 0 (2 * R) := by
    intro s hs
    obtain ⟨k, hk⟩ := mem_iUnion.mp hs
    have h1 : ‖x k‖ ≤ R := by simpa using hR (hx k).mem
    have h2 : ‖x k - s‖ ≤ R := by simpa using hR hk.1
    rw [mem_closedBall, dist_zero_right]
    calc ‖s‖ = ‖x k - (x k - s)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x k‖ + ‖x k - s‖ := norm_sub_le _ _
      _ ≤ 2 * R := by linarith
  have htop : μ (⋃ k, E k) = ⊤ := by
    rw [measure_iUnion hdisj hEm]
    refine top_unique ?_
    calc (⊤ : ENNReal) = ∑' _k : ℕ, (1 : ENNReal) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ ∑' k, μ (E k) := ENNReal.tsum_le_tsum fun k => gD hA hμ (hx k)
  have hfin : μ (closedBall (0 : Fin n → ℝ) (2 * R)) < ⊤ := (isCompact_closedBall _ _).measure_lt_top
  have hle := measure_mono (μ := μ) hsub
  rw [htop] at hle
  exact lt_irrefl _ (hle.trans_lt hfin)
end FCBridge
end
section
open MeasureTheory Filter Topology Metric Set Real Matrix
open scoped Pointwise ENNReal
open GraphicVoronoiPrototype FCBridge ProductInterval Hexagon
namespace FCBridge
def Hpoly2 {r : ℕ} (N : Fin r → Fin 2 → ℝ) (h : Fin r → ℝ) : Set (Fin 2 → ℝ) :=
  {x | ∀ j, N j ⬝ᵥ x ≤ h j}
theorem g7 {k : ℕ} (y' : Fin k → ℝ) (s : ℝ) (x : Fin (k + 1) → ℝ) : pt y' s ⬝ᵥ x = y' ⬝ᵥ nH x + s * nV x := by
  rw [dotProduct_comm, ← pt_nH_nV' x, dotProduct_pt, nH_pt, nV_pt, dotProduct_comm (nH x) y', mul_comm]
theorem g6 {r : ℕ} (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : IsUnit S.det) (N : Fin r → Fin 2 → ℝ) (h : Fin r → ℝ) : affEquiv S hS 0 ⁻¹' Hpoly2 N h = Hpoly2 (fun j => Sᵀ *ᵥ N j) h := by
  ext y
  simp only [Set.mem_preimage, affEquiv_apply, add_zero, Hpoly2, Set.mem_ofPred_eq]
  refine forall_congr' fun j => ?_
  rw [dotProduct_mulVec, mulVec_transpose]
def RightSpectral2 (A : Set (Fin 2 → ℝ)) : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℝ)), MeasurableSet B → Bornology.IsBounded B →
    isSpectral (productSet A B) → isSpectral B
theorem gI {m : ℕ} {A : Set (Fin 2 → ℝ)} {B : Set (Fin m → ℝ)} (c : Fin 2 → ℝ) (hspec : isSpectral (productSet A B)) : isSpectral (productSet {y | y + c ∈ A} B) := by
  set b : Fin (2 + m) → ℝ := fun i => Fin.addCases (fun i₁ => c i₁) (fun _ => (0 : ℝ)) i with hb
  have h1 : IsUnit (1 : Matrix (Fin (2 + m)) (Fin (2 + m)) ℝ).det := by simp
  have hpre : affEquiv 1 h1 b ⁻¹' productSet A B = productSet {y | y + c ∈ A} B := by
    ext x
    simp only [Set.mem_preimage, affEquiv_apply, one_mulVec, productSet, Set.mem_ofPred_eq]
    have e1 : (fun i => (x + b) (Fin.castAdd m i)) = (fun i => x (Fin.castAdd m i)) + c := by
      funext i; simp [hb]
    have e2 : (fun j => (x + b) (Fin.natAdd 2 j)) = fun j => x (Fin.natAdd 2 j) := by
      funext j; simp [hb]
    rw [e1, e2]
  have := isSpectral_affEquiv_preimage hspec 1 h1 b
  rwa [hpre] at this
theorem gJ {m : ℕ} {A : Set (Fin 2 → ℝ)} {B : Set (Fin m → ℝ)} (T : Matrix (Fin 2) (Fin 2) ℝ) (hT : IsUnit T.det) (hspec : isSpectral (productSet A B)) : isSpectral (productSet {y | T *ᵥ y ∈ A} B) := by
  set M : Matrix (Fin (2 + m)) (Fin (2 + m)) ℝ :=
    (Matrix.fromBlocks T 0 0 (1 : Matrix (Fin m) (Fin m) ℝ)).submatrix finSumFinEquiv.symm
      finSumFinEquiv.symm with hM
  have hMd : IsUnit M.det := by
    rw [hM, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one]; exact hT
  have hMv : ∀ x : Fin (2 + m) → ℝ, (∀ i, (M *ᵥ x) (Fin.castAdd m i) =
      (T *ᵥ fun k => x (Fin.castAdd m k)) i) ∧ ∀ j, (M *ᵥ x) (Fin.natAdd 2 j) = x (Fin.natAdd 2 j) := by
    intro x
    rw [hM, submatrix_mulVec_equiv, fromBlocks_mulVec]
    constructor
    · intro i
      simp only [Function.comp_apply, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl, Matrix.zero_mulVec, add_zero, Equiv.symm_symm]
      rfl
    · intro j
      simp only [Function.comp_apply, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr, Matrix.zero_mulVec, zero_add, Matrix.one_mulVec, Equiv.symm_symm]
      simp
  have hpre : affEquiv M hMd 0 ⁻¹' productSet A B = productSet {y | T *ᵥ y ∈ A} B := by
    ext x
    simp only [Set.mem_preimage, affEquiv_apply, add_zero, productSet, Set.mem_ofPred_eq]
    have h1 : (fun i => (M *ᵥ x) (Fin.castAdd m i)) = T *ᵥ fun k => x (Fin.castAdd m k) :=
      funext (hMv x).1
    have h2 : (fun j => (M *ᵥ x) (Fin.natAdd 2 j)) = fun j => x (Fin.natAdd 2 j) :=
      funext (hMv x).2
    rw [h1, h2]
  have := isSpectral_affEquiv_preimage hspec M hMd 0
  rwa [hpre] at this
theorem RightSpectral2.of_linear {A : Set (Fin 2 → ℝ)} (T : Matrix (Fin 2) (Fin 2) ℝ)
    (hT : IsUnit T.det) (h : RightSpectral2 {y | T *ᵥ y ∈ A}) : RightSpectral2 A :=
  fun _ _ hBm hBb hspec => h _ _ hBm hBb (gJ T hT hspec)
theorem g8 {d d' : ℕ} (h : d = d') {S : Set (Fin d' → ℝ)} : isSpectral ((fun x : Fin d → ℝ => fun i : Fin d' => x (Fin.cast h.symm i)) ⁻¹' S) ↔ isSpectral S := by
  subst h
  rfl
def box2 (a b : Fin 2 → ℝ) : Set (Fin 2 → ℝ) := {x | ∀ i, x i ∈ Set.Icc (a i) (b i)}
theorem gK {a b : Fin 2 → ℝ} (hab : ∀ i, a i < b i) : RightSpectral2 (box2 a b) := by
  intro m B hBm hBb hspec
  have h : 1 + (1 + m) = 2 + m := by omega
  have hset : (fun x : Fin (1 + (1 + m)) → ℝ =>
      fun i : Fin (2 + m) => x (Fin.cast h.symm i)) ⁻¹' productSet (box2 a b) B =
      productSet (ivl (a 0) (b 0)) (productSet (ivl (a 1) (b 1)) B) := by
    ext x
    have e2 : (fun k : Fin m => x (Fin.cast h.symm (Fin.natAdd 2 k))) =
        fun k => x (Fin.natAdd 1 (Fin.natAdd 1 k)) := by
      funext k; congr 1; ext; simp; omega
    have hbox : ∀ y : Fin 2 → ℝ, y ∈ box2 a b ↔
        y 0 ∈ Set.Icc (a 0) (b 0) ∧ y 1 ∈ Set.Icc (a 1) (b 1) := by
      intro y
      exact ⟨fun hy => ⟨hy 0, hy 1⟩, fun ⟨h0, h1⟩ i => by fin_cases i <;> assumption⟩
    show (fun j : Fin 2 => x (Fin.cast h.symm (Fin.castAdd m j))) ∈ box2 a b ∧
        (fun k : Fin m => x (Fin.cast h.symm (Fin.natAdd 2 k))) ∈ B ↔
      x (Fin.castAdd (1 + m) (0 : Fin 1)) ∈ Set.Icc (a 0) (b 0) ∧
        (x (Fin.natAdd 1 (Fin.castAdd m (0 : Fin 1))) ∈ Set.Icc (a 1) (b 1) ∧
          (fun k : Fin m => x (Fin.natAdd 1 (Fin.natAdd 1 k))) ∈ B)
    rw [hbox, e2]
    have i0 : x (Fin.cast h.symm (Fin.castAdd m (0 : Fin 2))) =
        x (Fin.castAdd (1 + m) (0 : Fin 1)) := rfl
    have i1 : x (Fin.cast h.symm (Fin.castAdd m (1 : Fin 2))) =
        x (Fin.natAdd 1 (Fin.castAdd m (0 : Fin 1))) := rfl
    simp only [i0, i1, and_assoc]
  have h2 : isSpectral (productSet (ivl (a 0) (b 0)) (productSet (ivl (a 1) (b 1)) B)) := by
    rw [← hset]; exact (g8 h).2 hspec
  have hB1m := measurableSet_productSet (measurableSet_ivl (a 1) (b 1)) hBm
  have hB1b := isBounded_productSet (isBounded_ivl (a 1) (b 1)) hBb
  exact isSpectral_right_of_ivl (hab 1) hBm hBb (isSpectral_right_of_ivl (hab 0) hB1m hB1b h2)
def det2 (u v : Fin 2 → ℝ) : ℝ := u 0 * v 1 - u 1 * v 0
def perp2 (u : Fin 2 → ℝ) : Fin 2 → ℝ := ![-u 1, u 0]
def rows2 (r₀ r₁ : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => ![r₀, r₁] i j
theorem is (u v : Fin 2 → ℝ) : det2 v u = -det2 u v := by unfold det2; ring
theorem it (u : Fin 2 → ℝ) : det2 u u = 0 := by unfold det2; ring
theorem g9 (u v : Fin 2 → ℝ) : det2 u (-v) = -det2 u v := by
  simp [det2]; ring
theorem hO (u v : Fin 2 → ℝ) : det2 (-u) v = -det2 u v := by
  simp [det2]; ring
theorem h6 (u : Fin 2 → ℝ) : u ⬝ᵥ perp2 u = 0 := by
  simp [perp2, dotProduct, Fin.sum_univ_two]; ring
theorem iu (u v : Fin 2 → ℝ) : u ⬝ᵥ perp2 v = -det2 u v := by
  simp [perp2, det2, dotProduct, Fin.sum_univ_two]; ring
theorem h7 {u : Fin 2 → ℝ} (hu : u ≠ 0) : perp2 u ≠ 0 := by
  intro h
  apply hu
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [perp2] at h0 h1
  funext i; fin_cases i <;> simp [h0, h1]
theorem h8 (r₀ r₁ x : Fin 2 → ℝ) : rows2 r₀ r₁ *ᵥ x = ![r₀ ⬝ᵥ x, r₁ ⬝ᵥ x] := by
  funext i; fin_cases i <;> simp [rows2, mulVec, dotProduct, Fin.sum_univ_two]
theorem h9 (r₀ r₁ c : Fin 2 → ℝ) : (rows2 r₀ r₁)ᵀ *ᵥ c = c 0 • r₀ + c 1 • r₁ := by
  funext i; fin_cases i <;> simp [rows2, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
theorem ia (r₀ r₁ : Fin 2 → ℝ) : (rows2 r₀ r₁).det = det2 r₀ r₁ := by
  rw [Matrix.det_fin_two]; simp [rows2, det2]
theorem ib (M : Matrix (Fin 2) (Fin 2) ℝ) (u v : Fin 2 → ℝ) : det2 (M *ᵥ u) (M *ᵥ v) = M.det * det2 u v := by
  rw [Matrix.det_fin_two]
  simp [det2, mulVec, dotProduct, Fin.sum_univ_two]
  ring
theorem iv (u v w : Fin 2 → ℝ) : det2 u v • w = det2 w v • u + det2 u w • v := by
  funext i; fin_cases i <;> simp [det2] <;> ring
theorem gL (n v : Fin 2 → ℝ) (h : n ⬝ᵥ v = 0) : (n 0 ^ 2 + n 1 ^ 2) • v = det2 n v • perp2 n := by
  simp only [dotProduct, Fin.sum_univ_two] at h
  funext i
  fin_cases i
  · simp [det2, perp2]; linear_combination n 0 * h
  · simp [det2, perp2]; linear_combination n 1 * h
theorem gM {n : Fin 2 → ℝ} (hn : n ≠ 0) : 0 < n 0 ^ 2 + n 1 ^ 2 := by
  by_contra hle
  have h0 : n 0 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
  have h1 : n 1 = 0 := by nlinarith [sq_nonneg (n 0), sq_nonneg (n 1)]
  exact hn (funext fun i => by fin_cases i <;> simp [h0, h1])
section Transport2
variable {S : Matrix (Fin 2) (Fin 2) ℝ} (hS : IsUnit S.det)
theorem gN (x : Fin 2 → ℝ) : affEquiv S hS 0 x = S *ᵥ x := by
  rw [affEquiv_apply, add_zero]
theorem gO (x y : Fin 2 → ℝ) : affEquiv S hS 0 (x - y) = affEquiv S hS 0 x - affEquiv S hS 0 y := by
  simp only [gN, mulVec_sub]
theorem gP (S : Matrix (Fin 2) (Fin 2) ℝ) :
    Continuous fun x : Fin 2 → ℝ => S *ᵥ x :=
  (Matrix.mulVecLin S).continuous_of_finiteDimensional
theorem gQ : Measure.QuasiMeasurePreserving (affEquiv S hS 0) volume volume := by
  have hmp := measurePreserving_affEquiv S hS 0
  exact ⟨hmp.measurable, by rw [hmp.map_eq]; exact Measure.smul_absolutelyContinuous⟩
theorem gR {A : Set (Fin 2 → ℝ)} {μ : Measure (Fin 2 → ℝ)} (hμ : ∀ᵐ x, μ {s | x - s ∈ A} = Aᶜ.indicator 1 x) : ∀ᵐ x, (μ.map (affEquiv S hS 0).symm) {s | x - s ∈ affEquiv S hS 0 ⁻¹' A} = (affEquiv S hS 0 ⁻¹' A)ᶜ.indicator 1 x := by
  set e := affEquiv S hS 0 with he
  filter_upwards [(gQ hS).ae hμ] with x hx
  rw [MeasurableEquiv.map_apply]
  have hset : e.symm ⁻¹' {s | x - s ∈ e ⁻¹' A} = {t | e x - t ∈ A} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have hsub : e (x - e.symm t) = e x - t := by
      rw [he, gO hS, ← he, MeasurableEquiv.apply_symm_apply]
    rw [hsub]
  rw [hset, hx]
  by_cases hxA : e x ∈ A
  · rw [Set.indicator_of_notMem (by simpa using hxA), Set.indicator_of_notMem (by simpa using hxA)]
  · rw [Set.indicator_of_mem (show e x ∈ Aᶜ from hxA),
      Set.indicator_of_mem (show x ∈ (e ⁻¹' A)ᶜ from hxA)]
    rfl
theorem gS {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (μ.map (affEquiv S hS 0).symm) := by
  constructor
  intro K hK
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_symm]
  have hcont : Continuous (affEquiv S hS 0) := by
    have : (affEquiv S hS 0 : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = fun x => S *ᵥ x :=
      funext (gN hS)
    rw [this]; exact gP S
  exact (hK.image hcont).measure_lt_top
theorem gT {A : Set (Fin 2 → ℝ)} {μ : Measure (Fin 2 → ℝ)} (hμ0 : μ (interior A - interior A) = 0) : (μ.map (affEquiv S hS 0).symm) (interior (affEquiv S hS 0 ⁻¹' A) - interior (affEquiv S hS 0 ⁻¹' A)) = 0 := by
  set L := (matLinEquiv S hS).toContinuousLinearEquiv with hL
  have hLe : ∀ x, L x = affEquiv S hS 0 x := fun x => by
    rw [gN, hL, LinearEquiv.coe_toContinuousLinearEquiv', matLinEquiv_apply]
  have hpre : affEquiv S hS 0 ⁻¹' A = L ⁻¹' A := by
    ext x; simp only [Set.mem_preimage, hLe]
  have hint : interior (affEquiv S hS 0 ⁻¹' A) = L ⁻¹' interior A := by
    rw [hpre]; exact (L.toHomeomorph.preimage_interior A).symm
  have hsub : interior (affEquiv S hS 0 ⁻¹' A) - interior (affEquiv S hS 0 ⁻¹' A) ⊆
      L ⁻¹' (interior A - interior A) := by
    rw [hint]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨L a, ha, L b, hb, by simp⟩
  refine measure_mono_null hsub ?_
  rw [MeasurableEquiv.map_apply]
  have : (affEquiv S hS 0).symm ⁻¹' (L ⁻¹' (interior A - interior A)) =
      interior A - interior A := by
    ext x
    simp only [Set.mem_preimage, hLe, MeasurableEquiv.apply_symm_apply]
  rw [this]; exact hμ0
end Transport2
section Cover2
variable {r : ℕ} {N : Fin r → Fin (1 + 1) → ℝ} {h : Fin r → ℝ} {A : Set (Fin (1 + 1) → ℝ)}
theorem gU (hAH : A = Hpoly2 N h) (hsymm : ∀ x ∈ A, -x ∈ A) {w : Fin (1 + 1) → ℝ} (hw : ∀ j, N j ⬝ᵥ w < 2 * h j) : w ∈ interior A - interior A := by
  set U : Set (Fin (1 + 1) → ℝ) := {x | ∀ j, N j ⬝ᵥ x < h j} with hU
  have hUo : IsOpen U := by
    rw [hU, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (continuous_dotProduct_left' _)
      continuous_const
  have hUA : U ⊆ A := fun x hx => by rw [hAH]; intro j; exact (hx j).le
  have hnegU : IsOpen (-U) := hUo.neg
  have hnegUA : -U ⊆ A := fun x hx => by
    have := hsymm _ (hUA hx)
    rwa [neg_neg] at this
  have h1 : (1 / 2 : ℝ) • w ∈ interior A := interior_maximal hUA hUo fun j => by
    rw [dotProduct_smul, smul_eq_mul]; linarith [hw j]
  have h2 : -((1 / 2 : ℝ) • w) ∈ interior A := interior_maximal hnegUA hnegU (by
    show -(-((1 / 2 : ℝ) • w)) ∈ U
    rw [neg_neg]; intro j; rw [dotProduct_smul, smul_eq_mul]; linarith [hw j])
  refine ⟨_, h1, _, h2, ?_⟩
  show (1 / 2 : ℝ) • w - -((1 / 2 : ℝ) • w) = w
  rw [sub_neg_eq_add, ← add_smul]; norm_num
theorem gV {a : ℝ} (hAH : A = Hpoly2 N h) {y : Fin 1 → ℝ} (hy : y ∈ interior (sect A a)) {j : Fin r} (hj : N j ⬝ᵥ pt y a = h j) : nH (N j) = 0 := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ρ / (2 * (‖nH (N j)‖ + 1)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hin : y + δ • nH (N j) ∈ sect A a := by
    refine interior_subset (hball ?_)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ0.le, hδ]
    have h1 : ρ / (2 * (‖nH (N j)‖ + 1)) * ‖nH (N j)‖ ≤ ρ / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [norm_nonneg (nH (N j))]
    linarith
  have hle : N j ⬝ᵥ pt (y + δ • nH (N j)) a ≤ h j := by
    have : pt (y + δ • nH (N j)) a ∈ A := hin
    rw [hAH] at this
    exact this j
  rw [dotProduct_comm, g7] at hle hj
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul] at hle
  have hsq : nH (N j) ⬝ᵥ nH (N j) ≤ 0 := by
    have : δ * (nH (N j) ⬝ᵥ nH (N j)) ≤ 0 := by linarith
    nlinarith
  exact dotProduct_self_eq_zero.1 (le_antisymm hsq (dot_self_nonneg _))
theorem gW (hAH : A = Hpoly2 N h) (hN : ∀ j, N j ≠ 0) (hsymm : ∀ x ∈ A, -x ∈ A) (hAc : IsCompact A) {a : ℝ} (ha : 0 < a) (htop : ∀ x ∈ A, nV x ≤ a) {μ : Measure (Fin (1 + 1) → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ A} = Aᶜ.indicator 1 x) (hμ0 : μ (interior A - interior A) = 0) : ∀ᵐ y : Fin 1 → ℝ, y ∈ interior (sect A a) → 1 ≤ μ {t | nV t = 2 * a ∧ nH t - y ∈ sect A a} := by
  have hae : ∀ᵐ y : Fin 1 → ℝ, ∀ᵐ s : ℝ,
      μ {t | pt y s - t ∈ A} = Aᶜ.indicator 1 (pt y s) := by
    have := (measurePreserving_pt (k := 1)).quasiMeasurePreserving.ae hμ
    exact Measure.ae_ae_of_ae_prod this
  filter_upwards [hae] with y hy hyF
  have hyA : pt y a ∈ A := (interior_subset hyF : y ∈ sect A a)
  have hA0 : (0 : Fin (1 + 1) → ℝ) ∈ A := by
    have := hAH ▸ hsymm _ hyA
    rw [hAH] at hyA ⊢
    intro j
    have h1 := hyA j
    have h2 := this j
    rw [dotProduct_neg] at h2
    rw [dotProduct_zero]
    linarith
  have hactive : ∀ j, N j ⬝ᵥ pt y a = h j → nH (N j) = 0 ∧ 0 < nV (N j) := by
    intro j hj
    have hH := gV hAH hyF hj
    refine ⟨hH, ?_⟩
    have hj' := hj
    rw [dotProduct_comm, g7, hH, dotProduct_zero, zero_add] at hj'
    have h0 : N j ⬝ᵥ (0 : Fin (1 + 1) → ℝ) ≤ h j := by rw [hAH] at hA0; exact hA0 j
    rw [dotProduct_zero] at h0
    have hne : nV (N j) ≠ 0 := by
      intro h'
      apply hN j
      rw [← pt_nH_nV' (N j), hH, h']
      have hsub := pt_sub (0 : Fin 1 → ℝ) 0 0 0
      simpa using hsub.symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exfalso; nlinarith
    · exact hgt
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j, N j ⬝ᵥ pt y a < h j →
      ε * |nV (N j)| < h j - N j ⬝ᵥ pt y a := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : N j ⬝ᵥ pt y a < h j
    · have ht : Tendsto (fun ε : ℝ => ε * |nV (N j)|) (𝓝[>] 0) (𝓝 0) := by
        have h0 : Tendsto (fun ε : ℝ => ε * |nV (N j)|) (𝓝 0) (𝓝 (0 * |nV (N j)|)) :=
          (continuous_id.mul continuous_const).tendsto 0
        rw [zero_mul] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      filter_upwards [ht.eventually (gt_mem_nhds (sub_pos.2 hj))] with ε hε _
      exact hε
    · exact Eventually.of_forall fun _ h' => absurd h' hj
  obtain ⟨ε₀, hε₀, hε₀pos⟩ := (hev.and self_mem_nhdsWithin).exists
  set K : ℝ → Set (Fin (1 + 1) → ℝ) := fun ρ =>
    {t | 2 * a ≤ nV t ∧ nV t ≤ 2 * a + ρ ∧ ∃ z ∈ A, a - ρ ≤ nV z ∧ nH z = nH t - y} with hK
  have hKmass : ∀ ρ > 0, 1 ≤ μ (K ρ) := by
    intro ρ hρ
    set ρ' := min ρ ε₀ with hρ'
    have hρ'pos : 0 < ρ' := lt_min hρ hε₀pos
    obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ : ∃ s ∈ Ioo a (a + ρ'),
        μ {t | pt y s - t ∈ A} = Aᶜ.indicator 1 (pt y s) := by
      by_contra hcon
      push Not at hcon
      have hsub : Ioo a (a + ρ') ⊆ {s | ¬ μ {t | pt y s - t ∈ A} = Aᶜ.indicator 1 (pt y s)} :=
        fun s hs => hcon s hs
      have := measure_mono_null hsub (ae_iff.1 hy)
      rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at this
      linarith
    have hsA : pt y s ∉ A := fun hmem => by
      have := htop _ hmem; rw [nV_pt] at this; linarith
    rw [Set.indicator_of_mem (show pt y s ∈ Aᶜ from hsA), Pi.one_apply] at hs
    have hcover : {t | pt y s - t ∈ A} ⊆ (interior A - interior A) ∪ K ρ := by
      intro t ht
      by_cases hall : ∀ j, N j ⬝ᵥ t < 2 * h j
      · exact Or.inl (gU hAH hsymm hall)
      right
      push Not at hall
      obtain ⟨j, hj⟩ := hall
      have hz : -(pt y s - t) ∈ A := hsymm _ ht
      have hzj : N j ⬝ᵥ (-(pt y s - t)) ≤ h j := by rw [hAH] at hz; exact hz j
      have hexp : N j ⬝ᵥ pt y s = N j ⬝ᵥ pt y a + (s - a) * nV (N j) := by
        rw [dotProduct_comm (N j) (pt y s), g7, dotProduct_comm (N j) (pt y a), g7]; ring
      have hkey : h j - N j ⬝ᵥ pt y a ≤ (s - a) * nV (N j) := by
        rw [dotProduct_neg, dotProduct_sub] at hzj
        linarith
      have hj_active : N j ⬝ᵥ pt y a = h j := by
        by_contra hne
        have hlt : N j ⬝ᵥ pt y a < h j := lt_of_le_of_ne (by rw [hAH] at hyA; exact hyA j) hne
        have h1 := hε₀ j hlt
        have h2 : (s - a) * nV (N j) ≤ ε₀ * |nV (N j)| := by
          calc (s - a) * nV (N j) ≤ (s - a) * |nV (N j)| :=
                mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
            _ ≤ ε₀ * |nV (N j)| :=
                mul_le_mul_of_nonneg_right (by linarith [min_le_right ρ ε₀]) (abs_nonneg _)
        linarith
      obtain ⟨hH, hV⟩ := hactive j hj_active
      have hNj : N j = pt 0 (nV (N j)) := by rw [← hH, pt_nH_nV']
      have ht2a : 2 * a ≤ nV t := by
        have e1 : N j ⬝ᵥ t = nV (N j) * nV t := by
          rw [hNj, dotProduct_comm, ← pt_nH_nV' t, g7, nH_pt, nV_pt, dotProduct_zero, zero_add, pt_nH_nV']
          ring
        have e2 : h j = nV (N j) * a := by
          rw [← hj_active, hNj, dotProduct_comm, g7, nH_pt, nV_pt, dotProduct_zero, zero_add]
          ring
        rw [e1, e2] at hj
        nlinarith
      refine ⟨ht2a, ?_, -(pt y s - t), hz, ?_, ?_⟩
      · have := htop _ hz
        rw [nV_neg] at this
        have e : nV (pt y s - t) = s - nV t := by
          rw [← pt_nH_nV' t, pt_sub, nV_pt, nV_pt]
        rw [e] at this
        linarith [min_le_left ρ ε₀]
      · rw [nV_neg]
        have e : nV (pt y s - t) = s - nV t := by
          rw [← pt_nH_nV' t, pt_sub, nV_pt, nV_pt]
        rw [e]
        linarith [min_le_left ρ ε₀]
      · have e : nH (pt y s - t) = y - nH t := by
          rw [← pt_nH_nV' t, pt_sub, nH_pt, nH_pt]
        have e' : nH (-(pt y s - t)) = -nH (pt y s - t) := by
          funext i; rfl
        rw [e', e, neg_sub]
    calc (1 : ENNReal) = μ {t | pt y s - t ∈ A} := hs.symm
      _ ≤ μ ((interior A - interior A) ∪ K ρ) := measure_mono hcover
      _ ≤ μ (interior A - interior A) + μ (K ρ) := measure_union_le _ _
      _ = μ (K ρ) := by rw [hμ0, zero_add]
  have hKanti : Antitone fun n : ℕ => K (1 / (n + 1)) := by
    intro m n hmn t ht
    obtain ⟨h1, h2, z, hz, h3, h4⟩ := ht
    have hle : (1 : ℝ) / (n + 1) ≤ 1 / (m + 1) := by gcongr
    exact ⟨h1, h2.trans (by linarith), z, hz, by linarith, h4⟩
  have hKclosed : ∀ ρ, IsClosed (K ρ) := by
    intro ρ
    have hC : IsClosed ((fun z : Fin (1 + 1) → ℝ => nH z) '' (A ∩ {z | a - ρ ≤ nV z})) :=
      ((hAc.inter_right (isClosed_le continuous_const continuous_nV)).image
        continuous_nH).isClosed
    have : K ρ = {t | 2 * a ≤ nV t} ∩ {t | nV t ≤ 2 * a + ρ} ∩
        (fun t => nH t - y) ⁻¹' ((fun z => nH z) '' (A ∩ {z | a - ρ ≤ nV z})) := by
      ext t
      simp only [hK, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
      exact ⟨fun ⟨h1, h2, z, hz, h3, h4⟩ => ⟨⟨h1, h2⟩, z, ⟨hz, h3⟩, h4⟩,
        fun ⟨⟨h1, h2⟩, z, ⟨hz, h3⟩, h4⟩ => ⟨h1, h2, z, hz, h3, h4⟩⟩
    rw [this]
    exact ((isClosed_le continuous_const continuous_nV).inter
      (isClosed_le continuous_nV continuous_const)).inter
      (hC.preimage (continuous_nH.sub continuous_const))
  have hKbdd : ∀ ρ, Bornology.IsBounded (K ρ) := by
    intro ρ
    obtain ⟨R, hR⟩ := hAc.isBounded.subset_closedBall 0
    refine (Metric.isBounded_closedBall (x := (0 : Fin (1 + 1) → ℝ))
      (r := ‖pt y 0‖ + R + |2 * a| + |ρ| + 1)).subset ?_
    intro t ⟨h1, h2, z, hz, h3, h4⟩
    rw [mem_closedBall, dist_zero_right]
    have hzR : ‖z‖ ≤ R := by have := hR hz; rwa [mem_closedBall, dist_zero_right] at this
    have e : t = pt y 0 + pt (nH z) 0 + pt 0 (nV t) := by
      rw [pt_add, pt_add, h4]
      simp only [add_zero, zero_add, add_sub_cancel]
      exact (pt_nH_nV' t).symm
    rw [e]
    calc ‖pt y 0 + pt (nH z) 0 + pt 0 (nV t)‖ ≤ ‖pt y 0‖ + ‖pt (nH z) 0‖ + ‖pt 0 (nV t)‖ :=
          norm_add₃_le
      _ ≤ ‖pt y 0‖ + R + (|2 * a| + |ρ|) := by
          gcongr
          · rw [norm_pt_zero]
            exact (norm_le_norm_pt (nH z) (nV z)).trans (by rw [pt_nH_nV']; exact hzR)
          · rw [norm_pt_zero_left, abs_le]
            constructor <;> cases abs_cases (2 * a) <;> cases abs_cases ρ <;> linarith
      _ ≤ ‖pt y 0‖ + R + |2 * a| + |ρ| + 1 := by linarith
  have hinter : (⋂ n : ℕ, K (1 / (n + 1))) = {t | nV t = 2 * a ∧ nH t - y ∈ sect A a} := by
    ext t
    rw [Set.mem_iInter]
    constructor
    · intro ht
      have ht' : ∀ n : ℕ, 2 * a ≤ nV t ∧ nV t ≤ 2 * a + 1 / (n + 1) ∧
          ∃ z ∈ A, a - 1 / (n + 1) ≤ nV z ∧ nH z = nH t - y := fun n => ht n
      have hV : nV t = 2 * a := by
        refine le_antisymm ?_ (ht' 0).1
        refine le_of_forall_pos_lt_add fun δ hδ => ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        linarith [(ht' n).2.1]
      refine ⟨hV, ?_⟩
      choose z hz hz1 hz2 using fun n : ℕ => (ht' n).2.2
      have hV' : Tendsto (fun n : ℕ => nV (z n)) atTop (𝓝 a) := by
        have hlow : Tendsto (fun n : ℕ => a - 1 / ((n : ℝ) + 1)) atTop (𝓝 a) := by
          have := (tendsto_const_nhds (x := a)).sub tendsto_one_div_add_atTop_nhds_zero_nat
          rwa [sub_zero] at this
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
          (fun n => hz1 n) (fun n => htop _ (hz n))
      have hfun : (fun n => z n) = fun n => pt (nH t - y) (nV (z n)) := by
        funext n; rw [← hz2 n, pt_nH_nV']
      have hlim : Tendsto (fun n : ℕ => z n) atTop (𝓝 (pt (nH t - y) a)) := by
        rw [hfun]
        exact ((continuous_pt (nH t - y)).tendsto a).comp hV'
      exact hAc.isClosed.mem_of_tendsto hlim (Eventually.of_forall hz)
    · rintro ⟨hV, hF⟩ n
      have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
      show 2 * a ≤ nV t ∧ nV t ≤ 2 * a + 1 / (n + 1) ∧
        ∃ z ∈ A, a - 1 / (n + 1) ≤ nV z ∧ nH z = nH t - y
      refine ⟨hV.ge, by rw [hV]; linarith, pt (nH t - y) a, hF, ?_, nH_pt _ _⟩
      rw [nV_pt]
      linarith
  rw [← hinter]
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (s := fun n : ℕ => K (1 / ((n : ℝ) + 1)))
    (fun n : ℕ => (hKclosed (1 / ((n : ℝ) + 1))).measurableSet.nullMeasurableSet) hKanti
    ⟨0, (hKbdd _).measure_lt_top.ne⟩
  exact ge_of_tendsto hlim (Eventually.of_forall fun n : ℕ => hKmass _ (by positivity))
end Cover2
theorem gX {A : Set (Fin 2 → ℝ)} (hA : IsCB A) (hsymm : ∀ x ∈ A, -x ∈ A) : (0 : Fin 2 → ℝ) ∈ interior A := by
  obtain ⟨x, hx⟩ := hA.interior_nonempty
  have hnx : -x ∈ interior A := by
    rw [mem_interior]
    refine ⟨-interior A, fun y hy => ?_, isOpen_interior.neg, by simpa using hx⟩
    have := hsymm _ (interior_subset (Set.mem_neg.1 hy))
    simpa using this
  have := hA.convex.interior hx hnx (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa [smul_neg] using this
theorem RegularAt.neg2 {A : Set (Fin 2 → ℝ)} (hsymm : ∀ x ∈ A, -x ∈ A)
    {x ξ : Fin 2 → ℝ} (hx : RegularAt A x ξ) : RegularAt A (-x) (-ξ) where
  mem := hsymm x hx.mem
  unit := by simpa using hx.unit
  supp y hy := by
    have := hx.supp (-y) (hsymm y hy)
    simp only [dotProduct_neg, neg_dotProduct] at this ⊢
    linarith
  uniq w hw0 hw := by
    obtain ⟨c, hc, hcw⟩ := hx.uniq (-w) (neg_ne_zero.2 hw0) fun y hy => by
      have := hw (-y) (hsymm y hy)
      simp only [dotProduct_neg, neg_dotProduct] at this ⊢
      linarith
    refine ⟨c, hc, ?_⟩
    have h1 := congrArg Neg.neg hcw
    simpa [smul_neg] using h1
theorem RegularAt.pos_of_zero_mem_interior2 {A : Set (Fin 2 → ℝ)} (h0 : (0 : Fin 2 → ℝ) ∈ interior A) {x ξ : Fin 2 → ℝ} (hx : RegularAt A x ξ) : 0 < ξ ⬝ᵥ x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior 0 h0
  set t := r / (2 * (‖ξ‖ + 1))
  have ht0 : 0 < t := by positivity
  have hmem : t • ξ ∈ A := by
    refine interior_subset (hball ?_)
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht0.le]
    have e : t * (‖ξ‖ + 1) = r / 2 := by simp [t]; field_simp
    nlinarith [norm_nonneg ξ]
  have h := hx.supp _ hmem
  rw [dotProduct_smul, hx.unit, smul_eq_mul, mul_one] at h
  linarith
theorem RegularAt.strict_of_ne2 {A : Set (Fin 2 → ℝ)} {x₁ ξ₁ x₂ ξ₂ : Fin 2 → ℝ} (h₁ : RegularAt A x₁ ξ₁) (h₂ : RegularAt A x₂ ξ₂) (hne : ξ₂ ≠ ξ₁) : ξ₂ ⬝ᵥ x₁ < ξ₂ ⬝ᵥ x₂ := by
  refine lt_of_le_of_ne (h₂.supp x₁ h₁.mem) fun heq => hne ?_
  obtain ⟨c, hc, hcξ⟩ := h₁.uniq ξ₂ h₂.ne_zero fun y hy => heq.symm ▸ h₂.supp y hy
  have h1 : c * c = 1 := by
    have := h₂.unit
    rw [hcξ, smul_dotProduct, dotProduct_smul, h₁.unit, smul_eq_mul, smul_eq_mul, mul_one] at this
    exact this
  have hc1 : c = 1 := by nlinarith
  rw [hcξ, hc1, one_smul]
theorem ic {ξ η : Fin 2 → ℝ} (hξ : ξ ⬝ᵥ ξ = 1) (hη : η ⬝ᵥ η = 1) (hd : det2 ξ η = 0) : η = ξ ∨ η = -ξ := by
  simp only [dotProduct, Fin.sum_univ_two, det2] at hξ hη hd
  have hsq : (ξ 0 * η 0 + ξ 1 * η 1) ^ 2 = 1 := by
    calc (ξ 0 * η 0 + ξ 1 * η 1) ^ 2
        = (ξ 0 * ξ 0 + ξ 1 * ξ 1) * (η 0 * η 0 + η 1 * η 1) - (ξ 0 * η 1 - ξ 1 * η 0) ^ 2 := by
          ring
      _ = 1 := by rw [hξ, hη, hd]; ring
  rcases sq_eq_one_iff.1 hsq with hdot | hdot
  · left
    have h0 : (η 0 - ξ 0) ^ 2 + (η 1 - ξ 1) ^ 2 = 0 := by linear_combination hξ + hη - 2 * hdot
    have e0 : η 0 = ξ 0 := by nlinarith [sq_nonneg (η 0 - ξ 0), sq_nonneg (η 1 - ξ 1)]
    have e1 : η 1 = ξ 1 := by nlinarith [sq_nonneg (η 0 - ξ 0), sq_nonneg (η 1 - ξ 1)]
    funext i; fin_cases i <;> assumption
  · right
    have h0 : (η 0 + ξ 0) ^ 2 + (η 1 + ξ 1) ^ 2 = 0 := by linear_combination hξ + hη + 2 * hdot
    have e0 : η 0 = -ξ 0 := by nlinarith [sq_nonneg (η 0 + ξ 0), sq_nonneg (η 1 + ξ 1)]
    have e1 : η 1 = -ξ 1 := by nlinarith [sq_nonneg (η 0 + ξ 0), sq_nonneg (η 1 + ξ 1)]
    funext i; fin_cases i <;> simp [e0, e1]
structure PolyData2 (r : ℕ) where
  N : Fin r → Fin 2 → ℝ
  negIdx : Fin r → Fin r
  wit : Fin r → Fin 2 → ℝ
  A : Set (Fin 2 → ℝ)
  hA_eq : A = Hpoly2 N (fun _ => 1)
  hAc : IsCompact A
  hAconv : Convex ℝ A
  hAsymm : ∀ x ∈ A, -x ∈ A
  h0 : (0 : Fin 2 → ℝ) ∈ interior A
  hN0 : ∀ j, N j ≠ 0
  hNeg : ∀ j, N (negIdx j) = -N j
  hPar : ∀ j k, det2 (N j) (N k) = 0 → k = j ∨ k = negIdx j
  hwit_mem : ∀ j, wit j ∈ A
  hwit_eq : ∀ j, N j ⬝ᵥ wit j = 1
  hwit_lt : ∀ j k, k ≠ j → N k ⬝ᵥ wit j < 1
namespace PolyData2
variable {r : ℕ} (D : PolyData2 r)
theorem mem_iff {x : Fin 2 → ℝ} : x ∈ D.A ↔ ∀ j, D.N j ⬝ᵥ x ≤ 1 := by
  rw [D.hA_eq]; rfl
theorem le_one {x : Fin 2 → ℝ} (hx : x ∈ D.A) (j : Fin r) : D.N j ⬝ᵥ x ≤ 1 :=
  D.mem_iff.1 hx j
theorem neg_one_le {x : Fin 2 → ℝ} (hx : x ∈ D.A) (j : Fin r) : -1 ≤ D.N j ⬝ᵥ x := by
  have := D.le_one (D.hAsymm x hx) j
  rw [dotProduct_neg] at this
  linarith
theorem abs_le_one {x : Fin 2 → ℝ} (hx : x ∈ D.A) (j : Fin r) : |D.N j ⬝ᵥ x| ≤ 1 :=
  abs_le.2 ⟨D.neg_one_le hx j, D.le_one hx j⟩
theorem N_injective : Function.Injective D.N := by
  intro j k hjk
  by_contra hne
  have := D.hwit_lt j k (Ne.symm hne)
  rw [← hjk, D.hwit_eq j] at this
  exact lt_irrefl _ this
theorem negIdx_inv (j : Fin r) : D.negIdx (D.negIdx j) = j := by
  apply D.N_injective
  rw [D.hNeg, D.hNeg, neg_neg]
theorem negIdx_ne (j : Fin r) : D.negIdx j ≠ j := by
  intro h
  have := D.hwit_eq j
  have h2 : D.N (D.negIdx j) ⬝ᵥ D.wit j = -1 := by rw [D.hNeg, neg_dotProduct, this]
  rw [h, this] at h2
  linarith
noncomputable def map (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : IsUnit S.det) : PolyData2 r where
  N j := Sᵀ *ᵥ D.N j
  negIdx := D.negIdx
  wit j := S⁻¹ *ᵥ D.wit j
  A := affEquiv S hS 0 ⁻¹' D.A
  hA_eq := by rw [D.hA_eq]; exact g6 S hS D.N (fun _ => 1)
  hAc := by
    have hsub : affEquiv S hS 0 ⁻¹' D.A = (fun x => S⁻¹ *ᵥ x) '' D.A := by
      ext y
      simp only [Set.mem_preimage, affEquiv_apply, add_zero, Set.mem_image]
      exact ⟨fun hy => ⟨S *ᵥ y, hy, by rw [mulVec_mulVec, nonsing_inv_mul S hS, one_mulVec]⟩,
        fun ⟨x, hx, hxy⟩ => by rw [← hxy, mulVec_mulVec, mul_nonsing_inv S hS, one_mulVec]; exact hx⟩
    rw [hsub]
    exact D.hAc.image (gP S⁻¹)
  hAconv := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_preimage, affEquiv_apply, add_zero] at hx hy ⊢
    rw [mulVec_add, mulVec_smul, mulVec_smul]
    exact D.hAconv hx hy ha hb hab
  hAsymm x hx := by
    simp only [Set.mem_preimage, affEquiv_apply, add_zero] at hx ⊢
    rw [mulVec_neg]
    exact D.hAsymm _ hx
  h0 := by
    set L := (matLinEquiv S hS).toContinuousLinearEquiv
    have hpre : affEquiv S hS 0 ⁻¹' D.A = L.toHomeomorph ⁻¹' D.A := by
      ext x; simp [affEquiv_apply, L, matLinEquiv_apply]
    rw [hpre, ← L.toHomeomorph.preimage_interior]
    change L 0 ∈ interior D.A
    rw [map_zero]
    exact D.h0
  hN0 j hj := D.hN0 j (by
    have hd : IsUnit Sᵀ.det := by rw [det_transpose]; exact hS
    have := congrArg (fun v => (Sᵀ)⁻¹ *ᵥ v) hj
    rw [mulVec_mulVec, nonsing_inv_mul _ hd, one_mulVec, mulVec_zero] at this
    exact this)
  hNeg j := by rw [D.hNeg, mulVec_neg]
  hPar j k hd := by
    rw [ib, det_transpose] at hd
    exact D.hPar j k ((mul_eq_zero.1 hd).resolve_left hS.ne_zero)
  hwit_mem j := by
    simp only [Set.mem_preimage, affEquiv_apply, add_zero, mulVec_mulVec, mul_nonsing_inv S hS, one_mulVec]
    exact D.hwit_mem j
  hwit_eq j := by
    rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv S hS, one_mulVec]
    exact D.hwit_eq j
  hwit_lt j k hkj := by
    rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec, mul_nonsing_inv S hS, one_mulVec]
    exact D.hwit_lt j k hkj
theorem no_three_active {q : Fin 2 → ℝ} {j₁ j₂ j₃ : Fin r} (h1 : D.N j₁ ⬝ᵥ q = 1) (h2 : D.N j₂ ⬝ᵥ q = 1) (h3 : D.N j₃ ⬝ᵥ q = 1) (hne12 : j₁ ≠ j₂) (hne13 : j₁ ≠ j₃) (hne23 : j₂ ≠ j₃) : False := by
  have opp_sign : ∀ a b : Fin r, a ≠ b → D.N a ⬝ᵥ q = 1 → D.N b ⬝ᵥ q = 1 →
      det2 (D.N a) (D.wit a - q) * det2 (D.N b) (D.wit b - q) < 0 := by
    intro a b hab ha hb
    have hbn : b ≠ D.negIdx a := by
      rintro rfl
      rw [D.hNeg, neg_dotProduct, ha] at hb
      linarith
    have hd : det2 (D.N a) (D.N b) ≠ 0 := fun h0 => by
      rcases D.hPar a b h0 with rfl | rfl
      · exact hab rfl
      · exact hbn rfl
    have hva0 : D.N a ⬝ᵥ (D.wit a - q) = 0 := by
      rw [dotProduct_sub, D.hwit_eq a, ha, sub_self]
    have hvb0 : D.N b ⬝ᵥ (D.wit b - q) = 0 := by
      rw [dotProduct_sub, D.hwit_eq b, hb, sub_self]
    have hab_lt : D.N a ⬝ᵥ (D.wit b - q) < 0 := by
      rw [dotProduct_sub, ha]; linarith [D.hwit_lt b a hab]
    have hba_lt : D.N b ⬝ᵥ (D.wit a - q) < 0 := by
      rw [dotProduct_sub, hb]; linarith [D.hwit_lt a b (Ne.symm hab)]
    have La := gM (D.hN0 a)
    have Lb := gM (D.hN0 b)
    have ea : (D.N b 0 ^ 2 + D.N b 1 ^ 2) * (D.N a ⬝ᵥ (D.wit b - q)) =
        -det2 (D.N b) (D.wit b - q) * det2 (D.N a) (D.N b) := by
      have := congrArg (fun w => D.N a ⬝ᵥ w) (gL (D.N b) (D.wit b - q) hvb0)
      simp only [dotProduct_smul, smul_eq_mul, iu] at this
      linarith
    have eb : (D.N a 0 ^ 2 + D.N a 1 ^ 2) * (D.N b ⬝ᵥ (D.wit a - q)) =
        det2 (D.N a) (D.wit a - q) * det2 (D.N a) (D.N b) := by
      have := congrArg (fun w => D.N b ⬝ᵥ w) (gL (D.N a) (D.wit a - q) hva0)
      simp only [dotProduct_smul, smul_eq_mul, iu] at this
      rw [is (D.N a) (D.N b)] at this
      linarith
    have hLa_neg : (D.N a 0 ^ 2 + D.N a 1 ^ 2) * (D.N b ⬝ᵥ (D.wit a - q)) < 0 :=
      mul_neg_of_pos_of_neg La hba_lt
    have hLb_neg : (D.N b 0 ^ 2 + D.N b 1 ^ 2) * (D.N a ⬝ᵥ (D.wit b - q)) < 0 :=
      mul_neg_of_pos_of_neg Lb hab_lt
    have p1 : 0 < det2 (D.N b) (D.wit b - q) * det2 (D.N a) (D.N b) := by linarith
    have p2 : det2 (D.N a) (D.wit a - q) * det2 (D.N a) (D.N b) < 0 := by linarith
    have hprod := mul_neg_of_pos_of_neg p1 p2
    by_contra hge
    push Not at hge
    have hnonneg := mul_nonneg hge (sq_nonneg (det2 (D.N a) (D.N b)))
    have hid : (det2 (D.N b) (D.wit b - q) * det2 (D.N a) (D.N b)) *
        (det2 (D.N a) (D.wit a - q) * det2 (D.N a) (D.N b)) =
        (det2 (D.N a) (D.wit a - q) * det2 (D.N b) (D.wit b - q)) *
        det2 (D.N a) (D.N b) ^ 2 := by ring
    linarith
  have s12 := opp_sign j₁ j₂ hne12 h1 h2
  have s23 := opp_sign j₂ j₃ hne23 h2 h3
  have s13 := opp_sign j₁ j₃ hne13 h1 h3
  have hp := mul_pos_of_neg_of_neg s12 s23
  have hle := mul_nonpos_of_nonpos_of_nonneg s13.le (sq_nonneg (det2 (D.N j₂) (D.wit j₂ - q)))
  have hid : (det2 (D.N j₁) (D.wit j₁ - q) * det2 (D.N j₂) (D.wit j₂ - q)) *
      (det2 (D.N j₂) (D.wit j₂ - q) * det2 (D.N j₃) (D.wit j₃ - q)) =
      (det2 (D.N j₁) (D.wit j₁ - q) * det2 (D.N j₃) (D.wit j₃ - q)) *
      det2 (D.N j₂) (D.wit j₂ - q) ^ 2 := by ring
  linarith
end PolyData2
theorem gY {A : Set (Fin 2 → ℝ)} (hA : IsCB A) (hsymm : ∀ x ∈ A, -x ∈ A) {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ A} = Aᶜ.indicator 1 x) : ∃ (r : ℕ) (D : PolyData2 r), D.A = A := by
  classical
  have h0 := gX hA hsymm
  have hfin := finite_normals hA hμ
  set U := hfin.toFinset
  have hreg : ∀ ξ : U, ∃ x, RegularAt A x ξ.1 := fun ξ => (Set.Finite.mem_toFinset hfin).1 ξ.2
  choose xw hxw using hreg
  have hneg_mem : ∀ ξ : U, -ξ.1 ∈ U := fun ξ =>
    (Set.Finite.mem_toFinset hfin).2 ⟨-xw ξ, (hxw ξ).neg2 hsymm⟩
  set e := U.equivFin.symm
  set r := U.card
  let ξf : Fin r → U := fun j => e j
  let hf : Fin r → ℝ := fun j => (ξf j).1 ⬝ᵥ xw (ξf j)
  have hpos : ∀ j, 0 < hf j := fun j => (hxw (ξf j)).pos_of_zero_mem_interior2 h0
  let Nf : Fin r → Fin 2 → ℝ := fun j => (hf j)⁻¹ • (ξf j).1
  let negf : Fin r → Fin r := fun j => e.symm ⟨-(ξf j).1, hneg_mem (ξf j)⟩
  have hcover : frontier A ⊆ ⋃ ξ ∈ {ξ | ∃ x, RegularAt A x ξ}, suppSet A ξ := by
    have hcl : IsClosed (⋃ ξ ∈ {ξ | ∃ x, RegularAt A x ξ}, suppSet A ξ) :=
      hfin.isClosed_biUnion fun ξ _ => (isCompact_suppSet hA.compact ξ).isClosed
    intro y hy
    refine hcl.closure_subset (Metric.mem_closure_iff.mpr fun ε hε => ?_)
    obtain ⟨z, ξ, hz, hzy⟩ := exists_regular_near hA hy hε
    exact ⟨z, mem_biUnion (x := ξ) ⟨z, hz⟩ ⟨hz.mem, hz.supp⟩, by rw [dist_comm]; exact hzy⟩
  have hA_eq : A = Hpoly2 Nf (fun _ => 1) := by
    ext x
    simp only [Hpoly2, Set.mem_ofPred_eq]
    constructor
    · intro hx j
      have hle := (hxw (ξf j)).supp x hx
      show ((hf j)⁻¹ • (ξf j).1) ⬝ᵥ x ≤ 1
      rw [smul_dotProduct, smul_eq_mul, inv_mul_le_iff₀ (hpos j), mul_one]
      exact hle
    · intro hx
      by_contra hxA
      have hseg : (segment ℝ 0 x ∩ frontier A).Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        have hsub : segment ℝ 0 x ⊆ interior A ∪ (closure A)ᶜ := fun v hv =>
          if hvi : v ∈ interior A then Or.inl hvi
          else Or.inr fun hvc => by
            have : v ∈ segment ℝ 0 x ∩ frontier A := ⟨hv, hvc, hvi⟩
            rw [hempty] at this; exact this
        have := (convex_segment 0 x).isPreconnected.subset_left_of_subset_union isOpen_interior
          isClosed_closure.isOpen_compl (Set.disjoint_left.mpr fun a ha hac =>
            hac (subset_closure (interior_subset ha))) hsub ⟨0, left_mem_segment ℝ 0 x, h0⟩
        exact hxA (interior_subset (this (right_mem_segment ℝ 0 x)))
      obtain ⟨b, hbseg, hbfr⟩ := hseg
      obtain ⟨ξ, hξ, hbξ⟩ := mem_iUnion₂.mp (hcover hbfr)
      have hξU : ξ ∈ U := (Set.Finite.mem_toFinset hfin).2 hξ
      set j := e.symm ⟨ξ, hξU⟩
      have hξj : (ξf j).1 = ξ := by simp [ξf, j]
      have hbj : ξ ⬝ᵥ b = hf j := by
        have h1 : (ξf j).1 ⬝ᵥ b ≤ hf j := (hxw (ξf j)).supp b hbξ.1
        have h2 : hf j ≤ ξ ⬝ᵥ b := by
          have := hbξ.2 (xw (ξf j)) (hxw (ξf j)).mem
          simpa [hf, hξj] using this
        rw [hξj] at h1
        linarith
      have hxj : ξ ⬝ᵥ x ≤ hf j := by
        have := hx j
        simp only [Nf, hξj, smul_dotProduct, smul_eq_mul] at this
        rwa [inv_mul_le_iff₀ (hpos j), mul_one] at this
      have h0j : 0 < hf j := hpos j
      obtain ⟨a₁, a₂, ha₁, ha₂, hsum, rfl⟩ := hbseg
      simp only [smul_zero, zero_add, dotProduct_smul, smul_eq_mul] at hbj hbfr
      rcases eq_or_lt_of_le ha₁ with ha0 | hapos
      · have ha2 : a₂ = 1 := by linarith
        rw [ha2, one_smul] at hbfr
        exact hxA (hA.compact.isClosed.frontier_subset hbfr)
      · have ha2lt : a₂ < 1 := by linarith
        nlinarith [mul_nonneg ha₂ (sub_nonneg.2 hxj)]
  refine ⟨r, ⟨Nf, negf, fun j => xw (ξf j), A, hA_eq, hA.compact, hA.convex, hsymm, h0,
    fun j => smul_ne_zero (inv_ne_zero (hpos j).ne') (hxw (ξf j)).ne_zero,
    fun j => ?_, fun j k hd => ?_, fun j => (hxw (ξf j)).mem, fun j => ?_, fun j k hkj => ?_⟩, rfl⟩
  · have hξneg : (ξf (negf j)).1 = -(ξf j).1 := by simp [ξf, negf]
    have hhneg : hf (negf j) = hf j := by
      have h1 := (hxw (ξf j)).neg2 hsymm
      have h2 := hxw (ξf (negf j))
      rw [hξneg] at h2
      have heq : (-(ξf j).1) ⬝ᵥ xw (ξf (negf j)) = (-(ξf j).1) ⬝ᵥ (-xw (ξf j)) :=
        le_antisymm (h1.supp _ h2.mem) (h2.supp _ h1.mem)
      simp only [hf, hξneg, heq, dotProduct_neg, neg_dotProduct, neg_neg]
    simp only [Nf, hξneg, hhneg, smul_neg]
  · simp only [Nf, det2, Pi.smul_apply, smul_eq_mul] at hd
    have hmul : (hf j)⁻¹ * (hf k)⁻¹ * det2 (ξf j).1 (ξf k).1 = 0 := by
      unfold det2; linear_combination hd
    have hd' : det2 (ξf j).1 (ξf k).1 = 0 :=
      (mul_eq_zero.1 hmul).resolve_left
        (mul_ne_zero (inv_ne_zero (hpos j).ne') (inv_ne_zero (hpos k).ne'))
    rcases ic (hxw (ξf j)).unit (hxw (ξf k)).unit hd' with heq | heq
    · left; exact e.injective (Subtype.ext heq)
    · right
      apply e.injective
      ext1
      simp [ξf, negf, heq]
  · show ((hf j)⁻¹ • (ξf j).1) ⬝ᵥ xw (ξf j) = 1
    rw [smul_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ (hpos j).ne'
  · have hne : (ξf k).1 ≠ (ξf j).1 := fun h => hkj (e.injective (Subtype.ext h))
    have hlt := RegularAt.strict_of_ne2 (hxw (ξf j)) (hxw (ξf k)) hne
    show ((hf k)⁻¹ • (ξf k).1) ⬝ᵥ xw (ξf j) < 1
    rw [smul_dotProduct, smul_eq_mul, inv_mul_lt_iff₀ (hpos k), mul_one]
    exact hlt
def HasFourPairs {r : ℕ} (D : PolyData2 r) : Prop :=
  ∃ j₀ j₁ j₂ j₃ : Fin r,
    det2 (D.N j₀) (D.N j₁) ≠ 0 ∧ det2 (D.N j₀) (D.N j₂) ≠ 0 ∧ det2 (D.N j₀) (D.N j₃) ≠ 0 ∧
    det2 (D.N j₁) (D.N j₂) ≠ 0 ∧ det2 (D.N j₁) (D.N j₃) ≠ 0 ∧ det2 (D.N j₂) (D.N j₃) ≠ 0
theorem PolyData2.hasFourPairs_map {r : ℕ} (D : PolyData2 r) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : IsUnit S.det) (h4 : HasFourPairs D) : HasFourPairs (D.map S hS) := by
  obtain ⟨j₀, j₁, j₂, j₃, h01, h02, h03, h12, h13, h23⟩ := h4
  have hd : Sᵀ.det ≠ 0 := by rw [det_transpose]; exact hS.ne_zero
  refine ⟨j₀, j₁, j₂, j₃, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { show det2 (Sᵀ *ᵥ _) (Sᵀ *ᵥ _) ≠ 0
      rw [ib]
      exact mul_ne_zero hd ‹_› }
theorem PolyData2.exists_two_pairs {r : ℕ} (D : PolyData2 r) : ∃ j₁ j₂ : Fin r, det2 (D.N j₁) (D.N j₂) ≠ 0 := by
  obtain ⟨R, hR⟩ := D.hAc.isBounded.subset_closedBall 0
  have hr : 0 < r := by
    by_contra hr0
    have hr' : r = 0 := by omega
    subst hr'
    have hmem : (![|R| + 1, 0] : Fin 2 → ℝ) ∈ D.A := by
      rw [D.mem_iff]; intro j; exact Fin.elim0 j
    have hb := hR hmem
    rw [mem_closedBall, dist_zero_right] at hb
    have hle := norm_le_pi_norm (![|R| + 1, 0] : Fin 2 → ℝ) 0
    simp only [Matrix.cons_val_zero, Real.norm_eq_abs] at hle
    have : 0 ≤ |R| := abs_nonneg R
    rw [abs_of_pos (by positivity)] at hle
    linarith [le_abs_self R]
  let j₁ : Fin r := ⟨0, hr⟩
  by_contra hall
  push Not at hall
  set v := perp2 (D.N j₁)
  have hv0 : v ≠ 0 := h7 (D.hN0 j₁)
  have hv_norm : 0 < ‖v‖ := norm_pos_iff.2 hv0
  let t := (|R| + 1) / ‖v‖
  have hmem : t • v ∈ D.A := by
    rw [D.mem_iff]
    intro k
    rcases D.hPar j₁ k (hall j₁ k) with rfl | rfl
    · rw [dotProduct_smul, h6, smul_zero]; norm_num
    · rw [D.hNeg, neg_dotProduct, dotProduct_smul, h6, smul_zero, neg_zero]; norm_num
  have hb := hR hmem
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hv_norm.ne'] at hb
  linarith [le_abs_self R]
theorem gZ {H₀ H₁ H₂ : ℝ} (_h0 : 0 < H₀) (_h1 : 0 < H₁) (_h2 : 0 < H₂) (t0 : H₀ < H₁ + H₂) (t1 : H₁ < H₀ + H₂) (t2 : H₂ < H₀ + H₁) : Hexagon.k3Zonotope ![H₁ + H₂ - H₀, H₀ + H₁ - H₂, H₀ + H₂ - H₁] = {y : Fin 2 → ℝ | |y 0 + y 1| ≤ H₀ ∧ |y 0| ≤ H₁ ∧ |y 1| ≤ H₂} := by
  set c : Fin 3 → ℝ := ![H₁ + H₂ - H₀, H₀ + H₁ - H₂, H₀ + H₂ - H₁] with hcdef
  have hc : ∀ e, 0 ≤ c e := fun e => by fin_cases e <;> simp [hcdef] <;> linarith
  ext y
  rw [Hexagon.mem_k3Zonotope_iff_cuts hc y, Set.mem_ofPred_eq]
  constructor
  · intro hcut
    have c01 := hcut {0, 1}
    have c2 := hcut {2}
    have c0 := hcut {0}
    have c12 := hcut {1, 2}
    have c1 := hcut {1}
    have c02 := hcut {0, 2}
    simp [cutVec2, cutCapacity, cutBit, crosses, k3Src, k3Dst, zr, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, hcdef] at c01 c2 c0 c12 c1 c02
    rw [abs_le, abs_le, abs_le]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨h01, hy0, hy1⟩ S
    rw [abs_le] at h01 hy0 hy1
    by_cases s0 : (0 : Fin 3) ∈ S <;> by_cases s1 : (1 : Fin 3) ∈ S <;>
      by_cases s2 : (2 : Fin 3) ∈ S <;>
      simp [cutVec2, cutCapacity, cutBit, crosses, k3Src, k3Dst, zr, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, s0, s1, s2, hcdef] <;> linarith
theorem PolyData2.rightSpectral_of_not_four {r : ℕ} (D : PolyData2 r) (hn4 : ¬ HasFourPairs D) : RightSpectral2 D.A := by
  obtain ⟨j₁, j₂, hd12⟩ := D.exists_two_pairs
  by_cases hex3 : ∃ j₀ : Fin r, det2 (D.N j₁) (D.N j₀) ≠ 0 ∧ det2 (D.N j₂) (D.N j₀) ≠ 0
  · obtain ⟨j₀, hd10, hd20⟩ := hex3
    have hd01 : det2 (D.N j₀) (D.N j₁) ≠ 0 := fun h => hd10 (by rw [is, h, neg_zero])
    have hd02 : det2 (D.N j₀) (D.N j₂) ≠ 0 := fun h => hd20 (by rw [is, h, neg_zero])
    have hall6 : ∀ k : Fin r,
        k = j₀ ∨ k = D.negIdx j₀ ∨ k = j₁ ∨ k = D.negIdx j₁ ∨ k = j₂ ∨ k = D.negIdx j₂ := by
      intro k
      by_contra hk
      push Not at hk
      apply hn4
      refine ⟨j₀, j₁, j₂, k, hd01, hd02, ?_, hd12, ?_, ?_⟩
      · intro h0; rcases D.hPar j₀ k h0 with h | h <;> tauto
      · intro h0; rcases D.hPar j₁ k h0 with h | h <;> tauto
      · intro h0; rcases D.hPar j₂ k h0 with h | h <;> tauto
    set α := det2 (D.N j₀) (D.N j₂) / det2 (D.N j₁) (D.N j₂)
    set β := det2 (D.N j₁) (D.N j₀) / det2 (D.N j₁) (D.N j₂)
    have hα0 : α ≠ 0 := div_ne_zero hd02 hd12
    have hβ0 : β ≠ 0 := div_ne_zero hd10 hd12
    have hn0_eq : D.N j₀ = α • D.N j₁ + β • D.N j₂ := by
      have hc := iv (D.N j₁) (D.N j₂) (D.N j₀)
      funext i
      have hci := congrFun hc i
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, α, β] at hci ⊢
      field_simp
      linear_combination hci
    set n₁ := α • D.N j₁
    set n₂ := β • D.N j₂
    set M := rows2 n₁ n₂
    have hMdet : M.det = α * β * det2 (D.N j₁) (D.N j₂) := by
      rw [ia]
      simp only [n₁, n₂, det2, Pi.smul_apply, smul_eq_mul]
      ring
    have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 (by rw [hMdet]; exact mul_ne_zero (mul_ne_zero hα0 hβ0) hd12)
    set T := M⁻¹
    have hTu : IsUnit T.det := by
      rw [isUnit_iff_ne_zero, det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_ne_zero hMu.ne_zero
    have hMT : ∀ y, M *ᵥ (T *ᵥ y) = y := fun y => by
      rw [mulVec_mulVec, mul_nonsing_inv M hMu, one_mulVec]
    have hdot1 : ∀ y, n₁ ⬝ᵥ (T *ᵥ y) = y 0 := fun y => by
      have := congrFun (hMT y) 0
      rw [show M = rows2 n₁ n₂ from rfl, h8, Matrix.cons_val_zero] at this
      exact this
    have hdot2 : ∀ y, n₂ ⬝ᵥ (T *ᵥ y) = y 1 := fun y => by
      have := congrFun (hMT y) 1
      rw [show M = rows2 n₁ n₂ from rfl, h8, Matrix.cons_val_one, Matrix.cons_val_zero] at this
      exact this
    have hdot0 : ∀ y, D.N j₀ ⬝ᵥ (T *ᵥ y) = y 0 + y 1 := fun y => by
      rw [hn0_eq, show (α • D.N j₁ + β • D.N j₂) ⬝ᵥ (T *ᵥ y) = n₁ ⬝ᵥ (T *ᵥ y) + n₂ ⬝ᵥ (T *ᵥ y) from add_dotProduct _ _ _, hdot1, hdot2]
    set H₀ : ℝ := 1
    set H₁ : ℝ := |α|
    set H₂ : ℝ := |β|
    have hH₀ : 0 < H₀ := one_pos
    have hH₁ : 0 < H₁ := abs_pos.2 hα0
    have hH₂ : 0 < H₂ := abs_pos.2 hβ0
    have hpre : {y | T *ᵥ y ∈ D.A} =
        {y : Fin 2 → ℝ | |y 0 + y 1| ≤ H₀ ∧ |y 0| ≤ H₁ ∧ |y 1| ≤ H₂} := by
      ext y
      simp only [Set.mem_ofPred_eq, D.mem_iff]
      have eq1 : |n₁ ⬝ᵥ (T *ᵥ y)| ≤ H₁ ↔ |D.N j₁ ⬝ᵥ (T *ᵥ y)| ≤ 1 := by
        simp only [n₁, smul_dotProduct, smul_eq_mul, abs_mul, H₁]
        exact ⟨fun h => le_of_mul_le_mul_left (by simpa using h) hH₁,
          fun h => by simpa using mul_le_mul_of_nonneg_left h hH₁.le⟩
      have eq2 : |n₂ ⬝ᵥ (T *ᵥ y)| ≤ H₂ ↔ |D.N j₂ ⬝ᵥ (T *ᵥ y)| ≤ 1 := by
        simp only [n₂, smul_dotProduct, smul_eq_mul, abs_mul, H₂]
        exact ⟨fun h => le_of_mul_le_mul_left (by simpa using h) hH₂,
          fun h => by simpa using mul_le_mul_of_nonneg_left h hH₂.le⟩
      rw [← hdot0 y, ← hdot1 y, ← hdot2 y, eq1, eq2]
      constructor
      · intro h
        have a0 : |D.N j₀ ⬝ᵥ (T *ᵥ y)| ≤ 1 := abs_le.2 ⟨by have := h (D.negIdx j₀); rw [D.hNeg, neg_dotProduct] at this; linarith, h j₀⟩
        have a1 : |D.N j₁ ⬝ᵥ (T *ᵥ y)| ≤ 1 := abs_le.2 ⟨by have := h (D.negIdx j₁); rw [D.hNeg, neg_dotProduct] at this; linarith, h j₁⟩
        have a2 : |D.N j₂ ⬝ᵥ (T *ᵥ y)| ≤ 1 := abs_le.2 ⟨by have := h (D.negIdx j₂); rw [D.hNeg, neg_dotProduct] at this; linarith, h j₂⟩
        exact ⟨a0, a1, a2⟩
      · rintro ⟨a0, a1, a2⟩ k
        rw [abs_le] at a0 a1 a2
        rcases hall6 k with rfl | rfl | rfl | rfl | rfl | rfl
        · exact a0.2
        · rw [D.hNeg, neg_dotProduct]; linarith
        · exact a1.2
        · rw [D.hNeg, neg_dotProduct]; linarith
        · exact a2.2
        · rw [D.hNeg, neg_dotProduct]; linarith
    have ne_pair : ∀ a b : Fin r, det2 (D.N a) (D.N b) ≠ 0 → b ≠ a ∧ D.negIdx b ≠ a := by
      intro a b hd
      refine ⟨fun h => hd (by rw [h, it]), fun h => hd ?_⟩
      rw [← h, D.hNeg, hO, it, neg_zero]
    have abs_lt_wit : ∀ a b : Fin r, det2 (D.N a) (D.N b) ≠ 0 → |D.N b ⬝ᵥ D.wit a| < 1 := by
      intro a b hd
      obtain ⟨h1, h2⟩ := ne_pair a b hd
      rw [abs_lt]
      refine ⟨?_, D.hwit_lt a b h1⟩
      have := D.hwit_lt a (D.negIdx b) h2
      rw [D.hNeg, neg_dotProduct] at this
      linarith
    have t0 : H₀ < H₁ + H₂ := by
      have w1 : |n₁ ⬝ᵥ D.wit j₀| < H₁ := by
        simp only [n₁, smul_dotProduct, smul_eq_mul, abs_mul, H₁]
        simpa using mul_lt_mul_of_pos_left (abs_lt_wit j₀ j₁ hd01) hH₁
      have w2 : |n₂ ⬝ᵥ D.wit j₀| < H₂ := by
        simp only [n₂, smul_dotProduct, smul_eq_mul, abs_mul, H₂]
        simpa using mul_lt_mul_of_pos_left (abs_lt_wit j₀ j₂ hd02) hH₂
      have w0 : n₁ ⬝ᵥ D.wit j₀ + n₂ ⬝ᵥ D.wit j₀ = 1 := by
        rw [← add_dotProduct, ← hn0_eq, D.hwit_eq]
      calc H₀ = |n₁ ⬝ᵥ D.wit j₀ + n₂ ⬝ᵥ D.wit j₀| := by rw [w0]; norm_num [H₀]
        _ ≤ |n₁ ⬝ᵥ D.wit j₀| + |n₂ ⬝ᵥ D.wit j₀| := abs_add_le _ _
        _ < H₁ + H₂ := add_lt_add w1 w2
    have t1 : H₁ < H₀ + H₂ := by
      have w0 : |D.N j₀ ⬝ᵥ D.wit j₁| < H₀ := abs_lt_wit j₁ j₀ hd10
      have w2 : |n₂ ⬝ᵥ D.wit j₁| < H₂ := by
        simp only [n₂, smul_dotProduct, smul_eq_mul, abs_mul, H₂]
        simpa using mul_lt_mul_of_pos_left (abs_lt_wit j₁ j₂ hd12) hH₂
      have w1 : |n₁ ⬝ᵥ D.wit j₁| = H₁ := by
        simp [n₁, smul_dotProduct, smul_eq_mul, abs_mul, D.hwit_eq, H₁]
      have weq : n₁ ⬝ᵥ D.wit j₁ = D.N j₀ ⬝ᵥ D.wit j₁ - n₂ ⬝ᵥ D.wit j₁ := by
        rw [hn0_eq, add_dotProduct]; ring
      calc H₁ = |D.N j₀ ⬝ᵥ D.wit j₁ - n₂ ⬝ᵥ D.wit j₁| := by rw [← weq, w1]
        _ ≤ |D.N j₀ ⬝ᵥ D.wit j₁| + |n₂ ⬝ᵥ D.wit j₁| := abs_sub _ _
        _ < H₀ + H₂ := add_lt_add w0 w2
    have t2 : H₂ < H₀ + H₁ := by
      have hd21 : det2 (D.N j₂) (D.N j₁) ≠ 0 := fun h => hd12 (by rw [is, h, neg_zero])
      have w0 : |D.N j₀ ⬝ᵥ D.wit j₂| < H₀ := abs_lt_wit j₂ j₀ hd20
      have w1 : |n₁ ⬝ᵥ D.wit j₂| < H₁ := by
        simp only [n₁, smul_dotProduct, smul_eq_mul, abs_mul, H₁]
        simpa using mul_lt_mul_of_pos_left (abs_lt_wit j₂ j₁ hd21) hH₁
      have w2 : |n₂ ⬝ᵥ D.wit j₂| = H₂ := by
        simp [n₂, smul_dotProduct, smul_eq_mul, abs_mul, D.hwit_eq, H₂]
      have weq : n₂ ⬝ᵥ D.wit j₂ = D.N j₀ ⬝ᵥ D.wit j₂ - n₁ ⬝ᵥ D.wit j₂ := by
        rw [hn0_eq, add_dotProduct]; ring
      calc H₂ = |D.N j₀ ⬝ᵥ D.wit j₂ - n₁ ⬝ᵥ D.wit j₂| := by rw [← weq, w2]
        _ ≤ |D.N j₀ ⬝ᵥ D.wit j₂| + |n₁ ⬝ᵥ D.wit j₂| := abs_sub _ _
        _ < H₀ + H₁ := add_lt_add w0 w1
    refine RightSpectral2.of_linear T hTu ?_
    rw [hpre, ← gZ hH₀ hH₁ hH₂ t0 t1 t2]
    intro m B hBm hBb hspec
    exact Hexagon.isSpectral_right_hexagon
      (fun e => by fin_cases e <;> simp <;> linarith) hBm hBb hspec
  · push Not at hex3
    have hall4 : ∀ k : Fin r,
        k = j₁ ∨ k = D.negIdx j₁ ∨ k = j₂ ∨ k = D.negIdx j₂ := by
      intro k
      by_cases h1 : det2 (D.N j₁) (D.N k) = 0
      · rcases D.hPar j₁ k h1 with h | h <;> tauto
      · have h2 := hex3 k h1
        rcases D.hPar j₂ k h2 with h | h <;> tauto
    set M := rows2 (D.N j₁) (D.N j₂)
    have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 (by rw [ia]; exact hd12)
    set T := M⁻¹
    have hTu : IsUnit T.det := by
      rw [isUnit_iff_ne_zero, det_nonsing_inv, Ring.inverse_eq_inv']
      exact inv_ne_zero hMu.ne_zero
    have hMT : ∀ y, M *ᵥ (T *ᵥ y) = y := fun y => by
      rw [mulVec_mulVec, mul_nonsing_inv M hMu, one_mulVec]
    have hpre : {y | T *ᵥ y ∈ D.A} = box2 ![-1, -1] ![1, 1] := by
      ext y
      simp only [Set.mem_ofPred_eq, D.mem_iff, box2, Set.mem_Icc]
      have d1 : D.N j₁ ⬝ᵥ (T *ᵥ y) = y 0 := by
        have := congrFun (hMT y) 0
        rw [show M = rows2 (D.N j₁) (D.N j₂) from rfl, h8, Matrix.cons_val_zero] at this
        exact this
      have d2 : D.N j₂ ⬝ᵥ (T *ᵥ y) = y 1 := by
        have := congrFun (hMT y) 1
        rw [show M = rows2 (D.N j₁) (D.N j₂) from rfl, h8, Matrix.cons_val_one, Matrix.cons_val_zero] at this
        exact this
      constructor
      · intro h i
        fin_cases i
        · simp
          have u1 := h j₁; have l1 := h (D.negIdx j₁)
          rw [D.hNeg, neg_dotProduct] at l1; rw [d1] at u1 l1
          exact ⟨by linarith, by linarith⟩
        · simp
          have u2 := h j₂; have l2 := h (D.negIdx j₂)
          rw [D.hNeg, neg_dotProduct] at l2; rw [d2] at u2 l2
          exact ⟨by linarith, by linarith⟩
      · intro hy k
        have y0 := hy 0; have y1 := hy 1
        simp at y0 y1
        rcases hall4 k with rfl | rfl | rfl | rfl
        · rw [d1]; exact y0.2
        · rw [D.hNeg, neg_dotProduct, d1]; linarith
        · rw [d2]; exact y1.2
        · rw [D.hNeg, neg_dotProduct, d2]; linarith
    refine RightSpectral2.of_linear T hTu ?_
    rw [hpre]
    exact gK fun i => by fin_cases i <;> norm_num
section Exclusion2D
theorem g0 {L : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)} (hL : Function.Injective L) (y : Fin 2 → ℝ) {U : Set (Fin 2 → ℝ)} (hU : IsOpen U) : IsOpen ((fun v => y + L v) '' U) := by
  set e := (LinearEquiv.ofInjectiveEndo L hL).toContinuousLinearEquiv
  have h1 : IsOpen (e '' U) := e.isOpenMap U hU
  have h2 : (fun v => y + L v) '' U = (fun w => y + w) '' (e '' U) := by
    rw [Set.image_image]; rfl
  rw [h2]
  exact (Homeomorph.addLeft y).isOpenMap _ h1
def lin2 (d₁ d₂ : Fin 2 → ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := v 0 • d₁ + v 1 • d₂
  map_add' v w := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' c v := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add]
theorem iw (d₁ d₂ v : Fin 2 → ℝ) : lin2 d₁ d₂ v = v 0 • d₁ + v 1 • d₂ := rfl
theorem g1 (k : Fin 2) (c : ℝ) : volume {x : Fin 2 → ℝ | x k = c} = 0 := by
  have : {x : Fin 2 → ℝ | x k = c} =
      Set.pi univ (fun i => if i = k then ({c} : Set ℝ) else univ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    exact ⟨fun hx i => by by_cases hi : i = k <;> [subst hi; skip] <;> simp [*],
      fun hx => by simpa using hx k⟩
  rw [this, volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
theorem g2 {P : (Fin 2 → ℝ) → Prop} (hP : ∀ᵐ v, P v) {U : Set (Fin 2 → ℝ)} (hU : IsOpen U) (hne : U.Nonempty) : ∃ v ∈ U, P v := by
  by_contra hcon
  push Not at hcon
  have h0 : volume {v | ¬P v} = 0 := ae_iff.1 hP
  have := measure_mono_null (fun v hv => hcon v hv) h0
  exact (hU.measure_pos volume hne).ne' this
theorem g3 {P : (Fin 2 → ℝ) → Prop} (hP : ∀ᵐ w, P w) (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : IsUnit M.det) (c : Fin 2 → ℝ) : ∀ᵐ x, P (affEquiv M hM c x) := by
  have hmp := measurePreserving_affEquiv M hM c
  have hq : Measure.QuasiMeasurePreserving (affEquiv M hM c) volume volume :=
    ⟨hmp.measurable, by rw [hmp.map_eq]; exact Measure.smul_absolutelyContinuous⟩
  exact hq.ae hP
theorem g4 {P : (Fin 1 → ℝ) → Prop} (hP : ∀ᵐ u, P u) : ∀ᵐ w : Fin (1 + 1) → ℝ, P (nH w) := by
  obtain ⟨B, hBsub, hBm, hB0⟩ := exists_measurable_superset_of_null (ae_iff.1 hP)
  rw [ae_iff]
  refine measure_mono_null (t := {w : Fin (1 + 1) → ℝ | nH w ∈ B}) (fun w hw => hBsub hw) ?_
  have hmeas : MeasurableSet {w : Fin (1 + 1) → ℝ | nH w ∈ B} :=
    hBm.preimage continuous_nH.measurable
  rw [← (measurePreserving_pt (k := 1)).measure_preimage hmeas.nullMeasurableSet]
  have : (fun p : (Fin 1 → ℝ) × ℝ => pt p.1 p.2) ⁻¹' {w | nH w ∈ B} = B ×ˢ univ := by
    ext p; simp [nH_pt]
  rw [this, Measure.prod_prod, hB0, zero_mul]
structure NormCorner2 (r : ℕ) extends PolyData2 r where
  j₁ : Fin r
  j₂ : Fin r
  hj₁ : N j₁ = ![0, -1]
  hj₂ : N j₂ = ![1, 0]
  hq : (![1, -1] : Fin 2 → ℝ) ∈ A
  ha₁ : ℝ
  hb₂ : ℝ
  ha₁_lt : -1 < ha₁ ∧ ha₁ < 1
  hb₂_lt : -1 < hb₂ ∧ hb₂ < 1
  hF₁_iff : ∀ u : ℝ, (![u, -1] : Fin 2 → ℝ) ∈ A ↔ u ∈ Icc ha₁ 1
  hF₂_iff : ∀ v : ℝ, (![1, v] : Fin 2 → ℝ) ∈ A ↔ v ∈ Icc (-1) hb₂
def cornerT₁ : Set (Fin 2 → ℝ) := {t | t 1 = -2 ∧ t 0 < 2}
def cornerT₂ : Set (Fin 2 → ℝ) := {t | t 0 = 2 ∧ -2 < t 1}
namespace NormCorner2
variable {r : ℕ} (C : NormCorner2 r)
def F₁ : Set (Fin 2 → ℝ) := {x | x ∈ C.A ∧ x 1 = -1}
def F₂ : Set (Fin 2 → ℝ) := {x | x ∈ C.A ∧ x 0 = 1}
def τ₁ : Fin 2 → ℝ := ![C.ha₁ + 1, -2]
def τ₂ : Fin 2 → ℝ := ![2, C.hb₂ - 1]
def D₂ : Set (Fin 2 → ℝ) := {x | ∃ f ∈ C.F₂, ∃ l ∈ Icc (0 : ℝ) 1, x = f + l • C.τ₂}
theorem le_one_0 {x : Fin 2 → ℝ} (hx : x ∈ C.A) : x 0 ≤ 1 := by
  have := C.toPolyData2.le_one hx C.j₂
  simpa [C.hj₂, dotProduct, Fin.sum_univ_two] using this
theorem neg_one_le_0 {x : Fin 2 → ℝ} (hx : x ∈ C.A) : -1 ≤ x 0 := by
  have := C.toPolyData2.neg_one_le hx C.j₂
  simpa [C.hj₂, dotProduct, Fin.sum_univ_two] using this
theorem neg_one_le_1 {x : Fin 2 → ℝ} (hx : x ∈ C.A) : -1 ≤ x 1 := by
  have := C.toPolyData2.le_one hx C.j₁
  simp [C.hj₁, dotProduct, Fin.sum_univ_two] at this
  linarith
theorem le_one_1 {x : Fin 2 → ℝ} (hx : x ∈ C.A) : x 1 ≤ 1 := by
  have := C.toPolyData2.neg_one_le hx C.j₁
  simp [C.hj₁, dotProduct, Fin.sum_univ_two] at this
  linarith
theorem mem_F₁_iff {x : Fin 2 → ℝ} : x ∈ C.F₁ ↔ x 0 ∈ Icc C.ha₁ 1 ∧ x 1 = -1 := by
  constructor
  · rintro ⟨hx, hx1⟩
    have hx' : (![x 0, -1] : Fin 2 → ℝ) = x := by funext i; fin_cases i <;> simp [hx1]
    rw [← hx'] at hx
    exact ⟨(C.hF₁_iff (x 0)).1 hx, hx1⟩
  · rintro ⟨hx0, hx1⟩
    have hx' : x = ![x 0, -1] := by funext i; fin_cases i <;> simp [hx1]
    exact ⟨hx' ▸ (C.hF₁_iff (x 0)).2 hx0, hx1⟩
theorem mem_F₂_iff {x : Fin 2 → ℝ} : x ∈ C.F₂ ↔ x 0 = 1 ∧ x 1 ∈ Icc (-1) C.hb₂ := by
  constructor
  · rintro ⟨hx, hx0⟩
    have hx' : (![1, x 1] : Fin 2 → ℝ) = x := by funext i; fin_cases i <;> simp [hx0]
    rw [← hx'] at hx
    exact ⟨hx0, (C.hF₂_iff (x 1)).1 hx⟩
  · rintro ⟨hx0, hx1⟩
    have hx' : x = ![1, x 1] := by funext i; fin_cases i <;> simp [hx0]
    exact ⟨hx' ▸ (C.hF₂_iff (x 1)).2 hx1, hx0⟩
theorem τ₁_sub_mem {f : Fin 2 → ℝ} (hf : f ∈ C.F₁) : C.τ₁ - f ∈ C.F₁ := by
  rw [C.mem_F₁_iff] at hf ⊢
  simp only [τ₁, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Set.mem_Icc] at hf ⊢
  exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
theorem τ₂_sub_mem {f : Fin 2 → ℝ} (hf : f ∈ C.F₂) : C.τ₂ - f ∈ C.F₂ := by
  rw [C.mem_F₂_iff] at hf ⊢
  simp only [τ₂, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Set.mem_Icc] at hf ⊢
  exact ⟨by linarith, by linarith, by linarith⟩
theorem prism₁ {f : Fin 2 → ℝ} (hf : f ∈ C.F₁) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) : f + l • C.τ₁ - C.τ₁ ∈ C.A := by
  have hneg : f - C.τ₁ ∈ C.A := by
    have := C.hAsymm _ (C.τ₁_sub_mem hf).1
    rwa [neg_sub] at this
  have := C.hAconv hf.1 hneg h0 (by linarith : 0 ≤ 1 - l) (by ring)
  rw [show f + l • C.τ₁ - C.τ₁ = l • f + (1 - l) • (f - C.τ₁) by module]
  exact this
theorem prism₂ {f : Fin 2 → ℝ} (hf : f ∈ C.F₂) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) : f + l • C.τ₂ - C.τ₂ ∈ C.A := by
  have hneg : f - C.τ₂ ∈ C.A := by
    have := C.hAsymm _ (C.τ₂_sub_mem hf).1
    rwa [neg_sub] at this
  have := C.hAconv hf.1 hneg h0 (by linarith : 0 ≤ 1 - l) (by ring)
  rw [show f + l • C.τ₂ - C.τ₂ = l • f + (1 - l) • (f - C.τ₂) by module]
  exact this
theorem vol_pos_translate2 {s : Fin 2 → ℝ} (hs : (![1, -1] : Fin 2 → ℝ) - s ∈ C.F₁) (hs0 : 0 < s 0) : 0 < volume (C.D₂ ∩ {x | x - C.τ₁ - s ∈ C.A}) := by
  rw [C.mem_F₁_iff] at hs
  have hs1 : s 1 = 0 := by simp at hs; linarith
  have hs0_le : 1 - s 0 ∈ Icc C.ha₁ 1 := by simpa using hs.1
  set y : Fin 2 → ℝ := ![1, -1]
  set LX := lin2 ![1, 0] C.τ₁
  set LY := lin2 ![0, 1] C.τ₂
  have hLXinj : Function.Injective LX := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have c0 := congrFun hv 0
    have c1 := congrFun hv 1
    simp [LX, iw, τ₁] at c0 c1
    rw [c1, zero_mul, add_zero] at c0
    funext i; fin_cases i <;> simp [c0, c1]
  have hLYinj : Function.Injective LY := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have c0 := congrFun hv 0
    have c1 := congrFun hv 1
    simp [LY, iw, τ₂] at c0 c1
    rw [c0, zero_mul, add_zero] at c1
    funext i; fin_cases i <;> simp [c0, c1]
  set UX : Set (Fin 2 → ℝ) := {v | 0 < v 0 ∧ v 0 < s 0 ∧ 0 < v 1 ∧ v 1 < 1}
  set UY : Set (Fin 2 → ℝ) := {v | 0 < v 0 ∧ v 0 < C.hb₂ + 1 ∧ 0 < v 1 ∧ v 1 < 1}
  have hUXo : IsOpen UX :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        ((isOpen_lt continuous_const (continuous_apply 1)).inter
          (isOpen_lt (continuous_apply 1) continuous_const)))
  have hUYo : IsOpen UY :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt (continuous_apply 0) continuous_const).inter
        ((isOpen_lt continuous_const (continuous_apply 1)).inter
          (isOpen_lt (continuous_apply 1) continuous_const)))
  have hOX := g0 hLXinj y hUXo
  have hOY := g0 hLYinj y hUYo
  have hXsub : (fun v => y + LX v) '' UX ⊆ {x | x - C.τ₁ - s ∈ C.A} := by
    rintro _ ⟨v, ⟨hv0, hv0', hv1, hv1'⟩, rfl⟩
    set f : Fin 2 → ℝ := ![1 - s 0 + v 0, -1]
    have hf : f ∈ C.F₁ := C.mem_F₁_iff.2 ⟨⟨by simp [f]; linarith [hs0_le.1], by simp [f]; linarith⟩, rfl⟩
    have hp := C.prism₁ hf hv1.le hv1'.le
    show y + LX v - C.τ₁ - s ∈ C.A
    have heq : y + LX v - C.τ₁ - s = f + v 1 • C.τ₁ - C.τ₁ := by
      funext i; fin_cases i <;> simp [y, LX, iw, f, hs1, τ₁] <;> ring
    rwa [heq]
  have hYsub : (fun v => y + LY v) '' UY ⊆ C.D₂ := by
    rintro _ ⟨v, ⟨hv0, hv0', hv1, hv1'⟩, rfl⟩
    set f : Fin 2 → ℝ := ![1, -1 + v 0]
    have hf : f ∈ C.F₂ := C.mem_F₂_iff.2 ⟨rfl, by simp [f]; linarith, by simp [f]; linarith⟩
    refine ⟨f, hf, v 1, ⟨hv1.le, hv1'.le⟩, ?_⟩
    funext i; fin_cases i <;> simp [y, LY, iw, f, τ₂] <;> ring
  have ht21 : C.τ₂ 1 < 0 := by simp [τ₂]; linarith [C.hb₂_lt.2]
  set l1 := min (1 / (|C.τ₁ 0| + 1)) (-(C.τ₂ 1) / 4)
  have hl1_pos : 0 < l1 := lt_min (by positivity) (by linarith)
  have hl1_a : l1 * (|C.τ₁ 0| + 1) ≤ 1 := by
    have := min_le_left (1 / (|C.τ₁ 0| + 1)) (-(C.τ₂ 1) / 4)
    rwa [le_div_iff₀ (by positivity)] at this
  have hl1_b : l1 ≤ -(C.τ₂ 1) / 4 := min_le_right _ _
  set a0 := 2 - l1 * C.τ₁ 0
  have ha0_pos : 0 < a0 := by
    have : l1 * C.τ₁ 0 ≤ l1 * |C.τ₁ 0| := mul_le_mul_of_nonneg_left (le_abs_self _) hl1_pos.le
    nlinarith
  set b0 := -(2 * l1) - C.τ₂ 1
  have hb0_pos : 0 < b0 := by simp [b0]; linarith
  set S := a0 / s 0 + l1 + b0 / (C.hb₂ + 1) + 2
  have hb2_pos : 0 < C.hb₂ + 1 := by linarith [C.hb₂_lt.1]
  have hdiv_a : 0 < a0 / s 0 := div_pos ha0_pos hs0
  have hdiv_b : 0 < b0 / (C.hb₂ + 1) := div_pos hb0_pos hb2_pos
  have hS_pos : 0 < S := by simp only [S]; linarith
  set ε := 1 / S
  have hε_pos : 0 < ε := one_div_pos.2 hS_pos
  have hεS : ε * S = 1 := one_div_mul_cancel hS_pos.ne'
  have h1 : ε * a0 < s 0 := by
    have hle : a0 / s 0 + 1 ≤ S := by simp only [S]; linarith
    have : ε * (a0 / s 0) < 1 := by nlinarith [mul_le_mul_of_nonneg_left hle hε_pos.le]
    rwa [← mul_div_assoc, div_lt_one hs0] at this
  have h2 : ε * l1 < 1 := by
    have hle : l1 + 1 ≤ S := by simp only [S]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hle hε_pos.le]
  have h3 : ε * b0 < C.hb₂ + 1 := by
    have hle : b0 / (C.hb₂ + 1) + 1 ≤ S := by simp only [S]; linarith
    have : ε * (b0 / (C.hb₂ + 1)) < 1 := by nlinarith [mul_le_mul_of_nonneg_left hle hε_pos.le]
    rwa [← mul_div_assoc, div_lt_one hb2_pos] at this
  have h4 : ε * 1 < 1 := by
    have hle : (2 : ℝ) ≤ S := by simp only [S]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hle hε_pos.le]
  set vX : Fin 2 → ℝ := ![ε * a0, ε * l1]
  set vY : Fin 2 → ℝ := ![ε * b0, ε * 1]
  have hvXU : vX ∈ UX := ⟨mul_pos hε_pos ha0_pos, h1, mul_pos hε_pos hl1_pos, h2⟩
  have hvYU : vY ∈ UY := ⟨mul_pos hε_pos hb0_pos, h3, mul_pos hε_pos one_pos, h4⟩
  have hcommon : LX vX = LY vY := by
    funext i; fin_cases i
    · show ε * a0 * 1 + ε * l1 * C.τ₁ 0 = ε * b0 * 0 + ε * 1 * 2
      simp [a0]; ring
    · show ε * a0 * 0 + ε * l1 * (-2) = ε * b0 * 1 + ε * 1 * C.τ₂ 1
      simp [b0]; ring
  have hne : ((fun v => y + LX v) '' UX ∩ (fun v => y + LY v) '' UY).Nonempty :=
    ⟨y + LX vX, ⟨vX, hvXU, rfl⟩, ⟨vY, hvYU, by rw [hcommon]⟩⟩
  calc 0 < volume ((fun v => y + LX v) '' UX ∩ (fun v => y + LY v) '' UY) :=
        (hOX.inter hOY).measure_pos volume hne
    _ ≤ volume (C.D₂ ∩ {x | x - C.τ₁ - s ∈ C.A}) :=
        measure_mono fun x hx => ⟨hYsub hx.2, hXsub hx.1⟩
def S₁_mat : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def S₂_mat : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
theorem S₁_mat_det : IsUnit S₁_mat.det := by
  rw [isUnit_iff_ne_zero, Matrix.det_fin_two]; simp [S₁_mat]
theorem S₂_mat_det : IsUnit S₂_mat.det := by
  rw [isUnit_iff_ne_zero, Matrix.det_fin_two]; simp [S₂_mat]
theorem facet_cover_F₁ {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ C.A} = C.Aᶜ.indicator 1 x) (hμ0 : μ (interior C.A - interior C.A) = 0) : ∀ᵐ u : Fin 1 → ℝ, u 0 ∈ Ioo C.ha₁ 1 → 1 ≤ μ {t | t - ![u 0, -1] ∈ C.F₁} := by
  set e := affEquiv S₁_mat S₁_mat_det 0
  set A' := e ⁻¹' C.A
  have hA'H : A' = Hpoly2 (fun j => S₁_matᵀ *ᵥ C.N j) (fun _ => 1) := by
    rw [show A' = e ⁻¹' C.A from rfl, C.hA_eq]
    exact g6 S₁_mat S₁_mat_det C.N (fun _ => 1)
  have hN' : ∀ j, S₁_matᵀ *ᵥ C.N j ≠ 0 := (C.toPolyData2.map S₁_mat S₁_mat_det).hN0
  have hsymm' := (C.toPolyData2.map S₁_mat S₁_mat_det).hAsymm
  have hcpt' := (C.toPolyData2.map S₁_mat S₁_mat_det).hAc
  have hmem' : ∀ x : Fin 2 → ℝ, x ∈ A' ↔ (![x 0, -x 1] : Fin 2 → ℝ) ∈ C.A := fun x => by
    simp only [A', e, Set.mem_preimage, affEquiv_apply, add_zero]
    have : S₁_mat *ᵥ x = ![x 0, -x 1] := by
      funext i; fin_cases i <;> simp [S₁_mat, mulVec, dotProduct, Fin.sum_univ_two]
    rw [this]
  have htop : ∀ x ∈ A', nV x ≤ 1 := fun x hx => by
    have := C.neg_one_le_1 ((hmem' x).1 hx)
    change x 1 ≤ 1
    simp at this; linarith
  haveI := gS S₁_mat_det (μ := μ)
  have hmain := gW hA'H hN' hsymm' hcpt' one_pos htop
    (gR S₁_mat_det hμ) (gT S₁_mat_det hμ0)
  have hsect : sect A' 1 = {u : Fin 1 → ℝ | u 0 ∈ Icc C.ha₁ 1} := by
    ext u
    show pt u 1 ∈ A' ↔ u 0 ∈ Icc C.ha₁ 1
    rw [ZonotopeFacets.pt_eq_vec2, hmem']
    simpa using C.hF₁_iff (u 0)
  have esym : ∀ t : Fin 2 → ℝ, (affEquiv S₁_mat S₁_mat_det 0).symm t = ![t 0, -t 1] := fun t => by
    rw [MeasurableEquiv.symm_apply_eq, gN]
    funext i; fin_cases i <;> simp [S₁_mat, mulVec, dotProduct, Fin.sum_univ_two]
  filter_upwards [hmain] with u hu hIoo
  have hint : u ∈ interior (sect A' 1) := by
    rw [hsect, mem_interior]
    set δ := min (u 0 - C.ha₁) (1 - u 0)
    have hδ : 0 < δ := lt_min (by linarith [hIoo.1]) (by linarith [hIoo.2])
    refine ⟨ball u δ, fun v hv => ?_, isOpen_ball, mem_ball_self hδ⟩
    rw [mem_ball, dist_eq_norm, ProductInterval.norm_fin_one] at hv
    have hv' := abs_lt.1 (by simpa using hv : |v 0 - u 0| < δ)
    exact ⟨by linarith [min_le_left (u 0 - C.ha₁) (1 - u 0)],
      by linarith [min_le_right (u 0 - C.ha₁) (1 - u 0)]⟩
  have h1 := hu hint
  rw [MeasurableEquiv.map_apply] at h1
  refine h1.trans (measure_mono fun t ht => ?_)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, esym, hsect] at ht
  have hv : nV (![t 0, -t 1] : Fin (1 + 1) → ℝ) = -t 1 := rfl
  have hh : (nH (![t 0, -t 1] : Fin (1 + 1) → ℝ) - u) 0 = t 0 - u 0 := rfl
  rw [hv, hh] at ht
  show t - ![u 0, -1] ∈ C.F₁
  rw [C.mem_F₁_iff]
  exact ⟨ht.2, by simp; linarith [ht.1]⟩
theorem facet_cover_F₂ {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ C.A} = C.Aᶜ.indicator 1 x) (hμ0 : μ (interior C.A - interior C.A) = 0) : ∀ᵐ v : Fin 1 → ℝ, v 0 ∈ Ioo (-1) C.hb₂ → 1 ≤ μ {t | t - ![1, v 0] ∈ C.F₂} := by
  set e := affEquiv S₂_mat S₂_mat_det 0
  set A' := e ⁻¹' C.A
  have hA'H : A' = Hpoly2 (fun j => S₂_matᵀ *ᵥ C.N j) (fun _ => 1) := by
    rw [show A' = e ⁻¹' C.A from rfl, C.hA_eq]
    exact g6 S₂_mat S₂_mat_det C.N (fun _ => 1)
  have hN' : ∀ j, S₂_matᵀ *ᵥ C.N j ≠ 0 := (C.toPolyData2.map S₂_mat S₂_mat_det).hN0
  have hsymm' := (C.toPolyData2.map S₂_mat S₂_mat_det).hAsymm
  have hcpt' := (C.toPolyData2.map S₂_mat S₂_mat_det).hAc
  have hmem' : ∀ x : Fin 2 → ℝ, x ∈ A' ↔ (![x 1, x 0] : Fin 2 → ℝ) ∈ C.A := fun x => by
    simp only [A', e, Set.mem_preimage, affEquiv_apply, add_zero]
    have : S₂_mat *ᵥ x = ![x 1, x 0] := by
      funext i; fin_cases i <;> simp [S₂_mat, mulVec, dotProduct, Fin.sum_univ_two]
    rw [this]
  have htop : ∀ x ∈ A', nV x ≤ 1 := fun x hx => by
    have := C.le_one_0 ((hmem' x).1 hx)
    change x 1 ≤ 1
    simpa using this
  haveI := gS S₂_mat_det (μ := μ)
  have hmain := gW hA'H hN' hsymm' hcpt' one_pos htop
    (gR S₂_mat_det hμ) (gT S₂_mat_det hμ0)
  have hsect : sect A' 1 = {v : Fin 1 → ℝ | v 0 ∈ Icc (-1) C.hb₂} := by
    ext v
    show pt v 1 ∈ A' ↔ v 0 ∈ Icc (-1) C.hb₂
    rw [ZonotopeFacets.pt_eq_vec2, hmem']
    simpa using C.hF₂_iff (v 0)
  have esym : ∀ t : Fin 2 → ℝ, (affEquiv S₂_mat S₂_mat_det 0).symm t = ![t 1, t 0] := fun t => by
    rw [MeasurableEquiv.symm_apply_eq, gN]
    funext i; fin_cases i <;> simp [S₂_mat, mulVec, dotProduct, Fin.sum_univ_two]
  filter_upwards [hmain] with v hv hIoo
  have hint : v ∈ interior (sect A' 1) := by
    rw [hsect, mem_interior]
    set δ := min (v 0 - (-1)) (C.hb₂ - v 0)
    have hδ : 0 < δ := lt_min (by linarith [hIoo.1]) (by linarith [hIoo.2])
    refine ⟨ball v δ, fun w hw => ?_, isOpen_ball, mem_ball_self hδ⟩
    rw [mem_ball, dist_eq_norm, ProductInterval.norm_fin_one] at hw
    have hw' := abs_lt.1 (by simpa using hw : |w 0 - v 0| < δ)
    exact ⟨by linarith [min_le_left (v 0 - (-1)) (C.hb₂ - v 0)],
      by linarith [min_le_right (v 0 - (-1)) (C.hb₂ - v 0)]⟩
  have h1 := hv hint
  rw [MeasurableEquiv.map_apply] at h1
  refine h1.trans (measure_mono fun t ht => ?_)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, esym, hsect] at ht
  have hv' : nV (![t 1, t 0] : Fin (1 + 1) → ℝ) = t 0 := rfl
  have hh' : (nH (![t 1, t 0] : Fin (1 + 1) → ℝ) - v) 0 = t 1 - v 0 := rfl
  rw [hv', hh'] at ht
  show t - ![1, v 0] ∈ C.F₂
  rw [C.mem_F₂_iff]
  exact ⟨by simp; linarith [ht.1], ht.2⟩
theorem isCompact_F₁ : IsCompact C.F₁ :=
  C.hAc.of_isClosed_subset
    (C.hAc.isClosed.inter (isClosed_eq (continuous_apply 1) continuous_const)) fun _ hx => hx.1
theorem isCompact_F₂ : IsCompact C.F₂ :=
  C.hAc.of_isClosed_subset
    (C.hAc.isClosed.inter (isClosed_eq (continuous_apply 0) continuous_const)) fun _ hx => hx.1
theorem isCompact_D₂ : IsCompact C.D₂ := by
  have : C.D₂ = (fun p : (Fin 2 → ℝ) × ℝ => p.1 + p.2 • C.τ₂) '' (C.F₂ ×ˢ Icc 0 1) := by
    ext x
    simp only [D₂, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod, Prod.exists]
    exact ⟨fun ⟨f, hf, l, hl, hfl⟩ => ⟨f, l, ⟨hf, hl⟩, hfl.symm⟩,
      fun ⟨f, l, ⟨hf, hl⟩, hfl⟩ => ⟨f, hf, l, hl, hfl.symm⟩⟩
  rw [this]
  exact (C.isCompact_F₂.prod isCompact_Icc).image
    (continuous_fst.add (continuous_snd.smul continuous_const))
noncomputable def MD2 : Matrix (Fin 2) (Fin 2) ℝ := !![-(C.τ₂ 1) / 2, 1; 1 / 2, 0]
noncomputable def cD2 : Fin 2 → ℝ := ![C.τ₂ 1 / 2, -(1 / 2)]
theorem MD2_det : IsUnit C.MD2.det := by
  rw [isUnit_iff_ne_zero, Matrix.det_fin_two]; simp [MD2]
theorem cover_D₂ {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ C.A} = C.Aᶜ.indicator 1 x) (hμ0 : μ (interior C.A - interior C.A) = 0) : ∀ᵐ x, x ∈ C.D₂ → 1 ≤ μ ({t | x - t ∈ C.A} ∩ cornerT₂) := by
  have hFC := C.facet_cover_F₂ hμ hμ0
  have hend : ∀ᵐ v : Fin 1 → ℝ, v 0 ≠ -1 ∧ v 0 ≠ C.hb₂ := by
    have hmp := volume_preserving_funUnique (Fin 1) ℝ
    have h1 : volume ({-1, C.hb₂} : Set ℝ) = 0 :=
      measure_union_null (measure_singleton _) (measure_singleton _)
    rw [ae_iff]
    refine measure_mono_null (t := (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' {-1, C.hb₂})
      (fun v hv => ?_) ?_
    · simp only [Set.mem_ofPred_eq, not_and_or, not_not] at hv
      exact hv
    · exact (hmp.measure_preimage (MeasurableSet.nullMeasurableSet (by simp))).trans h1
  have hgood : ∀ᵐ v : Fin 1 → ℝ, v 0 ∈ Icc (-1) C.hb₂ →
      v 0 ∈ Ioo (-1) C.hb₂ ∧ 1 ≤ μ {t | t - ![1, v 0] ∈ C.F₂} := by
    filter_upwards [hFC, hend] with v h1 h2 hv
    have hIoo : v 0 ∈ Ioo (-1) C.hb₂ :=
      ⟨lt_of_le_of_ne hv.1 (Ne.symm h2.1), lt_of_le_of_ne hv.2 h2.2⟩
    exact ⟨hIoo, h1 hIoo⟩
  have hgood' := g3 (g4 hgood) C.MD2 C.MD2_det C.cD2
  filter_upwards [hgood'] with x hx hxD
  obtain ⟨f, hf, l, ⟨hl0, hl1⟩, rfl⟩ := hxD
  obtain ⟨hf0, hf1⟩ := C.mem_F₂_iff.1 hf
  have hbase : (nH (affEquiv C.MD2 C.MD2_det C.cD2 (f + l • C.τ₂))) 0 = f 1 := by
    change (affEquiv C.MD2 C.MD2_det C.cD2 (f + l • C.τ₂)) 0 = f 1
    rw [affEquiv_apply]
    simp [MD2, cD2, τ₂, Matrix.vecHead, Matrix.vecTail, hf0]
    ring
  rw [hbase] at hx
  obtain ⟨hfIoo, hmass⟩ := hx hf1
  have hf_eq : (![1, f 1] : Fin 2 → ℝ) = f := by funext i; fin_cases i <;> simp [hf0]
  rw [hf_eq] at hmass
  refine hmass.trans (measure_mono fun t ht => ?_)
  have hf' : t - f ∈ C.F₂ := ht
  obtain ⟨ht0, ht1⟩ := C.mem_F₂_iff.1 hf'
  refine ⟨?_, ?_, ?_⟩
  · have := C.prism₂ (C.τ₂_sub_mem hf') hl0 hl1
    show f + l • C.τ₂ - t ∈ C.A
    convert this using 1
    module
  · show t 0 = 2
    simp at ht0; linarith
  · show -2 < t 1
    simp at ht1; linarith [hfIoo.1, ht1.1]
theorem exclusion2 {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ C.A} = C.Aᶜ.indicator 1 x) (hμ0 : μ (interior C.A - interior C.A) = 0) : ∀ᵐ t ∂μ, t ∈ cornerT₁ → volume (C.D₂ ∩ {x | x - t ∈ C.A}) = 0 := by
  have hD₂m : MeasurableSet C.D₂ := C.isCompact_D₂.isClosed.measurableSet
  have hAm : MeasurableSet C.A := C.hAc.isClosed.measurableSet
  have hT₁m : MeasurableSet cornerT₁ :=
    (measurableSet_eq_fun (measurable_pi_apply 1) measurable_const).inter
      (measurableSet_lt (measurable_pi_apply 0) measurable_const)
  have hT₂m : MeasurableSet cornerT₂ :=
    (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_pi_apply 1))
  set Sset := {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | p.1 ∈ C.D₂ ∧ p.2 ∈ cornerT₁ ∧ p.1 - p.2 ∈ C.A}
  have hSm : MeasurableSet Sset :=
    (hD₂m.preimage measurable_fst).inter ((hT₁m.preimage measurable_snd).inter
      (hAm.preimage (measurable_fst.sub measurable_snd)))
  have hmeas : Measurable (Sset.indicator (1 : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ENNReal)) :=
    measurable_one.indicator hSm
  have hswap := lintegral_lintegral_swap (μ := (volume : Measure (Fin 2 → ℝ))) (ν := μ)
    (f := fun x t => Sset.indicator 1 (x, t)) hmeas.aemeasurable
  have hin1 : ∀ x, ∫⁻ t, Sset.indicator 1 (x, t) ∂μ =
      C.D₂.indicator (fun x => μ ({t | x - t ∈ C.A} ∩ cornerT₁)) x := by
    intro x
    by_cases hx : x ∈ C.D₂
    · rw [Set.indicator_of_mem hx]
      have : (fun t => Sset.indicator (1 : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ENNReal) (x, t)) =
          ({t | x - t ∈ C.A} ∩ cornerT₁).indicator 1 := by
        funext t
        by_cases ht : x - t ∈ C.A ∧ t ∈ cornerT₁
        · have h1 : (x, t) ∈ Sset := ⟨hx, ht.2, ht.1⟩
          have h2 : t ∈ {t | x - t ∈ C.A} ∩ cornerT₁ := ht
          rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]; rfl
        · have h1 : (x, t) ∉ Sset := fun h' => ht ⟨h'.2.2, h'.2.1⟩
          have h2 : t ∉ {t | x - t ∈ C.A} ∩ cornerT₁ := ht
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      have hm1 : MeasurableSet ({t | x - t ∈ C.A} ∩ cornerT₁) :=
        (hAm.preimage (continuous_const.sub continuous_id).measurable).inter hT₁m
      rw [this]
      exact lintegral_indicator_one hm1
    · rw [Set.indicator_of_notMem hx]
      have : (fun t => Sset.indicator (1 : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ENNReal) (x, t)) = 0 :=
        funext fun t => Set.indicator_of_notMem (fun h' => hx h'.1) _
      rw [this]; exact lintegral_zero_fun
  have hin2 : ∀ t, ∫⁻ x, Sset.indicator 1 (x, t) =
      cornerT₁.indicator (fun t => volume (C.D₂ ∩ {x | x - t ∈ C.A})) t := by
    intro t
    by_cases ht : t ∈ cornerT₁
    · rw [Set.indicator_of_mem ht]
      have : (fun x => Sset.indicator (1 : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ENNReal) (x, t)) =
          (C.D₂ ∩ {x | x - t ∈ C.A}).indicator 1 := by
        funext x
        by_cases hx : x ∈ C.D₂ ∧ x - t ∈ C.A
        · have h1 : (x, t) ∈ Sset := ⟨hx.1, ht, hx.2⟩
          have h2 : x ∈ C.D₂ ∩ {x | x - t ∈ C.A} := hx
          rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]; rfl
        · have h1 : (x, t) ∉ Sset := fun h' => hx ⟨h'.1, h'.2.2⟩
          have h2 : x ∉ C.D₂ ∩ {x | x - t ∈ C.A} := hx
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      have hm2 : MeasurableSet (C.D₂ ∩ {x | x - t ∈ C.A}) :=
        hD₂m.inter (hAm.preimage (continuous_id.sub continuous_const).measurable)
      rw [this]
      exact lintegral_indicator_one hm2
    · rw [Set.indicator_of_notMem ht]
      have : (fun x => Sset.indicator (1 : (Fin 2 → ℝ) × (Fin 2 → ℝ) → ENNReal) (x, t)) = 0 :=
        funext fun x => Set.indicator_of_notMem (fun h' => ht h'.2.1) _
      rw [this]; exact lintegral_zero_fun
  simp only [hin1, hin2] at hswap
  have hnotA : ∀ᵐ x : Fin 2 → ℝ, x ∈ C.D₂ → x ∉ C.A := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (g1 0 1)
    simp only [Set.mem_ofPred_eq, not_forall, not_not] at hx
    obtain ⟨⟨f, hf, l, ⟨hl0, _⟩, rfl⟩, hA⟩ := hx
    have h1 := C.le_one_0 hA
    have hf0 := (C.mem_F₂_iff.1 hf).1
    show (f + l • C.τ₂) 0 = 1
    simp [τ₂, hf0] at h1 ⊢
    linarith
  have hdisjT : Disjoint cornerT₁ cornerT₂ := Set.disjoint_left.2 fun t ⟨_, h1⟩ ⟨h2, _⟩ => by linarith
  have hLHS : ∫⁻ x, C.D₂.indicator (fun x => μ ({t | x - t ∈ C.A} ∩ cornerT₁)) x = 0 := by
    rw [← lintegral_zero (μ := (volume : Measure (Fin 2 → ℝ)))]
    refine lintegral_congr_ae ?_
    filter_upwards [C.cover_D₂ hμ hμ0, hμ, hnotA] with x h1 h2 h3
    by_cases hx : x ∈ C.D₂
    · rw [Set.indicator_of_mem hx]
      have hxA := h3 hx
      rw [Set.indicator_of_mem (show x ∈ C.Aᶜ from hxA), Pi.one_apply] at h2
      have hdisj : Disjoint ({t | x - t ∈ C.A} ∩ cornerT₁) ({t | x - t ∈ C.A} ∩ cornerT₂) :=
        Disjoint.mono inter_subset_right inter_subset_right hdisjT
      have hunion := measure_union (μ := μ) hdisj
        ((hAm.preimage (continuous_const.sub continuous_id).measurable).inter hT₂m)
      have hle : μ ({t | x - t ∈ C.A} ∩ cornerT₁ ∪ {t | x - t ∈ C.A} ∩ cornerT₂) ≤ 1 := by
        rw [← h2]; exact measure_mono (union_subset inter_subset_left inter_subset_left)
      rw [hunion] at hle
      have h4 := h1 hx
      by_contra hne
      have hpos : 0 < μ ({t | x - t ∈ C.A} ∩ cornerT₁) := pos_iff_ne_zero.2 hne
      have : 1 < μ ({t | x - t ∈ C.A} ∩ cornerT₁) + μ ({t | x - t ∈ C.A} ∩ cornerT₂) :=
        calc (1 : ENNReal) = 0 + 1 := by rw [zero_add]
          _ < μ ({t | x - t ∈ C.A} ∩ cornerT₁) + 1 :=
              ENNReal.add_lt_add_right ENNReal.one_ne_top hpos
          _ ≤ _ := add_le_add le_rfl h4
      exact absurd hle (not_le.2 this)
    · rw [Set.indicator_of_notMem hx]
  rw [hLHS, eq_comm] at hswap
  have hmeas2 : Measurable fun t => cornerT₁.indicator (fun t => volume (C.D₂ ∩ {x | x - t ∈ C.A})) t := by
    have : (fun t => cornerT₁.indicator (fun t => volume (C.D₂ ∩ {x | x - t ∈ C.A})) t) =
        fun t => ∫⁻ x, Sset.indicator 1 (x, t) := funext fun t => (hin2 t).symm
    rw [this]; exact hmeas.lintegral_prod_left'
  have := (lintegral_eq_zero_iff hmeas2).1 hswap
  filter_upwards [this] with t ht htT
  rw [Pi.zero_apply, Set.indicator_of_mem htT] at ht
  exact ht
theorem atom_localize2 {ρ : ℝ} (hρ : 0 < ρ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ s : Fin 2 → ℝ, (![1 - ε, -1] : Fin 2 → ℝ) - s ∈ C.F₁ → volume.real (C.D₂ ∩ {x | x - C.τ₁ - s ∈ C.A}) = 0 → dist s 0 < ρ := by
  set Ψ : (Fin 2 → ℝ) → ℝ := fun s => xcorr C.D₂ C.A (C.τ₁ + s)
  have hΨ_eq : ∀ s, Ψ s = volume.real (C.D₂ ∩ {x | x - C.τ₁ - s ∈ C.A}) := fun s => by
    simp only [Ψ, xcorr]; congr 2; ext x; simp [sub_sub]
  have hΨ_cont : Continuous Ψ :=
    (continuous_xcorr C.D₂ C.hAc.isClosed.measurableSet C.hAc.measure_lt_top.ne).comp
      (continuous_const.add continuous_id)
  have hF₁_closed : IsClosed C.F₁ := C.isCompact_F₁.isClosed
  set K := {p : ℝ × (Fin 2 → ℝ) | p.1 ∈ Icc (0 : ℝ) 1 ∧ (![1 - p.1, -1] : Fin 2 → ℝ) - p.2 ∈ C.F₁ ∧
    Ψ p.2 = 0 ∧ ρ ≤ dist p.2 0}
  have hemb : Continuous fun q : ℝ × (Fin 2 → ℝ) => (![1 - q.1, -1] : Fin 2 → ℝ) - q.2 := by
    refine Continuous.sub (continuous_pi fun i => ?_) continuous_snd
    fin_cases i <;> simp <;> fun_prop
  have hL : IsCompact ((fun q : ℝ × (Fin 2 → ℝ) => (![1 - q.1, -1] : Fin 2 → ℝ) - q.2) ''
      (Icc 0 1 ×ˢ C.F₁)) := (isCompact_Icc.prod C.isCompact_F₁).image hemb
  have hKsub : K ⊆ Icc 0 1 ×ˢ
      ((fun q : ℝ × (Fin 2 → ℝ) => (![1 - q.1, -1] : Fin 2 → ℝ) - q.2) '' (Icc 0 1 ×ˢ C.F₁)) := by
    rintro ⟨ε, s⟩ ⟨hε, hs, -, -⟩
    exact ⟨hε, (ε, (![1 - ε, -1] : Fin 2 → ℝ) - s), ⟨hε, hs⟩, sub_sub_cancel _ _⟩
  have hKclosed : IsClosed K :=
    (isClosed_Icc.preimage continuous_fst).inter
      ((hF₁_closed.preimage hemb).inter
        ((isClosed_eq (hΨ_cont.comp continuous_snd) continuous_const).inter
          (isClosed_le continuous_const (continuous_snd.dist continuous_const))))
  have hKc : IsCompact K := (isCompact_Icc.prod hL).of_isClosed_subset hKclosed hKsub
  have h0 : (0 : ℝ) ∉ Prod.fst '' K := by
    rintro ⟨⟨ε, s⟩, ⟨-, hs, hΨ0, hfar⟩, rfl⟩
    have hs' : (![1, -1] : Fin 2 → ℝ) - s ∈ C.F₁ := by simpa using hs
    obtain ⟨hs0_mem, hs1⟩ := C.mem_F₁_iff.1 hs'
    have hs1_0 : s 1 = 0 := by simp at hs1; linarith
    by_cases hs0 : 0 < s 0
    · have hpos := C.vol_pos_translate2 hs' hs0
      have hfin : volume (C.D₂ ∩ {x | x - C.τ₁ - s ∈ C.A}) ≠ ⊤ :=
        (C.isCompact_D₂.measure_lt_top.trans_le' (measure_mono inter_subset_left)).ne
      have := ENNReal.toReal_pos hpos.ne' hfin
      rw [← measureReal_def, ← hΨ_eq] at this
      linarith
    · have hs0_0 : s 0 = 0 := by simp at hs0_mem; linarith [hs0_mem.2]
      have hs_zero : s = 0 := by funext i; fin_cases i <;> simp [hs0_0, hs1_0]
      rw [hs_zero, dist_self] at hfar
      linarith
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 (hKc.image continuous_fst).isClosed.isOpen_compl 0 h0
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, fun ε hε hεlt s hs hvol => ?_⟩
  by_contra hcon
  push Not at hcon
  have hmem : ε ∈ Prod.fst '' K :=
    ⟨(ε, s), ⟨⟨hε.le, (hεlt.trans_le (min_le_right _ _)).le⟩, hs, by rwa [hΨ_eq], hcon⟩, rfl⟩
  have hb : ε ∈ ball (0 : ℝ) ε₀ := by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    exact hεlt.trans_le (min_le_left _ _)
  exact hball hb hmem
theorem one_le_measure_τ₁ {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ C.A} = C.Aᶜ.indicator 1 x) (hμ0 : μ (interior C.A - interior C.A) = 0) : 1 ≤ μ {C.τ₁} := by
  have hFC := C.facet_cover_F₁ hμ hμ0
  have hnull : μ {t | ¬(t ∈ cornerT₁ → volume (C.D₂ ∩ {x | x - t ∈ C.A}) = 0)} = 0 :=
    ae_iff.1 (C.exclusion2 hμ hμ0)
  set U : ℕ → Set (Fin 2 → ℝ) := fun n => ball C.τ₁ (1 / ((n : ℝ) + 1))
  have hball_mass : ∀ n : ℕ, 1 ≤ μ (U n) := by
    intro n
    have hρ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨ε₀, hε₀, hloc⟩ := C.atom_localize2 hρ
    set δ := min ε₀ (1 - C.ha₁)
    have hδ : 0 < δ := lt_min hε₀ (by linarith [C.ha₁_lt.2])
    obtain ⟨u, hu_mem, huP⟩ : ∃ u : Fin 1 → ℝ, u 0 ∈ Ioo (1 - δ) 1 ∧
        (u 0 ∈ Ioo C.ha₁ 1 → 1 ≤ μ {t | t - ![u 0, -1] ∈ C.F₁}) := by
      by_contra hcon
      have hmp := volume_preserving_funUnique (Fin 1) ℝ
      have hsub : (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioo (1 - δ) 1 ⊆
          {u : Fin 1 → ℝ | ¬(u 0 ∈ Ioo C.ha₁ 1 → 1 ≤ μ {t | t - ![u 0, -1] ∈ C.F₁})} :=
        fun u hu => fun hP => hcon ⟨u, hu, hP⟩
      have h0 := measure_mono_null hsub (ae_iff.1 hFC)
      have hm : volume ((MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioo (1 - δ) 1) =
          volume (Ioo (1 - δ) 1) :=
        hmp.measure_preimage isOpen_Ioo.measurableSet.nullMeasurableSet
      rw [hm, Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
      linarith
    have huIoo : u 0 ∈ Ioo C.ha₁ 1 :=
      ⟨by linarith [hu_mem.1, min_le_right ε₀ (1 - C.ha₁)], hu_mem.2⟩
    set ε := 1 - u 0
    have hε0 : 0 < ε := by simp [ε]; linarith [hu_mem.2]
    have hε_lt : ε < ε₀ := by simp [ε]; linarith [hu_mem.1, min_le_left ε₀ (1 - C.ha₁)]
    calc (1 : ENNReal) ≤ μ {t | t - ![u 0, -1] ∈ C.F₁} := huP huIoo
      _ ≤ μ (U n ∪ {t | ¬(t ∈ cornerT₁ → volume (C.D₂ ∩ {x | x - t ∈ C.A}) = 0)}) := by
          refine measure_mono fun t ht => ?_
          by_cases hgood : t ∈ cornerT₁ → volume (C.D₂ ∩ {x | x - t ∈ C.A}) = 0
          swap
          · exact Or.inr hgood
          left
          obtain ⟨ht0_mem, ht1⟩ := C.mem_F₁_iff.1 ht
          have htT : t ∈ cornerT₁ := ⟨by simp at ht1; linarith, by simp at ht0_mem; linarith [hu_mem.2, ht0_mem.2]⟩
          have hvol := hgood htT
          set s := t - C.τ₁
          have hvol_real : volume.real (C.D₂ ∩ {x | x - C.τ₁ - s ∈ C.A}) = 0 := by
            have e : C.D₂ ∩ {x | x - C.τ₁ - s ∈ C.A} = C.D₂ ∩ {x | x - t ∈ C.A} := by
              congr 1; ext x; simp only [Set.mem_ofPred_eq, s]; rw [show x - C.τ₁ - (t - C.τ₁) = x - t by abel]
            rw [e, measureReal_def, hvol, ENNReal.toReal_zero]
          have hsF : (![1 - ε, -1] : Fin 2 → ℝ) - s ∈ C.F₁ := by
            have hrefl := C.τ₁_sub_mem ht
            have e : (![1 - ε, -1] : Fin 2 → ℝ) - s = C.τ₁ - (t - ![u 0, -1]) := by
              funext i; fin_cases i <;> simp [ε, s, τ₁] <;> ring
            rwa [e]
          have hd := hloc ε hε0 hε_lt s hsF hvol_real
          show t ∈ ball C.τ₁ (1 / ((n : ℝ) + 1))
          rw [mem_ball, dist_eq_norm]
          simpa [s, dist_eq_norm] using hd
      _ ≤ μ (U n) + μ {t | ¬(t ∈ cornerT₁ → volume (C.D₂ ∩ {x | x - t ∈ C.A}) = 0)} :=
          measure_union_le _ _
      _ = μ (U n) := by rw [hnull, add_zero]
  have hanti : Antitone U := fun m n hmn =>
    ball_subset_ball (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1))
  have hfin : μ (U 0) ≠ ⊤ :=
    ((isCompact_closedBall C.τ₁ 1).measure_lt_top.trans_le' (measure_mono (by simpa [U] using ball_subset_closedBall))).ne
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => isOpen_ball.measurableSet.nullMeasurableSet) hanti ⟨0, hfin⟩
  have hge : 1 ≤ μ (⋂ n, U n) := ge_of_tendsto' hlim hball_mass
  refine hge.trans (measure_mono fun t ht => ?_)
  rw [mem_iInter] at ht
  rw [mem_singleton_iff]
  by_contra hne
  have hd : 0 < dist t C.τ₁ := dist_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
  have := ht n
  rw [mem_ball] at this
  linarith
def ik : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; -1, 0]
theorem il : IsUnit ik.det := by
  rw [isUnit_iff_ne_zero, Matrix.det_fin_two]; simp [ik]
theorem io (x : Fin 2 → ℝ) : ik *ᵥ x = ![-x 1, -x 0] := by
  funext i; fin_cases i <;> simp [ik, mulVec, dotProduct, Fin.sum_univ_two]
theorem ip (x : Fin 2 → ℝ) : ik *ᵥ (ik *ᵥ x) = x := by
  rw [io, io]; funext i; fin_cases i <;> simp
noncomputable def refl : NormCorner2 r where
  toPolyData2 := C.toPolyData2.map ik il
  j₁ := C.j₂
  j₂ := C.j₁
  hj₁ := by
    show ikᵀ *ᵥ C.N C.j₂ = ![0, -1]
    rw [C.hj₂]; funext i; fin_cases i <;> simp [ik, mulVec, dotProduct, Fin.sum_univ_two]
  hj₂ := by
    show ikᵀ *ᵥ C.N C.j₁ = ![1, 0]
    rw [C.hj₁]; funext i; fin_cases i <;> simp [ik, mulVec, dotProduct, Fin.sum_univ_two]
  hq := by
    simp only [PolyData2.map, Set.mem_preimage, affEquiv_apply, add_zero, io]
    simpa using C.hq
  ha₁ := -C.hb₂
  hb₂ := -C.ha₁
  ha₁_lt := ⟨by linarith [C.hb₂_lt.2], by linarith [C.hb₂_lt.1]⟩
  hb₂_lt := ⟨by linarith [C.ha₁_lt.2], by linarith [C.ha₁_lt.1]⟩
  hF₁_iff u := by
    simp only [PolyData2.map, Set.mem_preimage, affEquiv_apply, add_zero, io, Matrix.cons_val_zero, Matrix.cons_val_one, neg_neg]
    rw [C.hF₂_iff (-u), Set.mem_Icc, Set.mem_Icc]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩
  hF₂_iff v := by
    simp only [PolyData2.map, Set.mem_preimage, affEquiv_apply, add_zero, io, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [C.hF₁_iff (-v), Set.mem_Icc, Set.mem_Icc]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩, fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩
theorem one_le_measure_τ₂ {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ C.A} = C.Aᶜ.indicator 1 x) (hμ0 : μ (interior C.A - interior C.A) = 0) : 1 ≤ μ {C.τ₂} := by
  haveI := gS il (μ := μ)
  have h1 := C.refl.one_le_measure_τ₁
    (gR il hμ) (gT il hμ0)
  rw [MeasurableEquiv.map_apply] at h1
  refine h1.trans (measure_mono fun t ht => ?_)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at ht ⊢
  have he : (affEquiv ik il 0).symm t = ik *ᵥ t := by
    rw [MeasurableEquiv.symm_apply_eq, gN, ip]
  rw [he] at ht
  have := congrArg (fun v => ik *ᵥ v) ht
  rw [ip] at this
  rw [this]
  show ik *ᵥ (![-C.hb₂ + 1, -2] : Fin 2 → ℝ) = C.τ₂
  rw [io]
  funext i; fin_cases i <;> simp [τ₂] <;> ring
theorem hex_subset_A {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (eq_p₂ : α + β * C.hb₂ = 1) (eq_p₁ : -(α * C.ha₁) + β = 1) {y : Fin 2 → ℝ} (hy0 : |y 0| ≤ 1) (hy1 : |y 1| ≤ 1) (hy01 : |α * y 0 + β * y 1| ≤ 1) : y ∈ C.A := by
  by_contra hyA
  obtain ⟨f, r, hfy, hfb⟩ := geometric_hahn_banach_point_closed C.hAconv C.hAc.isClosed hyA
  let w : Fin 2 → ℝ := fun i => -(f fun j => if i = j then 1 else 0)
  have hf : ∀ p : Fin 2 → ℝ, -f p = w 0 * p 0 + w 1 * p 1 := fun p => by
    have := LinearMap.pi_apply_eq_sum_univ (f : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) p
    simp [w, Fin.sum_univ_two, smul_eq_mul] at this ⊢
    linarith
  have hlt : ∀ b ∈ C.A, w 0 * b 0 + w 1 * b 1 < w 0 * y 0 + w 1 * y 1 := fun b hb => by
    have := hfb b hb
    linarith [hf y, hf b]
  have v1 : (![1, -1] : Fin 2 → ℝ) ∈ C.A := C.hq
  have v4 : (![-1, 1] : Fin 2 → ℝ) ∈ C.A := by simpa using C.hAsymm _ v1
  have v2 : (![1, C.hb₂] : Fin 2 → ℝ) ∈ C.A := (C.hF₂_iff C.hb₂).2 ⟨by linarith [C.hb₂_lt.1], le_rfl⟩
  have v5 : (![-1, -C.hb₂] : Fin 2 → ℝ) ∈ C.A := by simpa using C.hAsymm _ v2
  have v6 : (![C.ha₁, -1] : Fin 2 → ℝ) ∈ C.A := (C.hF₁_iff C.ha₁).2 ⟨le_rfl, by linarith [C.ha₁_lt.2]⟩
  have v3 : (![-C.ha₁, 1] : Fin 2 → ℝ) ∈ C.A := by simpa using C.hAsymm _ v6
  have b1 := hlt _ v1; have b2 := hlt _ v2; have b3 := hlt _ v3
  have b4 := hlt _ v4; have b5 := hlt _ v5; have b6 := hlt _ v6
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at b1 b2 b3 b4 b5 b6
  rw [abs_le] at hy0 hy1 hy01
  have hb₂_eq : C.hb₂ = (1 - α) / β := by field_simp; linarith
  have ha₁_eq : C.ha₁ = (β - 1) / α := by field_simp; linarith
  by_cases hw0 : 0 ≤ w 0 <;> by_cases hw1 : 0 ≤ w 1
  · by_cases hcmp : w 1 * α ≤ w 0 * β
    · have hc1 : 0 ≤ w 1 / β := div_nonneg hw1 hβ.le
      have hc2 : 0 ≤ w 0 - w 1 * α / β := by rw [sub_nonneg, div_le_iff₀ hβ]; exact hcmp
      have h1 := mul_le_mul_of_nonneg_left hy01.2 hc1
      have h2 := mul_le_mul_of_nonneg_left hy0.2 hc2
      have hid : w 0 * y 0 + w 1 * y 1 =
          (w 1 / β) * (α * y 0 + β * y 1) + (w 0 - w 1 * α / β) * y 0 := by field_simp; ring
      have hrhs : w 1 / β * 1 + (w 0 - w 1 * α / β) * 1 = w 0 * 1 + w 1 * C.hb₂ := by
        rw [hb₂_eq]; field_simp; ring
      linarith
    · push Not at hcmp
      have hc1 : 0 ≤ w 0 / α := div_nonneg hw0 hα.le
      have hc2 : 0 ≤ w 1 - w 0 * β / α := by rw [sub_nonneg, div_le_iff₀ hα]; linarith
      have h1 := mul_le_mul_of_nonneg_left hy01.2 hc1
      have h2 := mul_le_mul_of_nonneg_left hy1.2 hc2
      have hid : w 0 * y 0 + w 1 * y 1 =
          (w 0 / α) * (α * y 0 + β * y 1) + (w 1 - w 0 * β / α) * y 1 := by field_simp; ring
      have hrhs : w 0 / α * 1 + (w 1 - w 0 * β / α) * 1 = w 0 * (-C.ha₁) + w 1 * 1 := by
        rw [ha₁_eq]; field_simp; ring
      linarith
  · push Not at hw1
    nlinarith
  · push Not at hw0
    nlinarith
  · push Not at hw0 hw1
    by_cases hcmp : (-w 1) * α ≤ (-w 0) * β
    · have hc1 : 0 ≤ (-w 1) / β := div_nonneg (by linarith) hβ.le
      have hc2 : 0 ≤ (-w 0) - (-w 1) * α / β := by rw [sub_nonneg, div_le_iff₀ hβ]; exact hcmp
      have h1 := mul_le_mul_of_nonneg_left (neg_le.2 hy01.1) hc1
      have h2 := mul_le_mul_of_nonneg_left (neg_le.2 hy0.1) hc2
      have hid : w 0 * y 0 + w 1 * y 1 =
          ((-w 1) / β) * (-(α * y 0 + β * y 1)) + ((-w 0) - (-w 1) * α / β) * (-y 0) := by
        field_simp; ring
      have hrhs : (-w 1) / β * 1 + ((-w 0) - (-w 1) * α / β) * 1 = w 0 * (-1) + w 1 * (-C.hb₂) := by
        rw [hb₂_eq]; field_simp; ring
      linarith
    · push Not at hcmp
      have hc1 : 0 ≤ (-w 0) / α := div_nonneg (by linarith) hα.le
      have hc2 : 0 ≤ (-w 1) - (-w 0) * β / α := by rw [sub_nonneg, div_le_iff₀ hα]; linarith
      have h1 := mul_le_mul_of_nonneg_left (neg_le.2 hy01.1) hc1
      have h2 := mul_le_mul_of_nonneg_left (neg_le.2 hy1.1) hc2
      have hid : w 0 * y 0 + w 1 * y 1 =
          ((-w 0) / α) * (-(α * y 0 + β * y 1)) + ((-w 1) - (-w 0) * β / α) * (-y 1) := by
        field_simp; ring
      have hrhs : (-w 0) / α * 1 + ((-w 1) - (-w 0) * β / α) * 1 = w 0 * C.ha₁ + w 1 * (-1) := by
        rw [ha₁_eq]; field_simp; ring
      linarith
theorem exists_fourth_outside (h4 : HasFourPairs C.toPolyData2) (j₃ : Fin r) : ∃ k : Fin r, k ≠ C.j₁ ∧ k ≠ C.negIdx C.j₁ ∧ k ≠ C.j₂ ∧ k ≠ C.negIdx C.j₂ ∧ k ≠ j₃ ∧ k ≠ C.negIdx j₃ := by
  by_contra hall
  push Not at hall
  obtain ⟨a₀, a₁, a₂, a₃, d01, d02, d03, d12, d13, d23⟩ := h4
  have cls3 : ∀ a : Fin r, (a = C.j₁ ∨ a = C.negIdx C.j₁) ∨
      (a = C.j₂ ∨ a = C.negIdx C.j₂) ∨ (a = j₃ ∨ a = C.negIdx j₃) := fun a => by
    have := hall a; tauto
  have same_det : ∀ x y z : Fin r,
      (x = z ∨ x = C.negIdx z) → (y = z ∨ y = C.negIdx z) → det2 (C.N x) (C.N y) = 0 := by
    rintro x y z (rfl | rfl) (rfl | rfl) <;>
      simp [C.hNeg, hO, g9, it]
  rcases cls3 a₀ with c0 | c0 | c0 <;> rcases cls3 a₁ with c1 | c1 | c1 <;>
    rcases cls3 a₂ with c2 | c2 | c2 <;> rcases cls3 a₃ with c3 | c3 | c3
  all_goals first
    | exact d01 (same_det a₀ a₁ _ c0 c1)
    | exact d02 (same_det a₀ a₂ _ c0 c2)
    | exact d03 (same_det a₀ a₃ _ c0 c3)
    | exact d12 (same_det a₁ a₂ _ c1 c2)
    | exact d13 (same_det a₁ a₃ _ c1 c3)
    | exact d23 (same_det a₂ a₃ _ c2 c3)
theorem not_mem_open_subset_A {U : Set (Fin 2 → ℝ)} (hUo : IsOpen U) (hUA : U ⊆ C.A) (k : Fin r) (hmem : C.wit k ∈ U) : False := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo (C.wit k) hmem
  have hn0 := gM (C.hN0 k)
  set δ := ε / (2 * (‖C.N k‖ + 1))
  have hδ : 0 < δ := by positivity
  have hin : C.wit k + δ • C.N k ∈ C.A := hUA (hball (by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le]
    have e : δ * (‖C.N k‖ + 1) = ε / 2 := by simp [δ]; field_simp
    nlinarith [norm_nonneg (C.N k)]))
  have hle := C.toPolyData2.le_one hin k
  rw [dotProduct_add, C.hwit_eq k, dotProduct_smul, smul_eq_mul] at hle
  have hnn : C.N k ⬝ᵥ C.N k = C.N k 0 ^ 2 + C.N k 1 ^ 2 := by
    simp [dotProduct, Fin.sum_univ_two]; ring
  rw [hnn] at hle
  nlinarith
theorem exists_open_wedge (h4 : HasFourPairs C.toPolyData2) : ∃ W : Set (Fin 2 → ℝ), IsOpen W ∧ W.Nonempty ∧ W ⊆ C.Aᶜ ∧ ∀ x ∈ W, x - C.τ₁ ∈ C.A ∧ x - C.τ₂ ∈ C.A := by
  set p₁ : Fin 2 → ℝ := ![C.ha₁, -1]
  set p₂ : Fin 2 → ℝ := ![1, C.hb₂]
  have hp₁ : p₁ ∈ C.A := (C.hF₁_iff C.ha₁).2 ⟨le_rfl, C.ha₁_lt.2.le⟩
  have hp₂ : p₂ ∈ C.A := (C.hF₂_iff C.hb₂).2 ⟨C.hb₂_lt.1.le, le_rfl⟩
  have hj₀_ex : ∃ j₀ : Fin r, j₀ ≠ C.j₁ ∧ C.N j₀ ⬝ᵥ p₁ = 1 := by
    by_contra hall
    push Not at hall
    have hlt : ∀ k : Fin r, k ≠ C.j₁ → C.N k ⬝ᵥ p₁ < 1 := fun k hk =>
      lt_of_le_of_ne (C.toPolyData2.le_one hp₁ k) (hall k hk)
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ k : Fin r, k ≠ C.j₁ →
        C.N k ⬝ᵥ (![C.ha₁ - δ, -1] : Fin 2 → ℝ) < 1 := by
      rw [Filter.eventually_all]
      intro k
      by_cases hk : k = C.j₁
      · exact Eventually.of_forall fun _ hne => absurd hk hne
      · have hcont : Continuous fun δ : ℝ => C.N k ⬝ᵥ (![C.ha₁ - δ, -1] : Fin 2 → ℝ) := by
          simp [dotProduct, Fin.sum_univ_two]; fun_prop
        have ht : Tendsto (fun δ : ℝ => C.N k ⬝ᵥ (![C.ha₁ - δ, -1] : Fin 2 → ℝ)) (𝓝[>] 0)
            (𝓝 (C.N k ⬝ᵥ (![C.ha₁ - 0, -1] : Fin 2 → ℝ))) :=
          (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
        simp only [sub_zero] at ht
        filter_upwards [ht.eventually (gt_mem_nhds (hlt k hk))] with δ hδ _
        exact hδ
    obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
    have hδpos : (0 : ℝ) < δ := hδ0
    have hmem : (![C.ha₁ - δ, -1] : Fin 2 → ℝ) ∈ C.A := by
      rw [C.toPolyData2.mem_iff]
      intro k
      by_cases hk : k = C.j₁
      · subst hk; simp [C.hj₁, dotProduct, Fin.sum_univ_two]
      · exact (hδ k hk).le
    have := ((C.hF₁_iff (C.ha₁ - δ)).1 hmem).1
    linarith
  obtain ⟨j₀, hj₀_ne1, hj₀_act⟩ := hj₀_ex
  have hj₃_ex : ∃ j₃ : Fin r, j₃ ≠ C.j₂ ∧ C.N j₃ ⬝ᵥ p₂ = 1 := by
    by_contra hall
    push Not at hall
    have hlt : ∀ k : Fin r, k ≠ C.j₂ → C.N k ⬝ᵥ p₂ < 1 := fun k hk =>
      lt_of_le_of_ne (C.toPolyData2.le_one hp₂ k) (hall k hk)
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ k : Fin r, k ≠ C.j₂ →
        C.N k ⬝ᵥ (![1, C.hb₂ + δ] : Fin 2 → ℝ) < 1 := by
      rw [Filter.eventually_all]
      intro k
      by_cases hk : k = C.j₂
      · exact Eventually.of_forall fun _ hne => absurd hk hne
      · have hcont : Continuous fun δ : ℝ => C.N k ⬝ᵥ (![1, C.hb₂ + δ] : Fin 2 → ℝ) := by
          simp [dotProduct, Fin.sum_univ_two]; fun_prop
        have ht : Tendsto (fun δ : ℝ => C.N k ⬝ᵥ (![1, C.hb₂ + δ] : Fin 2 → ℝ)) (𝓝[>] 0)
            (𝓝 (C.N k ⬝ᵥ (![1, C.hb₂ + 0] : Fin 2 → ℝ))) :=
          (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
        simp only [add_zero] at ht
        filter_upwards [ht.eventually (gt_mem_nhds (hlt k hk))] with δ hδ _
        exact hδ
    obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
    have hδpos : (0 : ℝ) < δ := hδ0
    have hmem : (![1, C.hb₂ + δ] : Fin 2 → ℝ) ∈ C.A := by
      rw [C.toPolyData2.mem_iff]
      intro k
      by_cases hk : k = C.j₂
      · subst hk; simp [C.hj₂, dotProduct, Fin.sum_univ_two]
      · exact (hδ k hk).le
    have := ((C.hF₂_iff (C.hb₂ + δ)).1 hmem).2
    linarith
  obtain ⟨j₃, hj₃_ne2, hj₃_act⟩ := hj₃_ex
  have hj₁_ne2 : C.j₁ ≠ C.j₂ := fun h => by
    have := congrFun (C.hj₁.symm.trans (h ▸ C.hj₂)) 0; simp at this
  have hq_1 : C.N C.j₁ ⬝ᵥ (![1, -1] : Fin 2 → ℝ) = 1 := by simp [C.hj₁, dotProduct, Fin.sum_univ_two]
  have hq_2 : C.N C.j₂ ⬝ᵥ (![1, -1] : Fin 2 → ℝ) = 1 := by simp [C.hj₂, dotProduct, Fin.sum_univ_two]
  have hj₀_ne2 : j₀ ≠ C.j₂ := fun h => by
    rw [h, C.hj₂] at hj₀_act; simp [p₁, dotProduct, Fin.sum_univ_two] at hj₀_act; linarith [C.ha₁_lt.2]
  have hj₃_ne1 : j₃ ≠ C.j₁ := fun h => by
    rw [h, C.hj₁] at hj₃_act; simp [p₂, dotProduct, Fin.sum_univ_two] at hj₃_act; linarith [C.hb₂_lt.1]
  have hj₀_q_lt : C.N j₀ ⬝ᵥ (![1, -1] : Fin 2 → ℝ) < 1 :=
    lt_of_le_of_ne (C.toPolyData2.le_one C.hq j₀) fun h =>
      C.toPolyData2.no_three_active hq_1 hq_2 h hj₁_ne2 hj₀_ne1.symm hj₀_ne2.symm
  have hj₃_q_lt : C.N j₃ ⬝ᵥ (![1, -1] : Fin 2 → ℝ) < 1 :=
    lt_of_le_of_ne (C.toPolyData2.le_one C.hq j₃) fun h =>
      C.toPolyData2.no_three_active hq_1 hq_2 h hj₁_ne2 hj₃_ne1.symm hj₃_ne2.symm
  have hn0_0 : C.N j₀ 0 < 0 := by
    have h1 := hj₀_act; have h2 := hj₀_q_lt
    simp [p₁, dotProduct, Fin.sum_univ_two] at h1 h2
    have : C.N j₀ 0 * (1 - C.ha₁) < 0 := by linarith
    nlinarith [C.ha₁_lt.2]
  have hn0_1 : C.N j₀ 1 < 0 := by
    have h1 := hj₀_act; have hmp₂ := C.toPolyData2.le_one (C.hAsymm _ hp₂) j₀
    simp [p₁, p₂, dotProduct, Fin.sum_univ_two] at h1 hmp₂
    have : C.N j₀ 0 * (-1 - C.ha₁) + C.N j₀ 1 * (1 - C.hb₂) ≤ 0 := by linarith
    have hp : 0 < C.N j₀ 0 * (-1 - C.ha₁) := mul_pos_of_neg_of_neg hn0_0 (by linarith [C.ha₁_lt.1])
    nlinarith [C.hb₂_lt.2]
  have hn3_1 : 0 < C.N j₃ 1 := by
    have h1 := hj₃_act; have h2 := hj₃_q_lt
    simp [p₂, dotProduct, Fin.sum_univ_two] at h1 h2
    have : 0 < C.N j₃ 1 * (C.hb₂ + 1) := by linarith
    nlinarith [C.hb₂_lt.1]
  have hn3_0 : 0 < C.N j₃ 0 := by
    have h1 := hj₃_act; have hmp₁ := C.toPolyData2.le_one (C.hAsymm _ hp₁) j₃
    simp [p₁, p₂, dotProduct, Fin.sum_univ_two] at h1 hmp₁
    have : C.N j₃ 0 * (-C.ha₁ - 1) + C.N j₃ 1 * (1 - C.hb₂) ≤ 0 := by linarith
    have hp : 0 < C.N j₃ 1 * (1 - C.hb₂) := mul_pos hn3_1 (by linarith [C.hb₂_lt.2])
    nlinarith [C.ha₁_lt.1]
  set α₀ := -C.N j₀ 0
  set β₀ := -C.N j₀ 1
  set α₃ := C.N j₃ 0
  set β₃ := C.N j₃ 1
  have hα₀ : 0 < α₀ := by simp [α₀]; linarith
  have hβ₀ : 0 < β₀ := by simp [β₀]; linarith
  have hα₃ : 0 < α₃ := hn3_0
  have hβ₃ : 0 < β₃ := hn3_1
  have hj₃_not_neg0 : j₃ ≠ C.negIdx j₀ := by
    intro heq
    have hN30 : C.N j₃ = -C.N j₀ := heq ▸ C.hNeg j₀
    have eq_p₂ : α₃ + β₃ * C.hb₂ = 1 := by
      have h1 := hj₃_act; simp [p₂, dotProduct, Fin.sum_univ_two, α₃, β₃] at h1 ⊢; linarith
    have eq_p₁ : -(α₃ * C.ha₁) + β₃ = 1 := by
      have h1 : (-C.N j₀) ⬝ᵥ (-p₁) = 1 := by simp [hj₀_act]
      rw [← hN30] at h1
      simp [p₁, dotProduct, Fin.sum_univ_two, α₃, β₃] at h1 ⊢; linarith
    obtain ⟨k, hk1, hkn1, hk2, hkn2, hk3, hkn3⟩ := C.exists_fourth_outside h4 j₃
    set U := {y : Fin 2 → ℝ | |y 0| < 1 ∧ |y 1| < 1 ∧ |α₃ * y 0 + β₃ * y 1| < 1}
    have hUo : IsOpen U :=
      (isOpen_lt (continuous_apply 0).abs continuous_const).inter
        ((isOpen_lt (continuous_apply 1).abs continuous_const).inter
          (isOpen_lt (((continuous_const.mul (continuous_apply 0)).add
            (continuous_const.mul (continuous_apply 1)))).abs continuous_const))
    have hUA : U ⊆ C.A := fun y ⟨h1, h2, h3⟩ => C.hex_subset_A hα₃ hβ₃ eq_p₂ eq_p₁ h1.le h2.le h3.le
    have hwU : C.wit k ∈ U := by
      refine ⟨?_, ?_, ?_⟩
      · rw [abs_lt]
        have u := C.hwit_lt k C.j₂ hk2.symm
        have l := C.hwit_lt k (C.negIdx C.j₂) hkn2.symm
        rw [C.hNeg, neg_dotProduct] at l
        simp [C.hj₂, dotProduct, Fin.sum_univ_two] at u l
        exact ⟨by linarith, u⟩
      · rw [abs_lt]
        have l := C.hwit_lt k C.j₁ hk1.symm
        have u := C.hwit_lt k (C.negIdx C.j₁) hkn1.symm
        rw [C.hNeg, neg_dotProduct] at u
        simp [C.hj₁, dotProduct, Fin.sum_univ_two] at u l
        exact ⟨by linarith, by linarith⟩
      · rw [abs_lt]
        have u := C.hwit_lt k j₃ hk3.symm
        have l := C.hwit_lt k (C.negIdx j₃) hkn3.symm
        rw [C.hNeg, neg_dotProduct] at l
        have hd : C.N j₃ ⬝ᵥ C.wit k = α₃ * C.wit k 0 + β₃ * C.wit k 1 := by
          simp [dotProduct, Fin.sum_univ_two, α₃, β₃]
        rw [hd] at u l
        exact ⟨by linarith, u⟩
    exact C.not_mem_open_subset_A hUo hUA k hwU
  have hp₁_1 : C.N C.j₁ ⬝ᵥ p₁ = 1 := by simp [C.hj₁, p₁, dotProduct, Fin.sum_univ_two]
  have hp₂_2 : C.N C.j₂ ⬝ᵥ p₂ = 1 := by simp [C.hj₂, p₂, dotProduct, Fin.sum_univ_two]
  have hmp₁_n1 : C.N (C.negIdx C.j₁) ⬝ᵥ (-p₁) = 1 := by rw [C.hNeg, neg_dotProduct, dotProduct_neg, neg_neg, hp₁_1]
  have hmp₁_n0 : C.N (C.negIdx j₀) ⬝ᵥ (-p₁) = 1 := by rw [C.hNeg, neg_dotProduct, dotProduct_neg, neg_neg, hj₀_act]
  have hn1_ne_n0 : C.negIdx C.j₁ ≠ C.negIdx j₀ := fun h => hj₀_ne1 (by
    have := congrArg C.negIdx h; rw [C.toPolyData2.negIdx_inv, C.toPolyData2.negIdx_inv] at this; exact this.symm)
  have hj₃_ne_n1 : j₃ ≠ C.negIdx C.j₁ := fun h => by
    have : C.N j₃ 0 = 0 := by rw [h, C.hNeg, C.hj₁]; simp
    linarith
  have hn0_ne2 : C.negIdx j₀ ≠ C.j₂ := fun h => by
    have : C.N j₀ 1 = 0 := by
      have := congrArg C.negIdx h; rw [C.toPolyData2.negIdx_inv] at this
      rw [this, C.hNeg, C.hj₂]; simp
    linarith
  have ineq1 : C.N j₃ ⬝ᵥ (-p₁) < 1 :=
    lt_of_le_of_ne (C.toPolyData2.le_one (C.hAsymm _ hp₁) j₃) fun h =>
      C.toPolyData2.no_three_active hmp₁_n1 hmp₁_n0 h hn1_ne_n0 hj₃_ne_n1.symm hj₃_not_neg0.symm
  have ineq2 : C.N (C.negIdx j₀) ⬝ᵥ p₂ < 1 :=
    lt_of_le_of_ne (C.toPolyData2.le_one hp₂ (C.negIdx j₀)) fun h =>
      C.toPolyData2.no_three_active hp₂_2 hj₃_act h hj₃_ne2.symm hn0_ne2.symm hj₃_not_neg0
  have hdet_lt : α₀ * β₃ < β₀ * α₃ := by
    have e1 : α₃ * (-C.ha₁) + β₃ * 1 < 1 := by
      have h1 := ineq1; simp [p₁, dotProduct, Fin.sum_univ_two, α₃, β₃] at h1 ⊢; linarith
    have e2 : α₃ * 1 + β₃ * C.hb₂ = 1 := by
      have h1 := hj₃_act; simp [p₂, dotProduct, Fin.sum_univ_two, α₃, β₃] at h1 ⊢; linarith
    have e3 : α₀ * 1 + β₀ * C.hb₂ < 1 := by
      have h1 := ineq2; rw [C.hNeg] at h1
      simp [p₂, dotProduct, Fin.sum_univ_two, α₀, β₀] at h1 ⊢; linarith
    have e4 : α₀ * (-C.ha₁) + β₀ * 1 = 1 := by
      have h1 : (-C.N j₀) ⬝ᵥ (-p₁) = 1 := by simp [hj₀_act]
      simp [p₁, dotProduct, Fin.sum_univ_two, α₀, β₀] at h1 ⊢; linarith
    have s1 : α₀ * (1 + C.ha₁) < β₀ * (1 - C.hb₂) := by linarith
    have s2 : β₃ * (1 - C.hb₂) < α₃ * (1 + C.ha₁) := by linarith
    have pA : 0 < 1 + C.ha₁ := by linarith [C.ha₁_lt.1]
    have pB : 0 < 1 - C.hb₂ := by linarith [C.hb₂_lt.2]
    have prod_lt := mul_lt_mul'' s1 s2 (mul_pos hα₀ pA).le (mul_pos hβ₃ pB).le
    have eqL : α₀ * (1 + C.ha₁) * (β₃ * (1 - C.hb₂)) = (α₀ * β₃) * ((1 + C.ha₁) * (1 - C.hb₂)) := by ring
    have eqR : β₀ * (1 - C.hb₂) * (α₃ * (1 + C.ha₁)) = (β₀ * α₃) * ((1 + C.ha₁) * (1 - C.hb₂)) := by ring
    rw [eqL, eqR] at prod_lt
    exact lt_of_mul_lt_mul_right prod_lt (mul_pos pA pB).le
  have hslack1 : ∀ᶠ d in 𝓝 (0 : Fin 2 → ℝ), ∀ k : Fin r,
      k ≠ C.negIdx C.j₁ → k ≠ C.negIdx j₀ → C.N k ⬝ᵥ (-p₁ + d) < 1 := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k = C.negIdx C.j₁ ∨ k = C.negIdx j₀
    · exact Eventually.of_forall fun _ h1 h2 => hk.elim (fun h => absurd h h1) (fun h => absurd h h2)
    · push Not at hk
      have hlt : C.N k ⬝ᵥ (-p₁) < 1 :=
        lt_of_le_of_ne (C.toPolyData2.le_one (C.hAsymm _ hp₁) k) fun h =>
          C.toPolyData2.no_three_active hmp₁_n1 hmp₁_n0 h hn1_ne_n0 hk.1.symm hk.2.symm
      have hcont : Continuous fun d : Fin 2 → ℝ => C.N k ⬝ᵥ (-p₁ + d) :=
        (continuous_dotProduct_left' _).comp (continuous_const.add continuous_id)
      filter_upwards [(hcont.tendsto 0).eventually (by simpa using gt_mem_nhds hlt)] with d hd _ _
      exact hd
  have hmp₂_n2 : C.N (C.negIdx C.j₂) ⬝ᵥ (-p₂) = 1 := by rw [C.hNeg, neg_dotProduct, dotProduct_neg, neg_neg, hp₂_2]
  have hmp₂_n3 : C.N (C.negIdx j₃) ⬝ᵥ (-p₂) = 1 := by rw [C.hNeg, neg_dotProduct, dotProduct_neg, neg_neg, hj₃_act]
  have hn2_ne_n3 : C.negIdx C.j₂ ≠ C.negIdx j₃ := fun h => hj₃_ne2 (by
    have := congrArg C.negIdx h; rw [C.toPolyData2.negIdx_inv, C.toPolyData2.negIdx_inv] at this; exact this.symm)
  have hslack2 : ∀ᶠ d in 𝓝 (0 : Fin 2 → ℝ), ∀ k : Fin r,
      k ≠ C.negIdx C.j₂ → k ≠ C.negIdx j₃ → C.N k ⬝ᵥ (-p₂ + d) < 1 := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k = C.negIdx C.j₂ ∨ k = C.negIdx j₃
    · exact Eventually.of_forall fun _ h1 h2 => hk.elim (fun h => absurd h h1) (fun h => absurd h h2)
    · push Not at hk
      have hlt : C.N k ⬝ᵥ (-p₂) < 1 :=
        lt_of_le_of_ne (C.toPolyData2.le_one (C.hAsymm _ hp₂) k) fun h =>
          C.toPolyData2.no_three_active hmp₂_n2 hmp₂_n3 h hn2_ne_n3 hk.1.symm hk.2.symm
      have hcont : Continuous fun d : Fin 2 → ℝ => C.N k ⬝ᵥ (-p₂ + d) :=
        (continuous_dotProduct_left' _).comp (continuous_const.add continuous_id)
      filter_upwards [(hcont.tendsto 0).eventually (by simpa using gt_mem_nhds hlt)] with d hd _ _
      exact hd
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hslack1.and hslack2)
  set q : Fin 2 → ℝ := ![1, -1]
  set W : Set (Fin 2 → ℝ) := {x | dist x q < δ ∧ 0 < x 0 - 1 ∧ x 1 + 1 < 0 ∧
    α₀ * (x 0 - 1) + β₀ * (x 1 + 1) < 0 ∧ -(α₃ * (x 0 - 1)) - β₃ * (x 1 + 1) < 0}
  have hWo : IsOpen W :=
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
      ((isOpen_lt continuous_const ((continuous_apply 0).sub continuous_const)).inter
        ((isOpen_lt ((continuous_apply 1).add continuous_const) continuous_const).inter
          ((isOpen_lt ((continuous_const.mul ((continuous_apply 0).sub continuous_const)).add
            (continuous_const.mul ((continuous_apply 1).add continuous_const))) continuous_const).inter
            (isOpen_lt (((continuous_const.mul ((continuous_apply 0).sub continuous_const)).neg).sub
              (continuous_const.mul ((continuous_apply 1).add continuous_const))) continuous_const))))
  set dir : Fin 2 → ℝ := ![β₀ * α₃ + β₃ * α₀, -(2 * α₀ * α₃)]
  have hWne : W.Nonempty := by
    set t := δ / (2 * (‖dir‖ + 1))
    have ht0 : 0 < t := div_pos hδ (by positivity)
    refine ⟨q + t • dir, ?_, ?_, ?_, ?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
      have e : t * (‖dir‖ + 1) = δ / 2 := by simp [t]; field_simp
      nlinarith [norm_nonneg dir]
    · have : (q + t • dir) 0 - 1 = t * (β₀ * α₃ + β₃ * α₀) := by simp [q, dir]
      rw [this]; exact mul_pos ht0 (add_pos (mul_pos hβ₀ hα₃) (mul_pos hβ₃ hα₀))
    · have : (q + t • dir) 1 + 1 = -(t * (2 * α₀ * α₃)) := by simp [q, dir]
      rw [this]; linarith [mul_pos ht0 (mul_pos (mul_pos two_pos hα₀) hα₃)]
    · have hid : α₀ * ((q + t • dir) 0 - 1) + β₀ * ((q + t • dir) 1 + 1) =
          t * α₀ * (α₀ * β₃ - β₀ * α₃) := by simp [q, dir]; ring
      rw [hid]; exact mul_neg_of_pos_of_neg (mul_pos ht0 hα₀) (by linarith)
    · have hid : -(α₃ * ((q + t • dir) 0 - 1)) - β₃ * ((q + t • dir) 1 + 1) =
          t * α₃ * (α₀ * β₃ - β₀ * α₃) := by simp [q, dir]; ring
      rw [hid]; exact mul_neg_of_pos_of_neg (mul_pos ht0 hα₃) (by linarith)
  refine ⟨W, hWo, hWne, fun x hx hxA => ?_, fun x ⟨hdist, hx0, hx1, hw1, hw2⟩ => ?_⟩
  · have := C.le_one_0 hxA; linarith [hx.2.1]
  · set d := x - q
    have hd_dist : dist d 0 < δ := by simpa [d, dist_eq_norm] using hdist
    obtain ⟨hs1, hs2⟩ := hball hd_dist
    have eq1 : x - C.τ₁ = -p₁ + d := by
      funext i; fin_cases i <;> simp [d, q, τ₁, p₁, Matrix.vecHead, Matrix.vecTail] <;> ring
    have eq2 : x - C.τ₂ = -p₂ + d := by
      funext i; fin_cases i <;> simp [d, q, τ₂, p₂, Matrix.vecHead, Matrix.vecTail] <;> ring
    refine ⟨?_, ?_⟩
    · rw [eq1, C.toPolyData2.mem_iff]
      intro k
      by_cases hk1 : k = C.negIdx C.j₁
      · rw [hk1, C.hNeg, C.hj₁]
        simp [p₁, d, q, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]; linarith [hx1]
      by_cases hk0 : k = C.negIdx j₀
      · rw [hk0, dotProduct_add, hmp₁_n0, C.hNeg]
        have : (-C.N j₀) ⬝ᵥ d = α₀ * (x 0 - 1) + β₀ * (x 1 + 1) := by
          simp [d, q, dotProduct, Fin.sum_univ_two, α₀, β₀, Matrix.vecHead, Matrix.vecTail]; ring
        rw [this]; linarith [hw1]
      exact (hs1 k hk1 hk0).le
    · rw [eq2, C.toPolyData2.mem_iff]
      intro k
      by_cases hk2 : k = C.negIdx C.j₂
      · rw [hk2, C.hNeg, C.hj₂]
        simp [p₂, d, q, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]; linarith [hx0]
      by_cases hk3 : k = C.negIdx j₃
      · rw [hk3, dotProduct_add, hmp₂_n3, C.hNeg]
        have : (-C.N j₃) ⬝ᵥ d = -(α₃ * (x 0 - 1)) - β₃ * (x 1 + 1) := by
          simp [d, q, dotProduct, Fin.sum_univ_two, α₃, β₃, Matrix.vecHead, Matrix.vecTail]; ring
        rw [this]; linarith [hw2]
      exact (hs2 k hk2 hk3).le
theorem false_of_four_pairs (h4 : HasFourPairs C.toPolyData2) {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ C.A} = C.Aᶜ.indicator 1 x) (hμ0 : μ (interior C.A - interior C.A) = 0) : False := by
  have h1 := C.one_le_measure_τ₁ hμ hμ0
  have h2 := C.one_le_measure_τ₂ hμ hμ0
  obtain ⟨W, hWo, hWne, hWcompl, hWmem⟩ := C.exists_open_wedge h4
  obtain ⟨x, hxW, hxμ⟩ := g2 hμ hWo hWne
  rw [Set.indicator_of_mem (hWcompl hxW), Pi.one_apply] at hxμ
  have hne : C.τ₁ ≠ C.τ₂ := fun h => by
    have := congrFun h 0
    simp [τ₁, τ₂] at this
    linarith [C.ha₁_lt.2]
  have hdisj : Disjoint ({C.τ₁} : Set (Fin 2 → ℝ)) {C.τ₂} :=
    Set.disjoint_singleton.2 hne
  have hsub : ({C.τ₁} : Set (Fin 2 → ℝ)) ∪ {C.τ₂} ⊆ {t | x - t ∈ C.A} := by
    rintro t (rfl | rfl)
    · exact (hWmem x hxW).1
    · exact (hWmem x hxW).2
  have : (2 : ENNReal) ≤ 1 :=
    calc (2 : ENNReal) = 1 + 1 := by norm_num
      _ ≤ μ {C.τ₁} + μ {C.τ₂} := add_le_add h1 h2
      _ = μ ({C.τ₁} ∪ {C.τ₂}) := (measure_union hdisj (measurableSet_singleton _)).symm
      _ ≤ μ {t | x - t ∈ C.A} := measure_mono hsub
      _ = 1 := hxμ
  norm_num at this
end NormCorner2
theorem PolyData2.exists_bot_normal {r : ℕ} (D : PolyData2 r) (h4 : HasFourPairs D) {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ D.A} = D.Aᶜ.indicator 1 x) (hμ0 : μ (interior D.A - interior D.A) = 0) : ∃ (D₁ : PolyData2 r) (j₁ : Fin r) (μ₁ : Measure (Fin 2 → ℝ)), IsFiniteMeasureOnCompacts μ₁ ∧ HasFourPairs D₁ ∧ D₁.N j₁ = ![0, -1] ∧ (∀ᵐ x, μ₁ {s | x - s ∈ D₁.A} = D₁.Aᶜ.indicator 1 x) ∧ μ₁ (interior D₁.A - interior D₁.A) = 0 := by
  have h4' := h4
  rcases h4' with ⟨j₁, _, _, _, _, _, _, _, _, _⟩
  set M₁ := rows2 (perp2 (D.N j₁)) (-D.N j₁)
  have hM₁d : M₁.det = D.N j₁ 0 ^ 2 + D.N j₁ 1 ^ 2 := by
    rw [ia]; simp [perp2, det2]; ring
  have hM₁u : IsUnit M₁.det := isUnit_iff_ne_zero.2 (hM₁d ▸ (gM (D.hN0 j₁)).ne')
  set S₁ := M₁⁻¹
  have hS₁u : IsUnit S₁.det := by
    rw [isUnit_iff_ne_zero, det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hM₁u.ne_zero
  have hN₁ : (D.map S₁ hS₁u).N j₁ = ![0, -1] := by
    show S₁ᵀ *ᵥ D.N j₁ = ![0, -1]
    have hM₁t : M₁ᵀ *ᵥ (![0, -1] : Fin 2 → ℝ) = D.N j₁ := by
      rw [h9]; simp
    have hd : IsUnit M₁ᵀ.det := by rw [det_transpose]; exact hM₁u
    calc S₁ᵀ *ᵥ D.N j₁ = (M₁ᵀ)⁻¹ *ᵥ (M₁ᵀ *ᵥ ![0, -1]) := by rw [transpose_nonsing_inv, hM₁t]
      _ = ![0, -1] := by rw [mulVec_mulVec, nonsing_inv_mul _ hd, one_mulVec]
  exact ⟨D.map S₁ hS₁u, j₁, μ.map (affEquiv S₁ hS₁u 0).symm,
    gS hS₁u (μ := μ),
    D.hasFourPairs_map S₁ hS₁u h4, hN₁,
    gR hS₁u hμ, gT hS₁u hμ0⟩
theorem PolyData2.exists_adj_normals {r : ℕ} (D₁ : PolyData2 r) (j₁ : Fin r) (h4_1 : HasFourPairs D₁) (hN₁ : D₁.N j₁ = ![0, -1]) {μ₁ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ₁] (hμ₁ : ∀ᵐ x, μ₁ {s | x - s ∈ D₁.A} = D₁.Aᶜ.indicator 1 x) (hμ0_1 : μ₁ (interior D₁.A - interior D₁.A) = 0) : ∃ (D₂ : PolyData2 r) (j₂ : Fin r) (μ₂ : Measure (Fin 2 → ℝ)), IsFiniteMeasureOnCompacts μ₂ ∧ HasFourPairs D₂ ∧ j₂ ≠ j₁ ∧ D₂.N j₁ = ![0, -1] ∧ D₂.N j₂ = ![1, 0] ∧ (![1, -1] : Fin 2 → ℝ) ∈ D₂.A ∧ (∀ᵐ x, μ₂ {s | x - s ∈ D₂.A} = D₂.Aᶜ.indicator 1 x) ∧ μ₂ (interior D₂.A - interior D₂.A) = 0 := by
  set I₁ : Set ℝ := {u | (![u, -1] : Fin 2 → ℝ) ∈ D₁.A}
  have hI₁c : IsCompact I₁ := by
    obtain ⟨R, hR⟩ := D₁.hAc.isBounded.subset_closedBall 0
    refine Metric.isCompact_of_isClosed_isBounded
      (D₁.hAc.isClosed.preimage (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := R)).subset fun u hu => ?_
    have hb := hR hu
    rw [mem_closedBall, dist_zero_right] at hb ⊢
    exact (norm_le_pi_norm (![u, -1] : Fin 2 → ℝ) 0).trans hb
  have hw₁_1 : D₁.wit j₁ 1 = -1 := by
    have := D₁.hwit_eq j₁
    rw [hN₁] at this
    simp [dotProduct, Fin.sum_univ_two] at this
    linarith
  have hw₁_mem : D₁.wit j₁ 0 ∈ I₁ := by
    show (![D₁.wit j₁ 0, -1] : Fin 2 → ℝ) ∈ D₁.A
    have : (![D₁.wit j₁ 0, -1] : Fin 2 → ℝ) = D₁.wit j₁ := by funext i; fin_cases i <;> simp [hw₁_1]
    rw [this]; exact D₁.hwit_mem j₁
  set b₁ := sSup I₁
  have hb₁_mem : (![b₁, -1] : Fin 2 → ℝ) ∈ D₁.A := hI₁c.sSup_mem ⟨_, hw₁_mem⟩
  have hw₁_lt_b₁ : D₁.wit j₁ 0 < b₁ := by
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ k : Fin r, k ≠ j₁ →
        D₁.N k ⬝ᵥ (![D₁.wit j₁ 0 + δ, -1] : Fin 2 → ℝ) < 1 := by
      rw [Filter.eventually_all]
      intro k
      by_cases hk : k = j₁
      · exact Eventually.of_forall fun _ hne => absurd hk hne
      · have hcont : Continuous fun δ : ℝ => D₁.N k ⬝ᵥ (![D₁.wit j₁ 0 + δ, -1] : Fin 2 → ℝ) := by
          simp [dotProduct, Fin.sum_univ_two]; fun_prop
        have ht : Tendsto (fun δ : ℝ => D₁.N k ⬝ᵥ (![D₁.wit j₁ 0 + δ, -1] : Fin 2 → ℝ)) (𝓝[>] 0)
            (𝓝 (D₁.N k ⬝ᵥ (![D₁.wit j₁ 0 + 0, -1] : Fin 2 → ℝ))) :=
          (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
        have h0 : (![D₁.wit j₁ 0 + 0, -1] : Fin 2 → ℝ) = D₁.wit j₁ := by
          funext i; fin_cases i <;> simp [hw₁_1]
        rw [h0] at ht
        filter_upwards [ht.eventually (gt_mem_nhds (D₁.hwit_lt j₁ k hk))] with δ hδ _
        exact hδ
    obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
    have hδpos : (0 : ℝ) < δ := hδ0
    have hin : D₁.wit j₁ 0 + δ ∈ I₁ := by
      show (![D₁.wit j₁ 0 + δ, -1] : Fin 2 → ℝ) ∈ D₁.A
      rw [D₁.mem_iff]
      intro k
      by_cases hk : k = j₁
      · subst hk; simp [hN₁, dotProduct, Fin.sum_univ_two]
      · exact (hδ k hk).le
    have hle := le_csSup hI₁c.bddAbove hin
    linarith
  have hj₂_ex : ∃ j₂ : Fin r, j₂ ≠ j₁ ∧ D₁.N j₂ ⬝ᵥ (![b₁, -1] : Fin 2 → ℝ) = 1 := by
    by_contra hall
    push Not at hall
    have hlt : ∀ k : Fin r, k ≠ j₁ → D₁.N k ⬝ᵥ (![b₁, -1] : Fin 2 → ℝ) < 1 := fun k hk =>
      lt_of_le_of_ne (D₁.le_one hb₁_mem k) (hall k hk)
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ k : Fin r, k ≠ j₁ →
        D₁.N k ⬝ᵥ (![b₁ + δ, -1] : Fin 2 → ℝ) < 1 := by
      rw [Filter.eventually_all]
      intro k
      by_cases hk : k = j₁
      · exact Eventually.of_forall fun _ hne => absurd hk hne
      · have hcont : Continuous fun δ : ℝ => D₁.N k ⬝ᵥ (![b₁ + δ, -1] : Fin 2 → ℝ) := by
          simp [dotProduct, Fin.sum_univ_two]; fun_prop
        have ht : Tendsto (fun δ : ℝ => D₁.N k ⬝ᵥ (![b₁ + δ, -1] : Fin 2 → ℝ)) (𝓝[>] 0)
            (𝓝 (D₁.N k ⬝ᵥ (![b₁ + 0, -1] : Fin 2 → ℝ))) :=
          (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
        simp only [add_zero] at ht
        filter_upwards [ht.eventually (gt_mem_nhds (hlt k hk))] with δ hδ _
        exact hδ
    obtain ⟨δ, hδ, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
    have hδpos : (0 : ℝ) < δ := hδ0
    have hin : b₁ + δ ∈ I₁ := by
      show (![b₁ + δ, -1] : Fin 2 → ℝ) ∈ D₁.A
      rw [D₁.mem_iff]
      intro k
      by_cases hk : k = j₁
      · subst hk; simp [hN₁, dotProduct, Fin.sum_univ_two]
      · exact (hδ k hk).le
    have hle := le_csSup hI₁c.bddAbove hin
    linarith
  obtain ⟨j₂, hj₂_ne1, hj₂_act⟩ := hj₂_ex
  have hn2_0_pos : 0 < D₁.N j₂ 0 := by
    have hlt := D₁.hwit_lt j₁ j₂ hj₂_ne1
    have hw_eq : (![D₁.wit j₁ 0, -1] : Fin 2 → ℝ) = D₁.wit j₁ := by
      funext i; fin_cases i <;> simp [hw₁_1]
    rw [← hw_eq] at hlt
    have h2 := hj₂_act
    simp [dotProduct, Fin.sum_univ_two] at hlt h2
    have : 0 < D₁.N j₂ 0 * (b₁ - D₁.wit j₁ 0) := by linarith
    nlinarith
  set M₂ := rows2 (D₁.N j₂) ![0, 1]
  have hM₂d : M₂.det = D₁.N j₂ 0 := by rw [ia]; simp [det2]
  have hM₂u : IsUnit M₂.det := isUnit_iff_ne_zero.2 (hM₂d ▸ hn2_0_pos.ne')
  set S₂ := M₂⁻¹
  have hS₂u : IsUnit S₂.det := by
    rw [isUnit_iff_ne_zero, det_nonsing_inv, Ring.inverse_eq_inv']
    exact inv_ne_zero hM₂u.ne_zero
  have hd2t : IsUnit M₂ᵀ.det := by rw [det_transpose]; exact hM₂u
  have hN₂_1 : (D₁.map S₂ hS₂u).N j₁ = ![0, -1] := by
    show S₂ᵀ *ᵥ D₁.N j₁ = ![0, -1]
    have hM₂t : M₂ᵀ *ᵥ (![0, -1] : Fin 2 → ℝ) = D₁.N j₁ := by
      rw [h9, hN₁]; simp
    calc S₂ᵀ *ᵥ D₁.N j₁ = (M₂ᵀ)⁻¹ *ᵥ (M₂ᵀ *ᵥ ![0, -1]) := by rw [transpose_nonsing_inv, hM₂t]
      _ = ![0, -1] := by rw [mulVec_mulVec, nonsing_inv_mul _ hd2t, one_mulVec]
  have hN₂_2 : (D₁.map S₂ hS₂u).N j₂ = ![1, 0] := by
    show S₂ᵀ *ᵥ D₁.N j₂ = ![1, 0]
    have hM₂t : M₂ᵀ *ᵥ (![1, 0] : Fin 2 → ℝ) = D₁.N j₂ := by
      rw [h9]; simp
    calc S₂ᵀ *ᵥ D₁.N j₂ = (M₂ᵀ)⁻¹ *ᵥ (M₂ᵀ *ᵥ ![1, 0]) := by rw [transpose_nonsing_inv, hM₂t]
      _ = ![1, 0] := by rw [mulVec_mulVec, nonsing_inv_mul _ hd2t, one_mulVec]
  have hq₂ : (![1, -1] : Fin 2 → ℝ) ∈ (D₁.map S₂ hS₂u).A := by
    simp only [PolyData2.map, Set.mem_preimage, affEquiv_apply, add_zero]
    have hM₂q : M₂ *ᵥ (![b₁, -1] : Fin 2 → ℝ) = ![1, -1] := by
      rw [h8, hj₂_act]; simp [dotProduct, Fin.sum_univ_two]
    have : S₂ *ᵥ (![1, -1] : Fin 2 → ℝ) = ![b₁, -1] := by
      rw [← hM₂q, mulVec_mulVec, nonsing_inv_mul M₂ hM₂u, one_mulVec]
    rw [this]; exact hb₁_mem
  exact ⟨D₁.map S₂ hS₂u, j₂, μ₁.map (affEquiv S₂ hS₂u 0).symm,
    gS hS₂u (μ := μ₁),
    D₁.hasFourPairs_map S₂ hS₂u h4_1, hj₂_ne1, hN₂_1, hN₂_2, hq₂,
    gR hS₂u hμ₁, gT hS₂u hμ0_1⟩
theorem PolyData2.false_of_hasFourPairs {r : ℕ} (D : PolyData2 r) (h4 : HasFourPairs D) {μ : Measure (Fin 2 → ℝ)} [IsFiniteMeasureOnCompacts μ] (hμ : ∀ᵐ x, μ {s | x - s ∈ D.A} = D.Aᶜ.indicator 1 x) (hμ0 : μ (interior D.A - interior D.A) = 0) : False := by
  obtain ⟨D₁, j₁, μ₁, hμ₁c, h4_1, hN₁, hμ₁, hμ0_1⟩ := D.exists_bot_normal h4 hμ hμ0
  haveI := hμ₁c
  obtain ⟨D₂, j₂, μ₂, hμ₂c, h4_2, hj₂_ne1, hN₂_1, hN₂_2, hq₂, hμ₂, hμ0_2⟩ :=
    D₁.exists_adj_normals j₁ h4_1 hN₁ hμ₁ hμ0_1
  haveI := hμ₂c
  set J₁ : Set ℝ := {u | (![u, -1] : Fin 2 → ℝ) ∈ D₂.A}
  set J₂ : Set ℝ := {v | (![1, v] : Fin 2 → ℝ) ∈ D₂.A}
  have hJ₁c : IsCompact J₁ := by
    obtain ⟨R, hR⟩ := D₂.hAc.isBounded.subset_closedBall 0
    refine Metric.isCompact_of_isClosed_isBounded
      (D₂.hAc.isClosed.preimage (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := R)).subset fun u hu => ?_
    have hb := hR hu
    rw [mem_closedBall, dist_zero_right] at hb ⊢
    exact (norm_le_pi_norm (![u, -1] : Fin 2 → ℝ) 0).trans hb
  have hJ₂c : IsCompact J₂ := by
    obtain ⟨R, hR⟩ := D₂.hAc.isBounded.subset_closedBall 0
    refine Metric.isCompact_of_isClosed_isBounded
      (D₂.hAc.isClosed.preimage (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := R)).subset fun v hv => ?_
    have hb := hR hv
    rw [mem_closedBall, dist_zero_right] at hb ⊢
    exact (norm_le_pi_norm (![1, v] : Fin 2 → ℝ) 1).trans hb
  have hJ₁conv : Convex ℝ J₁ := fun u₁ hu₁ u₂ hu₂ a b ha hb hab => by
    have := D₂.hAconv hu₁ hu₂ ha hb hab
    show (![a * u₁ + b * u₂, -1] : Fin 2 → ℝ) ∈ D₂.A
    convert this using 1
    funext i; fin_cases i <;> simp
    linarith
  have hJ₂conv : Convex ℝ J₂ := fun v₁ hv₁ v₂ hv₂ a b ha hb hab => by
    have := D₂.hAconv hv₁ hv₂ ha hb hab
    show (![1, a * v₁ + b * v₂] : Fin 2 → ℝ) ∈ D₂.A
    convert this using 1
    funext i; fin_cases i <;> simp
    linarith
  set a₁ := sInf J₁
  set b₂ := sSup J₂
  have ha₁_mem : a₁ ∈ J₁ := hJ₁c.sInf_mem ⟨1, hq₂⟩
  have hb₂_mem : b₂ ∈ J₂ := hJ₂c.sSup_mem ⟨-1, hq₂⟩
  have hJ₁_eq : J₁ = Icc a₁ 1 := by
    refine Subset.antisymm (fun u hu => ⟨csInf_le hJ₁c.bddBelow hu, ?_⟩)
      ((convex_iff_ordConnected.1 hJ₁conv).out ha₁_mem hq₂)
    have := D₂.le_one hu j₂
    simpa [hN₂_2, dotProduct, Fin.sum_univ_two] using this
  have hJ₂_eq : J₂ = Icc (-1) b₂ := by
    refine Subset.antisymm (fun v hv => ⟨?_, le_csSup hJ₂c.bddAbove hv⟩)
      ((convex_iff_ordConnected.1 hJ₂conv).out hq₂ hb₂_mem)
    have := D₂.le_one hv j₁
    simp [hN₂_1, dotProduct, Fin.sum_univ_two] at this; linarith
  have ha₁_lt1 : a₁ < 1 := by
    have hw_1 : D₂.wit j₁ 1 = -1 := by
      have := D₂.hwit_eq j₁; rw [hN₂_1] at this; simp [dotProduct, Fin.sum_univ_two] at this; linarith
    have hw_lt : D₂.wit j₁ 0 < 1 := by
      have := D₂.hwit_lt j₁ j₂ hj₂_ne1
      simpa [hN₂_2, dotProduct, Fin.sum_univ_two] using this
    have hwJ : D₂.wit j₁ 0 ∈ J₁ := by
      show (![D₂.wit j₁ 0, -1] : Fin 2 → ℝ) ∈ D₂.A
      have : (![D₂.wit j₁ 0, -1] : Fin 2 → ℝ) = D₂.wit j₁ := by funext i; fin_cases i <;> simp [hw_1]
      rw [this]; exact D₂.hwit_mem j₁
    exact (csInf_le hJ₁c.bddBelow hwJ).trans_lt hw_lt
  have hb₂_gt : -1 < b₂ := by
    have hw_0 : D₂.wit j₂ 0 = 1 := by
      have := D₂.hwit_eq j₂; rw [hN₂_2] at this; simpa [dotProduct, Fin.sum_univ_two] using this
    have hw_gt : -1 < D₂.wit j₂ 1 := by
      have := D₂.hwit_lt j₂ j₁ hj₂_ne1.symm
      simp [hN₂_1, dotProduct, Fin.sum_univ_two] at this; linarith
    have hwJ : D₂.wit j₂ 1 ∈ J₂ := by
      show (![1, D₂.wit j₂ 1] : Fin 2 → ℝ) ∈ D₂.A
      have : (![1, D₂.wit j₂ 1] : Fin 2 → ℝ) = D₂.wit j₂ := by funext i; fin_cases i <;> simp [hw_0]
      rw [this]; exact D₂.hwit_mem j₂
    exact hw_gt.trans_le (le_csSup hJ₂c.bddAbove hwJ)
  have not_corner : (![1, 1] : Fin 2 → ℝ) ∉ D₂.A := by
    intro h11
    have hm11 : (![-1, -1] : Fin 2 → ℝ) ∈ D₂.A := by simpa using D₂.hAsymm _ h11
    have hm1p1 : (![-1, 1] : Fin 2 → ℝ) ∈ D₂.A := by simpa using D₂.hAsymm _ hq₂
    have hbox_sub : ∀ y : Fin 2 → ℝ, |y 0| ≤ 1 → |y 1| ≤ 1 → y ∈ D₂.A := by
      intro y hy0 hy1
      rw [abs_le] at hy0 hy1
      set s := (1 + y 0) / 2
      set t := (1 + y 1) / 2
      have hs0 : 0 ≤ s := by simp [s]; linarith
      have hs1 : 0 ≤ 1 - s := by simp [s]; linarith
      have ht0 : 0 ≤ t := by simp [t]; linarith
      have ht1 : 0 ≤ 1 - t := by simp [t]; linarith
      have bot_mem := D₂.hAconv hq₂ hm11 hs0 hs1 (by ring)
      have top_mem := D₂.hAconv h11 hm1p1 hs0 hs1 (by ring)
      have all_mem := D₂.hAconv top_mem bot_mem ht0 ht1 (by ring)
      convert all_mem using 1
      funext i; fin_cases i <;> simp [s, t] <;> ring
    obtain ⟨a₀, a₁', a₂, a₃, d01, d02, d03, d12, d13, d23⟩ := h4_2
    have hex_out : ∃ k : Fin r, k ≠ j₁ ∧ k ≠ D₂.negIdx j₁ ∧ k ≠ j₂ ∧ k ≠ D₂.negIdx j₂ := by
      by_contra hall
      push Not at hall
      have cls2 : ∀ a : Fin r, (a = j₁ ∨ a = D₂.negIdx j₁) ∨ (a = j₂ ∨ a = D₂.negIdx j₂) :=
        fun a => by have := hall a; tauto
      have same_det : ∀ x y z : Fin r,
          (x = z ∨ x = D₂.negIdx z) → (y = z ∨ y = D₂.negIdx z) → det2 (D₂.N x) (D₂.N y) = 0 := by
        rintro x y z (rfl | rfl) (rfl | rfl) <;>
          simp [D₂.hNeg, hO, g9, it]
      rcases cls2 a₀ with c0 | c0 <;> rcases cls2 a₁' with c1 | c1 <;> rcases cls2 a₂ with c2 | c2
      all_goals first
        | exact d01 (same_det a₀ a₁' _ c0 c1)
        | exact d02 (same_det a₀ a₂ _ c0 c2)
        | exact d12 (same_det a₁' a₂ _ c1 c2)
    obtain ⟨k, hk1, hkn1, hk2, hkn2⟩ := hex_out
    set U := {y : Fin 2 → ℝ | |y 0| < 1 ∧ |y 1| < 1}
    have hUo : IsOpen U :=
      (isOpen_lt (continuous_apply 0).abs continuous_const).inter
        (isOpen_lt (continuous_apply 1).abs continuous_const)
    have hwU : D₂.wit k ∈ U := by
      refine ⟨?_, ?_⟩
      · rw [abs_lt]
        have u := D₂.hwit_lt k j₂ hk2.symm
        have l := D₂.hwit_lt k (D₂.negIdx j₂) hkn2.symm
        rw [D₂.hNeg, neg_dotProduct] at l
        simp [hN₂_2, dotProduct, Fin.sum_univ_two] at u l
        exact ⟨by linarith, u⟩
      · rw [abs_lt]
        have l := D₂.hwit_lt k j₁ hk1.symm
        have u := D₂.hwit_lt k (D₂.negIdx j₁) hkn1.symm
        rw [D₂.hNeg, neg_dotProduct] at u
        simp [hN₂_1, dotProduct, Fin.sum_univ_two] at u l
        exact ⟨by linarith, by linarith⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUo (D₂.wit k) hwU
    have hn0 := gM (D₂.hN0 k)
    set δ := ε / (2 * (‖D₂.N k‖ + 1))
    have hδ : 0 < δ := by positivity
    have hin : D₂.wit k + δ • D₂.N k ∈ D₂.A := by
      have hbu : D₂.wit k + δ • D₂.N k ∈ U := hball (by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hδ.le]
        have e : δ * (‖D₂.N k‖ + 1) = ε / 2 := by simp [δ]; field_simp
        nlinarith [norm_nonneg (D₂.N k)])
      exact hbox_sub _ hbu.1.le hbu.2.le
    have hle := D₂.le_one hin k
    rw [dotProduct_add, D₂.hwit_eq k, dotProduct_smul, smul_eq_mul] at hle
    have hnn : D₂.N k ⬝ᵥ D₂.N k = D₂.N k 0 ^ 2 + D₂.N k 1 ^ 2 := by
      simp [dotProduct, Fin.sum_univ_two]; ring
    rw [hnn] at hle
    nlinarith
  have ha₁_gt : -1 < a₁ := by
    have hge : -1 ≤ a₁ := by
      have := D₂.neg_one_le ha₁_mem j₂
      simpa [hN₂_2, dotProduct, Fin.sum_univ_two] using this
    refine lt_of_le_of_ne hge fun heq => not_corner ?_
    have hm11 : (![-1, -1] : Fin 2 → ℝ) ∈ D₂.A := by
      have hmem : (![a₁, -1] : Fin 2 → ℝ) ∈ D₂.A := ha₁_mem
      rwa [← heq] at hmem
    simpa using D₂.hAsymm _ hm11
  have hb₂_lt1 : b₂ < 1 := by
    have hle : b₂ ≤ 1 := by
      have := D₂.neg_one_le hb₂_mem j₁
      simp [hN₂_1, dotProduct, Fin.sum_univ_two] at this; linarith
    refine lt_of_le_of_ne hle fun heq => not_corner ?_
    have hmem : (![1, b₂] : Fin 2 → ℝ) ∈ D₂.A := hb₂_mem
    rwa [heq] at hmem
  let NC : NormCorner2 r :=
    { toPolyData2 := D₂
      j₁ := j₁
      j₂ := j₂
      hj₁ := hN₂_1
      hj₂ := hN₂_2
      hq := hq₂
      ha₁ := a₁
      hb₂ := b₂
      ha₁_lt := ⟨ha₁_gt, ha₁_lt1⟩
      hb₂_lt := ⟨hb₂_gt, hb₂_lt1⟩
      hF₁_iff := fun u => by change u ∈ J₁ ↔ u ∈ Icc a₁ 1; rw [hJ₁_eq]
      hF₂_iff := fun v => by change v ∈ J₂ ↔ v ∈ Icc (-1) b₂; rw [hJ₂_eq] }
  exact NC.false_of_four_pairs h4_2 hμ₂ hμ0_2
end Exclusion2D
theorem g5 {A : Set (Fin 2 → ℝ)} (hA : IsCB A) : RightSpectral2 A := by
  intro m B hBm hBb hspec
  obtain ⟨c, hc⟩ := centrallySymmetric_of_isSpectral_productSet (k := 1) hA hBm hBb hspec
  set A₀ : Set (Fin 2 → ℝ) := {y | y + (1 / 2 : ℝ) • c ∈ A}
  have hspec₀ := gI ((1 / 2 : ℝ) • c) hspec
  have hA₀ : IsCB A₀ := by
    have hpre : A₀ = (Homeomorph.addRight ((1 / 2 : ℝ) • c)) ⁻¹' A := rfl
    refine ⟨hA.convex.translate_preimage_left _, ?_, ?_⟩
    · rw [hpre]; exact (Homeomorph.addRight _).isCompact_preimage.2 hA.compact
    · rw [hpre, ← Homeomorph.preimage_interior]
      obtain ⟨x, hx⟩ := hA.interior_nonempty
      exact ⟨x - (1 / 2 : ℝ) • c, by simpa using hx⟩
  have hsymm₀ : ∀ x ∈ A₀, -x ∈ A₀ := fun x hx => by
    have := hc _ hx
    show -x + (1 / 2 : ℝ) • c ∈ A
    convert this using 1
    funext i; simp; ring
  have hA₀m : MeasurableSet A₀ := hA₀.compact.isClosed.measurableSet
  have hA₀b : Bornology.IsBounded A₀ := hA₀.compact.isBounded
  obtain ⟨μ, hμc, hμ⟩ := exists_weakTiling_left_of_isSpectral_productSet hA₀m hA₀b hBm hBb hspec₀
  haveI := hμc
  have hμ0 := measure_diff_eq_zero hA₀ hμ
  obtain ⟨r, D, hDA⟩ := gY hA₀ hsymm₀ hμ
  have hn4 : ¬ HasFourPairs D := fun h4 => D.false_of_hasFourPairs h4 (hDA.symm ▸ hμ) (hDA.symm ▸ hμ0)
  have hRS := D.rightSpectral_of_not_four hn4
  rw [hDA] at hRS
  exact hRS m B hBm hBb hspec₀
end FCBridge
end
theorem OMA.solution : type_of% @SpectralSetProduct.isSpectral_right_of_product_two_dimensional := by
  intro m _ A B hA hBb hBm hspec
  exact FCBridge.g5 ⟨A.convex, A.isCompact, hA⟩ m B hBm hBb hspec
