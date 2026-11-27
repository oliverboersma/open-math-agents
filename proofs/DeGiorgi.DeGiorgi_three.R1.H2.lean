import OMAReductions.R_DeGiorgi_DeGiorgi_three_R1

/-!
# Weak equation for the derivative quotient

Credit: ported verbatim to dimension three (and to an arbitrary direction `i`) from the merged
proof of DeGiorgi.DeGiorgi_two.R1.H2 by @dk8827 (PR #1380).

Integrate the translated Allen--Cahn equation against a compactly supported test
function and differentiate the resulting identity in the translation parameter.
The two weak equations for the directional derivatives have the same zeroth-order
coefficient, which cancels in the quotient equation of Ghoussoub and Gui (1998).
-/

namespace OMA.DeGiorgiWeak3

open EuclideanGeometry InnerProductSpace MeasureTheory Filter Set Finset
open scoped Gradient Laplacian Topology

private abbrev Plane := ℝ^3

private noncomputable def partialDerivative (u : Plane → ℝ) (e : Plane) (x : Plane) : ℝ :=
  fderiv ℝ u x e

private theorem partial_continuous {u : Plane → ℝ} (h : ContDiff ℝ 1 u) (e : Plane) :
    Continuous (partialDerivative u e) :=
  (h.continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem partial_contDiff {u : Plane → ℝ} (h : ContDiff ℝ 2 u) (e : Plane) :
    ContDiff ℝ 1 (partialDerivative u e) :=
  (h.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem partial_compact {u : Plane → ℝ} (h : HasCompactSupport u) (e : Plane) :
    HasCompactSupport (partialDerivative u e) :=
  h.fderiv_apply ℝ e

private theorem integrate_compact_mul {a b : Plane → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hs : HasCompactSupport a) :
    Integrable (fun x => a x * b x) :=
  (ha.mul hb).integrable_of_hasCompactSupport (hs.mul_right (f' := b))

private theorem translated_deriv {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (x e : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • e)) (partialDerivative f e (x + t • e)) t := by
  exact (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const e).const_add x))

private theorem shifted_integral_deriv {a f : Plane → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a) (hf : ContDiff ℝ 1 f) (e : Plane) :
    HasDerivAt (fun t : ℝ => ∫ x, a x * f (x + t • e))
      (∫ x, a x * partialDerivative f e x) 0 := by
  let F := fun (t : ℝ) (x : Plane) => a x * f (x + t • e)
  let D := fun (t : ℝ) (x : Plane) => a x * partialDerivative f e (x + t • e)
  let S := tsupport a
  let T : Set ℝ := Set.Icc (-1) 1
  have hT : T ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hS : MeasurableSet S := (isClosed_tsupport a).measurableSet
  have hjoint : Continuous (fun p : ℝ × Plane => D p.1 p.2) :=
    (ha.comp continuous_snd).mul
      ((partial_continuous hf e).comp (continuous_snd.add (continuous_fst.smul continuous_const)))
  have hTC : IsCompact T := isCompact_Icc
  obtain ⟨M, hM⟩ := (hTC.prod hc).exists_bound_of_continuousOn hjoint.continuousOn
  let bound := S.indicator fun _ => M
  have hBound : Integrable bound :=
    (integrableOn_const (μ := volume) (C := M)
      (hs := hc.measure_lt_top.ne)).integrable_indicator hS
  have hDom : ∀ᵐ x : Plane ∂volume, ∀ t ∈ T, ‖D t x‖ ≤ bound x := by
    refine ae_of_all _ fun x t ht => ?_
    by_cases hx : x ∈ S
    · rw [show bound x = M from indicator_of_mem hx _]
      exact hM (t, x) ⟨ht, hx⟩
    · have he : a x = 0 := by
        by_contra h
        exact hx (subset_closure h)
      rw [show bound x = 0 from indicator_of_notMem hx _]
      simp [D, he]
  have hF (t : ℝ) : Continuous (F t) :=
    ha.mul (hf.continuous.comp (continuous_id.add continuous_const))
  have hD (t : ℝ) : Continuous (D t) :=
    ha.mul ((partial_continuous hf e).comp (continuous_id.add continuous_const))
  have hFint : Integrable (F 0) := integrate_compact_mul ha
    (hf.continuous.comp (continuous_id.add continuous_const)) hc
  have hd (x : Plane) (t : ℝ) : HasDerivAt (F · x) (D t x) t :=
    (translated_deriv hf x e t).const_mul _
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hT
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable) hFint
    (hD 0).aestronglyMeasurable hDom hBound
    (ae_of_all _ fun x t _ => hd x t)).2
  simpa only [F, D, zero_smul, add_zero] using h

private theorem derivative_of_partial {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (e d x : Plane) :
    partialDerivative (partialDerivative u e) d x =
      (fderiv ℝ (fderiv ℝ u) x d) e := by
  have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  unfold partialDerivative
  rw [fderiv_clm_apply (hF.differentiable one_ne_zero x) (differentiableAt_const e)]
  simp

private theorem partial_comm {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (x e d : Plane) :
    partialDerivative (partialDerivative u e) d x =
      partialDerivative (partialDerivative u d) e x := by
  rw [derivative_of_partial hu, derivative_of_partial hu]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)) d e

private theorem laplacian_as_partials {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (b : OrthonormalBasis (Fin 3) ℝ Plane) (x : Plane) :
    (Δ u) x = ∑ i, partialDerivative (partialDerivative u (b i)) (b i) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  exact sum_congr rfl fun i _ => by
    rw [iteratedFDeriv_two_apply, derivative_of_partial hu]
    simp

private theorem inner_gradient_as_partials (u v : Plane → ℝ)
    (b : OrthonormalBasis (Fin 3) ℝ Plane) (x : Plane) :
    inner ℝ (∇ u x) (∇ v x) =
      ∑ i, partialDerivative u (b i) x * partialDerivative v (b i) x := by
  rw [← b.sum_inner_mul_inner]
  apply sum_congr rfl
  intro i _
  have h (f : Plane → ℝ) : inner ℝ (∇ f x) (b i) = partialDerivative f (b i) x := by
    rw [← toDual_apply_apply, toDual_gradient]
    rfl
  rw [h u, real_inner_comm (∇ v x) (b i), h v]

private theorem shifted_partial {g : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (s d x : Plane) :
    partialDerivative (fun y => g (y + s)) d x = partialDerivative g d (x + s) := by
  have hh := ((hg.differentiable one_ne_zero (x + s)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const s)).fderiv
  change fderiv ℝ (fun y : Plane => g (y + s)) x =
    (fderiv ℝ g (x + s)).comp (ContinuousLinearMap.id ℝ Plane) at hh
  rw [ContinuousLinearMap.comp_id] at hh
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L d) hh

private theorem integrate_shifted_by_parts {g η : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (s e : Plane) :
    (∫ x, partialDerivative η e x * g (x + s)) =
      -∫ x, η x * partialDerivative g e (x + s) := by
  let g' := fun x => g (x + s)
  have hg' : ContDiff ℝ 1 g' := hg.comp (contDiff_id.add contDiff_const)
  have h1 := integrate_compact_mul hη.continuous (partial_continuous hg' e) hηc
  have h2 := integrate_compact_mul (partial_continuous hη e) hg'.continuous (partial_compact hηc e)
  have h3 := integrate_compact_mul hη.continuous hg'.continuous hηc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h2 h1 h3
    (fun x _ => hη.differentiable one_ne_zero x)
    (fun x _ => hg'.differentiable one_ne_zero x)
  change (∫ x, η x * partialDerivative g' e x) =
    -∫ x, partialDerivative η e x * g' x at h
  simp only [g', shifted_partial hg] at h ⊢
  linarith

private theorem reaction_derivative {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (e x : Plane) :
    partialDerivative (fun y => u y ^ 3 - u y) e x =
      (3 * (u x)^2 - 1) * partialDerivative u e x := by
  have h := (hu.differentiable (by norm_num) x).hasFDerivAt
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L e) ((h.pow 3).sub h).fderiv
  unfold partialDerivative
  simp only [sub_apply, smul_apply, smul_eq_mul] at he
  change (fderiv ℝ (fun y => u y ^ 3 - u y) x) e =
    3 • u x ^ (3 - 1) * (fderiv ℝ u x) e - (fderiv ℝ u x) e at he
  rw [he]
  norm_num
  ring

private theorem weak_partial {u : Plane → ℝ} (hu : DeGiorgi.IsBoundedSolution u)
    (e : Plane) {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ x, inner ℝ (∇ (partialDerivative u e) x) (∇ η x)) +
      (∫ x, η x * ((3 * (u x)^2 - 1) * partialDerivative u e x)) = 0 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let g (i : Fin 3) := partialDerivative u (b i)
  let a (i : Fin 3) := partialDerivative η (b i)
  let F (x : Plane) := u x ^ 3 - u x
  let W (t : ℝ) := (∑ i, ∫ x, a i x * g i (x + t • e)) + ∫ x, η x * F (x + t • e)
  have hg (i : Fin 3) : ContDiff ℝ 1 (g i) := partial_contDiff hu.regular (b i)
  have ha (i : Fin 3) : Continuous (a i) := partial_continuous hη (b i)
  have hac (i : Fin 3) : HasCompactSupport (a i) := partial_compact hηc (b i)
  have hU : ContDiff ℝ 1 u := hu.regular.of_le (by norm_num)
  have hF : ContDiff ℝ 1 F := (hU.pow 3).sub hU
  have hW : W = fun _ => 0 := by
    funext t
    have hLi (i : Fin 3) : Integrable
        (fun x => η x * partialDerivative (g i) (b i) (x + t • e)) :=
      integrate_compact_mul hη.continuous
        ((partial_continuous (hg i) (b i)).comp (continuous_id.add continuous_const)) hηc
    have hsum : (∑ i, ∫ x, a i x * g i (x + t • e)) = -(∫ x, η x * F (x + t • e)) := by
      calc
        _ = ∑ i, -(∫ x, η x * partialDerivative (g i) (b i) (x + t • e)) :=
          sum_congr rfl fun i _ => integrate_shifted_by_parts (hg i) hη hηc _ _
        _ = -(∫ x, ∑ i, η x * partialDerivative (g i) (b i) (x + t • e)) := by
          rw [sum_neg_distrib, integral_finsetSum _ (fun i _ => hLi i)]
        _ = _ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          rw [← mul_sum]
          change η x * (∑ i, partialDerivative (partialDerivative u (b i)) (b i)
            (x + t • e)) = η x * F (x + t • e)
          rw [← laplacian_as_partials hu.regular b]
          congr 1
          have hpde := hu.solution (x + t • e)
          dsimp [F]
          linarith
    change (∑ i, ∫ x, a i x * g i (x + t • e)) + (∫ x, η x * F (x + t • e)) = 0
    rw [hsum, neg_add_cancel]
  have hsumdiff := HasDerivAt.fun_sum (u := (univ : Finset (Fin 3)))
    (fun i _ => shifted_integral_deriv (ha i) (hac i) (hg i) e)
  have hD : HasDerivAt W ((∑ i, ∫ x, a i x * partialDerivative (g i) e x) +
      ∫ x, η x * partialDerivative F e x) 0 :=
    hsumdiff.add (shifted_integral_deriv hη.continuous hηc hF e)
  have hz := hD.deriv
  rw [hW, deriv_const] at hz
  calc
    _ = (∑ i, ∫ x, a i x * partialDerivative (g i) e x) +
        (∫ x, η x * partialDerivative F e x) := ?_
    _ = 0 := hz.symm
  congr 1
  · have hIi (i : Fin 3) : Integrable
        (fun x => a i x * partialDerivative (g i) e x) :=
      integrate_compact_mul (ha i) (partial_continuous (hg i) e) (hac i)
    rw [← integral_finsetSum _ (fun i _ => hIi i)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [inner_gradient_as_partials _ _ b]
    apply sum_congr rfl
    intro i _
    change partialDerivative (partialDerivative u e) (b i) x * a i x =
      a i x * partialDerivative (partialDerivative u (b i)) e x
    rw [partial_comm hu.regular, mul_comm]
  · apply integral_congr_ae
    filter_upwards [] with x
    change η x * ((3 * u x ^ 2 - 1) * partialDerivative u e x) =
      η x * partialDerivative (fun y => u y ^ 3 - u y) e x
    rw [reaction_derivative hu.regular]

private theorem gradient_product {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (x : Plane) :
    ∇ (fun y => f y * g y) x = f x • ∇ g x + g x • ∇ f x := by
  unfold gradient
  rw [fderiv_fun_mul (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x)]
  simp only [map_add, map_smul]

private theorem inner_gradient_integrable {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    Integrable (fun x => inner ℝ (∇ f x) (∇ g x)) := by
  have hGrad {h : Plane → ℝ} (hh : ContDiff ℝ 1 h) : Continuous (∇ h) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hh.continuous_fderiv one_ne_zero)
  apply ((hGrad hf).inner (hGrad hg)).integrable_of_hasCompactSupport
  apply hgc.mono'
  intro x hx
  apply support_fderiv_subset ℝ
  change fderiv ℝ g x ≠ 0
  intro he
  exact hx (by simp [gradient, he])

private theorem quotient_flux {v w η : Plane → ℝ} (hv : ContDiff ℝ 1 v)
    (hw : ContDiff ℝ 1 w) (hη : ContDiff ℝ 1 η) (hne : ∀ x, v x ≠ 0) (x : Plane) :
    (v x)^2 * inner ℝ (∇ (fun y => w y / v y) x) (∇ η x) =
      inner ℝ (∇ w x) (∇ (fun y => v y * η y) x) -
      inner ℝ (∇ v x) (∇ (fun y => w y * η y) x) := by
  let q := fun y => w y / v y
  have hq : ContDiff ℝ 1 q := hw.div hv hne
  have hqv (y : Plane) : v y * q y = w y := by
    dsimp [q]
    field_simp [hne y]
  have hwq : (fun y => v y * q y) = w := funext hqv
  have hgw := gradient_product hv hq x
  rw [hwq] at hgw
  change (v x)^2 * inner ℝ (∇ q x) (∇ η x) = _
  rw [gradient_product hv hη, gradient_product hw hη]
  simp only [inner_add_right, real_inner_smul_right]
  rw [real_inner_comm (∇ w x) (∇ v x)]
  rw [hgw]
  simp only [inner_add_left, real_inner_smul_left]
  rw [← hqv x]
  ring

set_option maxHeartbeats 600000 in
theorem solution (u : Plane → ℝ) (i : Fin 3) (hu : DeGiorgi.IsBoundedSolution u)
    (hpos : DeGiorgi.HasPositiveDeriv u) :
    let v := partialDerivative u (EuclideanSpace.single 0 1)
    let w := partialDerivative u (EuclideanSpace.single i 1)
    ∀ η : Plane → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x)^2 * inner ℝ (∇ (fun y => w y / v y) x) (∇ η x)) = 0 := by
  intro v w η hη hηc
  have hv : ContDiff ℝ 1 v := partial_contDiff hu.regular _
  have hw : ContDiff ℝ 1 w := partial_contDiff hu.regular _
  have hv0 (x : Plane) : v x ≠ 0 := by
    have h := hpos x
    rw [(hu.regular.differentiable (by norm_num) x).lineDeriv_eq_fderiv] at h
    exact h.ne'
  have hvη : ContDiff ℝ 1 (fun x => v x * η x) := hv.mul hη
  have hwη : ContDiff ℝ 1 (fun x => w x * η x) := hw.mul hη
  have hvηc : HasCompactSupport (fun x => v x * η x) := hηc.mul_left (f := v)
  have hwηc : HasCompactSupport (fun x => w x * η x) := hηc.mul_left (f := w)
  have hweakW := weak_partial hu (EuclideanSpace.single i 1) hvη hvηc
  have hweakV := weak_partial hu (EuclideanSpace.single 0 1) hwη hwηc
  let reaction := fun x => 3 * (u x)^2 - 1
  have hcancel : (∫ x, (v x * η x) * (reaction x * w x)) =
      (∫ x, (w x * η x) * (reaction x * v x)) :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  change (∫ x, inner ℝ (∇ w x) (∇ (fun y => v y * η y) x)) +
    (∫ x, (v x * η x) * (reaction x * w x)) = 0 at hweakW
  change (∫ x, inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) +
    (∫ x, (w x * η x) * (reaction x * v x)) = 0 at hweakV
  have hdiff : (∫ x, inner ℝ (∇ w x) (∇ (fun y => v y * η y) x)) =
      (∫ x, inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) := by
    rw [hcancel] at hweakW
    linarith
  calc
    _ = ∫ x, (inner ℝ (∇ w x) (∇ (fun y => v y * η y) x) -
        inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) :=
      integral_congr_ae (ae_of_all _ (quotient_flux hv hw hη hv0))
    _ = 0 := by
      rw [integral_sub (inner_gradient_integrable hw hvη hvηc)
        (inner_gradient_integrable hv hwη hwηc), hdiff, sub_self]

end OMA.DeGiorgiWeak3

theorem OMA.solution : OMA.R_DeGiorgi_DeGiorgi_three_R1.H2 := by
  intro u i hu hpos
  exact OMA.DeGiorgiWeak3.solution u i hu hpos
