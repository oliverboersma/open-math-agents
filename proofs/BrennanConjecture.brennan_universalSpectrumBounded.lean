import FormalConjectures.Wikipedia.Brennanconjecture
/-
Brennan conjecture, universal integral means spectrum bound: B(-2) = 1.

Credit: the analytic core (integral means machinery, the uniform inverse-square
bound and its supporting lemmas, namespace OAI) is adapted from the openai/math
repository, https://github.com/openai/math (lean/OAI/Analysis/IntegralMeans and
its dependencies), authors: OpenAI, licensed under the Apache License 2.0.
Changes: ported to the pinned Lean/Mathlib toolchain, unused declarations
removed, internal declarations renamed and whitespace compacted to fit the size
limit, local irreducibility expressed with `seal`.
The bridge to the formal-conjectures statement (namespace KBridgeBr, including
the lower bound via the explicit function z - z^2/2) is original.
-/
open Set MeasureTheory Filter Function InnerProductSpace TopologicalSpace
open scoped Classical CompactlySupported ComplexConjugate ENNReal InnerProductSpace Manifold NNReal Topology
section
namespace OAI
noncomputable section
namespace Brennan
def disk:Set ℂ:=Metric.ball 0 1
def kz1 (f:ℂ → ℂ) (U:Set ℂ):Prop :=
  DifferentiableOn ℂ f U ∧ Set.InjOn f U
def kz2 (f:ℂ → ℂ):Prop :=
  kz1 f disk ∧ f 0 = 0 ∧ deriv f 0 = 1
def kz3 (f:ℂ → ℂ) (t r:ℝ):ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r:ℂ) * Complex.exp ((θ:ℂ) * Complex.I))‖ ^ t
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def HasLogIncrement (γ:C(unitInterval,ℂ)) (q:ℂ):Prop :=
  ∃ T:C(unitInterval,ℂ),(∀ t,Complex.exp (T t) = γ t) ∧ T 1-T 0 = q
lemma HasLogIncrement.perturb {γ η:C(unitInterval,ℂ)} {q:ℂ}
    (hγ:HasLogIncrement γ q) (hloopγ:γ 1 = γ 0) (hloopη:η 1 = η 0)
    (h:∀ t,‖η t-γ t‖ < ‖γ t‖):HasLogIncrement η q:=by
  obtain ⟨T,hT,hend⟩:=hγ
  have hn (t):γ t ≠ 0:=(hT t ▸ Complex.exp_ne_zero (T t))
  have hratio (t):η t / γ t ∈ Complex.slitPlane:=by
    have he:η t / γ t = 1 + (η t-γ t)/γ t:=by field_simp [hn t]; ring
    rw [he]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_div,div_lt_one (norm_pos_iff.mpr (hn t))]
    exact h t
  let R:C(unitInterval,ℂ):=⟨fun t => Complex.log (η t / γ t),by
    apply Continuous.clog
    · exact η.continuous.div γ.continuous hn
    · exact hratio⟩
  refine ⟨T+R,?_,?_⟩
  · intro t
    change Complex.exp (T t+Complex.log (η t/γ t)) = η t
    rw [Complex.exp_add,hT t,Complex.exp_log (Complex.slitPlane_ne_zero (hratio t))]
    field_simp [hn t]
  · change (T 1+Complex.log (η 1/γ 1))-(T 0+Complex.log (η 0/γ 0))=q
    rw [hloopγ,hloopη]
    linear_combination hend
def kz4:C(unitInterval,ℂ) :=
  ⟨fun t => Complex.exp ((2*Real.pi*(t:ℝ):ℝ)*Complex.I),by fun_prop⟩
@[simp] lemma kz5:kz4 0 = 1:=by simp [kz4]
@[simp] lemma kz6:kz4 1 = 1:=by
  simp [kz4,Complex.exp_two_pi_mul_I]
@[simp] lemma kz7 (t:unitInterval):‖kz4 t‖ = 1:=by
  simp [kz4,Complex.norm_exp]
lemma kz8 (a:ℂ) (ha:a ≠ 0) :
    HasLogIncrement (a • kz4) (2*Real.pi*Complex.I):=by
  refine ⟨⟨fun t => Complex.log a+(2*Real.pi*(t:ℝ):ℝ)*Complex.I,by fun_prop⟩,?_,?_⟩
  · intro t
    simp [Complex.exp_add,Complex.exp_log ha,kz4]
  · simp
def kz9 (A:ℂ →L[ℝ] ℂ):ℂ:=(A 1-Complex.I*A Complex.I)/2
def kz10 (A:ℂ →L[ℝ] ℂ):ℂ:=(A 1+Complex.I*A Complex.I)/2
lemma kz11 (A:ℂ →L[ℝ] ℂ) (z:ℂ) :
    A z = kz9 A*z+kz10 A*conj z:=by
  have he:z = z.re • (1:ℂ)+z.im • Complex.I:=by simp [Complex.real_smul]
  calc
    A z = z.re • A 1+z.im • A Complex.I:=by
      conv_lhs => rw [he,map_add,map_smul,map_smul]
    _ = kz9 A*z+kz10 A*conj z:=by
      apply Complex.ext <;>
        simp [kz9,kz10,Complex.mul_re,Complex.mul_im,
          Complex.real_smul] <;> ring
lemma kz12 (A:ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det A = (A 1).re*(A Complex.I).im-(A Complex.I).re*(A 1).im:=by
  rw [← LinearMap.det_toMatrix Complex.basisOneI,Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Complex.coe_basisOneI,Complex.coe_basisOneI_repr]
lemma kz13 (A:ℂ →L[ℝ] ℂ) :
    LinearMap.det A.toLinearMap = ‖kz9 A‖^2-‖kz10 A‖^2:=by
  rw [kz12]
  simp only [← Complex.normSq_eq_norm_sq,kz9,kz10,
    Complex.normSq_apply,Complex.div_re,Complex.div_im,Complex.sub_re,
    Complex.sub_im,Complex.add_re,Complex.add_im,Complex.mul_re,
    Complex.mul_im,Complex.I_re,Complex.I_im]
  norm_num
  ring
lemma HasLogIncrement.smul {γ:C(unitInterval,ℂ)} {q:ℂ}
    (hγ:HasLogIncrement γ q) {c:ℂ} (hc:c ≠ 0) :
    HasLogIncrement (c • γ) q:=by
  obtain ⟨T,hT,hend⟩:=hγ
  refine ⟨T+ContinuousMap.const _ (Complex.log c),?_,?_⟩
  · intro t
    change Complex.exp (T t+Complex.log c) = c*γ t
    rw [Complex.exp_add,hT t,Complex.exp_log hc,mul_comm]
  · change (T 1+Complex.log c)-(T 0+Complex.log c)=q
    linear_combination hend
lemma kz14 (γ:C(unitInterval,ℂ)) (hγ:∀ t,γ t ≠ 0) :
    ∃ T:C(unitInterval,ℂ),∀ t,Complex.exp (T t) = γ t:=by
  let:=(convex_Icc (𝕜:=ℝ) (0:ℝ) 1).contractibleSpace (show (Icc (0:ℝ) 1).Nonempty from ⟨0,by simp⟩)
  let:=(convex_Icc (𝕜:=ℝ) (0:ℝ) 1).locallyPathConnectedSpace
  obtain ⟨T,⟨-,hT⟩,-⟩:=Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    γ (Complex.exp_log (hγ 0)) hγ
  exact ⟨T,fun t => congrFun hT t⟩
lemma log_lifts_difference_constant.{u_1} {X:Type u_1} [TopologicalSpace X] [PreconnectedSpace X]
    {A B:X → ℂ} (hA:Continuous A) (hB:Continuous B)
    (h:∀ x,Complex.exp (A x) = Complex.exp (B x)) (x y:X) :
    A y - B y = A x - B x:=by
  have hC:Continuous (fun z => B z + (A x - B x)):=hB.add continuous_const
  have he (z):Complex.exp (A z) = Complex.exp (B z + (A x - B x)):=by
    rw [Complex.exp_add,Complex.exp_sub,h x,div_self (Complex.exp_ne_zero _),mul_one]
    exact h z
  have heq:A = fun z => B z + (A x - B x) :=
    Complex.isCoveringMap_exp.eq_of_comp_eq hA hC
      (by funext z; exact Subtype.ext (he z)) x (by ring)
  have hy:=congrFun heq y
  linear_combination hy
lemma HasLogIncrement.unique {γ:C(unitInterval,ℂ)} {p q:ℂ}
    (hp:HasLogIncrement γ p) (hq:HasLogIncrement γ q):p = q:=by
  obtain ⟨A,hA,hp⟩:=hp
  obtain ⟨B,hB,hq⟩:=hq
  have he:=log_lifts_difference_constant A.continuous B.continuous
    (fun t => (hA t).trans (hB t).symm) (0:unitInterval) 1
  linear_combination hp.symm - hq.symm + he
lemma HasLogIncrement.mul {γ η:C(unitInterval,ℂ)} {p q:ℂ}
    (hγ:HasLogIncrement γ p) (hη:HasLogIncrement η q) :
    HasLogIncrement (γ * η) (p + q):=by
  obtain ⟨A,hA,hp⟩:=hγ
  obtain ⟨B,hB,hq⟩:=hη
  refine ⟨A+B,?_,?_⟩
  · intro t
    change Complex.exp (A t+B t) = γ t * η t
    rw [Complex.exp_add,hA t,hB t]
  · change (A 1+B 1)-(A 0+B 0)=p+q
    linear_combination hp+hq
lemma HasLogIncrement.inv {γ:C(unitInterval,ℂ)} {q:ℂ}
    (hγ:HasLogIncrement γ q) :
    HasLogIncrement ⟨fun t => (γ t)⁻¹,by
      exact γ.continuous.inv₀ (fun t => by
        obtain ⟨A,hA,-⟩:=hγ
        exact (hA t ▸ Complex.exp_ne_zero (A t)))⟩ (-q):=by
  obtain ⟨A,hA,hq⟩:=hγ
  refine ⟨-A,?_,?_⟩
  · intro t
    change Complex.exp (-A t) = (γ t)⁻¹
    rw [Complex.exp_neg,hA t]
  · change -A 1-(-A 0) = -q
    linear_combination -hq
lemma HasLogIncrement.conj {γ:C(unitInterval,ℂ)} {q:ℂ}
    (hγ:HasLogIncrement γ q) :
    HasLogIncrement ⟨fun t => conj (γ t),by fun_prop⟩ (conj q):=by
  obtain ⟨A,hA,hq⟩:=hγ
  refine ⟨⟨fun t => conj (A t),by fun_prop⟩,?_,?_⟩
  · intro t
    exact (Complex.exp_conj _).trans (congrArg conj (hA t))
  · change conj (A 1)-conj (A 0)=conj q
    rw [← map_sub,hq]
lemma HasLogIncrement.integer {γ:C(unitInterval,ℂ)} {q:ℂ}
    (hγ:HasLogIncrement γ q) (hloop:γ 1 = γ 0) :
    ∃ n:ℤ,q = n*(2*Real.pi*Complex.I):=by
  obtain ⟨A,hA,hq⟩:=hγ
  apply Complex.exp_eq_one_iff.mp
  rw [← hq,Complex.exp_sub,hA 1,hA 0,hloop,
    div_self (hA 0 ▸ Complex.exp_ne_zero _)]
lemma kz15:(2*Real.pi*Complex.I:ℂ) ≠ 0:=by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero
lemma kz16:Function.Injective
    (fun n:ℤ => (n:ℂ)*(2*Real.pi*Complex.I)):=by
  intro n m h
  exact_mod_cast (mul_right_cancel₀ kz15 h:(n:ℂ) = m)
lemma kz17 (γ:C(unitInterval,ℂ))
    (hloop:γ 1 = γ 0) (hγ:∀ t,γ t ≠ 0) :
    ∃ n:ℤ,HasLogIncrement γ (n*(2*Real.pi*Complex.I)):=by
  obtain ⟨A,hA⟩:=kz14 γ hγ
  have hi:HasLogIncrement γ (A 1-A 0):=⟨A,hA,rfl⟩
  obtain ⟨n,hn⟩:=hi.integer hloop
  exact ⟨n,hn ▸ hi⟩
def kz18 (γ:C(unitInterval,ℂ)):ℤ:=by
  classical
  exact if h:γ 1 = γ 0 ∧ ∀ t,γ t ≠ 0 then
    Classical.choose (kz17 γ h.1 h.2)
  else 0
lemma kz19 (γ:C(unitInterval,ℂ))
    (hloop:γ 1 = γ 0) (hγ:∀ t,γ t ≠ 0) :
    HasLogIncrement γ ((kz18 γ)*(2*Real.pi*Complex.I)):=by
  rw [kz18,dif_pos ⟨hloop,hγ⟩]
  exact Classical.choose_spec (kz17 γ hloop hγ)
lemma kz20 {γ:C(unitInterval,ℂ)} {n:ℤ}
    (hloop:γ 1 = γ 0) (h:HasLogIncrement γ (n*(2*Real.pi*Complex.I))) :
    kz18 γ = n:=by
  have hn (t):γ t ≠ 0:=by
    obtain ⟨A,hA,-⟩:=h
    exact hA t ▸ Complex.exp_ne_zero _
  exact kz16 ((kz19 γ hloop hn).unique h)
lemma kz21 (γ η:C(unitInterval,ℂ))
    (hloopγ:γ 1 = γ 0) (hloopη:η 1 = η 0)
    (hγ:∀ t,γ t ≠ 0) (hη:∀ t,η t ≠ 0) :
    kz18 (γ*η) = kz18 γ + kz18 η:=by
  apply kz20 (by simp [hloopγ,hloopη])
  convert (kz19 γ hloopγ hγ).mul (kz19 η hloopη hη) using 1
  push_cast
  ring
lemma kz22 {γ η:C(unitInterval,ℂ)}
    (hloopγ:γ 1 = γ 0) (hloopη:η 1 = η 0) (hγ:∀ t,γ t ≠ 0)
    (h:∀ t,‖η t-γ t‖ < ‖γ t‖):kz18 η = kz18 γ :=
  kz20 hloopη
    ((kz19 γ hloopγ hγ).perturb hloopγ hloopη h)
lemma exists_log_lift_of_simplyConnected.{u_1} {X:Type u_1} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x:X)
    (f:C(X,ℂ)) (hf:∀ y,f y ≠ 0) :
    ∃ A:C(X,ℂ),∀ y,Complex.exp (A y) = f y:=by
  obtain ⟨A,⟨-,hA⟩,-⟩:=Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    f (Complex.exp_log (hf x)) hf
  exact ⟨A,fun y => congrFun hA y⟩
lemma HasLogIncrement.homotopy {H:C(unitInterval × unitInterval,ℂ)}
    (hH:∀ p,H p ≠ 0) (hloop:∀ s,H (s,1) = H (s,0)) {q:ℂ}
    (h:HasLogIncrement ⟨fun t => H (0,t),by fun_prop⟩ q) :
    HasLogIncrement ⟨fun t => H (1,t),by fun_prop⟩ q:=by
  let:=(convex_Icc (𝕜:=ℝ) (0:ℝ) 1).contractibleSpace
    (show (Icc (0:ℝ) 1).Nonempty from ⟨0,by simp⟩)
  let:=(convex_Icc (𝕜:=ℝ) (0:ℝ) 1).locallyPathConnectedSpace
  obtain ⟨A,hA⟩:=exists_log_lift_of_simplyConnected (0,0) H hH
  have hi:HasLogIncrement ⟨fun t => H (0,t),by fun_prop⟩ (A (0,1)-A (0,0)) :=
    ⟨⟨fun t => A (0,t),by fun_prop⟩,fun t => hA (0,t),rfl⟩
  have hc:=log_lifts_difference_constant
    (show Continuous (fun s => A (s,1)) by fun_prop)
    (show Continuous (fun s => A (s,0)) by fun_prop)
    (fun s => by rw [hA,hA,hloop]) (0:unitInterval) 1
  refine ⟨⟨fun t => A (1,t),by fun_prop⟩,fun t => hA (1,t),?_⟩
  change A (1,1)-A (1,0)=q
  exact hc.trans (hi.unique h)
lemma kz23 (H:C(unitInterval × unitInterval,ℂ))
    (hH:∀ p,H p ≠ 0) (hloop:∀ s,H (s,1) = H (s,0)) :
    kz18 ⟨fun t => H (1,t),by fun_prop⟩ =
      kz18 ⟨fun t => H (0,t),by fun_prop⟩:=by
  apply kz20 (hloop 1)
  exact (kz19 ⟨fun t => H (0,t),by fun_prop⟩ (hloop 0)
    (fun t => hH (0,t))).homotopy hH hloop
def kz24 (γ:C(unitInterval,ℂ)) (a:ℂ):ℤ :=
  kz18 ⟨fun t => γ t-a,by fun_prop⟩
lemma kz25 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0)
    {a:ℂ} (ha:a ∉ range γ):∀ᶠ b in 𝓝 a,kz24 γ b = kz24 γ a:=by
  have hn (t):γ t-a ≠ 0:=sub_ne_zero.mpr (fun h => ha ⟨t,h⟩)
  obtain ⟨d,hd,hdist⟩:=isCompact_univ.exists_forall_le'
    (show ContinuousOn (fun t:unitInterval => ‖γ t-a‖) univ by fun_prop)
    (a:=0) (fun t _ => norm_pos_iff.mpr (hn t))
  filter_upwards [Metric.ball_mem_nhds a hd] with b hb
  apply kz22 (by simp [hloop]) (by simp [hloop]) hn
  intro t
  change ‖(γ t-b)-(γ t-a)‖ < ‖γ t-a‖
  rw [show (γ t-b)-(γ t-a)=a-b by ring,norm_sub_rev]
  exact (show ‖b-a‖ < d by simpa [Metric.mem_ball,dist_eq_norm] using hb).trans_le (hdist t (mem_univ t))
lemma kz26 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) :
    ContinuousOn (kz24 γ) (range γ)ᶜ:=by
  intro a ha
  apply ContinuousAt.continuousWithinAt
  have he:kz24 γ =ᶠ[𝓝 a] fun _ => kz24 γ a :=
    kz25 γ hloop ha
  exact continuousAt_const.congr he.symm
lemma kz27 (a:ℂ) (ha:a ≠ 0) :
    HasLogIncrement (ContinuousMap.const unitInterval a) 0:=by
  exact ⟨ContinuousMap.const unitInterval (Complex.log a),
    fun _ => Complex.exp_log ha,sub_self _⟩
lemma kz28 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0)
    {a:ℂ} (ha:∀ t,‖γ t‖ < ‖a‖):kz24 γ a = 0:=by
  have hane:a ≠ 0:=norm_pos_iff.mp ((norm_nonneg (γ 0)).trans_lt (ha 0))
  apply kz20 (by simp [hloop])
  have hh:HasLogIncrement ⟨fun t => γ t-a,by fun_prop⟩ 0 :=
    (kz27 (-a) (neg_ne_zero.mpr hane)).perturb rfl
      (by simp [hloop]) (fun t => by simpa using ha t)
  simpa using hh
lemma kz29 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) :
    ∃ R:ℝ,0 < R ∧ ∀ a:ℂ,R ≤ ‖a‖ → kz24 γ a = 0:=by
  obtain ⟨R,-,hR⟩:=(isCompact_range γ.continuous).isBounded.exists_pos_norm_lt
  refine ⟨max R 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro a ha
  apply kz28 γ hloop
  intro t
  exact (hR (γ t) ⟨t,rfl⟩).trans_le ((le_max_left R 1).trans ha)
def kz30 (γ:C(unitInterval,ℂ)):Set ℂ :=
  {a | a ∉ range γ ∧ kz24 γ a ≠ 0}
lemma kz31 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) :
    IsOpen (kz30 γ):=by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hc:=(isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds ha.1
  filter_upwards [hc,kz25 γ hloop ha.1] with b hb heq
  exact ⟨hb,heq ▸ ha.2⟩
lemma kz32 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) :
    Bornology.IsBounded (kz30 γ):=by
  obtain ⟨R,-,hR⟩:=kz29 γ hloop
  apply (Metric.isBounded_ball (x:=(0:ℂ)) (r:=R)).subset
  intro a ha
  rw [Metric.mem_ball,dist_zero_right]
  by_contra h
  exact ha.2 (hR a (le_of_not_gt h))
lemma kz33 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) :
    frontier (kz30 γ) ⊆ range γ:=by
  intro a ha
  by_contra han
  have hn:(range γ)ᶜ ∈ 𝓝 a :=
    (isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds han
  have he:=kz25 γ hloop han
  by_cases hi:kz24 γ a = 0
  · have hh:(kz30 γ)ᶜ ∈ 𝓝 a:=by
      filter_upwards [he] with b hb
      intro hbin
      exact hbin.2 (hb.trans hi)
    exact (mem_closure_iff_nhds.1 ha.1 _ hh).elim (fun b hb => hb.1 hb.2)
  · have hnmem:=ha.2
    rw [(kz31 γ hloop).interior_eq] at hnmem
    exact hnmem ⟨han,hi⟩
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def kz34 (positive:Bool) (a z:ℂ):ℂ :=
  if positive then z-a else conj (z-a)
@[simp] lemma kz35 (p:Bool) (a z:ℂ) :
    ‖kz34 p a z‖ = ‖z-a‖:=by cases p <;> simp only [kz34,Bool.false_eq_true,↓reduceIte,RCLike.norm_conj]
@[simp] lemma kz36 (p:Bool) (a z:ℂ) :
    kz34 p a z = 0 ↔ z = a:=by
  rw [← norm_eq_zero,kz35,norm_eq_zero,sub_eq_zero]
lemma kz37 (p:Bool) (a:ℂ) :
    Continuous (kz34 p a):=by
  unfold kz34
  cases p <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
def kz38 (a:ℂ) (r:ℝ) (z:ℂ):ℝ :=
  max 0 (min 1 (2-2*‖z-a‖/r))
lemma kz39 (a:ℂ) (r:ℝ):Continuous (kz38 a r):=by
  unfold kz38
  fun_prop
lemma kz40 {a z:ℂ} {r:ℝ} (hr:0 < r) (hz:‖z-a‖ ≤ r/2) :
    kz38 a r z = 1:=by
  have hb:2*‖z-a‖/r ≤ 1:=(div_le_iff₀ hr).mpr (by linarith)
  simp [kz38,min_eq_left (by linarith:1 ≤ 2-2*‖z-a‖/r)]
lemma kz41 {a z:ℂ} {r:ℝ} (hr:0 < r) (hz:r ≤ ‖z-a‖) :
    kz38 a r z = 0:=by
  rw [kz38,max_eq_left]
  apply min_le_of_right_le
  rw [sub_nonpos,le_div_iff₀ hr]
  linarith
def kz42 (X:ℂ → ℂ) (p:Bool) (a c:ℂ) (r:ℝ) (z:ℂ):ℂ :=
  (kz38 a r z:ℂ) * Complex.log (X z / (c*kz34 p a z))
lemma kz43 {X:ℂ → ℂ} (hX:Continuous X)
    {p:Bool} {a c z:ℂ} {r:ℝ} (hr:0 < r) (hc:c ≠ 0) (hz:z ≠ a)
    (hlocal:∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
      X w / (c*kz34 p a w) ∈ Complex.slitPlane) :
    ContinuousAt (kz42 X p a c r) z:=by
  by_cases hb:‖z-a‖ < 2*r
  · apply (Complex.continuous_ofReal.comp (kz39 a r)).continuousAt.mul
    apply ContinuousAt.clog
    · exact hX.continuousAt.div
        (continuous_const.mul (kz37 p a)).continuousAt
        (mul_ne_zero hc (mt (kz36 p a z).mp hz))
    · exact hlocal z hb hz
  · have hlt:r < ‖z-a‖:=by linarith
    have he:kz42 X p a c r =ᶠ[𝓝 z] fun _ => 0:=by
      filter_upwards [((show ContinuousAt (fun w:ℂ => ‖w-a‖) z by fun_prop).eventually
        (Ioi_mem_nhds hlt))] with w hw
      simp [kz42,kz41 hr (le_of_lt hw)]
    exact continuousAt_const.congr he.symm
lemma kz44 {X:ℂ → ℂ} {p:Bool} {a c z:ℂ} {r:ℝ}
    (hr:0 < r) (hz:r < ‖z-a‖):kz42 X p a c r =ᶠ[𝓝 z] fun _ => 0:=by
  filter_upwards [((show ContinuousAt (fun w:ℂ => ‖w-a‖) z by fun_prop).eventually
    (Ioi_mem_nhds hz))] with w hw
  simp [kz42,kz41 hr (le_of_lt hw)]
def kz45 (X:ℂ → ℂ) (p:Bool) (a c:ℂ) (r:ℝ) (z:ℂ):ℂ:=by
  classical
  exact if z = a then c else X z / kz34 p a z *
    Complex.exp (-kz42 X p a c r z)
lemma kz46 {X:ℂ → ℂ} {p:Bool} {a c z:ℂ} {r:ℝ}
    (hr:0 < r) (hc:c ≠ 0) (hz:‖z-a‖ < r/2)
    (hlocal:∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
      X w / (c*kz34 p a w) ∈ Complex.slitPlane) :
    kz45 X p a c r z = c:=by
  classical
  by_cases hza:z = a
  · simp [kz45,hza]
  · have hd:kz34 p a z ≠ 0:=mt (kz36 p a z).mp hza
    have hslit:=hlocal z (by linarith) hza
    have hx:X z ≠ 0:=by
      intro hx
      simpa [hx] using Complex.slitPlane_ne_zero hslit
    simp only [kz45,if_neg hza,kz42,kz40 hr hz.le,
      Complex.ofReal_one,one_mul,Complex.exp_neg,
      Complex.exp_log (Complex.slitPlane_ne_zero hslit)]
    field_simp
lemma kz47 {X:ℂ → ℂ} (hX:Continuous X)
    {p:Bool} {a c:ℂ} {r:ℝ} (hr:0 < r) (hc:c ≠ 0)
    (hlocal:∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
      X w / (c*kz34 p a w) ∈ Complex.slitPlane) :
    Continuous (kz45 X p a c r):=by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz:z = a
  · subst z
    have he:kz45 X p a c r =ᶠ[𝓝 a] fun _ => c:=by
      filter_upwards [Metric.ball_mem_nhds a (by positivity:0 < r/2)] with w hw
      exact kz46 hr hc (by simpa [Metric.mem_ball,dist_eq_norm] using hw) hlocal
    exact continuousAt_const.congr he.symm
  · have he:kz45 X p a c r =ᶠ[𝓝 z] fun w =>
        X w / kz34 p a w * Complex.exp (-kz42 X p a c r w):=by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
      have hwn:w ≠ a:=hw
      simp [kz45,hwn]
    apply ContinuousAt.congr ?_ he.symm
    exact (hX.continuousAt.div (kz37 p a).continuousAt
      (mt (kz36 p a z).mp hz)).mul
      ((kz43 hX hr hc hz hlocal).neg.cexp)
lemma kz48 {X:ℂ → ℂ} {p:Bool} {a c z:ℂ} {r:ℝ}
    (hc:c ≠ 0):kz45 X p a c r z = 0 ↔ X z = 0 ∧ z ≠ a:=by
  classical
  by_cases hz:z = a
  · simp [kz45,hz,hc]
  · simp [kz45,hz,div_eq_zero_iff,
      mt (kz36 p a z).mp hz,Complex.exp_ne_zero]
lemma kz49 {X:ℂ → ℂ} {p:Bool} {a c z:ℂ} {r:ℝ}
    (hz:z ≠ a):X z = kz34 p a z * kz45 X p a c r z *
      Complex.exp (kz42 X p a c r z):=by
  classical
  have hd:kz34 p a z ≠ 0:=mt (kz36 p a z).mp hz
  simp only [kz45,if_neg hz,Complex.exp_neg]
  field_simp
lemma kz50 {X:ℂ → ℂ} {a c:ℂ} {A:ℂ →L[ℝ] ℂ}
    {p:Bool} (hzero:X a = 0) (hd:HasFDerivAt X A a)
    {b:ℝ} (hb:b < ‖c‖)
    (herr:∀ w:ℂ,‖A w-c*kz34 p 0 w‖ ≤ b*‖w‖) :
    ∃ r:ℝ,0 < r ∧ ∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
      X w / (c*kz34 p a w) ∈ Complex.slitPlane:=by
  have hrem:=(hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound
    (by linarith:0 < (‖c‖-b)/2)
  obtain ⟨δ,hδ,hbound⟩:=Metric.eventually_nhds_iff.mp hrem
  refine ⟨δ/3,by positivity,fun w hw hwa => ?_⟩
  have hwn:0 < ‖w-a‖:=norm_pos_iff.mpr (sub_ne_zero.mpr hwa)
  have hremw:=hbound (show dist (w-a) 0 < δ by simpa only [dist_zero_right] using (show ‖w-a‖ < δ by linarith))
  simp only [add_sub_cancel,hzero,sub_zero] at hremw
  have her:=herr (w-a)
  have he:kz34 p 0 (w-a) = kz34 p a w:=by
    simp [kz34]
  rw [he] at her
  have hlt:‖X w-c*kz34 p a w‖ < ‖c*kz34 p a w‖:=by
    calc
      ‖X w-c*kz34 p a w‖ =
          ‖(X w-A (w-a))+(A (w-a)-c*kz34 p a w)‖:=by congr 1; ring
      _ ≤ ‖X w-A (w-a)‖+‖A (w-a)-c*kz34 p a w‖:=norm_add_le _ _
      _ ≤ (‖c‖-b)/2*‖w-a‖+b*‖w-a‖:=add_le_add hremw her
      _ < ‖c*kz34 p a w‖:=by
        rw [norm_mul,kz35]
        nlinarith
  have hcn:c*kz34 p a w ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt hlt)
  have hratio:X w/(c*kz34 p a w) =
      1 + (X w-c*kz34 p a w)/(c*kz34 p a w):=by
    field_simp [left_ne_zero_of_mul hcn,right_ne_zero_of_mul hcn]
    ring
  rw [hratio]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_div,div_lt_one (norm_pos_iff.mpr hcn)]
  exact hlt
lemma kz51 {X:ℂ → ℂ} {a:ℂ} {A:ℂ →L[ℝ] ℂ}
    (hzero:X a = 0) (hd:HasFDerivAt X A a)
    (hdet:0 < LinearMap.det A.toLinearMap) :
    kz9 A ≠ 0 ∧ ∃ r:ℝ,0 < r ∧ ∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
      X w / (kz9 A*kz34 true a w) ∈ Complex.slitPlane:=by
  have hn:‖kz10 A‖ < ‖kz9 A‖:=by
    rw [kz13] at hdet
    nlinarith [norm_nonneg (kz9 A),norm_nonneg (kz10 A)]
  refine ⟨norm_pos_iff.mp ((norm_nonneg _).trans_lt hn),
    kz50 hzero hd hn ?_⟩
  intro w
  simp [kz11,kz34]
lemma kz52 {X:ℂ → ℂ} {a:ℂ} {A:ℂ →L[ℝ] ℂ}
    (hzero:X a = 0) (hd:HasFDerivAt X A a)
    (hdet:LinearMap.det A.toLinearMap < 0) :
    kz10 A ≠ 0 ∧ ∃ r:ℝ,0 < r ∧ ∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
      X w / (kz10 A*kz34 false a w) ∈ Complex.slitPlane:=by
  have hn:‖kz9 A‖ < ‖kz10 A‖:=by
    rw [kz13] at hdet
    nlinarith [norm_nonneg (kz9 A),norm_nonneg (kz10 A)]
  refine ⟨norm_pos_iff.mp ((norm_nonneg _).trans_lt hn),
    kz50 hzero hd hn ?_⟩
  intro w
  simp [kz11,kz34]
lemma kz53 (p:Bool) (a:ℂ) :
    Differentiable ℝ (kz34 p a):=by
  unfold kz34
  cases p <;> simp only [Bool.false_eq_true,↓reduceIte]
  · exact Complex.conjCLE.differentiable.comp (differentiable_id.sub_const a)
  · exact differentiable_id.sub_const a
lemma kz54 {X:ℂ → ℂ} {p:Bool} {a b c:ℂ} {r:ℝ}
    (hr:0 < r) (hb:b ≠ a) (hzero:X b = 0) {A:ℂ →L[ℝ] ℂ}
    (hX:HasFDerivAt X A b)
    (hlocal:∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
      X w / (c*kz34 p a w) ∈ Complex.slitPlane) :
    HasFDerivAt (kz45 X p a c r) ((kz34 p a b)⁻¹ • A) b:=by
  have hbfar:r < ‖b-a‖:=by
    by_contra hn
    have he:=Complex.slitPlane_ne_zero (hlocal b (by linarith) hb)
    simp [hzero] at he
  have he:kz45 X p a c r =ᶠ[𝓝 b] fun w => X w * (kz34 p a w)⁻¹:=by
    filter_upwards [kz44 (X:=X) (p:=p) (c:=c) hr hbfar,
      isClosed_singleton.isOpen_compl.mem_nhds hb] with w hw hwa
    have hwn:w ≠ a:=hwa
    simp [kz45,hwn,hw,div_eq_mul_inv]
  have hdn:kz34 p a b ≠ 0:=mt (kz36 p a b).mp hb
  have hinv:=((hasDerivAt_inv hdn).hasFDerivAt.restrictScalars ℝ).comp b
    ((kz53 p a b).hasFDerivAt)
  have hm:=hX.fun_mul hinv
  simp only [hzero,zero_smul,zero_add] at hm
  exact hm.congr_of_eventuallyEq he
lemma kz55 (c:ℂ) (A:ℂ →L[ℝ] ℂ) :
    LinearMap.det (c • A).toLinearMap = ‖c‖^2 * LinearMap.det A.toLinearMap:=by
  rw [kz12,kz12,← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,smul_apply,smul_eq_mul,
    Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring
lemma kz56 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0)
    (p:Bool) (a:ℂ) (ha:∀ t,γ t ≠ a) :
    kz18 ⟨fun t => kz34 p a (γ t),
      (kz37 p a).comp γ.continuous⟩ =
      (if p then 1 else -1) * kz24 γ a:=by
  cases p
  · change kz18 ⟨fun t => conj (γ t-a),by fun_prop⟩ = -1 * kz24 γ a
    rw [neg_one_mul]
    apply kz20 (by simp [hloop])
    have hh:=(kz19 ⟨fun t => γ t-a,by fun_prop⟩
      (by simp [hloop]) (fun t => sub_ne_zero.mpr (ha t))).conj
    convert hh using 1 <;> try rfl
    change ((-kz18 ⟨fun t => γ t-a,by fun_prop⟩:ℤ):ℂ) *
      (2*Real.pi*Complex.I) = _
    simp only [Int.cast_neg,map_mul,map_intCast,map_ofNat,
      Complex.conj_ofReal,Complex.conj_I]
    ring
  · simp only [↓reduceIte,one_mul]
    rfl
lemma kz57 {X:ℂ → ℂ} (hX:Continuous X)
    {p:Bool} {a c:ℂ} {r:ℝ} (hr:0 < r) (hc:c ≠ 0)
    (hlocal:∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
      X w / (c*kz34 p a w) ∈ Complex.slitPlane)
    (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0)
    (ha:∀ t,γ t ≠ a) (hγ:∀ t,X (γ t) ≠ 0) :
    kz18 ((⟨X,hX⟩:C(ℂ,ℂ)).comp γ) =
      (if p then 1 else -1)*kz24 γ a +
      kz18 ((⟨kz45 X p a c r,kz47 hX hr hc hlocal⟩:C(ℂ,ℂ)).comp γ):=by
  let D:C(unitInterval,ℂ):=⟨fun t => kz34 p a (γ t),
    (kz37 p a).comp γ.continuous⟩
  let Y:C(unitInterval,ℂ) :=
    (⟨kz45 X p a c r,kz47 hX hr hc hlocal⟩:C(ℂ,ℂ)).comp γ
  let B:C(unitInterval,ℂ):=⟨fun t => kz42 X p a c r (γ t),by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (kz43 hX hr hc (ha t) hlocal).comp γ.continuous.continuousAt⟩
  let E:C(unitInterval,ℂ):=⟨fun t => Complex.exp (B t),by fun_prop⟩
  have hE:kz18 E = 0:=by
    apply kz20 (by simp [E,B,hloop])
    simpa using (show HasLogIncrement E 0 from ⟨B,fun _ => rfl,by simp [B,hloop]⟩)
  have hD:∀ t,D t ≠ 0:=fun t => mt (kz36 p a (γ t)).mp (ha t)
  have hY:∀ t,Y t ≠ 0:=by
    intro t h
    exact hγ t ((kz48 hc).mp (show kz45 X p a c r (γ t) = 0 from h)).1
  have hfact:(⟨X,hX⟩:C(ℂ,ℂ)).comp γ = D*Y*E:=by
    ext t
    exact kz49 (X:=X) (c:=c) (r:=r) (p:=p) (ha t)
  rw [hfact,kz21 _ _ (by simp [D,Y,hloop]) (by simp [E,B,hloop])
      (fun t => mul_ne_zero (hD t) (hY t)) (fun t => Complex.exp_ne_zero _),
    hE,add_zero,kz21 _ _ (by simp [D,hloop]) (by simp [Y,hloop]) hD hY]
  rw [show kz18 D = (if p then 1 else -1)*kz24 γ a from
    kz56 γ hloop p a ha]
lemma kz58 (X:C(ℂ,ℂ)) {K:Set ℂ}
    (hK:Convex ℝ K) (hX:∀ z ∈ K,X z ≠ 0)
    (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) (hγ:∀ t,γ t ∈ K) :
    kz18 (X.comp γ) = 0:=by
  let:=hK.contractibleSpace ⟨γ 0,hγ 0⟩
  let:=hK.locallyPathConnectedSpace
  let XK:C(K,ℂ):=⟨fun z => X z,by fun_prop⟩
  obtain ⟨B,hB⟩:=exists_log_lift_of_simplyConnected (⟨γ 0,hγ 0⟩:K) XK
    (fun z => hX z z.property)
  apply kz20 (by simp [hloop])
  refine ⟨⟨fun t => B ⟨γ t,hγ t⟩,by fun_prop⟩,?_,?_⟩
  · intro t
    exact hB ⟨γ t,hγ t⟩
  · simp only [Int.cast_zero,zero_mul]
    change B ⟨γ 1,hγ 1⟩-B ⟨γ 0,hγ 0⟩=0
    simp only [hloop,sub_self]
def kz59 (A:ℂ →L[ℝ] ℂ):ℤ :=
  if 0 < LinearMap.det A.toLinearMap then 1 else -1
lemma kz60 {c:ℂ} (hc:c ≠ 0) (A:ℂ →L[ℝ] ℂ) :
    kz59 (c • A) = kz59 A:=by
  have hp:0 < ‖c‖^2:=sq_pos_of_pos (norm_pos_iff.mpr hc)
  simp only [kz59,kz55,mul_pos_iff_of_pos_left hp]
theorem kz61 {K:Set ℂ} (hK:Convex ℝ K)
    (s:Finset ℂ) (X:C(ℂ,ℂ)) (A:ℂ → ℂ →L[ℝ] ℂ)
    (hsK:∀ z ∈ s,z ∈ K) (hzero:∀ z ∈ K,X z = 0 ↔ z ∈ s)
    (hD:∀ z ∈ s,HasFDerivAt X (A z) z ∧ LinearMap.det (A z).toLinearMap ≠ 0)
    (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) (hγK:∀ t,γ t ∈ K)
    (hγ:∀ t,X (γ t) ≠ 0) :
    kz18 (X.comp γ) = ∑ a ∈ s,kz59 (A a)*kz24 γ a:=by
  classical
  induction s using Finset.induction_on generalizing X A with
  | empty =>
      simp only [Finset.sum_empty]
      apply kz58 X hK _ γ hloop hγK
      intro z hz h
      exact Finset.notMem_empty z ((hzero z hz).mp h)
  | @insert a s ha ih =>
      have ham:a ∈ insert a s:=Finset.mem_insert_self a s
      have haz:X a = 0:=(hzero a (hsK a ham)).mpr ham
      obtain ⟨hDa,hdet⟩:=hD a ham
      obtain ⟨p,c,r,hr,hc,hsign,hlocal⟩:∃ (p:Bool) (c:ℂ) (r:ℝ),
          0 < r ∧ c ≠ 0 ∧ (if p then (1:ℤ) else -1) = kz59 (A a) ∧
          ∀ w:ℂ,‖w-a‖ < 2*r → w ≠ a →
            X w/(c*kz34 p a w) ∈ Complex.slitPlane:=by
        rcases lt_or_gt_of_ne hdet with hn | hp
        · obtain ⟨hc,r,hr,hl⟩:=kz52 haz hDa hn
          exact ⟨false,kz10 (A a),r,hr,hc,by simp [kz59,not_lt.mpr hn.le],hl⟩
        · obtain ⟨hc,r,hr,hl⟩:=kz51 haz hDa hp
          exact ⟨true,kz9 (A a),r,hr,hc,by simp [kz59,hp],hl⟩
      let Y:C(ℂ,ℂ):=⟨kz45 X p a c r,
        kz47 X.continuous hr hc hlocal⟩
      let D:ℂ → ℂ →L[ℝ] ℂ:=fun b => (kz34 p a b)⁻¹ • A b
      have hbne (b:ℂ) (hb:b ∈ s):b ≠ a:=by
        intro he
        exact ha (he ▸ hb)
      have hdc (b:ℂ) (hb:b ∈ s):(kz34 p a b)⁻¹ ≠ 0 :=
        inv_ne_zero (mt (kz36 p a b).mp (hbne b hb))
      have hsK':∀ z ∈ s,z ∈ K:=fun z hz => hsK z (Finset.mem_insert_of_mem hz)
      have hYzero:∀ z ∈ K,Y z = 0 ↔ z ∈ s:=by
        intro z hz
        change kz45 X p a c r z = 0 ↔ _
        rw [kz48 hc,hzero z hz,Finset.mem_insert]
        constructor
        · rintro ⟨h,hne⟩
          exact h.resolve_left hne
        · intro h
          exact ⟨Or.inr h,hbne z h⟩
      have hDY:∀ z ∈ s,HasFDerivAt Y (D z) z ∧ LinearMap.det (D z).toLinearMap ≠ 0:=by
        intro z hz
        obtain ⟨hDz,hdz⟩:=hD z (Finset.mem_insert_of_mem hz)
        have hzz:=(hzero z (hsK' z hz)).mpr (Finset.mem_insert_of_mem hz)
        refine ⟨kz54 hr (hbne z hz) hzz hDz hlocal,?_⟩
        dsimp only [D]
        rw [kz55]
        exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (hdc z hz))) hdz
      have hγa:∀ t,γ t ≠ a:=by
        intro t ht
        exact hγ t (ht ▸ haz)
      have hγY:∀ t,Y (γ t) ≠ 0:=by
        intro t ht
        exact hγ t ((kz48 hc).mp
          (show kz45 X p a c r (γ t) = 0 from ht)).1
      have hi:=ih Y D hsK' hYzero hDY hγY
      have hsigns:(∑ b ∈ s,kz59 (D b)*kz24 γ b) =
          ∑ b ∈ s,kz59 (A b)*kz24 γ b:=by
        apply Finset.sum_congr rfl
        intro b hb
        dsimp only [D]
        rw [kz60 (hdc b hb)]
      rw [Finset.sum_insert ha]
      have hrem:=kz57 X.continuous hr hc hlocal γ hloop hγa hγ
      change kz18 (X.comp γ) = (if p then (1:ℤ) else -1)*kz24 γ a +
        kz18 (Y.comp γ) at hrem
      rw [hrem,hsign,hi,hsigns]
lemma kz62 {f:ℂ → ℂ} {s:Set ℂ}
    (hs:MeasurableSet s) (hf:∀ z ∈ s,ContDiffAt ℝ 1 f z)
    (hreg:∀ z ∈ s,LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0) :
    ∃ p:ℕ → Set ℂ,(∀ n,MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧ (⋃ n,p n) = s ∧ ∀ n,InjOn f (p n):=by
  classical
  have hlocal (z:s):∃ U:Set ℂ,IsOpen U ∧ (z:ℂ) ∈ U ∧ InjOn f U:=by
    let e:ℂ ≃L[ℝ] ℂ :=
      (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr (hreg z z.2))).toContinuousLinearEquiv
    have he:(e:ℂ →L[ℝ] ℂ) = fderiv ℝ f z:=by
      ext v
      exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr (hreg z z.2)) v
    have hd:=(hf z z.2).hasStrictFDerivAt (by norm_num)
    rw [← he] at hd
    let e':=hd.toOpenPartialHomeomorph f
    exact ⟨e'.source,e'.open_source,hd.mem_toOpenPartialHomeomorph_source,e'.injOn⟩
  choose U hUo hUz hUi using hlocal
  by_cases he:s = ∅
  · subst s
    exact ⟨fun _ => ∅,by simp,by simp [Pairwise],by simp,by simp⟩
  · have:Nonempty s:=Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j,hj⟩:=(show IsLindelof s from HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
      U hUo (fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hUz ⟨z,hz⟩⟩)
    let q:ℕ → Set ℂ:=fun n => s ∩ U (j n)
    refine ⟨disjointed q,?_,?_,?_,?_⟩
    · intro n
      exact MeasurableSet.disjointed (fun n => hs.inter (hUo (j n)).measurableSet) n
    · exact disjoint_disjointed q
    · rw [iUnion_disjointed]
      ext z
      simp only [mem_iUnion,mem_inter_iff,q]
      exact ⟨fun ⟨_,hz,_⟩ => hz,fun hz => by obtain ⟨n,hn⟩:=mem_iUnion.mp (hj hz); exact ⟨n,hz,hn⟩⟩
    · intro n
      exact (hUi (j n)).mono ((disjointed_subset q n).trans inter_subset_right)
def kz63 (f:ℂ → ℂ) (s:Set ℂ) (w:ℂ):ℝ≥0∞ :=
  Measure.count {z | z ∈ s ∧ f z = w}
lemma kz64 {f:ℂ → ℂ} {s:Set ℂ} (hf:InjOn f s) (w:ℂ) :
    ({z | z ∈ s ∧ f z = w}:Set ℂ).Subsingleton:=by
  intro z hz z' hz'
  exact hf hz.1 hz'.1 (hz.2.trans hz'.2.symm)
lemma kz65 {f:ℂ → ℂ} {s:Set ℂ} (hf:InjOn f s) (w:ℂ) :
    kz63 f s w = (f '' s).indicator (fun _ => (1:ℝ≥0∞)) w:=by
  classical
  by_cases hw:w ∈ f '' s
  · obtain ⟨z,hz,rfl⟩:=hw
    have he:{a | a ∈ s ∧ f a = f z} = {z}:=by
      ext a
      exact ⟨fun h => hf h.1 hz h.2,fun h => by rcases h with rfl; exact ⟨hz,rfl⟩⟩
    rw [kz63,he,Measure.count_singleton,indicator_of_mem (mem_image_of_mem f hz)]
  · have he:{a | a ∈ s ∧ f a = w} = ∅:=by
      ext a
      exact ⟨fun h => (hw ⟨a,h.1,h.2⟩).elim,False.elim⟩
    simp [kz63,he,hw]
lemma kz66 {f:ℂ → ℂ} {s:Set ℂ} {p:ℕ → Set ℂ}
    (hd:Pairwise (Disjoint on p)) (hu:(⋃ n,p n) = s) (hi:∀ n,InjOn f (p n))
    (w:ℂ):kz63 f s w =
      ∑' n,(f '' p n).indicator (fun _ => (1:ℝ≥0∞)) w:=by
  have he:{z | z ∈ s ∧ f z = w} = ⋃ n,{z | z ∈ p n ∧ f z = w}:=by
    rw [← hu]
    ext z
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  rw [kz63,he,measure_iUnion]
  · exact tsum_congr (fun n => kz65 (hi n) w)
  · exact pairwise_disjoint_mono hd (fun n => inter_subset_left)
  · intro n
    exact (kz64 (hi n) w).finite.measurableSet
lemma kz67 {f:ℂ → ℂ} {s:Set ℂ}
    (hs:MeasurableSet s) (hf:∀ z ∈ s,ContDiffAt ℝ 1 f z)
    (hreg:∀ z ∈ s,LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0) :
    Measurable (kz63 f s) ∧
      (∫⁻ z in s,ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume) =
        ∫⁻ w,kz63 f s w ∂volume:=by
  obtain ⟨p,hpm,hpd,hpu,hpi⟩:=kz62 hs hf hreg
  have hps (n):p n ⊆ s:=hpu ▸ subset_iUnion p n
  have hder (n) (z) (hz:z ∈ p n):HasFDerivWithinAt f (fderiv ℝ f z) (p n) z :=
    ((hf z (hps n hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have him (n):MeasurableSet (f '' p n) :=
    measurable_image_of_fderivWithin (hpm n) (hder n) (hpi n)
  have he:=funext (kz66 hpd hpu hpi)
  refine ⟨?_,?_⟩
  · rw [he]
    exact Measurable.tsum (fun n => measurable_const.indicator (him n))
  · calc
      (∫⁻ z in s,ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume) =
          ∑' n,∫⁻ z in p n,ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume:=by
        conv_lhs => rw [← hpu]
        exact lintegral_iUnion hpm hpd _
      _ = ∑' n,volume (f '' p n):=tsum_congr (fun n =>
        lintegral_abs_det_fderiv_eq_addHaar_image volume (hpm n) (hder n) (hpi n))
      _ = ∫⁻ w,kz63 f s w ∂volume:=by
        rw [he,lintegral_tsum]
        · apply tsum_congr
          intro n
          rw [lintegral_indicator (him n)]
          simp
        · exact fun n => (measurable_const.indicator (him n)).aemeasurable
lemma kz68 {g:ℂ → ℝ} (hg:Measurable g) (s:Set ℂ) :
    (∫⁻ z in s,ENNReal.ofReal (g z) ∂volume) =
      ∫⁻ z in {z | z ∈ s ∧ 0 < g z},ENNReal.ofReal |g z| ∂volume:=by
  classical
  have hm:MeasurableSet {z | 0 < g z}:=measurableSet_lt measurable_const hg
  have he:(fun z => ENNReal.ofReal (g z)) =
      {z | 0 < g z}.indicator (fun z => ENNReal.ofReal |g z|):=by
    funext z
    by_cases hz:0 < g z
    · simp [hz,abs_of_pos hz]
    · simp [hz,ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hz)]
  rw [he,lintegral_indicator hm,Measure.restrict_restrict hm]
  exact congrArg (fun t:Set ℂ => ∫⁻ z in t,ENNReal.ofReal |g z| ∂volume) (inter_comm _ _)
lemma kz69 {f:ℂ → ℂ} {s:Set ℂ}
    (hs:MeasurableSet s) (hf:ContDiff ℝ 1 f)
    (hj:IntegrableOn (fun z => LinearMap.det (fderiv ℝ f z).toLinearMap) s volume)
    (hcount:∀ᵐ w ∂volume,
      kz63 f {z | z ∈ s ∧ 0 < LinearMap.det (fderiv ℝ f z).toLinearMap} w ≤
      kz63 f {z | z ∈ s ∧ LinearMap.det (fderiv ℝ f z).toLinearMap < 0} w) :
    ∫ z in s,LinearMap.det (fderiv ℝ f z).toLinearMap ∂volume ≤ 0:=by
  let J:ℂ → ℝ:=fun z => LinearMap.det (fderiv ℝ f z).toLinearMap
  have hJ:Continuous J:=ContinuousLinearMap.continuous_det.comp
    (hf.continuous_fderiv (by norm_num))
  have hp:MeasurableSet {z | z ∈ s ∧ 0 < J z} :=
    hs.inter (measurableSet_lt measurable_const hJ.measurable)
  have hm:MeasurableSet {z | z ∈ s ∧ J z < 0} :=
    hs.inter (measurableSet_lt hJ.measurable measurable_const)
  have hap:=(kz67 hp (fun z _ => hf.contDiffAt)
    (fun z hz => ne_of_gt hz.2)).2
  have ham:=(kz67 hm (fun z _ => hf.contDiffAt)
    (fun z hz => ne_of_lt hz.2)).2
  have hle:(∫⁻ z in s,ENNReal.ofReal (J z) ∂volume) ≤
      ∫⁻ z in s,ENNReal.ofReal (-J z) ∂volume:=by
    rw [kz68 hJ.measurable,kz68 (g:=fun z => -J z) hJ.neg.measurable]
    simp only [neg_pos,abs_neg]
    rw [hap,ham]
    exact lintegral_mono_ae hcount
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hj]
  exact sub_nonpos.mpr (ENNReal.toReal_mono (by
    exact (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hj.neg.2).ne) hle)
lemma kz70 {K:Set ℂ} (hK:IsCompact K)
    {X:ℂ → ℂ} (hc:ContinuousOn X K)
    (hd:∀ z ∈ K,X z = 0 → DifferentiableAt ℝ X z ∧
      LinearMap.det (fderiv ℝ X z).toLinearMap ≠ 0) :
    {z | z ∈ K ∧ X z = 0}.Finite:=by
  have hZ:IsCompact {z | z ∈ K ∧ X z = 0} :=
    hK.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  apply hZ.finite
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  obtain ⟨hzD,hzd⟩:=hd z hz.1 hz.2
  let e:ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hzd)).toContinuousLinearEquiv
  have he:(e:ℂ → ℂ) = fderiv ℝ X z:=by
    funext w
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hzd) w
  have ha:∃ C,AntilipschitzWith C (fderiv ℝ X z):=by
    rw [← he]
    exact ⟨_,e.antilipschitz⟩
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [hzD.hasFDerivAt.eventually_ne ha] with w hw
  exact fun h => hw (h.2.trans hz.2.symm)
lemma kz71 {r:ℝ} (hr:0 < r) {a:ℂ} (ha:‖a‖ < r) :
    kz24 ((r:ℂ) • kz4) a = 1:=by
  let γ:C(unitInterval,ℂ):=(r:ℂ) • kz4
  have hγloop:γ 1 = γ 0:=by simp [γ]
  have hγnorm (t):‖γ t‖ = r:=by simp [γ,abs_of_pos hr]
  have hγne (t):γ t ≠ 0:=norm_pos_iff.mp (by rw [hγnorm]; exact hr)
  have hwone:kz18 γ = 1:=by
    apply kz20 hγloop
    simpa using kz8 (r:ℂ) (by exact_mod_cast hr.ne')
  unfold kz24
  rw [← hwone]
  apply kz22 hγloop (by simp) hγne
  intro t
  simpa [γ,sub_sub_cancel_left,abs_of_pos hr] using ha
lemma kz72 {f:ℂ → ℂ} (hf:Differentiable ℝ f) :
    ∀ᵐ w ∂volume,∀ z,f z = w → LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0:=by
  have hm:volume (f '' {z | LinearMap.det (fderiv ℝ f z).toLinearMap = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) (fun _ h => h)
  have ha:∀ᵐ w ∂volume,w ∉ f '' {z | LinearMap.det (fderiv ℝ f z).toLinearMap = 0} :=
    ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hm)
  filter_upwards [ha] with w hw z hz hd
  exact hw ⟨z,hd,hz⟩
lemma kz73 (s:Finset ℂ) (J:ℂ → ℝ)
    (hJ:∀ z ∈ s,J z ≠ 0) :
    (∑ z ∈ s,if 0 < J z then (1:ℤ) else -1) =
      (s.filter (fun z => 0 < J z)).card - (s.filter (fun z => J z < 0)).card:=by
  classical
  rw [← Finset.sum_boole (R:=ℤ) (fun z => 0 < J z) s,
    ← Finset.sum_boole (R:=ℤ) (fun z => J z < 0) s,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rcases lt_or_gt_of_ne (hJ z hz) with hn | hp
  · simp [hn,not_lt.mpr hn.le]
  · simp [hp,not_lt.mpr hp.le]
lemma kz74 {f:ℂ → ℂ} (hf:ContDiff ℝ 1 f)
    {r:ℝ} (hr:0 < r)
    (hw:∀ ξ,ξ ∉ f '' Metric.sphere 0 r →
      kz18 (⟨fun t => f ((r:ℂ)*kz4 t)-ξ,by fun_prop⟩) ≤ 0) :
    ∫ z in Metric.closedBall 0 r,LinearMap.det (fderiv ℝ f z).toLinearMap ∂volume ≤ 0:=by
  classical
  let J:ℂ → ℝ:=fun z => LinearMap.det (fderiv ℝ f z).toLinearMap
  have hJc:Continuous J:=ContinuousLinearMap.continuous_det.comp
    (hf.continuous_fderiv (by norm_num))
  have hd:=hf.differentiable (by norm_num)
  have hbnull:volume (f '' Metric.sphere 0 r) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      hd.differentiableOn (Measure.addHaar_sphere volume 0 r)
  apply kz69 measurableSet_closedBall hf
    (hJc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
  filter_upwards [kz72 hd,show ∀ᵐ ξ ∂volume,ξ ∉ f '' Metric.sphere 0 r from
    ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hbnull)] with ξ hξ hξb
  let X:C(ℂ,ℂ):=⟨fun z => f z-ξ,by fun_prop⟩
  have hXD (z):HasFDerivAt X (fderiv ℝ f z) z:=(hd z).hasFDerivAt.sub_const ξ
  have hfinite:{z | z ∈ Metric.closedBall 0 r ∧ X z = 0}.Finite :=
    kz70 (isCompact_closedBall 0 r) X.continuous.continuousOn
      (fun z _ hz => ⟨(hXD z).differentiableAt,by
        rw [(hXD z).fderiv]; exact hξ z (sub_eq_zero.mp hz)⟩)
  let s:=hfinite.toFinset
  have hs (z):z ∈ s ↔ z ∈ Metric.closedBall 0 r ∧ f z = ξ:=by
    simp [s,X,sub_eq_zero]
  have hinside (z) (hz:z ∈ s):‖z‖ < r:=by
    have hz':=(hs z).mp hz
    have hle:‖z‖ ≤ r:=by simpa using hz'.1
    apply lt_of_le_of_ne hle
    intro he
    exact hξb ⟨z,by simpa using he,hz'.2⟩
  let γ:C(unitInterval,ℂ):=(r:ℂ) • kz4
  have hγnorm (t):‖γ t‖ = r:=by simp [γ,abs_of_pos hr]
  have hγsphere (t):γ t ∈ Metric.sphere 0 r:=by simpa using hγnorm t
  have hγzero (t):X (γ t) ≠ 0:=by
    intro he
    exact hξb ⟨γ t,hγsphere t,sub_eq_zero.mp he⟩
  have hreg (z) (hz:z ∈ s):J z ≠ 0:=hξ z ((hs z).mp hz).2
  have hindex:=kz61 (convex_closedBall (0:ℂ) r) s X
    (fun z => fderiv ℝ f z) (fun z hz => ((hs z).mp hz).1)
    (fun z hz => by simp [hs,hz,X,sub_eq_zero])
    (fun z hz => ⟨hXD z,hreg z hz⟩) γ (by simp [γ])
    (fun t => Metric.sphere_subset_closedBall (hγsphere t)) hγzero
  have hloopindex (z) (hz:z ∈ s):kz24 γ z = 1 :=
    kz71 hr (hinside z hz)
  have hsign:(∑ z ∈ s,if 0 < J z then (1:ℤ) else -1) ≤ 0:=by
    calc
      _ = kz18 (X.comp γ):=by
        rw [hindex]
        apply Finset.sum_congr rfl
        intro z hz
        rw [hloopindex z hz,mul_one]
        rfl
      _ ≤ 0:=hw ξ hξb
  have hcard:(s.filter (fun z => 0 < J z)).card ≤ (s.filter (fun z => J z < 0)).card:=by
    rw [kz73 s J hreg] at hsign
    exact_mod_cast sub_nonpos.mp hsign
  have hp:{z | z ∈ {z | z ∈ Metric.closedBall 0 r ∧ 0 < J z} ∧ f z = ξ} =
      ↑(s.filter (fun z => 0 < J z)):=by ext z; simp [hs]; aesop
  have hn:{z | z ∈ {z | z ∈ Metric.closedBall 0 r ∧ J z < 0} ∧ f z = ξ} =
      ↑(s.filter (fun z => J z < 0)):=by ext z; simp [hs]; aesop
  change kz63 f {z | z ∈ Metric.closedBall 0 r ∧ 0 < J z} ξ ≤
    kz63 f {z | z ∈ Metric.closedBall 0 r ∧ J z < 0} ξ
  simp only [kz63,hp,hn,Measure.count_apply_finset]
  exact_mod_cast hcard
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
lemma kz75 {K U:Set ℂ} (hK:IsCompact K) (hU:IsOpen U)
    (hKU:K ⊆ U) :
    ∃ χ:ℂ → ℝ,ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K,χ =ᶠ[𝓝 z] fun _ => 1) ∧ ∀ z,χ z ∈ Icc 0 1:=by
  obtain ⟨L,hL,hLc,hKL,hLU⟩:=exists_compact_closed_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,ℂ) hK.isClosed hKL (n:=2)
  have hs:tsupport (χ:ℂ → ℝ) ⊆ L:=by
    apply closure_minimal _ hLc
    intro z hz
    by_contra hn
    exact hz (hχ0 z hn)
  refine ⟨χ,contMDiff_iff_contDiff.mp χ.contMDiff,
    hL.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans hLU,?_,hχrange⟩
  intro z hz
  exact hχ1.filter_mono (nhds_le_nhdsSet hz)
lemma kz76 {f:ℂ → ℂ} {z:ℂ} (hd:DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ f z).toLinearMap = ‖deriv f z‖^2:=by
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv,kz12,
    ← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,one_mul,
    Complex.I_mul,Complex.normSq_apply]
  ring
lemma kz77 {K U:Set ℂ} (hK:IsCompact K)
    (hU:IsOpen U) (hKU:K ⊆ U) {x:ℂ → ℂ}
    (hx:∀ z ∈ U,ContDiffAt ℝ 2 x z) :
    ∃ X:ℂ → ℂ,ContDiff ℝ 2 X ∧ ∀ z ∈ K,X =ᶠ[𝓝 z] x:=by
  obtain ⟨χ,hχc,_hχK,hχU,hχ1,_hχrange⟩:=kz75 hK hU hKU
  let X:=fun z => (χ z:ℂ)*x z
  have hX:ContDiff ℝ 2 X:=by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz:z ∈ tsupport χ
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hχc.contDiffAt).mul (hx z (hχU hz))
    · have he:X =ᶠ[𝓝 z] fun _ => 0:=by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
        have hzero:χ w = 0:=notMem_support.mp (fun h => hw (subset_tsupport χ h))
        simp only [X,hzero,Complex.ofReal_zero,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨X,hX,?_⟩
  intro z hz
  filter_upwards [hχ1 z hz] with w hw
  simp only [X,hw,Complex.ofReal_one,one_mul]
lemma kz78 {h H:ℂ → ℂ}
    (hh:DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH:DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef:∀ z ∈ Metric.ball (0:ℂ) 1,z ≠ 0 → H z = z⁻¹+h z)
    (hHd:∀ z ∈ Metric.ball (0:ℂ) 1 \ {0},deriv H z ≠ 0)
    (hHi:InjOn H (Metric.ball 0 1 \ {0}))
    {r:ℝ} (hr:0 < r) (hr1:r < 1) (ξ:ℂ)
    (hξ:ξ ∉ H '' Metric.sphere 0 r) :
    kz18 (⟨fun t => H ((r:ℂ)*kz4 t)-ξ,by
      refine Continuous.sub ?_ continuous_const
      apply hH.continuousOn.comp_continuous (by fun_prop)
      intro t
      have he:‖(r:ℂ)*kz4 t‖ = r:=by simp [abs_of_pos hr]
      constructor
      · rw [Metric.mem_ball,dist_zero_right,he]
        exact hr1
      · change (r:ℂ)*kz4 t ≠ 0
        exact norm_pos_iff.mp (by rw [he]; exact hr)⟩) ≤ 0:=by
  classical
  let U:Set ℂ:=Metric.ball 0 1
  let K:Set ℂ:=Metric.closedBall 0 r
  have hKU:K ⊆ U:=Metric.closedBall_subset_ball hr1
  let x:ℂ → ℂ:=fun z => 1+z*(h z-ξ)
  have hx (z) (hz:z ∈ U):AnalyticAt ℂ x z:=by
    exact analyticAt_const.add (analyticAt_id.mul ((hh.analyticOnNhd Metric.isOpen_ball z hz).sub analyticAt_const))
  obtain ⟨X,hXc,hX⟩:=kz77 (isCompact_closedBall 0 r)
    Metric.isOpen_ball hKU (fun z hz => (hx z hz).contDiffAt.restrict_scalars ℝ)
  have hXval (z) (hz:z ∈ K):X z = x z:=(hX z hz).self_of_nhds
  have hxzero {z} (hz:z ∈ U):x z = 0 ↔ z ≠ 0 ∧ H z = ξ:=by
    by_cases hz0:z = 0
    · simp [x,hz0]
    · rw [hdef z hz hz0]
      dsimp [x]
      field_simp
      constructor <;> intro he
      · exact ⟨hz0,by linear_combination he⟩
      · linear_combination he.2
  have hss:{z | z ∈ K ∧ X z = 0}.Subsingleton:=by
    intro z hz w hw
    obtain ⟨hz0,hzξ⟩:=(hxzero (hKU hz.1)).mp ((hXval z hz.1) ▸ hz.2)
    obtain ⟨hw0,hwξ⟩:=(hxzero (hKU hw.1)).mp ((hXval w hw.1) ▸ hw.2)
    exact hHi ⟨hKU hz.1,hz0⟩ ⟨hKU hw.1,hw0⟩ (hzξ.trans hwξ.symm)
  let s:=hss.finite.toFinset
  have hs (z):z ∈ s ↔ z ∈ K ∧ X z = 0:=by simp [s]
  have hder (z) (hz:z ∈ s):DifferentiableAt ℂ X z ∧ deriv X z ≠ 0:=by
    have hzK:=((hs z).mp hz).1
    have hzero:=((hs z).mp hz).2
    obtain ⟨hz0,hzξ⟩:=(hxzero (hKU hzK)).mp (by rwa [hXval z hzK] at hzero)
    have hUz:z ∈ Metric.ball (0:ℂ) 1 \ {0}:=⟨hKU hzK,hz0⟩
    have hHd':=(hH z hUz).differentiableAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hUz)
    have heq:x =ᶠ[𝓝 z] fun w => w*(H w-ξ):=by
      filter_upwards [(Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hUz] with w hw
      have hw0:w ≠ 0:=hw.2
      rw [hdef w hw.1 hw0]
      dsimp [x]
      field_simp [hw0]
      ring
    have hD:HasDerivAt X (z*deriv H z) z:=by
      have hD:=(hasDerivAt_id z).mul (hHd'.hasDerivAt.sub_const ξ)
      simp only [hzξ,sub_self,mul_zero,zero_add] at hD
      exact hD.congr_of_eventuallyEq ((hX z hzK).trans heq)
    exact ⟨hD.differentiableAt,hD.deriv ▸ mul_ne_zero hz0 (hHd z hUz)⟩
  let γ:C(unitInterval,ℂ):=(r:ℂ) • kz4
  have hγnorm (t):‖γ t‖ = r:=by simp [γ,abs_of_pos hr]
  have hγK (t):γ t ∈ K:=by simpa [K] using (hγnorm t).le
  have hγU (t):γ t ∈ U:=hKU (hγK t)
  have hγ0 (t):γ t ≠ 0:=norm_pos_iff.mp (by rw [hγnorm]; exact hr)
  have hγξ (t):H (γ t) ≠ ξ:=fun he => hξ ⟨γ t,by simpa using hγnorm t,he⟩
  let Y:C(ℂ,ℂ):=⟨X,hXc.continuous⟩
  have hXY (t):Y (γ t) = γ t*(H (γ t)-ξ):=by
    rw [show Y (γ t) = X (γ t) from rfl,hXval _ (hγK t),hdef _ (hγU t) (hγ0 t)]
    dsimp only [x]
    field_simp [hγ0 t]
    ring
  have hγnonzero (t):Y (γ t) ≠ 0:=by rw [hXY]; exact mul_ne_zero (hγ0 t) (sub_ne_zero.mpr (hγξ t))
  have hi:=kz61 (convex_closedBall (0:ℂ) r) s Y
    (fun z => fderiv ℝ X z) (fun z hz => ((hs z).mp hz).1)
    (fun z hz => by simp [hs,show z ∈ K from hz,Y])
    (fun z hz => ⟨((hder z hz).1.restrictScalars ℝ).hasFDerivAt,by
      rw [kz76 (hder z hz).1]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hder z hz).2)⟩)
    γ (by simp [γ]) hγK hγnonzero
  have hins (z) (hz:z ∈ s):‖z‖ < r:=by
    have hzK:=((hs z).mp hz).1
    have hle:‖z‖ ≤ r:=by simpa [K] using hzK
    refine lt_of_le_of_ne hle ?_
    intro he
    have hzero:=((hs z).mp hz).2
    have hzξ:=((hxzero (hKU hzK)).mp (by rwa [hXval z hzK] at hzero)).2
    exact hξ ⟨z,by simpa using he,hzξ⟩
  have hi':kz18 (Y.comp γ) = (s.card:ℤ):=by
    rw [hi]
    calc
      _ = ∑ _z ∈ s,(1:ℤ):=by
        apply Finset.sum_congr rfl
        intro z hz
        rw [kz71 hr (hins z hz),mul_one]
        simp only [kz59,kz76 (hder z hz).1,
          sq_pos_of_pos (norm_pos_iff.mpr (hder z hz).2),ite_true]
      _ = ↑s.card:=by simp
  have hcard:s.card ≤ 1:=Finset.card_le_one.mpr (by
    intro z hz w hw
    exact hss ((hs z).mp hz) ((hs w).mp hw))
  let η:C(unitInterval,ℂ):=⟨fun t => H (γ t)-ξ,by
    refine Continuous.sub ?_ continuous_const
    apply hH.continuousOn.comp_continuous γ.continuous
    exact fun t => ⟨hγU t,hγ0 t⟩⟩
  have he:Y.comp γ = γ*η:=by ext t; exact hXY t
  have hwγ:kz18 γ = 1:=by
    apply kz20 (by simp [γ])
    simpa [γ] using kz8 (r:ℂ) (by exact_mod_cast hr.ne')
  rw [he,kz21 γ η (by simp [γ]) (by simp [η,γ]) hγ0
    (fun t => sub_ne_zero.mpr (hγξ t)),hwγ] at hi'
  change kz18 η ≤ 0
  have hc:(s.card:ℤ) ≤ 1:=by exact_mod_cast hcard
  omega
lemma kz79 {h:ℂ → ℂ} {z:ℂ}
    (hh:DifferentiableAt ℂ h z) (a:ℝ) :
    LinearMap.det (fderiv ℝ (fun w => a • conj w+h w) z).toLinearMap =
      ‖deriv h z‖^2-a^2:=by
  have hD:=(Complex.conjCLE.hasFDerivAt.const_smul a).add
    (hh.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  change HasFDerivAt (fun w => a • conj w+h w) _ z at hD
  rw [hD.fderiv,kz12,← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,add_apply,
    smul_apply,ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,one_mul,Complex.real_smul,Complex.normSq_apply]
  simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  ring
lemma kz80 {h H:ℂ → ℂ}
    (hh:DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH:DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef:∀ z ∈ Metric.ball (0:ℂ) 1,z ≠ 0 → H z = z⁻¹+h z)
    (hHd:∀ z ∈ Metric.ball (0:ℂ) 1 \ {0},deriv H z ≠ 0)
    (hHi:InjOn H (Metric.ball 0 1 \ {0}))
    {r:ℝ} (hr:0 < r) (hr1:r < 1) :
    ∫ z in Metric.closedBall 0 r,‖deriv h z‖^2 ∂volume ≤
      volume.real (Metric.closedBall (0:ℂ) r) * (r^2)⁻¹^2:=by
  let K:Set ℂ:=Metric.closedBall 0 r
  let x:ℂ → ℂ:=fun z => (r^2)⁻¹ • conj z+h z
  have hKU:K ⊆ Metric.ball 0 1:=Metric.closedBall_subset_ball hr1
  have hx (z) (hz:z ∈ Metric.ball (0:ℂ) 1):ContDiffAt ℝ 2 x z:=by
    exact (Complex.conjCLE.contDiff.contDiffAt.const_smul (r^2)⁻¹).add
      ((hh.analyticOnNhd Metric.isOpen_ball z hz).contDiffAt.restrict_scalars ℝ)
  obtain ⟨X,hXc,hX⟩:=kz77 (isCompact_closedBall 0 r)
    Metric.isOpen_ball hKU hx
  have hXval (z) (hz:z ∈ K):X z = x z:=(hX z hz).self_of_nhds
  have hb (z) (hz:z ∈ Metric.sphere (0:ℂ) r):X z = H z:=by
    have hn:‖z‖ = r:=by simpa using hz
    have hz0:z ≠ 0:=norm_pos_iff.mp (by rw [hn];exact hr)
    rw [hXval z (Metric.sphere_subset_closedBall hz),hdef z (hKU (Metric.sphere_subset_closedBall hz)) hz0]
    dsimp [x]
    rw [Complex.inv_def,Complex.normSq_eq_norm_sq,hn]
    congr 1
    simp [mul_comm]
  have hw (ξ) (hξ:ξ ∉ X '' Metric.sphere 0 r) :
      kz18 (⟨fun t => X ((r:ℂ)*kz4 t)-ξ,by fun_prop⟩) ≤ 0:=by
    have hξ':ξ ∉ H '' Metric.sphere 0 r:=by
      rintro ⟨z,hz,hzξ⟩
      exact hξ ⟨z,hz,(hb z hz).trans hzξ⟩
    have hw:=kz78 hh hH hdef hHd hHi hr hr1 ξ hξ'
    convert hw using 2
    ext t
    change X ((r:ℂ)*kz4 t)-ξ = H ((r:ℂ)*kz4 t)-ξ
    rw [hb _ (by simp [abs_of_pos hr])]
  have hi:=kz74
    (hXc.of_le (by norm_num)) hr hw
  have hdet (z) (hz:z ∈ K) :
      LinearMap.det (fderiv ℝ X z).toLinearMap = ‖deriv h z‖^2-(r^2)⁻¹^2:=by
    rw [(hX z hz).fderiv_eq]
    exact kz79
      ((hh z (hKU hz)).differentiableAt (Metric.isOpen_ball.mem_nhds (hKU hz))) _
  have hdcont:ContinuousOn (deriv h) K :=
    (hh.deriv Metric.isOpen_ball).continuousOn.mono hKU
  have hint:IntegrableOn (fun z => ‖deriv h z‖^2) K :=
    (hdcont.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)
  have hconst:IntegrableOn (fun _:ℂ => (r^2)⁻¹^2) K :=
    integrableOn_const (isCompact_closedBall 0 r).measure_ne_top
  have he:(∫ z in K,LinearMap.det (fderiv ℝ X z).toLinearMap) =
      (∫ z in K,‖deriv h z‖^2) - volume.real K * (r^2)⁻¹^2:=by
    rw [setIntegral_congr_fun measurableSet_closedBall hdet,
      integral_sub hint hconst]
    simp
  rw [he] at hi
  exact sub_nonpos.mp hi
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
lemma kz81 (r θ:ℝ) :
    Complex.polarCoord.symm (r,θ) = circleMap 0 r θ:=by
  rw [Complex.polarCoord_symm_apply,circleMap,zero_add]
  congr 1
  rw [Complex.exp_mul_I]
  simp
lemma kz82 (f:ℂ → ℂ) (c:ℂ) (r:ℝ) :
    Real.circleAverage f c r =
      (2*Real.pi)⁻¹ • ∫ θ in -Real.pi..Real.pi,f (circleMap c r θ):=by
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ))]
  congr 2 <;> ring
lemma kz83 {f:ℂ → ℂ} {R:ℝ} (hR:0 < R)
    (hf:ContinuousOn f (Metric.closedBall 0 R)) :
    ∫ z in Metric.ball (0:ℂ) R,f z =
      ∫ r in (0:ℝ)..R,(2*Real.pi*r) • Real.circleAverage f 0 r:=by
  let g:ℝ × ℝ → ℂ:=fun p => p.1 • f (Complex.polarCoord.symm p)
  have hg:IntegrableOn g (Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi):=by
    refine (show IntegrableOn g (Icc (0:ℝ) R ×ˢ Icc (-Real.pi) Real.pi) from ?_).mono_set ?_
    · apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hpolar:Continuous (fun p:ℝ × ℝ => Complex.polarCoord.symm p):=by
        simp only [Complex.polarCoord_symm_apply]
        fun_prop
      apply continuousOn_fst.smul (hf.comp hpolar.continuousOn ?_)
      intro p hp
      simp only [Metric.mem_closedBall,dist_zero_right,Complex.norm_polarCoord_symm]
      exact (abs_of_nonneg hp.1.1).trans_le hp.1.2
    · exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  calc
    _ = ∫ p in polarCoord.target,
        p.1 • (Metric.ball (0:ℂ) R).indicator f (Complex.polarCoord.symm p):=by
      rw [Complex.integral_comp_polarCoord_symm,
        integral_indicator Metric.isOpen_ball.measurableSet]
    _ = ∫ p in Ioo (0:ℝ) R ×ˢ Ioo (-Real.pi) Real.pi,g p:=by
      rw [polarCoord_target]
      have heq:(fun p:ℝ × ℝ => p.1 •
          (Metric.ball (0:ℂ) R).indicator f (Complex.polarCoord.symm p)) =ᶠ[
          ae (volume.restrict (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi))]
        (Iio R ×ˢ (univ:Set ℝ)).indicator g:=by
        filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
        have hp0:0 < p.1:=hp.1
        have hn:‖Complex.polarCoord.symm p‖ = p.1:=by
          rw [Complex.norm_polarCoord_symm,abs_of_pos hp0]
        by_cases hr:p.1 < R
        · rw [indicator_of_mem (by simpa [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos hp0] using hr),
            indicator_of_mem (show p ∈ Iio R ×ˢ (univ:Set ℝ) from ⟨hr,mem_univ _⟩)]
        · rw [indicator_of_notMem (by simpa [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos hp0] using hr),
            indicator_of_notMem (show p ∉ Iio R ×ˢ (univ:Set ℝ) from fun h => hr h.1),smul_zero]
      rw [integral_congr_ae heq,
        integral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
      rw [Measure.restrict_restrict (measurableSet_Iio.prod MeasurableSet.univ)]
      congr 2
      ext p
      simp only [mem_inter_iff,mem_prod,mem_Ioi,mem_Iio,mem_Ioo,mem_univ,and_true]
      tauto
    _ = ∫ r in Ioo (0:ℝ) R,∫ θ in Ioo (-Real.pi) Real.pi,g (r,θ):=by
      exact setIntegral_prod _ (by simpa only [← Measure.volume_eq_prod] using hg)
    _ = ∫ r in (0:ℝ)..R,(2*Real.pi*r) • Real.circleAverage f 0 r:=by
      rw [intervalIntegral.integral_of_le hR.le,integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [kz82,
        intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
        integral_Ioc_eq_integral_Ioo,← smul_assoc]
      have he:(2*Real.pi*r) * (2*Real.pi)⁻¹ = r:=by
        field_simp
      rw [smul_eq_mul,he,← integral_smul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ hθ
      simp only [g,kz81]
lemma kz84 (r:ℝ) :
    Metric.ball (0:ℂ) r =ᵐ[volume] Metric.closedBall 0 r:=by
  apply ae_eq_set.mpr
  constructor
  · rw [sdiff_eq_empty.mpr Metric.ball_subset_closedBall,measure_empty]
  · rw [Metric.closedBall_sdiff_ball]
    exact Measure.addHaar_sphere volume 0 r
lemma kz85 {f:ℂ → ℂ} {R r:ℝ}
    (hf:DifferentiableOn ℂ f (Metric.ball (0:ℂ) R))
    (hr:0 < r) (hrR:r < R) :
    ∫ z in Metric.ball (0:ℂ) r,f z = volume.real (Metric.ball (0:ℂ) r) • f 0:=by
  have hfc:ContinuousOn f (Metric.closedBall 0 r) :=
    hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  rw [kz83 hr hfc]
  have hm (t:ℝ) (ht:t ∈ Ioo 0 r):Real.circleAverage f 0 t = f 0:=by
    apply DiffContOnCl.circleAverage
    rw [abs_of_pos ht.1]
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 ht.1.ne']
    exact hf.mono (Metric.closedBall_subset_ball (ht.2.trans hrR))
  have hc:=kz83 (f:=fun _:ℂ => f 0) hr continuousOn_const
  rw [setIntegral_const] at hc
  rw [hc]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hr.le] at ht
  by_cases ht0:t = 0
  · simp [ht0]
  have htpos:0 < t:=lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have ht':t ∈ Ioo 0 r ∨ t = r:=by
    exact (lt_or_eq_of_le ht.2).elim (fun h => Or.inl ⟨htpos,h⟩) Or.inr
  have hmf:Real.circleAverage f 0 t = f 0:=by
    rcases ht' with ht' | rfl
    · exact hm t ht'
    · apply DiffContOnCl.circleAverage
      rw [abs_of_pos hr]
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball 0 hr.ne']
      exact hf.mono (Metric.closedBall_subset_ball hrR)
  simp only [hmf,Real.circleAverage_const]
lemma kz86 {f:ℂ → ℂ} {R r:ℝ}
    (hf:DifferentiableOn ℂ f (Metric.ball (0:ℂ) R))
    (hr:0 < r) (hrR:r < R) :
    ∫ z in Metric.closedBall (0:ℂ) r,f z =
      volume.real (Metric.closedBall (0:ℂ) r) • f 0:=by
  rw [← setIntegral_congr_set (kz84 r),
    kz85 hf hr hrR]
  congr 1
  exact congrArg ENNReal.toReal (measure_congr (kz84 r))
lemma kz87 {f:ℂ → ℂ} {R r:ℝ}
    (hf:DifferentiableOn ℂ f (Metric.ball (0:ℂ) R))
    (hr:0 < r) (hrR:r < R) :
    volume.real (Metric.closedBall (0:ℂ) r) * ‖f 0‖^2 ≤
      ∫ z in Metric.closedBall (0:ℂ) r,‖f z‖^2:=by
  let K:Set ℂ:=Metric.closedBall 0 r
  have hfc:ContinuousOn f K:=hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  have hfi:IntegrableOn f K:=hfc.integrableOn_compact (isCompact_closedBall 0 r)
  have hf2i:IntegrableOn (fun z => ‖f z‖^2) K :=
    (hfc.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)
  have hconst:IntegrableOn (fun _:ℂ => ‖f 0‖^2) K :=
    integrableOn_const (isCompact_closedBall 0 r).measure_ne_top
  have hnonneg:0 ≤ ∫ z in K,‖f z-f 0‖^2:=integral_nonneg (fun _ => sq_nonneg _)
  have he:(fun z => ‖f z-f 0‖^2) =
      (fun z => ‖f z‖^2-2*inner ℝ (f 0) (f z)+‖f 0‖^2):=by
    funext z
    rw [norm_sub_sq_real,real_inner_comm]
  have hsub:IntegrableOn (fun z => ‖f z‖^2-2*inner ℝ (f 0) (f z)) K :=
    hf2i.sub ((hfi.const_inner (f 0)).const_mul 2)
  have hinner:IntegrableOn (fun z => 2*inner ℝ (f 0) (f z)) K :=
    (hfi.const_inner (f 0)).const_mul 2
  rw [he,integral_add hsub hconst,
    integral_sub hf2i hinner,
    integral_const_mul,integral_inner hfi,setIntegral_const,
    kz86 hf hr hrR,real_inner_smul_right,
    real_inner_self_eq_norm_sq,smul_eq_mul] at hnonneg
  dsimp only [K] at hnonneg ⊢
  linarith
lemma kz88 {h H:ℂ → ℂ}
    (hh:DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH:DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef:∀ z ∈ Metric.ball (0:ℂ) 1,z ≠ 0 → H z = z⁻¹+h z)
    (hHd:∀ z ∈ Metric.ball (0:ℂ) 1 \ {0},deriv H z ≠ 0)
    (hHi:InjOn H (Metric.ball 0 1 \ {0})):‖deriv h 0‖ ≤ 1:=by
  have hb (r:ℝ) (hr:0 < r) (hr1:r < 1):‖deriv h 0‖^2 ≤ (r^2)⁻¹^2:=by
    have hM:0 < volume.real (Metric.closedBall (0:ℂ) r):=by
      rw [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr.le,ENNReal.coe_toReal]
      exact mul_pos (sq_pos_of_pos hr) Real.pi_pos
    have hle:=(kz87 (hh.deriv Metric.isOpen_ball) hr hr1).trans
      (kz80 hh hH hdef hHd hHi hr hr1)
    nlinarith
  have ht:Tendsto (fun r:ℝ => (r^2)⁻¹^2) (𝓝[<] (1:ℝ)) (𝓝 1):=by
    have hc:ContinuousAt (fun r:ℝ => (r^2)⁻¹^2) 1 :=
      ((continuousAt_id.pow 2).inv₀ (by norm_num)).pow 2
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsq:‖deriv h 0‖^2 ≤ 1:=by
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r:ℝ in 𝓝[<] (1:ℝ),0 < r from
        nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num:(0:ℝ)<1)))] with r hr1 hr
    exact hb r hr hr1
  nlinarith [norm_nonneg (deriv h 0)]
lemma kz89 {f:ℂ → ℂ} {U:Set ℂ}
    (hU:IsOpen U) (hf:Set.InjOn f U) {a:ℂ} (ha:a ∈ U) :
    ¬ ∀ᶠ z in 𝓝 a,f z = f a:=by
  intro hc
  have heq:∀ᶠ z in 𝓝 a,z = a:=by
    filter_upwards [hc,hU.mem_nhds ha] with z hz hzU
    exact hf hzU ha hz
  have heq':∀ᶠ z in 𝓝[≠] a,z = a:=heq.filter_mono nhdsWithin_le_nhds
  have hne':∀ᶠ z in 𝓝[≠] a,z ≠ a:=self_mem_nhdsWithin
  obtain ⟨z,hz,hne⟩:=(heq'.and hne').exists
  exact hne hz
lemma kz90 {f:ℂ → ℂ} {U:Set ℂ}
    (hU:IsOpen U) (hf:kz1 f U) {a:ℂ} (ha:a ∈ U) :
    ContinuousAt (Function.invFunOn f U) (f a):=by
  have haan:AnalyticAt ℂ f a:=(hf.1.analyticOnNhd hU) a ha
  have hopen:𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    haan.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (kz89 hU hf.2 ha)
  have hl:∀ᶠ z in 𝓝 a,Function.invFunOn f U (f z) = z:=by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have ht:Tendsto (Function.invFunOn f U ∘ f) (𝓝 a) (𝓝 a) :=
    tendsto_id.congr' (Filter.EventuallyEq.symm hl)
  rw [ContinuousAt,hf.2.leftInvOn_invFunOn ha]
  exact (tendsto_map'_iff.mpr ht).mono_left hopen
lemma kz91 {f:ℂ → ℂ} {U:Set ℂ}
    (hU:IsOpen U) (hf:kz1 f U) {a:ℂ} (ha:a ∈ U) :
    deriv f a ≠ 0:=by
  have han:AnalyticAt ℂ f a:=hf.1.analyticOnNhd hU a ha
  have hd_nonconst:¬ ∀ᶠ z in 𝓝 a,deriv f z = 0:=by
    intro hc
    obtain ⟨r,hr,hball⟩:=Metric.mem_nhds_iff.mp (hc.and (hU.mem_nhds ha))
    have hfball:DifferentiableOn ℂ f (Metric.ball a r) :=
      hf.1.mono (fun z hz => (hball hz).2)
    have hcball:∀ z ∈ Metric.ball a r,f z = f a:=by
      intro z hz
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
        hfball (fun w hw => (hball hw).1) hz (Metric.mem_ball_self hr)
    apply kz89 hU hf.2 ha
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz
    exact hcball z hz
  have hd:∀ᶠ z in 𝓝[≠] a,deriv f z ≠ 0 :=
    han.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left hd_nonconst
  let g:=Function.invFunOn f U
  have hgc:ContinuousAt g (f a):=kz90 hU hf ha
  have hga:g (f a) = a:=hf.2.leftInvOn_invFunOn ha
  have hopen:𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    han.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (kz89 hU hf.2 ha)
  have hright:∀ᶠ w in 𝓝 (f a),g w ∈ U ∧ f (g w) = w:=by
    apply (hopen (Filter.mem_map.mpr ?_))
    filter_upwards [hU.mem_nhds ha] with z hz
    exact ⟨Function.invFunOn_apply_mem hz,Function.invFunOn_apply_eq hz⟩
  have hgne:∀ᶠ w in 𝓝[≠] (f a),g w ≠ a:=by
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
      with w hw hwne
    intro heq
    exact hwne (hw.2.symm.trans (congrArg f heq))
  have hgt:Tendsto g (𝓝[≠] (f a)) (𝓝[≠] a):=by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,hgne⟩
    simpa only [hga] using (hgc.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto g (𝓝[≠] (f a)) (𝓝 (g (f a))))
  have hgd:∀ᶠ w in 𝓝[≠] (f a),DifferentiableAt ℂ g w:=by
    filter_upwards [hgt.eventually hd,hright.filter_mono nhdsWithin_le_nhds]
      with w hwder hw
    have hwan:AnalyticAt ℂ f (g w):=hf.1.analyticOnNhd hU (g w) hw.1
    have hws:HasStrictDerivAt f (deriv f (g w)) (g w) :=
      (hwan.contDiffAt (n:=1)).hasStrictDerivAt (by norm_num)
    have hl:∀ᶠ z in 𝓝 (g w),g (f z) = z:=by
      filter_upwards [hU.mem_nhds hw.1] with z hz
      exact hf.2.leftInvOn_invFunOn hz
    simpa [hw.2] using (hws.to_local_left_inverse hwder hl).hasDerivAt.differentiableAt
  have hgan:=Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hgd hgc
  have hcomp:=hgan.differentiableAt.hasDerivAt.comp a han.differentiableAt.hasDerivAt
  have hid:(fun z => g (f z)) =ᶠ[𝓝 a] id:=by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have hprod:deriv g (f a) * deriv f a = 1:=by
    simpa using (hcomp.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id a)
  intro hzero
  simp [hzero] at hprod
lemma kz92 {q F:ℂ → ℂ} {z:ℂ}
    (hq:ContinuousAt q z) (hF:DifferentiableAt ℂ F z)
    (hroot:(fun w => q w^2) =ᶠ[𝓝 z] F) (hq0:q z ≠ 0) :
    DifferentiableAt ℂ q z:=by
  have hp:HasStrictDerivAt (fun w:ℂ => w^2) (2*q z) (q z):=by
    have hp:=(hasStrictDerivAt_id (q z)).pow 2
    change HasStrictDerivAt (fun w:ℂ => w^2) _ (q z) at hp
    simpa only [id_eq,Nat.reduceSub,pow_one,Nat.cast_ofNat,mul_one] using hp
  have hn:2*q z ≠ 0:=mul_ne_zero (by norm_num) hq0
  let p:=hp.localInverse _ _ _ hn
  have hpD:DifferentiableAt ℂ p (F z):=by
    rw [← hroot.self_of_nhds]
    exact (hp.to_localInverse hn).hasDerivAt.differentiableAt
  have he:q =ᶠ[𝓝 z] fun w => p (F w):=by
    filter_upwards [hq.tendsto.eventually (hp.eventually_left_inverse hn),hroot] with w hw hwF
    exact (hwF ▸ hw).symm
  exact (hpD.comp z hF).congr_of_eventuallyEq he
lemma kz93 {F:ℂ → ℂ}
    (hF:DifferentiableOn ℂ F disk) (hF0:∀ z ∈ disk,F z ≠ 0)
    (hFone:F 0 = 1) :
    ∃ q:ℂ → ℂ,DifferentiableOn ℂ q disk ∧ q 0 = 1 ∧
      (∀ z ∈ disk,q z^2 = F z) ∧ ∀ z ∈ disk,q z ≠ 0:=by
  have hdz:(0:ℂ) ∈ disk:=by simp [disk]
  have hsim:IsSimplyConnected disk:=by
    have:ContractibleSpace disk:=(convex_ball (0:ℂ) (1:ℝ)).contractibleSpace ⟨0,hdz⟩
    change SimplyConnectedSpace disk
    exact inferInstance
  obtain ⟨q,hqc,hq⟩:=Complex.exists_continuousOn_pow_eq hsim Metric.isOpen_ball hF.continuousOn
    (by rintro ⟨z,hz,he⟩;exact hF0 z hz he) (n:=2) (by norm_num)
  have hqn (z) (hz:z ∈ disk):q z ≠ 0:=by
    intro he
    have:=hq z
    rw [he,zero_pow (by norm_num)] at this
    exact hF0 z hz this.symm
  have hqd:DifferentiableOn ℂ q disk:=by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply kz92
      (hqc.continuousAt (Metric.isOpen_ball.mem_nhds hz))
      ((hF z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz))
      (Filter.Eventually.of_forall hq) (hqn z hz)
  let Q:ℂ → ℂ:=fun z => q z / q 0
  refine ⟨Q,hqd.div_const _,by simp [Q,hqn 0 hdz],?_,?_⟩
  · intro z hz
    simp only [Q,div_pow,hq,hFone,div_one]
  · intro z hz
    exact div_ne_zero (hqn z hz) (hqn 0 hdz)
lemma kz94 (f:ℂ → ℂ) (z:ℂ) :
    z * dslope f 0 z = f z-f 0:=by
  simpa only [sub_zero,smul_eq_mul] using sub_smul_dslope f 0 z
lemma kz95 {z:ℂ} (hz:z ∈ disk):z^2 ∈ disk:=by
  have hn:‖z‖ < 1:=by simpa [disk] using hz
  simpa [disk] using pow_lt_one₀ (norm_nonneg z) hn (by norm_num:2 ≠ 0)
lemma kz96 {f:ℂ → ℂ} (hf:kz2 f) :
    ∃ q g h H:ℂ → ℂ,
      DifferentiableOn ℂ q disk ∧ q 0 = 1 ∧
      (∀ z ∈ disk,q z ≠ 0) ∧
      (∀ z ∈ disk,q z^2 = dslope f 0 z) ∧
      (∀ z,g z = z*q (z^2)) ∧
      kz1 g disk ∧ g 0 = 0 ∧
      DifferentiableOn ℂ h disk ∧ deriv h 0 = -deriv q 0 ∧
      (∀ z ∈ disk,z ≠ 0 → H z = z⁻¹+h z) ∧
      kz1 H (disk \ {0}) ∧
      deriv (deriv f) 0 = 4*deriv q 0:=by
  have hdz:(0:ℂ) ∈ disk:=by simp [disk]
  let F:=dslope f 0
  have hFd:DifferentiableOn ℂ F disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hf.1.1
  have hFn (z) (hz:z ∈ disk):F z ≠ 0:=by
    by_cases hz0:z = 0
    · simpa [F,hz0] using (show deriv f 0 ≠ 0 by rw [hf.2.2];norm_num)
    · intro he
      have hfact:=kz94 f z
      change z*F z = f z-f 0 at hfact
      rw [he,mul_zero] at hfact
      exact hz0 (hf.1.2 hz hdz (sub_eq_zero.mp hfact.symm))
  obtain ⟨q,hqd,hq0,hqs,hqn⟩:=kz93 hFd hFn (by simpa [F] using hf.2.2)
  let Q:=dslope q 0
  have hQd:DifferentiableOn ℂ Q disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hqd
  let g:ℂ → ℂ:=fun z => z*q (z^2)
  let h:ℂ → ℂ:=fun z => -z*Q (z^2)/q (z^2)
  let H:ℂ → ℂ:=fun z => (g z)⁻¹
  have hgd:DifferentiableOn ℂ g disk:=by
    exact differentiableOn_id.mul (hqd.comp (differentiableOn_id.pow 2) (fun z hz => kz95 hz))
  have hgs (z) (hz:z ∈ disk):g z^2 = f (z^2):=by
    dsimp only [g]
    rw [mul_pow,hqs _ (kz95 hz)]
    simpa [F,hf.2.1] using kz94 f (z^2)
  have hgn (z) (hz:z ∈ disk) (hz0:z ≠ 0):g z ≠ 0 :=
    mul_ne_zero hz0 (hqn _ (kz95 hz))
  have hgi:InjOn g disk:=by
    intro z hz w hw he
    have hsq:z^2 = w^2:=hf.1.2 (kz95 hz) (kz95 hw)
      ((hgs z hz).symm.trans ((congrArg (fun t => t^2) he).trans (hgs w hw)))
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · exact heq
    · have hgneg:g z = -g w:=by simp [g,heq]
      have hw0:w = 0:=by
        by_contra hn
        exact hgn w hw hn (by linear_combination (he.symm+hgneg)/2)
      simpa [hw0] using heq
  have hhd:DifferentiableOn ℂ h disk:=by
    exact (differentiableOn_id.neg.mul
      (hQd.comp (differentiableOn_id.pow 2) (fun z hz => kz95 hz))).div
      (hqd.comp (differentiableOn_id.pow 2) (fun z hz => kz95 hz))
      (fun z hz => hqn _ (kz95 hz))
  have hderh:deriv h 0 = -deriv q 0:=by
    have hqd0:=((hqd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt
    have hQd0:=((hQd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt
    have hp:HasDerivAt (fun z:ℂ => z^2) 0 0:=by
      have hp:=(hasDerivAt_id (0:ℂ)).pow 2
      change HasDerivAt (fun z:ℂ => z^2) _ 0 at hp
      simpa only [id_eq,Nat.reduceSub,pow_one,Nat.cast_ofNat,mul_one,mul_zero] using hp
    have hQcomp:HasDerivAt (fun z:ℂ => Q (z^2)) 0 0:=by
      have hQd0':HasDerivAt Q (deriv Q 0) ((0:ℂ)^2):=by simpa using hQd0
      convert hQd0'.comp (h:=fun z:ℂ => z^2) 0 hp using 1 <;> first | rfl | simp
    have hqcomp:HasDerivAt (fun z:ℂ => q (z^2)) 0 0:=by
      have hqd0':HasDerivAt q (deriv q 0) ((0:ℂ)^2):=by simpa using hqd0
      convert hqd0'.comp (h:=fun z:ℂ => z^2) 0 hp using 1 <;> first | rfl | simp
    have hD:=((hasDerivAt_id (0:ℂ)).neg.mul hQcomp).div hqcomp
      (by simpa using hqn 0 hdz)
    change HasDerivAt h _ 0 at hD
    simpa [Q,hq0] using hD.deriv
  have hdef (z) (hz:z ∈ disk) (hz0:z ≠ 0):H z = z⁻¹+h z:=by
    have hfact:=kz94 q (z^2)
    rw [hq0] at hfact
    change z^2 * Q (z^2) = q (z^2)-1 at hfact
    dsimp only [H,g,h]
    field_simp [hz0,hqn _ (kz95 hz)]
    linear_combination hfact
  have hHu:kz1 H (disk \ {0}):=by
    refine ⟨(hgd.mono sdiff_subset).inv (fun z hz => hgn z hz.1 hz.2),?_⟩
    intro z hz w hw he
    exact hgi hz.1 hw.1 (inv_inj.mp he)
  have hFq:deriv F 0 = 2*deriv q 0:=by
    have hD:=(((hqd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt).pow 2
    have he:(fun z => q z^2) =ᶠ[𝓝 (0:ℂ)] F:=by
      filter_upwards [Metric.isOpen_ball.mem_nhds hdz] with z hz
      exact hqs z hz
    have:=(hD.congr_of_eventuallyEq he.symm).deriv
    simpa [hq0] using this
  have hff:deriv (deriv f) 0 = 2*deriv F 0:=by
    have hidentity:f = fun z => z*F z:=by
      funext z
      simpa [hf.2.1,F] using (kz94 f z).symm
    have he:deriv f =ᶠ[𝓝 (0:ℂ)] fun z => F z+z*deriv F z:=by
      filter_upwards [Metric.isOpen_ball.mem_nhds hdz] with z hz
      have hD:=(hasDerivAt_id z).mul
        (((hFd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt)
      rw [hidentity]
      change HasDerivAt (fun w => w*F w) _ z at hD
      simpa using hD.deriv
    have hD:=(((hFd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt).add
      ((hasDerivAt_id (0:ℂ)).mul
        (((hFd.deriv Metric.isOpen_ball 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt))
    have:=(hD.congr_of_eventuallyEq he).deriv
    simpa [two_mul] using this
  refine ⟨q,g,h,H,hqd,hq0,hqn,hqs,fun _ => rfl,⟨hgd,hgi⟩,by simp [g],hhd,hderh,hdef,hHu,?_⟩
  rw [hff,hFq]
  ring
lemma kz97 {f:ℂ → ℂ} (hf:kz2 f) :
    ‖deriv (deriv f) 0‖ ≤ 4:=by
  obtain ⟨q,g,h,H,hqd,hq0,hqn,hqs,hgd,hgu,hg0,hhd,hderh,hdef,hHu,hff⟩ :=
    kz96 hf
  have hbound:‖deriv h 0‖ ≤ 1 :=
    kz88 hhd hHu.1 hdef
      (fun z hz => kz91
        (Metric.isOpen_ball.sdiff isClosed_singleton) hHu hz) hHu.2
  rw [hderh,norm_neg] at hbound
  rw [hff,norm_mul]
  norm_num
  linarith
def kz98 (a z:ℂ):ℂ:=(z+a)/(1+starRingEnd ℂ a*z)
lemma kz99 {a z:ℂ} (ha:a ∈ disk) (hz:z ∈ disk) :
    1+starRingEnd ℂ a*z ≠ 0:=by
  have hna:‖a‖ < 1:=by simpa [disk] using ha
  have hnz:‖z‖ < 1:=by simpa [disk] using hz
  intro he
  have hb:‖starRingEnd ℂ a*z‖ < 1:=by
    rw [norm_mul,Complex.norm_conj]
    nlinarith [norm_nonneg a,norm_nonneg z]
  have he':starRingEnd ℂ a*z = -1:=by linear_combination he
  rw [he'] at hb
  norm_num at hb
lemma kz100 (a z:ℂ) :
    Complex.normSq (1+starRingEnd ℂ a*z)-Complex.normSq (z+a) =
      (1-Complex.normSq a)*(1-Complex.normSq z):=by
  simp [Complex.normSq,Complex.mul_re,Complex.mul_im]
  ring
lemma kz101 {a z:ℂ} (ha:a ∈ disk) (hz:z ∈ disk) :
    kz98 a z ∈ disk:=by
  have hna:‖a‖ < 1:=by simpa [disk] using ha
  have hnz:‖z‖ < 1:=by simpa [disk] using hz
  have hpos:0 < (1-Complex.normSq a)*(1-Complex.normSq z):=by
    rw [← Complex.sq_norm,← Complex.sq_norm]
    apply mul_pos <;> nlinarith [norm_nonneg a,norm_nonneg z]
  have hineq:=kz100 a z
  have hd:=kz99 ha hz
  rw [disk,Metric.mem_ball,dist_zero_right,kz98,norm_div,div_lt_one (norm_pos_iff.mpr hd)]
  rw [← Complex.sq_norm,← Complex.sq_norm] at hineq
  nlinarith [norm_nonneg (z+a),norm_nonneg (1+starRingEnd ℂ a*z)]
lemma kz102 {a z:ℂ} (ha:a ∈ disk) (hz:z ∈ disk) :
    HasDerivAt (kz98 a)
      ((1-(‖a‖^2:ℝ))/(1+starRingEnd ℂ a*z)^2) z:=by
  have hd:=((hasDerivAt_id z).add_const a).div
    (((hasDerivAt_id z).const_mul (starRingEnd ℂ a)).const_add 1)
    (kz99 ha hz)
  convert hd using 1 <;> try rfl
  rw [Complex.sq_norm]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [id_eq]
  ring
lemma kz103 {a:ℂ} (ha:a ∈ disk):InjOn (kz98 a) disk:=by
  intro z hz w hw he
  have he':=(div_eq_div_iff (kz99 ha hz)
    (kz99 ha hw)).mp he
  have hna:‖a‖ < 1:=by simpa [disk] using ha
  have hd:(1-starRingEnd ℂ a*a) ≠ 0:=by
    rw [← Complex.normSq_eq_conj_mul_self,← Complex.ofReal_one,← Complex.ofReal_sub]
    apply Complex.ofReal_ne_zero.mpr
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg a]
  apply (mul_left_cancel₀ hd)
  linear_combination he'
lemma kz104 (a:ℂ):kz98 a 0 = a:=by simp [kz98]
lemma kz105 {a:ℂ} (ha:a ∈ disk) :
    DifferentiableOn ℂ (kz98 a) disk :=
  fun _ hz => (kz102 ha hz).differentiableAt.differentiableWithinAt
def kz106 (f:ℂ → ℂ) (a z:ℂ):ℂ :=
  (f (kz98 a z)-f a)/((1-((‖a‖^2:ℝ):ℂ))*deriv f a)
lemma kz107 {a:ℂ} (ha:a ∈ disk):1-((‖a‖^2:ℝ):ℂ) ≠ 0:=by
  have hn:‖a‖ < 1:=by simpa [disk] using ha
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.ofReal_ne_zero]
  nlinarith [norm_nonneg a]
lemma kz108 {f:ℂ → ℂ} {a:ℂ} (hf:kz1 f disk)
    (ha:a ∈ disk) (hfd:deriv f a ≠ 0):kz1 (kz106 f a) disk:=by
  refine ⟨?_,?_⟩
  · exact ((hf.1.comp (kz105 ha)
      (fun _ hz => kz101 ha hz)).sub_const (f a)).div_const _
  · intro z hz w hw he
    have he':=(div_left_inj' (mul_ne_zero (kz107 ha) hfd)).mp he
    exact kz103 ha hz hw
      (hf.2 (kz101 ha hz) (kz101 ha hw) (sub_left_inj.mp he'))
lemma kz109 {f:ℂ → ℂ} {a z:ℂ} (hf:DifferentiableOn ℂ f disk)
    (ha:a ∈ disk) (hz:z ∈ disk) :
    HasDerivAt (kz106 f a)
      ((deriv f (kz98 a z)*((1-((‖a‖^2:ℝ):ℂ))/(1+starRingEnd ℂ a*z)^2))/
        ((1-((‖a‖^2:ℝ):ℂ))*deriv f a)) z:=by
  exact ((((hf _ (kz101 ha hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (kz101 ha hz))).hasDerivAt.comp z
    (kz102 ha hz)).sub_const (f a)).div_const _
lemma kz110 {f:ℂ → ℂ} {a:ℂ} (hf:kz1 f disk)
    (ha:a ∈ disk) (hfd:deriv f a ≠ 0):kz2 (kz106 f a):=by
  refine ⟨kz108 hf ha hfd,?_,?_⟩
  · simp [kz106,kz104]
  · have hd:=(kz109 hf.1 ha (by simp [disk] : (0:ℂ) ∈ disk)).deriv
    rw [hd]
    simp only [kz104,mul_zero,add_zero,one_pow,div_one]
    rw [mul_comm (deriv f a),div_self (mul_ne_zero (kz107 ha) hfd)]
lemma kz111 {f:ℂ → ℂ} {a:ℂ} (hf:DifferentiableOn ℂ f disk)
    (ha:a ∈ disk) (hfd:deriv f a ≠ 0) :
    deriv (deriv (kz106 f a)) 0 =
      (1-((‖a‖^2:ℝ):ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a:=by
  have hzero:(0:ℂ) ∈ disk:=by simp [disk]
  have he:deriv (kz106 f a) =ᶠ[𝓝 (0:ℂ)]
      fun z => (deriv f (kz98 a z)*
        ((1-((‖a‖^2:ℝ):ℂ))/(1+starRingEnd ℂ a*z)^2))/
        ((1-((‖a‖^2:ℝ):ℂ))*deriv f a):=by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact (kz109 hf ha hz).deriv
  have hda:=((hf.deriv Metric.isOpen_ball a ha).differentiableAt
    (Metric.isOpen_ball.mem_nhds ha)).hasDerivAt
  have hda':HasDerivAt (deriv f) (deriv (deriv f) a) (kz98 a 0):=by
    simpa [kz104] using hda
  have hcomp:=hda'.comp 0 (kz102 ha hzero)
  have hrat:=(hasDerivAt_const (0:ℂ) (1-((‖a‖^2:ℝ):ℂ))).div
    ((((hasDerivAt_id (0:ℂ)).const_mul (starRingEnd ℂ a)).const_add 1).pow 2)
    (by simp)
  have hd:=((hcomp.mul hrat).div_const
    ((1-((‖a‖^2:ℝ):ℂ))*deriv f a)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Pi.div_apply,Pi.pow_apply,Function.comp_apply,kz104,
    mul_zero,add_zero,one_pow,div_one,zero_sub,id_eq,mul_one]
  have halg (A B C D:ℂ) (hB:B ≠ 0) (hC:C ≠ 0) :
      (A*C*C+B*(-(C*(2*D))))/(C*B) = C*A/B-2*D:=by
    field_simp
    ring
  exact halg (deriv (deriv f) a) (deriv f a)
    (1-((‖a‖^2:ℝ):ℂ)) (starRingEnd ℂ a) hfd (kz107 ha)
def kz112 (f:ℂ → ℂ) (w z:ℂ):ℂ:=w*f z/(w-f z)
lemma kz113 {f:ℂ → ℂ} {w:ℂ}
    (hf:kz1 f disk) (hw:w ∉ f '' disk) (hw0:w ≠ 0) :
    kz1 (kz112 f w) disk:=by
  have hn (z) (hz:z ∈ disk):w-f z ≠ 0:=by
    intro he
    exact hw ⟨z,hz,(sub_eq_zero.mp he).symm⟩
  refine ⟨(hf.1.const_mul w).div (hf.1.const_sub w) hn,?_⟩
  intro z hz v hv he
  apply hf.2 hz hv
  apply mul_left_cancel₀ (pow_ne_zero 2 hw0)
  have he':=(div_eq_div_iff (hn z hz) (hn v hv)).mp he
  linear_combination he'
lemma kz114 {f:ℂ → ℂ} {w z:ℂ}
    (hf:DifferentiableOn ℂ f disk) (hw:w ∉ f '' disk) (hz:z ∈ disk) :
    HasDerivAt (kz112 f w) (w^2*deriv f z/(w-f z)^2) z:=by
  have hn:w-f z ≠ 0:=fun he => hw ⟨z,hz,(sub_eq_zero.mp he).symm⟩
  have hd:=((hf z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
  convert (hd.const_mul w).div (hd.const_sub w) hn using 1 <;> try rfl
  ring
lemma kz115 {f:ℂ → ℂ} {w:ℂ}
    (hf:kz2 f) (hw:w ∉ f '' disk):kz2 (kz112 f w):=by
  have hzero:(0:ℂ) ∈ disk:=by simp [disk]
  have hw0:w ≠ 0:=fun h => hw ⟨0,hzero,hf.2.1.trans h.symm⟩
  refine ⟨kz113 hf.1 hw hw0,?_,?_⟩
  · simp [kz112,hf.2.1]
  · rw [(kz114 hf.1.1 hw hzero).deriv,hf.2.1,hf.2.2]
    simp [hw0]
lemma kz116 {f:ℂ → ℂ} {w:ℂ}
    (hf:kz2 f) (hw:w ∉ f '' disk) :
    deriv (deriv (kz112 f w)) 0 = deriv (deriv f) 0+2/w:=by
  have hzero:(0:ℂ) ∈ disk:=by simp [disk]
  have hw0:w ≠ 0:=fun h => hw ⟨0,hzero,hf.2.1.trans h.symm⟩
  have he:deriv (kz112 f w) =ᶠ[𝓝 (0:ℂ)]
      fun z => w^2*deriv f z/(w-f z)^2:=by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact (kz114 hf.1.1 hw hz).deriv
  have hfd:=((hf.1.1 0 hzero).differentiableAt (Metric.isOpen_ball.mem_nhds hzero)).hasDerivAt
  have hfdd:=((hf.1.1.deriv Metric.isOpen_ball 0 hzero).differentiableAt
    (Metric.isOpen_ball.mem_nhds hzero)).hasDerivAt
  have hd:=((hfdd.const_mul (w^2)).div ((hfd.const_sub w).pow 2)
    (by simpa [hf.2.1] using pow_ne_zero 2 hw0)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Pi.pow_apply,hf.2.1,hf.2.2,sub_zero,mul_one]
  field_simp [hw0]
  ring
lemma kz117 {f:ℂ → ℂ} (hf:kz2 f) {a:ℂ} (ha:a ∈ disk) :
    ‖(1-((‖a‖^2:ℝ):ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a‖ ≤ 4:=by
  have hn:=kz91 Metric.isOpen_ball hf.1 ha
  have hb:=kz97 (kz110 hf.1 ha hn)
  rwa [kz111 hf.1.1 ha hn] at hb
lemma kz118 {f:ℂ → ℂ} (hf:kz2 f) :
    Metric.ball (0:ℂ) (1/4) ⊆ f '' disk:=by
  intro w hw
  by_contra hnot
  have hz:(0:ℂ) ∈ disk:=by simp [disk]
  have hw0:w ≠ 0:=fun h => hnot ⟨0,hz,hf.2.1.trans h.symm⟩
  have hb:=kz97 (kz115 hf hnot)
  rw [kz116 hf hnot] at hb
  have hdiff:‖(2:ℂ)/w‖ ≤ 8:=by
    have ht:=norm_sub_le (deriv (deriv f) 0+2/w) (deriv (deriv f) 0)
    have hf2:=kz97 hf
    simp only [add_sub_cancel_left] at ht
    linarith
  rw [norm_div] at hdiff
  norm_num at hdiff
  have hle:=(div_le_iff₀ (norm_pos_iff.mpr hw0)).mp hdiff
  have hw':‖w‖ < 1/4:=by simpa using hw
  linarith
lemma kz119 {g:ℝ → ℂ} {d:ℂ} {x:ℝ}
    (hg:HasDerivAt g d x) (hn:g x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖g t‖) (d/g x).re x:=by
  have heq:(fun t => Real.log ‖g t‖) =
      (fun t => (1/2:ℝ)*Real.log (‖g t‖^2)):=by
    funext t
    rw [Real.log_pow]
    ring
  have hd:=((hg.norm_sq).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).const_mul (1/2:ℝ)
  rw [heq]
  refine hd.congr_deriv ?_
  simp only [Complex.inner,Complex.conj_re,Complex.conj_im,Complex.mul_re,
    Complex.div_re,Complex.normSq_eq_norm_sq]
  ring
lemma kz120 {L D:ℝ → ℝ} {r:ℝ} (hr:0 ≤ r) (hr1:r < 1)
    (hL:∀ x ∈ Icc 0 r,HasDerivAt L (D x) x) (hL0:L 0 = 0)
    (hbound:∀ x ∈ Icc 0 r,
      (2*x-4)/(1-x^2) ≤ D x ∧ D x ≤ (2*x+4)/(1-x^2)) :
    Real.log (1-r)-3*Real.log (1+r) ≤ L r ∧
      L r ≤ Real.log (1+r)-3*Real.log (1-r):=by
  have hp (x:ℝ) (hx:x ∈ Icc 0 r):0 < 1-x ∧ 0 < 1+x ∧ 0 < 1-x^2:=by
    constructor
    · linarith [hx.2]
    constructor
    · linarith [hx.1]
    · have:=hx.1
      nlinarith [hx.2]
  let U:=fun x => L x-Real.log (1+x)+3*Real.log (1-x)
  let V:=fun x => L x-Real.log (1-x)+3*Real.log (1+x)
  have hU (x) (hx:x ∈ Icc 0 r):HasDerivAt U
      (D x-1/(1+x)-3/(1-x)) x:=by
    have hlogp:=((hasDerivAt_id x).const_add 1).log (ne_of_gt (hp x hx).2.1)
    have hlogm:=((hasDerivAt_id x).const_sub 1).log (ne_of_gt (hp x hx).1)
    convert ((hL x hx).sub hlogp).add (hlogm.const_mul 3) using 1 <;> try rfl
    simp
    ring
  have hV (x) (hx:x ∈ Icc 0 r):HasDerivAt V
      (D x+1/(1-x)+3/(1+x)) x:=by
    have hlogp:=((hasDerivAt_id x).const_add 1).log (ne_of_gt (hp x hx).2.1)
    have hlogm:=((hasDerivAt_id x).const_sub 1).log (ne_of_gt (hp x hx).1)
    convert ((hL x hx).sub hlogm).add (hlogp.const_mul 3) using 1 <;> try rfl
    simp
    ring
  have halg (x) (hx:x ∈ Icc 0 r) :
      1/(1+x)+3/(1-x) = (2*x+4)/(1-x^2) ∧
      -(1/(1-x)+3/(1+x)) = (2*x-4)/(1-x^2):=by
    constructor <;> field_simp [(hp x hx).1.ne',(hp x hx).2.1.ne',(hp x hx).2.2.ne'] <;> ring
  have hUa:AntitoneOn U (Icc 0 r):=by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 r)
      (fun x hx => (hU x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hU x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hU x (interior_subset hx)).deriv]
    have hb:=(hbound x (interior_subset hx)).2
    rw [← (halg x (interior_subset hx)).1] at hb
    linarith
  have hVm:MonotoneOn V (Icc 0 r):=by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
      (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hV x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hV x (interior_subset hx)).deriv]
    have hb:=(hbound x (interior_subset hx)).1
    rw [← (halg x (interior_subset hx)).2] at hb
    linarith
  have hu:=hUa (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have hv:=hVm (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  dsimp [U,V] at hu hv
  simp only [hL0,add_zero,sub_zero,Real.log_one,mul_zero] at hu hv
  constructor <;> linarith
lemma kz121 {f:ℂ → ℂ}
    (hf:DifferentiableOn ℂ f disk) (hf0:deriv f 0 = 1)
    (hfn:∀ a ∈ disk,deriv f a ≠ 0)
    (hps:∀ a ∈ disk,
      ‖(1-((‖a‖^2:ℝ):ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a‖ ≤ 4)
    {r:ℝ} (hr:0 ≤ r) (hr1:r < 1) {ζ:ℂ} (hζ:‖ζ‖ = 1) :
    (1-r)/(1+r)^3 ≤ ‖deriv f ((r:ℂ)*ζ)‖ ∧
      ‖deriv f ((r:ℂ)*ζ)‖ ≤ (1+r)/(1-r)^3:=by
  let L:ℝ → ℝ:=fun x => Real.log ‖deriv f ((x:ℂ)*ζ)‖
  let D:ℝ → ℝ:=fun x => (deriv (deriv f) ((x:ℂ)*ζ)*ζ/deriv f ((x:ℂ)*ζ)).re
  have hn (x) (hx:x ∈ Icc 0 r):‖(x:ℂ)*ζ‖ = x:=by
    rw [norm_mul,hζ,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1]
  have hm (x) (hx:x ∈ Icc 0 r):(x:ℂ)*ζ ∈ disk:=by
    simp only [disk,Metric.mem_ball,dist_zero_right,hn x hx]
    exact hx.2.trans_lt hr1
  have hD (x) (hx:x ∈ Icc 0 r):HasDerivAt L (D x) x:=by
    have hd:=((hf.deriv Metric.isOpen_ball _ (hm x hx)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hm x hx))).hasDerivAt
    have hx':HasDerivAt (fun t:ℝ => (t:ℂ)*ζ) ζ x:=by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const ζ :
        HasDerivAt (fun t:ℝ => Complex.ofRealCLM t*ζ) ((Complex.ofRealCLM (1:ℝ))*ζ) x)
    have hdc:HasDerivAt (fun t:ℝ => deriv f ((t:ℂ)*ζ))
        (deriv (deriv f) ((x:ℂ)*ζ)*ζ) x:=by
      convert HasDerivAt.comp (𝕜:=ℝ) x hd hx' using 1 <;> rfl
    exact kz119 hdc (hfn _ (hm x hx))
  have hb (x) (hx:x ∈ Icc 0 r) :
      (2*x-4)/(1-x^2) ≤ D x ∧ D x ≤ (2*x+4)/(1-x^2):=by
    let A:ℂ:=(1-((x^2:ℝ):ℂ))*deriv (deriv f) ((x:ℂ)*ζ)/deriv f ((x:ℂ)*ζ)
      -2*starRingEnd ℂ ((x:ℂ)*ζ)
    have hA:‖A*ζ‖ ≤ 4:=by
      rw [norm_mul,hζ,mul_one]
      simpa only [A,hn x hx] using hps _ (hm x hx)
    have he:(A*ζ).re = (1-x^2)*D x-2*x:=by
      have hzz:starRingEnd ℂ ζ*ζ = 1:=by
        rw [← Complex.normSq_eq_conj_mul_self,← Complex.sq_norm,hζ]
        norm_num
      have heq:A*ζ = ((1-x^2:ℝ):ℂ)*
          (deriv (deriv f) ((x:ℂ)*ζ)*ζ/deriv f ((x:ℂ)*ζ))-2*(x:ℂ):=by
        dsimp only [A]
        rw [map_mul,Complex.conj_ofReal]
        rw [Complex.ofReal_sub,Complex.ofReal_one]
        linear_combination -2*(x:ℂ)*hzz
      rw [heq]
      simp only [D,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
      norm_num
    have hreal:=(Complex.abs_re_le_norm (A*ζ)).trans hA
    rw [he,abs_le] at hreal
    have hpos:0 < 1-x^2:=by nlinarith [hx.1,hx.2]
    constructor
    · rw [div_le_iff₀ hpos]
      nlinarith [hreal.1]
    · rw [le_div_iff₀ hpos]
      nlinarith [hreal.2]
  have hbnd:=kz120 hr hr1 hD (by simp [L,hf0]) hb
  have hposm:0 < 1-r:=sub_pos.mpr hr1
  have hposp:0 < 1+r:=by linarith
  have hnorm:0 < ‖deriv f ((r:ℂ)*ζ)‖:=norm_pos_iff.mpr (hfn _ (hm r (right_mem_Icc.mpr hr)))
  constructor
  · apply (Real.log_le_log_iff (div_pos hposm (pow_pos hposp 3)) hnorm).mp
    simpa only [Real.log_div hposm.ne' (pow_ne_zero 3 hposp.ne'),Real.log_pow,Nat.cast_ofNat] using hbnd.1
  · apply (Real.log_le_log_iff hnorm (div_pos hposp (pow_pos hposm 3))).mp
    simpa only [Real.log_div hposp.ne' (pow_ne_zero 3 hposm.ne'),Real.log_pow,Nat.cast_ofNat] using hbnd.2
lemma kz122 {f:ℂ → ℂ} (hf:kz2 f) {z:ℂ} (hz:z ∈ disk) :
    (1-‖z‖)/(1+‖z‖)^3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1+‖z‖)/(1-‖z‖)^3:=by
  by_cases hzero:z = 0
  · simp [hzero,hf.2.2]
  have hn:=norm_pos_iff.mpr hzero
  have hζ:‖z/(‖z‖ : ℂ)‖ = 1:=by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z),div_self hn.ne']
  have heq:(‖z‖ : ℂ)*(z/(‖z‖ : ℂ)) = z:=by
    field_simp [show (‖z‖ : ℂ) ≠ 0 by exact_mod_cast hn.ne']
  have hb:=kz121 hf.1.1 hf.2.2
    (fun _ ha => kz91 Metric.isOpen_ball hf.1 ha)
    (fun _ ha => kz117 hf ha) (norm_nonneg z)
    (show ‖z‖ < 1 by simpa [disk] using hz) hζ
  rwa [heq] at hb
lemma kz123 {f:ℂ → ℂ} (hf:kz2 f)
    {R:ℝ} (hR:R < 1) {z:ℂ} (hz:‖z‖ ≤ R) :
    ‖deriv f z‖ ≤ 2/(1-R)^3:=by
  have hzm:z ∈ disk:=by simpa [disk] using hz.trans_lt hR
  apply (kz122 hf hzm).2.trans
  have hd:0 < 1-R:=sub_pos.mpr hR
  apply div_le_div₀ (by positivity) (by linarith [norm_nonneg z]) (by positivity)
  exact pow_le_pow_left₀ hd.le (by linarith) 3
lemma kz124 {f:ℂ → ℂ} (hf:kz2 f)
    {R:ℝ} (hR:R < 1) {z w:ℂ} (hz:‖z‖ ≤ R) (hw:‖w‖ ≤ R) :
    ‖f z-f w‖ ≤ (2/(1-R)^3)*‖z-w‖:=by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s:=Metric.closedBall 0 R)
    (𝕜:=ℂ) _ _ (convex_closedBall 0 R)
    (by simpa using hw) (by simpa using hz)
  · intro x hx
    apply (hf.1.1 x _).differentiableAt
      (Metric.isOpen_ball.mem_nhds (show x ∈ disk from ?_))
    all_goals simpa [disk] using (show ‖x‖ ≤ R by simpa using hx).trans_lt hR
  · intro x hx
    exact kz123 hf hR (by simpa using hx)
lemma kz125 {f:ℂ → ℂ} (hf:kz2 f)
    {R:ℝ} (hR:R < 1) {z:ℂ} (hz:‖z‖ ≤ R) :
    ‖f z‖ ≤ (2/(1-R)^3)*R:=by
  have h:=kz124 hf hR hz
    (show ‖(0:ℂ)‖ ≤ R by simpa using (norm_nonneg z).trans hz)
  simp only [hf.2.1,sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left hz (by positivity))
def kz126 (f:ℂ → ℂ) (a:ℂ) (R:ℝ) (z:ℂ):ℂ :=
  (f (a+(R:ℂ)*z)-f a)/((R:ℂ)*deriv f a)
lemma kz127 (a:ℂ) {R:ℝ} (hR:0 < R) :
    MapsTo (fun z:ℂ => a+(R:ℂ)*z) disk (Metric.ball a R):=by
  intro z hz
  have hz':‖z‖ < 1:=by simpa [disk] using hz
  simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  nlinarith
lemma kz128 {f:ℂ → ℂ} {a z:ℂ} {R:ℝ} (hR:0 < R)
    (hf:DifferentiableOn ℂ f (Metric.ball a R)) (hz:z ∈ disk) :
    HasDerivAt (kz126 f a R)
      (deriv f (a+(R:ℂ)*z)/deriv f a) z:=by
  have hmap:=kz127 a hR hz
  have hd:=((hf _ hmap).differentiableAt (Metric.isOpen_ball.mem_nhds hmap)).hasDerivAt
  have hdz:=(((hd.comp z (((hasDerivAt_id z).const_mul (R:ℂ)).const_add a)).sub_const (f a)).div_const
    ((R:ℂ)*deriv f a))
  convert hdz using 1 <;> try rfl
  have hRc:(R:ℂ) ≠ 0:=by exact_mod_cast hR.ne'
  simp only [mul_one]
  field_simp
lemma kz129 {f:ℂ → ℂ} {a:ℂ} {R:ℝ} (hR:0 < R)
    (hf:kz1 f (Metric.ball a R)) (hn:deriv f a ≠ 0) :
    kz2 (kz126 f a R):=by
  have hRc:(R:ℂ) ≠ 0:=by exact_mod_cast hR.ne'
  have hmap:=kz127 a hR
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro z hz
    exact (kz128 hR hf.1 hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    apply mul_left_cancel₀ hRc
    apply add_left_cancel (a:=a)
    apply hf.2 (hmap hz) (hmap hw)
    have he':=(div_left_inj' (mul_ne_zero hRc hn)).mp he
    exact sub_left_inj.mp he'
  · simp [kz126]
  · rw [(kz128 hR hf.1 (show (0:ℂ) ∈ disk by simp [disk])).deriv]
    simp [hn]
lemma kz130 {f:ℂ → ℂ} {a:ℂ} {R:ℝ} (hR:0 < R)
    (hf:kz1 f (Metric.ball a R)) :
    Metric.ball (f a) (R*‖deriv f a‖/4) ⊆ f '' Metric.ball a R:=by
  have ha:a ∈ Metric.ball a R:=Metric.mem_ball_self hR
  have hn:=kz91 Metric.isOpen_ball hf ha
  have hRc:(R:ℂ) ≠ 0:=by exact_mod_cast hR.ne'
  have hden:=mul_ne_zero hRc hn
  intro w hw
  have hu:(w-f a)/((R:ℂ)*deriv f a) ∈ Metric.ball (0:ℂ) (1/4):=by
    simp only [Metric.mem_ball,dist_zero_right,norm_div,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    rw [div_lt_iff₀ (mul_pos hR (norm_pos_iff.mpr hn))]
    have hw':‖w-f a‖ < R*‖deriv f a‖/4:=by simpa [dist_eq_norm] using hw
    linarith
  obtain ⟨z,hz,he⟩:=kz118 (kz129 hR hf hn) hu
  refine ⟨a+(R:ℂ)*z,kz127 a hR hz,?_⟩
  have hes:=(div_left_inj' hden).mp he
  exact sub_left_inj.mp hes
lemma kz131 {f:ℂ → ℂ} (hf:kz2 f)
    {z w:ℂ} (_hz:z ∈ disk) (hw:w ∈ disk) {R:ℝ} (hR:0 < R)
    (hsub:Metric.ball z R ⊆ disk) (hdist:R ≤ ‖w-z‖) :
    R*‖deriv f z‖/4 ≤ ‖f w-f z‖:=by
  by_contra! hlt
  have hm:f w ∈ Metric.ball (f z) (R*‖deriv f z‖/4):=by
    simpa [dist_eq_norm] using hlt
  obtain ⟨v,hv,he⟩:=kz130 hR ⟨hf.1.1.mono hsub,hf.1.2.mono hsub⟩ hm
  have hvw:=hf.1.2 (hsub hv) hw he
  subst v
  have:‖w-z‖ < R:=by simpa [dist_eq_norm] using hv
  exact (not_lt_of_ge hdist) this
lemma kz132 {f:ℂ → ℂ} (hf:kz2 f) {z:ℂ} (hz:z ∈ disk) :
    ‖z‖/4 ≤ ‖f z‖:=by
  by_cases hzero:z = 0
  · simp [hzero,hf.2.1]
  have h:=kz131 hf (show (0:ℂ) ∈ disk by simp [disk]) hz
    (norm_pos_iff.mpr hzero)
    (Metric.ball_subset_ball (show ‖z‖ ≤ 1 by exact le_of_lt (by simpa [disk] using hz)))
    (show ‖z‖ ≤ ‖z-(0:ℂ)‖ by simp)
  simpa [hf.2.1,hf.2.2] using h
lemma kz133 {z w:ℂ} (hz:z ∈ disk) (hw:w ∈ disk)
    (hne:z ≠ w):∃ c:ℝ,0 < c ∧ ∀ f:ℂ → ℂ,kz2 f → c ≤ ‖f w-f z‖:=by
  have hz1:‖z‖ < 1:=by simpa [disk] using hz
  let R:=min ((1-‖z‖)/2) (‖w-z‖/2)
  have hR:0 < R:=lt_min (by linarith)
    (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)) (by norm_num))
  have hR1:R ≤ (1-‖z‖)/2:=min_le_left _ _
  have hR2:R ≤ ‖w-z‖/2:=min_le_right _ _
  have hsub:Metric.ball z R ⊆ disk:=by
    intro v hv
    have hvR:‖v-z‖ < R:=by simpa [dist_eq_norm] using hv
    have ht:=norm_add_le (v-z) z
    rw [sub_add_cancel] at ht
    simp only [disk,Metric.mem_ball,dist_zero_right]
    linarith
  refine ⟨R*((1-‖z‖)/(1+‖z‖)^3)/4,by positivity,?_⟩
  intro f hf
  have h:=kz131 hf hz hw hR hsub (by linarith [norm_nonneg (w-z)])
  apply le_trans _ h
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (kz122 hf hz).1 hR.le)
    (by norm_num)
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
instance:LocallyCompactSpace disk:=(show IsOpen disk from Metric.isOpen_ball).locallyCompactSpace
lemma kz134 (S:Set C(disk,ℂ))
    (hLip:∀ R:ℝ,R < 1 → ∃ C:ℝ,∀ g ∈ S,∀ z w:disk,
      ‖(z:ℂ)‖ ≤ R → ‖(w:ℂ)‖ ≤ R → ‖g z-g w‖ ≤ C*‖(z:ℂ)-(w:ℂ)‖)
    (hBd:∀ z:disk,∃ C:ℝ,∀ g ∈ S,‖g z‖ ≤ C) :
    IsCompact (closure S):=by
  let:T2Space (UniformOnFun disk ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  have heq:Equicontinuous (fun g:S => fun z:disk => g.1 z):=by
    intro z
    obtain ⟨R,hzR,hR⟩:=exists_between (show ‖(z:ℂ)‖ < 1 by simpa [disk] using z.2)
    obtain ⟨C,hC⟩:=hLip R hR
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun w:disk => C*dist (z:ℂ) (w:ℂ))
    · simpa using (tendsto_const_nhds (x:=C)).mul
        ((tendsto_const_nhds (x:=(z:ℂ))).dist (continuous_subtype_val.tendsto z))
    · have hn:∀ᶠ w:disk in 𝓝 z,‖(w:ℂ)‖ < R :=
        (continuous_norm.comp continuous_subtype_val).continuousAt (Iio_mem_nhds hzR)
      filter_upwards [hn] with w hw g
      simpa [dist_eq_norm] using hC g.1 g.2 z w hzR.le hw.le
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F:=fun g:C(disk,ℂ) => fun z:disk => g z)
    (𝔖:={K | IsCompact K}) (fun _ h => h)
    (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding)
  · intro K _
    exact heq.equicontinuousOn K
  · intro K _ z _
    obtain ⟨C,hC⟩:=hBd z
    exact ⟨Metric.closedBall 0 C,isCompact_closedBall _ _,by simpa using hC⟩
def kz135 (g:C(disk,ℂ)) (z:ℂ):ℂ :=
  by classical exact if hz:z ∈ disk then g ⟨z,hz⟩ else 0
@[simp] lemma kz136 (g:C(disk,ℂ)) (z:disk):kz135 g z = g z:=by
  simp [kz135,z.2]
lemma diskExtend_convergence.{u_1} {ι:Type u_1} {l:Filter ι}
    {g:ι → C(disk,ℂ)} {f:C(disk,ℂ)} (h:Tendsto g l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun i => kz135 (g i)) (kz135 f) l disk:=by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def,kz136] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h
def kz137:Set C(disk,ℂ):={g | kz2 (kz135 g)}
lemma kz138:IsClosed kz137:=by
  rw [isClosed_iff_forall_filter]
  intro g l hl hs hg
  let:=hl
  have hS:∀ᶠ f:C(disk,ℂ) in l,kz2 (kz135 f) :=
    le_principal_iff.mp hs
  have hc:=diskExtend_convergence (g:=id) hg
  have hhol:∀ᶠ f:C(disk,ℂ) in l,DifferentiableOn ℂ (kz135 f) disk :=
    hS.mono (fun _ h => h.1.1)
  have hgH:=hc.differentiableOn hhol (show IsOpen disk from Metric.isOpen_ball)
  refine ⟨⟨hgH,?_⟩,?_,?_⟩
  · intro z hz w hw he
    by_contra hne
    obtain ⟨c,hc0,hs⟩:=kz133 hz hw hne
    have hevent:∀ᶠ f:C(disk,ℂ) in l,c ≤ ‖kz135 f w-kz135 f z‖ :=
      hS.mono (fun f hf => hs (kz135 f) hf)
    have ht:=((hc.tendsto_at hw).sub (hc.tendsto_at hz)).norm
    have hc':=ge_of_tendsto ht hevent
    rw [he,sub_self,norm_zero] at hc'
    exact not_le_of_gt hc0 hc'
  · apply tendsto_nhds_unique (hc.tendsto_at (show (0:ℂ) ∈ disk by simp [disk]))
    exact tendsto_const_nhds.congr' (hS.mono (fun _ hf => hf.2.1.symm))
  · apply tendsto_nhds_unique ((hc.deriv hhol (show IsOpen disk from Metric.isOpen_ball)).tendsto_at
      (show (0:ℂ) ∈ disk by simp [disk]))
    exact tendsto_const_nhds.congr' (hS.mono (fun _ hf => hf.2.2.symm))
lemma kz139:IsCompact kz137:=by
  rw [← kz138.closure_eq]
  apply kz134
  · intro R hR
    refine ⟨2/(1-R)^3,?_⟩
    intro g hg z w hz hw
    simpa only [kz136] using kz124 hg hR hz hw
  · intro z
    refine ⟨(2/(1-‖(z:ℂ)‖)^3)*‖(z:ℂ)‖,?_⟩
    intro g hg
    simpa only [kz136] using kz125 hg
      (show ‖(z:ℂ)‖ < 1 by simpa [disk] using z.2) le_rfl
def kz140:=kz137
instance:TopologicalSpace kz140:=inferInstanceAs (TopologicalSpace kz137)
instance:CompactSpace kz140:=isCompact_iff_compactSpace.mp kz139
lemma kz141 {f:ℂ → ℂ} (hf:DifferentiableOn ℂ f disk)
    (n:ℕ):DifferentiableOn ℂ (iteratedDeriv n f) disk:=by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv (show IsOpen disk from Metric.isOpen_ball)
lemma tendstoLocallyUniformlyOn_iteratedDeriv_disk.{u_1} {ι:Type u_1} {l:Filter ι}
    {f:ι → ℂ → ℂ} {g:ℂ → ℂ} (h:TendstoLocallyUniformlyOn f g l disk)
    (hf:∀ᶠ i in l,DifferentiableOn ℂ (f i) disk) (n:ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) l disk:=by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv
      (hf.mono (fun i h => kz141 h n))
      (show IsOpen disk from Metric.isOpen_ball)
def kz142 (n:ℕ) (g:kz140):C(disk,ℂ) :=
  ⟨fun z => iteratedDeriv n (kz135 g.1) z,
    continuousOn_iff_continuous_domRestrict.mp
      (kz141 g.2.1.1 n).continuousOn⟩
lemma kz143 (n:ℕ):Continuous (kz142 n):=by
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have h:=tendstoLocallyUniformlyOn_iteratedDeriv_disk
    (diskExtend_convergence (continuous_subtype_val.tendsto g))
    (Eventually.of_forall (fun f:kz140 => f.2.1.1)) n
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp h
lemma kz144 (n:ℕ) :
    Continuous (fun p:kz140 × disk => iteratedDeriv n (kz135 p.1.1) p.2) :=
  continuous_eval.comp ((kz143 n).prodMap continuous_id)
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def kz145:Set ℂ:={z | 0 < z.im}
lemma kz146:IsOpen kz145 :=
  isOpen_lt continuous_const Complex.continuous_im
def kz147 (f:ℂ → ℂ):Prop :=
  kz1 f kz145 ∧ f Complex.I = 0 ∧ deriv f Complex.I = 1
def kz148 (z w:ℂ):ℂ:=(z.re:ℂ) + (z.im:ℂ) * w
@[simp] lemma kz149 (z:ℂ):kz148 z Complex.I = z:=by
  apply Complex.ext <;> simp [kz148]
@[simp] lemma kz150 (w:ℂ):kz148 Complex.I w = w:=by
  simp [kz148]
lemma kz151 (z w u:ℂ):kz148 (kz148 z w) u = kz148 z (kz148 w u):=by
  apply Complex.ext <;> simp [kz148,Complex.mul_re,Complex.mul_im] <;> ring
lemma kz152 {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) :
    kz148 z w ∈ kz145:=by
  change 0 < (kz148 z w).im
  simpa [kz148] using mul_pos hz hw
lemma kz153 {z:ℂ} (hz:z ∈ kz145):Function.Injective (kz148 z):=by
  intro u v h
  dsimp [kz148] at h
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))) (add_left_cancel h)
lemma kz154 (z w:ℂ):HasDerivAt (kz148 z) (z.im:ℂ) w:=by
  convert (hasDerivAt_const w (z.re:ℂ)).add
    ((hasDerivAt_id w).const_mul (z.im:ℂ)) using 1 <;> first | rfl | simp
def kz155 (f:ℂ → ℂ) (z w:ℂ):ℂ :=
  (f (kz148 z w) - f z) / ((z.im:ℂ) * deriv f z)
lemma kz156 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) :
    HasDerivAt (kz155 f z) (deriv f (kz148 z w) / deriv f z) w:=by
  have hfd:=(hf.1 (kz148 z w) (kz152 hz hw)).differentiableAt
    (kz146.mem_nhds (kz152 hz hw))
  have h:=((hfd.hasDerivAt.comp w (kz154 z w)).sub_const (f z)).div_const
    ((z.im:ℂ) * deriv f z)
  have hy:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hd:deriv f z ≠ 0:=kz91 kz146 hf hz
  convert h using 1 <;> first | rfl | field_simp
lemma kz157 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) :
    deriv (kz155 f z) w = deriv f (kz148 z w) / deriv f z :=
  (kz156 hf hz hw).deriv
lemma kz158 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145):kz147 (kz155 f z):=by
  have hy:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hdf:deriv f z ≠ 0:=kz91 kz146 hf hz
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro w hw
    exact (kz156 hf hz hw).differentiableAt.differentiableWithinAt
  · intro u hu v hv h
    apply kz153 hz
    apply hf.2 (kz152 hz hu) (kz152 hz hv)
    have hh:f (kz148 z u) - f z = f (kz148 z v) - f z :=
      (div_left_inj' (mul_ne_zero hy hdf)).mp h
    exact sub_left_injective hh
  · simp [kz155]
  · rw [kz157 hf hz (by simp [kz145]),kz149,div_self hdf]
lemma kz159 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) :
    kz155 (kz155 f z) w = kz155 f (kz148 z w):=by
  have hy:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hv:(w.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hw)
  have hdf:deriv f z ≠ 0:=kz91 kz146 hf hz
  have hdg:deriv f (kz148 z w) ≠ 0 :=
    kz91 kz146 hf (kz152 hz hw)
  funext u
  have him:((kz148 z w).im:ℂ) = (z.im:ℂ) * (w.im:ℂ):=by
    simp [kz148]
  change (kz155 f z (kz148 w u) - kz155 f z w) /
    ((w.im:ℂ) * deriv (kz155 f z) w) = _
  rw [kz157 hf hz hw]
  simp only [kz155,kz151,him]
  field_simp
  ring
def kz160 (f:ℂ → ℂ) (z:ℂ):ℂ:=(deriv f z)⁻¹
lemma kz161 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) :
    kz160 (kz155 f z) w = kz160 f (kz148 z w) / kz160 f z:=by
  simp [kz160,kz157 hf hz hw,div_eq_mul_inv,mul_comm]
def kz162 (z:ℂ):ℂ:=(z-Complex.I)/(z+Complex.I)
def kz163 (z:ℂ):ℂ:=Complex.I*(1+z)/(1-z)
lemma kz164 {z:ℂ} (hz:z ∈ kz145):z+Complex.I ≠ 0:=by
  intro he
  have:=congrArg Complex.im he
  simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at this
  change 0 < z.im at hz
  linarith
lemma kz165 {z:ℂ} (hz:z ∈ disk):1-z ≠ 0:=by
  intro he
  have hz':‖z‖ < 1:=by simpa [disk] using hz
  rw [← sub_eq_zero.mp he] at hz'
  norm_num at hz'
lemma kz166 {z:ℂ} (hz:z ∈ kz145):kz162 z ∈ disk:=by
  have hd:=kz164 hz
  simp only [disk,Metric.mem_ball,dist_zero_right,kz162,norm_div]
  rw [div_lt_one (norm_pos_iff.mpr hd)]
  have hsql:‖z-Complex.I‖^2 = z.re^2+(z.im-1)^2:=by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hsqr:‖z+Complex.I‖^2 = z.re^2+(z.im+1)^2:=by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hz':0 < z.im:=hz
  nlinarith [norm_nonneg (z+Complex.I),norm_nonneg (z-Complex.I)]
lemma kz167 {z:ℂ} (_hz:z ∈ disk) :
    (kz163 z).im = (1-‖z‖^2)/‖1-z‖^2:=by
  simp only [kz163,Complex.div_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.add_re,Complex.add_im,Complex.one_re,
    Complex.one_im,Complex.sub_re,Complex.sub_im,Complex.sq_norm,Complex.normSq_apply]
  ring
lemma kz168 {z:ℂ} (hz:z ∈ disk):kz163 z ∈ kz145:=by
  have hz':‖z‖ < 1:=by simpa [disk] using hz
  change 0 < (kz163 z).im
  rw [kz167 hz]
  exact div_pos (by nlinarith [norm_nonneg z])
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (kz165 hz)))
lemma kz169 {z:ℂ} (hz:z ∈ kz145):kz163 (kz162 z) = z:=by
  have hd:=kz164 hz
  have hd2:=kz165 (kz166 hz)
  dsimp [kz163,kz162] at *
  field_simp
  ring_nf
lemma kz170 {z:ℂ} (hz:z ∈ disk):kz162 (kz163 z) = z:=by
  have hd:=kz165 hz
  have hd2:=kz164 (kz168 hz)
  dsimp [kz163,kz162] at *
  field_simp
  ring
lemma kz171 {z:ℂ} (hz:z ∈ kz145) :
    HasDerivAt kz162 (2*Complex.I/(z+Complex.I)^2) z:=by
  convert ((hasDerivAt_id z).sub_const Complex.I).div
    ((hasDerivAt_id z).add_const Complex.I) (kz164 hz) using 1 <;> try rfl
  simp only [id_eq,mul_one,one_mul]
  ring
lemma kz172 {z:ℂ} (hz:z ∈ disk) :
    HasDerivAt kz163 (2*Complex.I/(1-z)^2) z:=by
  convert (((hasDerivAt_id z).const_add 1).const_mul Complex.I).div
    ((hasDerivAt_id z).const_sub 1) (kz165 hz) using 1 <;> try rfl
  simp only [id_eq,mul_one]
  ring
@[simp] lemma kz173:kz162 Complex.I = 0:=by simp [kz162]
@[simp] lemma kz174:kz163 0 = Complex.I:=by simp [kz163]
def kz175 (f:ℂ → ℂ) (z:ℂ):ℂ:=2*Complex.I*f (kz162 z)
def kz176 (f:ℂ → ℂ) (z:ℂ):ℂ:=f (kz163 z)/(2*Complex.I)
lemma kz177 {f:ℂ → ℂ} (hf:DifferentiableOn ℂ f disk)
    {z:ℂ} (hz:z ∈ kz145):HasDerivAt (kz175 f)
      (-(4:ℂ)*deriv f (kz162 z)/(z+Complex.I)^2) z:=by
  have hd:=((hf _ (kz166 hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (kz166 hz))).hasDerivAt
  convert (hd.comp z (kz171 hz)).const_mul (2*Complex.I) using 1 <;> try rfl
  ring_nf
  simp [Complex.I_sq]
lemma kz178 {f:ℂ → ℂ} (hf:DifferentiableOn ℂ f kz145)
    {z:ℂ} (hz:z ∈ disk):HasDerivAt (kz176 f)
      (deriv f (kz163 z)/(1-z)^2) z:=by
  have hd:=((hf _ (kz168 hz)).differentiableAt
    (kz146.mem_nhds (kz168 hz))).hasDerivAt
  convert (hd.comp z (kz172 hz)).div_const (2*Complex.I) using 1 <;> try rfl
  field_simp
lemma kz179 {f:ℂ → ℂ} (hf:kz2 f) :
    kz147 (kz175 f):=by
  refine ⟨⟨fun z hz => (kz177 hf.1.1 hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    have hm:=hf.1.2 (kz166 hz) (kz166 hw)
      ((mul_left_cancel₀ (by simp:(2:ℂ)*Complex.I ≠ 0)) he)
    simpa only [kz169 hz,kz169 hw] using congrArg kz163 hm
  · simp [kz175,hf.2.1]
  · rw [(kz177 hf.1.1 (show Complex.I ∈ kz145 by simp [kz145])).deriv]
    norm_num [hf.2.2,add_sq,mul_assoc,Complex.I_sq,Complex.I_mul_I]
lemma kz180 {f:ℂ → ℂ} (hf:kz147 f) :
    kz2 (kz176 f):=by
  refine ⟨⟨fun z hz => (kz178 hf.1.1 hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    have hm:=hf.1.2 (kz168 hz) (kz168 hw)
      ((div_left_inj' (by simp:(2:ℂ)*Complex.I ≠ 0)).mp he)
    simpa only [kz170 hz,kz170 hw] using congrArg kz162 hm
  · simp [kz176,hf.2.1]
  · rw [(kz178 hf.1.1 (show (0:ℂ) ∈ disk by simp [disk])).deriv]
    simp [hf.2.2]
lemma kz181 {f:ℂ → ℂ} {z:ℂ} (hz:z ∈ kz145) :
    kz175 (kz176 f) z = f z:=by
  simp only [kz175,kz176,kz169 hz]
  field_simp
lemma kz182 {f:ℂ → ℂ} {z:ℂ} (hz:z ∈ disk) :
    kz176 (kz175 f) z = f z:=by
  simp [kz175,kz176,kz170 hz]
def kz183 (g:kz140):ℂ → ℂ:=kz175 (kz135 g.1)
lemma kz184 (g:kz140):kz147 (kz183 g) :=
  kz179 g.2
def kz185 (f:ℂ → ℂ) (hf:kz147 f):kz140 :=
  ⟨⟨fun z => kz176 f z,continuousOn_iff_continuous_domRestrict.mp
    (kz180 hf).1.1.continuousOn⟩,by
      have he:EqOn (kz135 (⟨fun z => kz176 f z,
        continuousOn_iff_continuous_domRestrict.mp
          (kz180 hf).1.1.continuousOn⟩:C(disk,ℂ))) (kz176 f) disk:=by
        intro z hz
        exact kz136 _ ⟨z,hz⟩
      refine ⟨⟨(kz180 hf).1.1.congr he,?_⟩,?_,?_⟩
      · intro z hz w hw h
        exact (kz180 hf).1.2 hz hw ((he hz).symm.trans (h.trans (he hw)))
      · rw [he (by simp [disk])]
        exact (kz180 hf).2.1
      · rw [he.deriv Metric.isOpen_ball (by simp [disk])]
        exact (kz180 hf).2.2⟩
lemma kz186 {f:ℂ → ℂ} (hf:kz147 f) :
    EqOn (kz183 (kz185 f hf)) f kz145:=by
  intro z hz
  dsimp [kz183,kz175,kz185]
  rw [kz136 _ (⟨kz162 z,kz166 hz⟩:disk)]
  exact kz181 hz
lemma kz187:Continuous (fun p:kz140 × kz145 => kz183 p.1 p.2):=by
  have hm':Continuous (fun z:kz145 => kz162 z):=by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (kz171 z.2).continuousAt.comp continuous_subtype_val.continuousAt
  have h:=(kz144 0).comp
    (continuous_id.prodMap (hm'.subtype_mk (fun z => kz166 z.2)))
  simpa only [iteratedDeriv_zero,kz183,kz175,Function.comp_def,Prod.map,id_eq] using h.const_mul (2*Complex.I)
instance:LocallyCompactSpace kz145:=kz146.locallyCompactSpace
instance:T2Space kz140:=inferInstanceAs (T2Space kz137)
instance:MeasurableSpace kz140:=borel kz140
instance:BorelSpace kz140:=⟨rfl⟩
lemma kz188 {U:Set ℂ} (hU:IsOpen U)
    {f:ℂ → ℂ} (hf:DifferentiableOn ℂ f U) (n:ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) U:=by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv hU
lemma tendstoLocallyUniformlyOn_iteratedDeriv_open.{u_1} {U:Set ℂ} (hU:IsOpen U)
    {ι:Type u_1} {l:Filter ι} {f:ι → ℂ → ℂ} {g:ℂ → ℂ}
    (h:TendstoLocallyUniformlyOn f g l U)
    (hf:∀ᶠ i in l,DifferentiableOn ℂ (f i) U) (n:ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) l U:=by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv
      (hf.mono (fun i h => kz188 hU h n)) hU
def kz189 (n:ℕ) (g:kz140):C(kz145,ℂ) :=
  ⟨fun z => iteratedDeriv n (kz183 g) z,continuousOn_iff_continuous_domRestrict.mp
    (kz188 kz146 (kz184 g).1.1 n).continuousOn⟩
lemma kz190 (n:ℕ):Continuous (kz189 n):=by
  have hc:Continuous (kz189 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ kz187
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv:=ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h:TendstoLocallyUniformlyOn kz183 (kz183 g) (𝓝 g) kz145 :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open kz146 h
      (Eventually.of_forall (fun f:kz140 => (kz184 f).1.1)) n)
lemma kz191 (n:ℕ) :
    Continuous (fun p:kz140 × kz145 => iteratedDeriv n (kz183 p.1) p.2) :=
  continuous_eval.comp ((kz190 n).prodMap continuous_id)
def kz192 (g:kz140) (z:kz145):kz140 :=
  kz185 (kz155 (kz183 g) z) (kz158 (kz184 g).1 z.2)
lemma kz193 (g:kz140) (z:kz145) :
    EqOn (kz183 (kz192 g z)) (kz155 (kz183 g) z) kz145 :=
  kz186 _
lemma kz194:Continuous (fun p:kz140 × kz145 => kz192 p.1 p.2):=by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc:Continuous (fun p:(kz140 × kz145) × disk =>
      (⟨kz163 p.2,kz168 p.2.2⟩:kz145)):=by
    apply Continuous.subtype_mk
    have hm:Continuous (fun z:disk => kz163 z):=by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (kz172 z.2).continuousAt.comp continuous_subtype_val.continuousAt
    exact hm.comp continuous_snd
  have ha:Continuous (fun p:(kz140 × kz145) × disk =>
      (⟨kz148 p.1.2 (kz163 p.2),kz152 p.1.2.2 (kz168 p.2.2)⟩:kz145)):=by
    apply Continuous.subtype_mk
    have hre:Continuous (fun p:(kz140 × kz145) × disk => p.1.2.val.re):=Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    have him:Continuous (fun p:(kz140 × kz145) × disk => p.1.2.val.im):=Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    exact (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul (continuous_subtype_val.comp hc))
  have hvalue:=kz187.comp ((continuous_fst.comp continuous_fst).prodMk ha)
  have hroot:Continuous (fun p:(kz140 × kz145) × disk => kz183 p.1.1 p.1.2) :=
    kz187.comp continuous_fst
  have hder:Continuous (fun p:(kz140 × kz145) × disk => deriv (kz183 p.1.1) p.1.2):=by
    simpa only [iteratedDeriv_one,Function.comp_def] using
      ((kz191 1).comp (continuous_fst:Continuous (Prod.fst:(kz140 × kz145) × disk → kz140 × kz145)))
  have him:Continuous (fun p:(kz140 × kz145) × disk => (p.1.2.val.im:ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hdiv:=(hvalue.sub hroot).div (him.mul hder) (fun p => mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt p.1.2.2))
    (kz91 kz146 (kz184 p.1.1).1 p.1.2.2))
  exact hdiv.div_const (2*Complex.I)
lemma kz195 {g h:kz140} (he:EqOn (kz183 g) (kz183 h) kz145):g = h:=by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  have hx:=congrArg (fun q:ℂ => q/(2*Complex.I)) (he (kz168 z.2))
  have hg:(kz183 g) (kz163 z)/(2*Complex.I) = g.1 z:=by
    exact (kz182 z.2).trans (kz136 _ z)
  have hh:(kz183 h) (kz163 z)/(2*Complex.I) = h.1 z:=by
    exact (kz182 z.2).trans (kz136 _ z)
  rwa [hg,hh] at hx
lemma kz196 {f g:ℂ → ℂ} (he:EqOn f g kz145) {z:ℂ} (hz:z ∈ kz145) :
    EqOn (kz155 f z) (kz155 g z) kz145:=by
  intro w hw
  simp only [kz155,he (kz152 hz hw),he hz,he.deriv kz146 hz]
lemma kz197 (g:kz140) (z w:kz145) :
    kz192 (kz192 g z) w = kz192 g ⟨kz148 z w,kz152 z.2 w.2⟩:=by
  apply kz195
  intro u hu
  rw [kz193 _ _ hu,kz196 (kz193 g z) w.2 hu,
    kz159 (kz184 g).1 z.2 w.2,kz193 _ _ hu]
def kz198 (g:kz140) (z:kz145):ℝ:=‖kz160 (kz183 g) z‖^2
lemma kz199 (g:kz140) (z:kz145):0 < kz198 g z:=by
  apply sq_pos_of_ne_zero
  exact norm_ne_zero_iff.mpr (inv_ne_zero
    (kz91 kz146 (kz184 g).1 z.2))
lemma kz200:Continuous (fun p:kz140 × kz145 => kz198 p.1 p.2):=by
  have hd:Continuous (fun p:kz140 × kz145 => deriv (kz183 p.1) p.2):=by
    simpa only [iteratedDeriv_one] using kz191 1
  exact (hd.inv₀ (fun p => kz91 kz146 (kz184 p.1).1 p.2.2)).norm.pow 2
lemma kz201 (g:kz140) (z w:kz145) :
    kz198 g z * kz198 (kz192 g z) w =
      kz198 g ⟨kz148 z w,kz152 z.2 w.2⟩:=by
  have he:=(kz193 g z).deriv kz146 w.2
  have hq:kz160 (kz183 (kz192 g z)) w =
      kz160 (kz155 (kz183 g) z) w:=congrArg Inv.inv he
  simp only [kz198,hq,kz161 (kz184 g).1 z.2 w.2,norm_div,div_pow]
  have hn:‖kz160 (kz183 g) z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (inv_ne_zero
      (kz91 kz146 (kz184 g).1 z.2))
  field_simp
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def kz202 (f:ℂ → ℂ) (z:ℂ):ℂ :=
  Complex.I * (z.im:ℂ) * deriv (kz160 f) z / kz160 f z
lemma kz203 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145) :
    kz202 f z = -Complex.I * (z.im:ℂ) * deriv (deriv f) z / deriv f z:=by
  have han:AnalyticAt ℂ f z:=hf.1.analyticOnNhd kz146 z hz
  have hd:deriv f z ≠ 0:=kz91 kz146 hf hz
  have hq:deriv (kz160 f) z = -deriv (deriv f) z / (deriv f z)^2 :=
    (han.deriv.differentiableAt.hasDerivAt.inv hd).deriv
  rw [kz202,hq,kz160]
  field_simp
def kz204 (f:ℂ → ℂ) (k:ℝ) (z:ℂ):ℂ :=
  f z - Complex.I / (k:ℂ) * (z.im:ℂ) * deriv f z
def kz205 (f:ℂ → ℂ) (k:ℝ) (z:ℂ):ℝ :=
  LinearMap.det (fderiv ℝ (kz204 f k) z).toLinearMap / ‖deriv f z‖^2
lemma kz206 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145) (k:ℝ) (v:ℂ) :
    fderiv ℝ (kz204 f k) z v = deriv f z * v -
      Complex.I / (k:ℂ) * ((v.im:ℂ) * deriv f z +
        (z.im:ℂ) * (deriv (deriv f) z * v)):=by
  have han:AnalyticAt ℂ f z:=hf.1.analyticOnNhd kz146 z hz
  have ha:=han.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hb:=han.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc:=Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
  have hG:=ha.sub ((hc.const_mul (Complex.I / (k:ℂ))).mul hb)
  have hG':HasFDerivAt (kz204 f k)
      (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) -
        ((Complex.I / (k:ℂ) * (z.im:ℂ)) •
          ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv f) z)) +
        deriv f z • (Complex.I / (k:ℂ)) •
          (Complex.ofRealCLM.comp Complex.imCLM))) z:=hG
  rw [hG'.fderiv]
  change v * deriv f z -
    ((Complex.I / (k:ℂ) * (z.im:ℂ)) * (v * deriv (deriv f) z) +
      deriv f z * (Complex.I / (k:ℂ) * (v.im:ℂ))) = _
  ring
lemma kz207 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145) (k:ℝ) (hk:k ≠ 0) :
    fderiv ℝ (kz204 f k) z 1 = deriv f z / (k:ℂ) * ((k:ℂ) + kz202 f z) ∧
    fderiv ℝ (kz204 f k) z Complex.I =
      Complex.I * (deriv f z / (k:ℂ)) * ((k:ℂ) - 1 + kz202 f z):=by
  have hd:deriv f z ≠ 0:=kz91 kz146 hf hz
  have hk':(k:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr hk
  constructor <;> rw [kz206 hf hz,kz203 hf hz] <;>
    simp only [Complex.one_im,Complex.I_im,Complex.ofReal_zero,Complex.ofReal_one,
      zero_mul,one_mul,mul_one,zero_add] <;> field_simp <;> ring
lemma kz208 (u q:ℂ) (k:ℝ) :
    (u * ((k:ℂ) + q)).re * (Complex.I * u * ((k:ℂ) - 1 + q)).im -
      (Complex.I * u * ((k:ℂ) - 1 + q)).re * (u * ((k:ℂ) + q)).im =
    ‖u‖^2 * (k * (k-1) + (2*k-1)*q.re + ‖q‖^2):=by
  simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
    Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,
    Complex.sq_norm,Complex.normSq_apply]
  ring
lemma kz209 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145) (k:ℝ) (hk:k ≠ 0) :
    k^2 * kz205 f k z =
      k * (k - 1) + (2*k - 1) * (kz202 f z).re + ‖kz202 f z‖^2:=by
  have hd:‖deriv f z‖ ≠ 0:=norm_ne_zero_iff.mpr
    (kz91 kz146 hf hz)
  obtain ⟨hc₁,hc₂⟩:=kz207 hf hz k hk
  rw [kz205,kz12]
  change k ^ 2 * (((fderiv ℝ (kz204 f k) z 1).re *
    (fderiv ℝ (kz204 f k) z Complex.I).im -
    (fderiv ℝ (kz204 f k) z Complex.I).re *
    (fderiv ℝ (kz204 f k) z 1).im) / ‖deriv f z‖^2) = _
  rw [hc₁,hc₂,kz208,norm_div,Complex.norm_real,
    Real.norm_eq_abs,div_pow,sq_abs]
  field_simp
lemma kz210 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145) :
    HasDerivAt (kz160 f) (deriv (kz160 f) z) z:=by
  have han:AnalyticAt ℂ f z:=hf.1.analyticOnNhd kz146 z hz
  exact (han.deriv.differentiableAt.inv
    (kz91 kz146 hf hz)).hasDerivAt
lemma kz211 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) :
    kz202 (kz155 f z) w = kz202 f (kz148 z w):=by
  have hqz:kz160 f z ≠ 0:=inv_ne_zero
    (kz91 kz146 hf hz)
  have hqw:kz160 f (kz148 z w) ≠ 0:=inv_ne_zero
    (kz91 kz146 hf (kz152 hz hw))
  have heq:kz160 (kz155 f z) =ᶠ[𝓝 w]
      (fun u => kz160 f (kz148 z u) / kz160 f z):=by
    filter_upwards [kz146.mem_nhds hw] with u hu
    exact kz161 hf hz hu
  have hD:=((((kz210 hf (kz152 hz hw)).comp w
    (kz154 z w)).div_const (kz160 f z)).congr_of_eventuallyEq heq).deriv
  have him:((kz148 z w).im:ℂ) = (z.im:ℂ) * (w.im:ℂ):=by
    simp [kz148]
  rw [kz202,hD,kz161 hf hz hw,kz202,him]
  field_simp
lemma kz212 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) (k:ℝ) :
    kz204 (kz155 f z) k w =
      (kz204 f k (kz148 z w) - f z) / ((z.im:ℂ) * deriv f z):=by
  have hy:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hd:deriv f z ≠ 0:=kz91 kz146 hf hz
  have him:((kz148 z w).im:ℂ) = (z.im:ℂ) * (w.im:ℂ):=by
    simp [kz148]
  rw [kz204,kz157 hf hz hw]
  simp only [kz155,kz204,him]
  field_simp
  ring
lemma kz213 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) (k:ℝ) (hk:k ≠ 0) :
    kz205 (kz155 f z) k w = kz205 f k (kz148 z w):=by
  apply (mul_left_cancel₀ (pow_ne_zero 2 hk))
  rw [kz209 (kz158 hf hz).1 hw k hk,
    kz209 hf (kz152 hz hw) k hk,kz211 hf hz hw]
def kz214 (f:ℂ → ℂ) (k:ℝ) (ξ z:ℂ):ℝ≥0∞ :=
  (ENNReal.ofReal z.im) ^ k / ENNReal.ofReal ‖f z - ξ‖
def kz215 (f:ℂ → ℂ) (k:ℝ) (ξ:ℂ):Prop :=
  (∀ δ:ℝ,0 < δ → IsCompact {z | z ∈ kz145 ∧ ENNReal.ofReal δ ≤ kz214 f k ξ z}) ∧
  (∀ z ∈ kz145,kz204 f k z = ξ → kz205 f k z ≠ 0)
lemma kz216 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145) (k:ℝ) :
    DifferentiableAt ℝ (kz204 f k) z:=by
  have han:AnalyticAt ℂ f z:=hf.1.analyticOnNhd kz146 z hz
  exact ((han.differentiableAt.restrictScalars ℝ).sub
    (((Complex.ofRealCLM.differentiableAt.comp z Complex.imCLM.differentiableAt).const_mul
      (Complex.I / (k:ℂ))).mul (han.deriv.differentiableAt.restrictScalars ℝ)))
lemma kz217 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} {ξ:ℂ} (hreg:∀ z ∈ kz145,
      kz204 f k z = ξ → kz205 f k z ≠ 0) :
    IsDiscrete {z | z ∈ kz145 ∧ kz204 f k z = ξ}:=by
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  have hd:LinearMap.det (fderiv ℝ (kz204 f k) z).toLinearMap ≠ 0 :=
    (div_ne_zero_iff.mp (hreg z hz.1 hz.2)).1
  let e:ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)).toContinuousLinearEquiv
  have he:(e:ℂ → ℂ) = fderiv ℝ (kz204 f k) z:=by
    funext w
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hd) w
  have ha:∃ C,AntilipschitzWith C (fderiv ℝ (kz204 f k) z):=by
    rw [← he]
    exact ⟨_,e.antilipschitz⟩
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [(kz216 hf hz.1 k).hasFDerivAt.eventually_ne ha] with w hw
  exact fun h => hw h.2
lemma kz218 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} {ξ:ℂ} (hg:kz215 f k ξ) {h:ℝ} (hh:0 < h) :
    {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧
      ENNReal.ofReal h ≤ kz214 f k ξ z}.Finite:=by
  let P:={z | z ∈ kz145 ∧ ENNReal.ofReal h ≤ kz214 f k ξ z}
  have hP:IsCompact P:=hg.1 h hh
  have hc:ContinuousOn (kz204 f k) P:=by
    intro z hz
    exact (kz216 hf hz.1 k).continuousAt.continuousWithinAt
  have hclosed:=hc.preimage_isClosed_of_isClosed hP.isClosed (isClosed_singleton (x:=ξ))
  have hcompact:IsCompact (P ∩ (kz204 f k) ⁻¹' {ξ}) :=
    hP.of_isClosed_subset hclosed inter_subset_left
  have hdiscrete:=(kz217 hf hg.2).mono
    (show P ∩ (kz204 f k) ⁻¹' {ξ} ⊆
      {z | z ∈ kz145 ∧ kz204 f k z = ξ} from fun _ hz => ⟨hz.1.1,hz.2⟩)
  convert hcompact.finite hdiscrete using 1
  ext z
  simp only [P,mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_singleton_iff]
  tauto
def kz219 (f:ℂ → ℂ) (k:ℝ) (ξ z:ℂ):ℝ :=
  k * Real.log z.im - Real.log ‖f z - ξ‖
lemma kz220 {g:ℂ → ℂ} {z:ℂ}
    (hg:DifferentiableAt ℂ g z) (hn:g z ≠ 0) :
    DifferentiableAt ℝ (fun w => Real.log ‖g w‖) z :=
  ((hg.restrictScalars ℝ).norm ℂ hn).log (norm_ne_zero_iff.mpr hn)
lemma kz221 {g:ℂ → ℂ} {d z:ℂ} (hg:HasDerivAt g d z)
    (hn:g z ≠ 0) (v:ℂ) :
    fderiv ℝ (fun w => Real.log ‖g w‖) z v = (d * v / g z).re:=by
  have heq:(fun w => Real.log ‖g w‖) =
      (fun w => (1 / 2:ℝ) * Real.log (‖g w‖ ^ 2)):=by
    funext w
    rw [Real.log_pow]
    ring
  have hh:=(((hg.hasFDerivAt.restrictScalars ℝ).norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).const_mul (1 / 2:ℝ)
  rw [heq,hh.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,innerSL_apply_apply]
  simp only [Complex.inner,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.mul_im,Complex.div_re,Complex.normSq_eq_norm_sq]
  ring
lemma kz222 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) (k:ℝ) :
    DifferentiableAt ℝ (kz219 f k ξ) z:=by
  have hd:=(hf.1 z hz).differentiableAt (kz146.mem_nhds hz)
  exact ((Complex.imCLM.differentiableAt.log (ne_of_gt hz)).const_mul k).sub
    (kz220 (hd.sub_const ξ) (sub_ne_zero.mpr hp))
lemma kz223 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) (k:ℝ) (v:ℂ) :
    fderiv ℝ (kz219 f k ξ) z v =
      k / z.im * v.im - (deriv f z * v / (f z - ξ)).re:=by
  have hd:=(hf.1 z hz).differentiableAt (kz146.mem_nhds hz)
  have ha:=(Complex.imCLM.hasFDerivAt.log (ne_of_gt hz)).const_mul k
  simp only [Complex.imCLM_apply] at ha
  have hb:=kz220 (hd.sub_const ξ) (sub_ne_zero.mpr hp)
  change fderiv ℝ (fun w => k * Real.log w.im - Real.log ‖f w - ξ‖) z v = _
  rw [fderiv_fun_sub ha.differentiableAt hb,
    sub_apply,ha.fderiv,
    kz221 (hd.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)]
  simp only [smul_apply,smul_eq_mul,Complex.imCLM_apply,div_eq_mul_inv]
  ring
lemma kz224 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:k ≠ 0) {z ξ:ℂ} (hz:z ∈ kz145)
    (hc:kz204 f k z = ξ):f z ≠ ξ:=by
  intro hp
  have hn:=mul_ne_zero (mul_ne_zero (div_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr hk)) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
    (kz91 kz146 hf hz)
  apply hn
  simpa [kz204,hp] using hc
lemma kz225 {f:ℂ → ℂ} {k:ℝ} {z ξ:ℂ}
    (hc:kz204 f k z = ξ) :
    f z - ξ = Complex.I / (k:ℂ) * (z.im:ℂ) * deriv f z:=by
  unfold kz204 at hc
  linear_combination hc
def kz226 (f:ℂ → ℂ) (ξ z:ℂ):ℂ:=deriv f z / (f z - ξ)
lemma kz227 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) :
    HasDerivAt (kz226 f ξ)
      ((deriv (deriv f) z * (f z - ξ) - deriv f z * deriv f z) / (f z - ξ)^2) z:=by
  have han:AnalyticAt ℂ f z:=hf.1.analyticOnNhd kz146 z hz
  exact han.deriv.differentiableAt.hasDerivAt.div
    (han.differentiableAt.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)
def kz228 (u:ℂ → ℝ) (z v w:ℂ):ℝ :=
  fderiv ℝ (fun t => fderiv ℝ u t v) z w
def kz229 (u:ℂ → ℝ) (z:ℂ):Matrix (Fin 2) (Fin 2) ℝ :=
  !![kz228 u z 1 1,kz228 u z 1 Complex.I;
    kz228 u z Complex.I 1,kz228 u z Complex.I Complex.I]
lemma kz230 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) (k:ℝ) (v:ℂ) :
    kz228 (kz219 f k ξ) z 1 v =
      -(deriv (kz226 f ξ) z * v).re:=by
  have hd:=(hf.1 z hz).differentiableAt (kz146.mem_nhds hz)
  have hn:=hd.continuousAt.eventually_ne hp
  have heq:(fun w => fderiv ℝ (kz219 f k ξ) w 1) =ᶠ[𝓝 z]
      (fun w => -(kz226 f ξ w).re):=by
    filter_upwards [kz146.mem_nhds hz,hn] with w hw hne
    simp only [kz223 hf hw hne,Complex.one_im,mul_zero,
      mul_one,zero_sub,kz226]
  have hr:=(kz227 hf hz hp).differentiableAt.hasDerivAt
  have hh:=(Complex.reCLM.hasFDerivAt.comp z
    (hr.hasFDerivAt.restrictScalars ℝ)).neg
  change HasFDerivAt (fun w => -(kz226 f ξ w).re) _ z at hh
  rw [kz228,heq.fderiv_eq,hh.fderiv]
  simp only [neg_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,Complex.reCLM_apply,mul_comm v]
lemma kz231 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) (k:ℝ) (v:ℂ) :
    kz228 (kz219 f k ξ) z Complex.I v =
      -k / z.im^2 * v.im + (deriv (kz226 f ξ) z * v).im:=by
  have hd:=(hf.1 z hz).differentiableAt (kz146.mem_nhds hz)
  have hn:=hd.continuousAt.eventually_ne hp
  have heq:(fun w => fderiv ℝ (kz219 f k ξ) w Complex.I) =ᶠ[𝓝 z]
      (fun w => k / w.im + (kz226 f ξ w).im):=by
    filter_upwards [kz146.mem_nhds hz,hn] with w hw hne
    rw [kz223 hf hw hne,
      show deriv f w * Complex.I / (f w - ξ) =
        (deriv f w / (f w - ξ)) * Complex.I by ring]
    simp only [Complex.I_im,mul_one,Complex.mul_I_re,sub_neg_eq_add,kz226]
  have hr:=(kz227 hf hz hp).differentiableAt.hasDerivAt
  have ha:=(((hasDerivAt_inv (ne_of_gt hz)).hasFDerivAt).comp z
    Complex.imCLM.hasFDerivAt).const_mul k
  have hb:=Complex.imCLM.hasFDerivAt.comp z (hr.hasFDerivAt.restrictScalars ℝ)
  have hh:=ha.add hb
  change HasFDerivAt (fun w => k * w.im⁻¹ + (kz226 f ξ w).im) _ z at hh
  simp only [← div_eq_mul_inv] at hh
  rw [kz228,heq.fderiv_eq,hh.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
    Complex.imCLM_apply,mul_comm v]
  ring
lemma kz232 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) (k:ℝ) :
    kz229 (kz219 f k ξ) z =
      !![-(deriv (kz226 f ξ) z).re,(deriv (kz226 f ξ) z).im;
        (deriv (kz226 f ξ) z).im,-k / z.im^2 + (deriv (kz226 f ξ) z).re]:=by
  simp only [kz229,kz230 hf hz hp,
    kz231 hf hz hp,mul_one,Complex.mul_I_re,
    Complex.mul_I_im,Complex.one_im,Complex.I_im,mul_zero,mul_one,zero_add,neg_neg]
lemma kz233 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) (k:ℝ) :
    Matrix.trace (kz229 (kz219 f k ξ) z) = -k / z.im^2:=by
  rw [kz232 hf hz hp]
  simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
lemma kz234 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:0 < k) {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) :
    Matrix.trace (kz229 (kz219 f k ξ) z) < 0:=by
  rw [kz233 hf hz hp]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hk) (sq_pos_of_pos hz)
lemma kz235 {f:ℂ → ℂ} {k:ℝ} {ξ z:ℂ}
    (hz:z ∈ kz145) (hp:f z ≠ ξ) :
    kz214 f k ξ z = ENNReal.ofReal (z.im^k / ‖f z - ξ‖):=by
  rw [kz214,ENNReal.ofReal_rpow_of_pos hz,
    ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp))]
lemma kz236 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:0 < k) {z ξ:ℂ} (hz:z ∈ kz145)
    (hc:kz204 f k z = ξ) :
    kz214 f k ξ z = ENNReal.ofReal (k * z.im^(k-1) * ‖kz160 f z‖):=by
  have hd:=kz91 kz146 hf hz
  have hy:z.im ≠ 0:=ne_of_gt hz
  have hn:‖deriv f z‖ ≠ 0:=norm_ne_zero_iff.mpr hd
  rw [kz235 hz (kz224 hf (ne_of_gt hk) hz hc),
    kz225 hc,norm_mul,norm_mul,norm_div,Complex.norm_I,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos hk,abs_of_pos hz,Real.rpow_sub_one hy,kz160,norm_inv]
  congr 1
  field_simp
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
lemma kz237 {f f':ℝ → ℝ} {b:ℝ}
    (hmin:IsLocalMin f 0) (hf:∀ᶠ x in 𝓝 0,HasDerivAt f (f' x) x)
    (hf':HasDerivAt f' b 0):0 ≤ b:=by
  by_contra hb
  have hb:b < 0:=lt_of_not_ge hb
  have hzero:f' 0 = 0:=hmin.hasDerivAt_eq_zero hf.self_of_nhds
  have hrem:=(hasDerivAt_iff_isLittleO_nhds_zero.mp hf').bound
    (by linarith:0 < -b/2)
  have he:∀ᶠ x in 𝓝 (0:ℝ),
      HasDerivAt f (f' x) x ∧ f 0 ≤ f x ∧ |f' x - x*b| ≤ (-b/2)*|x|:=by
    filter_upwards [hf,hmin,hrem] with x hdx hmx hrx
    exact ⟨hdx,hmx,by simpa [hzero,Real.norm_eq_abs] using hrx⟩
  obtain ⟨δ,hδ,hall⟩:=Metric.eventually_nhds_iff.mp he
  have hball {x:ℝ} (hx:x ∈ Icc 0 (δ/2)):dist x 0 < δ:=by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
    linarith [hx.2]
  have hc:ContinuousOn f (Icc 0 (δ/2)):=by
    intro x hx
    exact (hall (hball hx)).1.continuousAt.continuousWithinAt
  obtain ⟨c,hcint,hceq⟩:=exists_deriv_eq_slope f (by linarith:0 < δ/2) hc
    (fun x hx => (hall (hball (Ioo_subset_Icc_self hx))).1.differentiableAt.differentiableWithinAt)
  have hcl:=hall (hball (Ioo_subset_Icc_self hcint))
  rw [hcl.1.deriv] at hceq
  have hend:=(hall (hball (show δ/2 ∈ Icc 0 (δ/2) by constructor <;> linarith))).2.1
  have hf'c:0 ≤ f' c:=by
    rw [hceq]
    exact div_nonneg (sub_nonneg.mpr hend) (by linarith)
  have hupper:=(le_abs_self (f' c-c*b)).trans hcl.2.2
  rw [abs_of_pos hcint.1] at hupper
  nlinarith [mul_neg_of_pos_of_neg hcint.1 hb]
lemma kz238 {u:ℂ → ℝ} {z v:ℂ}
    (hmin:IsLocalMin u z)
    (hu:∀ᶠ w in 𝓝 z,DifferentiableAt ℝ u w)
    (hv:DifferentiableAt ℝ (fun w => fderiv ℝ u w v) z) :
    0 ≤ fderiv ℝ (fun w => fderiv ℝ u w v) z v:=by
  let g:ℝ → ℂ:=fun t => z + t • v
  have hg (t:ℝ):HasDerivAt g v t:=by
    simpa [g] using (hasDerivAt_id t).smul_const v |>.const_add z
  have hgz:g 0 = z:=by simp [g]
  have hmin':IsLocalMin (u ∘ g) 0 :=
    (hgz ▸ hmin).comp_continuous (hg 0).continuousAt
  have hu':∀ᶠ t in 𝓝 (0:ℝ),HasDerivAt (u ∘ g) (fderiv ℝ u (g t) v) t:=by
    have ht:Tendsto g (𝓝 0) (𝓝 z):=hgz ▸ (hg 0).continuousAt
    filter_upwards [ht.eventually hu] with t ht
    exact ht.hasFDerivAt.comp_hasDerivAt t (hg t)
  have hv':HasDerivAt (fun t => fderiv ℝ u (g t) v)
      (fderiv ℝ (fun w => fderiv ℝ u w v) z v) 0:=by
    exact (hv.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hg 0) hgz.symm)
  exact kz237 hmin' hu' hv'
lemma kz239 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {z ξ:ℂ} (hz:z ∈ kz145)
    (hp:f z ≠ ξ) (k:ℝ) (v:ℂ) :
    DifferentiableAt ℝ (fun w => fderiv ℝ (kz219 f k ξ) w v) z:=by
  have hd:=(hf.1 z hz).differentiableAt (kz146.mem_nhds hz)
  have hn:=hd.continuousAt.eventually_ne hp
  have heq:(fun w => fderiv ℝ (kz219 f k ξ) w v) =ᶠ[𝓝 z]
      (fun w => k / w.im * v.im - (kz226 f ξ w * v).re):=by
    filter_upwards [kz146.mem_nhds hz,hn] with w hw hne
    rw [kz223 hf hw hne]
    unfold kz226
    congr 2
    ring
  have ha:DifferentiableAt ℝ (fun w:ℂ => k / w.im * v.im) z:=by
    have hi:=(hasDerivAt_inv (ne_of_gt hz)).differentiableAt.comp z
      Complex.imCLM.differentiableAt
    simpa only [div_eq_mul_inv,Function.comp_def,Complex.imCLM_apply] using
      (hi.const_mul k).mul_const v.im
  have hb:DifferentiableAt ℝ (fun w => (kz226 f ξ w * v).re) z :=
    Complex.reCLM.differentiableAt.comp z
      (((kz227 hf hz hp).differentiableAt.restrictScalars ℝ).mul_const v)
  exact (ha.sub hb).congr_of_eventuallyEq heq
lemma kz240 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:0 < k) {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) :
    ¬ IsLocalMin (kz219 f k ξ) z:=by
  intro hmin
  have hd:=(hf.1 z hz).differentiableAt (kz146.mem_nhds hz)
  have hu:∀ᶠ w in 𝓝 z,DifferentiableAt ℝ (kz219 f k ξ) w:=by
    filter_upwards [kz146.mem_nhds hz,hd.continuousAt.eventually_ne hp]
      with w hw hne
    exact kz222 hf hw hne k
  have h1:=kz238 hmin hu
    (kz239 hf hz hp k 1)
  have hI:=kz238 hmin hu
    (kz239 hf hz hp k Complex.I)
  have ht:=kz234 hf hk hz hp
  simp only [kz229,Matrix.trace,Matrix.diag,Fin.sum_univ_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one] at ht
  change kz228 _ z 1 1 + kz228 _ z Complex.I Complex.I < 0 at ht
  unfold kz228 at ht
  linarith
def kz241 (f:ℂ → ℂ) (k:ℝ) (ξ z:ℂ):ℝ :=
  ‖f z-ξ‖ / z.im^k
lemma kz242 {f:ℂ → ℂ} (hf:kz1 f kz145)
    (k:ℝ) (ξ:ℂ):ContinuousOn (kz241 f k ξ) kz145:=by
  apply ((hf.1.continuousOn.sub continuousOn_const).norm).div
    (Complex.continuous_im.continuousOn.rpow_const (fun z hz => Or.inl (ne_of_gt hz)))
  intro z hz
  exact ne_of_gt (Real.rpow_pos_of_pos hz k)
lemma kz243 {f:ℂ → ℂ} {k:ℝ} {ξ z:ℂ}
    (hz:z ∈ kz145) (hp:f z ≠ ξ):0 < kz241 f k ξ z:=by
  exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp)) (Real.rpow_pos_of_pos hz k)
lemma kz244 {f:ℂ → ℂ} {k:ℝ} {ξ z:ℂ}
    (hz:z ∈ kz145) (hp:f z ≠ ξ) :
    Real.log (kz241 f k ξ z) = -kz219 f k ξ z:=by
  rw [kz241,Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp))
    (ne_of_gt (Real.rpow_pos_of_pos hz k)),Real.log_rpow hz,kz219]
  ring
lemma kz245 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:0 < k) {z ξ:ℂ} (hz:z ∈ kz145) (hp:f z ≠ ξ) :
    ¬ IsLocalMax (kz241 f k ξ) z:=by
  intro hmax
  apply kz240 hf hk hz hp
  have hd:=(hf.1 z hz).differentiableAt (kz146.mem_nhds hz)
  filter_upwards [hmax,kz146.mem_nhds hz,hd.continuousAt.eventually_ne hp]
    with w hw hwH hwne
  have hl:=Real.log_le_log (kz243 hwH hwne) hw
  rw [kz244 hwH hwne,kz244 hz hp] at hl
  linarith
lemma kz246 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k b:ℝ} (hk:0 < k) (hb:0 < b) (ξ:ℂ) {U:Set ℂ}
    (ho:IsOpen U) (hcompact:IsCompact (closure U))
    (hH:closure U ⊆ kz145)
    (hboundary:∀ z ∈ frontier U,kz241 f k ξ z ≤ b)
    {z:ℂ} (hz:z ∈ U):kz241 f k ξ z < b:=by
  have hcont:=(kz242 hf k ξ).mono hH
  obtain ⟨a,ha,hmax⟩:=hcompact.exists_isMaxOn ⟨z,subset_closure hz⟩ hcont
  have hmaxle:kz241 f k ξ a ≤ b:=by
    by_contra hn
    have hab:b < kz241 f k ξ a:=lt_of_not_ge hn
    have haU:a ∈ U:=by
      by_contra hau
      have haf:a ∈ frontier U:=⟨ha,by simpa only [ho.interior_eq] using hau⟩
      exact (not_lt_of_ge (hboundary a haf)) hab
    have hane:f a ≠ ξ:=by
      intro he
      have he0:kz241 f k ξ a = 0:=by simp [kz241,he]
      linarith
    exact kz245 hf hk (hH ha) hane
      (hmax.isLocalMax (mem_of_superset (ho.mem_nhds haU) subset_closure))
  have hwhole:∀ w ∈ closure U,kz241 f k ξ w ≤ b :=
    fun w hw => (hmax hw).trans hmaxle
  have hzle:=hwhole z (subset_closure hz)
  apply lt_of_le_of_ne hzle
  intro he
  have hzne:f z ≠ ξ:=by
    intro hze
    have he0:kz241 f k ξ z = 0:=by simp [kz241,hze]
    linarith
  apply kz245 hf hk (hH (subset_closure hz)) hzne
  filter_upwards [ho.mem_nhds hz] with w hw
  exact (hwhole w (subset_closure hw)).trans_eq he.symm
def kz247 (f:ℂ → ℂ) (k:ℝ) (ξ z:ℂ):ℂ :=
  ((k:ℂ)*Complex.I/(z.im:ℂ))*(f z-ξ)*conj (kz204 f k z-ξ)
lemma kz248 {f:ℂ → ℂ} {k:ℝ} (hk:k ≠ 0)
    {ξ z:ℂ} (hz:z ∈ kz145) :
    kz247 f k ξ z = 0 ↔ f z = ξ ∨ kz204 f k z = ξ:=by
  have hc:((k:ℂ)*Complex.I/(z.im:ℂ)) ≠ 0:=div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))
  simp only [kz247,mul_eq_zero,hc,false_or,sub_eq_zero,map_eq_zero]
lemma kz249 {z:ℂ} (hz:z ∈ kz145) (k:ℝ) :
    DifferentiableAt ℝ (fun w:ℂ => (k:ℂ)*Complex.I/(w.im:ℂ)) z:=by
  have hn:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hi:=((hasDerivAt_inv hn).differentiableAt.restrictScalars ℝ).comp z
    ((Complex.ofRealCLM.comp Complex.imCLM).differentiableAt)
  simpa only [div_eq_mul_inv,Function.comp_def,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,Complex.imCLM_apply] using hi.const_mul ((k:ℂ)*Complex.I)
lemma kz250 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145) (k:ℝ) (ξ:ℂ) :
    DifferentiableAt ℝ (kz247 f k ξ) z:=by
  have hd:=((hf.1 z hz).differentiableAt (kz146.mem_nhds hz)).restrictScalars ℝ
  exact ((kz249 hz k).mul (hd.sub_const ξ)).mul
    (Complex.conjCLE.differentiableAt.comp z ((kz216 hf hz k).sub_const ξ))
lemma kz251 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {k:ℝ} {ξ z:ℂ} (hz:z ∈ kz145)
    (hc:kz204 f k z = ξ) :
    HasFDerivAt (kz247 f k ξ)
      ((((k:ℂ)*Complex.I/(z.im:ℂ))*(f z-ξ)) •
        (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ (kz204 f k) z))) z:=by
  have hd:=((hf.1 z hz).differentiableAt (kz146.mem_nhds hz)).restrictScalars ℝ
  have hG:=(kz216 hf hz k).hasFDerivAt.sub_const ξ
  have hh:=((kz249 hz k).hasFDerivAt.fun_mul
    (hd.hasFDerivAt.sub_const ξ)).fun_mul (Complex.conjCLE.hasFDerivAt.comp z hG)
  convert hh using 1 <;> first | rfl | simp only [Function.comp_def,hc,sub_self,map_zero,zero_smul,add_zero]
lemma kz252 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {k:ℝ} {ξ z:ℂ} (hz:z ∈ kz145)
    (hp:f z = ξ) :
    HasFDerivAt (kz247 f k ξ)
      ((((k:ℂ)*Complex.I/(z.im:ℂ))*conj (kz204 f k z-ξ)) •
        (fderiv ℝ f z)) z:=by
  have hd:=((hf.1 z hz).differentiableAt (kz146.mem_nhds hz)).restrictScalars ℝ
  have hG:=(kz216 hf hz k).hasFDerivAt.sub_const ξ
  have hh:=((kz249 hz k).hasFDerivAt.fun_mul
    (hd.hasFDerivAt.sub_const ξ)).fun_mul (Complex.conjCLE.hasFDerivAt.comp z hG)
  convert hh using 1 <;> first | rfl | simp only [Function.comp_def,hp,sub_self,mul_zero,zero_smul,zero_add,add_zero,smul_smul,Complex.conjCLE_apply,mul_comm]
lemma kz253 (A:ℂ →L[ℝ] ℂ) :
    LinearMap.det (Complex.conjCLE.toContinuousLinearMap.comp A).toLinearMap =
      -LinearMap.det A.toLinearMap:=by
  rw [kz12,kz12]
  simp only [ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,Complex.conjCLE_apply,Complex.conj_re,Complex.conj_im]
  ring
lemma kz254 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} {ξ z:ℂ} (hz:z ∈ kz145) (hc:kz204 f k z = ξ) :
    LinearMap.det (fderiv ℝ (kz247 f k ξ) z).toLinearMap =
      -‖((k:ℂ)*Complex.I/(z.im:ℂ))*(f z-ξ)‖^2 * ‖deriv f z‖^2 *
        kz205 f k z:=by
  rw [(kz251 hf hz hc).fderiv,
    kz55,kz253,kz205]
  have hd:‖deriv f z‖ ≠ 0:=norm_ne_zero_iff.mpr
    (kz91 kz146 hf hz)
  field_simp
lemma kz255 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:k ≠ 0) {ξ z:ℂ} (hz:z ∈ kz145) (hp:f z = ξ) :
    0 < LinearMap.det (fderiv ℝ (kz247 f k ξ) z).toLinearMap:=by
  have hG:kz204 f k z ≠ ξ:=fun hc => kz224 hf hk hz hc hp
  rw [(kz252 hf hz hp).fderiv,kz55,
    kz76 ((hf.1 z hz).differentiableAt (kz146.mem_nhds hz))]
  apply mul_pos
  · apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact mul_ne_zero (div_ne_zero
      (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
      ((map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hG))
  · exact sq_pos_of_pos (norm_pos_iff.mpr (kz91 kz146 hf hz))
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
lemma HasLogIncrement.path_trans {a b c:ℂ} {γ:Path a b} {η:Path b c}
    {p q:ℂ} (hγ:HasLogIncrement γ.toContinuousMap p)
    (hη:HasLogIncrement η.toContinuousMap q) :
    HasLogIncrement (γ.trans η).toContinuousMap (p+q):=by
  obtain ⟨A,hA,hp⟩:=hγ
  obtain ⟨B,hB,hq⟩:=hη
  let α:Path (A 0) (A 1):=⟨A,rfl,rfl⟩
  let β:Path (A 1) (B 1+A 1-B 0) :=
    ⟨⟨fun t => B t+A 1-B 0,by fun_prop⟩,by simp,rfl⟩
  refine ⟨(α.trans β).toContinuousMap,?_,?_⟩
  · intro t
    change Complex.exp ((α.trans β) t) = (γ.trans η) t
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs with h
    · exact hA _
    · dsimp only [β,ContinuousMap.coe_mk,Path.coe_mk_mk]
      have heA:Complex.exp (A 1) = b:=(hA 1).trans γ.target
      have heB:Complex.exp (B 0) = b:=(hB 0).trans η.source
      have hb:b ≠ 0:=heB ▸ Complex.exp_ne_zero (B 0)
      rw [Complex.exp_sub,Complex.exp_add,heA,heB,hB]
      exact mul_div_cancel_right₀ _ hb
  · change (α.trans β) 1-(α.trans β) 0=p+q
    simp only [Path.target,Path.source]
    linear_combination hp+hq
lemma HasLogIncrement.path_symm {a b:ℂ} {γ:Path a b} {q:ℂ}
    (hγ:HasLogIncrement γ.toContinuousMap q) :
    HasLogIncrement γ.symm.toContinuousMap (-q):=by
  obtain ⟨A,hA,hq⟩:=hγ
  refine ⟨⟨fun t => A (unitInterval.symm t),by fun_prop⟩,?_,?_⟩
  · exact fun t => hA (unitInterval.symm t)
  · simp only [ContinuousMap.coe_mk,unitInterval.symm_one,unitInterval.symm_zero]
    linear_combination -hq
lemma kz256 {a b:ℂ} (γ:Path a b) (hn:∀ t,γ t ≠ 0) :
    ∃ q,HasLogIncrement γ.toContinuousMap q:=by
  let:=(convex_Icc (𝕜:=ℝ) (0:ℝ) 1).contractibleSpace
    (show (Icc (0:ℝ) 1).Nonempty from ⟨0,by simp⟩)
  let:=(convex_Icc (𝕜:=ℝ) (0:ℝ) 1).locallyPathConnectedSpace
  obtain ⟨A,hA⟩:=exists_log_lift_of_simplyConnected (0:unitInterval) γ.toContinuousMap hn
  exact ⟨A 1-A 0,A,hA,rfl⟩
lemma HasLogIncrement.of_slit (γ:C(unitInterval,ℂ))
    (hγ:∀ t,γ t ∈ Complex.slitPlane) :
    HasLogIncrement γ (Complex.log (γ 1)-Complex.log (γ 0)):=by
  exact ⟨⟨fun t => Complex.log (γ t),γ.continuous.clog hγ⟩,
    fun t => Complex.exp_log (Complex.slitPlane_ne_zero (hγ t)),rfl⟩
lemma HasLogIncrement.of_neg_slit (γ:C(unitInterval,ℂ))
    (hγ:∀ t,-γ t ∈ Complex.slitPlane) :
    HasLogIncrement γ (Complex.log (-γ 1)-Complex.log (-γ 0)):=by
  refine ⟨⟨fun t => Complex.log (-γ t)+(Real.pi:ℂ)*Complex.I,
    ((γ.continuous.neg).clog hγ).add continuous_const⟩,?_,?_⟩
  · intro t
    simp only [ContinuousMap.coe_mk,Complex.exp_add,Complex.exp_pi_mul_I]
    rw [Complex.exp_log (Complex.slitPlane_ne_zero (hγ t))]
    ring
  · dsimp only [ContinuousMap.coe_mk]
    ring
lemma kz257 {z:ℂ} (hi:z.im < 0) :
    Complex.log (-z) = Complex.log z+(Real.pi:ℂ)*Complex.I:=by
  apply Complex.ext
  · simp [Complex.log_re,norm_neg]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_add_pi_of_im_neg hi
lemma kz258 {z:ℂ} (hi:0 < z.im) :
    Complex.log (-z) = Complex.log z-(Real.pi:ℂ)*Complex.I:=by
  apply Complex.ext
  · simp [Complex.log_re,norm_neg]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi
def kz259 (r h:ℝ):Path ((-r:ℂ)-(h:ℂ)*Complex.I)
    ((-r:ℂ)-(h:ℂ)*Complex.I) :=
  (((Path.segment ((-r:ℂ)-(h:ℂ)*Complex.I) ((r:ℂ)-(h:ℂ)*Complex.I)).trans
    (Path.segment ((r:ℂ)-(h:ℂ)*Complex.I) ((r:ℂ)+(h:ℂ)*Complex.I))).trans
    (Path.segment ((r:ℂ)+(h:ℂ)*Complex.I) ((-r:ℂ)+(h:ℂ)*Complex.I))).trans
    (Path.segment ((-r:ℂ)+(h:ℂ)*Complex.I) ((-r:ℂ)-(h:ℂ)*Complex.I))
lemma kz260 {r h:ℝ} (hr:0 < r) (hh:0 < h) :
    HasLogIncrement (kz259 r h).toContinuousMap (2*Real.pi*Complex.I):=by
  let a:ℂ:=(-r:ℂ)-(h:ℂ)*Complex.I
  let b:ℂ:=(r:ℂ)-(h:ℂ)*Complex.I
  let c:ℂ:=(r:ℂ)+(h:ℂ)*Complex.I
  let d:ℂ:=(-r:ℂ)+(h:ℂ)*Complex.I
  have hab (t:unitInterval):(Path.segment a b) t ∈ Complex.slitPlane:=by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,a,b,Complex.add_im,
      Complex.sub_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_im]
    nlinarith
  have hbc (t:unitInterval):(Path.segment b c) t ∈ Complex.slitPlane:=by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,b,c,Complex.add_re,
      Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    nlinarith
  have hcd (t:unitInterval):(Path.segment c d) t ∈ Complex.slitPlane:=by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,c,d,Complex.add_im,
      Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_im]
    nlinarith
  have hda (t:unitInterval) : -(Path.segment d a) t ∈ Complex.slitPlane:=by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,d,a,Complex.add_re,
      Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_re]
    nlinarith
  have h₁:=HasLogIncrement.of_slit (Path.segment a b).toContinuousMap hab
  have h₂:=HasLogIncrement.of_slit (Path.segment b c).toContinuousMap hbc
  have h₃:=HasLogIncrement.of_slit (Path.segment c d).toContinuousMap hcd
  have h₄:=HasLogIncrement.of_neg_slit (Path.segment d a).toContinuousMap hda
  have he:=((h₁.path_trans h₂).path_trans h₃).path_trans h₄
  have ha:a.im < 0:=by simpa [a] using hh
  have hd:0 < d.im:=by simpa [d] using hh
  have hla:=kz257 ha
  have hld:=kz258 hd
  convert he using 1
  · rfl
  · simp only [Path.coe_toContinuousMap,Path.target,Path.source]
    rw [hla,hld]
    ring
lemma kz261 {r h:ℝ} (hr:0 < r) (hh:0 < h) :
    kz18 (kz259 r h).toContinuousMap = 1:=by
  apply kz20 ((kz259 r h).target.trans (kz259 r h).source.symm)
  simpa only [Int.cast_one,one_mul] using kz260 hr hh
lemma kz262 {a b:ℂ} (γ:Path a b)
    (hc:γ 1 = γ 0) (hn:∀ t,γ t ≠ 0) :
    kz18 γ.symm.toContinuousMap = -kz18 γ.toContinuousMap:=by
  apply kz20 (by simpa using hc.symm)
  convert (kz19 γ.toContinuousMap hc hn).path_symm using 1
  push_cast
  ring
lemma kz263 {a b c d:ℂ}
    (α:Path a b) (β:Path b c) (χ:Path c d) (δ:Path d a)
    (hβc:β 1 = β 0) (hδc:δ 1 = δ 0)
    (hχ:χ.toContinuousMap = α.symm.toContinuousMap)
    (hα:∀ t,α t ≠ 0) (hβ:∀ t,β t ≠ 0) (hδ:∀ t,δ t ≠ 0) :
    kz18 (((α.trans β).trans χ).trans δ).toContinuousMap =
      kz18 β.toContinuousMap + kz18 δ.toContinuousMap:=by
  obtain ⟨p,hp⟩:=kz256 α hα
  have hq:=kz19 β.toContinuousMap hβc hβ
  have hr:=kz19 δ.toContinuousMap hδc hδ
  have hs:HasLogIncrement χ.toContinuousMap (-p):=hχ ▸ hp.path_symm
  apply kz20
    ((((α.trans β).trans χ).trans δ).target.trans
      (((α.trans β).trans χ).trans δ).source.symm)
  convert ((hp.path_trans hq).path_trans hs).path_trans hr using 1
  push_cast
  ring
lemma kz264 (H:ℂ → ℂ) (hH:Continuous H) (r h:ℝ)
    (hp:∀ x:ℝ,H ((x:ℂ)+(h:ℂ)*Complex.I) =
      H ((x:ℂ)-(h:ℂ)*Complex.I))
    (hn:∀ z ∈ range (kz259 r h),H z ≠ 0) :
    kz18 (((kz259 r h).map hH).toContinuousMap) =
      kz18 (((Path.segment ((r:ℂ)-(h:ℂ)*Complex.I)
        ((r:ℂ)+(h:ℂ)*Complex.I)).map hH).toContinuousMap) -
      kz18 (((Path.segment ((-r:ℂ)-(h:ℂ)*Complex.I)
        ((-r:ℂ)+(h:ℂ)*Complex.I)).map hH).toContinuousMap):=by
  let a:ℂ:=(-r:ℂ)-(h:ℂ)*Complex.I
  let b:ℂ:=(r:ℂ)-(h:ℂ)*Complex.I
  let c:ℂ:=(r:ℂ)+(h:ℂ)*Complex.I
  let d:ℂ:=(-r:ℂ)+(h:ℂ)*Complex.I
  let α:=(Path.segment a b).map hH
  let β:=(Path.segment b c).map hH
  let χ:=(Path.segment c d).map hH
  let δ:=(Path.segment d a).map hH
  have hpc:H c = H b:=hp r
  have hpa:H d = H a:=by simpa only [Complex.ofReal_neg] using hp (-r)
  have hβc:β 1 = β 0:=β.target.trans (hpc.trans β.source.symm)
  have hδc:δ 1 = δ 0:=δ.target.trans (hpa.symm.trans δ.source.symm)
  have hχ:χ.toContinuousMap = α.symm.toContinuousMap:=by
    ext t
    simp only [Path.coe_toContinuousMap,χ,α,Path.map_coe,Function.comp_apply,Path.symm_apply,
      Path.segment_apply,AffineMap.lineMap_apply_module]
    have he₁:(1-(t:ℝ)) • c + (t:ℝ) • d =
        (((1-(t:ℝ))*r+(t:ℝ)*(-r):ℝ):ℂ)+(h:ℂ)*Complex.I:=by
      simp [c,d,Complex.real_smul]
      ring
    have he₂:(1-(unitInterval.symm t:ℝ)) • a+(unitInterval.symm t:ℝ) • b =
        (((1-(t:ℝ))*r+(t:ℝ)*(-r):ℝ):ℂ)-(h:ℂ)*Complex.I:=by
      simp [a,b,Complex.real_smul]
      ring
    rw [he₁,he₂]
    exact hp _
  have hsub:range (Path.segment a b) ∪ range (Path.segment b c) ∪
      range (Path.segment c d) ∪ range (Path.segment d a) ⊆ range (kz259 r h):=by
    intro z hz
    change z ∈ range ((((Path.segment a b).trans (Path.segment b c)).trans
      (Path.segment c d)).trans (Path.segment d a))
    simpa only [Path.trans_range] using hz
  have hα:∀ t,α t ≠ 0:=fun t => hn _ (hsub (Or.inl (Or.inl (Or.inl ⟨t,rfl⟩))))
  have hβ:∀ t,β t ≠ 0:=fun t => hn _ (hsub (Or.inl (Or.inl (Or.inr ⟨t,rfl⟩))))
  have hδ:∀ t,δ t ≠ 0:=fun t => hn _ (hsub (Or.inr ⟨t,rfl⟩))
  have hi:=kz263 α β χ δ hβc hδc hχ hα hβ hδ
  have hs:=kz262 δ hδc hδ
  have he:δ.symm.toContinuousMap = ((Path.segment a d).map hH).toContinuousMap:=by
    ext t
    simp [δ,Path.segment_symm]
  rw [he] at hs
  have hg:(((kz259 r h).map hH).toContinuousMap) =
      (((α.trans β).trans χ).trans δ).toContinuousMap:=by
    simp only [kz259,Path.map_trans]
    rfl
  rw [hg,hi]
  change kz18 β.toContinuousMap + kz18 δ.toContinuousMap =
    kz18 β.toContinuousMap - kz18 ((Path.segment a d).map hH).toContinuousMap
  rw [hs]
  omega
lemma kz265 {γ:ℝ → ℂ} {d:ℂ} (hd:HasDerivAt γ d 0) :
    HasFDerivAt (fun w:ℂ => γ w.im-γ 0-w.re • (Complex.I*d))
      ((-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ) 0:=by
  have h:=((hd.hasFDerivAt.comp (0:ℂ) (Complex.imCLM.hasFDerivAt)).sub_const
    (γ 0)).sub (Complex.reCLM.hasFDerivAt.smul_const (Complex.I*d))
  have he:ContinuousLinearMap.toSpanSingleton ℝ d ∘L Complex.imCLM -
      Complex.reCLM.smulRight (Complex.I*d) =
      (-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ:=by
    ext z
    apply Complex.ext <;> simp [Complex.real_smul] <;> ring
  rw [he] at h
  exact h
lemma kz266 {d:ℂ} (hd:d ≠ 0) :
    0 < LinearMap.det (((-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ).toLinearMap):=by
  rw [kz55]
  simp only [ContinuousLinearMap.coe_id,LinearMap.det_id,mul_one]
  exact sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hd))
lemma kz267 {γ:ℝ → ℂ} (hp:Function.Periodic γ 1)
    (hinj:InjOn γ (Ico (0:ℝ) 1)) {t:ℝ} (ht:t ∈ Icc (-(1/2:ℝ)) (1/2))
    (he:γ t = γ 0):t = 0:=by
  by_cases hn:0 ≤ t
  · exact hinj ⟨hn,by linarith [ht.2]⟩ ⟨le_rfl,by norm_num⟩ he
  · have hne:t+1 = 0:=hinj ⟨by linarith [ht.1],by linarith⟩
      ⟨le_rfl,by norm_num⟩ ((hp t).trans he)
    linarith [ht.1]
lemma kz268 {γ:ℝ → ℂ} (hc:Continuous γ)
    (hp:Function.Periodic γ 1) (hinj:InjOn γ (Ico (0:ℝ) 1))
    {d:ℂ} (hd:HasDerivAt γ d 0) (hdn:d ≠ 0) :
    ∃ δ:ℝ,0 < δ ∧ ∀ w:ℂ,|w.re| ≤ δ → |w.im| ≤ 1/2 →
      (γ w.im-γ 0-w.re • (Complex.I*d) = 0 ↔ w = 0):=by
  let H:ℂ → ℂ:=fun w => γ w.im-γ 0-w.re • (Complex.I*d)
  have hH0:H 0 = 0:=by simp [H]
  obtain ⟨_,r,hr,hlocal⟩:=kz51 hH0 (kz265 hd)
    (kz266 hdn)
  let η:=min (r/2) (1/4:ℝ)
  have hη:0 < η:=lt_min (by linarith) (by norm_num)
  let K:Set ℝ:=Icc (-(1/2:ℝ)) (1/2) ∩ {t | η ≤ |t|}
  have hK:IsCompact K:=isCompact_Icc.inter_right
    (isClosed_le continuous_const continuous_abs)
  obtain ⟨m,hm,hbound⟩:=hK.exists_forall_le' ((hc.sub continuous_const).norm.continuousOn)
    (a:=(0:ℝ)) (fun t ht => norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro he
      have he0:=kz267 hp hinj ht.1 he
      have hb:η ≤ |t|:=ht.2
      simp only [he0,abs_zero] at hb
      exact (not_le.mpr hη) hb)))
  let δ:=min (r/2) (m/(2*‖d‖))
  have hδ:0 < δ:=lt_min (by linarith) (div_pos hm (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro w hre him
  constructor
  · intro hz
    by_contra hwn
    by_cases hi:|w.im| < η
    · have hn:‖w-0‖ < 2*r:=by
        simpa only [sub_zero] using calc
          ‖w‖ ≤ |w.re|+|w.im|:=Complex.norm_le_abs_re_add_abs_im w
          _ < r/2+r/2:=by
            have hδr:=min_le_left (r/2) (m/(2*‖d‖))
            have hηr:=min_le_left (r/2) (1/4:ℝ)
            dsimp only [δ] at hre
            dsimp only [η] at hi
            linarith
          _ < 2*r:=by linarith
      have hnon:=Complex.slitPlane_ne_zero (hlocal w hn hwn)
      apply hnon
      simp only [H,hz,zero_div]
    · have hb:=hbound w.im ⟨abs_le.mp him,not_lt.mp hi⟩
      change m ≤ ‖γ w.im-γ 0‖ at hb
      have he:γ w.im-γ 0 = w.re • (Complex.I*d):=sub_eq_zero.mp hz
      have hnorm:‖γ w.im-γ 0‖ = |w.re| *‖d‖:=by
        rw [he,norm_smul,Real.norm_eq_abs,norm_mul,Complex.norm_I,one_mul]
      have hδm:δ*‖d‖ ≤ m/2:=by
        have h:=min_le_right (r/2) (m/(2*‖d‖))
        have hn:=norm_pos_iff.mpr hdn
        dsimp only [δ]
        apply (le_div_iff₀ hn).mp
        convert h using 1; field_simp
      have:|w.re| *‖d‖ ≤ m/2:=(mul_le_mul_of_nonneg_right hre (norm_nonneg d)).trans hδm
      linarith
  · rintro rfl
    simp
def kz269 (r h:ℝ):Set ℂ:={z | |z.re| ≤ r ∧ |z.im| ≤ h}
lemma kz270 (r h:ℝ):Convex ℝ (kz269 r h):=by
  have he:kz269 r h = (Complex.reCLM ⁻¹' Icc (-r) r) ∩
      (Complex.imCLM ⁻¹' Icc (-h) h):=by
    ext z
    simp [kz269,abs_le]
  rw [he]
  exact ((convex_Icc (-r) r).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Icc (-h) h).linear_preimage Complex.imCLM.toLinearMap)
lemma kz271 {r h:ℝ} (hr:0 ≤ r) (hh:0 ≤ h) (t:unitInterval) :
    kz259 r h t ∈ kz269 r h:=by
  have hs (a b:ℂ) (ha:a ∈ kz269 r h) (hb:b ∈ kz269 r h) :
      range (Path.segment a b) ⊆ kz269 r h:=by
    rintro _ ⟨s,rfl⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module] using
      (kz270 r h) ha hb (sub_nonneg.mpr s.2.2) s.2.1 (by ring)
  have h₁:((-r:ℂ)-(h:ℂ)*Complex.I) ∈ kz269 r h:=by
    simp [kz269,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₂:((r:ℂ)-(h:ℂ)*Complex.I) ∈ kz269 r h:=by
    simp [kz269,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₃:((r:ℂ)+(h:ℂ)*Complex.I) ∈ kz269 r h:=by
    simp [kz269,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₄:((-r:ℂ)+(h:ℂ)*Complex.I) ∈ kz269 r h:=by
    simp [kz269,abs_of_nonneg hr,abs_of_nonneg hh]
  have hb:range (kz259 r h) ⊆ kz269 r h:=by
    simp only [kz259,Path.trans_range]
    exact union_subset (union_subset (union_subset (hs _ _ h₁ h₂) (hs _ _ h₂ h₃))
      (hs _ _ h₃ h₄)) (hs _ _ h₄ h₁)
  exact hb ⟨t,rfl⟩
lemma kz272 {r h:ℝ} (hr:0 < r) (hh:0 < h) (t:unitInterval) :
    kz259 r h t ≠ 0:=by
  obtain ⟨T,hT,_⟩:=kz260 hr hh
  exact (hT t ▸ Complex.exp_ne_zero (T t))
lemma kz273 {γ:ℝ → ℂ} (hc:Continuous γ)
    (hp:Function.Periodic γ 1) (hinj:InjOn γ (Ico (0:ℝ) 1))
    {d:ℂ} (hd:HasDerivAt γ d 0) (hdn:d ≠ 0) :
    ∃ δ:ℝ,0 < δ ∧ ∀ r:ℝ,0 < r → r ≤ δ →
      kz24 ⟨fun t:unitInterval => γ ((t:ℝ)-1/2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩
        (γ 0+r • (Complex.I*d)) -
      kz24 ⟨fun t:unitInterval => γ ((t:ℝ)-1/2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩
        (γ 0-r • (Complex.I*d)) = 1:=by
  let H:C(ℂ,ℂ):=⟨fun w => γ w.im-γ 0-w.re • (Complex.I*d),
    ((hc.comp Complex.continuous_im).sub continuous_const).sub
      (Complex.continuous_re.smul continuous_const)⟩
  let A:ℂ →L[ℝ] ℂ:=(-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ
  obtain ⟨δ,hδ,hzero⟩:=kz268 hc hp hinj hd hdn
  refine ⟨δ,hδ,?_⟩
  intro r hr hrd
  let p:=kz259 r (1/2)
  have hp0:∀ t,p t ≠ 0:=kz272 hr (by norm_num)
  have hmem:∀ t,p t ∈ kz269 r (1/2):=kz271 hr.le (by norm_num)
  have hz:∀ z ∈ kz269 r (1/2),H z = 0 ↔ z ∈ ({0}:Finset ℂ):=by
    intro z hz
    simpa only [Finset.mem_singleton,H,ContinuousMap.coe_mk] using hzero z (hz.1.trans hrd) hz.2
  have hn:∀ t,H (p t) ≠ 0:=by
    intro t ht
    exact hp0 t (Finset.mem_singleton.mp ((hz _ (hmem t)).mp ht))
  have hi:=kz61 (kz270 r (1/2)) {0} H
    (fun _ => A) (by intro z hz; simpa [Finset.mem_singleton,kz269] using
      (show |z.re| ≤ r ∧ |z.im| ≤ 1/2 from by simpa [Finset.mem_singleton.mp hz] using
        (show (0:ℝ) ≤ r ∧ (0:ℝ) ≤ 1/2 from ⟨hr.le,by norm_num⟩))) hz
    (by intro z hz; have he:=Finset.mem_singleton.mp hz; subst z
        exact ⟨kz265 hd,ne_of_gt (kz266 hdn)⟩)
    p.toContinuousMap (p.target.trans p.source.symm) hmem hn
  have hindex:kz59 A = 1:=by
    simp only [A,kz59,if_pos (kz266 hdn)]
  have hpindex:kz24 p.toContinuousMap 0 = 1:=by
    change kz18 (⟨fun t => p t-0,by fun_prop⟩:C(unitInterval,ℂ)) = 1
    have he:(⟨fun t => p t-0,by fun_prop⟩:C(unitInterval,ℂ)) = p.toContinuousMap:=by
      ext t; simp
    rw [he]
    exact kz261 hr (by norm_num)
  simp only [Finset.sum_singleton,hindex,hpindex,mul_one] at hi
  have hperiod:∀ x:ℝ,H ((x:ℂ)+((1/2:ℝ):ℂ)*Complex.I) =
      H ((x:ℂ)-((1/2:ℝ):ℂ)*Complex.I):=by
    intro x
    change γ (((x:ℂ)+((1/2:ℝ):ℂ)*Complex.I).im)-γ 0-
        (((x:ℂ)+((1/2:ℝ):ℂ)*Complex.I).re) • (Complex.I*d) = _
    have he:γ (1/2) = γ (-(1/2)):=by
      convert hp (-(1/2)) using 1; norm_num
    simpa only [H,ContinuousMap.coe_mk,Complex.add_im,Complex.sub_im,Complex.add_re,
      Complex.sub_re,Complex.mul_im,Complex.mul_re,Complex.ofReal_im,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,mul_one,sub_zero,add_zero,zero_add,
      zero_sub] using congrArg (fun z:ℂ => z-γ 0-x • (Complex.I*d)) he
  have hstrip:=kz264 H H.continuous r (1/2) hperiod (by
    rintro _ ⟨t,rfl⟩; exact hn t)
  have hcomp:((kz259 r (1/2)).map H.continuous).toContinuousMap =
      H.comp p.toContinuousMap:=rfl
  rw [hcomp,hi] at hstrip
  have hright:((Path.segment ((r:ℂ)-((1/2:ℝ):ℂ)*Complex.I)
        ((r:ℂ)+((1/2:ℝ):ℂ)*Complex.I)).map H.continuous).toContinuousMap =
      (⟨fun t:unitInterval => γ ((t:ℝ)-1/2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩:C(unitInterval,ℂ)) -
        ContinuousMap.const _ (γ 0+r • (Complex.I*d)):=by
    ext t
    simp only [Path.coe_toContinuousMap,Path.map_coe,Function.comp_apply,
      Path.segment_apply,AffineMap.lineMap_apply_module,H,ContinuousMap.coe_mk,
      ContinuousMap.sub_apply,ContinuousMap.const_apply]
    have hre:((1-(t:ℝ)) • ((r:ℂ)-((1/2:ℝ):ℂ)*Complex.I)+
        (t:ℝ) • ((r:ℂ)+((1/2:ℝ):ℂ)*Complex.I)).re = r:=by
      simp [Complex.real_smul]; ring
    have him:((1-(t:ℝ)) • ((r:ℂ)-((1/2:ℝ):ℂ)*Complex.I)+
        (t:ℝ) • ((r:ℂ)+((1/2:ℝ):ℂ)*Complex.I)).im = (t:ℝ)-1/2:=by
      simp [Complex.real_smul]; ring
    rw [hre,him]; abel
  have hleft:((Path.segment ((-r:ℂ)-((1/2:ℝ):ℂ)*Complex.I)
        ((-r:ℂ)+((1/2:ℝ):ℂ)*Complex.I)).map H.continuous).toContinuousMap =
      (⟨fun t:unitInterval => γ ((t:ℝ)-1/2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩:C(unitInterval,ℂ)) -
        ContinuousMap.const _ (γ 0-r • (Complex.I*d)):=by
    ext t
    simp only [Path.coe_toContinuousMap,Path.map_coe,Function.comp_apply,
      Path.segment_apply,AffineMap.lineMap_apply_module,H,ContinuousMap.coe_mk,
      ContinuousMap.sub_apply,ContinuousMap.const_apply]
    have hre:((1-(t:ℝ)) • ((-r:ℂ)-((1/2:ℝ):ℂ)*Complex.I)+
        (t:ℝ) • ((-r:ℂ)+((1/2:ℝ):ℂ)*Complex.I)).re = -r:=by
      simp [Complex.real_smul]; ring
    have him:((1-(t:ℝ)) • ((-r:ℂ)-((1/2:ℝ):ℂ)*Complex.I)+
        (t:ℝ) • ((-r:ℂ)+((1/2:ℝ):ℂ)*Complex.I)).im = (t:ℝ)-1/2:=by
      simp [Complex.real_smul]; ring
    rw [hre,him,neg_smul]; abel
  rw [hright,hleft] at hstrip
  exact hstrip.symm
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def kz274 {γ:ℝ → ℂ} (hc:Continuous γ) (s:ℝ):C(unitInterval,ℂ) :=
  ⟨fun t => γ ((t:ℝ)+s),hc.comp (continuous_subtype_val.add continuous_const)⟩
lemma kz275 {γ:ℝ → ℂ} (hc:Continuous γ)
    (hp:Function.Periodic γ 1) (s:ℝ) :
    kz274 hc s 1 = kz274 hc s 0:=by
  simpa only [kz274,ContinuousMap.coe_mk,show ((1:unitInterval):ℝ) = 1 from rfl,show ((0:unitInterval):ℝ) = 0 from rfl,
    zero_add,add_zero,add_comm] using hp s
lemma kz276 {γ:ℝ → ℂ} (hc:Continuous γ)
    (hp:Function.Periodic γ 1) (s:ℝ):range (kz274 hc s) = range γ:=by
  apply Subset.antisymm
  · rintro _ ⟨t,rfl⟩; exact ⟨(t:ℝ)+s,rfl⟩
  · rintro _ ⟨t,rfl⟩
    obtain ⟨u,hu,he⟩:=hp.exists_mem_Ico (by norm_num) t s
    refine ⟨⟨u-s,⟨by linarith [hu.1],by linarith [hu.2]⟩⟩,?_⟩
    simpa only [kz274,ContinuousMap.coe_mk,sub_add_cancel] using he.symm
lemma kz277 {γ:ℝ → ℂ} (hc:Continuous γ)
    (hp:Function.Periodic γ 1) {a:ℂ} (ha:a ∉ range γ) (s:ℝ) :
    kz24 (kz274 hc s) a = kz24 (kz274 hc 0) a:=by
  let H:C(unitInterval × unitInterval,ℂ) :=
    ⟨fun p => γ ((p.2:ℝ)+(p.1:ℝ)*s)-a,by fun_prop⟩
  have hi:=kz23 H (by
    intro p; exact sub_ne_zero.mpr (fun he => ha ⟨_,he⟩)) (by
    intro t
    change γ (1+(t:ℝ)*s)-a = γ (0+(t:ℝ)*s)-a
    simpa only [zero_add,add_zero,add_comm] using congrArg (fun z:ℂ => z-a) (hp ((t:ℝ)*s)))
  simpa only [H,kz24,kz274,show ((1:unitInterval):ℝ) = 1 from rfl,show ((0:unitInterval):ℝ) = 0 from rfl,
    ContinuousMap.coe_mk,one_mul,zero_mul] using hi
lemma kz278 {γ:ℝ → ℂ} (hp:Function.Periodic γ 1)
    {d:ℂ} {δ:ℝ}
    (hz:∀ w:ℂ,|w.re| ≤ δ → |w.im| ≤ 1/2 →
      (γ w.im-γ 0-w.re • (Complex.I*d) = 0 ↔ w = 0))
    {r:ℝ} (hr:r ≠ 0) (hrd:|r| ≤ δ) :
    γ 0+r • (Complex.I*d) ∉ range γ:=by
  rintro ⟨t,ht⟩
  obtain ⟨u,hu,he⟩:=hp.exists_mem_Ico (by norm_num) t (-(1/2))
  have hui:|u| ≤ 1/2:=abs_le.mpr ⟨hu.1,by linarith [hu.2]⟩
  let w:ℂ:=(r:ℂ)+(u:ℂ)*Complex.I
  have hre:w.re = r:=by simp [w]
  have him:w.im = u:=by simp [w]
  have hw:w = 0:=(hz w (hre ▸ hrd) (him ▸ hui)).mp (by
    rw [hre,him,← he,ht]; abel)
  have h:=congrArg Complex.re hw
  exact hr (by simpa only [hre,Complex.zero_re] using h)
lemma kz279 {γ:ℝ → ℂ} (hc:Continuous γ)
    (hp:Function.Periodic γ 1) (hinj:InjOn γ (Ico (0:ℝ) 1))
    {d:ℂ} (hd:HasDerivAt γ d 0) (hdn:d ≠ 0) :
    ∃ δ:ℝ,0 < δ ∧ ∀ r:ℝ,0 < r → r ≤ δ →
      γ 0+r • (Complex.I*d) ∉ range γ ∧ γ 0-r • (Complex.I*d) ∉ range γ ∧
      kz24 (kz274 hc 0) (γ 0+r • (Complex.I*d)) -
      kz24 (kz274 hc 0) (γ 0-r • (Complex.I*d)) = 1:=by
  obtain ⟨δ,hδ,hjump⟩:=kz273 hc hp hinj hd hdn
  obtain ⟨ε,hε,hzero⟩:=kz268 hc hp hinj hd hdn
  refine ⟨min δ ε,lt_min hδ hε,?_⟩
  intro r hr hre
  have hn₁:=kz278 hp hzero hr.ne'
    (show |r| ≤ ε from (abs_of_pos hr).symm ▸ hre.trans (min_le_right _ _))
  have hn₂:γ 0-r • (Complex.I*d) ∉ range γ:=by
    simpa only [neg_smul,sub_eq_add_neg] using kz278 hp hzero
      (neg_ne_zero.mpr hr.ne') (show |-r| ≤ ε by
        rw [abs_neg,abs_of_pos hr]; exact hre.trans (min_le_right _ _))
  refine ⟨hn₁,hn₂,?_⟩
  have hj:=hjump r hr (hre.trans (min_le_left _ _))
  change kz24 (kz274 hc (-(1/2))) (γ 0+r • (Complex.I*d))-
    kz24 (kz274 hc (-(1/2))) (γ 0-r • (Complex.I*d)) = 1 at hj
  rwa [kz277 hc hp hn₁,kz277 hc hp hn₂] at hj
lemma kz280 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0)
    {a:ℂ} (ha:∀ t,a.re < (γ t).re):kz24 γ a = 0:=by
  apply kz20 (by simp [hloop])
  have h:=HasLogIncrement.of_slit (⟨fun t => γ t-a,by fun_prop⟩:C(unitInterval,ℂ))
    (fun t => Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr (ha t))))
  simpa only [ContinuousMap.coe_mk,hloop,sub_self,Int.cast_zero,zero_mul] using h
lemma kz281 {γ:ℝ → ℂ} (hc:Continuous γ)
    (hp:Function.Periodic γ 1) (hinj:InjOn γ (Ico (0:ℝ) 1))
    {d:ℂ} (hd:HasDerivAt γ d 0) (hdi:d.im < 0)
    (hmin:∀ t,(γ 0).re ≤ (γ t).re) :
    ∃ δ:ℝ,0 < δ ∧ ∀ r:ℝ,0 < r → r ≤ δ →
      γ 0+r • (Complex.I*d) ∉ range γ ∧
      kz24 (kz274 hc 0) (γ 0+r • (Complex.I*d)) = 1:=by
  have hdn:d ≠ 0:=by intro he; simp only [he,Complex.zero_im] at hdi; linarith
  obtain ⟨δ,hδ,hj⟩:=kz279 hc hp hinj hd hdn
  refine ⟨δ,hδ,?_⟩
  intro r hr hrd
  obtain ⟨hn,_,hjump⟩:=hj r hr hrd
  have hzero:kz24 (kz274 hc 0) (γ 0-r • (Complex.I*d)) = 0 :=
    kz280 _ (kz275 hc hp 0) (by
      intro t
      change (γ 0-r • (Complex.I*d)).re < (γ ((t:ℝ)+0)).re
      simp only [Complex.sub_re,Complex.smul_re,Complex.mul_re,Complex.I_re,zero_mul,
        Complex.I_im,one_mul,zero_sub,smul_eq_mul]
      nlinarith [hmin ((t:ℝ)+0)])
  rw [hzero,sub_zero] at hjump
  exact ⟨hn,hjump⟩
lemma kz282 {γ:ℝ → ℂ} {v:ℂ → ℂ} :
    IsMIntegralCurve (I:=𝓘(ℝ,ℂ)) γ v ↔ ∀ t,HasDerivAt γ (v (γ t)) t:=by
  constructor
  · intro h t
    have ht:HasFDerivAt γ ((1:ℝ →L[ℝ] ℝ).smulRight (v (γ t))) t :=
      hasMFDerivAt_iff_hasFDerivAt.mp (h t)
    simpa only [ContinuousLinearMap.smulRight_apply,one_apply_eq_self,one_smul] using ht.hasDerivAt
  · intro h t
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    convert (h t).hasFDerivAt using 1
    rfl
lemma kz283 {v:ℂ → ℂ} (hv:ContDiff ℝ 1 v)
    (hc:HasCompactSupport v) (x:ℂ) :
    ∃ γ:ℝ → ℂ,γ 0 = x ∧ ∀ t,HasDerivAt γ (v (γ t)) t:=by
  obtain ⟨K,hK⟩:=ContDiff.lipschitzWith_of_hasCompactSupport hc hv (by simp)
  obtain ⟨B,hB⟩:=hc.exists_bound_of_continuous hv.continuous
  let L:ℝ≥0:=⟨max B 0,le_max_right _ _⟩
  have hL:∀ z,‖v z‖ ≤ (L:ℝ):=fun z => (hB z).trans (le_max_left _ _)
  have hm:ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩:TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have he:∀ z:ℂ,∃ γ:ℝ → ℂ,γ 0 = z ∧
      IsMIntegralCurveOn (I:=𝓘(ℝ,ℂ)) γ v (Ioo (-1) 1):=by
    intro z
    have hi:IsPicardLindelof (fun _:ℝ => v)
        (⟨0,by norm_num⟩:Icc (-1:ℝ) 1) z L 0 L K:=by
      refine ⟨fun _ _ => hK.lipschitzOnWith,fun _ _ => continuousOn_const,
        fun _ _ w _ => hL w,?_⟩
      simp
    obtain ⟨γ,hγ0,hγ⟩:=hi.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨γ,hγ0,fun t ht => ?_⟩
    exact ((hγ t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨γ,hγ0,hγ⟩:=exists_isMIntegralCurve_of_isMIntegralCurveOn hm (by norm_num:(0:ℝ)<1) he x
  exact ⟨γ,hγ0,kz282.mp hγ⟩
def kz284 (p:ℂ →L[ℝ] ℝ):ℂ →L[ℝ] ℝ :=
  (-p Complex.I) • Complex.reCLM + (p 1) • Complex.imCLM
def kz285 (p:ℂ →L[ℝ] ℝ):ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp p + Complex.I • (Complex.ofRealCLM.comp (kz284 p))
lemma kz286 (p:ℂ →L[ℝ] ℝ) (w:ℂ) :
    p w = w.re * p 1 + w.im * p Complex.I:=by
  have hw:w = w.re • (1:ℂ) + w.im • Complex.I:=by
    simp [Complex.real_smul,Complex.re_add_im]
  conv_lhs => rw [hw,map_add,map_smul,map_smul]
  simp only [smul_eq_mul]
lemma kz287 (p:ℂ →L[ℝ] ℝ) :
    LinearMap.det (kz285 p).toLinearMap = (p 1)^2 + (p Complex.I)^2:=by
  rw [kz12]
  simp [kz285,kz284,Complex.mul_re,Complex.mul_im]
  ring
lemma kz288 {p:ℂ →L[ℝ] ℝ} (hp:p ≠ 0) :
    0 < LinearMap.det (kz285 p).toLinearMap:=by
  rw [kz287]
  have hn:p 1 ≠ 0 ∨ p Complex.I ≠ 0:=by
    by_contra h
    push Not at h
    apply hp
    ext w
    rw [kz286,h.1,h.2]
    simp
  rcases hn with hn|hn
  · nlinarith [sq_pos_of_ne_zero hn,sq_nonneg (p Complex.I)]
  · nlinarith [sq_pos_of_ne_zero hn,sq_nonneg (p 1)]
lemma kz289 {f:ℂ → ℝ} {z:ℂ}
    (hf:ContDiffAt ℝ 1 f z) (hp:fderiv ℝ f z ≠ 0) :
    ∃ e:OpenPartialHomeomorph ℂ ℂ,z ∈ e.source ∧
      (∀ w,(e w).re = f w) ∧
      (∀ w,(e w).im = kz284 (fderiv ℝ f z) w):=by
  let p:=fderiv ℝ f z
  let Φ:ℂ → ℂ:=fun w => (f w:ℂ) + Complex.I * (kz284 p w:ℂ)
  have hc:ContDiffAt ℝ 1 Φ z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z hf).add
      (contDiffAt_const.mul ((Complex.ofRealCLM.comp (kz284 p)).contDiff.contDiffAt))
  have hd:HasFDerivAt Φ (kz285 p) z:=by
    exact (Complex.ofRealCLM.hasFDerivAt.comp z (hf.differentiableAt (by simp)).hasFDerivAt).add
      (((Complex.ofRealCLM.comp (kz284 p)).hasFDerivAt).const_mul Complex.I)
  let A:ℂ ≃L[ℝ] ℂ:=(LinearMap.equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (ne_of_gt (kz288 hp)))).toContinuousLinearEquiv
  have hA:(A:ℂ →L[ℝ] ℂ) = kz285 p:=by
    ext w
    exact LinearMap.equivOfIsUnitDet_apply _ w
  rw [← hA] at hd
  refine ⟨hc.toOpenPartialHomeomorph Φ hd (by simp),
    hc.mem_toOpenPartialHomeomorph_source hd (by simp),?_,?_⟩
  · intro w
    change (Φ w).re = f w
    simp [Φ]
  · intro w
    change (Φ w).im = kz284 p w
    simp [Φ]
lemma kz290 {f:ℂ → ℝ} {γ:ℝ → ℂ} {t:ℝ} {v:ℂ}
    (hf:ContDiffAt ℝ 1 f (γ t)) (hp:fderiv ℝ f (γ t) ≠ 0)
    (hγ:ContDiffAt ℝ 1 γ t) (hd:HasDerivAt γ v t) (hv:v ≠ 0)
    (hc:∀ s,f (γ s) = f (γ t)) {U:Set ℝ} (hU:U ∈ 𝓝 t) :
    ∀ᶠ w in 𝓝 (γ t),f w = f (γ t) → w ∈ γ '' U:=by
  let p:=fderiv ℝ f (γ t)
  let q:=kz284 p
  have hfd:=(hf.differentiableAt (by simp)).hasFDerivAt
  have hpv:p v = 0:=by
    have hh:=hfd.comp_hasDerivAt t hd
    have he:(f ∘ γ) = fun _ => f (γ t):=funext hc
    rw [he] at hh
    exact hh.unique (hasDerivAt_const t _)
  have hqv:q v ≠ 0:=by
    intro hq
    have hA:IsUnit (LinearMap.det (kz285 p).toLinearMap) :=
      isUnit_iff_ne_zero.mpr (ne_of_gt (kz288 hp))
    let A:=LinearMap.equivOfIsUnitDet hA
    have hz:A v = A 0:=by
      rw [show A v = kz285 p v from LinearMap.equivOfIsUnitDet_apply _ v,
        show A 0 = kz285 p 0 from LinearMap.equivOfIsUnitDet_apply _ 0]
      simp [kz285,hpv,show kz284 p v = 0 from hq]
    exact hv (A.injective hz)
  let ψ:ℝ → ℝ:=fun s => q (γ s)
  have hψ:HasStrictDerivAt ψ (q v) t :=
    (q.contDiff.contDiffAt.comp t hγ).hasStrictDerivAt'
      (q.hasFDerivAt.comp_hasDerivAt t hd) (by simp)
  let σ:=hψ.localInverse ψ (q v) t hqv
  have hσ:σ (ψ t) = t:=hψ.eventually_left_inverse hqv |>.self_of_nhds
  have hσc:Tendsto σ (𝓝 (ψ t)) (𝓝 t):=by
    have ht:Tendsto σ (𝓝 (ψ t)) (𝓝 (σ (ψ t))) :=
      (hψ.to_localInverse hqv).hasDerivAt.continuousAt.tendsto
    rwa [hσ] at ht
  obtain ⟨e,het,her,hei⟩:=kz289 hf hp
  have hw:∀ᶠ w in 𝓝 (γ t),w ∈ e.source:=e.open_source.mem_nhds het
  have hqc:Tendsto q (𝓝 (γ t)) (𝓝 (ψ t)):=q.continuous.continuousAt.tendsto
  have hi:∀ᶠ w in 𝓝 (γ t),ψ (σ (q w)) = q w :=
    hqc.eventually (hψ.eventually_right_inverse hqv)
  have hu:∀ᶠ w in 𝓝 (γ t),σ (q w) ∈ U:=(hσc.comp hqc).eventually hU
  have hs:∀ᶠ w in 𝓝 (γ t),γ (σ (q w)) ∈ e.source :=
    (hγ.continuousAt.tendsto.comp (hσc.comp hqc)).eventually hw
  filter_upwards [hw,hi,hu,hs] with w hw hi hu hs hfwe
  refine ⟨σ (q w),hu,e.injOn hs hw ?_⟩
  apply Complex.ext
  · rw [her,her,hc,hfwe]
  · rw [hei,hei]
    exact hi
lemma kz291 {v:ℂ → ℂ} {γ:ℝ → ℂ}
    (hv:Continuous v) (hγ:∀ t,HasDerivAt γ (v (γ t)) t) :
    ContDiff ℝ 1 γ:=by
  apply contDiff_one_iff_deriv.mpr
  have hc:Continuous γ:=continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  refine ⟨fun t => (hγ t).differentiableAt,?_⟩
  have he:deriv γ = v ∘ γ:=funext fun t => (hγ t).deriv
  rw [he]
  exact hv.comp hc
lemma kz292 {f:ℂ → ℝ} {v:ℂ → ℂ} {γ:ℝ → ℂ}
    (hf:Differentiable ℝ f) (horth:∀ z,fderiv ℝ f z (v z) = 0)
    (hγ:∀ t,HasDerivAt γ (v (γ t)) t) (s t:ℝ):f (γ s) = f (γ t):=by
  have hd (t:ℝ):HasDerivAt (fun t => f (γ t)) 0 t:=by
    convert (hf (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t) using 1 <;>
      first | rfl | simp only [horth]
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t
lemma kz293 {v:ℂ → ℂ} {γ κ:ℝ → ℂ}
    (hv:ContDiff ℝ 1 v)
    (hγ:∀ t,HasDerivAt γ (v (γ t)) t)
    (hκ:∀ t,HasDerivAt κ (v (κ t)) t)
    {a b:ℝ} (he:γ a = κ b) (s:ℝ):γ (s+a) = κ (s+b):=by
  have hm:ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩:TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hh:=isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀:=0) hm
    ((kz282.mpr hγ).comp_add a)
    ((kz282.mpr hκ).comp_add b) (by simpa using he)
  exact congrFun hh s
lemma kz294 {f:ℂ → ℝ} {γ:ℝ → ℂ} {c:ℝ}
    (hf:ContDiff ℝ 1 f) (hp:∀ z,f z = c → fderiv ℝ f z ≠ 0)
    (hγ:ContDiff ℝ 1 γ) (hn:∀ t,deriv γ t ≠ 0)
    (hc:∀ t,f (γ t) = c) :
    IsOpenMap (fun t => (⟨γ t,hc t⟩:{z:ℂ | f z = c})):=by
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨t,ht,rfl⟩
  have hh:=kz290 hf.contDiffAt (hp _ (hc t)) hγ.contDiffAt
    (hγ.differentiable (by simp) t).hasDerivAt (hn t)
    (fun s => (hc s).trans (hc t).symm) (hU.mem_nhds ht)
  have hm:Tendsto (Subtype.val:{z:ℂ | f z = c} → ℂ)
      (𝓝 ⟨γ t,hc t⟩) (𝓝 (γ t)):=continuous_subtype_val.continuousAt.tendsto
  have he:=hm.eventually hh
  filter_upwards [he] with w hw
  obtain ⟨s,hs,heq⟩:=hw (w.property.trans (hc t).symm)
  exact ⟨s,hs,Subtype.ext heq⟩
lemma kz295 {f:ℂ → ℝ} {v:ℂ → ℂ} {c:ℝ}
    (hf:ContDiff ℝ 1 f) (hv:ContDiff ℝ 1 v) (hvc:HasCompactSupport v)
    (horth:∀ z,fderiv ℝ f z (v z) = 0)
    (hp:∀ z,f z = c → fderiv ℝ f z ≠ 0)
    (hn:∀ z,f z = c → v z ≠ 0)
    (hK:IsCompact {z:ℂ | f z = c}) {γ:ℝ → ℂ}
    (hγ:∀ t,HasDerivAt γ (v (γ t)) t) (hγ0:f (γ 0) = c) :
    ∃ T > 0,Periodic γ T:=by
  let K:={z:ℂ | f z = c}
  have hc (t:ℝ):f (γ t) = c :=
    (kz292 (hf.differentiable (by simp)) horth hγ t 0).trans hγ0
  let Γ:ℝ → K:=fun t => ⟨γ t,hc t⟩
  have hγc:=kz291 hv.continuous hγ
  have hΓo:IsOpenMap Γ:=kz294 hf hp hγc
    (fun t => by rw [(hγ t).deriv]; exact hn _ (hc t)) hc
  have hΓc:Continuous Γ:=hγc.continuous.subtype_mk _
  have hclosed:IsClosed (range Γ):=by
    apply isOpen_compl_iff.mp
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    obtain ⟨κ,hκ0,hκ⟩:=kz283 hv hvc w.val
    have hκc (s:ℝ):f (κ s) = c:=by
      rw [kz292 (hf.differentiable (by simp)) horth hκ s 0,hκ0]
      exact w.property
    let Δ:ℝ → K:=fun s => ⟨κ s,hκc s⟩
    have hΔo:IsOpenMap Δ:=kz294 hf hp
      (kz291 hv.continuous hκ)
      (fun s => by rw [(hκ s).deriv]; exact hn _ (hκc s)) hκc
    have hwΔ:w ∈ range Δ:=⟨0,Subtype.ext hκ0⟩
    apply mem_of_superset (hΔo.isOpen_range.mem_nhds hwΔ)
    rintro y ⟨s,rfl⟩ ⟨t,ht⟩
    apply hw
    have he:γ t = κ s:=congrArg Subtype.val ht
    refine ⟨-s+t,Subtype.ext ?_⟩
    have hh:=kz293 hv hγ hκ he (-s)
    simpa only [neg_add_cancel,hκ0] using hh
  have hcompact:IsCompact (range Γ):=by
    have:CompactSpace K:=isCompact_iff_compactSpace.mp hK
    exact hclosed.isCompact
  have hnotinj:¬ Injective γ:=by
    intro hi
    have hΓi:Injective Γ:=fun a b h => hi (congrArg Subtype.val h)
    have he:=Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hΓc hΓi hΓo
    apply noncompact_univ ℝ
    apply he.isEmbedding.isCompact_iff.mpr
    simpa only [image_univ] using hcompact
  have hm:ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩:TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  exact (xor_iff_iff_not.mp
    ((kz282.mpr hγ).periodic_xor_injective hm)).mpr hnotinj
lemma kz296 {γ:ℝ → ℂ} {t:ℝ}
    (hγ:ContDiffAt ℝ 1 γ t) (hn:deriv γ t ≠ 0) :
    ∃ ε > 0,InjOn γ (Metric.ball t ε):=by
  obtain ⟨p,hp⟩:∃ p:ℂ →L[ℝ] ℝ,p (deriv γ t) ≠ 0:=by
    by_cases hr:(deriv γ t).re = 0
    · refine ⟨Complex.imCLM,fun hi => hn (Complex.ext hr hi)⟩
    · exact ⟨Complex.reCLM,hr⟩
  have hd:HasStrictDerivAt (fun s => p (γ s)) (p (deriv γ t)) t :=
    (p.contDiff.contDiffAt.comp t hγ).hasStrictDerivAt'
      (p.hasFDerivAt.comp_hasDerivAt t
        (hγ.differentiableAt (by simp)).hasDerivAt) (by simp)
  obtain ⟨ε,hε,hsub⟩:=Metric.mem_nhds_iff.mp (hd.eventually_left_inverse hp)
  refine ⟨ε,hε,fun a ha b hb he => ?_⟩
  have h₁:=hsub ha
  have h₂:=hsub hb
  change HasStrictDerivAt.localInverse (fun s => p (γ s)) (p (deriv γ t)) t hd hp (p (γ a)) = a at h₁
  change HasStrictDerivAt.localInverse (fun s => p (γ s)) (p (deriv γ t)) t hd hp (p (γ b)) = b at h₂
  rw [he] at h₁
  exact h₁.symm.trans h₂
lemma kz297 {v:ℂ → ℂ} {γ:ℝ → ℂ}
    (hv:ContDiff ℝ 1 v) (hγ:∀ t,HasDerivAt γ (v (γ t)) t)
    (hn:v (γ 0) ≠ 0) (hper:∃ T > 0,Periodic γ T) :
    ∃ T > 0,Periodic γ T ∧ InjOn γ (Ico 0 T):=by
  have hγc:=kz291 hv.continuous hγ
  obtain ⟨ε,hε,hεinj⟩:=kz296 (t:=0) hγc.contDiffAt
    (by rw [(hγ 0).deriv]; exact hn)
  have hlow:∀ t,0 < t → γ t = γ 0 → ε ≤ t:=by
    intro t ht he
    by_contra hh
    have hlt:t < ε:=lt_of_not_ge hh
    have hmem:t ∈ Metric.ball (0:ℝ) ε:=by
      simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos ht] using hlt
    have hz:=hεinj hmem (Metric.mem_ball_self hε) he
    linarith
  obtain ⟨T,hT,hpT⟩:=hper
  have hTr:γ T = γ 0:=by simpa using hpT 0
  let S:=Icc ε T ∩ {t | γ t = γ 0}
  have hS:IsCompact S:=isCompact_Icc.inter_right
    (isClosed_eq hγc.continuous continuous_const)
  obtain ⟨P,hP,hmin⟩:=hS.exists_isMinOn ⟨T,⟨⟨hlow T hT hTr,le_rfl⟩,hTr⟩⟩
    continuousOn_id
  have hPpos:0 < P:=hε.trans_le hP.1.1
  have hleast:∀ t,0 < t → γ t = γ 0 → P ≤ t:=by
    intro t ht he
    by_cases hle:t ≤ T
    · exact hmin ⟨⟨hlow t ht he,hle⟩,he⟩
    · exact hP.1.2.trans (le_of_not_ge hle)
  have hm:ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ)).tangent 1
      (fun z => (⟨z,v z⟩:TangentBundle 𝓘(ℝ,ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hi:=kz282.mpr hγ
  have hPP:Periodic γ P:=by simpa using hi.periodic_of_eq hm hP.2
  refine ⟨P,hPpos,hPP,fun a ha b hb he => ?_⟩
  rcases lt_trichotomy a b with hab|hab|hab
  · have hper:=hi.periodic_of_eq hm he.symm
    have hret:γ (b-a) = γ 0:=by simpa using hper 0
    have hh:=hleast (b-a) (sub_pos.mpr hab) hret
    linarith [ha.1,hb.2]
  · exact hab
  · have hper:=hi.periodic_of_eq hm he
    have hret:γ (a-b) = γ 0:=by simpa using hper 0
    have hh:=hleast (a-b) (sub_pos.mpr hab) hret
    linarith [hb.1,ha.2]
lemma kz298 {v:ℂ → ℂ} {γ κ:ℝ → ℂ}
    (hv:ContDiff ℝ 1 v)
    (hγ:∀ t,HasDerivAt γ (v (γ t)) t)
    (hκ:∀ t,HasDerivAt κ (v (κ t)) t)
    {a b:ℝ} (he:γ a = κ b):range γ = range κ:=by
  apply Subset.antisymm
  · rintro _ ⟨s,rfl⟩
    refine ⟨s-a+b,?_⟩
    have hh:=kz293 hv hγ hκ he (s-a)
    simpa only [sub_add_cancel] using hh.symm
  · rintro _ ⟨s,rfl⟩
    refine ⟨s-b+a,?_⟩
    have hh:=kz293 hv hκ hγ he.symm (s-b)
    simpa only [sub_add_cancel] using hh.symm
lemma kz299 {f:ℂ → ℝ} {v:ℂ → ℂ} {c:ℝ}
    (hf:ContDiff ℝ 1 f) (hv:ContDiff ℝ 1 v) (hvc:HasCompactSupport v)
    (horth:∀ z,fderiv ℝ f z (v z) = 0)
    (hp:∀ z,f z = c → fderiv ℝ f z ≠ 0)
    (hn:∀ z,f z = c → v z ≠ 0)
    (hK:IsCompact {z:ℂ | f z = c}) :
    ∃ C:Finset (Set ℂ),(⋃ S ∈ C,S) = {z:ℂ | f z = c} ∧
      (∀ S ∈ C,∀ T ∈ C,S ≠ T → Disjoint S T) ∧
      ∀ S ∈ C,∃ γ:ℝ → ℂ,∃ P > 0,
        range γ = S ∧ (∀ t,HasDerivAt γ (v (γ t)) t) ∧
        Periodic γ P ∧ InjOn γ (Ico 0 P):=by
  classical
  let K:={z:ℂ | f z = c}
  have hE:∀ z:K,∃ γ:ℝ → ℂ,γ 0 = z.val ∧
      ∀ t,HasDerivAt γ (v (γ t)) t:=fun z => kz283 hv hvc z.val
  choose γ hγ0 hγ using hE
  have hc (z:K) (t:ℝ):f (γ z t) = c:=by
    rw [kz292 (hf.differentiable (by simp)) horth (hγ z) t 0,
      hγ0 z]
    exact z.property
  let Γ (z:K):ℝ → K:=fun t => ⟨γ z t,hc z t⟩
  have hΓo (z:K):IsOpenMap (Γ z):=kz294 hf hp
    (kz291 hv.continuous (hγ z))
    (fun t => by rw [(hγ z t).deriv]; exact hn _ (hc z t)) (hc z)
  have:CompactSpace K:=isCompact_iff_compactSpace.mp hK
  obtain ⟨s,hs⟩:=isCompact_univ.elim_finite_subcover (fun z:K => range (Γ z))
    (fun z => (hΓo z).isOpen_range) (by
      intro z _
      exact mem_iUnion.mpr ⟨z,0,Subtype.ext (hγ0 z)⟩)
  let C:=s.image (fun z => range (γ z))
  refine ⟨C,?_,?_,?_⟩
  · ext w
    constructor
    · intro hw
      obtain ⟨S,hS,hw⟩:=mem_iUnion₂.mp hw
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hS
      obtain ⟨t,rfl⟩:=hw
      exact hc z t
    · intro hw
      obtain ⟨z,hz,t,ht⟩:=mem_iUnion₂.mp (hs (mem_univ (⟨w,hw⟩:K)))
      refine mem_iUnion₂.mpr ⟨range (γ z),Finset.mem_image.mpr ⟨z,hz,rfl⟩,t,?_⟩
      exact congrArg Subtype.val ht
  · intro S hS T hT hne
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hS
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hT
    apply disjoint_left.mpr
    rintro a ⟨s,hs⟩ ⟨t,ht⟩
    exact hne (kz298 hv (hγ z) (hγ w) (hs.trans ht.symm))
  · intro S hS
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hS
    obtain ⟨P,hP,hper,hinj⟩:=kz297 hv (hγ z)
      (hn _ (hc z 0))
      (kz295 hf hv hvc horth hp hn hK (hγ z) (hc z 0))
    exact ⟨γ z,P,hP,rfl,hγ z,hper,hinj⟩
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def kz300:Set (ℝ × ℝ):={p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}
lemma kz301:Convex ℝ kz300:=by
  intro p hp q hq a b ha hb hab
  change 0 ≤ a*p.1+b*q.1 ∧ a*p.1+b*q.1 ≤ a*p.2+b*q.2 ∧ a*p.2+b*q.2 ≤ 1
  rcases hp with ⟨hp0,hpst,hp1⟩
  rcases hq with ⟨hq0,hqst,hq1⟩
  refine ⟨add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0),
    add_le_add (mul_le_mul_of_nonneg_left hpst ha)
      (mul_le_mul_of_nonneg_left hqst hb),?_⟩
  calc
    _ ≤ a*1+b*1:=add_le_add (mul_le_mul_of_nonneg_left hp1 ha)
      (mul_le_mul_of_nonneg_left hq1 hb)
    _ = 1:=by simpa using hab
lemma kz302:kz300.Nonempty:=⟨(0,0),by simp [kz300]⟩
def kz303 (γ:ℝ → ℂ) (s t:ℝ):ℂ :=
  ∫ u in (0:ℝ)..1,deriv γ (s+u*(t-s))
lemma kz304 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ) :
    Continuous (fun p:ℝ × ℝ => kz303 γ p.1 p.2):=by
  have hd:Continuous (deriv γ):=hγ.continuous_deriv (by norm_num)
  have hi:Continuous (fun p:ℝ × ℝ => ∫ u in Icc (0:ℝ) 1,deriv γ (p.1+u*(p.2-p.1))) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  simpa [kz303,intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using hi
lemma kz305 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ) (s t:ℝ) :
    (t-s) • kz303 γ s t = γ t-γ s:=by
  have hd:Continuous (deriv γ):=hγ.continuous_deriv (by norm_num)
  have hD (u:ℝ):HasDerivAt (fun v:ℝ => γ (s+v*(t-s)))
      ((t-s) • deriv γ (s+u*(t-s))) u:=by
    simpa only [Function.comp_def,Pi.add_apply,id_eq,zero_add,one_mul] using ((hγ.differentiable (by norm_num) (s+u*(t-s))).hasDerivAt.scomp u
      ((hasDerivAt_const u s).add ((hasDerivAt_id u).mul_const (t-s))))
  have hFTC:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hD u)
    (((hd.comp (show Continuous (fun u:ℝ => s+u*(t-s)) by fun_prop)).const_smul (t-s)).intervalIntegrable 0 1)
  simpa [kz303,intervalIntegral.integral_smul,sub_eq_add_neg] using hFTC
@[simp] lemma kz306 (γ:ℝ → ℂ) (s:ℝ) :
    kz303 γ s s = deriv γ s:=by simp [kz303]
def kz307 (γ:ℝ → ℂ) (p:ℝ × ℝ):ℂ :=
  (1-(p.2-p.1)) • kz303 γ p.1 p.2 -
    (p.2-p.1) • kz303 γ p.1 (p.2-1)
lemma kz308 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ) :
    Continuous (kz307 γ):=by
  have hc:=kz304 hγ
  exact ((continuous_const.sub (continuous_snd.sub continuous_fst)).smul hc).sub
    ((continuous_snd.sub continuous_fst).smul (hc.comp (show Continuous (fun p:ℝ × ℝ => (p.1,p.2-1)) by fun_prop)))
@[simp] lemma kz309 (γ:ℝ → ℂ) (s:ℝ) :
    kz307 γ (s,s) = deriv γ s:=by simp [kz307]
@[simp] lemma kz310 (γ:ℝ → ℂ) :
    kz307 γ (0,1) = -deriv γ 0:=by simp [kz307]
lemma kz311 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ)
    (hp:Function.Periodic γ 1) (s t:ℝ) :
    ((t-s)*(1-(t-s))) • kz307 γ (s,t) =
      ((1-(t-s))^2+(t-s)^2) • (γ t-γ s):=by
  have h₁:=kz305 hγ s t
  have h₂:=kz305 hγ s (t-1)
  rw [hp.sub_eq] at h₂
  change ((t-s)*(1-(t-s))) • ((1-(t-s)) • kz303 γ s t -
    (t-s) • kz303 γ s (t-1)) = _
  calc
    _ = (1-(t-s))^2 • ((t-s) • kz303 γ s t) +
      (t-s)^2 • ((t-1-s) • kz303 γ s (t-1)):=by
        simp only [smul_sub,smul_smul]
        module
    _ = _:=by rw [h₁,h₂,← add_smul]
lemma kz312 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ)
    (hp:Function.Periodic γ 1) (hinj:InjOn γ (Ico 0 1))
    (hd:∀ t ∈ Icc (0:ℝ) 1,deriv γ t ≠ 0) {p:ℝ × ℝ}
    (hpt:p ∈ kz300):kz307 γ p ≠ 0:=by
  rcases p with ⟨s,t⟩
  rcases hpt with ⟨hs,hst,ht⟩
  by_cases heq:s = t
  · subst t
    simpa using hd s ⟨hs,ht⟩
  by_cases hc:s = 0 ∧ t = 1
  · rcases hc with ⟨rfl,rfl⟩
    simpa using hd 0 (by simp)
  have hst':s < t:=lt_of_le_of_ne hst heq
  have hneq:γ t ≠ γ s:=by
    by_cases ht1:t = 1
    · subst t
      rw [hp.eq]
      have hs0:s ≠ 0:=fun h => hc ⟨h,rfl⟩
      exact fun h => hs0 ((hinj ⟨by norm_num,by norm_num⟩ ⟨hs,hst'⟩ h).symm)
    · exact fun h => (ne_of_gt hst') (hinj ⟨hs.trans hst,lt_of_le_of_ne ht ht1⟩
        ⟨hs,hst'.trans_le ht⟩ h)
  have hpos:0 < (1-(t-s))^2+(t-s)^2:=by nlinarith [sq_nonneg (1-(t-s))]
  intro he
  have hscale:=kz311 hγ hp s t
  rw [he,smul_zero] at hscale
  exact hneq (sub_eq_zero.mp ((smul_eq_zero.mp hscale.symm).resolve_left hpos.ne'))
lemma kz313 {γ:ℝ → ℂ} (hp:Function.Periodic γ 1) :
    Function.Periodic (deriv γ) 1:=by
  intro t
  rw [← deriv_comp_add_const γ 1 t]
  congr 1
  exact funext hp
lemma kz314 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ)
    (hp:Function.Periodic γ 1) {t:ℝ} (ht:t ∈ Icc (0:ℝ) 1) :
    kz307 γ (t,1) = -kz307 γ (0,t):=by
  by_cases h0:t = 0
  · subst t
    simp
  by_cases h1:t = 1
  · subst t
    simpa using (kz313 hp).eq
  have hd:t*(1-t) ≠ 0:=mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
  apply (smul_right_injective ℂ hd)
  have ha:=kz311 hγ hp 0 t
  have hb:=kz311 hγ hp t 1
  simp only [sub_zero] at ha
  rw [hp.eq] at hb
  have he:(1-t)*(1-(1-t)) = t*(1-t):=by ring
  have he':(1-(1-t))^2+(1-t)^2 = (1-t)^2+t^2:=by ring
  rw [he,he'] at hb
  change (t*(1-t)) • kz307 γ (t,1) = (t*(1-t)) • (-kz307 γ (0,t))
  rw [smul_neg,ha,hb,← smul_neg]
  congr 1
  module
lemma kz315 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ)
    (hp:Function.Periodic γ 1) (hm:∀ t ∈ Icc (0:ℝ) 1,(γ 0).re ≤ (γ t).re)
    (hd:(deriv γ 0).re = 0) {t:ℝ} (ht:t ∈ Icc (0:ℝ) 1) :
    0 ≤ (kz307 γ (0,t)).re:=by
  by_cases h0:t = 0
  · subst t
    simp [hd]
  by_cases h1:t = 1
  · subst t
    simp [hd]
  have hpos:0 < t*(1-t):=mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h0))
    (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))
  have hs:=congrArg Complex.re (kz311 hγ hp 0 t)
  simp only [sub_zero,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.sub_re] at hs
  have hnonneg:0 ≤ ((1-t)^2+t^2)*((γ t).re-(γ 0).re) :=
    mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sub_nonneg.mpr (hm t ht))
  nlinarith
def kz316:kz300:=⟨(0,0),by simp [kz300]⟩
def kz317:kz300:=⟨(0,1),by simp [kz300]⟩
def kz318:kz300:=⟨(1,1),by simp [kz300]⟩
lemma kz319 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ)
    (hp:Function.Periodic γ 1) (hinj:InjOn γ (Ico 0 1))
    (hd:∀ t ∈ Icc (0:ℝ) 1,deriv γ t ≠ 0) :
    ∃ A:C(kz300,ℂ),A kz316 = Complex.log (deriv γ 0) ∧
      ∀ p,Complex.exp (A p) = kz307 γ p:=by
  let:=kz301.contractibleSpace kz302
  let:=kz301.locallyPathConnectedSpace
  let S:C(kz300,ℂ) :=
    ⟨fun p => kz307 γ p,(kz308 hγ).comp continuous_subtype_val⟩
  have he:Complex.exp (Complex.log (deriv γ 0)) = S kz316:=by
    simpa [S,kz316] using Complex.exp_log (hd 0 (by simp))
  obtain ⟨A,⟨hA0,hA⟩,-⟩:=Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts S he
    (fun p => kz312 hγ hp hinj hd p.property)
  exact ⟨A,hA0,fun p => congrFun hA p⟩
lemma continuous_log_unique.{u_1} {X:Type u_1} [TopologicalSpace X] [PreconnectedSpace X]
    {A B:X → ℂ} (hA:Continuous A) (hB:Continuous B)
    (h:∀ x,Complex.exp (A x) = Complex.exp (B x)) {x:X} (hx:A x = B x):A = B:=by
  exact Complex.isCoveringMap_exp.eq_of_comp_eq hA hB
    (by funext y; exact Subtype.ext (h y)) x hx
def kz320 (t:unitInterval):kz300 :=
  ⟨(0,t),by exact ⟨le_rfl,t.property.1,t.property.2⟩⟩
def kz321 (t:unitInterval):kz300 :=
  ⟨(t,1),by exact ⟨t.property.1,t.property.2,le_rfl⟩⟩
def kz322 (t:unitInterval):kz300 :=
  ⟨(t,t),by exact ⟨t.property.1,le_rfl,t.property.2⟩⟩
lemma kz323:Continuous kz320:=by
  unfold kz320
  fun_prop
lemma kz324:Continuous kz321:=by
  unfold kz321
  fun_prop
lemma kz325:Continuous kz322:=by
  unfold kz322
  fun_prop
lemma kz326 {z:ℂ} (hz:z ≠ 0) (hr:0 ≤ z.re) :
    z ∈ Complex.slitPlane:=by
  by_cases hi:z.im = 0
  · left
    exact lt_of_le_of_ne hr (fun he => hz (Complex.ext he.symm hi))
  · exact Or.inr hi
lemma kz327 {z:ℂ} (hr:z.re = 0) (hi:z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi:ℂ)*Complex.I:=by
  apply Complex.ext
  · simp [Complex.log_re,norm_neg]
  · have ha:=Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hr,hi⟩
    have hb:Complex.arg (-z) = Real.pi/2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨by simpa using hr,by simpa using hi⟩
    simp only [Complex.log_im,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,mul_one,Complex.ofReal_im,Complex.I_re,mul_zero,add_zero,ha,hb]
    ring
lemma kz328 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ)
    (hp:Function.Periodic γ 1) (hinj:InjOn γ (Ico 0 1))
    (hd:∀ t ∈ Icc (0:ℝ) 1,deriv γ t ≠ 0)
    (hm:∀ t ∈ Icc (0:ℝ) 1,(γ 0).re ≤ (γ t).re)
    (hr:(deriv γ 0).re = 0) (hi:(deriv γ 0).im < 0) :
    ∃ T:C(unitInterval,ℂ),(∀ t,Complex.exp (T t) = deriv γ t) ∧
      T 1 = T 0 + (2*Real.pi:ℝ)*Complex.I:=by
  obtain ⟨A,hA0,hA⟩:=kz319 hγ hp hinj hd
  have hleftc:Continuous (fun t:unitInterval =>
      Complex.log (kz307 γ (kz320 t))):=by
    rw [continuous_iff_continuousAt]
    intro t
    exact (continuousAt_clog (kz326
      (kz312 hγ hp hinj hd (kz320 t).property)
      (kz315 hγ hp hm hr t.property))).comp (f:=fun u:unitInterval => kz307 γ (kz320 u))
      ((kz308 hγ).comp
        (continuous_subtype_val.comp kz323)).continuousAt
  have hleft:(fun t:unitInterval => A (kz320 t)) =
      (fun t:unitInterval => Complex.log (kz307 γ (kz320 t))):=by
    apply continuous_log_unique (x:=(0:unitInterval)) (A.continuous.comp kz323) hleftc
    · intro t
      dsimp only [Function.comp_def]
      rw [hA,Complex.exp_log
        (kz312 hγ hp hinj hd (kz320 t).property)]
    · simpa [Function.comp_def,kz320,kz316] using hA0
  have hcorner:A kz317 = A kz316 + (Real.pi:ℂ)*Complex.I:=by
    have hcl:=congrFun hleft 1
    have hcl':A kz317 = Complex.log (-deriv γ 0):=by
      simpa [kz320,kz317] using hcl
    rw [hcl',hA0,kz327 hr hi]
  have htop:(fun t:unitInterval => A (kz321 t)) =
      (fun t:unitInterval => A (kz320 t) + (Real.pi:ℂ)*Complex.I):=by
    apply continuous_log_unique (x:=(0:unitInterval)) (A.continuous.comp kz324)
      ((A.continuous.comp kz323).add continuous_const)
    · intro t
      dsimp only [Function.comp_def,Pi.add_apply]
      rw [Complex.exp_add,hA,hA,Complex.exp_pi_mul_I,mul_neg_one]
      exact kz314 hγ hp t.property
    · exact hcorner
  refine ⟨⟨fun t => A (kz322 t),A.continuous.comp kz325⟩,
    fun t => ?_,?_⟩
  · exact (hA (kz322 t)).trans (kz309 γ t)
  · have hpt:=congrFun htop 1
    change A kz318 = A kz317 + (Real.pi:ℂ)*Complex.I at hpt
    change A kz318 = A kz316 + (↑(2*Real.pi):ℂ)*Complex.I
    rw [hpt,hcorner]
    push_cast
    ring
lemma kz329 {f:ℂ → ℝ} {z:ℂ}
    (hf:ContDiffAt ℝ 1 f z) (hp:fderiv ℝ f z ≠ 0)
    {W:Set ℂ} (hW:W ∈ 𝓝 z) :
    ∃ U:Set ℂ,IsOpen U ∧ z ∈ U ∧ U ⊆ W ∧
      IsPreconnected (U ∩ {w | f w < f z}) ∧
      (U ∩ {w | f w < f z}).Nonempty:=by
  obtain ⟨e,hz,her,_⟩:=kz289 hf hp
  have het:e z ∈ e.target:=e.map_source hz
  have hn:e.target ∩ e.symm ⁻¹' W ∈ 𝓝 (e z) :=
    inter_mem (e.open_target.mem_nhds het) (by
      have ht:=(e.continuousAt_symm het).preimage_mem_nhds
        (show W ∈ 𝓝 (e.symm (e z)) by rwa [e.left_inv hz])
      exact ht)
  obtain ⟨r,hr,hball⟩:=Metric.mem_nhds_iff.mp hn
  let B:=Metric.ball (e z) r
  let U:=e.source ∩ e ⁻¹' B
  have hBo:IsOpen B:=Metric.isOpen_ball
  have hBU:∀ b ∈ B,b ∈ e.target ∧ e.symm b ∈ U:=by
    intro b hb
    have hbt:=(hball hb).1
    exact ⟨hbt,e.map_target hbt,by simpa only [mem_preimage,e.right_inv hbt] using hb⟩
  have hUo:IsOpen U:=e.isOpen_inter_preimage hBo
  have hzU:z ∈ U:=⟨hz,by simpa [B] using hr⟩
  have hUW:U ⊆ W:=by
    intro w hw
    have h:=(hball hw.2).2
    simpa only [mem_preimage,e.left_inv hw.1] using h
  have he:U ∩ {w | f w < f z} = e.symm '' (B ∩ {b | b.re < f z}):=by
    ext w
    constructor
    · rintro ⟨hw,hfw⟩
      exact ⟨e w,⟨hw.2,by simpa only [mem_ofPred,her] using hfw⟩,e.left_inv hw.1⟩
    · rintro ⟨b,⟨hb,hbr⟩,rfl⟩
      refine ⟨(hBU b hb).2,?_⟩
      have hh:=her (e.symm b)
      rw [e.right_inv (hBU b hb).1] at hh
      change f (e.symm b) < f z
      rw [← hh]
      exact hbr
  have hconv:Convex ℝ (B ∩ {b:ℂ | b.re < f z}) :=
    (convex_ball (e z) r).inter ((convex_Iio (f z)).linear_preimage Complex.reCLM.toLinearMap)
  have hpc:IsPreconnected (U ∩ {w | f w < f z}):=by
    rw [he]
    exact hconv.isPreconnected.image e.symm (e.continuousOn_symm.mono (by
      intro b hb; exact (hBU b hb.1).1))
  refine ⟨U,hUo,hzU,hUW,hpc,?_⟩
  rw [he]
  apply Nonempty.image
  refine ⟨e z - (r/2:ℝ),?_,?_⟩
  · change dist (e z-(r/2:ℝ)) (e z) < r
    rw [dist_eq_norm,sub_sub_cancel_left,norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by linarith:(0:ℝ) < r/2)]
    linarith
  · change (e z - (r/2:ℝ)).re < f z
    rw [Complex.sub_re,Complex.ofReal_re,her]
    linarith
lemma kz330 {f:ℂ → ℝ} {z:ℂ}
    (hf:ContDiffAt ℝ 1 f z) (hp:fderiv ℝ f z ≠ 0) :
    ∃ᶠ w in 𝓝 z,f w < f z:=by
  rw [frequently_iff]
  intro P hP
  obtain ⟨U,_,_,hUP,_,w,hwU,hwf⟩:=kz329 hf hp hP
  exact ⟨w,hUP hwU,hwf⟩
lemma kz331 {f:ℂ → ℝ} {j:ℂ → ℤ} {c:ℝ} {z:ℂ}
    (hf:ContDiffAt ℝ 1 f z) (hp:fderiv ℝ f z ≠ 0) (hz:f z = c)
    (hj:ContinuousOn j {w | f w ≠ c}) (hj0:∀ w,c < f w → j w = 0) :
    ∃ n:ℤ,∀ᶠ w in 𝓝 z,f w ≠ c → j w = if f w < c then n else 0:=by
  obtain ⟨U,hUo,hzU,_,hpc,w₀,hw₀,hfw₀⟩:=kz329 hf hp
    (show (univ:Set ℂ) ∈ 𝓝 z from univ_mem)
  refine ⟨j w₀,?_⟩
  filter_upwards [hUo.mem_nhds hzU] with w hw hne
  by_cases hlt:f w < c
  · rw [if_pos hlt]
    have hdisc:=(hpc.image j (hj.mono (by
      intro v hv
      have hh:f v < f z:=hv.2
      exact ne_of_lt (by simpa only [hz] using hh)))).subsingleton
    exact hdisc ⟨w,⟨hw,by change f w < f z; simpa only [hz] using hlt⟩,rfl⟩ ⟨w₀,⟨hw₀,hfw₀⟩,rfl⟩
  · rw [if_neg hlt]
    exact hj0 w (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
lemma kz332 {f:ℂ → ℝ} {j:ℂ → ℤ} {c:ℝ} {z:ℂ}
    (hf:ContDiffAt ℝ 1 f z) (hp:fderiv ℝ f z ≠ 0) (hz:f z = c)
    {m n:ℤ}
    (hm:∀ᶠ w in 𝓝 z,f w ≠ c → j w = if f w < c then m else 0)
    (hn:∀ᶠ w in 𝓝 z,f w ≠ c → j w = if f w < c then n else 0):m = n:=by
  obtain ⟨w,hw,hmw,hnw⟩:=((kz330 hf hp).and_eventually
    (hm.and hn)).exists
  have hlt:f w < c:=by simpa only [hz] using hw
  have hm':=hmw hlt.ne
  have hn':=hnw hlt.ne
  simpa only [if_pos hlt] using hm'.symm.trans hn'
lemma kz333 {f:ℂ → ℝ} {j:ℂ → ℤ}
    {c:ℝ} {γ:ℝ → ℂ} (hc:Continuous γ)
    (hf:∀ t,ContDiffAt ℝ 1 f (γ t)) (hp:∀ t,fderiv ℝ f (γ t) ≠ 0)
    (hz:∀ t,f (γ t) = c) (hj:ContinuousOn j {w | f w ≠ c})
    (hj0:∀ w,c < f w → j w = 0) :
    ∃ n:ℤ,∀ t,∀ᶠ w in 𝓝 (γ t),
      f w ≠ c → j w = if f w < c then n else 0:=by
  choose n hn using fun t => kz331 (hf t) (hp t) (hz t) hj hj0
  have hnc:Continuous n:=by
    apply continuous_iff_continuousAt.mpr
    intro t
    have he:∀ᶠ s in 𝓝 t,n s = n t:=by
      filter_upwards [(hc.tendsto t).eventually (hn t).eventually_nhds] with s hs
      exact (kz332 (hf s) (hp s) (hz s) hs (hn s)).symm
    exact continuousAt_const.congr (he.mono fun _ h => h.symm)
  refine ⟨n 0,fun t => ?_⟩
  have he:n t = n 0:=TotallyDisconnectedSpace.eq_of_continuous n hnc t 0
  simpa only [he] using hn t
lemma kz334 {f:ℂ → ℝ} {c:ℝ} {γ:ℝ → ℂ}
    (hc:Continuous γ) (hp:Function.Periodic γ 1)
    (hinj:InjOn γ (Ico (0:ℝ) 1)) {d:ℂ}
    (hd:HasDerivAt γ d 0) (hdi:d.im < 0)
    (hmin:∀ t,(γ 0).re ≤ (γ t).re)
    (hf:∀ t,ContDiffAt ℝ 1 f (γ t))
    (hreg:∀ t,fderiv ℝ f (γ t) ≠ 0) (hz:∀ t,f (γ t) = c)
    (hbelow:∀ w,w ∉ range γ → kz24 (kz274 hc 0) w ≠ 0 → f w < c) :
    ∀ t,∀ᶠ w in 𝓝 (γ t),f w ≠ c →
      kz24 (kz274 hc 0) w = if f w < c then 1 else 0:=by
  have hj:ContinuousOn (kz24 (kz274 hc 0)) {w | f w ≠ c} :=
    (kz26 _ (kz275 hc hp 0)).mono (by
      intro w hw
      rintro ⟨t,rfl⟩
      exact hw (hz ((t:ℝ)+0)))
  have hj0:∀ w,c < f w → kz24 (kz274 hc 0) w = 0:=by
    intro w hw
    by_contra hn
    have hwr:w ∉ range γ:=by rintro ⟨t,rfl⟩; linarith [hz t]
    exact (hbelow w hwr hn).not_gt hw
  obtain ⟨n,hn⟩:=kz333 hc hf hreg hz hj hj0
  obtain ⟨δ,hδ,hjump⟩:=kz281 hc hp hinj hd hdi hmin
  have ht:Tendsto (fun r:ℝ => γ 0+r • (Complex.I*d)) (𝓝 0) (𝓝 (γ 0)):=by
    have h:Continuous (fun r:ℝ => γ 0+r • (Complex.I*d)):=by fun_prop
    simpa only [zero_smul,add_zero] using h.tendsto 0
  obtain ⟨ε,hε,he⟩:=Metric.mem_nhds_iff.mp (ht.eventually (hn 0))
  let r:=min δ ε /2
  have hr:0 < r:=by dsimp [r]; exact half_pos (lt_min hδ hε)
  have hrd:r ≤ δ:=by dsimp [r]; linarith [min_le_left δ ε]
  have hre:r < ε:=by dsimp [r]; linarith [min_le_right δ ε]
  obtain ⟨hoff,hi⟩:=hjump r hr hrd
  have hlt:=hbelow _ hoff (by rw [hi]; norm_num)
  have hh:=he (show r ∈ Metric.ball (0:ℝ) ε by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hr] using hre) hlt.ne
  have hne:n = 1:=by simpa only [if_pos hlt,hi] using hh.symm
  simpa only [hne] using hn
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
lemma sum_loopIndex_sublevel.{u_1} {ι:Type u_1} [Fintype ι] [DecidableEq ι]
    (γ:ι → C(unitInterval,ℂ)) (hclosed:∀ i,γ i 1 = γ i 0)
    {f:ℂ → ℝ} {c:ℝ} (hf:Continuous f)
    (hcover:∀ z,f z = c ↔ ∃ i,z ∈ range (γ i))
    (hdisjoint:∀ i j,i ≠ j → Disjoint (range (γ i)) (range (γ j)))
    (hlocal:∀ i z,z ∈ range (γ i) → ∀ᶠ w in 𝓝 z,f w ≠ c →
      kz24 (γ i) w = if f w < c then 1 else 0)
    (hbelow:∀ i w,w ∉ range (γ i) → kz24 (γ i) w ≠ 0 → f w < c)
    (habove:∃ z,c < f z) :
    ∀ z,f z ≠ c → ∑ i,kz24 (γ i) z = if f z < c then 1 else 0:=by
  let J:ℂ → ℤ:=fun z => if f z = c then 0 else
    ∑ i,kz24 (γ i) z - if f z < c then 1 else 0
  have hzero (i:ι) (z:ℂ) (hz:c ≤ f z) (hoff:z ∉ range (γ i)) :
      kz24 (γ i) z = 0:=by
    by_contra hn
    exact (hbelow i z hoff hn).not_ge hz
  have hcont:Continuous J:=by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz:f z = c
    · obtain ⟨i,hiz⟩:=(hcover z).mp hz
      have hj:∀ᶠ w in 𝓝 z,∀ j,j ≠ i → kz24 (γ j) w = 0:=by
        apply Filter.eventually_all.mpr
        intro j
        by_cases hji:j = i
        · exact Filter.Eventually.of_forall (fun _ h => (h hji).elim)
        · have hoff:z ∉ range (γ j):=by
            intro hjz
            exact Set.disjoint_left.mp (hdisjoint i j (Ne.symm hji)) hiz hjz
          have hjz:=hzero j z hz.ge hoff
          filter_upwards [kz25 (γ j) (hclosed j) hoff] with w hw _
          exact hw.trans hjz
      have he:∀ᶠ w in 𝓝 z,J w = 0:=by
        filter_upwards [hlocal i z hiz,hj] with w hw hjw
        dsimp only [J]
        by_cases hwe:f w = c
        · rw [if_pos hwe]
        · rw [if_neg hwe]
          have hs : ∑ j,kz24 (γ j) w = kz24 (γ i) w:=by
            apply Finset.sum_eq_single i
            · intro j _ hji; exact hjw j hji
            · simp
          rw [hs,hw hwe,sub_self]
      exact continuousAt_const.congr (he.mono fun _ h => h.symm)
    · have hgood (i):z ∉ range (γ i):=fun hi => hz ((hcover z).mpr ⟨i,hi⟩)
      have hj:∀ᶠ w in 𝓝 z,∀ i,kz24 (γ i) w = kz24 (γ i) z :=
        Filter.eventually_all.mpr fun i => kz25 (γ i) (hclosed i) (hgood i)
      have hsign:∀ᶠ w in 𝓝 z,f w ≠ c ∧ (f w < c ↔ f z < c):=by
        by_cases hlt:f z < c
        · filter_upwards [(isOpen_lt hf continuous_const).mem_nhds hlt] with w hw
          exact ⟨hw.ne,iff_of_true hw hlt⟩
        · have hgt:c < f z:=lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hz)
          filter_upwards [(isOpen_lt continuous_const hf).mem_nhds hgt] with w hw
          exact ⟨hw.ne',iff_of_false hw.not_gt hlt⟩
      have he:∀ᶠ w in 𝓝 z,J w = J z:=by
        filter_upwards [hj,hsign] with w hjw hw
        simp only [J,if_neg hz,if_neg hw.1]
        rw [Finset.sum_congr rfl (fun i _ => hjw i)]
        simp only [hw.2]
      exact continuousAt_const.congr (he.mono fun _ h => h.symm)
  obtain ⟨a,ha⟩:=habove
  have hJa:J a = 0:=by
    have hs:∀ i,kz24 (γ i) a = 0:=fun i =>
      hzero i a ha.le (fun hi => ha.ne ((hcover a).mpr ⟨i,hi⟩).symm)
    simp only [J,if_neg ha.ne',if_neg ha.not_gt,hs,Finset.sum_const_zero,sub_zero]
  intro z hz
  have he:=(TotallyDisconnectedSpace.eq_of_continuous J hcont z a).trans hJa
  change (if f z = c then (0:ℤ) else _) = 0 at he
  rw [if_neg hz,sub_eq_zero] at he
  exact he
lemma kz335 {γ:ℝ → ℂ} (hγ:ContDiff ℝ 1 γ)
    (hp:Function.Periodic γ 1) (hinj:InjOn γ (Ico (0:ℝ) 1))
    (hd:∀ t,deriv γ t ≠ 0)
    (hm:∀ t,(γ 0).re ≤ (γ t).re)
    (hr:(deriv γ 0).re = 0) (hi:(deriv γ 0).im < 0)
    (X:C(ℂ,ℂ)) (hX:∀ t,X (γ t) ≠ 0)
    (horth:∀ t,(X (γ t)*(conj (deriv γ t))).re = 0) :
    kz18 (X.comp (kz274 hγ.continuous 0)) = 1:=by
  let T:C(unitInterval,ℂ):=⟨fun t => deriv γ t,
    (hγ.continuous_deriv (by simp)).comp continuous_subtype_val⟩
  let R:C(unitInterval,ℂ):=⟨fun t => X (γ t)/deriv γ t,by
    apply Continuous.div
    · exact X.continuous.comp (hγ.continuous.comp continuous_subtype_val)
    · exact T.continuous
    · exact fun t => hd t⟩
  have hTloop:T 1 = T 0:=(kz313 hp).eq
  have hRloop:R 1 = R 0:=by
    change X (γ 1)/deriv γ 1 = X (γ 0)/deriv γ 0
    rw [hp.eq,(kz313 hp).eq]
  have hRn (t):R t ≠ 0:=div_ne_zero (hX t) (hd t)
  have hRslit (t):R t ∈ Complex.slitPlane:=by
    apply Or.inr
    have hre:(R t).re = 0:=by
      change (X (γ t)/deriv γ t).re = 0
      rw [Complex.div_re,← add_div]
      have hh:=horth t
      simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,mul_neg,sub_neg_eq_add] at hh
      rw [hh,zero_div]
    intro him
    exact hRn t (Complex.ext hre him)
  have hwindR:kz18 R = 0:=by
    apply kz20 hRloop
    simpa only [hRloop,sub_self,Int.cast_zero,zero_mul] using HasLogIncrement.of_slit R hRslit
  have hwindT:kz18 T = 1:=by
    apply kz20 hTloop
    obtain ⟨A,hA,hinc⟩:=kz328 hγ hp hinj (fun t _ => hd t)
      (fun t _ => hm t) hr hi
    refine ⟨A,hA,?_⟩
    rw [hinc,add_sub_cancel_left]
    simp only [Int.cast_one,one_mul]
    push_cast
    ring
  have he:X.comp (kz274 hγ.continuous 0) = T*R:=by
    ext t
    change X (γ ((t:ℝ)+0)) = deriv γ t*(X (γ t)/deriv γ t)
    rw [add_zero,mul_div_cancel₀ _ (hd t)]
  rw [he,kz21 T R hTloop hRloop (fun t => hd t) hRn,hwindT,hwindR,add_zero]
lemma kz336 {γ:ℝ → ℂ} (hp:Periodic γ 1)
    (hinj:InjOn γ (Ico (0:ℝ) 1)) {a b:ℝ}
    (he:γ a = γ b) (hab:|a-b| < 1):a = b:=by
  have hh (t:ℝ):γ (Int.fract t) = γ t:=by
    simpa only [Int.fract,mul_one] using hp.sub_int_mul_eq (x:=t) ⌊t⌋
  have hfr:Int.fract a = Int.fract b:=hinj
    ⟨Int.fract_nonneg a,Int.fract_lt_one a⟩ ⟨Int.fract_nonneg b,Int.fract_lt_one b⟩
    ((hh a).trans (he.trans (hh b).symm))
  obtain ⟨n,hn⟩:=Int.fract_eq_fract.mp hfr
  rw [hn] at hab
  have hnlo:(-1:ℤ) < n:=by exact_mod_cast (abs_lt.mp hab).1
  have hnhi:n < (1:ℤ):=by exact_mod_cast (abs_lt.mp hab).2
  have hn0:n = 0:=by omega
  rw [hn0,Int.cast_zero] at hn
  exact sub_eq_zero.mp hn
lemma kz337 {γ:ℝ → ℂ} (hp:Periodic γ 1)
    (hinj:InjOn γ (Ico (0:ℝ) 1)) (s:ℝ) :
    InjOn (fun t => γ (t+s)) (Ico (0:ℝ) 1):=by
  intro a ha b hb he
  have hh:|(a+s)-(b+s)| < 1:=by
    rw [abs_lt]
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have heq:=kz336 hp hinj he hh
  linarith
lemma kz338 {γ:ℝ → ℂ} (hp:Periodic γ 1)
    (hinj:InjOn γ (Ico (0:ℝ) 1)) :
    InjOn (fun t => γ (-t)) (Ico (0:ℝ) 1):=by
  intro a ha b hb he
  have hh:|(-a)-(-b)| < 1:=by
    rw [abs_lt]
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have heq:=kz336 hp hinj he hh
  linarith
lemma kz339 {γ:ℝ → ℂ} (hc:ContDiff ℝ 1 γ)
    (hp:Periodic γ 1) (hinj:InjOn γ (Ico (0:ℝ) 1))
    (hd:∀ t,deriv γ t ≠ 0) :
    ∃ η:ℝ → ℂ,range η = range γ ∧ ContDiff ℝ 1 η ∧
      Periodic η 1 ∧ InjOn η (Ico (0:ℝ) 1) ∧ (∀ t,deriv η t ≠ 0) ∧
      (∀ t,(η 0).re ≤ (η t).re) ∧ (deriv η 0).re = 0 ∧ (deriv η 0).im < 0:=by
  have hk:IsCompact (range γ):=by
    rw [← kz276 hc.continuous hp 0]
    exact isCompact_range (kz274 hc.continuous 0).continuous
  obtain ⟨z,⟨s,hs⟩,hmin⟩:=hk.exists_isMinOn ⟨γ 0,⟨0,rfl⟩⟩
    Complex.continuous_re.continuousOn
  subst z
  let η:ℝ → ℂ:=fun t => γ (t+s)
  have hηr:range η = range γ:=by
    apply Subset.antisymm
    · rintro _ ⟨t,rfl⟩; exact ⟨t+s,rfl⟩
    · rintro _ ⟨t,rfl⟩; exact ⟨t-s,by simp only [η,sub_add_cancel]⟩
  have hηc:ContDiff ℝ 1 η:=hc.comp (contDiff_id.add contDiff_const)
  have hηp:Periodic η 1:=hp.add_const s
  have hηinj:InjOn η (Ico (0:ℝ) 1):=kz337 hp hinj s
  have hηd (t):deriv η t ≠ 0:=by
    dsimp only [η]
    rw [deriv_comp_add_const]
    exact hd (t+s)
  have hηmin (t):(η 0).re ≤ (η t).re:=by
    simpa only [η,zero_add] using
      (show (γ s).re ≤ (γ (t+s)).re from hmin ⟨t+s,rfl⟩)
  have hlocal:IsLocalMin (fun t => (η t).re) 0 :=
    Filter.Eventually.of_forall hηmin
  have hηre:(deriv η 0).re = 0:=hlocal.hasDerivAt_eq_zero
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
      ((hηc.differentiable (by simp)) 0).hasDerivAt)
  by_cases hi:(deriv η 0).im < 0
  · exact ⟨η,hηr,hηc,hηp,hηinj,hηd,hηmin,hηre,hi⟩
  · have him:0 < (deriv η 0).im:=lt_of_le_of_ne (not_lt.mp hi) (by
      intro he
      exact hηd 0 (Complex.ext hηre he.symm))
    let κ:ℝ → ℂ:=fun t => η (-t)
    have hκr:range κ = range η:=by
      apply Subset.antisymm
      · rintro _ ⟨t,rfl⟩; exact ⟨-t,rfl⟩
      · rintro _ ⟨t,rfl⟩; exact ⟨-t,by simp [κ]⟩
    refine ⟨κ,hκr.trans hηr,hηc.comp contDiff_id.neg,?_,
      kz338 hηp hηinj,?_,?_,?_,?_⟩
    · intro t
      change η (-(t+1)) = η (-t)
      rw [show -(t+1) = -t-1 by ring,hηp.sub_eq]
    · intro t
      dsimp only [κ]
      rw [deriv_comp_neg]
      exact neg_ne_zero.mpr (hηd (-t))
    · intro t
      simpa only [κ,neg_zero] using hηmin (-t)
    · dsimp only [κ]
      rw [deriv_comp_neg,neg_zero,Complex.neg_re,hηre,neg_zero]
    · dsimp only [κ]
      rw [deriv_comp_neg,neg_zero,Complex.neg_im]
      exact neg_neg_of_pos him
lemma kz340 {γ:ℝ → ℂ} {P:ℝ} (hP:0 < P)
    (hc:ContDiff ℝ 1 γ) (hp:Periodic γ P) (hinj:InjOn γ (Ico (0:ℝ) P))
    (hd:∀ t,deriv γ t ≠ 0) :
    ∃ η:ℝ → ℂ,range η = range γ ∧ ContDiff ℝ 1 η ∧
      Periodic η 1 ∧ InjOn η (Ico (0:ℝ) 1) ∧ (∀ t,deriv η t ≠ 0) ∧
      (∀ t,(η 0).re ≤ (η t).re) ∧ (deriv η 0).re = 0 ∧ (deriv η 0).im < 0:=by
  let κ:ℝ → ℂ:=fun t => γ (P*t)
  have hκr:range κ = range γ:=by
    apply Subset.antisymm
    · rintro _ ⟨t,rfl⟩; exact ⟨P*t,rfl⟩
    · rintro _ ⟨t,rfl⟩; exact ⟨t/P,by simp [κ,mul_div_cancel₀ _ hP.ne']⟩
  have hκc:ContDiff ℝ 1 κ:=hc.comp (contDiff_const.mul contDiff_id)
  have hκp:Periodic κ 1:=by
    intro t
    change γ (P*(t+1)) = γ (P*t)
    rw [mul_add,mul_one,hp]
  have hκinj:InjOn κ (Ico (0:ℝ) 1):=by
    intro a ha b hb he
    have heq:=hinj ⟨mul_nonneg hP.le ha.1,by nlinarith [ha.2]⟩
      ⟨mul_nonneg hP.le hb.1,by nlinarith [hb.2]⟩ he
    exact (mul_left_cancel₀ hP.ne') heq
  have hκd (t):deriv κ t ≠ 0:=by
    dsimp only [κ]
    rw [deriv_comp_mul_left]
    exact smul_ne_zero hP.ne' (hd (P*t))
  obtain ⟨η,hηr,hh⟩:=kz339 hκc hκp hκinj hκd
  exact ⟨η,hηr.trans hκr,hh⟩
lemma regular_level_index_sum.{u_1} {ι:Type u_1} [Fintype ι] [DecidableEq ι]
    {f:ℂ → ℝ} {c:ℝ} (hf:Continuous f)
    (γ:ι → ℝ → ℂ) (hc:∀ i,ContDiff ℝ 1 (γ i))
    (hp:∀ i,Periodic (γ i) 1) (hi:∀ i,InjOn (γ i) (Ico (0:ℝ) 1))
    (hd:∀ i t,deriv (γ i) t ≠ 0)
    (hm:∀ i t,(γ i 0).re ≤ (γ i t).re)
    (hr:∀ i,(deriv (γ i) 0).re = 0) (hdown:∀ i,(deriv (γ i) 0).im < 0)
    (hlevel:∀ i t,f (γ i t) = c)
    (hfreg:∀ z,f z = c → ContDiffAt ℝ 1 f z ∧ fderiv ℝ f z ≠ 0)
    (hcover:∀ z,f z = c ↔ ∃ i,z ∈ range (γ i))
    (hdisjoint:∀ i j,i ≠ j → Disjoint (range (γ i)) (range (γ j)))
    (hbelow:∀ i w,w ∉ range (γ i) →
      kz24 (kz274 (hc i).continuous 0) w ≠ 0 → f w < c)
    (habove:∃ z,c < f z)
    {K:Set ℂ} (hK:Convex ℝ K) (hγK:∀ i t,γ i t ∈ K)
    (s:Finset ℂ) (X:C(ℂ,ℂ)) (A:ℂ → ℂ →L[ℝ] ℂ)
    (hsK:∀ z ∈ s,z ∈ K) (hzero:∀ z ∈ K,X z = 0 ↔ z ∈ s)
    (hD:∀ z ∈ s,HasFDerivAt X (A z) z ∧ LinearMap.det (A z).toLinearMap ≠ 0)
    (hX:∀ i t,X (γ i t) ≠ 0)
    (horth:∀ i t,(X (γ i t)*conj (deriv (γ i) t)).re = 0) :
    ∑ a ∈ s,(if f a < c then kz59 (A a) else 0) = (Fintype.card ι:ℤ):=by
  let Γ (i:ι):=kz274 (hc i).continuous 0
  have hΓclosed (i):Γ i 1 = Γ i 0:=kz275 _ (hp i) 0
  have hΓrange (i):range (Γ i) = range (γ i):=kz276 _ (hp i) 0
  have hΓlocal (i) (z) (hz:z ∈ range (Γ i)) :
      ∀ᶠ w in 𝓝 z,f w ≠ c → kz24 (Γ i) w = if f w < c then 1 else 0:=by
    rw [hΓrange i] at hz
    obtain ⟨t,rfl⟩:=hz
    exact kz334 (hc i).continuous (hp i) (hi i)
      (((hc i).differentiable (by simp)) 0).hasDerivAt (hdown i) (hm i)
      (fun t => (hfreg _ (hlevel i t)).1) (fun t => (hfreg _ (hlevel i t)).2)
      (hlevel i) (hbelow i) t
  have hsum:=sum_loopIndex_sublevel Γ hΓclosed hf
    (by intro z; simp only [hΓrange]; exact hcover z)
    (by intro i j hij; rw [hΓrange,hΓrange]; exact hdisjoint i j hij)
    hΓlocal (by intro i w hw; rw [hΓrange] at hw; exact hbelow i w hw) habove
  have hnotlevel (a) (ha:a ∈ s):f a ≠ c:=by
    intro hal
    obtain ⟨i,t,ht⟩:=(hcover a).mp hal
    exact hX i t (ht ▸ (hzero a (hsK a ha)).mpr ha)
  have hindex (i):(1:ℤ) = ∑ a ∈ s,kz59 (A a)*kz24 (Γ i) a:=by
    have h:=kz61 hK s X A hsK hzero hD (Γ i) (hΓclosed i)
      (fun t => hγK i ((t:ℝ)+0)) (fun t => hX i ((t:ℝ)+0))
    rw [kz335 (hc i) (hp i) (hi i) (hd i) (hm i) (hr i)
      (hdown i) X (hX i) (horth i)] at h
    exact h
  calc
    ∑ a ∈ s,(if f a < c then kz59 (A a) else 0) =
        ∑ a ∈ s,kz59 (A a)*(∑ i,kz24 (Γ i) a):=by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsum a (hnotlevel a ha)]
      split_ifs <;> simp
    _ = ∑ i,∑ a ∈ s,kz59 (A a)*kz24 (Γ i) a:=by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ _i:ι,(1:ℤ):=by
      apply Finset.sum_congr rfl
      intro i _
      exact (hindex i).symm
    _ = (Fintype.card ι:ℤ):=by simp
def kz341 (f:ℂ → ℝ) (z:ℂ):ℂ :=
  (-(fderiv ℝ f z Complex.I):ℂ) + Complex.I*(fderiv ℝ f z 1:ℂ)
lemma kz342 (f:ℂ → ℝ) (z:ℂ) :
    fderiv ℝ f z (kz341 f z) = 0:=by
  rw [kz286]
  simp only [kz341,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im]
  ring
lemma kz343 {f:ℂ → ℝ} {z:ℂ} (h:fderiv ℝ f z ≠ 0) :
    kz341 f z ≠ 0:=by
  intro he
  have hre:=congrArg Complex.re he
  have him:=congrArg Complex.im he
  simp only [kz341,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.zero_re,Complex.zero_im] at hre him
  apply h
  ext w
  rw [kz286]
  simp only [zero_mul,one_mul,sub_zero,neg_zero,zero_add,add_zero,neg_eq_zero] at hre him
  simp only [him,hre,mul_zero,add_zero,zero_apply]
lemma kz344 {f:ℂ → ℝ} (hf:ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (kz341 f):=by
  have hd:=hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num)
  exact ((Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)).neg).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)))
lemma kz345 {f:ℂ → ℝ} {d:ℝ}
    (hs:HasCompactSupport (fun z => f z-d)):HasCompactSupport (kz341 f):=by
  have hD:=hs.fderiv ℝ
  apply hD.mono'
  intro z hz
  by_contra hn
  have hzer:fderiv ℝ (fun z => f z-d) z = 0:=notMem_support.mp
    (fun h => hn (subset_tsupport _ h))
  have hfzero:fderiv ℝ f z = 0:=by simpa only [fderiv_sub_const] using hzer
  exact hz (by simp only [kz341,hfzero,zero_apply,
    Complex.ofReal_zero,neg_zero,mul_zero,add_zero])
lemma kz346 {f:ℂ → ℝ} {c d:ℝ}
    (hf:ContDiff ℝ 2 f) (hs:HasCompactSupport (fun z => f z-d))
    (hreg:∀ z,f z = c → fderiv ℝ f z ≠ 0)
    (hK:IsCompact {z | f z = c}) :
    ∃ C:Finset (Set ℂ),(⋃ S ∈ C,S) = {z | f z = c} ∧
      (∀ S ∈ C,∀ T ∈ C,S ≠ T → Disjoint S T) ∧
      ∀ S ∈ C,∃ γ:ℝ → ℂ,range γ = S ∧ ContDiff ℝ 1 γ ∧
        Periodic γ 1 ∧ InjOn γ (Ico (0:ℝ) 1) ∧ (∀ t,deriv γ t ≠ 0) ∧
        (∀ t,(γ 0).re ≤ (γ t).re) ∧ (deriv γ 0).re = 0 ∧ (deriv γ 0).im < 0:=by
  obtain ⟨C,hC,hdis,hcurves⟩:=kz299
    (hf.of_le (by norm_num)) (kz344 hf) (kz345 hs)
    (kz342 f) hreg (fun z hz => kz343 (hreg z hz)) hK
  refine ⟨C,hC,hdis,?_⟩
  intro S hS
  obtain ⟨γ,P,hP,hrange,hD,hper,hinj⟩:=hcurves S hS
  have hlevel (t):f (γ t) = c:=by
    have hm:γ t ∈ ⋃ S ∈ C,S:=mem_iUnion₂.mpr ⟨S,hS,hrange ▸ mem_range_self t⟩
    rwa [hC] at hm
  obtain ⟨η,hηrange,hη⟩:=kz340 hP
    (kz291 (kz344 hf).continuous hD)
    hper hinj (fun t => by rw [(hD t).deriv]; exact kz343 (hreg _ (hlevel t)))
  exact ⟨η,hηrange.trans hrange,hη⟩
lemma kz347 (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0)
    {a:ℂ} (ha:∀ t,a.im < (γ t).im):kz24 γ a = 0:=by
  have hslit (t):γ t-a ∈ Complex.slitPlane:=by
    apply Complex.mem_slitPlane_iff.mpr
    right
    exact ne_of_gt (sub_pos.mpr (ha t))
  apply kz20 (by simp [hloop])
  refine ⟨⟨fun t => Complex.log (γ t-a),?_⟩,?_,?_⟩
  · exact Continuous.clog (by fun_prop) hslit
  · intro t
    exact Complex.exp_log (Complex.slitPlane_ne_zero (hslit t))
  · simp [hloop]
lemma kz348 (γ:C(unitInterval,ℂ))
    (hloop:γ 1 = γ 0) (hγ:∀ t,γ t ∈ kz145) :
    closure (kz30 γ) ⊆ kz145:=by
  obtain ⟨d,hd,hdist⟩:=isCompact_univ.exists_forall_le'
    (show ContinuousOn (fun t:unitInterval => (γ t).im) univ by fun_prop)
    (a:=0) (fun t _ => hγ t)
  have hsub:kz30 γ ⊆ {a:ℂ | d ≤ a.im}:=by
    intro a ha
    by_contra hn
    exact ha.2 (kz347 γ hloop
      (fun t => (lt_of_not_ge hn).trans_le (hdist t (mem_univ t))))
  have hc:=closure_minimal hsub (isClosed_le continuous_const Complex.continuous_im)
  intro a ha
  exact hd.trans_le (hc ha)
lemma kz349 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {k b:ℝ} (hk:0 < k) (hb:0 < b) (ξ:ℂ)
    (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) (hγ:∀ t,γ t ∈ kz145)
    (hlevel:∀ t,kz241 f k ξ (γ t) = b)
    {z:ℂ} (hz:z ∈ kz30 γ):kz241 f k ξ z < b:=by
  apply kz246 hf hk hb ξ (kz31 γ hloop)
    ((kz32 γ hloop).isCompact_closure)
    (kz348 γ hloop hγ) _ hz
  intro w hw
  obtain ⟨t,rfl⟩:=kz33 γ hloop hw
  exact (hlevel t).le
lemma kz350 {U:Set ℂ} (hU:IsOpen U) {f:ℂ → ℝ}
    (hf:∀ z ∈ U,ContDiffAt ℝ 2 f z) {d:ℝ}
    (hK:IsCompact {z | z ∈ U ∧ f z ≤ d}) :
    ∃ F:ℂ → ℝ,ContDiff ℝ 2 F ∧ HasCompactSupport (fun z => F z-d) ∧
      (∀ z,z ∈ U → f z ≤ d → F =ᶠ[𝓝 z] f) ∧
      (∀ z ∉ U,F z = d) ∧
      (∀ z c,c < d → (F z ≤ c ↔ z ∈ U ∧ f z ≤ c)) ∧
      (∀ z c,c < d → (F z < c ↔ z ∈ U ∧ f z < c)):=by
  obtain ⟨χ,hχc,hχK,hχU,hχ1,hχrange⟩:=kz75 hK hU
    (fun _ h => h.1)
  let F:=fun z => χ z*(f z-d)+d
  have heq (z) (hz:z ∈ U) (hzd:f z ≤ d):F =ᶠ[𝓝 z] f:=by
    filter_upwards [hχ1 z ⟨hz,hzd⟩] with w hw
    simp only [F,hw,one_mul,sub_add_cancel]
  have hzero (z) (hz:z ∉ tsupport χ):F =ᶠ[𝓝 z] fun _ => d:=by
    filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
    have hh:χ w = 0:=notMem_support.mp (fun h => hw (subset_tsupport χ h))
    simp only [F,hh,zero_mul,zero_add]
  have hFc:ContDiff ℝ 2 F:=by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz:z ∈ tsupport χ
    · exact ((hχc.contDiffAt.mul ((hf z (hχU hz)).sub contDiffAt_const)).add
        contDiffAt_const)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero z hz)
  have hFK:HasCompactSupport (fun z => F z-d):=by
    apply hχK.mono'
    intro z hz
    by_contra hn
    have hh:=(hzero z hn).self_of_nhds
    exact hz (sub_eq_zero.mpr hh)
  have hFd (z) (hz:z ∉ U):F z = d :=
    (hzero z (fun h => hz (hχU h))).self_of_nhds
  have hlarge (z) (hz:z ∈ U) (hdz:d ≤ f z):d ≤ F z:=by
    dsimp only [F]
    exact le_add_of_nonneg_left (mul_nonneg (hχrange z).1 (sub_nonneg.mpr hdz))
  refine ⟨F,hFc,hFK,heq,hFd,?_,?_⟩
  · intro z c hc
    constructor
    · intro hz
      have hzU:z ∈ U:=by
        by_contra hn
        rw [hFd z hn] at hz
        exact hc.not_ge hz
      have hzd:f z ≤ d:=by
        by_contra hn
        exact hc.not_ge ((hlarge z hzU (not_le.mp hn).le).trans hz)
      exact ⟨hzU,(heq z hzU hzd).self_of_nhds ▸ hz⟩
    · rintro ⟨hzU,hz⟩
      rwa [(heq z hzU (hz.trans hc.le)).self_of_nhds]
  · intro z c hc
    constructor
    · intro hz
      have hzU:z ∈ U:=by
        by_contra hn
        rw [hFd z hn] at hz
        exact hc.not_gt hz
      have hzd:f z ≤ d:=by
        by_contra hn
        exact hc.not_gt ((hlarge z hzU (not_le.mp hn).le).trans_lt hz)
      exact ⟨hzU,(heq z hzU hzd).self_of_nhds ▸ hz⟩
    · rintro ⟨hzU,hz⟩
      rwa [(heq z hzU (hz.le.trans hc.le)).self_of_nhds]
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def kz351 (f:ℂ → ℂ) (k:ℝ) (ξ z:ℂ):ℝ :=
  ‖f z-ξ‖^2 * z.im^(-2*k)
lemma kz352 {f:ℂ → ℂ} {k:ℝ} {ξ z:ℂ}
    (hz:z ∈ kz145) :
    kz351 f k ξ z = (kz241 f k ξ z)^2:=by
  rw [kz351,kz241,div_pow]
  have he:z.im^(-2*k) = ((z.im^k)^2)⁻¹:=by
    rw [show -2*k = -(k*2) by ring,Real.rpow_neg hz.le,Real.rpow_mul hz.le,
      Real.rpow_two]
  rw [he,div_eq_mul_inv]
lemma kz353 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {z:ℂ} (hz:z ∈ kz145) (k:ℝ) (ξ:ℂ) :
    ContDiffAt ℝ 2 (kz351 f k ξ) z:=by
  have hc:ContDiffAt ℝ 2 f z :=
    (hf.1.analyticOnNhd kz146 z hz).contDiffAt.restrict_scalars ℝ
  exact ((hc.sub contDiffAt_const).norm_sq ℂ).mul
    (Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne (ne_of_gt hz))
lemma kz354 {f:ℂ → ℂ} {k h:ℝ}
    (hk:0 ≤ k) (hh:0 < h) {ξ z:ℂ} (hz:z ∈ kz145) :
    ENNReal.ofReal h ≤ kz214 f k ξ z ↔ kz241 f k ξ z ≤ h⁻¹:=by
  have hy:=Real.rpow_pos_of_pos hz k
  rw [kz214,ENNReal.ofReal_rpow_of_nonneg hz.le hk,
    ENNReal.le_div_iff_mul_le
      (Or.inr (ne_of_gt (ENNReal.ofReal_pos.mpr hy))) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hh.le,ENNReal.ofReal_le_ofReal_iff hy.le,kz241,
    div_le_iff₀ hy,inv_mul_eq_div,le_div_iff₀ hh]
  exact mul_comm h ‖f z-ξ‖ ▸ Iff.rfl
lemma kz355 {f:ℂ → ℂ} {k:ℝ} (hk:0 ≤ k)
    {ξ:ℂ} (hg:kz215 f k ξ) {d:ℝ} (hd:0 < d) :
    IsCompact {z | z ∈ kz145 ∧ kz351 f k ξ z ≤ d}:=by
  have hs:0 < Real.sqrt d:=Real.sqrt_pos.mpr hd
  have he:{z | z ∈ kz145 ∧ kz351 f k ξ z ≤ d} =
      {z | z ∈ kz145 ∧ ENNReal.ofReal ((Real.sqrt d)⁻¹) ≤ kz214 f k ξ z}:=by
    ext z
    constructor
    · rintro ⟨hz,hzval⟩
      refine ⟨hz,(kz354 hk (inv_pos.mpr hs) hz).mpr ?_⟩
      rw [inv_inv]
      rw [kz352 hz] at hzval
      nlinarith [Real.sq_sqrt hd.le]
    · rintro ⟨hz,hzval⟩
      have hv:=(kz354 hk (inv_pos.mpr hs) hz).mp hzval
      rw [inv_inv] at hv
      refine ⟨hz,?_⟩
      rw [kz352 hz]
      have hn:0 ≤ kz241 f k ξ z:=div_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _)
      nlinarith [Real.sq_sqrt hd.le]
  rw [he]
  exact hg.1 _ (inv_pos.mpr hs)
lemma kz356 {f:ℂ → ℂ} {k:ℝ} (hk:k ≠ 0)
    {ξ z:ℂ} (hz:z ∈ kz145) :
    kz247 f k ξ z =
      ((k:ℂ)*Complex.I/(z.im:ℂ))*((‖f z-ξ‖^2:ℝ):ℂ) -
        (f z-ξ)*conj (deriv f z):=by
  have hy:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hkc:(k:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr hk
  have he:conj (kz204 f k z-ξ) = conj (f z-ξ) +
      Complex.I/(k:ℂ)*(z.im:ℂ)*conj (deriv f z):=by
    simp only [kz204,div_eq_mul_inv,map_sub,map_mul,map_inv₀,Complex.conj_I,Complex.conj_ofReal]
    ring
  rw [kz247,he,mul_add,mul_assoc _ (f z-ξ),Complex.mul_conj',
    ← Complex.ofReal_pow]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring
lemma kz357 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {k:ℝ} (hk:k ≠ 0)
    {ξ z:ℂ} (hz:z ∈ kz145) (v:ℂ) :
    fderiv ℝ (kz351 f k ξ) z v =
      -2*z.im^(-2*k)*(kz247 f k ξ z * conj v).re:=by
  have hd:=(((hf.1 z hz).differentiableAt (kz146.mem_nhds hz)).hasDerivAt.sub_const ξ).hasFDerivAt.restrictScalars ℝ
  have hy:=Complex.imCLM.hasFDerivAt.rpow_const (p:=-2*k) (Or.inl (ne_of_gt hz))
  have hu:=hd.norm_sq.fun_mul hy
  simp only [Complex.imCLM_apply] at hu
  change (fderiv ℝ (fun w => ‖f w - ξ‖ ^ 2 * w.im ^ (-2*k)) z) v = _
  rw [hu.fderiv]
  simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,innerSL_apply_apply,Complex.imCLM_apply]
  rw [kz356 hk hz,Real.rpow_sub hz,Real.rpow_one]
  simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.sub_re,Complex.sub_im,Complex.div_re,Complex.div_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.normSq_ofReal]
  field_simp [ne_of_gt (show 0 < z.im from hz)]
  ring
lemma kz358 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {k:ℝ} (hk:k ≠ 0)
    {ξ z:ℂ} (hz:z ∈ kz145) :
    fderiv ℝ (kz351 f k ξ) z = 0 ↔
      kz247 f k ξ z = 0:=by
  constructor
  · intro hzero
    have hh:=kz357 hf hk (ξ:=ξ) hz
      (kz247 f k ξ z)
    rw [hzero,zero_apply,Complex.mul_conj',← Complex.ofReal_pow,Complex.ofReal_re] at hh
    have hp:=Real.rpow_pos_of_pos hz (-2*k)
    have hn:=norm_nonneg (kz247 f k ξ z)
    apply norm_eq_zero.mp
    have hsq:‖kz247 f k ξ z‖^2 = 0 :=
      (mul_eq_zero.mp hh.symm).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt hp))
    nlinarith
  · intro hzero
    ext v
    rw [kz357 hf hk hz v,hzero]
    simp
lemma kz359 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:k ≠ 0) {ξ:ℂ} (hg:kz215 f k ξ)
    {z:ℂ} (hz:z ∈ kz145) (hzero:kz247 f k ξ z = 0) :
    LinearMap.det (fderiv ℝ (kz247 f k ξ) z).toLinearMap ≠ 0:=by
  rcases (kz248 hk hz).mp hzero with hp | hc
  · exact ne_of_gt (kz255 hf hk hz hp)
  · rw [kz254 hf hz hc]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr
          (mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk)
            Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
            (sub_ne_zero.mpr (kz224 hf hk hz hc)))))
      · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr
          (kz91 kz146 hf hz))
    · exact hg.2 z hz hc
lemma kz360 {P:Set ℂ} (hP:IsCompact P)
    (hPH:P ⊆ kz145) :
    ∃ K:Set ℂ,IsCompact K ∧ Convex ℝ K ∧ P ⊆ K ∧ K ⊆ kz145:=by
  obtain ⟨η,hη,hheight⟩:=hP.exists_forall_le' Complex.continuous_im.continuousOn hPH
  obtain ⟨R,hR⟩:=hP.isBounded.subset_closedBall (0:ℂ)
  refine ⟨Metric.closedBall 0 R ∩ {z:ℂ | η ≤ z.im},
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const Complex.continuous_im),
    (convex_closedBall (0:ℂ) R).inter (convex_halfSpace_im_ge η),?_,?_⟩
  · exact fun z hz => ⟨hR hz,hheight z hz⟩
  · exact fun z hz => hη.trans_le hz.2
lemma kz361 {K U:Set ℂ} (hK:IsCompact K)
    (hU:IsOpen U) (hKU:K ⊆ U) {x:ℂ → ℂ}
    (hx:∀ z ∈ U,ContinuousAt x z) :
    ∃ X:C(ℂ,ℂ),∀ z ∈ K,(X:ℂ → ℂ) =ᶠ[𝓝 z] x:=by
  obtain ⟨χ,hχc,_hχK,hχU,hχ1,_hχrange⟩:=kz75 hK hU hKU
  let X:=fun z => (χ z:ℂ)*x z
  have hX:Continuous X:=by
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz:z ∈ tsupport χ
    · exact (Complex.continuous_ofReal.continuousAt.comp hχc.continuous.continuousAt).mul
        (hx z (hχU hz))
    · have he:X =ᶠ[𝓝 z] fun _ => 0:=by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
        have hzero:χ w = 0:=notMem_support.mp (fun h => hw (subset_tsupport χ h))
        simp only [X,hzero,Complex.ofReal_zero,zero_mul]
      exact continuousAt_const.congr he.symm
  refine ⟨⟨X,hX⟩,?_⟩
  intro z hz
  filter_upwards [hχ1 z hz] with w hw
  simp only [ContinuousMap.coe_mk,X,hw,Complex.ofReal_one,one_mul]
lemma kz362 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {k c:ℝ} (hk:0 < k) (hc:0 < c) (ξ:ℂ)
    (γ:C(unitInterval,ℂ)) (hloop:γ 1 = γ 0) (hγ:∀ t,γ t ∈ kz145)
    (hlevel:∀ t,kz351 f k ξ (γ t) = c)
    {z:ℂ} (hz:z ∈ kz30 γ) :
    z ∈ kz145 ∧ kz351 f k ξ z < c:=by
  have hzH:=kz348 γ hloop hγ (subset_closure hz)
  have hb:0 < Real.sqrt c:=Real.sqrt_pos.mpr hc
  have hl (t):kz241 f k ξ (γ t) = Real.sqrt c:=by
    have hsq:=hlevel t
    rw [kz352 (hγ t)] at hsq
    have hn:0 ≤ kz241 f k ξ (γ t) :=
      div_nonneg (norm_nonneg _) (Real.rpow_nonneg (hγ t).le _)
    nlinarith [Real.sq_sqrt hc.le]
  have hh:=kz349 hf hk hb ξ γ hloop hγ hl hz
  have hn:0 ≤ kz241 f k ξ z :=
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg hzH.le _)
  refine ⟨hzH,?_⟩
  rw [kz352 hzH]
  nlinarith [Real.sq_sqrt hc.le]
lemma kz363 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:0 < k) {ξ:ℂ} (hg:kz215 f k ξ) {c:ℝ} (hc:0 < c)
    (hreg:∀ z ∈ kz145,kz351 f k ξ z = c →
      kz247 f k ξ z ≠ 0) :
    ∃ (s:Finset ℂ) (N:ℕ),
      (∀ z ∈ s,z ∈ kz145 ∧ kz247 f k ξ z = 0) ∧
      (∀ z ∈ kz145,kz351 f k ξ z < c →
        (z ∈ s ↔ kz247 f k ξ z = 0)) ∧
      (∑ z ∈ s,if kz351 f k ξ z < c then
        kz59 (fderiv ℝ (kz247 f k ξ) z) else 0) = (N:ℤ) ∧
      ((∃ z ∈ kz145,f z = ξ) → 1 ≤ N):=by
  classical
  let u:=kz351 f k ξ
  let x:=kz247 f k ξ
  let d:=c+1
  have hcd:c < d:=by dsimp [d]; linarith
  have hd:0 < d:=hc.trans hcd
  have hP:=kz355 hk.le hg hd
  obtain ⟨K,hK,hKcv,hPK,hKH⟩:=kz360 hP (fun _ h => h.1)
  obtain ⟨F,hFc,hFs,hFeq,hFout,hFle,hFlt⟩:=kz350 kz146
    (fun z hz => kz353 hf hz k ξ) hP
  have hlevel (z) (hz:F z = c):z ∈ kz145 ∧ u z = c:=by
    have hh:=(hFle z c hcd).mp hz.le
    exact ⟨hh.1,((hFeq z hh.1 (hh.2.trans hcd.le)).self_of_nhds).symm.trans hz⟩
  have hFreg (z) (hz:F z = c):fderiv ℝ F z ≠ 0:=by
    obtain ⟨hzH,huz⟩:=hlevel z hz
    rw [(hFeq z hzH (huz.le.trans hcd.le)).fderiv_eq]
    exact fun hh => hreg z hzH huz ((kz358
      hf (ne_of_gt hk) hzH).mp hh)
  have hL:IsCompact {z | F z = c}:=hP.of_isClosed_subset
    (isClosed_eq hFc.continuous continuous_const)
    (fun z hz => ⟨(hlevel z hz).1,(hlevel z hz).2.le.trans hcd.le⟩)
  obtain ⟨C,hC,hdis,hcurves⟩:=kz346 hFc hFs hFreg hL
  let ι:={S:Set ℂ // S ∈ C}
  choose γ hγrange hγc hγp hγi hγd hγm hγr hγdown using
    (fun S:ι => hcurves S.1 S.2)
  have hγlevel (i:ι) (t:ℝ):F (γ i t) = c:=by
    have hh:γ i t ∈ ⋃ S ∈ C,S:=mem_iUnion₂.mpr
      ⟨i.1,i.2,hγrange i ▸ mem_range_self t⟩
    rwa [hC] at hh
  have hγH (i:ι) (t:ℝ):γ i t ∈ kz145:=(hlevel _ (hγlevel i t)).1
  have hγu (i:ι) (t:ℝ):u (γ i t) = c:=(hlevel _ (hγlevel i t)).2
  have hcover (z):F z = c ↔ ∃ i:ι,z ∈ range (γ i):=by
    constructor
    · intro hz
      have hm:z ∈ ⋃ S ∈ C,S:=hC.symm ▸ hz
      obtain ⟨S,hS,hzS⟩:=mem_iUnion₂.mp hm
      exact ⟨⟨S,hS⟩,(hγrange ⟨S,hS⟩).symm ▸ hzS⟩
    · rintro ⟨i,t,rfl⟩
      exact hγlevel i t
  have hγdis (i j:ι) (hij:i ≠ j):Disjoint (range (γ i)) (range (γ j)):=by
    rw [hγrange,hγrange]
    exact hdis i.1 i.2 j.1 j.2 (Subtype.val_injective.ne hij)
  have hbelow (i:ι) (w:ℂ) (hw:w ∉ range (γ i))
      (hind:kz24 (kz274 (hγc i).continuous 0) w ≠ 0):F w < c:=by
    have hw':w ∈ kz30 (kz274 (hγc i).continuous 0) :=
      ⟨by rwa [kz276 _ (hγp i) 0],hind⟩
    have hh:=kz362 hf hk hc ξ
      (kz274 (hγc i).continuous 0) (kz275 _ (hγp i) 0)
      (fun t => hγH i ((t:ℝ)+0)) (fun t => hγu i ((t:ℝ)+0)) hw'
    exact (hFlt w c hcd).mpr hh
  have hFzero:F 0 = d:=hFout 0 (by simp [kz145])
  have habove:∃ z,c < F z:=⟨0,hFzero ▸ hcd⟩
  obtain ⟨X,hXeq⟩:=kz361 hK kz146 hKH
    (fun z hz => (kz250 hf hz k ξ).continuousAt)
  have hfinite:{z | z ∈ K ∧ x z = 0}.Finite:=kz70 hK
    (fun z hz => (kz250 hf (hKH hz) k ξ).continuousAt.continuousWithinAt)
    (fun z hz hzero => ⟨kz250 hf (hKH hz) k ξ,
      kz359 hf (ne_of_gt hk) hg (hKH hz) hzero⟩)
  let s:=hfinite.toFinset
  have hs (z):z ∈ s ↔ z ∈ K ∧ x z = 0:=hfinite.mem_toFinset
  have hsK (z) (hz:z ∈ s):z ∈ K:=((hs z).mp hz).1
  have hXzero (z) (hz:z ∈ K):X z = 0 ↔ z ∈ s:=by
    rw [(hXeq z hz).self_of_nhds,hs]
    exact ⟨fun h => ⟨hz,h⟩,fun h => h.2⟩
  have hD (z) (hz:z ∈ s) :
      HasFDerivAt X (fderiv ℝ x z) z ∧ LinearMap.det (fderiv ℝ x z).toLinearMap ≠ 0:=by
    refine ⟨(kz250 hf (hKH (hsK z hz)) k ξ).hasFDerivAt.congr_of_eventuallyEq
      (hXeq z (hsK z hz)),?_⟩
    exact kz359 hf (ne_of_gt hk) hg (hKH (hsK z hz)) ((hs z).mp hz).2
  have hγK (i:ι) (t:ℝ):γ i t ∈ K:=hPK ⟨hγH i t,(hγu i t).le.trans hcd.le⟩
  have hX (i:ι) (t:ℝ):X (γ i t) ≠ 0:=by
    rw [(hXeq _ (hγK i t)).self_of_nhds]
    exact hreg _ (hγH i t) (hγu i t)
  have horth (i:ι) (t:ℝ):(X (γ i t)*conj (deriv (γ i) t)).re = 0:=by
    have he:HasDerivAt (fun q => F (γ i q))
        (fderiv ℝ F (γ i t) (deriv (γ i) t)) t :=
      ((hFc.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt t
        (((hγc i).differentiable (by norm_num)) t).hasDerivAt
    have he0:fderiv ℝ F (γ i t) (deriv (γ i) t) = 0 :=
      (he.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun q => (hγlevel i q).symm))).unique (hasDerivAt_const t c)
    rw [(hFeq _ (hγH i t) ((hγu i t).le.trans hcd.le)).fderiv_eq,
      kz357 hf (ne_of_gt hk) (hγH i t)] at he0
    rw [(hXeq _ (hγK i t)).self_of_nhds]
    exact (mul_eq_zero.mp he0).resolve_left (mul_ne_zero (by norm_num)
      (ne_of_gt (Real.rpow_pos_of_pos (hγH i t) (-2*k))))
  have hsum:=regular_level_index_sum hFc.continuous γ hγc hγp hγi hγd hγm hγr hγdown
    hγlevel (fun z hz => ⟨hFc.contDiffAt.of_le (by norm_num),hFreg z hz⟩)
    hcover hγdis hbelow habove hKcv hγK s X (fderiv ℝ x) hsK hXzero hD hX horth
  refine ⟨s,Fintype.card ι,?_,?_,?_,?_⟩
  · intro z hz
    exact ⟨hKH (hsK z hz),((hs z).mp hz).2⟩
  · intro z hzH hzu
    rw [hs]
    exact ⟨fun h => h.2,fun hx => ⟨hPK ⟨hzH,hzu.le.trans hcd.le⟩,hx⟩⟩
  · convert hsum using 1
    apply Finset.sum_congr rfl
    intro z hz
    simp only [show (F z < c) ↔ u z < c from (hFlt z c hcd).trans
      (and_iff_right (hKH (hsK z hz)))]
    rfl
  · rintro ⟨z,hzH,hpole⟩
    have huz:u z = 0:=by simp [u,kz351,hpole]
    have hFz:F z = 0:=(hFeq z hzH (huz.le.trans hd.le)).self_of_nhds.trans huz
    obtain ⟨w,hw⟩:=intermediate_value_univ z 0 hFc.continuous
      (show c ∈ Icc (F z) (F 0) by rw [hFz,hFzero]; exact ⟨hc.le,hcd.le⟩)
    obtain ⟨i,_hi⟩:=(hcover w).mp hw
    exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
lemma kz364 {f:ℂ → ℂ}
    (hf:kz1 f kz145) {k:ℝ} (hk:k ≠ 0)
    {ξ z:ℂ} (hz:z ∈ kz145) (hcrit:kz204 f k z = ξ) :
    kz59 (fderiv ℝ (kz247 f k ξ) z) =
      if kz205 f k z < 0 then 1 else -1:=by
  have hp:0 < ‖((k:ℂ)*Complex.I/(z.im:ℂ))*(f z-ξ)‖^2 * ‖deriv f z‖^2:=by
    apply mul_pos
    · apply sq_pos_of_pos
      apply norm_pos_iff.mpr
      exact mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk)
        Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
        (sub_ne_zero.mpr (kz224 hf hk hz hcrit))
    · exact sq_pos_of_pos (norm_pos_iff.mpr (kz91 kz146 hf hz))
  rw [kz59,kz254 hf hz hcrit]
  congr 1
  apply propext
  rw [neg_mul,neg_mul,neg_pos]
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg hp.le (le_of_not_gt hn))) h
  · exact mul_neg_of_pos_of_neg hp
lemma kz365 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:0 < k) {ξ:ℂ} (hg:kz215 f k ξ) {c:ℝ} (hc:0 < c)
    (hreg:∀ z ∈ kz145,kz351 f k ξ z = c →
      kz247 f k ξ z ≠ 0) :
    let critical:={z | z ∈ kz145 ∧ kz204 f k z = ξ ∧
      kz351 f k ξ z < c}
    critical.Finite ∧ ({z ∈ critical | 0 < kz205 f k z}).ncard ≤
      ({z ∈ critical | kz205 f k z < 0}).ncard:=by
  classical
  dsimp only
  obtain ⟨s,N,hs,hsall,hsum,hpole⟩:=kz363 hf hk hg hc hreg
  let u:=kz351 f k ξ
  let p:=s.filter (fun z => u z < c ∧ f z = ξ)
  let m:=s.filter (fun z => u z < c ∧ kz204 f k z = ξ ∧ kz205 f k z < 0)
  let a:=s.filter (fun z => u z < c ∧ kz204 f k z = ξ ∧ 0 < kz205 f k z)
  have hcritmem (z) (hz:z ∈ kz145) (hG:kz204 f k z = ξ) (hu:u z < c):z ∈ s :=
    (hsall z hz hu).mpr ((kz248 (ne_of_gt hk) hz).mpr (Or.inr hG))
  have hfinite:{z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ u z < c}.Finite :=
    s.finite_toSet.subset (fun z hz => hcritmem z hz.1 hz.2.1 hz.2.2)
  have hmset:{z | (z ∈ kz145 ∧ kz204 f k z = ξ ∧ u z < c) ∧
      kz205 f k z < 0} = (m:Set ℂ):=by
    ext z
    simp only [m,Finset.mem_coe,Finset.mem_filter,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz,hG,hu⟩,hJ⟩
      exact ⟨hcritmem z hz hG hu,hu,hG,hJ⟩
    · rintro ⟨hz,hu,hG,hJ⟩
      exact ⟨⟨(hs z hz).1,hG,hu⟩,hJ⟩
  have haset:{z | (z ∈ kz145 ∧ kz204 f k z = ξ ∧ u z < c) ∧
      0 < kz205 f k z} = (a:Set ℂ):=by
    ext z
    simp only [a,Finset.mem_coe,Finset.mem_filter,mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz,hG,hu⟩,hJ⟩
      exact ⟨hcritmem z hz hG hu,hu,hG,hJ⟩
    · rintro ⟨hz,hu,hG,hJ⟩
      exact ⟨⟨(hs z hz).1,hG,hu⟩,hJ⟩
  have hpcard:p.card ≤ 1:=by
    apply Finset.card_le_one.mpr
    intro z hz w hw
    obtain ⟨hz,huz,hpz⟩:=Finset.mem_filter.mp hz
    obtain ⟨hw,huw,hpw⟩:=Finset.mem_filter.mp hw
    exact hf.2 (hs z hz).1 (hs w hw).1 (hpz.trans hpw.symm)
  have hpN:p.card ≤ N:=by
    by_cases hpe:p = ∅
    · simp [hpe]
    · obtain ⟨z,hz⟩:=Finset.nonempty_iff_ne_empty.mpr hpe
      obtain ⟨hz,huz,hpz⟩:=Finset.mem_filter.mp hz
      exact hpcard.trans (hpole ⟨z,(hs z hz).1,hpz⟩)
  have hterm (z) (hz:z ∈ s) :
      (if u z < c then kz59 (fderiv ℝ (kz247 f k ξ) z) else 0) =
        (if u z < c ∧ f z = ξ then (1:ℤ) else 0) +
        (if u z < c ∧ kz204 f k z = ξ ∧ kz205 f k z < 0 then 1 else 0) -
        (if u z < c ∧ kz204 f k z = ξ ∧ 0 < kz205 f k z then 1 else 0):=by
    by_cases hu:u z < c
    · simp only [hu,true_and,ite_true]
      rcases (kz248 (ne_of_gt hk) (hs z hz).1).mp (hs z hz).2 with hpz | hG
      · have hGn:kz204 f k z ≠ ξ:=fun h => kz224 hf (ne_of_gt hk) (hs z hz).1 h hpz
        simp [hpz,hGn,kz59,kz255 hf (ne_of_gt hk) (hs z hz).1 hpz]
      · have hpn:=kz224 hf (ne_of_gt hk) (hs z hz).1 hG
        rw [kz364 hf (ne_of_gt hk) (hs z hz).1 hG]
        rcases lt_or_gt_of_ne (hg.2 z (hs z hz).1 hG) with hJ | hJ
        · simp [hpn,hG,hJ,not_lt_of_ge hJ.le]
        · simp [hpn,hG,hJ,not_lt_of_ge hJ.le]
    · simp [hu]
  have heuler:(p.card:ℤ) + m.card - a.card = N:=by
    rw [← hsum]
    calc
      (p.card:ℤ) + m.card - a.card =
          ∑ z ∈ s,((if u z < c ∧ f z = ξ then (1:ℤ) else 0) +
            (if u z < c ∧ kz204 f k z = ξ ∧ kz205 f k z < 0 then 1 else 0) -
            (if u z < c ∧ kz204 f k z = ξ ∧ 0 < kz205 f k z then 1 else 0)):=by
        simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_boole,p,m,a]
      _ = _:=Finset.sum_congr rfl (fun z hz => (hterm z hz).symm)
  refine ⟨hfinite,?_⟩
  change ({z | (z ∈ kz145 ∧ kz204 f k z = ξ ∧ u z < c) ∧
      0 < kz205 f k z}).ncard ≤
    ({z | (z ∈ kz145 ∧ kz204 f k z = ξ ∧ u z < c) ∧
      kz205 f k z < 0}).ncard
  rw [haset,hmset,Set.ncard_coe_finset,Set.ncard_coe_finset]
  omega
lemma kz366 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:0 ≤ k) {ξ:ℂ} (hg:kz215 f k ξ) {d:ℝ} (hd:0 < d) :
    {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧
      kz351 f k ξ z ≤ d}.Finite:=by
  have hs:0 < Real.sqrt d:=Real.sqrt_pos.mpr hd
  apply (kz218 hf hg (h:=(Real.sqrt d)⁻¹) (inv_pos.mpr hs)).subset
  intro z hz
  refine ⟨hz.1,hz.2.1,(kz354 hk (inv_pos.mpr hs) hz.1).mpr ?_⟩
  rw [inv_inv]
  have hh:=hz.2.2
  rw [kz352 hz.1] at hh
  nlinarith [Real.sq_sqrt hd.le]
lemma kz367 {f:ℂ → ℂ} {k h:ℝ}
    (hk:0 ≤ k) (hh:0 < h) {ξ z:ℂ} (hz:z ∈ kz145) :
    ENNReal.ofReal h ≤ kz214 f k ξ z ↔
      kz351 f k ξ z ≤ (h⁻¹)^2:=by
  rw [kz354 hk hh hz,kz352 hz]
  exact (sq_le_sq₀ (div_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _))
    (inv_nonneg.mpr hh.le)).symm
lemma kz368 (s:Finset ℝ) (r d:ℝ) (hrd:r < d) :
    ∃ c,r < c ∧ c < d ∧ ∀ a ∈ s,r < a → c < a:=by
  classical
  induction s using Finset.induction_on generalizing d with
  | empty =>
    obtain ⟨c,hrc,hcd⟩:=exists_between hrd
    exact ⟨c,hrc,hcd,by simp⟩
  | @insert a s ha ih =>
    by_cases hra:r < a
    · obtain ⟨c,hrc,hcd,hcs⟩:=ih (min d a) (lt_min hrd hra)
      refine ⟨c,hrc,hcd.trans_le (min_le_left _ _),?_⟩
      intro b hb hrb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact hcd.trans_le (min_le_right _ _)
      · exact hcs b hb hrb
    · obtain ⟨c,hrc,hcd,hcs⟩:=ih d hrd
      refine ⟨c,hrc,hcd,?_⟩
      intro b hb hrb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact (hra hrb).elim
      · exact hcs b hb hrb
theorem kz369 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {k:ℝ} (hk:0 < k) {ξ:ℂ} (hg:kz215 f k ξ) {h:ℝ} (hh:0 < h) :
    let critical:={z | z ∈ kz145 ∧ kz204 f k z = ξ ∧
      ENNReal.ofReal h ≤ kz214 f k ξ z}
    critical.Finite ∧ ({z ∈ critical | 0 < kz205 f k z}).ncard ≤
      ({z ∈ critical | kz205 f k z < 0}).ncard:=by
  classical
  let u:=kz351 f k ξ
  let r:=(h⁻¹)^2
  have hr:0 < r:=sq_pos_of_pos (inv_pos.mpr hh)
  have hd:0 < r+1:=by linarith
  have hfinite:=kz366 hf hk.le hg hd
  let s:=hfinite.toFinset.image u
  obtain ⟨c,hrc,hcd,hcs⟩:=kz368 s r (r+1) (by linarith)
  have hcmem (z) (hz:z ∈ kz145) (hG:kz204 f k z = ξ)
      (hu:u z ≤ r+1):u z ∈ s :=
    Finset.mem_image.mpr ⟨z,hfinite.mem_toFinset.mpr ⟨hz,hG,hu⟩,rfl⟩
  have hcut (z) (hz:z ∈ kz145) (hG:kz204 f k z = ξ):u z < c ↔ u z ≤ r:=by
    constructor
    · intro huc
      by_contra hn
      have hru:r < u z:=lt_of_not_ge hn
      exact (hcs (u z) (hcmem z hz hG (huc.trans hcd).le) hru).not_gt huc
    · exact fun h => h.trans_lt hrc
  have hreg (z) (hz:z ∈ kz145) (huc:u z = c):kz247 f k ξ z ≠ 0:=by
    intro hzero
    rcases (kz248 (ne_of_gt hk) hz).mp hzero with hp | hG
    · have huz:u z = 0:=by simp [u,kz351,hp]
      linarith
    · have hmem:=hcmem z hz hG (huc.le.trans hcd.le)
      have hcc:=hcs (u z) hmem (hrc.trans_eq huc.symm)
      linarith
  have hc:=kz365 hf hk hg (hr.trans hrc) hreg
  have he:{z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ ENNReal.ofReal h ≤ kz214 f k ξ z} =
      {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ u z < c}:=by
    ext z
    constructor
    · rintro ⟨hz,hG,hV⟩
      exact ⟨hz,hG,(hcut z hz hG).mpr ((kz367 hk.le hh hz).mp hV)⟩
    · rintro ⟨hz,hG,hu⟩
      exact ⟨hz,hG,(kz367 hk.le hh hz).mpr ((hcut z hz hG).mp hu)⟩
  dsimp only
  rw [he]
  exact hc
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
instance diskClassSecondCountable:SecondCountableTopology kz140:=inferInstanceAs (SecondCountableTopology kz137)
lemma kz370:Continuous (fun p:kz140 × kz145 => deriv (kz183 p.1) p.2):=by
  simpa only [iteratedDeriv_one] using kz191 1
lemma kz371 :
    Continuous (fun p:kz140 × kz145 => deriv (deriv (kz183 p.1)) p.2):=by
  simpa only [show 2 = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using kz191 2
lemma kz372 (k:ℝ) :
    Continuous (fun p:kz140 × kz145 => kz204 (kz183 p.1) k p.2):=by
  exact kz187.sub ((continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_subtype_val.comp continuous_snd)))).mul kz370)
lemma kz373 (k:ℝ) :
    Continuous (fun p:kz140 × kz145 => fderiv ℝ (kz204 (kz183 p.1) k) p.2):=by
  let A:ℂ →L[ℝ] ℂ:=1
  let B:ℂ →L[ℝ] ℂ:=Complex.ofRealCLM.comp Complex.imCLM
  have he (p:kz140 × kz145):fderiv ℝ (kz204 (kz183 p.1) k) p.2 =
      deriv (kz183 p.1) p.2 • A -
      (Complex.I / (k:ℂ) * (p.2.val.im:ℂ) * deriv (deriv (kz183 p.1)) p.2) • A -
      (Complex.I / (k:ℂ) * deriv (kz183 p.1) p.2) • B:=by
    ext v
    rw [kz206 (kz184 p.1).1 p.2.property]
    change _ = deriv (kz183 p.1) p.2 * v -
      (Complex.I / (k:ℂ) * (p.2.val.im:ℂ) * deriv (deriv (kz183 p.1)) p.2) * v -
      (Complex.I / (k:ℂ) * deriv (kz183 p.1) p.2) * (v.im:ℂ)
    ring
  simp_rw [he]
  have hy:Continuous (fun p:kz140 × kz145 => (p.2.val.im:ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd))
  exact ((kz370.smul continuous_const).sub
    (((continuous_const.mul hy).mul kz371).smul continuous_const)).sub
    ((continuous_const.mul kz370).smul continuous_const)
lemma kz374 (k:ℝ) :
    Continuous (fun p:kz140 × kz145 => kz205 (kz183 p.1) k p.2):=by
  apply (ContinuousLinearMap.continuous_det.comp (kz373 k)).div
    (kz370.norm.pow 2)
  intro p
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr
    (kz91 kz146 (kz184 p.1).1 p.2.property))
def kz375 (f:ℂ → ℂ) (k:ℝ) (z:ℂ):ℝ :=
  k * z.im^(k-1) * ‖kz160 f z‖
lemma kz376 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {z:ℂ} (hz:z ∈ kz145):0 < kz375 f k z:=by
  exact mul_pos (mul_pos hk (Real.rpow_pos_of_pos hz _))
    (norm_pos_iff.mpr (inv_ne_zero (kz91 kz146 hf hz)))
lemma kz377 (k:ℝ) :
    Continuous (fun p:kz140 × kz145 => kz375 (kz183 p.1) k p.2):=by
  have hy:Continuous (fun p:kz140 × kz145 => p.2.val.im^(k-1)) :=
    (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd)).rpow_const
      (fun p => Or.inl (ne_of_gt p.2.property))
  have hh:Continuous (fun p:kz140 × kz145 =>
      k * p.2.val.im^(k-1) * ‖deriv (kz183 p.1) p.2‖⁻¹) :=
    (continuous_const.mul hy).mul (kz370.norm.inv₀
      (fun p => norm_ne_zero_iff.mpr (kz91 kz146
        (kz184 p.1).1 p.2.property)))
  exact hh.congr (fun p => by simp only [kz375,kz160,norm_inv])
lemma continuousOn_prod_of_continuous_subtype.{u_1,u_2,u_3} {P:Type u_1} {X:Type u_2} {Y:Type u_3}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    {s:Set X} {F:P → X → Y}
    (hF:Continuous (fun q:P × s => F q.1 q.2)) :
    ContinuousOn (fun q:P × X => F q.1 q.2) (univ ×ˢ s):=by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact hF.comp (continuous_subtype_val.fst.prodMk
    (continuous_subtype_val.snd.subtype_mk (fun q => q.property.2)))
lemma kz378 {f g:ℂ → ℂ} (he:EqOn f g kz145) (k:ℝ) :
    EqOn (kz204 f k) (kz204 g k) kz145:=by
  intro z hz
  rw [kz204,kz204,he hz,he.deriv kz146 hz]
lemma kz379 {f g:ℂ → ℂ} (he:EqOn f g kz145) (k:ℝ) :
    EqOn (kz205 f k) (kz205 g k) kz145:=by
  intro z hz
  have hG:kz204 f k =ᶠ[𝓝 z] kz204 g k:=by
    filter_upwards [kz146.mem_nhds hz] with w hw
    exact kz378 he k hw
  rw [kz205,kz205,hG.fderiv_eq,he.deriv kz146 hz]
lemma kz380 {f g:ℂ → ℂ} (he:EqOn f g kz145) (k:ℝ) :
    EqOn (kz375 f k) (kz375 g k) kz145:=by
  intro z hz
  rw [kz375,kz375,kz160,kz160,he.deriv kz146 hz]
lemma kz381 {f g:ℂ → ℂ} (he:EqOn f g kz145) (k:ℝ) (ξ:ℂ) :
    kz215 f k ξ ↔ kz215 g k ξ:=by
  have hs (δ:ℝ):{z | z ∈ kz145 ∧ ENNReal.ofReal δ ≤ kz214 f k ξ z} =
      {z | z ∈ kz145 ∧ ENNReal.ofReal δ ≤ kz214 g k ξ z}:=by
    ext z
    by_cases hz:z ∈ kz145
    · simp only [mem_ofPred_eq,hz,true_and,kz214,he hz]
    · simp only [mem_ofPred_eq,hz,false_and]
  simp only [kz215,hs]
  apply and_congr_right
  intro _
  constructor <;> intro h z hz hG
  · rw [← kz379 he k hz]
    exact h z hz ((kz378 he k hz).trans hG)
  · rw [kz379 he k hz]
    exact h z hz ((kz378 he k hz).symm.trans hG)
def kz382 (t:ℂ) (ht:t ∈ kz145):ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (t.im:ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))).trans
    (Homeomorph.addLeft (t.re:ℂ))
lemma kz383 (t:ℂ) (ht:t ∈ kz145) (z:ℂ) :
    kz382 t ht z = kz148 t z:=rfl
lemma kz384 {t:ℂ} (ht:t ∈ kz145) (z:ℂ) :
    kz148 t z ∈ kz145 ↔ z ∈ kz145:=by
  change 0 < (kz148 t z).im ↔ 0 < z.im
  simp only [kz148,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
    zero_mul,zero_add,add_zero]
  exact mul_pos_iff_of_pos_left ht
def kz385 (f:ℂ → ℂ) (t ξ:ℂ):ℂ :=
  (ξ-f t)/((t.im:ℂ)*deriv f t)
def kz386 (f:ℂ → ℂ) (k:ℝ) (t:ℂ):ℝ :=
  t.im^(k-1) / ‖deriv f t‖
lemma kz387 {f:ℂ → ℂ} (hf:kz1 f kz145) (k:ℝ)
    {t:ℂ} (ht:t ∈ kz145):0 < kz386 f k t :=
  div_pos (Real.rpow_pos_of_pos ht _) (norm_pos_iff.mpr (kz91 kz146 hf ht))
lemma kz388 {f:ℂ → ℂ} (hf:kz1 f kz145) (k:ℝ)
    {t z:ℂ} (ht:t ∈ kz145) (hz:z ∈ kz145) (ξ:ℂ) :
    kz241 (kz155 f t) k (kz385 f t ξ) z =
      kz386 f k t * kz241 f k ξ (kz148 t z):=by
  have he:kz155 f t z-kz385 f t ξ =
      (f (kz148 t z)-ξ)/((t.im:ℂ)*deriv f t):=by
    simp only [kz155,kz385,← sub_div]
    congr 1
    ring
  have hn:‖deriv f t‖ ≠ 0:=norm_ne_zero_iff.mpr (kz91 kz146 hf ht)
  have hpow:z.im^k ≠ 0:=ne_of_gt (Real.rpow_pos_of_pos hz k)
  have him:(kz148 t z).im = t.im*z.im:=by simp [kz148]
  rw [kz241,he,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,
    kz241,him,Real.mul_rpow ht.le hz.le,kz386,Real.rpow_sub_one (ne_of_gt ht)]
  have htp:t.im^k ≠ 0:=ne_of_gt (Real.rpow_pos_of_pos ht _)
  field_simp
lemma kz389 {f:ℂ → ℂ} (hf:kz1 f kz145) (k:ℝ)
    {t z:ℂ} (ht:t ∈ kz145) (hz:z ∈ kz145) :
    kz375 (kz155 f t) k z = kz375 f k (kz148 t z) / kz386 f k t:=by
  have him:(kz148 t z).im = t.im*z.im:=by simp [kz148]
  have hn:‖deriv f t‖ ≠ 0:=norm_ne_zero_iff.mpr (kz91 kz146 hf ht)
  have hp:t.im^(k-1) ≠ 0:=ne_of_gt (Real.rpow_pos_of_pos ht _)
  rw [kz375,kz161 hf ht hz,norm_div,kz375,him,
    Real.mul_rpow ht.le hz.le,kz386]
  simp only [kz160,norm_inv]
  field_simp
lemma kz390 {f:ℂ → ℂ} (hf:kz1 f kz145) (k:ℝ)
    {t z:ℂ} (ht:t ∈ kz145) (hz:z ∈ kz145) (ξ:ℂ) :
    kz204 (kz155 f t) k z = kz385 f t ξ ↔ kz204 f k (kz148 t z) = ξ:=by
  rw [kz212 hf ht hz,kz385,div_left_inj' (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ht)) (kz91 kz146 hf ht)),sub_left_inj]
lemma kz391 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 ≤ k)
    {t:ℂ} (ht:t ∈ kz145) (ξ:ℂ) {δ:ℝ} (hδ:0 < δ) :
    {z | z ∈ kz145 ∧ ENNReal.ofReal δ ≤ kz214 (kz155 f t) k (kz385 f t ξ) z} =
      (kz382 t ht) ⁻¹' {w | w ∈ kz145 ∧
        ENNReal.ofReal (δ*kz386 f k t) ≤ kz214 f k ξ w}:=by
  have hc:=kz387 hf k ht
  ext z
  simp only [mem_ofPred_eq,mem_preimage,kz383,kz384 ht]
  apply and_congr_right
  intro hz
  rw [kz354 hk hδ hz,
    kz354 hk (mul_pos hδ hc) (kz152 ht hz),
    kz388 hf k ht hz ξ,mul_inv_rev]
  rw [mul_comm,← le_div_iff₀ hc,div_eq_mul_inv]
  rw [mul_comm δ⁻¹]
lemma kz392 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {t:ℂ} (ht:t ∈ kz145) (ξ:ℂ) :
    kz215 (kz155 f t) k (kz385 f t ξ) ↔ kz215 f k ξ:=by
  have hc:=kz387 hf k ht
  constructor
  · rintro ⟨hcompact,hregular⟩
    constructor
    · intro δ hδ
      have h:=hcompact (δ/kz386 f k t) (div_pos hδ hc)
      rw [kz391 hf hk.le ht ξ (div_pos hδ hc),div_mul_cancel₀ _ (ne_of_gt hc)] at h
      exact (kz382 t ht).isCompact_preimage.mp h
    · intro w hw hG
      let z:=(kz382 t ht).symm w
      have he:kz148 t z = w:=(kz382 t ht).apply_symm_apply w
      have hz:z ∈ kz145:=(kz384 ht z).mp (he.symm ▸ hw)
      have hr:=hregular z hz ((kz390 hf k ht hz ξ).mpr (he.symm ▸ hG))
      rwa [kz213 hf ht hz k (ne_of_gt hk),he] at hr
  · rintro ⟨hcompact,hregular⟩
    constructor
    · intro δ hδ
      rw [kz391 hf hk.le ht ξ hδ]
      exact (kz382 t ht).isCompact_preimage.mpr (hcompact _ (mul_pos hδ hc))
    · intro z hz hG
      rw [kz213 hf ht hz k (ne_of_gt hk)]
      exact hregular _ (kz152 ht hz) ((kz390 hf k ht hz ξ).mp hG)
def orderRank.{u_1} {α:Type u_1} [LinearOrder α] (S:Set α) (x:α):ℕ:=(S ∩ Iio x).ncard
lemma orderRank_strictMonoOn.{u_1} {α:Type u_1} [LinearOrder α] {S:Set α}
    (hfin:∀ x ∈ S,(S ∩ Iio x).Finite):StrictMonoOn (orderRank S) S:=by
  intro x hx y hy hxy
  apply Set.ncard_lt_ncard _ (hfin y hy)
  refine ssubset_iff_subset_ne.mpr ⟨?_,?_⟩
  · exact fun a ha => ⟨ha.1,ha.2.trans hxy⟩
  · intro he
    have:x ∈ S ∩ Iio x:=he ▸ (show x ∈ S ∩ Iio y from ⟨hx,hxy⟩)
    exact lt_irrefl x this.2
lemma orderRank_injOn.{u_1} {α:Type u_1} [LinearOrder α] {S:Set α}
    (hfin:∀ x ∈ S,(S ∩ Iio x).Finite):InjOn (orderRank S) S :=
  (orderRank_strictMonoOn hfin).injOn
lemma orderRank_finset_enum.{u_1} {α:Type u_1} [LinearOrder α] (s:Finset α)
    (j:Fin s.card):orderRank (s:Set α) (s.orderEmbOfFin rfl j) = j.val:=by
  classical
  let e:=s.orderEmbOfFin rfl
  have he:(s:Set α) ∩ Iio (e j) = e '' Iio j:=by
    ext a
    constructor
    · intro ha
      obtain ⟨i,rfl⟩:=(s.range_orderEmbOfFin rfl).symm ▸ ha.1
      exact ⟨i,e.lt_iff_lt.mp ha.2,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨s.orderEmbOfFin_mem rfl i,e.strictMono hi⟩
  rw [orderRank,he,Set.ncard_image_of_injective _ e.injective]
  rw [← Finset.coe_Iio,Set.ncard_coe_finset,Fin.card_Iio]
lemma exists_orderRank_of_finite_initial.{u_1} {α:Type u_1} [LinearOrder α]
    {S A:Set α} (hA:A.Finite) (hAS:A ⊆ S)
    (hinit:∀ x ∈ A,∀ y ∈ S,y < x → y ∈ A)
    {j:ℕ} (hj:j < A.ncard):∃ x ∈ A,orderRank S x = j:=by
  classical
  let s:=hA.toFinset
  have hscard:s.card = A.ncard:=(Set.ncard_eq_toFinset_card A hA).symm
  let x:α:=s.orderEmbOfFin rfl ⟨j,by simpa [hscard] using hj⟩
  have hx:x ∈ A:=hA.mem_toFinset.mp (s.orderEmbOfFin_mem rfl ⟨j,by simpa [hscard] using hj⟩)
  refine ⟨x,hx,?_⟩
  have he:S ∩ Iio x = A ∩ Iio x:=by
    ext y
    exact ⟨fun hy => ⟨hinit x hx y hy.1 hy.2,hy.2⟩,fun hy => ⟨hAS hy.1,hy.2⟩⟩
  calc
    orderRank S x = orderRank A x:=congrArg Set.ncard he
    _ = j:=by simpa only [s,Set.Finite.coe_toFinset] using
      orderRank_finset_enum s ⟨j,by simpa [hscard] using hj⟩
def kz393 (H:ℂ → ℝ) (z:ℂ):Lex (ℝ × Lex (ℝ × ℝ)) :=
  toLex (-H z,toLex (z.re,z.im))
lemma kz394 (H:ℂ → ℝ):Injective (kz393 H):=by
  intro z w he
  have he':=congrArg (fun a:Lex (ℝ × Lex (ℝ × ℝ)) => ofLex ((ofLex a).2)) he
  exact Complex.ext (congrArg Prod.fst he') (congrArg Prod.snd he')
abbrev kz395 (H:ℂ → ℝ):LinearOrder ℂ:=LinearOrder.lift' (kz393 H) (kz394 H)
def kz396 (H:ℂ → ℝ) (S:Set ℂ) (z:ℂ):ℕ:=@orderRank ℂ (kz395 H) S z
def kz397 (H:ℂ → ℝ) (z w:ℂ):Prop :=
  H w < H z ∨ H z = H w ∧ (z.re < w.re ∨ z.re = w.re ∧ z.im < w.im)
lemma kz398 (H:ℂ → ℝ) (z w:ℂ) :
    @LT.lt ℂ (kz395 H).toLT z w ↔ kz397 H z w:=by
  change kz393 H z < kz393 H w ↔ _
  simp only [kz393,Prod.Lex.toLex_lt_toLex,neg_lt_neg_iff,neg_inj,kz397]
lemma kz399 {H:ℂ → ℝ} {z w:ℂ}
    (h : @LT.lt ℂ (kz395 H).toLT z w):H w ≤ H z:=by
  rcases (kz398 H z w).mp h with h | ⟨h,_⟩
  · exact h.le
  · exact h.ge
lemma kz400 {H:ℂ → ℝ} {S:Set ℂ} {z:ℂ}
    (hfin:(S ∩ {w | H z ≤ H w}).Finite) :
    @Set.Finite ℂ (S ∩ @Iio ℂ (kz395 H).toPreorder z):=by
  exact hfin.subset (fun w hw => ⟨hw.1,kz399 hw.2⟩)
lemma kz401 {H:ℂ → ℝ} {S:Set ℂ} {z:ℂ} (hz:z ∈ S)
    (hfin:(S ∩ {w | H z ≤ H w}).Finite) :
    kz396 H S z < (S ∩ {w | H z ≤ H w}).ncard:=by
  let _:=kz395 H
  apply Set.ncard_lt_ncard _ hfin
  refine ssubset_iff_subset_ne.mpr ⟨fun w hw => ⟨hw.1,kz399 hw.2⟩,?_⟩
  intro he
  have:z ∈ S ∩ Iio z:=he ▸ (show z ∈ S ∩ {w | H z ≤ H w} from ⟨hz,show H z ≤ H z from le_refl _⟩)
  exact lt_irrefl z this.2
lemma kz402 {H:ℂ → ℝ} {A B:Set ℂ} {z:ℂ}
    (hz:z ∈ A) (hAf:(A ∩ {w | H z ≤ H w}).Finite)
    (hBf:(B ∩ {w | H z ≤ H w}).Finite)
    (hc:(A ∩ {w | H z ≤ H w}).ncard ≤ (B ∩ {w | H z ≤ H w}).ncard) :
    ∃ w ∈ B,H z ≤ H w ∧ kz396 H B w = kz396 H A z:=by
  let _:=kz395 H
  have hj:=(kz401 hz hAf).trans_le hc
  obtain ⟨w,hw,hr⟩:=exists_orderRank_of_finite_initial hBf inter_subset_left
    (fun x hx y hy hyx => ⟨hy,hx.2.trans (kz399 hyx)⟩) hj
  exact ⟨w,hw.1,hw.2,hr⟩
lemma kz403 {H:ℂ → ℝ} {S:Set ℂ}
    (hfin:∀ z ∈ S,(S ∩ {w | H z ≤ H w}).Finite):InjOn (kz396 H S) S :=
  @orderRank_injOn ℂ (kz395 H) S (fun z hz => kz400 (hfin z hz))
lemma kz404 (H:ℂ → ℝ) (S:Set ℂ) (z:ℂ) :
    kz396 H S z = {w | w ∈ S ∧ kz397 H w z}.ncard:=by
  let:=kz395 H
  rw [kz396,orderRank]
  congr 1
  ext w
  exact and_congr_right (fun _ => kz398 H w z)
def kz405 (H:ℂ → ℝ) (A B:Set ℂ) (z:ℂ):ℂ :=
  if h:∃ w ∈ B,kz396 H B w = kz396 H A z then h.choose else z
lemma kz406 {H:ℂ → ℝ} {A B:Set ℂ} {z:ℂ}
    (h:∃ w ∈ B,kz396 H B w = kz396 H A z) :
    kz405 H A B z ∈ B ∧
      kz396 H B (kz405 H A B z) = kz396 H A z:=by
  rw [kz405,dif_pos h]
  exact h.choose_spec
lemma kz407 {H:ℂ → ℝ} {A B:Set ℂ} {z w:ℂ}
    (hri:InjOn (kz396 H B) B) (hw:w ∈ B)
    (hr:kz396 H B w = kz396 H A z):kz405 H A B z = w:=by
  have hs:=kz406 ⟨w,hw,hr⟩
  exact hri hs.1 hw (hs.2.trans hr.symm)
def kz408 (f:ℂ → ℂ) (k:ℝ) (ξ:ℂ):Set ℂ :=
  {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ 0 < kz205 f k z}
def kz409 (f:ℂ → ℂ) (k:ℝ) (ξ:ℂ):Set ℂ :=
  {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ kz205 f k z < 0}
lemma kz410 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {ξ:ℂ} (hg:kz215 f k ξ) {h:ℝ} (hh:0 < h) :
    (kz408 f k ξ ∩ {z | h ≤ kz375 f k z}).Finite ∧
    (kz409 f k ξ ∩ {z | h ≤ kz375 f k z}).Finite ∧
    (kz408 f k ξ ∩ {z | h ≤ kz375 f k z}).ncard ≤
      (kz409 f k ξ ∩ {z | h ≤ kz375 f k z}).ncard:=by
  have he:{z | z ∈ kz145 ∧ kz204 f k z = ξ ∧
      ENNReal.ofReal h ≤ kz214 f k ξ z} =
      {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ h ≤ kz375 f k z}:=by
    ext z
    constructor
    · rintro ⟨hz,hG,hv⟩
      refine ⟨hz,hG,?_⟩
      rw [kz236 hf hk hz hG] at hv
      exact (ENNReal.ofReal_le_ofReal_iff (kz376 hf hk hz).le).mp hv
    · rintro ⟨hz,hG,hv⟩
      refine ⟨hz,hG,?_⟩
      rw [kz236 hf hk hz hG]
      exact ENNReal.ofReal_le_ofReal hv
  have hc:=kz369 hf hk hg hh
  dsimp only at hc
  rw [he] at hc
  have hp:{z ∈ {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ h ≤ kz375 f k z} |
      0 < kz205 f k z} = kz408 f k ξ ∩ {z | h ≤ kz375 f k z}:=by
    ext z
    simp only [mem_ofPred_eq,mem_inter_iff,kz408]
    tauto
  have hn:{z ∈ {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ h ≤ kz375 f k z} |
      kz205 f k z < 0} = kz409 f k ξ ∩ {z | h ≤ kz375 f k z}:=by
    ext z
    simp only [mem_ofPred_eq,mem_inter_iff,kz409]
    tauto
  refine ⟨hc.1.subset (fun z hz => ⟨hz.1.1,hz.1.2.1,hz.2⟩),
    hc.1.subset (fun z hz => ⟨hz.1.1,hz.1.2.1,hz.2⟩),?_⟩
  rw [hp,hn] at hc
  exact hc.2
lemma kz411 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {ξ:ℂ} (hg:kz215 f k ξ) :
    InjOn (kz396 (kz375 f k) (kz408 f k ξ)) (kz408 f k ξ) ∧
    InjOn (kz396 (kz375 f k) (kz409 f k ξ)) (kz409 f k ξ):=by
  constructor
  · exact kz403 (fun z hz =>
      (kz410 hf hk hg (kz376 hf hk hz.1)).1)
  · exact kz403 (fun z hz =>
      (kz410 hf hk hg (kz376 hf hk hz.1)).2.1)
lemma kz412 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {ξ:ℂ} (hg:kz215 f k ξ) {z:ℂ} (hz:z ∈ kz408 f k ξ) :
    ∃ w ∈ kz409 f k ξ,kz375 f k z ≤ kz375 f k w ∧
      kz396 (kz375 f k) (kz409 f k ξ) w =
        kz396 (kz375 f k) (kz408 f k ξ) z:=by
  have hc:=kz410 hf hk hg (kz376 hf hk hz.1)
  exact kz402 hz hc.1 hc.2.1 hc.2.2
def kz413 (f:ℂ → ℂ) (k:ℝ) (z:ℂ):ℂ :=
  kz405 (kz375 f k) (kz408 f k (kz204 f k z))
    (kz409 f k (kz204 f k z)) z
lemma kz414 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {z:ℂ} (hz:z ∈ kz145) (hJ:0 < kz205 f k z)
    (hg:kz215 f k (kz204 f k z)) :
    kz413 f k z ∈ kz145 ∧ kz204 f k (kz413 f k z) = kz204 f k z ∧
      kz205 f k (kz413 f k z) < 0 ∧
      kz375 f k z ≤ kz375 f k (kz413 f k z):=by
  obtain ⟨w,hw,hh,hr⟩:=kz412 hf hk hg ⟨hz,rfl,hJ⟩
  have he:kz413 f k z = w:=kz407 (kz411 hf hk hg).2 hw hr
  rw [he]
  exact ⟨hw.1,hw.2.1,hw.2.2,hh⟩
lemma kz415 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k) :
    InjOn (kz413 f k) {z | z ∈ kz145 ∧ 0 < kz205 f k z ∧
      kz215 f k (kz204 f k z)}:=by
  intro z hz w hw he
  have hsz:=kz414 hf hk hz.1 hz.2.1 hz.2.2
  have hsw:=kz414 hf hk hw.1 hw.2.1 hw.2.2
  have hG:kz204 f k z = kz204 f k w:=by rw [← hsz.2.1,he,hsw.2.1]
  have hri:=(kz411 hf hk hz.2.2).1
  have hze:=kz412 hf hk hz.2.2 (show z ∈ kz408 f k (kz204 f k z) from ⟨hz.1,rfl,hz.2.1⟩)
  have hwe:=kz412 hf hk hz.2.2 (show w ∈ kz408 f k (kz204 f k z) from ⟨hw.1,hG.symm,hw.2.1⟩)
  have hzr:=kz406 (show ∃ v ∈ kz409 f k (kz204 f k z),
      kz396 (kz375 f k) (kz409 f k (kz204 f k z)) v =
        kz396 (kz375 f k) (kz408 f k (kz204 f k z)) z from by
    obtain ⟨v,hv,_,hr⟩:=hze; exact ⟨v,hv,hr⟩)
  have hwr:=kz406 (show ∃ v ∈ kz409 f k (kz204 f k z),
      kz396 (kz375 f k) (kz409 f k (kz204 f k z)) v =
        kz396 (kz375 f k) (kz408 f k (kz204 f k z)) w from by
    obtain ⟨v,hv,_,hr⟩:=hwe; exact ⟨v,hv,hr⟩)
  apply hri ⟨hz.1,rfl,hz.2.1⟩ ⟨hw.1,hG.symm,hw.2.1⟩
  rw [← hzr.2,← hwr.2]
  apply congrArg
  simpa only [kz413,← hG] using he
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
lemma joint_locally_injective.{u_1} {P:Type u_1} [TopologicalSpace P]
    {F:P → ℂ → ℂ} {DF:P → ℂ → ℂ →L[ℝ] ℂ} {s:Set ℂ}
    (hs:IsOpen s) (hder:∀ p z,z ∈ s → HasFDerivAt (F p) (DF p z) z)
    (hc:ContinuousOn (fun q:P × ℂ => DF q.1 q.2) (univ ×ˢ s))
    {p:P} {z:ℂ} (hz:z ∈ s) (he:LinearMap.det (DF p z).toLinearMap ≠ 0) :
    ∃ U:Set (P × ℂ),IsOpen U ∧ (p,z) ∈ U ∧
      InjOn (fun q:P × ℂ => (q.1,F q.1 q.2)) U:=by
  let e:ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr he)).toContinuousLinearEquiv
  have heq:(e:ℂ →L[ℝ] ℂ) = DF p z:=by
    ext v
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr he) v
  let c:ℝ≥0:=‖(e.symm:ℂ →L[ℝ] ℂ)‖₊⁻¹ / 2
  have hn:0 < ‖(e.symm:ℂ →L[ℝ] ℂ)‖₊:=by exact_mod_cast e.symm.norm_pos
  have hcpos:0 < c:=by dsimp [c]; positivity
  have hclt:c < ‖(e.symm:ℂ →L[ℝ] ℂ)‖₊⁻¹:=by
    dsimp [c]
    exact half_lt_self (inv_pos.mpr hn)
  have hcAt:ContinuousAt (fun q:P × ℂ => DF q.1 q.2) (p,z):=hc.continuousAt ((isOpen_univ.prod hs).mem_nhds ⟨mem_univ p,hz⟩)
  have hnb:{q:P × ℂ | q.2 ∈ s ∧ ‖DF q.1 q.2-(e:ℂ →L[ℝ] ℂ)‖₊ < c} ∈ 𝓝 (p,z):=by
    apply Filter.inter_mem
    · exact continuous_snd.continuousAt.preimage_mem_nhds (hs.mem_nhds hz)
    · exact ((hcAt.sub continuousAt_const).nnnorm).eventually
        (gt_mem_nhds (by simpa only [Pi.sub_apply,heq,sub_self,nnnorm_zero] using hcpos))
  obtain ⟨u,hu,v,hv,huv⟩:=mem_nhds_prod_iff.mp hnb
  obtain ⟨u',hu'u,hu'o,hpu⟩:=mem_nhds_iff.mp hu
  obtain ⟨r,hr,hvr⟩:=Metric.mem_nhds_iff.mp hv
  refine ⟨u' ×ˢ Metric.ball z r,hu'o.prod Metric.isOpen_ball,⟨hpu,Metric.mem_ball_self hr⟩,?_⟩
  rintro ⟨p1,z1⟩ h1 ⟨p2,z2⟩ h2 hh
  have hp:p1 = p2:=congrArg Prod.fst hh
  subst p2
  have hbound (w:ℂ) (hw:w ∈ Metric.ball z r) :
      w ∈ s ∧ ‖DF p1 w-(e:ℂ →L[ℝ] ℂ)‖₊ < c :=
    huv (show (p1,w) ∈ u ×ˢ v from ⟨hu'u h1.1,hvr hw⟩)
  have hLip:LipschitzOnWith c (fun w => F p1 w-e w) (Metric.ball z r):=by
    apply (convex_ball z r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun w hw => ((hder p1 w (hbound w hw).1).sub e.hasFDerivAt).hasFDerivWithinAt)
    exact fun w hw => (hbound w hw).2.le
  have hInj:=hLip.approximatesLinearOn.injOn (Or.inr hclt)
  exact Prod.ext rfl (hInj h1.2 h2.2 (congrArg Prod.snd hh))
lemma countable_joint_injective_partition.{u_1} {P:Type u_1} [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P]
    {F:P → ℂ → ℂ} {DF:P → ℂ → ℂ →L[ℝ] ℂ} {s:Set ℂ}
    (hs:IsOpen s) (hder:∀ p z,z ∈ s → HasFDerivAt (F p) (DF p z) z)
    (hc:ContinuousOn (fun q:P × ℂ => DF q.1 q.2) (univ ×ˢ s)) :
    ∃ p:ℕ → Set (P × ℂ),(∀ n,MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧
      (⋃ n,p n) = {q | q.2 ∈ s ∧ LinearMap.det (DF q.1 q.2).toLinearMap ≠ 0} ∧
      ∀ n,InjOn (fun q:P × ℂ => (q.1,F q.1 q.2)) (p n):=by
  classical
  let t:Set (P × ℂ):={q | q.2 ∈ s ∧ LinearMap.det (DF q.1 q.2).toLinearMap ≠ 0}
  have htopen:IsOpen t:=by
    have h:IsOpen ((univ ×ˢ s) ∩ (fun q:P × ℂ => DF q.1 q.2) ⁻¹' {d | d.det ≠ 0}) :=
      hc.isOpen_inter_preimage (isOpen_univ.prod hs)
        (isClosed_eq ContinuousLinearMap.continuous_det continuous_const).isOpen_compl
    convert h using 1
    ext q
    simp [t]
  have hlocal (q:t):∃ U:Set (P × ℂ),IsOpen U ∧ q.val ∈ U ∧
      InjOn (fun q:P × ℂ => (q.1,F q.1 q.2)) U :=
    joint_locally_injective hs hder hc q.property.1 q.property.2
  choose U hUo hUq hUi using hlocal
  by_cases he:t = ∅
  · refine ⟨fun _ => ∅,by simp,by simp [Pairwise],?_,by simp⟩
    simpa using he.symm
  · have:Nonempty t:=Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j,hj⟩:=(show IsLindelof t from HereditarilyLindelofSpace.isLindelof t).indexed_countable_subcover
      U hUo (fun q hq => mem_iUnion.mpr ⟨⟨q,hq⟩,hUq ⟨q,hq⟩⟩)
    let q:ℕ → Set (P × ℂ):=fun n => t ∩ U (j n)
    refine ⟨disjointed q,?_,disjoint_disjointed q,?_,?_⟩
    · intro n
      exact MeasurableSet.disjointed (fun n => htopen.measurableSet.inter (hUo (j n)).measurableSet) n
    · rw [iUnion_disjointed]
      ext z
      simp only [mem_iUnion,mem_inter_iff,q]
      exact ⟨fun ⟨_,hz,_⟩ => hz,fun hz => by obtain ⟨n,hn⟩:=mem_iUnion.mp (hj hz); exact ⟨n,hz,hn⟩⟩
    · intro n
      exact (hUi (j n)).mono ((disjointed_subset q n).trans inter_subset_right)
lemma exists_borel_partial_inverse.{u_1,u_2} {X:Type u_1} {Y:Type u_2}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f:X → Y} {s:Set X} (hs:MeasurableSet s) (hf:ContinuousOn f s) (hi:InjOn f s) :
    ∃ b:Y → X,Measurable b ∧ MeasurableSet (f '' s) ∧
      (∀ y ∈ f '' s,b y ∈ s ∧ f (b y) = y) ∧ ∀ x ∈ s,b (f x) = x:=by
  classical
  have hm:=hf.measurableEmbedding hs hi
  by_cases hne:s.Nonempty
  · let:Nonempty s:=Set.nonempty_coe_sort.mpr hne
    let b:Y → X:=fun y => (hm.invFun y).val
    refine ⟨b,measurable_subtype_coe.comp hm.measurable_invFun,?_,?_,?_⟩
    · simpa only [Set.range_domRestrict] using hm.measurableSet_range
    · rintro y ⟨x,hx,rfl⟩
      have hb:b (f x) = x:=congrArg Subtype.val (hm.leftInverse_invFun ⟨x,hx⟩)
      exact ⟨hb.symm ▸ hx,congrArg f hb⟩
    · intro x hx
      exact congrArg Subtype.val (hm.leftInverse_invFun ⟨x,hx⟩)
  · have he:s = ∅:=not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => Classical.arbitrary X,measurable_const,?_,?_,?_⟩ <;> simp [he]
lemma fiber_count_eq_tsum_branches.{u_1,u_2} {X:Type u_1} {Y:Type u_2} [MeasurableSpace X] [MeasurableSingletonClass X]
    {f:X → Y} {s:Set X} {p:ℕ → Set X} {b:ℕ → Y → X}
    (hp:Pairwise (Disjoint on p)) (hu:(⋃ n,p n) = s)
    (hi:∀ n,InjOn f (p n))
    (hb:∀ n y,y ∈ f '' p n → b n y ∈ p n ∧ f (b n y) = y)
    (hinv:∀ n x,x ∈ p n → b n (f x) = x)
    (R:X → Prop) (y:Y) :
    Measure.count {x | x ∈ s ∧ f x = y ∧ R x} =
      ∑' n,if y ∈ f '' p n ∧ R (b n y) then (1:ℝ≥0∞) else 0:=by
  classical
  have he:{x | x ∈ s ∧ f x = y ∧ R x} = ⋃ n,{x | x ∈ p n ∧ f x = y ∧ R x}:=by
    rw [← hu]
    ext x
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  have hsub (n):({x | x ∈ p n ∧ f x = y ∧ R x}:Set X).Subsingleton:=by
    intro x hx z hz
    exact hi n hx.1 hz.1 (hx.2.1.trans hz.2.1.symm)
  rw [he,measure_iUnion]
  · apply tsum_congr
    intro n
    by_cases hy:y ∈ f '' p n ∧ R (b n y)
    · rw [if_pos hy]
      have hx:{x | x ∈ p n ∧ f x = y ∧ R x} = {b n y}:=by
        apply Set.Subsingleton.eq_singleton_of_mem (hsub n)
        exact ⟨(hb n y hy.1).1,(hb n y hy.1).2,hy.2⟩
      rw [hx,Measure.count_singleton]
    · rw [if_neg hy]
      have hx:{x | x ∈ p n ∧ f x = y ∧ R x} = ∅:=by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hy
        refine ⟨⟨x,hx.1,hx.2.1⟩,?_⟩
        rw [← hx.2.1,hinv n x hx.1]
        exact hx.2.2
      rw [hx,measure_empty]
  · exact pairwise_disjoint_mono hp (fun n => fun x hx => hx.1)
  · intro n
    exact (hsub n).countable.measurableSet
lemma measurable_fiber_count_branches.{u_1,u_2,u_3} {X:Type u_1} {Y:Type u_2} {Q:Type u_3}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSpace Q]
    {f:X → Y} {s:Set X} {p:ℕ → Set X} {b:ℕ → Y → X}
    (hp:Pairwise (Disjoint on p)) (hu:(⋃ n,p n) = s)
    (hi:∀ n,InjOn f (p n)) (hbm:∀ n,Measurable (b n))
    (hdm:∀ n,MeasurableSet (f '' p n))
    (hb:∀ n y,y ∈ f '' p n → b n y ∈ p n ∧ f (b n y) = y)
    (hinv:∀ n x,x ∈ p n → b n (f x) = x)
    {R:Q → X → Prop} (hR:MeasurableSet {q:Q × X | R q.1 q.2})
    {y:Q → Y} (hy:Measurable y) :
    Measurable (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}):=by
  classical
  have he:(fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) =
      fun q => ∑' n,if y q ∈ f '' p n ∧ R q (b n (y q)) then (1:ℝ≥0∞) else 0:=by
    funext q
    exact fiber_count_eq_tsum_branches hp hu hi hb hinv (R q) (y q)
  rw [he]
  apply Measurable.tsum
  intro n
  apply Measurable.ite
  · exact (hdm n |>.preimage hy).inter
      (hR.preimage (measurable_id.prodMk ((hbm n).comp hy)))
  · exact measurable_const
  · exact measurable_const
lemma measurable_branch_selection.{u_1,u_2} {Q:Type u_1} {X:Type u_2} [MeasurableSpace Q] [MeasurableSpace X]
    {b:ℕ → Q → X} {M:ℕ → Set Q} {f:Q → X}
    (hb:∀ n,Measurable (b n)) (hM:∀ n,MeasurableSet (M n))
    (he:∀ q,∃ n,q ∈ M n) (hf:∀ n q,q ∈ M n → f q = b n q):Measurable f:=by
  intro T hT
  have hset:f ⁻¹' T = ⋃ n,M n ∩ (b n) ⁻¹' T:=by
    ext q
    constructor
    · intro hq
      obtain ⟨n,hn⟩:=he q
      exact mem_iUnion.mpr ⟨n,hn,by simpa only [mem_preimage,← hf n q hn] using hq⟩
    · intro hq
      obtain ⟨n,hn,ht⟩:=mem_iUnion.mp hq
      simpa only [mem_preimage,hf n q hn] using ht
  rw [hset]
  exact MeasurableSet.iUnion (fun n => (hM n).inter (hT.preimage (hb n)))
structure BorelBranches.{u_1,u_2} {X:Type u_1} {Y:Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    (f:X → Y) (s:Set X) where
  part:ℕ → Set X
  branch:ℕ → Y → X
  measurable_part:∀ n,MeasurableSet (part n)
  disjoint:Pairwise (Disjoint on part)
  cover:(⋃ n,part n) = s
  injective:∀ n,InjOn f (part n)
  measurable_branch:∀ n,Measurable (branch n)
  measurable_image:∀ n,MeasurableSet (f '' part n)
  right_inv:∀ n y,y ∈ f '' part n → branch n y ∈ part n ∧ f (branch n y) = y
  left_inv:∀ n x,x ∈ part n → branch n (f x) = x
lemma exists_borelBranches.{u_1,u_2} {X:Type u_1} {Y:Type u_2}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f:X → Y} {s:Set X} (hf:ContinuousOn f s)
    (hp:∃ p:ℕ → Set X,(∀ n,MeasurableSet (p n)) ∧ Pairwise (Disjoint on p) ∧
      (⋃ n,p n) = s ∧ ∀ n,InjOn f (p n)):Nonempty (BorelBranches f s):=by
  obtain ⟨p,hpm,hpd,hpc,hpi⟩:=hp
  have hb (n):=exists_borel_partial_inverse (hpm n)
    (hf.mono (show p n ⊆ s from hpc ▸ subset_iUnion p n)) (hpi n)
  choose b hbm him hbr hbl using hb
  exact ⟨⟨p,b,hpm,hpd,hpc,hpi,hbm,him,hbr,hbl⟩⟩
lemma BorelBranches.measurable_count.{u_1,u_2,u_3} {X:Type u_1} {Y:Type u_2} {Q:Type u_3}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSpace Q]
    {f:X → Y} {s:Set X} (B:BorelBranches f s)
    {R:Q → X → Prop} (hR:MeasurableSet {q:Q × X | R q.1 q.2})
    {y:Q → Y} (hy:Measurable y) :
    Measurable (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) :=
  measurable_fiber_count_branches B.disjoint B.cover B.injective B.measurable_branch
    B.measurable_image B.right_inv B.left_inv hR hy
lemma count_product_fiber.{u_1,u_2,u_3} {P:Type u_1} {X:Type u_2} {Y:Type u_3} [MeasurableSpace P] [MeasurableSingletonClass P]
    [MeasurableSpace X] [MeasurableSingletonClass X] (F:P → X → Y)
    (R:P × X → Prop) (p:P) (y:Y) :
    Measure.count {q:P × X | (q.1,F q.1 q.2) = (p,y) ∧ R q} =
      Measure.count {x | F p x = y ∧ R (p,x)}:=by
  have he:{q:P × X | (q.1,F q.1 q.2) = (p,y) ∧ R q} =
      (fun x => (p,x)) '' {x | F p x = y ∧ R (p,x)}:=by
    ext q
    constructor
    · rintro ⟨hq,hR⟩
      obtain rfl:q.1 = p:=congrArg Prod.fst hq
      exact ⟨q.2,⟨congrArg Prod.snd hq,hR⟩,rfl⟩
    · rintro ⟨x,⟨hx,hR⟩,rfl⟩
      exact ⟨Prod.ext rfl hx,hR⟩
  rw [he]
  exact Measure.count_injective_image (fun _ _ h => congrArg Prod.snd h) _
lemma count_subtype_set.{u_1} {X:Type u_1} [MeasurableSpace X] [MeasurableSingletonClass X]
    (s:Set X) (R:X → Prop) :
    Measure.count {x:s | R x} = Measure.count {x:X | x ∈ s ∧ R x}:=by
  rw [← Measure.count_injective_image (f:=(Subtype.val:s → X)) Subtype.val_injective]
  congr 1
  ext x
  simp only [mem_image,mem_ofPred_eq,Subtype.exists,exists_prop]
  aesop
instance:PolishSpace kz140:=by
  let:=TopologicalSpace.metrizableSpaceMetric kz140
  infer_instance
instance:PolishSpace kz145:=kz146.polishSpace
instance:Nonempty kz145:=⟨⟨Complex.I,by simp [kz145]⟩⟩
def kz416 (z:ℂ):ℂ:=z-Complex.I
lemma kz417:kz147 kz416:=by
  refine ⟨⟨(differentiable_id.sub_const Complex.I).differentiableOn,?_⟩,by simp [kz416],?_⟩
  · exact (sub_left_injective).injOn
  · exact (hasDerivAt_id Complex.I |>.sub_const Complex.I).deriv
def kz418:kz140:=kz185 kz416 kz417
instance:Nonempty kz140:=⟨kz418⟩
def kz419 (k:ℝ) (q:kz140 × kz145):kz140 × ℂ :=
  (q.1,kz204 (kz183 q.1) k q.2)
def kz420 (k:ℝ):Set (kz140 × kz145) :=
  {q | kz205 (kz183 q.1) k q.2 ≠ 0}
lemma kz421 (k:ℝ):Continuous (kz419 k) :=
  continuous_fst.prodMk (kz372 k)
lemma kz422 (k:ℝ):Nonempty (BorelBranches (kz419 k) (kz420 k)):=by
  apply exists_borelBranches (kz421 k).continuousOn
  obtain ⟨p,hpm,hpd,hpc,hpi⟩:=countable_joint_injective_partition kz146
    (fun g z hz => (kz216 (kz184 g).1 hz k).hasFDerivAt)
    (continuousOn_prod_of_continuous_subtype (F:=fun g z => fderiv ℝ (kz204 (kz183 g) k) z) (kz373 k))
  let e:kz140 × kz145 → kz140 × ℂ:=fun q => (q.1,q.2)
  have hem:Measurable e:=measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  let u:ℕ → Set (kz140 × kz145):=fun n => e ⁻¹' p n
  refine ⟨u,fun n => (hpm n).preimage hem,?_,?_,?_⟩
  · intro n m hnm
    exact (hpd hnm).preimage e
  · ext q
    have hc:(∃ n,e q ∈ p n) ↔ (e q).2 ∈ kz145 ∧
        LinearMap.det (fderiv ℝ (kz204 (kz183 q.1) k) q.2).toLinearMap ≠ 0:=by
      rw [← mem_iUnion,hpc]
      rfl
    simp only [mem_iUnion,mem_preimage,u]
    rw [hc]
    simp only [e,q.2.property,true_and,kz420,mem_ofPred_eq,kz205]
    exact ((div_ne_zero_iff).trans (and_iff_left
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (kz91 kz146
        (kz184 q.1).1 q.2.property))))).symm
  · intro n q hq r hr he
    have hz:e q = e r:=hpi n hq hr he
    have hfst:q.1 = r.1:=congrArg (fun x:kz140 × ℂ => x.1) hz
    have hsnd:q.2.val = r.2.val:=congrArg (fun x:kz140 × ℂ => x.2) hz
    exact Prod.ext hfst (Subtype.ext hsnd)
def kz423 (k:ℝ) (q r:kz140 × kz145):Prop :=
  kz375 (kz183 r.1) k r.2 < kz375 (kz183 q.1) k q.2 ∨
  kz375 (kz183 q.1) k q.2 = kz375 (kz183 r.1) k r.2 ∧
    (q.2.val.re < r.2.val.re ∨ q.2.val.re = r.2.val.re ∧ q.2.val.im < r.2.val.im)
lemma kz424 (k:ℝ) :
    MeasurableSet {p:(kz140 × kz145) × (kz140 × kz145) | kz423 k p.1 p.2}:=by
  have hH:=(kz377 k).measurable
  have hr:Measurable (fun q:kz140 × kz145 => q.2.val.re) :=
    Complex.continuous_re.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  have hi:Measurable (fun q:kz140 × kz145 => q.2.val.im) :=
    Complex.continuous_im.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  exact (measurableSet_lt (hH.comp measurable_snd) (hH.comp measurable_fst)).union
    ((measurableSet_eq_fun (hH.comp measurable_fst) (hH.comp measurable_snd)).inter
      ((measurableSet_lt (hr.comp measurable_fst) (hr.comp measurable_snd)).union
        ((measurableSet_eq_fun (hr.comp measurable_fst) (hr.comp measurable_snd)).inter
          (measurableSet_lt (hi.comp measurable_fst) (hi.comp measurable_snd)))))
def kz425 (k σ:ℝ) (q:kz140 × kz145):ℝ≥0∞ :=
  Measure.count {r | r ∈ kz420 k ∧ kz419 k r = kz419 k q ∧
    0 < σ * kz205 (kz183 r.1) k r.2 ∧ kz423 k r q}
lemma kz426 (k σ:ℝ):Measurable (kz425 k σ):=by
  let B:=Classical.choice (kz422 k)
  apply B.measurable_count _ (kz421 k).measurable
  exact (measurableSet_lt measurable_const
    (measurable_const.mul ((kz374 k).measurable.comp measurable_snd))).inter
    ((kz424 k).preimage measurable_swap)
def kz427 (f:ℂ → ℂ) (k:ℝ) (ξ:ℂ) (σ:ℝ):Set ℂ :=
  {z | z ∈ kz145 ∧ kz204 f k z = ξ ∧ 0 < σ * kz205 f k z}
lemma kz428 (f:ℂ → ℂ) (k:ℝ) (ξ:ℂ) :
    kz427 f k ξ 1 = kz408 f k ξ:=by ext z; simp [kz427,kz408]
lemma kz429 (f:ℂ → ℂ) (k:ℝ) (ξ:ℂ) :
    kz427 f k ξ (-1) = kz409 f k ξ:=by ext z; simp [kz427,kz409]
lemma kz430 (k σ:ℝ) (q:kz140 × kz145) :
    kz425 k σ q = Measure.count {w | w ∈ kz427 (kz183 q.1) k
      (kz204 (kz183 q.1) k q.2) σ ∧ kz397 (kz375 (kz183 q.1) k) w q.2}:=by
  let R:kz140 × kz145 → Prop:=fun r =>
    0 < σ * kz205 (kz183 r.1) k r.2 ∧ kz423 k r q
  have he:{r | r ∈ kz420 k ∧ kz419 k r = kz419 k q ∧ R r} =
      {r:kz140 × kz145 | kz419 k r = kz419 k q ∧ R r}:=by
    ext r
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_,h⟩
      intro hz
      have hp:=h.2.1
      rw [hz,mul_zero] at hp
      exact lt_irrefl 0 hp
  change Measure.count {r | r ∈ kz420 k ∧ kz419 k r = kz419 k q ∧ R r} = _
  rw [he]
  simp only [kz419]
  rw [count_product_fiber (fun g (z:kz145) => kz204 (kz183 g) k z) R]
  change Measure.count {w:kz145 | kz204 (kz183 q.1) k w = kz204 (kz183 q.1) k q.2 ∧
    0 < σ * kz205 (kz183 q.1) k w ∧ kz397 (kz375 (kz183 q.1) k) w q.2} = _
  rw [count_subtype_set kz145 (fun w:ℂ => kz204 (kz183 q.1) k w = kz204 (kz183 q.1) k q.2 ∧
    0 < σ * kz205 (kz183 q.1) k w ∧ kz397 (kz375 (kz183 q.1) k) w q.2)]
  congr 1
  ext w
  simp only [mem_ofPred_eq,kz427]
  tauto
lemma kz431 {k:ℝ} (hk:0 < k) (σ:ℝ) (q:kz140 × kz145)
    (hg:kz215 (kz183 q.1) k (kz204 (kz183 q.1) k q.2)) :
    kz425 k σ q =
      (kz396 (kz375 (kz183 q.1) k)
        (kz427 (kz183 q.1) k (kz204 (kz183 q.1) k q.2) σ) q.2:ℝ≥0∞):=by
  rw [kz430,kz404]
  have hpos:=kz376 (kz184 q.1).1 hk q.2.property
  have hc:=kz369 (kz184 q.1).1 hk hg hpos
  have hf:{w | w ∈ kz427 (kz183 q.1) k (kz204 (kz183 q.1) k q.2) σ ∧
      kz397 (kz375 (kz183 q.1) k) w q.2}.Finite:=by
    apply hc.1.subset
    intro w hw
    refine ⟨hw.1.1,hw.1.2.1,?_⟩
    rw [kz236 (kz184 q.1).1 hk hw.1.1 hw.1.2.1]
    apply ENNReal.ofReal_le_ofReal
    exact kz399 ((kz398 _ _ _).mpr hw.2)
  rw [Measure.count_apply_finite _ hf,← Set.ncard_eq_toFinset_card _ hf]
lemma kz432 {H H':ℂ → ℝ} {S S':Set ℂ} (e:ℂ ≃ ℂ)
    (hS:∀ w,w ∈ S' ↔ e w ∈ S) (z:ℂ)
    (hord:∀ w ∈ S',kz397 H' w z ↔ kz397 H (e w) (e z)) :
    kz396 H' S' z = kz396 H S (e z):=by
  rw [kz404,kz404]
  apply Set.ncard_congr (fun w _ => e w)
  · intro w hw
    exact ⟨(hS w).mp hw.1,(hord w hw.1).mp hw.2⟩
  · intro a b _ _ hab
    exact e.injective hab
  · intro w hw
    have hm:e.symm w ∈ S':=(hS _).mpr (by simpa using hw.1)
    exact ⟨e.symm w,⟨hm,(hord _ hm).mpr (by simpa using hw.2)⟩,e.apply_symm_apply w⟩
lemma kz433 {f:ℂ → ℂ} (hf:kz1 f kz145) (k:ℝ)
    {t z w:ℂ} (ht:t ∈ kz145) (hz:z ∈ kz145) (hw:w ∈ kz145) :
    kz397 (kz375 (kz155 f t) k) z w ↔
      kz397 (kz375 f k) (kz148 t z) (kz148 t w):=by
  have hc:=kz387 hf k ht
  have hre (v:ℂ):(kz148 t v).re = t.re+t.im*v.re:=by simp [kz148]
  have him (v:ℂ):(kz148 t v).im = t.im*v.im:=by simp [kz148]
  simp only [kz397,kz389 hf k ht hz,kz389 hf k ht hw,
    div_lt_div_iff_of_pos_right hc,div_left_inj' (ne_of_gt hc),hre,him,
    add_lt_add_iff_left,add_right_inj,mul_lt_mul_iff_right₀ (show 0 < t.im from ht),mul_right_inj' (ne_of_gt (show 0 < t.im from ht))]
lemma kz434 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {t:ℂ} (ht:t ∈ kz145) (ξ:ℂ) (σ:ℝ) (w:ℂ) :
    w ∈ kz427 (kz155 f t) k (kz385 f t ξ) σ ↔
      kz148 t w ∈ kz427 f k ξ σ:=by
  simp only [kz427,mem_ofPred_eq,kz384 ht]
  apply and_congr_right
  intro hw
  rw [kz390 hf k ht hw,kz213 hf ht hw k (ne_of_gt hk)]
lemma kz435 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {t z:ℂ} (ht:t ∈ kz145) (hz:z ∈ kz145) (ξ:ℂ) (σ:ℝ) :
    kz396 (kz375 (kz155 f t) k) (kz427 (kz155 f t) k (kz385 f t ξ) σ) z =
      kz396 (kz375 f k) (kz427 f k ξ σ) (kz148 t z):=by
  apply kz432 (kz382 t ht).toEquiv
    (kz434 hf hk ht ξ σ) z
  intro w hw
  exact kz433 hf k ht hw.1 hz
lemma kz436 {f:ℂ → ℂ} (hf:kz1 f kz145) {k:ℝ} (hk:0 < k)
    {t z:ℂ} (ht:t ∈ kz145) (hz:z ∈ kz145)
    (hJ:0 < kz205 f k (kz148 t z))
    (hg:kz215 f k (kz204 f k (kz148 t z))) :
    kz148 t (kz413 (kz155 f t) k z) = kz413 f k (kz148 t z):=by
  let f':=kz155 f t
  have hf':kz1 f' kz145:=(kz158 hf ht).1
  have hG:kz204 f' k z = kz385 f t (kz204 f k (kz148 t z)) :=
    kz212 hf ht hz k
  have hg':kz215 f' k (kz204 f' k z):=by
    rw [hG]
    exact (kz392 hf hk ht _).mpr hg
  have hJ':0 < kz205 f' k z:=by
    rw [kz213 hf ht hz k (ne_of_gt hk)]
    exact hJ
  have hs:=kz414 hf' hk hz hJ' hg'
  have hr:=kz406 (show ∃ w ∈ kz409 f' k (kz204 f' k z),
      kz396 (kz375 f' k) (kz409 f' k (kz204 f' k z)) w =
        kz396 (kz375 f' k) (kz408 f' k (kz204 f' k z)) z from by
    obtain ⟨w,hw,_,he⟩:=kz412 hf' hk hg' ⟨hz,rfl,hJ'⟩
    exact ⟨w,hw,he⟩)
  have hr':kz396 (kz375 f k)
      (kz409 f k (kz204 f k (kz148 t z))) (kz148 t (kz413 f' k z)) =
      kz396 (kz375 f k) (kz408 f k (kz204 f k (kz148 t z))) (kz148 t z):=by
    have h:=hr.2
    change kz396 (kz375 f' k) (kz409 f' k (kz204 f' k z)) (kz413 f' k z) = _ at h
    rw [← kz429,← kz428,hG,
      kz435 hf hk ht hs.1 _ (-1),kz435 hf hk ht hz _ 1,
      kz429,kz428] at h
    exact h
  have hm:kz148 t (kz413 f' k z) ∈ kz409 f k (kz204 f k (kz148 t z)):=by
    rw [← kz429,← kz434 hf hk ht _ (-1),← hG,kz429]
    exact ⟨hs.1,hs.2.1,hs.2.2.1⟩
  exact (kz407 (kz411 hf hk hg).2 hm hr').symm
lemma kz437 {H H':ℂ → ℝ} {S:Set ℂ} (hS:S ⊆ kz145)
    (he:EqOn H H' kz145) {z:ℂ} (hz:z ∈ kz145) :
    kz396 H S z = kz396 H' S z:=by
  rw [kz404,kz404]
  congr 1
  ext w
  apply and_congr_right
  intro hw
  simp only [kz397,he hz,he (hS hw)]
lemma kz438 {f g:ℂ → ℂ} (he:EqOn f g kz145) (k:ℝ) (ξ:ℂ) (σ:ℝ) :
    kz427 f k ξ σ = kz427 g k ξ σ:=by
  ext z
  simp only [kz427,mem_ofPred_eq]
  apply and_congr_right
  intro hz
  rw [kz378 he k hz,kz379 he k hz]
lemma kz439 {f g:ℂ → ℂ} (hf:kz1 f kz145) (hg:kz1 g kz145)
    (he:EqOn f g kz145) {k:ℝ} (hk:0 < k) {z:ℂ} (hz:z ∈ kz145)
    (hJ:0 < kz205 f k z) (hgood:kz215 f k (kz204 f k z)) :
    kz413 f k z = kz413 g k z:=by
  have hG:=kz378 he k hz
  have hgood':kz215 g k (kz204 g k z):=by
    rw [← hG]
    exact (kz381 he k _).mp hgood
  have hs:=kz414 hf hk hz hJ hgood
  have hr:=kz406 (show ∃ w ∈ kz409 f k (kz204 f k z),
      kz396 (kz375 f k) (kz409 f k (kz204 f k z)) w =
        kz396 (kz375 f k) (kz408 f k (kz204 f k z)) z from by
    obtain ⟨w,hw,_,hr⟩:=kz412 hf hk hgood ⟨hz,rfl,hJ⟩
    exact ⟨w,hw,hr⟩)
  have hneg:kz409 f k (kz204 f k z) = kz409 g k (kz204 g k z):=by
    rw [← kz429,← kz429,kz438 he,hG]
  have hpos:kz408 f k (kz204 f k z) = kz408 g k (kz204 g k z):=by
    rw [← kz428,← kz428,kz438 he,hG]
  have hr':=hr.2
  change kz396 (kz375 f k) (kz409 f k (kz204 f k z)) (kz413 f k z) = _ at hr'
  rw [kz437 (fun w hw => hw.1) (kz380 he k) hs.1,
    kz437 (fun w hw => hw.1) (kz380 he k) hz,hneg,hpos] at hr'
  exact (kz407 (kz411 hg hk hgood').2 (hneg ▸ hr.1) hr').symm
def kz440:kz145:=⟨Complex.I,by simp [kz145]⟩
lemma kz441 (g:kz140) {k:ℝ} (hk:0 < k)
    (t w:kz145) :
    kz205 (kz183 (kz192 g t)) k w =
      kz205 (kz183 g) k (kz148 t w):=by
  rw [kz379 (kz193 g t) k w.property,
    kz213 (kz184 g).1 t.property w.property k (ne_of_gt hk)]
lemma kz442 (g:kz140) {k:ℝ} (hk:0 < k) (t w:kz145) :
    kz215 (kz183 (kz192 g t)) k
        (kz204 (kz183 (kz192 g t)) k w) ↔
      kz215 (kz183 g) k (kz204 (kz183 g) k (kz148 t w)):=by
  rw [kz378 (kz193 g t) k w.property,
    kz381 (kz193 g t) k,
    kz212 (kz184 g).1 t.property w.property k]
  exact kz392 (kz184 g).1 hk t.property _
lemma kz443 (g:kz140) {k:ℝ} (hk:0 < k) (t w:kz145)
    (hj:0 < kz205 (kz183 g) k (kz148 t w))
    (hg:kz215 (kz183 g) k (kz204 (kz183 g) k (kz148 t w))) :
    kz148 t (kz413 (kz183 (kz192 g t)) k w) =
      kz413 (kz183 g) k (kz148 t w):=by
  have hj':0 < kz205 (kz183 (kz192 g t)) k w:=by
    rw [kz441 g hk t w]; exact hj
  have hg':=(kz442 g hk t w).mpr hg
  rw [kz439 (kz184 (kz192 g t)).1
      (kz158 (kz184 g).1 t.property).1
      (kz193 g t) hk w.property hj' hg']
  exact kz436 (kz184 g).1 hk t.property w.property hj hg
lemma kz444 (g:kz140) {k:ℝ} (hk:0 < k) (z:kz145) :
    kz205 (kz183 (kz192 g z)) k Complex.I =
      kz205 (kz183 g) k z:=by
  simpa only [kz440,kz149] using kz441 g hk z kz440
lemma kz445 (g:kz140) {k:ℝ} (hk:0 < k) (z:kz145) :
    kz215 (kz183 (kz192 g z)) k
        (kz204 (kz183 (kz192 g z)) k Complex.I) ↔
      kz215 (kz183 g) k (kz204 (kz183 g) k z):=by
  simpa only [kz440,kz149] using kz442 g hk z kz440
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def fiberSum.{u_1,u_2} {X:Type u_1} {Y:Type u_2} (f:X → Y) (s:Set X) (u:X → ℝ≥0∞) (y:Y):ℝ≥0∞ :=
  ∑' x:{x | x ∈ s ∧ f x = y},u x
lemma BorelBranches.fiberSum_eq.{u_1,u_2} {X:Type u_1} {Y:Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    {f:X → Y} {s:Set X} (B:BorelBranches f s) (u:X → ℝ≥0∞) (y:Y) :
    fiberSum f s u y = ∑' n,(f '' B.part n).indicator (fun y => u (B.branch n y)) y:=by
  classical
  have he:{x | x ∈ s ∧ f x = y} = ⋃ n,{x | x ∈ B.part n ∧ f x = y}:=by
    ext x
    simp only [mem_ofPred_eq]
    rw [show x ∈ s ↔ x ∈ ⋃ n,B.part n from by rw [B.cover]]
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  rw [fiberSum,he,ENNReal.tsum_biUnion]
  · apply tsum_congr
    intro n
    by_cases hy:y ∈ f '' B.part n
    · have hx:{x | x ∈ B.part n ∧ f x = y} = {B.branch n y}:=by
        ext x
        constructor
        · intro hx
          exact mem_singleton_iff.mpr (B.injective n hx.1 (B.right_inv n y hy).1
            (hx.2.trans (B.right_inv n y hy).2.symm))
        · rintro rfl
          exact B.right_inv n y hy
      rw [hx,tsum_singleton,indicator_of_mem hy]
    · have hx:{x | x ∈ B.part n ∧ f x = y} = ∅:=by
        exact eq_empty_iff_forall_notMem.mpr (fun x hx => hy ⟨x,hx.1,hx.2⟩)
      simp [hx,hy]
  · intro n _ m _ hnm
    exact (B.disjoint hnm).mono (fun _ h => h.1) (fun _ h => h.1)
lemma BorelBranches.measurable_fiberSum.{u_1,u_2} {X:Type u_1} {Y:Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    {f:X → Y} {s:Set X} (B:BorelBranches f s) {u:X → ℝ≥0∞} (hu:Measurable u) :
    Measurable (fiberSum f s u):=by
  have he:=funext (B.fiberSum_eq u)
  rw [he]
  exact Measurable.tsum (fun n => (hu.comp (B.measurable_branch n)).indicator (B.measurable_image n))
lemma kz446 {f:ℂ → ℂ} {s:Set ℂ}
    (hs:MeasurableSet s) (hf:∀ z ∈ s,ContDiffAt ℝ 1 f z)
    (hreg:∀ z ∈ s,LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0)
    {u:ℂ → ℝ≥0∞} (hu:Measurable u) :
    Measurable (fiberSum f s u) ∧
    (∫⁻ z in s,ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z) =
      ∫⁻ y,fiberSum f s u y:=by
  let B:=Classical.choice (exists_borelBranches
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (kz62 hs hf hreg))
  have hsub (n:ℕ):B.part n ⊆ s:=fun z hz => by rw [← B.cover]; exact mem_iUnion.mpr ⟨n,hz⟩
  have hder (n:ℕ) (z:ℂ) (hz:z ∈ B.part n) :
      HasFDerivWithinAt f (fderiv ℝ f z) (B.part n) z :=
    ((hf z (hsub n hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  refine ⟨B.measurable_fiberSum hu,?_⟩
  calc
    (∫⁻ z in s,ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z) =
        ∑' n,∫⁻ z in B.part n,ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z:=by
      conv_lhs => rw [← B.cover]
      exact lintegral_iUnion B.measurable_part B.disjoint _
    _ = ∑' n,∫⁻ y in f '' B.part n,u (B.branch n y):=by
      apply tsum_congr
      intro n
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (B.measurable_part n) (hder n) (B.injective n)]
      apply setLIntegral_congr_fun (B.measurable_part n)
      intro z hz
      dsimp only
      rw [B.left_inv n z hz]
    _ = ∫⁻ y,fiberSum f s u y:=by
      rw [funext (B.fiberSum_eq u),lintegral_tsum]
      · exact tsum_congr (fun n => (lintegral_indicator (B.measurable_image n) _).symm)
      · exact fun n => ((hu.comp (B.measurable_branch n)).indicator (B.measurable_image n)).aemeasurable
lemma fiberSum_mono_injective.{u_1,u_2} {X:Type u_1} {Y:Type u_2} {f:X → Y} {s t:Set X} {u v:X → ℝ≥0∞}
    (R:X → X) (y:Y)
    (hR:∀ x ∈ s,f x = y → R x ∈ t ∧ f (R x) = y)
    (hinj:InjOn R {x | x ∈ s ∧ f x = y})
    (hle:∀ x ∈ s,f x = y → u x ≤ v (R x)) :
    fiberSum f s u y ≤ fiberSum f t v y:=by
  let e:{x | x ∈ s ∧ f x = y} → {x | x ∈ t ∧ f x = y}:=fun x =>
    ⟨R x,hR x x.property.1 x.property.2⟩
  have hi:Injective e:=fun a b h => Subtype.ext
    (hinj a.property b.property (congrArg Subtype.val h))
  exact ENNReal.summable.tsum_le_tsum_of_inj e hi (fun _ _ => zero_le)
    (fun x => hle x x.property.1 x.property.2) ENNReal.summable
lemma kz447 {f:ℂ → ℂ} (hf:kz1 f kz145)
    {z:ℂ} (hz:z ∈ kz145) (k:ℝ):ContDiffAt ℝ 1 (kz204 f k) z:=by
  have han:AnalyticAt ℂ f z:=hf.1.analyticOnNhd kz146 z hz
  have hc:ContDiffAt ℝ 1 (fun w:ℂ => (w.im:ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z Complex.imCLM.contDiff.contDiffAt
  exact (han.contDiffAt.restrict_scalars ℝ).sub
    ((contDiffAt_const.mul hc).mul (han.deriv.contDiffAt.restrict_scalars ℝ))
lemma kz448 (P:ℂ → Prop)
    (hP:MeasurableSet {z:kz145 | P z}) :
    MeasurableSet {z:ℂ | z ∈ kz145 ∧ P z}:=by
  have h:=kz146.measurableSet.subtype_image hP
  convert h using 1
  ext z
  simp only [mem_ofPred_eq,mem_image,Subtype.exists,exists_prop]
  aesop
def kz449 (g:kz140) (k σ:ℝ):Set ℂ :=
  {z | z ∈ kz145 ∧ 0 < σ * kz205 (kz183 g) k z}
lemma kz450 (g:kz140) (k σ:ℝ) :
    MeasurableSet (kz449 g k σ):=by
  apply kz448
  exact measurableSet_lt measurable_const
    (measurable_const.mul (((kz374 k).comp
      (continuous_const.prodMk continuous_id)).measurable))
lemma kz451 (g:kz140) (k σ:ℝ) {z:ℂ}
    (hz:z ∈ kz449 g k σ) :
    LinearMap.det (fderiv ℝ (kz204 (kz183 g) k) z).toLinearMap ≠ 0:=by
  intro hzero
  have h:=hz.2
  simp only [kz205,hzero,zero_div,mul_zero] at h
  exact lt_irrefl 0 h
def kz452 (g:kz140) (β:ℝ) (z:ℂ):ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1)*‖kz160 (kz183 g) z‖^2)
def kz453 (g:kz140) (β:ℝ):ℂ → ℝ≥0∞ :=
  kz145.indicator (fun z => ENNReal.ofReal (z.im^(β-1)*‖kz160 (kz183 g) z‖^4))
seal kz198
lemma kz454 (g:kz140) (β:ℝ):Measurable (kz453 g β):=by
  have hc:ContinuousOn (fun z:ℂ => ENNReal.ofReal (z.im^(β-1)*‖kz160 (kz183 g) z‖^4)) kz145:=by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hm:Continuous (fun z:kz145 => (g,z)):=continuous_const.prodMk continuous_id
    have hq:Continuous (fun z:kz145 => kz198 g z):=kz200.comp hm
    have hp:Continuous (fun z:kz145 => z.val.im^(β-1)) :=
      (Complex.continuous_im.comp continuous_subtype_val).rpow_const (fun z => Or.inl (ne_of_gt z.property))
    convert ENNReal.continuous_ofReal.comp (hp.mul (hq.pow 2)) using 1
    funext z
    simp only [domRestrict_apply,Function.comp_apply,Pi.mul_apply,Pi.pow_apply,kz198,← pow_mul]
  exact hc.measurable_piecewise continuousOn_const kz146.measurableSet
lemma kz455 (g:kz140) (β k σ:ℝ) (hσ:|σ| = 1)
    {z:ℂ} (hz:z ∈ kz449 g k σ) :
    kz452 g β z * ENNReal.ofReal (σ * kz205 (kz183 g) k z) =
      ENNReal.ofReal |LinearMap.det (fderiv ℝ (kz204 (kz183 g) k) z).toLinearMap| * kz453 g β z:=by
  have hD:0 < ‖deriv (kz183 g) z‖:=norm_pos_iff.mpr
    (kz91 kz146 (kz184 g).1 hz.1)
  have habs:|kz205 (kz183 g) k z| = σ * kz205 (kz183 g) k z:=by
    rw [← one_mul |kz205 (kz183 g) k z|,← hσ,← abs_mul,abs_of_pos hz.2]
  have hdet:|LinearMap.det (fderiv ℝ (kz204 (kz183 g) k) z).toLinearMap| =
      ‖deriv (kz183 g) z‖^2 * (σ * kz205 (kz183 g) k z):=by
    rw [← habs,kz205,abs_div,abs_pow,abs_norm]
    field_simp
  rw [kz452,kz453,indicator_of_mem hz.1,hdet]
  simp only [kz160,norm_inv]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _)),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hz.2.le)]
  congr 1
  field_simp
lemma kz456 (g:kz140) (β k σ:ℝ) (hσ:|σ| = 1)
    {h:ℂ → ℝ≥0∞} (hm:Measurable h) :
    (∫⁻ z in kz145,kz452 g β z *
      ENNReal.ofReal (σ * kz205 (kz183 g) k z) * h z) =
    ∫⁻ ξ,fiberSum (kz204 (kz183 g) k) (kz449 g k σ)
      (fun z => kz453 g β z*h z) ξ:=by
  have hs:=kz450 g k σ
  have he:=(kz446 hs
    (fun z hz => kz447 (kz184 g).1 hz.1 k)
    (fun z hz => kz451 g k σ hz)
    ((kz454 g β).mul hm)).2
  refine Eq.trans ?_ he
  have hzero:(fun z => kz452 g β z *
      ENNReal.ofReal (σ * kz205 (kz183 g) k z) * h z) =ᶠ[ae (volume.restrict kz145)]
      (kz449 g k σ).indicator (fun z => kz452 g β z *
        ENNReal.ofReal (σ * kz205 (kz183 g) k z) * h z):=by
    filter_upwards [ae_restrict_mem kz146.measurableSet] with z hz
    by_cases hj:0 < σ * kz205 (kz183 g) k z
    · rw [indicator_of_mem (show z ∈ kz449 g k σ from ⟨hz,hj⟩)]
    · rw [indicator_of_notMem (show z ∉ kz449 g k σ from fun h => hj h.2),
        ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hj),mul_zero,zero_mul]
  rw [lintegral_congr_ae hzero,lintegral_indicator hs,Measure.restrict_restrict hs]
  have hinter:kz449 g k σ ∩ kz145 = kz449 g k σ :=
    inter_eq_left.mpr (fun z hz => hz.1)
  rw [hinter]
  apply setLIntegral_congr_fun hs
  intro z hz
  dsimp only
  rw [kz455 g β k σ hσ hz,mul_assoc]
  rfl
lemma kz457 (g:kz140) {β k:ℝ} (hk:0 < k)
    (hb:β-1 = 4*(k-1)) {z:ℂ} (hz:z ∈ kz145) :
    kz453 g β z = ENNReal.ofReal ((kz375 (kz183 g) k z/k)^4):=by
  rw [kz453,indicator_of_mem hz,kz375,hb,mul_comm (4:ℝ),Real.rpow_mul hz.le]
  congr 1
  simp only [Real.rpow_ofNat]
  field_simp
lemma kz458 (g:kz140) {β k:ℝ} (hk:0 < k)
    (hb:β-1 = 4*(k-1)) {z:ℂ} (hz:z ∈ kz145)
    (hJ:0 < kz205 (kz183 g) k z)
    (hg:kz215 (kz183 g) k (kz204 (kz183 g) k z)) :
    kz453 g β z ≤ kz453 g β (kz413 (kz183 g) k z):=by
  have hs:=kz414 (kz184 g).1 hk hz hJ hg
  rw [kz457 g hk hb hz,kz457 g hk hb hs.1]
  apply ENNReal.ofReal_le_ofReal
  gcongr
  · exact div_nonneg (kz376 (kz184 g).1 hk hz).le hk.le
  · exact hs.2.2.2
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
def kz459:Set ℂ:={z | z ∈ kz145 ∧ (1/2:ℝ) ≤ ‖kz162 z‖}
lemma kz460:Measurable kz162 :=
  (measurable_id.sub_const _).div (measurable_id.add_const _)
lemma kz461:MeasurableSet kz459 :=
  kz146.measurableSet.inter (measurableSet_le measurable_const kz460.norm)
lemma kz462 (g:kz140) {z:ℂ} (hz:z ∈ kz459) :
    (1/16:ℝ) ≤ ‖kz183 g z‖:=by
  have hl:=kz132 g.2 (kz166 hz.1)
  have he:‖kz183 g z‖ = 2*‖kz135 g.1 (kz162 z)‖:=by
    simp [kz183,kz175]
  rw [he]
  have hm:=hz.2
  linarith
lemma kz463 (g:kz140) {z:ℂ} (hz:z ∈ kz459) :
    kz183 g z ≠ 0:=by
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) (kz462 g hz)))
def kz464 (g:kz140) (z:ℂ):ℂ :=
  by classical exact if z ∈ kz145 then kz183 g z else 0
seal kz183
lemma kz465:Measurable (fun p:kz140 × ℂ => kz464 p.1 p.2):=by
  classical
  let s:Set (kz140 × ℂ):=Prod.snd ⁻¹' kz145
  have hc:Continuous (fun p:s => kz183 p.val.1 p.val.2):=by
    exact kz187.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2)))
  simpa only [kz464,s,Set.mem_preimage,dite_eq_ite] using
    hc.measurable.dite (measurable_const (a:=(0:ℂ)))
      (kz146.measurableSet.preimage measurable_snd)
lemma kz466 (g:kz140) {z:ℂ} (hz:z ∈ kz145) :
    kz464 g z = kz183 g z:=by simp [kz464,hz]
lemma integral_closedBall_translate.{u_1} {E:Type u_1} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f:ℂ → E) (z:ℂ) (r:ℝ) :
    (∫ w in Metric.closedBall (0:ℂ) r,f (w+z)) = ∫ w in Metric.closedBall z r,f w:=by
  have he:(fun w:ℂ => w+z) ⁻¹' Metric.closedBall z r = Metric.closedBall 0 r:=by
    ext w
    simp [Metric.mem_closedBall,dist_eq_norm]
  rw [← he]
  exact (measurePreserving_add_right volume z).setIntegral_preimage_emb
    (Homeomorph.addRight z).measurableEmbedding f _
lemma kz467 (z:ℂ) {r:ℝ} (hr:0 ≤ r) :
    volume.real (Metric.closedBall z r) = Real.pi*r^2:=by
  rw [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp only [ENNReal.coe_toReal,NNReal.coe_real_pi]
  ring
lemma kz468 {f:ℂ → ℂ} {z:ℂ} {R r:ℝ}
    (hf:DifferentiableOn ℂ f (Metric.ball z R)) (hr:0 < r) (hrR:r < R) :
    Real.pi*r^2*‖f z‖^2 ≤ ∫ w in Metric.closedBall z r,‖f w‖^2:=by
  have hfd:DifferentiableOn ℂ (fun w => f (w+z)) (Metric.ball 0 R):=by
    apply hf.comp (differentiable_id.add_const z).differentiableOn
    intro w hw
    simpa [Metric.mem_ball,dist_eq_norm] using hw
  have hh:=kz87 hfd hr hrR
  rw [integral_closedBall_translate (fun w => ‖f w‖^2) z r] at hh
  simpa only [kz467 0 hr.le,zero_add] using hh
lemma kz469 {f:ℂ → ℂ} {z:ℂ} {R r:ℝ}
    (hf:DifferentiableOn ℂ f (Metric.ball z R)) (hr:0 < r) (hrR:r < R) :
    ENNReal.ofReal (Real.pi*r^2*‖f z‖^2) ≤
      ∫⁻ w in Metric.closedBall z r,ENNReal.ofReal (‖f w‖^2):=by
  have hi:IntegrableOn (fun w => ‖f w‖^2) (Metric.closedBall z r) volume:=((hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)).norm.pow 2).integrableOn_compact
    (isCompact_closedBall z r)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (kz468 hf hr hrR)
lemma kz470 (s:Set ℂ) (b:ℂ → ℝ≥0∞)
    (hf:(∫⁻ z in s,b z) < ∞) {ε:ℝ≥0∞} (hε:0 < ε) :
    ∃ K:Set ℂ,IsCompact K ∧ (∫⁻ z in s \ K,b z) < ε:=by
  let ν:=(volume.restrict s).withDensity b
  have:IsFiniteMeasure ν:=isFiniteMeasure_withDensity hf.ne
  obtain ⟨K,hKsub,hK,hKε⟩:=(MeasurableSet.univ (α:=ℂ)).exists_isCompact_sdiff_lt
    (μ:=ν) (measure_ne_top ν univ) hε.ne'
  refine ⟨K,hK,?_⟩
  have he:ν (univ \ K) = ∫⁻ z in s \ K,b z:=by
    dsimp only [ν]
    have heK:(univ \ K:Set ℂ) = Kᶜ:=by ext z; simp
    rw [heK]
    rw [withDensity_apply _ hK.isClosed.measurableSet.compl]
    rw [Measure.restrict_restrict hK.isClosed.measurableSet.compl]
    have hsK:Kᶜ ∩ s = s \ K:=by ext z; simp [and_comm]
    rw [hsK]
  rwa [he] at hKε
lemma kz471 {q:ℂ → ℂ} {s:Set ℂ} {a R₀:ℝ}
    (ha:0 ≤ a) (hR₀:0 ≤ R₀)
    (hs:∀ z:ℂ,0 < z.im → R₀ < ‖z‖ → z ∈ s)
    (hq:∀ z ∈ s,DifferentiableAt ℂ q z)
    (hfin:(∫⁻ z in s,ENNReal.ofReal (z.im^a*‖q z‖^2)) < ∞) :
    ∀ ε:ℝ,0 < ε → ∃ R:ℝ,∀ z:ℂ,0 < z.im → R ≤ ‖z‖ →
      z.im^(a+2)*‖q z‖^2 < ε:=by
  intro ε hε
  let C:ℝ:=16*(2:ℝ)^a/Real.pi
  have hC:0 < C:=by dsimp [C]; positivity
  obtain ⟨K,hK,hKε⟩:=kz470 s
    (fun z => ENNReal.ofReal (z.im^a*‖q z‖^2)) hfin
    (ENNReal.ofReal_pos.mpr (div_pos hε hC))
  obtain ⟨M,hM⟩:=hK.isBounded.subset_closedBall (0:ℂ)
  refine ⟨2*(max R₀ M+1),fun z hy hz => ?_⟩
  have hn:0 < ‖z‖:=by nlinarith [le_max_left R₀ M]
  have hball (w:ℂ) (hw:w ∈ Metric.ball z (z.im/2)) :
      0 < w.im ∧ R₀ < ‖w‖ ∧ w ∉ K:=by
    have hd:‖w-z‖ < z.im/2:=by simpa only [Metric.mem_ball,dist_eq_norm] using hw
    have hi:=Complex.abs_im_le_norm (w-z)
    have him:z.im/2 < w.im:=by
      rw [Complex.sub_im] at hi
      have hl:=neg_le_of_abs_le hi
      linarith
    have himz:z.im ≤ ‖z‖:=(le_abs_self _).trans (Complex.abs_im_le_norm z)
    have hnw:=norm_sub_norm_le z w
    have hdist:‖z-w‖ = ‖w-z‖:=norm_sub_rev z w
    rw [hdist] at hnw
    have hnw':max R₀ M < ‖w‖:=by nlinarith
    refine ⟨by linarith,lt_of_le_of_lt (le_max_left _ _) hnw',?_⟩
    intro hwK
    have hm:=hM hwK
    simp only [Metric.mem_closedBall,dist_zero_right] at hm
    exact (not_lt_of_ge (hm.trans (le_max_right _ _))) hnw'
  have hhol:DifferentiableOn ℂ q (Metric.ball z (z.im/2)):=fun w hw =>
    (hq w (hs w (hball w hw).1 (hball w hw).2.1)).differentiableWithinAt
  have hsmall:Metric.closedBall z (z.im/4) ⊆ Metric.ball z (z.im/2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hsub:Metric.closedBall z (z.im/4) ⊆ s \ K:=by
    intro w hw
    obtain ⟨hwi,hwn,hwK⟩:=hball w (hsmall hw)
    exact ⟨hs w hwi hwn,hwK⟩
  have hmean:=kz469 hhol (by linarith:0 < z.im/4) (by linarith)
  have hcomp (w:ℂ) (hw:w ∈ Metric.closedBall z (z.im/4)) :
      z.im^a*‖q w‖^2 ≤ (2:ℝ)^a*(w.im^a*‖q w‖^2):=by
    have hwi:=(hball w (hsmall hw)).1
    have hd:‖w-z‖ ≤ z.im/4:=by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
    have hi:=Complex.abs_im_le_norm (w-z)
    rw [Complex.sub_im] at hi
    have hl:=neg_le_of_abs_le hi
    have hle:z.im ≤ 2*w.im:=by linarith
    have hh:=Real.rpow_le_rpow hy.le hle ha
    rw [Real.mul_rpow (by norm_num) hwi.le] at hh
    nlinarith [sq_nonneg ‖q w‖]
  have hweighted:ENNReal.ofReal (z.im^a)*(∫⁻ w in Metric.closedBall z (z.im/4),ENNReal.ofReal (‖q w‖^2)) ≤
      ENNReal.ofReal ((2:ℝ)^a)*(∫⁻ w in s \ K,ENNReal.ofReal (w.im^a*‖q w‖^2)):=by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply le_trans ?_ (lintegral_mono_set hsub)
    apply setLIntegral_mono' measurableSet_closedBall
    intro w hw
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    exact ENNReal.ofReal_le_ofReal (hcomp w hw)
  have hineq:ENNReal.ofReal (z.im^(a+2)*‖q z‖^2) ≤
      ENNReal.ofReal C*(∫⁻ w in s \ K,ENNReal.ofReal (w.im^a*‖q w‖^2)):=by
    have hh:=(mul_le_mul' (le_refl (ENNReal.ofReal (z.im^a))) hmean).trans hweighted
    have hmul:ENNReal.ofReal (z.im^a)*ENNReal.ofReal (Real.pi*(z.im/4)^2*‖q z‖^2) =
        ENNReal.ofReal (Real.pi/16)*ENNReal.ofReal (z.im^(a+2)*‖q z‖^2):=by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
        ← ENNReal.ofReal_mul (by positivity),Real.rpow_add hy,Real.rpow_two]
      congr 1
      ring
    rw [hmul] at hh
    apply (ENNReal.mul_le_mul_iff_right (by positivity:ENNReal.ofReal (Real.pi/16) ≠ 0)
      ENNReal.ofReal_ne_top).mp
    have he:ENNReal.ofReal (Real.pi/16)*ENNReal.ofReal C = ENNReal.ofReal ((2:ℝ)^a):=by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp only [C]
      field_simp
    rw [← mul_assoc,he]
    exact hh
  have hh:=hineq.trans_lt ((ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top).mpr hKε)
  have he:ENNReal.ofReal C*ENNReal.ofReal (ε/C) = ENNReal.ofReal ε:=by
    rw [← ENNReal.ofReal_mul hC.le,mul_div_cancel₀ ε (ne_of_gt hC)]
  rw [he] at hh
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hh
def kz472 (F:ℂ → ℂ) (a:ℝ):Prop :=
  ∀ ε:ℝ,0 < ε → ∃ R:ℝ,∀ z:ℂ,0 < z.im → R ≤ ‖z‖ →
    z.im^a*‖F z‖⁻¹^4 < ε
lemma kz473 {F:ℂ → ℂ} {a R₀:ℝ}
    (ha:0 ≤ a) (ht:kz472 F a)
    (hzero:∀ z:ℂ,0 < z.im → R₀ < ‖z‖ → F z ≠ 0)
    (hc:ContinuousOn F {z | 0 < z.im}) {K:Set ℂ} (hK:IsCompact K)
    {η:ℝ} (hη:0 < η):IsCompact ({z:ℂ | η ≤ z.im} ∩ F ⁻¹' K):=by
  obtain ⟨M₀,hM₀⟩:=hK.isBounded.subset_closedBall (0:ℂ)
  let M:=max M₀ 1
  have hM:0 < M:=lt_of_lt_of_le (by norm_num) (le_max_right M₀ 1)
  have hδ:0 < η^a*M⁻¹^4:=mul_pos (Real.rpow_pos_of_pos hη _) (pow_pos (inv_pos.mpr hM) _)
  obtain ⟨R,hR⟩:=ht (η^a*M⁻¹^4) hδ
  have hb:{z:ℂ | η ≤ z.im} ∩ F ⁻¹' K ⊆ Metric.closedBall 0 (max R (R₀+1)):=by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra! hzn
    have hy:0 < z.im:=hη.trans_le hz.1
    have hznR:R ≤ ‖z‖:=(le_max_left _ _).trans hzn.le
    have hzn₀:R₀ < ‖z‖:=by linarith [le_max_right R (R₀+1)]
    have hFn:0 < ‖F z‖:=norm_pos_iff.mpr (hzero z hy hzn₀)
    have hFle:‖F z‖ ≤ M:=by
      have hh:=hM₀ hz.2
      exact (show ‖F z‖ ≤ M₀ by simpa using hh).trans (le_max_left _ _)
    have hpow:M⁻¹^4 ≤ ‖F z‖⁻¹^4 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hM.le) ((inv_le_inv₀ hM hFn).mpr hFle) 4
    have hheight:=Real.rpow_le_rpow hη.le hz.1 ha
    have hle:=mul_le_mul hheight hpow (by positivity) (Real.rpow_nonneg hy.le _)
    exact (not_lt_of_ge hle) (hR z hy hznR)
  apply (isCompact_closedBall (0:ℂ) (max R (R₀+1))).of_isClosed_subset _ hb
  exact (hc.mono (fun z hz => hη.trans_le hz)).preimage_isClosed_of_isClosed
    (isClosed_le continuous_const Complex.continuous_im) hK.isClosed
lemma kz474 {F:ℂ → ℂ} {a R₀:ℝ}
    (ha:0 ≤ a) (ht:kz472 F a)
    (hzero:∀ z:ℂ,0 < z.im → R₀ < ‖z‖ → F z ≠ 0)
    (hc:ContinuousOn F {z | 0 < z.im}) {K:Set ℂ} (hK:IsCompact K) :
    ∃ H:ℝ,0 < H ∧ ∀ z:ℂ,0 < z.im → F z ∈ K → z.im ≤ H:=by
  have hk:=kz473 ha ht hzero hc hK (by norm_num:(0:ℝ) < 1)
  obtain ⟨M,hM⟩:=hk.isBounded.subset_closedBall (0:ℂ)
  refine ⟨max M 1,lt_of_lt_of_le (by norm_num) (le_max_right M 1),fun z _ hz => ?_⟩
  by_cases hy:1 ≤ z.im
  · have hh:‖z‖ ≤ M:=by simpa using hM ⟨hy,hz⟩
    exact ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans (hh.trans (le_max_left _ _))
  · exact (le_of_lt (lt_of_not_ge hy)).trans (le_max_right _ _)
lemma kz475 {F:ℂ → ℂ} {k:ℝ} (ht:kz472 F (4*k)) :
    ∀ ε:ℝ,0 < ε → ∃ R:ℝ,∀ z:ℂ,0 < z.im → R ≤ ‖z‖ →
      z.im^k*‖F z‖⁻¹ < ε:=by
  intro ε hε
  obtain ⟨R,hR⟩:=ht (ε^4) (pow_pos hε _)
  refine ⟨R,fun z hz hzr => ?_⟩
  have hh:=hR z hz hzr
  have he:z.im^(4*k)*‖F z‖⁻¹^4 = (z.im^k*‖F z‖⁻¹)^4:=by
    rw [mul_comm (4:ℝ) k,Real.rpow_mul hz.le,Real.rpow_ofNat,mul_pow]
  rw [he] at hh
  by_contra! hle
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le hle 4)) hh
lemma kz476 {z:ℂ} (hz:z ∈ kz145) (hn:3 < ‖z‖) :
    z ∈ kz459:=by
  refine ⟨hz,?_⟩
  change (1/2:ℝ) ≤ ‖(z-Complex.I)/(z+Complex.I)‖
  rw [norm_div,le_div_iff₀ (norm_pos_iff.mpr (kz164 hz))]
  have h₁:‖z‖ ≤ ‖z-Complex.I‖+1:=by
    simpa only [sub_add_cancel,Complex.norm_I] using norm_add_le (z-Complex.I) Complex.I
  have h₂:‖z+Complex.I‖ ≤ ‖z‖+1:=by
    simpa only [Complex.norm_I] using norm_add_le z Complex.I
  linarith
lemma kz477 (g:kz140) {β:ℝ} (hβ:1 < β)
    (hfin:(∫⁻ z in kz459,
      ENNReal.ofReal (z.im^(β+1)*‖kz183 g z‖⁻¹^4)) < ∞) :
    kz472 (kz183 g) (β+3):=by
  let q:ℂ → ℂ:=fun z => (kz183 g z)⁻¹^2
  have hnorm (z:ℂ):‖q z‖^2 = ‖kz183 g z‖⁻¹^4:=by
    simp only [q,norm_pow,norm_inv,← pow_mul]
  have hhol (z:ℂ) (hz:z ∈ kz459):DifferentiableAt ℂ q z :=
    (((kz184 g).1.1.differentiableAt
      (kz146.mem_nhds hz.1)).inv (kz463 g hz)).pow 2
  have hfq:(∫⁻ z in kz459,ENNReal.ofReal (z.im^(β+1)*‖q z‖^2)) < ∞:=by
    simpa only [hnorm] using hfin
  have hh:=kz471 (by linarith:0 ≤ β+1) (by norm_num:(0:ℝ) ≤ 3)
    (fun z hz hn => kz476 hz hn) hhol hfq
  intro ε hε
  obtain ⟨R,hR⟩:=hh ε hε
  refine ⟨R,fun z hz hzr => ?_⟩
  have he:β+1+2 = β+3:=by ring
  simpa only [he,hnorm] using hR z hz hzr
lemma kz478 (g:kz140) {β:ℝ} (hβ:1 < β)
    (hfin:(∫⁻ z in kz459,
      ENNReal.ofReal (z.im^(β+1)*‖kz183 g z‖⁻¹^4)) < ∞)
    {K:Set ℂ} (hK:IsCompact K) {η:ℝ} (hη:0 < η) :
    IsCompact ({z:ℂ | η ≤ z.im} ∩ kz183 g ⁻¹' K) :=
  kz473 (by linarith:0 ≤ β+3) (kz477 g hβ hfin)
    (fun z hz hn => kz463 g (kz476 hz hn))
    (kz184 g).1.1.continuousOn hK hη
lemma kz479 (g:kz140) {β:ℝ} (hβ:1 < β)
    (hfin:(∫⁻ z in kz459,
      ENNReal.ofReal (z.im^(β+1)*‖kz183 g z‖⁻¹^4)) < ∞)
    {K:Set ℂ} (hK:IsCompact K) :
    ∃ H:ℝ,0 < H ∧ ∀ z:ℂ,0 < z.im → kz183 g z ∈ K → z.im ≤ H :=
  kz474 (by linarith:0 ≤ β+3) (kz477 g hβ hfin)
    (fun z hz hn => kz463 g (kz476 hz hn))
    (kz184 g).1.1.continuousOn hK
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
def kz480 (g:ℝ × ℝ → ℝ) (p:ℝ × ℝ):ℝ :=
  fderiv ℝ (fderiv ℝ g) p (1,0) (1,0) + fderiv ℝ (fderiv ℝ g) p (0,1) (0,1)
def kz481 (g:ℝ × ℝ → ℝ) (ε:ℝ) (p:ℝ × ℝ):ℝ :=
  (p.2-ε)*fderiv ℝ g p (1,0)
def kz482 (g:ℝ × ℝ → ℝ) (ε:ℝ) (p:ℝ × ℝ):ℝ :=
  (p.2-ε)*fderiv ℝ g p (0,1)-g p
lemma kz483 {g:ℝ × ℝ → ℝ} {p:ℝ × ℝ}
    (hg:ContDiffAt ℝ 2 g p) (ε:ℝ) :
    ContDiffAt ℝ 1 (kz481 g ε) p ∧ ContDiffAt ℝ 1 (kz482 g ε) p:=by
  have hd:ContDiffAt ℝ 1 (fderiv ℝ g) p:=hg.fderiv_right (by norm_num)
  have htr:ContDiffAt ℝ 1 g p:=hg.of_le (by norm_num)
  constructor
  · unfold kz481; fun_prop
  · unfold kz482; fun_prop
lemma kz484 {g:ℝ × ℝ → ℝ} {p:ℝ × ℝ}
    (hg:ContDiffAt ℝ 2 g p) (ε:ℝ) :
    fderiv ℝ (kz481 g ε) p (1,0)+fderiv ℝ (kz482 g ε) p (0,1) =
      (p.2-ε)*kz480 g p:=by
  have hdg:=hg.differentiableAt (by norm_num)
  have hddg:=(hg.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hx:=hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((1,0):ℝ × ℝ) p)
  have hy:=hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((0,1):ℝ × ℝ) p)
  have hs:HasFDerivAt (fun p:ℝ × ℝ => p.2-ε) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.sub_const ε
  unfold kz481 kz482
  have hfx:=(hs.mul hx).fderiv
  have hfy:=((hs.mul hy).sub hdg.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => (p.2-ε)*fderiv ℝ g p (1,0)) p = _ at hfx
  change fderiv ℝ (fun p => (p.2-ε)*fderiv ℝ g p (0,1)-g p) p = _ at hfy
  rw [hfx,hfy]
  simp [kz480,ContinuousLinearMap.flip_apply,mul_add]
lemma kz485 {g:ℝ × ℝ → ℝ} {p:ℝ × ℝ}
    (hg:ContDiffAt ℝ 2 g p):ContinuousAt (kz480 g) p:=by
  have hh:ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ g)) p :=
    (hg.fderiv_right (m:=1) (by norm_num)).fderiv_right (by norm_num)
  have hc:=hh.continuousAt
  unfold kz480
  fun_prop
lemma kz486 {g:ℝ × ℝ → ℝ} {R ε Y:ℝ}
    (hR:0 ≤ R) (hεY:ε ≤ Y)
    (hg:∀ p ∈ Icc (-R,ε) (R,Y),ContDiffAt ℝ 2 g p)
    (htop:∀ x ∈ Icc (-R) R,g (x,Y) = 0 ∧ fderiv ℝ g (x,Y) (0,1) = 0)
    (hside:∀ y ∈ Icc ε Y,
      fderiv ℝ g (-R,y) (1,0) = 0 ∧ fderiv ℝ g (R,y) (1,0) = 0) :
    (∫ p in Icc (-R,ε) (R,Y),(p.2-ε)*kz480 g p) =
      ∫ x in -R..R,g (x,ε):=by
  have hf:ContinuousOn (kz481 g ε) (Icc (-R,ε) (R,Y)) :=
    fun p hp => ((kz483 (hg p hp) ε).1.continuousAt).continuousWithinAt
  have hh:ContinuousOn (kz482 g ε) (Icc (-R,ε) (R,Y)) :=
    fun p hp => ((kz483 (hg p hp) ε).2.continuousAt).continuousWithinAt
  have hint:IntegrableOn (fun p:ℝ × ℝ => (p.2-ε)*kz480 g p)
      (Icc (-R,ε) (R,Y)) volume:=by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    have hc:ContinuousAt (fun p:ℝ × ℝ => (p.2-ε)*kz480 g p) p :=
      (continuous_snd.continuousAt.sub_const ε).mul (kz485 (hg p hp))
    exact hc.continuousWithinAt
  have heq (p:ℝ × ℝ) (hp:p ∈ Icc (-R,ε) (R,Y)):=kz484 (hg p hp) ε
  have hi:IntegrableOn (fun p => fderiv ℝ (kz481 g ε) p (1,0)+
      fderiv ℝ (kz482 g ε) p (0,1)) (Icc (-R,ε) (R,Y)) volume :=
    hint.congr (ae_restrict_of_forall_mem measurableSet_Icc (fun p hp => (heq p hp).symm))
  have hb:=integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (kz481 g ε) (kz482 g ε) (fderiv ℝ (kz481 g ε))
    (fderiv ℝ (kz482 g ε)) (-R,ε) (R,Y) ⟨by linarith,hεY⟩ hf hh
    (fun p hp => ((kz483 (hg p ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩) ε).1.differentiableAt (by norm_num)).hasFDerivAt)
    (fun p hp => ((kz483 (hg p ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩) ε).2.differentiableAt (by norm_num)).hasFDerivAt) hi
  rw [setIntegral_congr_fun measurableSet_Icc heq] at hb
  have ht:(∫ x in -R..R,kz482 g ε (x,Y)) = 0:=by
    calc
      _ = ∫ _ in -R..R,(0:ℝ):=?_
      _ = 0:=by simp
    apply intervalIntegral.integral_congr
    intro x hx
    have hx':x ∈ Icc (-R) R:=by simpa only [uIcc_of_le (by linarith : -R ≤ R)] using hx
    simp [kz482,(htop x hx').1,(htop x hx').2]
  have hl:(∫ y in ε..Y,kz481 g ε (-R,y)) = 0:=by
    calc
      _ = ∫ _ in ε..Y,(0:ℝ):=?_
      _ = 0:=by simp
    apply intervalIntegral.integral_congr
    intro y hy
    simp [kz481,(hside y (by simpa only [uIcc_of_le hεY] using hy)).1]
  have hr:(∫ y in ε..Y,kz481 g ε (R,y)) = 0:=by
    calc
      _ = ∫ _ in ε..Y,(0:ℝ):=?_
      _ = 0:=by simp
    apply intervalIntegral.integral_congr
    intro y hy
    simp [kz481,(hside y (by simpa only [uIcc_of_le hεY] using hy)).2]
  change _ = ((∫ x in -R..R,kz482 g ε (x,Y)) - ∫ x in -R..R,kz482 g ε (x,ε)) +
    (∫ y in ε..Y,kz481 g ε (R,y)) - ∫ y in ε..Y,kz481 g ε (-R,y) at hb
  rw [ht,hl,hr] at hb
  simpa only [kz482,sub_self,zero_mul,zero_sub,
    intervalIntegral.integral_neg,sub_neg_eq_add,zero_add,add_zero,sub_zero] using hb
lemma kz487 {g:ℝ × ℝ → ℝ} {ε:ℝ} (hε:0 < ε)
    (hc:∀ p:ℝ × ℝ,0 < p.2 → ContDiffAt ℝ 2 g p)
    {K:Set (ℝ × ℝ)} (hK:IsCompact K)
    (hs:∀ p:ℝ × ℝ,ε/2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    ∃ R:ℝ,0 < R ∧ ε ≤ R ∧ Integrable (fun x:ℝ => g (x,ε)) ∧
      (∫ x:ℝ,g (x,ε)) =
        ∫ p in Icc (-R,ε) (R,R),(p.2-ε)*kz480 g p:=by
  obtain ⟨M,hM⟩:=hK.isBounded.subset_closedBall (0:ℝ × ℝ)
  let R:=max M ε+1
  have hR:0 < R:=by dsimp only [R]; linarith [le_max_right M ε]
  have hεR:ε ≤ R:=by dsimp only [R]; linarith [le_max_right M ε]
  have hMR:M < R:=by dsimp only [R]; linarith [le_max_left M ε]
  have hz (p:ℝ × ℝ) (hy:ε/2 ≤ p.2) (hn:M < ‖p‖):g p = 0:=by
    by_contra hg
    have hh:‖p‖ ≤ M:=by simpa using hM (hs p hy hg)
    exact (not_lt_of_ge hh) hn
  have hznhd (p:ℝ × ℝ) (hy:ε/2 < p.2) (hn:M < ‖p‖) :
      g =ᶠ[𝓝 p] (0:ℝ × ℝ → ℝ):=by
    have hy':{q:ℝ × ℝ | ε/2 < q.2} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_snd).mem_nhds hy
    have hn':{q:ℝ × ℝ | M < ‖q‖} ∈ 𝓝 p :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hn
    filter_upwards [hy',hn'] with q hq₁ hq₂
    exact hz q hq₁.le hq₂
  have hd (p:ℝ × ℝ) (hy:ε/2 < p.2) (hn:M < ‖p‖):fderiv ℝ g p = 0:=by
    rw [(hznhd p hy hn).fderiv_eq,fderiv_zero]
    rfl
  have htop (x:ℝ) (_hx:x ∈ Icc (-R) R) :
      g (x,R) = 0 ∧ fderiv ℝ g (x,R) (0,1) = 0:=by
    have hn:M < ‖(x,R)‖:=hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_of_pos hR] using norm_snd_le (x,R))
    exact ⟨hz (x,R) (by linarith) hn,by rw [hd (x,R) (by linarith) hn]; rfl⟩
  have hside (y:ℝ) (hy:y ∈ Icc ε R) :
      fderiv ℝ g (-R,y) (1,0) = 0 ∧ fderiv ℝ g (R,y) (1,0) = 0:=by
    have h₁:M < ‖(-R,y)‖:=hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_neg,abs_of_pos hR] using norm_fst_le (-R,y))
    have h₂:M < ‖(R,y)‖:=hMR.trans_le (by simpa only [Real.norm_eq_abs,abs_of_pos hR] using norm_fst_le (R,y))
    rw [hd (-R,y) (by linarith [hy.1]) h₁,hd (R,y) (by linarith [hy.1]) h₂]
    simp
  have hbox (p:ℝ × ℝ) (hp:p ∈ Icc (-R,ε) (R,R)):ContDiffAt ℝ 2 g p :=
    hc p (hε.trans_le hp.1.2)
  have hb:=kz486 hR.le hεR hbox htop hside
  have hzero (x:ℝ) (hx:x ∉ Icc (-R) R):g (x,ε) = 0:=by
    apply hz (x,ε) (by linarith)
    have hh:R < |x|:=by
      have hh:x < -R ∨ R < x:=by simpa only [mem_Icc,not_and_or,not_le] using hx
      rcases hh with hh | hh
      · exact (lt_neg_of_lt_neg hh).trans_le (neg_le_abs x)
      · exact hh.trans_le (le_abs_self x)
    exact hMR.trans (hh.trans_le (norm_fst_le (x,ε)))
  have hcont:Continuous (fun x:ℝ => g (x,ε)):=by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hc (x,ε) hε).continuousAt.comp (f:=fun x:ℝ => (x,ε))
      (continuous_id.prodMk continuous_const).continuousAt
  have hint:=hcont.continuousOn.integrableOn_compact (μ:=volume) (isCompact_Icc (a:=-R) (b:=R))
  have hline:(∫ x in -R..R,g (x,ε)) = ∫ x:ℝ,g (x,ε):=by
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R),
      setIntegral_congr_set Ioc_ae_eq_Icc]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  exact ⟨R,hR,hεR,hint.integrable_of_forall_notMem_eq_zero hzero,(hline.symm.trans hb.symm)⟩
lemma ofReal_integral_le_lintegral_abs.{u_1} {α:Type u_1} [MeasurableSpace α]
    {μ:Measure α} {f:α → ℝ} (hf:Integrable f μ) :
    ENNReal.ofReal (∫ x,f x ∂μ) ≤ ∫⁻ x,ENNReal.ofReal |f x| ∂μ:=by
  rw [← ofReal_integral_eq_lintegral_ofReal hf.abs (Eventually.of_forall (fun x => abs_nonneg (f x)))]
  exact ENNReal.ofReal_le_ofReal (integral_mono hf hf.abs (fun x => le_abs_self _))
lemma kz488 {g:ℝ × ℝ → ℝ} {ε:ℝ} (hε:0 < ε)
    (hc:∀ p:ℝ × ℝ,0 < p.2 → ContDiffAt ℝ 2 g p)
    (hn:∀ p:ℝ × ℝ,0 ≤ g p)
    {K:Set (ℝ × ℝ)} (hK:IsCompact K)
    (hs:∀ p:ℝ × ℝ,ε/2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    (∫⁻ x:ℝ,ENNReal.ofReal (g (x,ε))) ≤
      ∫⁻ p in {p:ℝ × ℝ | ε ≤ p.2},ENNReal.ofReal ((p.2-ε)*|kz480 g p|):=by
  obtain ⟨R,_,_,hi,he⟩:=kz487 hε hc hK hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => hn (x,ε))),he]
  have hi₂:IntegrableOn (fun p:ℝ × ℝ => (p.2-ε)*kz480 g p)
      (Icc (-R,ε) (R,R)) volume:=by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    have hp':0 < p.2:=hε.trans_le hp.1.2
    have hh:ContinuousAt (fun p:ℝ × ℝ => (p.2-ε)*kz480 g p) p :=
      (continuous_snd.continuousAt.sub_const ε).mul (kz485 (hc p hp'))
    exact hh.continuousWithinAt
  refine (ofReal_integral_le_lintegral_abs hi₂).trans ?_
  calc
    (∫⁻ p in Icc (-R,ε) (R,R),ENNReal.ofReal |(p.2-ε)*kz480 g p|) =
        ∫⁻ p in Icc (-R,ε) (R,R),ENNReal.ofReal ((p.2-ε)*|kz480 g p|):=by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro p hp
      simp only [abs_mul,abs_of_nonneg (sub_nonneg.mpr hp.1.2)]
    _ ≤ _:=lintegral_mono_set (fun p hp => hp.1.2)
def kz489 (f:ℂ → ℝ) (z u v:ℂ):ℝ:=fderiv ℝ (fderiv ℝ f) z u v
def kz490 (f:ℂ → ℂ) (z u v:ℂ):ℂ:=fderiv ℝ (fderiv ℝ f) z u v
lemma kz491 {ψ:ℂ → ℝ} {F:ℂ → ℂ} {z:ℂ}
    (hψ:ContDiffAt ℝ 2 ψ (F z)) (hF:ContDiffAt ℝ 2 F z) (u v:ℂ) :
    kz489 (ψ ∘ F) z u v =
      fderiv ℝ ψ (F z) (kz490 F z u v) +
      kz489 ψ (F z) (fderiv ℝ F z u) (fderiv ℝ F z v):=by
  have hdψ:=hψ.differentiableAt (by norm_num)
  have hdF:=hF.differentiableAt (by norm_num)
  have hddψ:=(hψ.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hddF:=(hF.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have he:fderiv ℝ (ψ ∘ F) =ᶠ[𝓝 z] fun w =>
      (fderiv ℝ ψ (F w)).comp (fderiv ℝ F w):=by
    filter_upwards [hF.eventually (by simp),hdF.continuousAt.eventually (hψ.eventually (by simp))] with w hFw hψw
    exact fderiv_comp w (hψw.differentiableAt (by norm_num)) (hFw.differentiableAt (by norm_num))
  have hh:=((hddψ.hasFDerivAt.comp z hdF.hasFDerivAt).clm_comp hddF.hasFDerivAt).congr_of_eventuallyEq he
  rw [kz489,hh.fderiv]
  simp [kz489,kz490,ContinuousLinearMap.compL_apply]
lemma kz492 (B:ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (c:ℂ) :
    B c c + B (c*Complex.I) (c*Complex.I) = ‖c‖^2*(B 1 1+B Complex.I Complex.I):=by
  have hc:c = c.re • (1:ℂ)+c.im • Complex.I:=by simp
  have hci:c*Complex.I = (-c.im) • (1:ℂ)+c.re • Complex.I:=by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  have hn:‖c‖^2 = c.re^2+c.im^2:=by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,pow_two]
  rw [hci,hc]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [← hc,hn]
  ring
lemma kz493 (f:ℂ → ℝ) (z:ℂ) :
    Laplacian.laplacian f z = kz489 f z 1 1+kz489 f z Complex.I Complex.I:=by
  simp [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,kz489]
lemma kz494 (f:ℂ → ℂ) (z:ℂ) :
    Laplacian.laplacian f z = kz490 f z 1 1+kz490 f z Complex.I Complex.I:=by
  simp [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,kz490]
lemma kz495 {F:ℂ → ℂ} {z:ℂ}
    (hF:DifferentiableAt ℂ F z) (v:ℂ):fderiv ℝ F z v = deriv F z*v:=by
  rw [(hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [smul_eq_mul,mul_comm]
lemma kz496 {ψ:ℂ → ℝ} {F:ℂ → ℂ} {z:ℂ}
    (hψ:ContDiffAt ℝ 2 ψ (F z)) (hF:AnalyticAt ℂ F z) :
    Laplacian.laplacian (ψ ∘ F) z = ‖deriv F z‖^2*Laplacian.laplacian ψ (F z):=by
  rw [kz493,kz491 hψ (hF.contDiffAt.restrict_scalars ℝ),
    kz491 hψ (hF.contDiffAt.restrict_scalars ℝ)]
  have hz:=hF.harmonicAt.2.eq_of_nhds
  rw [kz494] at hz
  change kz490 F z 1 1+kz490 F z Complex.I Complex.I = 0 at hz
  have he:fderiv ℝ ψ (F z) (kz490 F z 1 1)+
      fderiv ℝ ψ (F z) (kz490 F z Complex.I Complex.I) = 0:=by
    rw [← map_add,hz,map_zero]
  simp only [kz495 hF.differentiableAt,mul_one]
  have hb:=kz492 (fderiv ℝ (fderiv ℝ ψ) (F z)) (deriv F z)
  rw [kz493]
  dsimp only [kz489] at *
  linarith
lemma kz497 (f:ℂ → ℝ) (p:ℝ × ℝ) :
    kz480 (f ∘ Complex.equivRealProdCLM.symm) p =
      Laplacian.laplacian f (Complex.equivRealProdCLM.symm p):=by
  have he:=Complex.equivRealProdCLM.symm.iteratedFDerivWithin_comp_right
    f (s:=univ) uniqueDiffOn_univ (mem_univ (Complex.equivRealProdCLM.symm p)) 2
  simp only [preimage_univ,iteratedFDerivWithin_univ] at he
  have h₁:=congrArg (fun B => B ![((1,0):ℝ × ℝ),(1,0)]) he
  have h₂:=congrArg (fun B => B ![((0,1):ℝ × ℝ),(0,1)]) he
  simp only [iteratedFDeriv_two_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,ContinuousLinearEquiv.coe_coe] at h₁ h₂
  have hc₁:Complex.equivRealProdCLM.symm (1,0) = 1:=by simp [Complex.equivRealProdCLM_symm_apply]
  have hc₂:Complex.equivRealProdCLM.symm (0,1) = Complex.I:=by simp [Complex.equivRealProdCLM_symm_apply]
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  rw [kz480,h₁,h₂,kz493]
  rfl
lemma kz498 {ψ:ℂ → ℝ} {z:ℂ}
    (hz:z ∉ tsupport ψ):Laplacian.laplacian ψ z = 0:=by
  have he:=notMem_tsupport_iff_eventuallyEq.mp hz
  have hh:=laplacian_congr_nhds he
  exact hh.eq_of_nhds.trans (by
    change Laplacian.laplacian (fun _:ℂ => (0:ℝ)) z = 0
    rw [laplacian_const]
    rfl)
lemma kz499 {ψ:ℂ → ℝ} (hψ:ContDiff ℝ 2 ψ) :
    Continuous (Laplacian.laplacian ψ):=by
  have hh:ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ ψ)) :=
    (hψ.fderiv_right (m:=1) (by norm_num)).fderiv_right (by norm_num)
  have hc:=hh.continuous
  have he:Laplacian.laplacian ψ = fun z => kz489 ψ z 1 1+kz489 ψ z Complex.I Complex.I :=
    funext (kz493 ψ)
  rw [he]
  unfold kz489
  fun_prop
lemma kz500 {ψ:ℂ → ℝ} (hψ:HasCompactSupport ψ) :
    HasCompactSupport (Laplacian.laplacian ψ):=by
  apply hψ.mono'
  intro z hz
  by_contra hn
  exact hz (kz498 hn)
lemma kz501 {F:ℂ → ℂ} {s:Set ℂ} (hs:MeasurableSet s)
    (hF:∀ z ∈ s,DifferentiableAt ℂ F z) (hi:InjOn F s) (b:ℂ → ℝ≥0∞) :
    (∫⁻ z in s,ENNReal.ofReal (‖deriv F z‖^2)*b (F z)) ≤ ∫⁻ w,b w:=by
  have he:=lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b
  have hh:(∫⁻ z in s,ENNReal.ofReal (‖deriv F z‖^2)*b (F z)) = ∫⁻ w in F '' s,b w:=by
    rw [he]
    apply setLIntegral_congr_fun hs
    intro z hz
    have hd:=(hF z hz).hasFDerivAt.restrictScalars ℝ
    have hf:(ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z:=hd.fderiv.symm
    dsimp only
    rw [hf]
    have hd':(fderiv ℝ F z).det = ‖deriv F z‖^2:=kz76 (hF z hz)
    rw [hd',abs_of_nonneg (sq_nonneg _)]
  rw [hh]
  exact lintegral_mono' Measure.restrict_le_self le_rfl
lemma kz502 {F:ℂ → ℂ} {ψ:ℂ → ℝ}
    (hF:∀ z:ℂ,0 < z.im → AnalyticAt ℂ F z)
    (hi:InjOn F {z:ℂ | 0 < z.im})
    (hψ:ContDiff ℝ 2 ψ) (hn:∀ w,0 ≤ ψ w) (_hψK:HasCompactSupport ψ)
    (hproper:∀ η:ℝ,0 < η → IsCompact ({z:ℂ | η ≤ z.im} ∩ F ⁻¹' tsupport ψ))
    {H:ℝ} (hH:0 ≤ H)
    (hheight:∀ z:ℂ,0 < z.im → F z ∈ tsupport ψ → z.im ≤ H) :
    ∀ ε:ℝ,0 < ε → (∫⁻ x:ℝ,ENNReal.ofReal (ψ (F (x+ε*Complex.I)))) ≤
      ENNReal.ofReal H * ∫⁻ w:ℂ,ENNReal.ofReal |Laplacian.laplacian ψ w|:=by
  intro ε hε
  let C:=Complex.equivRealProdCLM.symm
  let g:ℝ × ℝ → ℝ:=(ψ ∘ F) ∘ C
  have hc (p:ℝ × ℝ) (hp:0 < p.2):ContDiffAt ℝ 2 g p:=by
    have hz:0 < (C p).im:=hp
    exact (hψ.contDiffAt.comp _ ((hF (C p) hz).contDiffAt.restrict_scalars ℝ)).comp _ C.contDiff.contDiffAt
  have hK:=(hproper (ε/2) (by linarith)).image Complex.equivRealProdCLM.continuous
  have hs (p:ℝ × ℝ) (hp:ε/2 ≤ p.2) (hg:g p ≠ 0) :
      p ∈ Complex.equivRealProdCLM '' ({z:ℂ | ε/2 ≤ z.im} ∩ F ⁻¹' tsupport ψ):=by
    refine ⟨C p,⟨hp,subset_closure hg⟩,?_⟩
    exact Complex.equivRealProdCLM.apply_symm_apply p
  have ht:=kz488 hε hc (fun p => hn _) hK hs
  have ht':(∫⁻ x:ℝ,ENNReal.ofReal (ψ (F (x+ε*Complex.I)))) ≤
      ∫⁻ z in {z:ℂ | ε ≤ z.im},ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|):=by
    have he:=Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p:ℝ × ℝ => ENNReal.ofReal ((p.2-ε)*|kz480 g p|)) {p:ℝ × ℝ | ε ≤ p.2}
    have hh:(∫⁻ p in {p:ℝ × ℝ | ε ≤ p.2},ENNReal.ofReal ((p.2-ε)*|kz480 g p|)) =
        ∫⁻ z in {z:ℂ | ε ≤ z.im},ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|):=by
      rw [← he]
      apply lintegral_congr
      intro z
      dsimp only [g,C]
      rw [kz497]
      rfl
    rw [hh] at ht
    simpa only [g,C,Function.comp_apply,Complex.equivRealProdCLM_symm_apply] using ht
  refine ht'.trans ?_
  have hmeas:MeasurableSet {z:ℂ | ε ≤ z.im}:=isClosed_le continuous_const Complex.continuous_im |>.measurableSet
  calc
    (∫⁻ z in {z:ℂ | ε ≤ z.im},ENNReal.ofReal ((z.im-ε)*|Laplacian.laplacian (ψ ∘ F) z|)) ≤
        ∫⁻ z in {z:ℂ | ε ≤ z.im},ENNReal.ofReal H *
          (ENNReal.ofReal (‖deriv F z‖^2)*ENNReal.ofReal |Laplacian.laplacian ψ (F z)|):=by
      apply setLIntegral_mono' hmeas
      intro z hz
      rw [kz496 hψ.contDiffAt (hF z (hε.trans_le hz)),
        abs_mul,abs_of_nonneg (sq_nonneg _),← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul hH]
      apply ENNReal.ofReal_le_ofReal
      by_cases hd:Laplacian.laplacian ψ (F z) = 0
      · simp [hd]
      have hm:F z ∈ tsupport ψ:=by
        by_contra hh
        exact hd (kz498 hh)
      nlinarith [sq_nonneg ‖deriv F z‖,abs_nonneg (Laplacian.laplacian ψ (F z)),
        hheight z (hε.trans_le hz) hm,
        mul_nonneg (sq_nonneg ‖deriv F z‖) (abs_nonneg (Laplacian.laplacian ψ (F z)))]
    _ = ENNReal.ofReal H * ∫⁻ z in {z:ℂ | ε ≤ z.im},
        ENNReal.ofReal (‖deriv F z‖^2)*ENNReal.ofReal |Laplacian.laplacian ψ (F z)| :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _:=by
      exact mul_le_mul le_rfl (kz501 hmeas
        (fun z hz => (hF z (hε.trans_le hz)).differentiableAt)
        (hi.mono (fun z hz => hε.trans_le hz))
        (fun w => ENNReal.ofReal |Laplacian.laplacian ψ w|)) zero_le zero_le
lemma kz503 (K:Set ℂ) (hK:IsCompact K) :
    ∃ ψ:ℂ → ℝ,ContDiff ℝ 2 ψ ∧ (∀ w,0 ≤ ψ w) ∧ HasCompactSupport ψ ∧
      ∀ w ∈ K,ψ w = 1:=by
  obtain ⟨R,hR⟩:=hK.isBounded.subset_closedBall (0:ℂ)
  let b:ContDiffBump (0:ℂ):=⟨max R 0+1,max R 0+2,by positivity,by linarith⟩
  refine ⟨b,b.contDiff,b.nonneg',b.hasCompactSupport,fun w hw => ?_⟩
  apply b.one_of_mem_closedBall
  exact Metric.closedBall_subset_closedBall (by dsimp [b]; linarith [le_max_left R 0]) (hR hw)
lemma kz504 {F:ℂ → ℂ}
    (hF:∀ z:ℂ,0 < z.im → AnalyticAt ℂ F z)
    (hi:InjOn F {z:ℂ | 0 < z.im})
    (hproper:∀ K:Set ℂ,IsCompact K → ∀ η:ℝ,0 < η →
      IsCompact ({z:ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hheight:∀ K:Set ℂ,IsCompact K → ∃ H:ℝ,0 < H ∧
      ∀ z:ℂ,0 < z.im → F z ∈ K → z.im ≤ H)
    {K:Set ℂ} (hK:IsCompact K) :
    ∃ C:ℝ≥0∞,C < ∞ ∧ ∀ ε:ℝ,0 < ε →
      volume {x:ℝ | F (x+ε*Complex.I) ∈ K} ≤ C:=by
  obtain ⟨ψ,hψ,hn,hψK,hψone⟩:=kz503 K hK
  obtain ⟨H,hH,hHb⟩:=hheight (tsupport ψ) hψK
  let C:=ENNReal.ofReal H * ∫⁻ w:ℂ,ENNReal.ofReal |Laplacian.laplacian ψ w|
  have hfin:C < ∞:=by
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    have hi:=(kz499 hψ).integrable_of_hasCompactSupport (μ:=volume) (kz500 hψK)
    simpa only [HasFiniteIntegral,← ofReal_norm,Real.norm_eq_abs] using hi.hasFiniteIntegral
  refine ⟨C,hfin,fun ε hε => ?_⟩
  have hb:=kz502 hF hi hψ hn hψK
    (hproper (tsupport ψ) hψK) hH.le hHb ε hε
  refine le_trans ?_ hb
  have hcont:Continuous (fun x:ℝ => F (x+ε*Complex.I)):=by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hz:0 < (x+ε*Complex.I:ℂ).im:=by simpa using hε
    exact (hF _ hz).continuousAt.comp (f:=fun x:ℝ => (x+ε*Complex.I:ℂ))
      (by fun_prop)
  have hm:MeasurableSet {x:ℝ | F (x+ε*Complex.I) ∈ K} :=
    hK.isClosed.measurableSet.preimage hcont.measurable
  rw [← lintegral_indicator_one hm]
  apply lintegral_mono
  intro x
  by_cases hx:F (x+ε*Complex.I) ∈ K
  · simp [hx,hψone _ hx]
  · simp [hx]
lemma kz505 (g:kz140) {β:ℝ} (hβ:1 < β)
    (hfin:(∫⁻ z in kz459,
      ENNReal.ofReal (z.im^(β+1)*‖kz183 g z‖⁻¹^4)) < ∞)
    {K:Set ℂ} (hK:IsCompact K) :
    ∃ C:ℝ≥0∞,C < ∞ ∧ ∀ ε:ℝ,0 < ε →
      volume {x:ℝ | kz183 g (x+ε*Complex.I) ∈ K} ≤ C:=by
  apply kz504
    (fun z hz => (kz184 g).1.1.analyticAt (kz146.mem_nhds hz))
    (kz184 g).1.2
    (fun _ hK η hη => kz478 g hβ hfin hK hη)
    (fun _ hK => kz479 g hβ hfin hK) hK
lemma kz506 :
    ∃ M:ℝ,0 ≤ M ∧ ∀ (g:kz140) (w:ℂ),|w.re| ≤ 1 →
      (1/2:ℝ) ≤ w.im → w.im ≤ 1 → ‖kz183 g w‖ ≤ M:=by
  let B:Set (ℝ × ℝ):=Icc (-1,1/2) (1,1)
  let K:Set ℂ:=Complex.equivRealProdCLM.symm '' B
  have hK:IsCompact K:=isCompact_Icc.image Complex.equivRealProdCLM.symm.continuous
  have hKsub:K ⊆ Set.range (fun w:kz145 => (w:ℂ)):=by
    rintro _ ⟨p,hp,rfl⟩
    refine ⟨⟨Complex.equivRealProdCLM.symm p,?_⟩,rfl⟩
    change 0 < p.2
    linarith [hp.1.2]
  have hKs:IsCompact ((fun w:kz145 => (w:ℂ)) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKsub
  have hprod:=(isCompact_univ (X:=kz140)).prod hKs
  obtain ⟨M,hM⟩:=hprod.exists_bound_of_continuousOn kz187.continuousOn
  refine ⟨max M 0,le_max_right _ _,fun g w hx hy hyy => ?_⟩
  have hw:w ∈ kz145:=by change 0 < w.im; linarith
  have hmem:(g,⟨w,hw⟩) ∈ (univ:Set kz140) ×ˢ ((fun w:kz145 => (w:ℂ)) ⁻¹' K):=by
    refine ⟨mem_univ _,⟨(w.re,w.im),?_,?_⟩⟩
    · exact ⟨⟨(abs_le.mp hx).1,hy⟩,⟨(abs_le.mp hx).2,hyy⟩⟩
    · exact Complex.equivRealProdCLM.symm_apply_apply w
  exact (hM _ hmem).trans (le_max_left _ _)
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
lemma kz507 {z:ℂ} (_hz:z ∈ kz145) :
    Metric.ball z z.im ⊆ kz145:=by
  intro w hw
  have hh:‖w-z‖ < z.im:=by simpa only [Metric.mem_ball,dist_eq_norm] using hw
  have hb:=Complex.abs_im_le_norm (w-z)
  change 0 < w.im
  simp only [Complex.sub_im] at hb
  linarith [neg_le_abs (w.im-z.im)]
lemma kz508 {F:ℂ → ℂ} (hf:kz1 F kz145)
    {z ξ:ℂ} (hz:z ∈ kz145) (hξ:ξ ∉ F '' kz145) :
    z.im*‖deriv F z‖ ≤ 4*‖F z-ξ‖:=by
  have hr:0 < z.im:=hz
  have hb:=kz130 hr
    (show kz1 F (Metric.ball z z.im) from ⟨hf.1.mono (kz507 hz),hf.2.mono (kz507 hz)⟩)
  have hn:ξ ∉ Metric.ball (F z) (z.im*‖deriv F z‖/4):=by
    intro hh
    exact hξ ((image_mono (kz507 hz)) (hb hh))
  have hn':z.im*‖deriv F z‖/4 ≤ ‖F z-ξ‖:=by
    simpa only [Metric.mem_ball,dist_eq_norm,not_lt,norm_sub_rev] using hn
  linarith
lemma kz509 {M:ℝ} (hM:0 ≤ M)
    (hb:∀ (g:kz140) (w:ℂ),|w.re| ≤ 1 → (1/2:ℝ) ≤ w.im → w.im ≤ 1 → ‖kz183 g w‖ ≤ M)
    (g:kz140) {h x y x':ℝ} {ξ:ℂ} (hh:0 < h)
    (hy:h ≤ y) (hyy:y ≤ 2*h) (hxx:|x'-x| ≤ h)
    (hξ:ξ ∉ kz183 g '' kz145) :
    ‖kz183 g (x'+h*Complex.I)-ξ‖ ≤ (1+4*M)*‖kz183 g (x+y*Complex.I)-ξ‖:=by
  let z:ℂ:=x+y*Complex.I
  let w:ℂ:=((x'-x)/y:ℝ)+(h/y:ℝ)*Complex.I
  have hy0:0 < y:=hh.trans_le hy
  have hz:z ∈ kz145:=by simpa [z,kz145] using hy0
  have hwy:w.im = h/y:=by simp [w]
  have hwx:w.re = (x'-x)/y:=by simp [w]
  have hw:w ∈ kz145:=by simpa [kz145,hwy] using (div_pos hh hy0)
  have hwr:|w.re| ≤ 1:=by rw [hwx,abs_div,abs_of_pos hy0]; exact (div_le_one hy0).mpr (hxx.trans hy)
  have hwl:(1/2:ℝ) ≤ w.im:=by rw [hwy,le_div_iff₀ hy0]; linarith
  have hwu:w.im ≤ 1:=by rw [hwy]; exact (div_le_one hy0).mpr hy
  have hwa:kz148 z w = x'+h*Complex.I:=by
    apply Complex.ext <;> simp [kz148,z,w,Complex.mul_re,Complex.mul_im]
    · field_simp
      ring
    · field_simp
  have hd:‖deriv (kz183 g) z‖ > 0:=norm_pos_iff.mpr (kz91 kz146 (kz184 g).1 hz)
  have hm:=hb (kz192 g ⟨z,hz⟩) w hwr hwl hwu
  rw [kz193 _ _ hw,kz155,hwa,norm_div,norm_mul,Complex.norm_real] at hm
  have hzim:z.im = y:=by simp [z]
  rw [hzim,Real.norm_eq_abs,abs_of_pos hy0] at hm
  have hm':=(div_le_iff₀ (mul_pos hy0 hd)).mp hm
  have hq:=kz508 (kz184 g).1 hz hξ
  rw [hzim] at hq
  have hsum:=norm_add_le (kz183 g (x'+h*Complex.I)-kz183 g z) (kz183 g z-ξ)
  simp only [sub_add_sub_cancel] at hsum
  have hhq:=mul_le_mul_of_nonneg_left hq hM
  dsimp only [z] at *
  nlinarith
def kz510 (F:ℂ → ℂ) (k δ:ℝ) (ξ:ℂ):Set ℂ :=
  {z | 0 < z.im ∧ ‖F z-ξ‖ ≤ z.im^k/δ}
lemma kz511 {F:ℂ → ℂ} {k δ:ℝ}
    (hk:0 < k) (_hδ:0 < δ)
    (hi:InjOn F {z:ℂ | 0 < z.im})
    (hopen:∀ z:ℂ,0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    {ξ:ℂ} (hξ:ξ ∈ F '' {z:ℂ | 0 < z.im}) :
    ∃ η:ℝ,0 < η ∧ ∀ z:ℂ,0 < z.im →
      ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im:=by
  obtain ⟨z₀,hz₀,rfl⟩:=hξ
  change 0 < z₀.im at hz₀
  have hn:{z:ℂ | z₀.im/2 < z.im} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by change z₀.im/2 < z₀.im; linarith)
  have hn':=image_mem_map (m:=F) hn
  rw [hopen z₀ hz₀] at hn'
  obtain ⟨r,hr,hrB⟩:=Metric.mem_nhds_iff.mp hn'
  have hc:ContinuousAt (fun y:ℝ => y^k/δ) 0 :=
    (Real.continuous_rpow_const hk.le).continuousAt.div_const δ
  have he:(0:ℝ)^k/δ = 0:=by rw [Real.zero_rpow (ne_of_gt hk),zero_div]
  have hevent:∀ᶠ y:ℝ in 𝓝 0,y^k/δ < r:=by
    have hh:=hc.eventually (gt_mem_nhds (show (0:ℝ)^k/δ < r by rwa [he]))
    exact hh
  obtain ⟨a,ha,haB⟩:=Metric.mem_nhds_iff.mp hevent
  refine ⟨min a (z₀.im/2),lt_min ha (by linarith),fun z hz hzw => ?_⟩
  by_contra! hsmall
  have hza:z.im < a:=hsmall.trans_le (min_le_left _ _)
  have hm:F z ∈ Metric.ball (F z₀) r:=by
    rw [Metric.mem_ball,dist_eq_norm]
    exact hzw.trans_lt (haB (by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hz] using hza))
  obtain ⟨w,hw,hwe⟩:=hrB hm
  have hwH:0 < w.im:=by change z₀.im/2 < w.im at hw; linarith
  have hwz:w = z:=hi hwH hz hwe
  subst w
  change z₀.im/2 < z.im at hw
  exact (not_lt_of_ge hw.le) (hsmall.trans_le (min_le_right _ _))
lemma kz512 {F:ℂ → ℂ} {k δ:ℝ} {ξ:ℂ}
    (hk:0 ≤ k) (hδ:0 < δ)
    (hc:ContinuousOn F {z:ℂ | 0 < z.im})
    (ht:kz472 F (4*k))
    (hp:∀ K:Set ℂ,IsCompact K → ∀ η:ℝ,0 < η →
      IsCompact ({z:ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hheight:∃ η:ℝ,0 < η ∧ ∀ z:ℂ,0 < z.im →
      ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im) :
    IsCompact (kz510 F k δ ξ):=by
  obtain ⟨η,hη,hηb⟩:=hheight
  obtain ⟨R₀,hR₀⟩:=(hp (Metric.closedBall (0:ℂ) (2*‖ξ‖+1))
    (isCompact_closedBall _ _) η hη).isBounded.subset_closedBall (0:ℂ)
  obtain ⟨R₁,hR₁⟩:=kz475 ht (δ/2) (by linarith)
  have hb:kz510 F k δ ξ ⊆ Metric.closedBall 0 (max R₀ R₁):=by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    by_contra! hn
    have hno:2*‖ξ‖+1 < ‖F z‖:=by
      by_contra! hle
      have hh:=hR₀ ⟨hηb z hz.1 hz.2,by simpa using hle⟩
      have hh':‖z‖ ≤ R₀:=by simpa using hh
      linarith [le_max_left R₀ R₁]
    have hFn:0 < ‖F z‖:=by nlinarith [norm_nonneg ξ]
    have ht':=hR₁ z hz.1 ((le_max_right _ _).trans hn.le)
    rw [← div_eq_mul_inv,div_lt_iff₀ hFn] at ht'
    have hpot:=(le_div_iff₀ hδ).mp hz.2
    have hnorm:‖F z‖ ≤ ‖F z-ξ‖+‖ξ‖:=by
      simpa only [sub_add_cancel] using norm_add_le (F z-ξ) ξ
    nlinarith
  have he:kz510 F k δ ξ =
      {z:ℂ | η ≤ z.im} ∩ (fun z => ‖F z-ξ‖-z.im^k/δ) ⁻¹' Iic 0:=by
    ext z
    constructor
    · intro hz
      exact ⟨hηb z hz.1 hz.2,sub_nonpos.mpr hz.2⟩
    · intro hz
      exact ⟨hη.trans_le hz.1,sub_nonpos.mp hz.2⟩
  have hcc:ContinuousOn (fun z:ℂ => ‖F z-ξ‖-z.im^k/δ) {z:ℂ | η ≤ z.im}:=by
    apply ((hc.mono (fun z hz => hη.trans_le hz)).sub continuousOn_const).norm.sub
    exact ((Real.continuous_rpow_const hk).comp Complex.continuous_im).continuousOn.div_const δ
  apply (isCompact_closedBall (0:ℂ) (max R₀ R₁)).of_isClosed_subset _ hb
  rw [he]
  exact hcc.preimage_isClosed_of_isClosed (isClosed_le continuous_const Complex.continuous_im) isClosed_Iic
def kz513 (h:ℝ) (j:ℤ):Set ℝ:=Ico ((j:ℝ)*h) (((j:ℝ)+1)*h)
lemma kz514 {h:ℝ} (hh:0 < h):Pairwise (Function.onFun Disjoint (kz513 h)):=by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hhij:(i:ℝ)+1 ≤ j:=by exact_mod_cast Int.add_one_le_iff.mpr hij
    have hm:=mul_le_mul_of_nonneg_right hhij hh.le
    exact (not_lt_of_ge (hm.trans hy.1)) hx.2
  · have hhji:(j:ℝ)+1 ≤ i:=by exact_mod_cast Int.add_one_le_iff.mpr hji
    have hm:=mul_le_mul_of_nonneg_right hhji hh.le
    exact (not_lt_of_ge (hm.trans hx.1)) hy.2
lemma kz515 {h:ℝ} (_hh:0 ≤ h) (j:ℤ) :
    volume (kz513 h j) = ENNReal.ofReal h:=by
  rw [kz513,Real.volume_Ico]
  congr 1
  ring
lemma kz516 {h:ℝ} (hh:0 < h) (x:ℝ):x ∈ kz513 h ⌊x/h⌋:=by
  constructor
  · exact (le_div_iff₀ hh).mp (Int.floor_le _)
  · exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)
lemma kz517 {h:ℝ} (_hh:0 < h) {j:ℤ} {x x':ℝ}
    (hx:x ∈ kz513 h j) (hx':x' ∈ kz513 h j):|x'-x| ≤ h:=by
  rw [abs_le]
  constructor <;> dsimp [kz513] at hx hx' <;> nlinarith [hx.1,hx.2,hx'.1,hx'.2]
lemma kz518 {h r:ℝ} (hh:0 < h) (hr:0 ≤ r)
    (W:Set ℤ) (centers:ℤ → ℂ) {S:Set ℝ} {C:ℝ≥0∞}
    (hsub:∀ j ∈ W,kz513 h j ⊆ S) (hS:volume S ≤ C) :
    volume (⋃ j:W,Metric.closedBall (centers j) r) ≤
      (ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*C:=by
  have hlen:(∑' j:W,ENNReal.ofReal h) ≤ C:=by
    have hd:Pairwise (Function.onFun Disjoint (fun j:W => kz513 h j)):=by
      intro i j hij
      exact kz514 hh (fun he => hij (Subtype.ext he))
    have he:=measure_iUnion (μ:=volume) hd (fun _ => measurableSet_Ico)
    simp only [kz515 hh.le] at he
    rw [← he]
    exact (measure_mono (iUnion_subset (fun (j:W) => hsub j.val j.property))).trans hS
  have harea (j:W):volume (Metric.closedBall (centers j) r) = ENNReal.ofReal (Real.pi*r^2):=by
    rw [Complex.volume_closedBall]
    have hpi:(NNReal.pi:ℝ≥0∞) = ENNReal.ofReal Real.pi:=by
      rw [ENNReal.ofReal,ENNReal.coe_inj]
      apply Subtype.ext
      exact (Real.coe_toNNReal Real.pi Real.pi_pos.le).symm
    rw [hpi,ENNReal.ofReal_mul Real.pi_pos.le,ENNReal.ofReal_pow hr]
    exact mul_comm _ _
  calc
    _ ≤ ∑' j:W,volume (Metric.closedBall (centers j) r):=measure_iUnion_le _
    _ = ∑' j:W,(ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*ENNReal.ofReal h:=by
      apply tsum_congr
      intro j
      rw [harea]
      exact (ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hh)) ENNReal.ofReal_ne_top).symm
    _ = (ENNReal.ofReal (Real.pi*r^2)/ENNReal.ofReal h)*(∑' j:W,ENNReal.ofReal h):=ENNReal.tsum_mul_left
    _ ≤ _:=mul_le_mul le_rfl hlen zero_le zero_le
lemma kz519 {r:ℝ} (hr0:0 ≤ r) (hr1:r < 1) :
    (∑' n:ℕ,ENNReal.ofReal (r^n)) < ∞:=by
  have hs:Summable (fun n:ℕ => (⟨r^n,pow_nonneg hr0 n⟩:ℝ≥0)) :=
    NNReal.summable_coe.mp (summable_geometric_of_lt_one hr0 hr1)
  have ht:=ENNReal.tsum_coe_ne_top_iff_summable.mpr hs
  apply lt_top_iff_ne_top.mpr
  convert ht using 1
  congr 1
  ext n
  exact ENNReal.ofReal_eq_coe_nnreal (pow_nonneg hr0 n)
lemma kz520 {E:ℕ → Set ℂ} {C:ℝ≥0∞} (hC:C < ∞)
    {r:ℝ} (hr0:0 ≤ r) (hr1:r < 1)
    (hE:∀ n,volume (E n) ≤ C*ENNReal.ofReal (r^n)) :
    ∀ᵐ ξ:ℂ,∀ᶠ n:ℕ in atTop,ξ ∉ E n:=by
  apply ae_eventually_notMem
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hE)
  rw [ENNReal.tsum_mul_left]
  exact ne_of_lt (ENNReal.mul_lt_top hC (kz519 hr0 hr1))
def kz521 (n:ℕ):ℝ:=(1/2)^n
lemma kz522 (n:ℕ):0 < kz521 n:=pow_pos (by norm_num) n
lemma kz523 (n:ℕ):kz521 n ≤ 1:=pow_le_one₀ (by norm_num) (by norm_num)
lemma kz524 {y:ℝ} (hy:0 < y) (hy1:y ≤ 1) :
    ∃ n:ℕ,kz521 n ≤ y ∧ y ≤ 2*kz521 n:=by
  obtain ⟨n,hn,hn'⟩:=exists_nat_pow_near_of_lt_one hy hy1
    (by norm_num:(0:ℝ) < 1/2) (by norm_num:(1/2:ℝ) < 1)
  refine ⟨n+1,hn.le,?_⟩
  dsimp [kz521]
  rw [pow_succ]
  nlinarith
lemma kz525:Antitone kz521:=by
  intro m n hmn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
lemma kz526 (N:ℕ) {y:ℝ} (hy:0 < y) (hyN:y < kz521 N) :
    ∃ n ≥ N,kz521 n ≤ y ∧ y ≤ 2*kz521 n:=by
  obtain ⟨n,hn,hn'⟩:=kz524 hy (hyN.le.trans (kz523 N))
  refine ⟨n,?_,hn,hn'⟩
  by_contra! h
  exact (not_lt_of_ge ((kz525 h.le).trans hn)) hyN
lemma kz527 {k h y:ℝ} (hk:1 ≤ k) (hh:0 < h) (hh1:h ≤ 1)
    (hy:0 ≤ y) (hyh:y ≤ 2*h):y^k ≤ (2:ℝ)^k*h:=by
  calc
    y^k ≤ (2*h)^k:=Real.rpow_le_rpow hy hyh (by linarith)
    _ = (2:ℝ)^k*h^k:=Real.mul_rpow (by norm_num) hh.le
    _ ≤ _:=mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one hh.le hh1 hk) (by positivity)
def kz528 (F:ℂ → ℂ) (k R δ h:ℝ):Set ℂ :=
  {ξ | ξ ∉ F '' {z:ℂ | 0 < z.im} ∧ ‖ξ‖ ≤ R ∧
    ∃ x y:ℝ,h ≤ y ∧ y ≤ 2*h ∧ ‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ}
lemma kz529 {F:ℂ → ℂ} {k L R δ:ℝ}
    (hk:1 ≤ k) (hL:0 ≤ L) (hδ:0 < δ)
    (hcell:∀ h x y x':ℝ,∀ ξ:ℂ,0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z:ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace:∀ K:Set ℂ,IsCompact K → ∃ C:ℝ≥0∞,C < ∞ ∧ ∀ ε:ℝ,0 < ε →
      volume {x:ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∃ C:ℝ≥0∞,C < ∞ ∧ ∀ h:ℝ,0 < h → h ≤ 1 →
      volume (kz528 F k R δ h) ≤ C*ENNReal.ofReal h:=by
  let D:=L*(2:ℝ)^k/δ
  have hD:0 ≤ D:=div_nonneg (mul_nonneg hL (by positivity)) hδ.le
  let K:=Metric.closedBall (0:ℂ) (R+D)
  obtain ⟨C,hC,hCt⟩:=htrace K (isCompact_closedBall _ _)
  refine ⟨ENNReal.ofReal (Real.pi*D^2)*C,ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC,fun h hh hh1 => ?_⟩
  let W:Set ℤ:={j | ∃ ξ ∈ kz528 F k R δ h,
    ∃ x y:ℝ,x ∈ kz513 h j ∧ h ≤ y ∧ y ≤ 2*h ∧ ‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ}
  let center (j:ℤ):=F ((((j:ℝ)+1/2)*h:ℝ)+h*Complex.I)
  have hb {j:ℤ} {ξ:ℂ} (hξ:ξ ∈ kz528 F k R δ h)
      {x y x':ℝ} (hx:x ∈ kz513 h j) (hy:h ≤ y) (hyy:y ≤ 2*h)
      (hFw:‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ) (hx':x' ∈ kz513 h j) :
      ‖F (x'+h*Complex.I)-ξ‖ ≤ D*h:=by
    have ht:=hcell h x y x' ξ hh hy hyy (kz517 hh hx hx') hξ.1
    have hp:=div_le_div_of_nonneg_right (kz527 hk hh hh1 (hh.le.trans hy) hyy) hδ.le
    have hp':=mul_le_mul_of_nonneg_left (hFw.trans hp) hL
    dsimp [D]
    calc
      _ ≤ L*((2:ℝ)^k*h/δ):=ht.trans hp'
      _ = _:=by ring
  have hsub (j:ℤ) (hj:j ∈ W):kz513 h j ⊆ {x:ℝ | F (x+h*Complex.I) ∈ K}:=by
    rcases hj with ⟨ξ,hξ,x,y,hx,hy,hyy,hFw⟩
    intro x' hx'
    have hhB:=hb hξ hx hy hyy hFw hx'
    have hn:=norm_add_le (F (x'+h*Complex.I)-ξ) ξ
    simp only [sub_add_cancel] at hn
    change F (x'+h*Complex.I) ∈ Metric.closedBall (0:ℂ) (R+D)
    rw [Metric.mem_closedBall,dist_zero_right]
    nlinarith [hξ.2.1,mul_le_of_le_one_right hD hh1]
  have hcovered:kz528 F k R δ h ⊆ ⋃ j:W,Metric.closedBall (center j) (D*h):=by
    intro ξ hξ
    obtain ⟨x,y,hy,hyy,hFw⟩:=hξ.2.2
    let j:ℤ:=⌊x/h⌋
    have hx:x ∈ kz513 h j:=kz516 hh _
    have hj:j ∈ W:=⟨ξ,hξ,x,y,hx,hy,hyy,hFw⟩
    apply mem_iUnion.mpr
    refine ⟨⟨j,hj⟩,?_⟩
    rw [Metric.mem_closedBall,dist_eq_norm,norm_sub_rev]
    change ‖F ((((j:ℝ)+1/2)*h:ℝ)+h*Complex.I)-ξ‖ ≤ D*h
    exact hb (x':=((j:ℝ)+1/2)*h) hξ hx hy hyy hFw (by constructor <;> nlinarith)
  calc
    _ ≤ volume (⋃ j:W,Metric.closedBall (center j) (D*h)):=measure_mono hcovered
    _ ≤ (ENNReal.ofReal (Real.pi*(D*h)^2)/ENNReal.ofReal h)*C :=
      kz518 hh (mul_nonneg hD hh.le) W center hsub (hCt h hh)
    _ = _:=by
      rw [← ENNReal.ofReal_div_of_pos hh]
      have he:Real.pi*(D*h)^2/h = (Real.pi*D^2)*h:=by field_simp
      rw [he,ENNReal.ofReal_mul (by positivity)]
      ring
lemma kz530 {F:ℂ → ℂ} {k L R δ:ℝ}
    (hk:1 ≤ k) (hL:0 ≤ L) (hδ:0 < δ)
    (hcell:∀ h x y x':ℝ,∀ ξ:ℂ,0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z:ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace:∀ K:Set ℂ,IsCompact K → ∃ C:ℝ≥0∞,C < ∞ ∧ ∀ ε:ℝ,0 < ε →
      volume {x:ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ:ℂ,ξ ∉ F '' {z:ℂ | 0 < z.im} → ‖ξ‖ ≤ R →
      ∃ η:ℝ,0 < η ∧ ∀ z:ℂ,0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im:=by
  obtain ⟨C,hC,hCb⟩:=kz529 hk hL hδ hcell htrace (R:=R)
  have hae:=kz520 hC
    (by norm_num:(0:ℝ) ≤ 1/2) (by norm_num:(1/2:ℝ) < 1)
    (E:=fun n => kz528 F k R δ (kz521 n))
    (fun n => hCb _ (kz522 n) (kz523 n))
  filter_upwards [hae] with ξ hξ
  intro ho hR
  obtain ⟨N,hN⟩:=eventually_atTop.mp hξ
  refine ⟨kz521 N,kz522 N,fun z hz hzw => ?_⟩
  by_contra! hh
  obtain ⟨n,hn,hy,hyy⟩:=kz526 N hz hh
  apply hN n hn
  refine ⟨ho,hR,z.re,z.im,hy,hyy,?_⟩
  simpa only [Complex.re_add_im] using hzw
lemma kz531 {F:ℂ → ℂ} {k L:ℝ}
    (hk:1 ≤ k) (hL:0 ≤ L)
    (hi:InjOn F {z:ℂ | 0 < z.im})
    (hopen:∀ z:ℂ,0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    (hcell:∀ h x y x':ℝ,∀ ξ:ℂ,0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z:ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace:∀ K:Set ℂ,IsCompact K → ∃ C:ℝ≥0∞,C < ∞ ∧ ∀ ε:ℝ,0 < ε →
      volume {x:ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ:ℂ,∀ δ:ℝ,0 < δ →
      ∃ η:ℝ,0 < η ∧ ∀ z:ℂ,0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/δ → η ≤ z.im:=by
  have hae:∀ᵐ ξ:ℂ,∀ R n:ℕ,
      ξ ∉ F '' {z:ℂ | 0 < z.im} → ‖ξ‖ ≤ R →
      ∃ η:ℝ,0 < η ∧ ∀ z:ℂ,0 < z.im →
        ‖F z-ξ‖ ≤ z.im^k/(1/(n+1:ℝ)) → η ≤ z.im:=by
    apply ae_all_iff.mpr
    intro R
    apply ae_all_iff.mpr
    intro n
    exact kz530 hk hL (by positivity) hcell htrace
  filter_upwards [hae] with ξ hξ
  intro δ hδ
  by_cases ho:ξ ∈ F '' {z:ℂ | 0 < z.im}
  · exact kz511 (by linarith) hδ hi hopen ho
  obtain ⟨R,hR⟩:=exists_nat_ge ‖ξ‖
  obtain ⟨n,hn⟩:=exists_nat_gt (1/δ)
  have hn0:0 < (n+1:ℝ):=by positivity
  have hnδ:1/(n+1:ℝ) ≤ δ:=by
    apply (div_le_iff₀ hn0).mpr
    have hh:=(div_lt_iff₀ hδ).mp hn
    nlinarith
  obtain ⟨η,hη,hηb⟩:=hξ R n ho hR
  refine ⟨η,hη,fun z hz hzw => ?_⟩
  exact hηb z hz (hzw.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) (by positivity) hnδ))
lemma kz532 {F:ℂ → ℂ} {k L:ℝ}
    (hk:1 ≤ k) (hL:0 ≤ L)
    (hc:ContinuousOn F {z:ℂ | 0 < z.im})
    (hi:InjOn F {z:ℂ | 0 < z.im})
    (hopen:∀ z:ℂ,0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    (ht:kz472 F (4*k))
    (hp:∀ K:Set ℂ,IsCompact K → ∀ η:ℝ,0 < η →
      IsCompact ({z:ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hcell:∀ h x y x':ℝ,∀ ξ:ℂ,0 < h → h ≤ y → y ≤ 2*h → |x'-x| ≤ h →
      ξ ∉ F '' {z:ℂ | 0 < z.im} →
      ‖F (x'+h*Complex.I)-ξ‖ ≤ L*‖F (x+y*Complex.I)-ξ‖)
    (htrace:∀ K:Set ℂ,IsCompact K → ∃ C:ℝ≥0∞,C < ∞ ∧ ∀ ε:ℝ,0 < ε →
      volume {x:ℝ | F (x+ε*Complex.I) ∈ K} ≤ C) :
    ∀ᵐ ξ:ℂ,∀ δ:ℝ,0 < δ → IsCompact (kz510 F k δ ξ):=by
  filter_upwards [kz531 hk hL hi hopen hcell htrace] with ξ hξ
  intro δ hδ
  exact kz512 (by linarith) hδ hc ht hp (hξ δ hδ)
lemma kz533 (g:kz140) {β:ℝ} (hβ:1 < β)
    (hfin:(∫⁻ z in kz459,
      ENNReal.ofReal (z.im^(β+1)*‖kz183 g z‖⁻¹^4)) < ∞) :
    ∀ᵐ ξ:ℂ,∀ δ:ℝ,0 < δ →
      IsCompact (kz510 (kz183 g) ((β+3)/4) δ ξ):=by
  obtain ⟨M,hM,hMb⟩:=kz506
  have ht:kz472 (kz183 g) (4*((β+3)/4)):=by
    convert kz477 g hβ hfin using 1; ring
  apply kz532 (by linarith:1 ≤ (β+3)/4)
    (by linarith:0 ≤ 1+4*M) (kz184 g).1.1.continuousOn
    (kz184 g).1.2 _ ht
    (fun _ hK _ hη => kz478 g hβ hfin hK hη)
    (fun _ _ _ _ _ hh hy hyy hxx hξ => kz509 hM hMb g hh hy hyy hxx hξ)
    (fun _ hK => kz505 g hβ hfin hK)
  intro z hz
  have hd:=((kz184 g).1.1.analyticAt (kz146.mem_nhds hz)).contDiffAt (n:=1)
  exact (hd.hasStrictDerivAt (by norm_num)).map_nhds_eq
    (kz91 kz146 (kz184 g).1 hz)
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
lemma compact_sublevels_iff_exhaustion.{u_1} {X:Type u_1} [TopologicalSpace X] [T2Space X]
    (K:CompactExhaustion X) {f:X → ℝ} (hf:Continuous f) :
    (∀ r:ℝ,IsCompact {x | f x ≤ r}) ↔
      ∀ n:ℕ,∃ m:ℕ,∀ x:X,x ∉ K m → (n:ℝ) ≤ f x:=by
  constructor
  · intro h n
    obtain ⟨m,hm⟩:=K.exists_superset_of_isCompact (h n)
    refine ⟨m,fun x hx => ?_⟩
    by_contra! hh
    exact hx (hm hh.le)
  · intro h r
    obtain ⟨n,hn⟩:=exists_nat_gt r
    obtain ⟨m,hm⟩:=h n
    apply (K.isCompact m).of_isClosed_subset (isClosed_le hf continuous_const)
    intro x hx
    by_contra hh
    exact (not_lt_of_ge ((hm x hh).trans hx)) hn
lemma measurableSet_compact_sublevels.{u_1,u_2} {P:Type u_1} {X:Type u_2}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    {f:P → X → ℝ} (hp:∀ x,Continuous (fun p => f p x))
    (hx:∀ p,Continuous (f p)) :
    MeasurableSet {p | ∀ r:ℝ,IsCompact {x | f p x ≤ r}}:=by
  let K:=CompactExhaustion.choice X
  have he:{p | ∀ r:ℝ,IsCompact {x | f p x ≤ r}} =
      ⋂ n:ℕ,⋃ m:ℕ,⋂ x:X,⋂ (_:x ∉ K m),{p | (n:ℝ) ≤ f p x}:=by
    ext p
    simp only [mem_ofPred_eq,mem_iInter,mem_iUnion]
    exact compact_sublevels_iff_exhaustion K (hx p)
  rw [he]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro m
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (hp x)
lemma compact_sublevels_iff_positive.{u_1} {X:Type u_1} [TopologicalSpace X] [T2Space X]
    {f:X → ℝ} (hf:Continuous f) :
    (∀ r:ℝ,IsCompact {x | f x ≤ r}) ↔ ∀ r:ℝ,0 < r → IsCompact {x | f x ≤ r}:=by
  refine ⟨fun h r _ => h r,fun h r => ?_⟩
  exact (h (max r 1) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))).of_isClosed_subset
    (isClosed_le hf continuous_const) (fun x hx => (show f x ≤ r from hx).trans (le_max_left _ _))
lemma kz534 {F:ℂ → ℂ} (k:ℝ) (ξ:ℂ)
    (hc:ContinuousOn F kz145) :
    (∀ δ:ℝ,0 < δ → IsCompact (kz510 F k δ ξ)) ↔
      ∀ r:ℝ,IsCompact {z:kz145 | ‖F z-ξ‖/z.val.im^k ≤ r}:=by
  have hy (z:kz145):0 < z.val.im^k:=Real.rpow_pos_of_pos z.property k
  have hcont:Continuous (fun z:kz145 => ‖F z-ξ‖/z.val.im^k):=by
    refine ((hc.domRestrict.sub continuous_const).norm).div ?_ (fun z => ne_of_gt (hy z))
    exact (Complex.continuous_im.comp continuous_subtype_val).rpow_const
      (fun z => Or.inl (ne_of_gt z.property))
  rw [compact_sublevels_iff_positive hcont]
  have he (r:ℝ) (hr:0 < r) :
      Subtype.val '' {z:kz145 | ‖F z-ξ‖/z.val.im^k ≤ r} =
        kz510 F k (1/r) ξ:=by
    ext z
    simp only [mem_image,mem_ofPred_eq,kz510]
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w.property,?_⟩
      rw [div_le_iff₀ (hy w)] at hw
      simpa only [one_div,div_inv_eq_mul,mul_comm r] using hw
    · rintro ⟨hz,hzv⟩
      refine ⟨⟨z,hz⟩,?_,rfl⟩
      rw [div_le_iff₀ (hy ⟨z,hz⟩)]
      simpa only [one_div,div_inv_eq_mul,mul_comm r] using hzv
  constructor
  · intro h r hr
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [he r hr]
    exact h (1/r) (by positivity)
  · intro h δ hδ
    have hh:=(h (1/δ) (by positivity)).image continuous_subtype_val
    rw [he (1/δ) (by positivity)] at hh
    simpa only [one_div_one_div] using hh
lemma measurableSet_compact_positive_superlevels.{u_1} {P:Type u_1}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    {F:P → ℂ → ℂ} (hF:Continuous (fun p:P × kz145 => F p.1 p.2)) (k:ℝ) :
    MeasurableSet {p:P × ℂ | ∀ δ:ℝ,0 < δ →
      IsCompact (kz510 (F p.1) k δ p.2)}:=by
  let f:(P × ℂ) → kz145 → ℝ:=fun p z => ‖F p.1 z-p.2‖/z.val.im^k
  have hc (p:P × ℂ):ContinuousOn (F p.1) kz145:=by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hF.comp (continuous_const.prodMk continuous_id)
  have he:{p:P × ℂ | ∀ δ:ℝ,0 < δ →
      IsCompact (kz510 (F p.1) k δ p.2)} =
      {p | ∀ r:ℝ,IsCompact {z:kz145 | f p z ≤ r}}:=by
    ext p
    exact kz534 k p.2 (hc p)
  rw [he]
  apply measurableSet_compact_sublevels
  · intro z
    exact (((hF.comp (continuous_fst.prodMk continuous_const)).sub continuous_snd).norm).div_const _
  · intro p
    refine (((hc p).domRestrict.sub continuous_const).norm).div ?_
      (fun z => ne_of_gt (Real.rpow_pos_of_pos z.property k))
    exact (Complex.continuous_im.comp continuous_subtype_val).rpow_const
      (fun z => Or.inl (ne_of_gt z.property))
lemma measurableSet_regular_parameters.{u_1,u_2,u_3} {P:Type u_1} {X:Type u_2} {Y:Type u_3}
    [TopologicalSpace P] [SigmaCompactSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [T2Space P]
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology P] [SecondCountableTopology Y]
    {F:P → X → Y} {J:P → X → ℝ}
    (hF:Continuous (fun q:P × X => F q.1 q.2))
    (hJ:Continuous (fun q:P × X => J q.1 q.2)) :
    MeasurableSet {q:P × Y | ∀ x,F q.1 x = q.2 → J q.1 x ≠ 0}:=by
  let Z:Set (P × X):={q | J q.1 q.2 = 0}
  let M:P × X → P × Y:=fun q => (q.1,F q.1 q.2)
  have hZ:IsSigmaCompact Z:=isSigmaCompact_univ.of_isClosed_subset
    (isClosed_eq hJ continuous_const) (subset_univ _)
  have hM:Continuous M:=continuous_fst.prodMk hF
  have him:MeasurableSet (M '' Z):=by
    obtain ⟨K,hK,he⟩:=hZ.image hM
    rw [← he]
    exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)
  have he:{q:P × Y | ∀ x,F q.1 x = q.2 → J q.1 x ≠ 0} = (M '' Z)ᶜ:=by
    ext q
    constructor
    · intro h ⟨⟨p,x⟩,hx,hq⟩
      have hp:p = q.1:=congrArg Prod.fst hq
      have hf:F p x = q.2:=congrArg Prod.snd hq
      exact h x (hp ▸ hf) (hp ▸ hx)
    · intro h x hx hJx
      exact h ⟨(q.1,x),hJx,Prod.ext rfl hx⟩
  rw [he]
  exact him.compl
lemma kz535 {f:ℂ → ℂ} {s:Set ℂ}
    (hf:∀ z ∈ s,DifferentiableAt ℝ f z) :
    ∀ᵐ ξ ∂volume,∀ z ∈ s,f z = ξ → LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0:=by
  let t:Set ℂ:={z | z ∈ s ∧ LinearMap.det (fderiv ℝ f z).toLinearMap = 0}
  have hz:volume (f '' t) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun z hz => (hf z hz.1).hasFDerivAt.hasFDerivWithinAt) (fun z hz => hz.2)
  filter_upwards [show ∀ᵐ ξ ∂volume,ξ ∉ f '' t from ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hz)] with ξ hξ z hzs hfz hdet
  exact hξ ⟨z,⟨hzs,hdet⟩,hfz⟩
lemma kz536 {f:ℂ → ℂ} {k δ:ℝ} (hk:0 ≤ k) (hδ:0 < δ) (ξ:ℂ) :
    {z | z ∈ kz145 ∧ ENNReal.ofReal δ ≤ kz214 f k ξ z} =
      kz510 f k δ ξ:=by
  ext z
  by_cases hz:z ∈ kz145
  · simp only [mem_ofPred_eq,kz510,show 0 < z.im from hz,hz,true_and]
    rw [kz354 hk hδ hz,kz241,
      div_le_iff₀ (Real.rpow_pos_of_pos hz k),inv_mul_eq_div]
  · simp only [mem_ofPred_eq,hz,false_and,kz510]
    exact iff_false_intro (fun h => hz h.1) |>.symm
lemma kz537 {k:ℝ} (hk:0 ≤ k) :
    MeasurableSet {p:kz140 × ℂ | kz215 (kz183 p.1) k p.2}:=by
  have hcompact:=measurableSet_compact_positive_superlevels kz187 k
  have hregular:=measurableSet_regular_parameters (F:=fun g (z:kz145) => kz204 (kz183 g) k z) (J:=fun g (z:kz145) => kz205 (kz183 g) k z) (kz372 k)
    (kz374 k)
  have he:{p:kz140 × ℂ | kz215 (kz183 p.1) k p.2} =
      {p:kz140 × ℂ | ∀ δ:ℝ,0 < δ →
        IsCompact (kz510 (kz183 p.1) k δ p.2)} ∩
      {p:kz140 × ℂ | ∀ z:kz145,
        kz204 (kz183 p.1) k z = p.2 → kz205 (kz183 p.1) k z ≠ 0}:=by
    ext p
    simp only [mem_inter_iff,mem_ofPred_eq,kz215]
    constructor
    · rintro ⟨hc,hr⟩
      exact ⟨fun δ hδ => (kz536 hk hδ p.2) ▸ hc δ hδ,
        fun z => hr z z.property⟩
    · rintro ⟨hc,hr⟩
      exact ⟨fun δ hδ => (kz536 hk hδ p.2).symm ▸ hc δ hδ,
        fun z hz => hr ⟨z,hz⟩⟩
  rw [he]
  exact hcompact.inter hregular
lemma kz538 (g:kz140) {β:ℝ} (hβ:1 < β)
    (hfin:(∫⁻ z in kz459,
      ENNReal.ofReal (z.im^(β+1)*‖kz183 g z‖⁻¹^4)) < ∞) :
    ∀ᵐ ξ:ℂ,kz215 (kz183 g) ((β+3)/4) ξ:=by
  have hc:=kz533 g hβ hfin
  have hr:=kz535 (s:=kz145)
    (fun z hz => kz216 (kz184 g).1 hz ((β+3)/4))
  filter_upwards [hc,hr] with ξ hc hr
  refine ⟨fun δ hδ => ?_,fun z hz hG => ?_⟩
  · rw [kz536 (by linarith:0 ≤ (β+3)/4) hδ]
    exact hc δ hδ
  · exact div_ne_zero (hr z hz hG) (pow_ne_zero _ (norm_ne_zero_iff.mpr
      (kz91 kz146 (kz184 g).1 hz)))
def kz539 (k:ℝ):Set (kz140 × kz145) :=
  {q | 0 < kz205 (kz183 q.1) k q.2 ∧
    kz215 (kz183 q.1) k (kz204 (kz183 q.1) k q.2)}
lemma kz540 {k:ℝ} (hk:0 ≤ k):MeasurableSet (kz539 k):=by
  have hJ:Measurable (fun q:kz140 × kz145 => kz205 (kz183 q.1) k q.2) :=
    (kz374 k).measurable
  have hG:=(kz537 hk).preimage (kz421 k).measurable
  change MeasurableSet {q:kz140 × kz145 | kz215 (kz183 q.1) k (kz204 (kz183 q.1) k q.2)} at hG
  exact (measurableSet_lt measurable_const hJ).inter hG
lemma kz541 {k:ℝ} (hk:0 < k) (q r:kz140 × kz145)
    (hg:kz215 (kz183 q.1) k (kz204 (kz183 q.1) k q.2))
    (he:kz419 k r = kz419 k q)
    (hJ:kz205 (kz183 r.1) k r.2 < 0)
    (hr:kz425 k (-1) r = kz425 k 1 q) :
    kz413 (kz183 q.1) k q.2 = r.2:=by
  rcases q with ⟨g,z⟩
  rcases r with ⟨h,w⟩
  have hp:h = g:=congrArg Prod.fst he
  subst h
  have hG:kz204 (kz183 g) k w = kz204 (kz183 g) k z:=congrArg Prod.snd he
  have hgw:kz215 (kz183 g) k (kz204 (kz183 g) k w):=hG ▸ hg
  rw [kz431 hk (-1) (g,w) hgw,
    kz431 hk 1 (g,z) hg,kz429,kz428,hG] at hr
  have heq:kz396 (kz375 (kz183 g) k) (kz409 (kz183 g) k (kz204 (kz183 g) k z)) w =
      kz396 (kz375 (kz183 g) k) (kz408 (kz183 g) k (kz204 (kz183 g) k z)) z:=by
    exact_mod_cast hr
  exact kz407 (kz411 (kz184 g).1 hk hg).2 ⟨w.property,hG,hJ⟩ heq
lemma kz542 {k:ℝ} (hk:0 < k) :
    Measurable (fun q:kz539 k => kz413 (kz183 q.val.1) k q.val.2):=by
  let B:=Classical.choice (kz422 k)
  let y:kz539 k → kz140 × ℂ:=fun q => kz419 k q.val
  let b:ℕ → kz539 k → kz140 × kz145:=fun n q => B.branch n (y q)
  let M:ℕ → Set (kz539 k):=fun n => {q | y q ∈ kz419 k '' B.part n ∧
    kz205 (kz183 (b n q).1) k (b n q).2 < 0 ∧
    kz425 k (-1) (b n q) = kz425 k 1 q.val}
  have hym:Measurable y:=(kz421 k).measurable.comp measurable_subtype_coe
  have hbm (n):Measurable (b n):=(B.measurable_branch n).comp hym
  apply measurable_branch_selection (b:=fun n q => (b n q).2.val) (M:=M)
  · intro n
    exact measurable_subtype_coe.comp ((hbm n).snd)
  · intro n
    exact ((B.measurable_image n).preimage hym).inter
      ((measurableSet_lt ((kz374 k).measurable.comp (hbm n)) measurable_const).inter
        (measurableSet_eq_fun ((kz426 k (-1)).comp (hbm n))
          ((kz426 k 1).comp measurable_subtype_coe)))
  · intro q
    obtain ⟨w,hw,_,hr⟩:=kz412 (kz184 q.val.1).1 hk q.property.2
      (show q.val.2.val ∈ kz408 (kz183 q.val.1) k (kz204 (kz183 q.val.1) k q.val.2) from
        ⟨q.val.2.property,rfl,q.property.1⟩)
    let r:kz140 × kz145:=(q.val.1,⟨w,hw.1⟩)
    have hG:kz419 k r = y q:=Prod.ext rfl hw.2.1
    have hns:r ∈ kz420 k:=ne_of_lt hw.2.2
    obtain ⟨n,hn⟩:=mem_iUnion.mp (B.cover.symm ▸ hns)
    have hb:b n q = r:=by
      dsimp [b]
      rw [← hG]
      exact B.left_inv n r hn
    refine ⟨n,⟨⟨r,hn,hG⟩,?_,?_⟩⟩
    · simpa only [hb] using hw.2.2
    · rw [hb,kz431 hk (-1) r (by simpa only [r,hw.2.1] using q.property.2),
        kz431 hk 1 q.val q.property.2,kz429,kz428]
      simpa only [r,hw.2.1] using congrArg (fun n:ℕ => (n:ℝ≥0∞)) hr
  · intro n q hq
    exact kz541 hk q.val (b n q) q.property.2
      (B.right_inv n (y q) hq.1).2 hq.2.1 hq.2.2
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
def kz543 (N:ℝ) (z w:ℂ):Prop :=
  z.im ≤ N*w.im ∧ w.im ≤ N*z.im ∧ |w.re-z.re| ≤ N*z.im
def kz544 (k N:ℝ):Set (kz140 × kz145) :=
  {q | q ∈ kz539 k ∧
    kz543 N q.2 (kz413 (kz183 q.1) k q.2)}
lemma kz545 {k:ℝ} (hk:0 < k) (N:ℝ) :
    MeasurableSet (kz544 k N):=by
  have hr:=kz542 hk
  have hz:Measurable (fun q:kz539 k => (q.val.2:ℂ)) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.snd)
  have hm:MeasurableSet {q:kz539 k |
      kz543 N q.val.2 (kz413 (kz183 q.val.1) k q.val.2)} :=
    (measurableSet_le (Complex.measurable_im.comp hz)
      (measurable_const.mul (Complex.measurable_im.comp hr))).inter
    ((measurableSet_le (Complex.measurable_im.comp hr)
      (measurable_const.mul (Complex.measurable_im.comp hz))).inter
    (measurableSet_le (((Complex.measurable_re.comp hr).sub (Complex.measurable_re.comp hz)).abs)
      (measurable_const.mul (Complex.measurable_im.comp hz))))
  have h:=(kz540 hk.le).subtype_image hm
  convert h using 1
  ext q
  simp only [kz544,mem_ofPred_eq,mem_image,Subtype.exists,exists_prop]
  aesop
lemma kz546 (N:ℝ) {t:ℂ} (ht:t ∈ kz145) (z w:ℂ) :
    kz543 N (kz148 t z) (kz148 t w) ↔ kz543 N z w:=by
  have him (v:ℂ):(kz148 t v).im = t.im*v.im:=by simp [kz148]
  have hre:(kz148 t w).re-(kz148 t z).re = t.im*(w.re-z.re):=by simp [kz148]; ring
  simp only [kz543,him,hre,abs_mul,abs_of_pos (show 0<t.im from ht)]
  simp only [show N*(t.im*w.im) = t.im*(N*w.im) from by ring,
    show N*(t.im*z.im) = t.im*(N*z.im) from by ring,
    mul_le_mul_iff_right₀ (show 0<t.im from ht)]
lemma kz547 (g:kz140) {k:ℝ} (hk:0 < k) (N:ℝ) (z:kz145) :
    (kz192 g z,kz440) ∈ kz544 k N ↔ (g,z) ∈ kz544 k N:=by
  have hJ:=kz444 g hk z
  have hG:=kz445 g hk z
  change (0 < kz205 (kz183 (kz192 g z)) k Complex.I ∧
    kz215 (kz183 (kz192 g z)) k (kz204 (kz183 (kz192 g z)) k Complex.I)) ∧ _ ↔
    (0 < kz205 (kz183 g) k z ∧ kz215 (kz183 g) k (kz204 (kz183 g) k z)) ∧ _
  rw [hJ,hG]
  apply and_congr_right
  intro h
  have he:=kz443 g hk z kz440 (by simpa only [kz440,kz149] using h.1)
    (by simpa only [kz440,kz149] using h.2)
  simp only [kz440,kz149] at he
  change kz543 N Complex.I (kz413 (kz183 (kz192 g z)) k Complex.I) ↔
    kz543 N z (kz413 (kz183 g) k z)
  rw [← kz546 N z.property Complex.I,kz149,he]
lemma kz548 {N M:ℝ} (hNM:N ≤ M) {z w:ℂ}
    (hz:z ∈ kz145) (hw:w ∈ kz145) (h:kz543 N z w) :
    kz543 M z w :=
  ⟨h.1.trans (mul_le_mul_of_nonneg_right hNM hw.le),
    h.2.1.trans (mul_le_mul_of_nonneg_right hNM hz.le),
    h.2.2.trans (mul_le_mul_of_nonneg_right hNM hz.le)⟩
lemma kz549 {z w:ℂ} (hz:z ∈ kz145) (hw:w ∈ kz145) :
    ∃ n:ℕ,kz543 (n+1) z w:=by
  obtain ⟨n,hn⟩:=exists_nat_gt (max (z.im/w.im) (max (w.im/z.im) (|w.re-z.re|/z.im)))
  refine ⟨n,?_,?_,?_⟩
  · exact (div_le_iff₀ hw).mp ((le_max_left _ _).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_left _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_right _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
lemma kz550 {k:ℝ} (hk:0 < k) {N M:ℝ} (hNM:N ≤ M) :
    kz544 k N ⊆ kz544 k M:=by
  rintro ⟨g,z⟩ ⟨hp,hw⟩
  exact ⟨hp,kz548 hNM z.property
    (kz414 (kz184 g).1 hk z.property hp.1 hp.2).1 hw⟩
lemma kz551 {k:ℝ} (hk:0 < k) :
    (⋃ n:ℕ,kz544 k (n+1)) = kz539 k:=by
  ext q
  constructor
  · rintro ⟨_,⟨n,rfl⟩,hq⟩
    exact hq.1
  · intro hq
    obtain ⟨n,hn⟩:=kz549 q.2.property
      (kz414 (kz184 q.1).1 hk q.2.property hq.1 hq.2).1
    exact mem_iUnion.mpr ⟨n,hq,hn⟩
def kz552 (g:kz140) (k N:ℝ):Set ℂ :=
  {z | z ∈ kz145 ∧ 0 < kz205 (kz183 g) k z ∧
    kz215 (kz183 g) k (kz204 (kz183 g) k z) ∧
    kz543 N z (kz413 (kz183 g) k z)}
lemma kz553 (g:kz140) (k N:ℝ) (z:kz145) :
    z.val ∈ kz552 g k N ↔ (g,z) ∈ kz544 k N:=by
  simp only [kz552,kz544,kz539,mem_ofPred_eq,z.property,true_and,and_assoc]
lemma kz554 (g:kz140) {k:ℝ} (hk:0 < k) (N:ℝ) :
    MeasurableSet (kz552 g k N):=by
  apply kz448
  have hm:Measurable (fun z:kz145 => (g,z)):=measurable_const.prodMk measurable_id
  have h:=(kz545 hk N).preimage hm
  convert h using 1
  ext z
  exact and_assoc.symm
def kz555 (R a b:ℝ):Set ℂ:={z | |z.re| ≤ R ∧ a ≤ z.im ∧ z.im ≤ b}
lemma kz556 (R a b:ℝ):MeasurableSet (kz555 R a b) :=
  (measurableSet_le Complex.measurable_re.abs measurable_const).inter
    ((measurableSet_le measurable_const Complex.measurable_im).inter
      (measurableSet_le Complex.measurable_im measurable_const))
lemma kz557 {N R Y:ℝ} (hN:1 ≤ N) {z w:ℂ}
    (hz:z ∈ kz555 R 1 Y) (hw:kz543 N z w) :
    w ∈ kz555 (R+N*Y) (1/N) (N*Y):=by
  have hn:0 < N:=lt_of_lt_of_le zero_lt_one hN
  have hab:|w.re| ≤ |z.re|+|w.re-z.re|:=by
    calc |w.re| = |z.re+(w.re-z.re)|:=by congr 1; ring
         _ ≤ |z.re|+|w.re-z.re|:=abs_add_le _ _
  refine ⟨hab.trans (add_le_add hz.1 (hw.2.2.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le))),?_,
    hw.2.1.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le)⟩
  rw [div_le_iff₀ hn]
  nlinarith [hw.1,hz.2.1]
lemma fiberSum_mul_indicator.{u_1,u_2} {X:Type u_1} {Y:Type u_2} (f:X → Y) (s t:Set X)
    (u:X → ℝ≥0∞) (y:Y) :
    fiberSum f s (fun x => u x * t.indicator 1 x) y = fiberSum f (s ∩ t) u y:=by
  classical
  rw [fiberSum,fiberSum,tsum_subtype {x | x ∈ s ∧ f x = y} (fun x => u x * t.indicator 1 x),
    tsum_subtype {x | x ∈ s ∩ t ∧ f x = y} u]
  apply tsum_congr
  intro x
  by_cases hs:x ∈ s <;> by_cases ht:x ∈ t <;> by_cases hy:f x = y <;>
    simp [hs,ht,hy]
lemma kz558 (g:kz140) {β k N R Y:ℝ} (hk:0 < k)
    (hb:β-1 = 4*(k-1)) (hN:1 ≤ N) :
    (∫⁻ z in kz145,kz452 g β z * ENNReal.ofReal (kz205 (kz183 g) k z) *
      (kz552 g k N ∩ kz555 R 1 Y).indicator 1 z) ≤
    ∫⁻ z in kz145,kz452 g β z * ENNReal.ofReal (-kz205 (kz183 g) k z) *
      (kz555 (R+N*Y) (1/N) (N*Y)).indicator 1 z:=by
  let S:=kz552 g k N ∩ kz555 R 1 Y
  let T:=kz555 (R+N*Y) (1/N) (N*Y)
  have hs:MeasurableSet S:=(kz554 g hk N).inter (kz556 R 1 Y)
  have ht:MeasurableSet T:=kz556 _ _ _
  have hp:=kz456 g β k 1 (by norm_num) (measurable_const.indicator hs:Measurable (S.indicator (1:ℂ → ℝ≥0∞)))
  have hn:=kz456 g β k (-1) (by norm_num) (measurable_const.indicator ht:Measurable (T.indicator (1:ℂ → ℝ≥0∞)))
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  apply le_trans hp.le
  apply le_trans ?_ hn.symm.le
  apply lintegral_mono
  intro ξ
  apply le_trans (fiberSum_mul_indicator (kz204 (kz183 g) k) (kz449 g k 1) S (kz453 g β) ξ).le
  apply le_trans ?_ (fiberSum_mul_indicator (kz204 (kz183 g) k) (kz449 g k (-1)) T (kz453 g β) ξ).symm.le
  apply fiberSum_mono_injective (kz413 (kz183 g) k) ξ
  · intro z hz hG
    have hsz:=hz.2.1
    have hpair:=kz414 (kz184 g).1 hk hsz.1 hsz.2.1 hsz.2.2.1
    exact ⟨⟨⟨hpair.1,by simpa only [neg_one_mul] using neg_pos.mpr hpair.2.2.1⟩,
      kz557 hN hz.2.2 hsz.2.2.2⟩,hpair.2.1.trans hG⟩
  · apply (kz415 (kz184 g).1 hk).mono
    intro z hz
    exact ⟨hz.1.2.1.1,hz.1.2.1.2.1,hz.1.2.1.2.2.1⟩
  · intro z hz _
    exact kz458 g hk hb hz.2.1.1 hz.2.1.2.1 hz.2.1.2.2.1
lemma kz559 (g:kz140) {k:ℝ} (hk:0 < k) :
    MeasurableSet {z:ℂ | z ∈ kz145 ∧ ¬kz215 (kz183 g) k (kz204 (kz183 g) k z)}:=by
  apply kz448
  have hm:Measurable (fun z:kz145 => (g,kz204 (kz183 g) k z)) :=
    (continuous_const.prodMk ((kz372 k).comp
      (show Continuous (fun z:kz145 => (g,z)) from continuous_const.prodMk continuous_id))).measurable
  exact ((kz537 hk.le).preimage hm).compl
lemma kz560 (g:kz140) {β k:ℝ} (hk:0 < k)
    (hg:∀ᵐ ξ:ℂ,kz215 (kz183 g) k ξ) :
    (∫⁻ z in kz145,kz452 g β z * ENNReal.ofReal (kz205 (kz183 g) k z) *
      {z:ℂ | z ∈ kz145 ∧ ¬kz215 (kz183 g) k (kz204 (kz183 g) k z)}.indicator 1 z) = 0:=by
  have hs:=kz559 g hk
  have he:=kz456 g β k 1 (by norm_num)
    (measurable_const.indicator hs:Measurable ({z:ℂ | z ∈ kz145 ∧ ¬kz215 (kz183 g) k (kz204 (kz183 g) k z)}.indicator (1:ℂ → ℝ≥0∞)))
  simp only [one_mul] at he
  refine he.trans ?_
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hg] with ξ hξ
  unfold fiberSum
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  have hn:z.val ∉ {z:ℂ | z ∈ kz145 ∧ ¬kz215 (kz183 g) k (kz204 (kz183 g) k z)}:=by
    rintro ⟨_,hbad⟩
    exact hbad (z.property.2.symm ▸ hξ)
  exact (congrArg (kz453 g β z * ·) (indicator_of_notMem (f:=(1:ℂ → ℝ≥0∞)) hn)).trans (mul_zero _)
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
def kz561 (z w:kz145):kz145:=⟨kz148 z w,kz152 z.2 w.2⟩
def kz562 (x y:ℝ) (hy:0 < y):kz145 :=
  ⟨(x:ℂ)+(y:ℂ)*Complex.I,by simpa [kz145]⟩
def kz563 (x:ℝ):kz145:=kz562 x 1 zero_lt_one
lemma kz564 (x y u v:ℝ) (hy:0 < y) (hv:0 < v) :
    kz561 (kz562 x y hy) (kz562 u v hv) = kz562 (x+y*u) (y*v) (mul_pos hy hv):=by
  apply Subtype.ext
  apply Complex.ext <;> simp [kz561,kz562,kz148]
lemma continuous_halfPoint.{u_1} {Y:Type u_1} [TopologicalSpace Y] {x y:Y → ℝ}
    (hx:Continuous x) (hy:Continuous y) (hp:∀ a,0 < y a) :
    Continuous (fun a => kz562 (x a) (y a) (hp a)) :=
  ((Complex.continuous_ofReal.comp hx).add ((Complex.continuous_ofReal.comp hy).mul continuous_const)).subtype_mk _
lemma kz565 (g:kz140):kz192 g kz440 = g:=by
  apply kz195
  intro z hz
  rw [kz193 _ _ hz]
  simp [kz155,kz440,(kz184 g).2.1,(kz184 g).2.2]
lemma kz566 (g:kz140):kz198 g kz440 = 1:=by
  simp [kz198,kz160,kz440,(kz184 g).2.2]
seal kz192
def kz567 (z:kz145):C(kz140,ℝ) :=
  ⟨fun g => kz198 g z,by
    have hc:Continuous (fun g:kz140 => (g,z)):=continuous_id.prodMk continuous_const
    exact kz200.comp hc⟩
def kz568 (z:kz145):C(kz140,kz140) :=
  ⟨fun g => kz192 g z,by
    have hc:Continuous (fun g:kz140 => (g,z)):=continuous_id.prodMk continuous_const
    exact kz194.comp hc⟩
def kz569 (z:kz145):C(kz140,ℝ) →L[ℝ] C(kz140,ℝ) :=
  (ContinuousLinearMap.mul ℝ C(kz140,ℝ) (kz567 z)).comp (ContinuousMap.compCLM ℝ ℝ (kz568 z))
lemma kz570 (z:kz145) (f:C(kz140,ℝ)) (g:kz140) :
    kz569 z f g = kz198 g z * f (kz192 g z):=rfl
lemma kz571 (z:kz145) (f:C(kz140,ℝ)) (hf:0 ≤ f) :
    0 ≤ kz569 z f:=fun g => mul_nonneg (kz199 g z).le (hf _)
lemma kz572 (z w:kz145) :
    kz569 z * kz569 w = kz569 (kz561 z w):=by
  ext f g
  change kz198 g z * (kz198 (kz192 g z) w * f (kz192 (kz192 g z) w)) = _
  rw [← mul_assoc,kz201,kz197]
  rfl
lemma kz573:kz569 kz440 = 1:=by
  ext f g
  simp only [kz570,kz566,kz565,one_mul]
  rfl
lemma kz574 (f:C(kz140,ℝ)) :
    Continuous (fun z:kz145 => kz569 z f):=by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hw:Continuous (fun p:kz145 × kz140 => kz198 p.2 p.1) :=
    kz200.comp (continuous_swap:Continuous (Prod.swap:kz145 × kz140 → kz140 × kz145))
  have ht:Continuous (fun p:kz145 × kz140 => kz192 p.2 p.1) :=
    kz194.comp (continuous_swap:Continuous (Prod.swap:kz145 × kz140 → kz140 × kz145))
  exact hw.mul (f.continuous.comp ht)
lemma kz575 {z:kz145} {B:ℝ} (hB:0 ≤ B)
    (hw:∀ g:kz140,kz198 g z ≤ B):‖kz569 z‖ ≤ B:=by
  apply (kz569 z).opNorm_le_bound hB
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg f))).mpr
  intro g
  rw [kz570,norm_mul,Real.norm_of_nonneg (kz199 g z).le]
  exact mul_le_mul (hw g) (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _) hB
lemma kz576:EqOn (kz183 kz418) kz416 kz145 :=
  kz186 kz417
lemma kz577 (z:kz145):kz198 kz418 z = 1:=by
  have hd:=kz576.deriv kz146 z.2
  have hi:deriv kz416 z = 1:=((hasDerivAt_id (z:ℂ)).sub_const Complex.I).deriv
  simp [kz198,kz160,hd,hi]
lemma kz578 (z:kz145):kz192 kz418 z = kz418:=by
  apply kz195
  intro w hw
  rw [kz193 _ _ hw,kz196 kz576 z.2 hw,kz576 hw]
  have hd:deriv kz416 z = 1:=((hasDerivAt_id (z:ℂ)).sub_const Complex.I).deriv
  have he:(z.val.re:ℂ)+(z.val.im:ℂ)*Complex.I = z:=by apply Complex.ext <;> simp
  dsimp [kz155,kz416,kz148]
  rw [hd,mul_one]
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr (ne_of_gt z.2))).mpr
  linear_combination he
def kz579:kz145:=kz562 (-1/2) (1/2) (by norm_num)
def kz580:kz145:=kz562 (1/2) (1/2) (by norm_num)
def kz581:C(kz140,ℝ) →L[ℝ] C(kz140,ℝ) :=
  (1/2:ℝ) • (kz569 kz579+kz569 kz580)
lemma kz582 (f:C(kz140,ℝ)) (hf:0 ≤ f):0 ≤ kz581 f:=by
  intro g
  change 0 ≤ (1/2:ℝ)*(kz569 kz579 f g+kz569 kz580 f g)
  exact mul_nonneg (by norm_num) (add_nonneg (kz571 _ f hf g) (kz571 _ f hf g))
lemma kz583 (f:C(kz140,ℝ)):kz581 f kz418 = f kz418:=by
  change (1/2:ℝ)*(kz569 kz579 f kz418+kz569 kz580 f kz418) = _
  simp only [kz570,kz577,kz578,one_mul]
  ring
lemma kz584 (n:ℕ):(kz581^n) 1 kz418 = 1:=by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',mul_apply_eq_comp,kz583] using ih
lemma kz585 (n:ℕ):1 ≤ ‖kz581^n‖:=by
  have hv:=(ContinuousMap.norm_coe_le_norm ((kz581^n) 1) kz418).trans
    ((kz581^n).le_opNorm 1)
  simpa only [kz584,norm_one,mul_one] using hv
lemma kz586 {z:ℂ} (hz:z ∈ kz145) :
    (1-‖kz162 z‖^2)*‖z+Complex.I‖^2 = 4*z.im:=by
  have hd:‖z+Complex.I‖ ≠ 0:=norm_ne_zero_iff.mpr (kz164 hz)
  rw [kz162,norm_div,div_pow]
  field_simp
  rw [Complex.sq_norm,Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring
lemma kz587 (g:kz140) (z:kz145) :
    ‖deriv (kz183 g) z‖ = 4*‖deriv (kz135 g.1) (kz162 z)‖/‖z.val+Complex.I‖^2:=by
  have hd:=(kz177 g.2.1.1 z.2).deriv
  rw [kz183]
  rw [hd,norm_div,norm_mul,norm_neg,norm_pow]
  norm_num
lemma kz588 (g:kz140) (z:kz145) :
    ‖kz160 (kz183 g) z‖ = ‖z.val+Complex.I‖^2/
      (4*‖deriv (kz135 g.1) (kz162 z)‖):=by
  rw [kz160,norm_inv,kz587,inv_div]
lemma kz589 (g:kz140) (z:kz145) :
    ‖kz160 (kz183 g) z‖ ≤ ‖z.val+Complex.I‖^4/z.val.im:=by
  let r:=‖kz162 z‖
  let D:=‖z.val+Complex.I‖^2
  let a:=‖deriv (kz135 g.1) (kz162 z)‖
  have hr0:0 ≤ r:=norm_nonneg _
  have hr1:r < 1:=by simpa [r,disk] using kz166 z.2
  have hD0:0 < D:=sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (kz164 z.2))
  have ha0:0 < a:=norm_pos_iff.mpr (kz91 Metric.isOpen_ball g.2.1 (kz166 z.2))
  have he:(1-r^2)*D = 4*z.val.im:=kz586 z.2
  have hlo:(1-r)/(1+r)^3 ≤ a:=(kz122 g.2 (kz166 z.2)).1
  have hden:0 < (1+r)^3:=pow_pos (by linarith) 3
  have h8:(1+r)^3 ≤ 8:=by nlinarith [sq_nonneg (1-r),sq_nonneg r,mul_nonneg hr0 (sq_nonneg (1-r))]
  have hl:1-r ≤ 8*a:=by
    have hh:=(div_le_iff₀ hden).mp hlo
    nlinarith [mul_le_mul_of_nonneg_left h8 ha0.le]
  have hD:2*z.val.im ≤ (1-r)*D:=by
    have hh:(1-r^2) ≤ 2*(1-r):=by nlinarith [sq_nonneg (1-r)]
    nlinarith [mul_le_mul_of_nonneg_right hh hD0.le]
  have hDa:z.val.im ≤ 4*a*D:=by
    have hh:=mul_le_mul_of_nonneg_right hl hD0.le
    nlinarith
  rw [kz588]
  change D/(4*a) ≤ ‖z.val+Complex.I‖^4/z.val.im
  rw [div_le_div_iff₀ (by positivity:0 < 4*a) z.2]
  have hh:=mul_le_mul_of_nonneg_right hDa hD0.le
  dsimp [D] at *
  nlinarith
lemma kz590 (g:kz140) {C₀:ℝ} (hC:0 ≤ C₀) (z:kz145)
    (hx:|z.val.re| ≤ C₀) (hy:z.val.im ≤ 1) :
    ‖kz160 (kz183 g) z‖ ≤ (C₀^2+4)^2/z.val.im:=by
  apply (kz589 g z).trans
  apply div_le_div_of_nonneg_right _ z.2.le
  have hD:‖z.val+Complex.I‖^2 = z.val.re^2+(z.val.im+1)^2:=by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hxr:z.val.re^2 ≤ C₀^2:=by nlinarith [sq_abs z.val.re,(sq_le_sq₀ (abs_nonneg _) hC).mpr hx]
  have hDle:‖z.val+Complex.I‖^2 ≤ C₀^2+4:=by
    have hz0:0 < z.val.im:=z.2
    rw [hD]
    nlinarith [mul_nonneg hz0.le (sub_nonneg.mpr hy)]
  nlinarith [sq_nonneg (‖z.val+Complex.I‖^2-(C₀^2+4))]
lemma kz591 (g:kz140) (z:kz145)
    (hx:|z.val.re| ≤ 2) (hy:z.val.im ≤ 1) :
    ‖kz160 (kz183 g) z‖ ≤ 64/z.val.im:=by
  convert kz590 g (by norm_num:(0:ℝ) ≤ 2) z hx hy using 1
  norm_num
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
seal kz192
lemma positive_operator_mono.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f):Monotone L:=by
  intro f g h
  have:=hp (g-f) (sub_nonneg.mpr h)
  simpa only [map_sub,sub_nonneg] using this
lemma positive_operator_abs_bound.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f) (f:C(X,ℝ)) (x:X) :
    |L f x| ≤ ‖f‖ * L 1 x:=by
  have hlo:(-‖f‖) • (1:C(X,ℝ)) ≤ f:=by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).1
  have hhi:f ≤ ‖f‖ • (1:C(X,ℝ)):=by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).2
  have h1:=positive_operator_mono L hp hlo x
  have h2:=positive_operator_mono L hp hhi x
  simp only [map_smul,ContinuousMap.toFun_eq_coe,ContinuousMap.smul_apply,smul_eq_mul,neg_mul] at h1 h2
  exact abs_le.mpr ⟨h1,h2⟩
lemma positive_operator_norm.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f):‖L‖ = ‖L 1‖:=by
  apply le_antisymm
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro f
    apply (ContinuousMap.norm_le (L f) (by positivity)).mpr
    intro x
    calc
      ‖L f x‖ = |L f x|:=Real.norm_eq_abs _
      _ ≤ ‖f‖ * L 1 x:=positive_operator_abs_bound L hp f x
      _ ≤ ‖f‖ * ‖L 1‖:=mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self _) (ContinuousMap.norm_coe_le_norm (L 1) x)) (norm_nonneg _)
      _ = ‖L 1‖ * ‖f‖:=mul_comm _ _
  · simpa using L.le_opNorm (1:C(X,ℝ))
lemma positive_operator_pow.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f) (n:ℕ) :
    ∀ f,0 ≤ f → 0 ≤ (L^n) f:=by
  induction n with
  | zero => simp
  | succ n ih =>
    intro f hf
    simpa only [pow_succ',mul_apply_eq_comp] using hp ((L^n) f) (ih f hf)
lemma log_norm_pow_subadditive.{u_1} {A:Type u_1} [NormedRing A] (a:A)
    (h:∀ n:ℕ,1 ≤ ‖a^n‖):Subadditive (fun n => Real.log ‖a^n‖):=by
  intro m n
  change Real.log ‖a^(m+n)‖ ≤ _
  rw [pow_add]
  calc
    Real.log ‖a^m*a^n‖ ≤ Real.log (‖a^m‖*‖a^n‖) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (by simpa [pow_add] using h (m+n))) (norm_mul_le _ _)
    _ = Real.log ‖a^m‖ + Real.log ‖a^n‖:=Real.log_mul (by linarith [h m]) (by linarith [h n])
lemma log_norm_pow_bddBelow.{u_1} {A:Type u_1} [NormedRing A] (a:A)
    (h:∀ n:ℕ,1 ≤ ‖a^n‖):BddBelow (range (fun n:ℕ => Real.log ‖a^n‖/n)):=by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  exact div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n)
def growthLog.{u_1} {A:Type u_1} [NormedRing A] (a:A) (h:∀ n:ℕ,1 ≤ ‖a^n‖):ℝ :=
  (log_norm_pow_subadditive a h).lim
def growthRate.{u_1} {A:Type u_1} [NormedRing A] (a:A) (h:∀ n:ℕ,1 ≤ ‖a^n‖):ℝ :=
  Real.exp (growthLog a h)
lemma tendsto_log_norm_pow.{u_1} {A:Type u_1} [NormedRing A] (a:A)
    (h:∀ n:ℕ,1 ≤ ‖a^n‖) :
    Tendsto (fun n:ℕ => Real.log ‖a^n‖/n) atTop (𝓝 (growthLog a h)) :=
  (log_norm_pow_subadditive a h).tendsto_lim (log_norm_pow_bddBelow a h)
lemma growthLog_nonneg.{u_1} {A:Type u_1} [NormedRing A] (a:A)
    (h:∀ n:ℕ,1 ≤ ‖a^n‖):0 ≤ growthLog a h :=
  ge_of_tendsto (tendsto_log_norm_pow a h)
    (Eventually.of_forall (fun n => div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n)))
lemma growthRate_ge_one.{u_1} {A:Type u_1} [NormedRing A] (a:A)
    (h:∀ n:ℕ,1 ≤ ‖a^n‖):1 ≤ growthRate a h :=
  Real.one_le_exp_iff.mpr (growthLog_nonneg a h)
lemma norm_pow_eventually_le.{u_1} {A:Type u_1} [NormedRing A] (a:A)
    (h:∀ n:ℕ,1 ≤ ‖a^n‖) {r:ℝ} (hr:growthRate a h < r) :
    ∀ᶠ n:ℕ in atTop,‖a^n‖ ≤ r^n:=by
  have hr0:0 < r:=lt_of_lt_of_le zero_lt_one ((growthRate_ge_one a h).trans hr.le)
  have hlog:growthLog a h < Real.log r:=by
    rwa [← Real.exp_lt_exp,Real.exp_log hr0]
  filter_upwards [(tendsto_log_norm_pow a h).eventually (gt_mem_nhds hlog),
    eventually_gt_atTop (0:ℕ)] with n hn hn0
  have hnR:(0:ℝ) < n:=by exact_mod_cast hn0
  have he:Real.log ‖a^n‖ ≤ (n:ℝ)*Real.log r:=by
    have:=(div_lt_iff₀ hnR).mp hn
    linarith
  have:=Real.exp_le_exp.mpr he
  simpa only [Real.exp_log (lt_of_lt_of_le zero_lt_one (h n)),Real.exp_nat_mul,
    Real.exp_log hr0] using this
lemma summable_scaled_pow.{u_1} {A:Type u_1} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a:A) (h:∀ n:ℕ,1 ≤ ‖a^n‖) {τ:ℝ} (hτ:growthRate a h < τ) :
    Summable (fun n:ℕ => (τ⁻¹)^n • a^n):=by
  obtain ⟨r,hr,hrτ⟩:=exists_between hτ
  have hr0:0 < r:=lt_of_lt_of_le zero_lt_one ((growthRate_ge_one a h).trans hr.le)
  have hτ0:0 < τ:=hr0.trans hrτ
  apply Summable.of_norm_bounded_eventually (g:=fun n:ℕ => (r/τ)^n)
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hτ0).mpr hrτ))
  have he:=norm_pow_eventually_le a h hr
  rw [← Nat.cofinite_eq_atTop] at he
  filter_upwards [he] with n hn
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity:0 ≤ (τ⁻¹)^n)]
  calc
    (τ⁻¹)^n * ‖a^n‖ ≤ (τ⁻¹)^n*r^n:=mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (r/τ)^n:=by rw [← mul_pow]; congr 1; ring
lemma growthRate_le_of_pow_bound.{u_1} {A:Type u_1} [NormedRing A] (a:A)
    (h:∀ n:ℕ,1 ≤ ‖a^n‖) {M c:ℝ} (hM:0 < M) (_hc:0 ≤ c)
    (hb:∀ n:ℕ,‖a^n‖ ≤ M*c^n):growthRate a h ≤ c:=by
  have hc0:0 < c:=by
    have:=hb 1
    have:=h 1
    simp only [pow_one] at *
    nlinarith
  have ht:Tendsto (fun n:ℕ => Real.log M/(n:ℝ)+Real.log c) atTop (𝓝 (Real.log c)):=by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const (Real.log c)
  have hl:growthLog a h ≤ Real.log c:=by
    apply le_of_tendsto_of_tendsto (tendsto_log_norm_pow a h) ht
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hnR:(0:ℝ) < n:=by exact_mod_cast hn
    have hlog:=Real.log_le_log (lt_of_lt_of_le zero_lt_one (h n)) (hb n)
    rw [Real.log_mul hM.ne' (pow_pos hc0 n).ne',Real.log_pow] at hlog
    calc
      Real.log ‖a^n‖/(n:ℝ) ≤ (Real.log M+(n:ℝ)*Real.log c)/(n:ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
      _ = Real.log M/(n:ℝ)+Real.log c:=by field_simp
  simpa [growthRate,Real.exp_log hc0] using Real.exp_le_exp.mpr hl
def positiveResolvent.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (τ:ℝ):C(X,ℝ) →L[ℝ] C(X,ℝ) :=
  ∑' n:ℕ,(τ⁻¹)^n • L^n
lemma summable_resolvent_eval.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (h:∀ n:ℕ,1 ≤ ‖L^n‖)
    {τ:ℝ} (hτ:growthRate L h < τ) (f:C(X,ℝ)) (x:X) :
    Summable (fun n:ℕ => (τ⁻¹)^n * (L^n) f x):=by
  let e:(C(X,ℝ) →L[ℝ] C(X,ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R:=ℝ) x).comp (ContinuousLinearMap.apply ℝ C(X,ℝ) f)
  have hs:=e.summable (summable_scaled_pow L h hτ)
  simpa only [e,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    smul_apply,ContinuousMap.evalCLM_apply,ContinuousMap.smul_apply,smul_eq_mul] using hs
lemma positiveResolvent_eval.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (h:∀ n:ℕ,1 ≤ ‖L^n‖)
    {τ:ℝ} (hτ:growthRate L h < τ) (f:C(X,ℝ)) (x:X) :
    positiveResolvent L τ f x = ∑' n:ℕ,(τ⁻¹)^n * (L^n) f x:=by
  let e:(C(X,ℝ) →L[ℝ] C(X,ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R:=ℝ) x).comp (ContinuousLinearMap.apply ℝ C(X,ℝ) f)
  exact e.map_tsum (summable_scaled_pow L h hτ)
lemma positiveResolvent_nonneg.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f)
    (h:∀ n:ℕ,1 ≤ ‖L^n‖) {τ:ℝ} (hτ:growthRate L h < τ) :
    ∀ f,0 ≤ f → 0 ≤ positiveResolvent L τ f:=by
  have ht:0 < τ:=lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  intro f hf x
  change 0 ≤ positiveResolvent L τ f x
  rw [positiveResolvent_eval L h hτ]
  exact tsum_nonneg (fun n => mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) n)
    (positive_operator_pow L hp n f hf x))
lemma positiveResolvent_ge_one.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f)
    (h:∀ n:ℕ,1 ≤ ‖L^n‖) {τ:ℝ} (hτ:growthRate L h < τ) :
    1 ≤ positiveResolvent L τ 1:=by
  have ht:0 < τ:=lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  intro x
  change 1 ≤ positiveResolvent L τ 1 x
  rw [positiveResolvent_eval L h hτ]
  have hn (n:ℕ):0 ≤ (τ⁻¹)^n * (L^n) (1:C(X,ℝ)) x :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) n) (positive_operator_pow L hp n 1 (by intro; simp) x)
  simpa using (summable_resolvent_eval L h hτ 1 x).le_tsum 0 (fun n _ => hn n)
lemma positiveResolvent_mul.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (h:∀ n:ℕ,1 ≤ ‖L^n‖)
    {τ:ℝ} (hτ:growthRate L h < τ) :
    positiveResolvent L τ * L = τ • (positiveResolvent L τ-1) ∧
    L * positiveResolvent L τ = τ • (positiveResolvent L τ-1):=by
  have ht:τ ≠ 0:=ne_of_gt (lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le))
  have hs:=summable_scaled_pow L h hτ
  have htail : ∑' n:ℕ,(τ⁻¹)^(n+1) • L^(n+1) = positiveResolvent L τ-1:=by
    have he:=hs.sum_add_tsum_nat_add 1
    simpa [positiveResolvent] using eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he)
  have he (n:ℕ):τ • ((τ⁻¹)^(n+1) • L^(n+1)) = (τ⁻¹)^n • (L^n*L):=by
    rw [smul_smul,pow_succ,pow_succ]
    congr 1
    field_simp
  constructor
  · change (∑' n:ℕ,(τ⁻¹)^n • L^n)*L = _
    rw [show (∑' n:ℕ,(τ⁻¹)^n • L^n)*L =
      ∑' n:ℕ,((τ⁻¹)^n • L^n)*L from
      ((ContinuousLinearMap.compL ℝ C(X,ℝ) C(X,ℝ) C(X,ℝ)).flip L).map_tsum hs,
      ← htail,← tsum_const_smul'']
    exact tsum_congr (fun n => by
      rw [he]; change ((τ⁻¹)^n • L^n).comp L = (τ⁻¹)^n • ((L^n).comp L)
      exact ContinuousLinearMap.smul_comp _ _ _)
  · change L*(∑' n:ℕ,(τ⁻¹)^n • L^n) = _
    rw [show L*(∑' n:ℕ,(τ⁻¹)^n • L^n) =
      ∑' n:ℕ,L*((τ⁻¹)^n • L^n) from
      ((ContinuousLinearMap.compL ℝ C(X,ℝ) C(X,ℝ) C(X,ℝ)) L).map_tsum hs,
      ← htail,← tsum_const_smul'']
    apply tsum_congr
    intro n
    rw [he]
    change L.comp ((τ⁻¹)^n • L^n) = (τ⁻¹)^n • ((L^n).comp L)
    rw [ContinuousLinearMap.comp_smul]
    congr 1
    change L * L^n = L^n * L
    rw [← pow_succ',← pow_succ]
lemma positive_operator_pow_bound.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f)
    {g:C(X,ℝ)} (hg:1 ≤ g) {c:ℝ} (hc:0 ≤ c) (hLg:L g ≤ c • g) (n:ℕ) :
    ‖L^n‖ ≤ ‖g‖*c^n:=by
  have hiter:∀ n:ℕ,(L^n) g ≤ c^n • g:=by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1:=positive_operator_mono L hp ih
      have h2:c^n • L g ≤ c^n • (c • g):=smul_le_smul_of_nonneg_left hLg (pow_nonneg hc n)
      rw [map_smul] at h1
      have h3:=h1.trans h2
      simpa only [pow_succ',mul_apply_eq_comp,smul_smul,mul_comm] using h3
  rw [positive_operator_norm (L^n) (positive_operator_pow L hp n)]
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (pow_nonneg hc n))).mpr
  intro x
  have hn:=positive_operator_pow L hp n 1 (by intro; simp) x
  have h1:=positive_operator_mono (L^n) (positive_operator_pow L hp n) hg x
  have h2:=hiter n x
  change (L^n) g x ≤ c^n*g x at h2
  calc
    ‖(L^n) 1 x‖ = (L^n) 1 x:=Real.norm_of_nonneg hn
    _ ≤ c^n*g x:=h1.trans h2
    _ ≤ c^n*‖g‖:=mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x)) (pow_nonneg hc n)
    _ = ‖g‖*c^n:=mul_comm _ _
lemma positiveResolvent_norm_bound.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f)
    (h:∀ n:ℕ,1 ≤ ‖L^n‖) {τ:ℝ} (hτ:growthRate L h < τ) :
    1 ≤ ‖positiveResolvent L τ 1‖ ∧
    τ / ‖positiveResolvent L τ 1‖ ≤ τ - growthRate L h:=by
  let g:=positiveResolvent L τ 1
  have hg:1 ≤ g:=positiveResolvent_ge_one L hp h hτ
  have hM:1 ≤ ‖g‖:=by
    obtain ⟨x⟩:=‹Nonempty X›
    exact (hg x).trans ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x))
  have hM0:0 < ‖g‖:=zero_lt_one.trans_le hM
  have ht:0 < τ:=lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  let c:=τ*(1-1/‖g‖)
  have hc:0 ≤ c:=mul_nonneg ht.le (sub_nonneg.mpr ((div_le_one hM0).mpr hM))
  have he:L g = τ • (g-1):=by
    have hv:=congrArg (fun A:C(X,ℝ) →L[ℝ] C(X,ℝ) => A 1) (positiveResolvent_mul L h hτ).2
    simpa only [mul_apply_eq_comp,smul_apply,
      sub_apply,one_apply_eq_self] using hv
  have hLg:L g ≤ c • g:=by
    rw [he]
    intro x
    change τ*(g x-1) ≤ c*g x
    have hgx:g x ≤ ‖g‖:=(le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x)
    have hdiv:g x / ‖g‖ ≤ 1:=(div_le_one hM0).mpr hgx
    dsimp [c]
    have hh:=mul_le_mul_of_nonneg_left hdiv ht.le
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    nlinarith
  have hr:=growthRate_le_of_pow_bound L h hM0 hc (positive_operator_pow_bound L hp hg hc hLg)
  refine ⟨hM,?_⟩
  dsimp [c] at hr
  change τ/‖g‖ ≤ τ-growthRate L h
  simp only [div_eq_mul_inv,one_mul] at hr ⊢
  nlinarith
lemma probability_of_positive_functional.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (Λ:C(X,ℝ) →L[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f) (h1:Λ 1 = 1) :
    ∃ μ:ProbabilityMeasure X,∀ f:C(X,ℝ),∫ x,f x ∂(μ:Measure X) = Λ f:=by
  let Λ':C_c(X,ℝ) →ₚ[ℝ] ℝ :=
    { toFun:=fun f => Λ f.toContinuousMap
      map_add':=fun f g => map_add Λ f.toContinuousMap g.toContinuousMap
      map_smul':=fun c f => map_smul Λ c f.toContinuousMap
      monotone':=by
        intro f g hfg
        have hn:0 ≤ Λ (g.toContinuousMap-f.toContinuousMap):=hp _ (sub_nonneg.mpr hfg)
        simpa only [map_sub,sub_nonneg] using hn }
  let μ:=RealRMK.rieszMeasure Λ'
  have hi (f:C(X,ℝ)) : ∫ x,f x ∂μ = Λ f:=by
    let f':C_c(X,ℝ):=⟨f,HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure Λ' f'
  have hμ:IsProbabilityMeasure μ:=isProbabilityMeasure_iff_real.mpr (by
    have hh:=hi 1
    simpa [h1] using hh)
  exact ⟨⟨μ,hμ⟩,hi⟩
lemma exists_max_of_nonneg_continuous.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (f:C(X,ℝ)) (hf:0 ≤ f):∃ x:X,f x = ‖f‖:=by
  obtain ⟨x,_,hx⟩:=isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.continuousOn
  refine ⟨x,le_antisymm ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm f x)) ?_⟩
  apply (ContinuousMap.norm_le f (hf x)).mpr
  intro y
  calc
    ‖f y‖ = f y:=Real.norm_of_nonneg (hf y)
    _ ≤ f x:=hx (mem_univ y)
lemma exists_resolvent_probability.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f)
    (h:∀ n:ℕ,1 ≤ ‖L^n‖) {τ:ℝ} (hτ:growthRate L h < τ) :
    ∃ μ:ProbabilityMeasure X,∀ f:C(X,ℝ),
      |(∫ x,L f x ∂(μ:Measure X))-τ*(∫ x,f x ∂(μ:Measure X))| ≤
      (τ-growthRate L h)*‖f‖:=by
  let R:=positiveResolvent L τ
  let g:=R 1
  have hg:1 ≤ g:=positiveResolvent_ge_one L hp h hτ
  have hg0:0 ≤ g:=le_trans (by intro; simp) hg
  obtain ⟨x,hx⟩:=exists_max_of_nonneg_continuous g hg0
  have hM:=positiveResolvent_norm_bound L hp h hτ
  have hM0:0 < ‖g‖:=zero_lt_one.trans_le hM.1
  let Λ:C(X,ℝ) →L[ℝ] ℝ:=(‖g‖⁻¹ • ContinuousMap.evalCLM (R:=ℝ) x).comp R
  have hΛ (f:C(X,ℝ)):Λ f = R f x / ‖g‖:=by change ‖g‖⁻¹ * R f x = R f x / ‖g‖; ring
  have hpΛ:∀ f,0 ≤ f → 0 ≤ Λ f:=by
    intro f hf
    rw [hΛ]
    exact div_nonneg (positiveResolvent_nonneg L hp h hτ f hf x) hM0.le
  have h1:Λ 1 = 1:=by rw [hΛ]; change g x / ‖g‖ = 1; rw [hx,div_self hM0.ne']
  obtain ⟨μ,hμ⟩:=probability_of_positive_functional Λ hpΛ h1
  refine ⟨μ,fun f => ?_⟩
  rw [hμ (L f),hμ f,hΛ,hΛ]
  have he:R (L f) x = τ*(R f x-f x):=by
    have hv:=congrArg (fun A:C(X,ℝ) →L[ℝ] C(X,ℝ) => A f x) (positiveResolvent_mul L h hτ).1
    exact hv
  rw [he]
  have hτ0:0 ≤ τ:=lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le) |>.le
  calc
    |τ*(R f x-f x)/‖g‖-τ*(R f x/‖g‖)| = (τ/‖g‖)*|f x|:=by
      rw [show τ*(R f x-f x)/‖g‖-τ*(R f x/‖g‖) = -(τ/‖g‖)*f x by ring,
        abs_mul,abs_neg,abs_of_nonneg (div_nonneg hτ0 hM0.le)]
    _ ≤ (τ/‖g‖)*‖f‖:=mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f x)
      (div_nonneg hτ0 hM0.le)
    _ ≤ (τ-growthRate L h)*‖f‖:=mul_le_mul_of_nonneg_right hM.2 (norm_nonneg f)
lemma exists_growth_eigenmeasure.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (L:C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp:∀ f,0 ≤ f → 0 ≤ L f)
    (h:∀ n:ℕ,1 ≤ ‖L^n‖) :
    ∃ μ:ProbabilityMeasure X,∀ f:C(X,ℝ),
      (∫ x,L f x ∂(μ:Measure X)) = growthRate L h*(∫ x,f x ∂(μ:Measure X)):=by
  let ρ:=growthRate L h
  let τ:ℕ → ℝ:=fun n => ρ+1/((n:ℝ)+1)
  have hτ (n:ℕ):growthRate L h < τ n:=by
    dsimp [τ,ρ]
    exact lt_add_of_pos_right _ (by positivity)
  choose μ hμ using fun n:ℕ => exists_resolvent_probability L hp h (hτ n)
  let U:=Ultrafilter.of (atTop:Filter ℕ)
  let V:=U.map μ
  let ν:=V.lim
  have hν:Tendsto μ (U:Filter ℕ) (𝓝 ν):=V.le_nhds_lim
  have ht:Tendsto τ (U:Filter ℕ) (𝓝 ρ):=by
    have hh:Tendsto τ atTop (𝓝 ρ):=by
      simpa [τ] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add ρ
    exact hh.mono_left (Ultrafilter.of_le atTop)
  refine ⟨ν,fun f => ?_⟩
  have hi:=(ProbabilityMeasure.continuous_integral_continuousMap f).tendsto ν |>.comp hν
  have hLi:=(ProbabilityMeasure.continuous_integral_continuousMap (L f)).tendsto ν |>.comp hν
  have hb:=le_of_tendsto_of_tendsto ((hLi.sub (ht.mul hi)).abs)
    ((ht.sub_const ρ).mul_const ‖f‖) (Eventually.of_forall (hμ · f))
  simp only [sub_self,zero_mul] at hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)
lemma positive_functional_bound.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (Λ:C(X,ℝ) →ₗ[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f) (f:C(X,ℝ)) :
    ‖Λ f‖ ≤ Λ 1 * ‖f‖:=by
  have hlo:(-‖f‖) • (1:C(X,ℝ)) ≤ f:=by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).1
  have hhi:f ≤ ‖f‖ • (1:C(X,ℝ)):=by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).2
  have h1:=hp (f-(-‖f‖) • 1) (sub_nonneg.mpr hlo)
  have h2:=hp (‖f‖ • 1-f) (sub_nonneg.mpr hhi)
  simp only [map_sub,map_smul,smul_eq_mul,neg_mul] at h1 h2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
seal kz192
def positiveFunctionalCLM.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (Λ:C(X,ℝ) →ₗ[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f):C(X,ℝ) →L[ℝ] ℝ :=
  Λ.mkContinuous (Λ 1) (positive_functional_bound Λ hp)
def intervalFunctional.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A:ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc:∀ f,Continuous (fun t => A t f))
    (hp:∀ t f,0 ≤ f → 0 ≤ A t f)
    (Λ:C(X,ℝ) →L[ℝ] ℝ) (hΛ:∀ f,0 ≤ f → 0 ≤ Λ f)
    (a b:ℝ) (hab:a ≤ b):C(X,ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun:=fun f => ∫ t in a..b,Λ (A t f)
      map_add':=by
        intro f g
        simp only [map_add]
        exact intervalIntegral.integral_add ((Λ.continuous.comp (hc f)).intervalIntegrable a b)
          ((Λ.continuous.comp (hc g)).intervalIntegrable a b)
      map_smul':=by
        intro c f
        simp only [map_smul,smul_eq_mul]
        exact intervalIntegral.integral_const_mul c _ }
    (by
      intro f hf
      exact intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf)))
lemma intervalFunctional_apply.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A:ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc:∀ f,Continuous (fun t => A t f))
    (hp:∀ t f,0 ≤ f → 0 ≤ A t f)
    (Λ:C(X,ℝ) →L[ℝ] ℝ) (hΛ:∀ f,0 ≤ f → 0 ≤ Λ f)
    (a b:ℝ) (hab:a ≤ b) (f:C(X,ℝ)) :
    intervalFunctional A hc hp Λ hΛ a b hab f = ∫ t in a..b,Λ (A t f):=rfl
lemma intervalFunctional_nonneg.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A:ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc:∀ f,Continuous (fun t => A t f))
    (hp:∀ t f,0 ≤ f → 0 ≤ A t f)
    (Λ:C(X,ℝ) →L[ℝ] ℝ) (hΛ:∀ f,0 ≤ f → 0 ≤ Λ f)
    (a b:ℝ) (hab:a ≤ b) (f:C(X,ℝ)) (hf:0 ≤ f) :
    0 ≤ intervalFunctional A hc hp Λ hΛ a b hab f :=
  intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf))
def kz592 (x y:ℝ) (hy:0 < y):=kz569 (kz562 x y hy)
lemma kz593 (x y u v:ℝ) (hy:0 < y) (hv:0 < v) :
    kz592 x y hy * kz592 u v hv = kz592 (x+y*u) (y*v) (mul_pos hy hv):=by
  simp only [kz592,kz572,kz564]
lemma kz594:kz592 0 1 zero_lt_one = 1:=by
  have h:kz562 0 1 zero_lt_one = kz440:=by
    apply Subtype.ext
    simp [kz562,kz440]
  rw [kz592,h,kz573]
lemma kz595 (x:ℝ):kz592 x 1 zero_lt_one = kz569 (kz563 x):=rfl
lemma kz596 (v:ℝ) (hv:0 < v) :
    kz581 * (kz592 (1+v) v hv-kz592 (-1+v) v hv) =
      (1/2:ℝ) • (kz592 (1+v/2) (v/2) (by positivity)-
        kz592 (-1+v/2) (v/2) (by positivity)):=by
  change ((1/2:ℝ) • (kz592 (-1/2) (1/2) (by norm_num)+
    kz592 (1/2) (1/2) (by norm_num))) * _ = _
  rw [smul_mul_assoc,add_mul,mul_sub,mul_sub]
  simp only [kz593]
  have h1 : -1/2+1/2*(1+v) = v/2:=by ring
  have h2 : -1/2+1/2*(-1+v) = -1+v/2:=by ring
  have h3:1/2+1/2*(1+v) = 1+v/2:=by ring
  have h4:1/2+1/2*(-1+v) = v/2:=by ring
  simp only [h1,h2,h3,h4,show (1/2:ℝ)*v = v/2 by ring]
  congr 1
  abel
lemma kz597 (n:ℕ) :
    kz581^n * (kz569 (kz563 2)-1) =
      ((1/2:ℝ)^n) • (kz592 (1+(1/2:ℝ)^n) ((1/2:ℝ)^n) (by positivity)-
        kz592 (-1+(1/2:ℝ)^n) ((1/2:ℝ)^n) (by positivity)):=by
  induction n with
  | zero =>
    simp only [pow_zero,one_mul,one_smul]
    norm_num only [show (1+(1:ℝ)) = 2 by norm_num,show (-1+(1:ℝ)) = 0 by norm_num]
    rw [kz594,kz595]
  | succ n ih =>
    rw [pow_succ',mul_assoc,ih,mul_smul_comm,kz596,smul_smul]
    simp only [pow_succ,div_eq_mul_inv,one_mul]
lemma kz598 (n:ℕ) :
    ‖kz592 (1+(1/2:ℝ)^n) ((1/2:ℝ)^n) (by positivity)-
      kz592 (-1+(1/2:ℝ)^n) ((1/2:ℝ)^n) (by positivity)‖ ≤
      8192 / ((1/2:ℝ)^n)^2:=by
  let v:=(1/2:ℝ)^n
  have hv:0 < v:=by positivity
  have hv1:v ≤ 1:=pow_le_one₀ (by norm_num) (by norm_num)
  have hb (x:ℝ) (hx:|x| ≤ 2):‖kz592 x v hv‖ ≤ 4096/v^2:=by
    apply kz575 (by positivity)
    intro g
    have hq:=kz591 g (kz562 x v hv) (by simpa [kz562] using hx)
      (by simpa [kz562] using hv1)
    simp only [kz562,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hq
    rw [kz198]
    have hh:=(sq_le_sq₀ (norm_nonneg _) (by positivity:0 ≤ 64/v)).mpr hq
    simpa only [kz562,div_pow,show (64:ℝ)^2 = 4096 by norm_num] using hh
  have hp:=hb (1+v) (by rw [abs_le]; constructor <;> linarith)
  have hm:=hb (-1+v) (by rw [abs_le]; constructor <;> linarith)
  calc
    _ ≤ ‖kz592 (1+v) v hv‖+‖kz592 (-1+v) v hv‖:=norm_sub_le (kz592 (1+v) v hv) (kz592 (-1+v) v hv)
    _ ≤ 4096/v^2+4096/v^2:=add_le_add hp hm
    _ = 8192/v^2:=by ring
lemma kz599 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (ρ:ℝ)
    (hΛ:∀ f,Λ (kz581 f) = ρ*Λ f) (n:ℕ) (f:C(kz140,ℝ)) :
    Λ ((kz581^n) f) = ρ^n*Λ f:=by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ',mul_apply_eq_comp,hΛ,ih]; ring
lemma kz600 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (ρ:ℝ)
    (hρ:2 < ρ) (hΛ:∀ f,Λ (kz581 f) = ρ*Λ f) (f:C(kz140,ℝ)) :
    Λ (kz569 (kz563 2) f) = Λ f:=by
  have hρ0:0 < ρ:=by linarith
  have hn (n:ℕ):‖Λ (kz569 (kz563 2) f)-Λ f‖ ≤
      (8192*‖Λ‖*‖f‖)*(2/ρ)^n:=by
    let v:=(1/2:ℝ)^n
    let B:=kz592 (1+v) v (by positivity)-kz592 (-1+v) v (by positivity)
    have he:ρ^n*(Λ (kz569 (kz563 2) f)-Λ f) = v*Λ (B f):=by
      rw [← map_sub,← kz599 Λ ρ hΛ]
      change Λ ((kz581^n * (kz569 (kz563 2)-1)) f) = _
      rw [kz597]
      change Λ (v • B f) = _
      exact map_smul Λ v (B f)
    have hb:‖B‖ ≤ 8192/v^2:=kz598 n
    have hh:ρ^n*‖Λ (kz569 (kz563 2) f)-Λ f‖ ≤
        v*(‖Λ‖*(8192/v^2*‖f‖)):=by
      calc
        _ = ‖v*Λ (B f)‖:=by rw [← he,norm_mul,Real.norm_of_nonneg (pow_nonneg hρ0.le n)]
        _ ≤ v*(‖Λ‖*(‖B‖*‖f‖)):=by
          rw [norm_mul,Real.norm_of_nonneg (by positivity:0 ≤ v)]
          exact mul_le_mul_of_nonneg_left ((Λ.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (B.le_opNorm f) (norm_nonneg Λ))) (by positivity)
        _ ≤ _:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg f)) (norm_nonneg Λ)) (by positivity)
    calc
      _ ≤ (v*(‖Λ‖*(8192/v^2*‖f‖)))/ρ^n :=
        (le_div_iff₀ (pow_pos hρ0 n)).mpr (by simpa only [mul_comm] using hh)
      _ = _:=by
        dsimp [v]
        simp only [div_pow,one_pow]
        field_simp
  have ht:Tendsto (fun n:ℕ => (8192*‖Λ‖*‖f‖)*(2/ρ)^n) atTop (𝓝 0):=by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity:0 ≤ 2/ρ)
      ((div_lt_one hρ0).mpr hρ)).const_mul (8192*‖Λ‖*‖f‖)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht (Eventually.of_forall hn)) (norm_nonneg _)))
def probabilityFunctional.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:ProbabilityMeasure X):C(X,ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun:=fun f => ∫ x,f x ∂(μ:Measure X)
      map_add':=fun f g => integral_add (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul':=fun c f => integral_smul c f }
    (fun _ hf => integral_nonneg hf)
lemma probabilityFunctional_apply.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:ProbabilityMeasure X) (f:C(X,ℝ)) :
    probabilityFunctional μ f = ∫ x,f x ∂(μ:Measure X):=rfl
lemma probabilityFunctional_one.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:ProbabilityMeasure X) :
    probabilityFunctional μ 1 = 1:=by simp [probabilityFunctional_apply]
lemma probabilityFunctional_pos.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:ProbabilityMeasure X) (f:C(X,ℝ)) (hf:0 ≤ f) :
    0 ≤ probabilityFunctional μ f:=integral_nonneg hf
lemma kz601 (F:ℝ → ℝ) (hc:Continuous F) (hp:Function.Periodic F 2) :
    (∫ x in (0:ℝ)..2,(F (-1/2+x/2)+F (1/2+x/2))) = 2*∫ x in (0:ℝ)..2,F x:=by
  have hm:(∫ x in (0:ℝ)..2,F (-1/2+x/2)) = 2*∫ x in (-1/2:ℝ)..(1/2),F x:=by
    have hh:=intervalIntegral.integral_comp_mul_add (a:=(0:ℝ)) (b:=2) F
      (by norm_num:(1/2:ℝ) ≠ 0) (-1/2)
    convert hh using 1 <;> (try { congr 1; funext x; congr 1; ring }); norm_num
  have hp':(∫ x in (0:ℝ)..2,F (1/2+x/2)) = 2*∫ x in (1/2:ℝ)..(3/2),F x:=by
    have hh:=intervalIntegral.integral_comp_mul_add (a:=(0:ℝ)) (b:=2) F
      (by norm_num:(1/2:ℝ) ≠ 0) (1/2)
    convert hh using 1 <;> (try { congr 1; funext x; congr 1; ring }); norm_num
  have hi:(∫ x in (-1/2:ℝ)..(3/2),F x) = ∫ x in (0:ℝ)..2,F x:=by
    convert hp.intervalIntegral_add_eq (-1/2) 0 using 1 <;> norm_num
  have hcm:Continuous (fun x:ℝ => F (-1/2+x/2)):=hc.comp (continuous_const.add (continuous_id.div_const 2))
  have hcp:Continuous (fun x:ℝ => F (1/2+x/2)):=hc.comp (continuous_const.add (continuous_id.div_const 2))
  rw [intervalIntegral.integral_add (hcm.intervalIntegrable _ _) (hcp.intervalIntegrable _ _),hm,hp',← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),hi]
lemma kz602 (y:ℝ) (hy:0 < y) (f:C(kz140,ℝ)) :
    Continuous (fun x:ℝ => kz592 x y hy f) :=
  (kz574 f).comp (continuous_halfPoint continuous_id continuous_const (fun _ => hy))
lemma kz603 (f:C(kz140,ℝ)) :
    Continuous (fun x:ℝ => kz569 (kz563 x) f):=kz602 1 zero_lt_one f
def kz604 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f) :
    C(kz140,ℝ) →L[ℝ] ℝ :=
  (1/2:ℝ) • intervalFunctional (fun x => kz569 (kz563 x)) kz603
    (fun _ => kz571 _) Λ hp 0 2 (by norm_num)
lemma kz605 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (f:C(kz140,ℝ)):kz604 Λ hp f = (1/2:ℝ)*∫ x in (0:ℝ)..2,Λ (kz569 (kz563 x) f):=rfl
lemma kz606 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (f:C(kz140,ℝ)) (hf:0 ≤ f):0 ≤ kz604 Λ hp f:=by
  rw [kz605]
  apply mul_nonneg (by norm_num)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hp _ (kz571 _ f hf))
lemma kz607 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (h1:0 < Λ 1):0 < kz604 Λ hp 1:=by
  rw [kz605]
  apply mul_pos (by norm_num)
  apply intervalIntegral.integral_pos (by norm_num)
    (Λ.continuous.comp (kz603 1)).continuousOn
    (fun x _ => hp _ (kz571 _ 1 (by intro; simp)))
  refine ⟨0,by norm_num,?_⟩
  change 0 < Λ (kz592 0 1 zero_lt_one 1)
  rw [kz594,one_apply_eq_self]
  exact h1
lemma kz608 (Λ:C(kz140,ℝ) →L[ℝ] ℝ)
    (hper:∀ f,Λ (kz569 (kz563 2) f) = Λ f)
    (y:ℝ) (hy:0 < y) (f:C(kz140,ℝ)) :
    Function.Periodic (fun x:ℝ => Λ (kz592 x y hy f)) 2:=by
  intro x
  have hh:=hper (kz592 x y hy f)
  rw [← kz595,← mul_apply_eq_comp,kz593] at hh
  simpa only [one_mul,add_comm x 2] using hh
lemma kz609 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (u v:ℝ) (hv:0 < v) (f:C(kz140,ℝ)) :
    kz604 Λ hp (kz592 u v hv f) =
      (1/2:ℝ)*∫ x in (0:ℝ)..2,Λ (kz592 (x+u) v hv f):=by
  rw [kz605]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← kz595,← mul_apply_eq_comp,kz593]
  simp only [one_mul]
lemma kz610 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (hper:∀ f,Λ (kz569 (kz563 2) f) = Λ f)
    (t:ℝ) (f:C(kz140,ℝ)) :
    kz604 Λ hp (kz569 (kz563 t) f) = kz604 Λ hp f:=by
  rw [← kz595,kz609]
  rw [intervalIntegral.integral_comp_add_right (fun x => Λ (kz592 x 1 zero_lt_one f)) t]
  have hh:=(kz608 Λ hper 1 zero_lt_one f).intervalIntegral_add_eq t 0
  rw [zero_add] at hh
  rw [zero_add,add_comm 2 t,hh,kz605]
  rfl
lemma kz611 (Λ:C(kz140,ℝ) →L[ℝ] ℝ) (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (hper:∀ f,Λ (kz569 (kz563 2) f) = Λ f)
    (ρ:ℝ) (heig:∀ f,Λ (kz581 f) = ρ*Λ f) (f:C(kz140,ℝ)) :
    kz604 Λ hp (kz592 0 (1/2) (by norm_num) f) = ρ*kz604 Λ hp f:=by
  have he (x:ℝ):ρ*Λ (kz569 (kz563 x) f) =
      (1/2:ℝ)*(Λ (kz592 (-1/2+x/2) (1/2) (by norm_num) f)+
        Λ (kz592 (1/2+x/2) (1/2) (by norm_num) f)):=by
    rw [← heig]
    change Λ (((1/2:ℝ) • (kz592 (-1/2) (1/2) (by norm_num)+kz592 (1/2) (1/2) (by norm_num)))
      (kz592 x 1 zero_lt_one f)) = _
    rw [← mul_apply_eq_comp,smul_mul_assoc,add_mul]
    simp only [kz593,mul_one,smul_apply,map_smul,add_apply,map_add,smul_eq_mul]
    simp only [show (1/2:ℝ)*x = x/2 by ring]
  have hc:Continuous (fun x:ℝ => Λ (kz592 x (1/2) (by norm_num) f)) :=
    Λ.continuous.comp (kz602 _ _ f)
  have hi:=kz601 (fun x => Λ (kz592 x (1/2) (by norm_num) f)) hc
    (kz608 Λ hper (1/2) (by norm_num) f)
  rw [kz609,kz605]
  simp only [add_zero]
  rw [show ρ*((1/2:ℝ)*∫ x in (0:ℝ)..2,Λ (kz569 (kz563 x) f)) =
    (1/2:ℝ)*(∫ x in (0:ℝ)..2,ρ*Λ (kz569 (kz563 x) f)) by
      rw [intervalIntegral.integral_const_mul]; ring]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,hi]
  ring
lemma period_average_invariant.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A:ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc:∀ f,Continuous (fun t => A t f))
    (hp:∀ t f,0 ≤ f → 0 ≤ A t f)
    (hm:∀ t s,A (t+s) = A t*A s)
    (Λ:C(X,ℝ) →L[ℝ] ℝ) (hΛ:∀ f,0 ≤ f → 0 ≤ Λ f)
    (l:ℝ) (hl:0 ≤ l) (hper:∀ f,Λ (A l f) = Λ f)
    (s:ℝ) (f:C(X,ℝ)) :
    intervalFunctional A hc hp Λ hΛ 0 l hl (A s f) =
      intervalFunctional A hc hp Λ hΛ 0 l hl f:=by
  have hfper:Function.Periodic (fun t:ℝ => Λ (A t f)) l:=by
    intro t
    dsimp only
    rw [add_comm t l,hm,mul_apply_eq_comp,hper]
  rw [intervalFunctional_apply,intervalFunctional_apply]
  have he (t:ℝ):Λ (A t (A s f)) = Λ (A (t+s) f):=by rw [hm,mul_apply_eq_comp]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right (fun t => Λ (A t f)) s]
  simpa only [zero_add,add_comm l s] using hfper.intervalIntegral_add_eq s 0
lemma intervalFunctional_mass_pos.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A:ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc:∀ f,Continuous (fun t => A t f))
    (hp:∀ t f,0 ≤ f → 0 ≤ A t f)
    (h0:A 0 = 1)
    (Λ:C(X,ℝ) →L[ℝ] ℝ) (hΛ:∀ f,0 ≤ f → 0 ≤ Λ f)
    (h1:0 < Λ 1) (l:ℝ) (hl:0 < l) :
    0 < intervalFunctional A hc hp Λ hΛ 0 l hl.le 1:=by
  rw [intervalFunctional_apply]
  apply intervalIntegral.integral_pos hl (Λ.continuous.comp (hc 1)).continuousOn
    (fun t _ => hΛ _ (hp _ _ (by intro; simp)))
  refine ⟨0,by simp [hl.le],?_⟩
  change 0 < Λ (A 0 1)
  simpa only [h0,one_apply_eq_self] using h1
def kz612 (β t:ℝ):C(kz140,ℝ) →L[ℝ] C(kz140,ℝ) :=
  Real.exp (β*t) • kz592 0 (Real.exp t) (Real.exp_pos t)
lemma kz613 (β t:ℝ) (f:C(kz140,ℝ)) :
    kz612 β t f = Real.exp (β*t) • kz592 0 (Real.exp t) (Real.exp_pos t) f:=rfl
lemma kz614 (β:ℝ) (f:C(kz140,ℝ)) :
    Continuous (fun t => kz612 β t f):=by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((kz574 f).comp
      (continuous_halfPoint continuous_const Real.continuous_exp Real.exp_pos))
lemma kz615 (β t:ℝ) (f:C(kz140,ℝ)) (hf:0 ≤ f) :
    0 ≤ kz612 β t f:=by
  rw [kz613]
  exact smul_nonneg (Real.exp_pos _).le (kz571 _ f hf)
lemma kz616 (β:ℝ):kz612 β 0 = 1:=by
  simp only [kz612,mul_zero,Real.exp_zero,one_smul,kz594]
lemma kz617 (β t s:ℝ) :
    kz612 β (t+s) = kz612 β t*kz612 β s:=by
  simp only [kz612,smul_mul_smul_comm,kz593,mul_zero,add_zero,Real.exp_add,mul_add]
lemma kz618 (β t u:ℝ) :
    kz612 β t*kz569 (kz563 u) =
      kz569 (kz563 (Real.exp t*u))*kz612 β t:=by
  simp only [kz612,← kz595,smul_mul_assoc,mul_smul_comm,kz593,
    mul_one,one_mul,mul_zero,zero_add,add_zero]
lemma kz619 (Λ:C(kz140,ℝ) →L[ℝ] ℝ)
    (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (hper:∀ f,Λ (kz569 (kz563 2) f) = Λ f)
    (ρ:ℝ) (hρ:0 < ρ) (heig:∀ f,Λ (kz581 f) = ρ*Λ f)
    (f:C(kz140,ℝ)) :
    kz604 Λ hp (kz612 (Real.log ρ/Real.log 2) (Real.log 2) f) =
      kz604 Λ hp f:=by
  have he:=kz611 Λ hp hper ρ heig (kz592 0 2 (by norm_num) f)
  rw [← mul_apply_eq_comp,kz593] at he
  norm_num only [mul_zero,add_zero,show (1/2:ℝ)*2 = 1 by norm_num,kz594,one_apply_eq_self] at he
  rw [kz613,map_smul,smul_eq_mul]
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num:(1:ℝ) < 2))),
    Real.exp_log hρ]
  simp only [Real.exp_log (by norm_num:(0:ℝ) < 2)]
  exact he.symm
def kz620 (β:ℝ) (Λ:C(kz140,ℝ) →L[ℝ] ℝ)
    (hp:∀ f,0 ≤ f → 0 ≤ Λ f):C(kz140,ℝ) →L[ℝ] ℝ :=
  intervalFunctional (kz612 β) (kz614 β) (kz615 β)
    Λ hp 0 (Real.log 2) (Real.log_nonneg (by norm_num))
lemma kz621 (β:ℝ) (Λ:C(kz140,ℝ) →L[ℝ] ℝ)
    (hp:∀ f,0 ≤ f → 0 ≤ Λ f) (f:C(kz140,ℝ)) :
    kz620 β Λ hp f = ∫ t in (0:ℝ)..Real.log 2,Λ (kz612 β t f):=rfl
lemma kz622 (β:ℝ) (Λ:C(kz140,ℝ) →L[ℝ] ℝ)
    (hp:∀ f,0 ≤ f → 0 ≤ Λ f) (f:C(kz140,ℝ)) (hf:0 ≤ f) :
    0 ≤ kz620 β Λ hp f :=
  intervalFunctional_nonneg _ _ _ _ hp _ _ _ f hf
lemma kz623 (β:ℝ) (Λ:C(kz140,ℝ) →L[ℝ] ℝ)
    (hp:∀ f,0 ≤ f → 0 ≤ Λ f) (h1:0 < Λ 1):0 < kz620 β Λ hp 1 :=
  intervalFunctional_mass_pos _ _ _ (kz616 β) Λ hp h1 _ (Real.log_pos (by norm_num))
lemma kz624 (β:ℝ) (Λ:C(kz140,ℝ) →L[ℝ] ℝ)
    (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (hper:∀ f,Λ (kz612 β (Real.log 2) f) = Λ f)
    (y:ℝ) (hy:0 < y) (f:C(kz140,ℝ)) :
    kz620 β Λ hp (kz592 0 y hy f) = y^(-β)*kz620 β Λ hp f:=by
  have he:=period_average_invariant (kz612 β) (kz614 β)
    (kz615 β) (kz617 β) Λ hp (Real.log 2)
    (Real.log_nonneg (by norm_num)) hper (Real.log y) f
  change kz620 β Λ hp (kz612 β (Real.log y) f) = kz620 β Λ hp f at he
  simp only [kz613,map_smul,smul_eq_mul,Real.exp_log hy] at he
  rw [Real.rpow_def_of_pos hy]
  have hinv:Real.exp (Real.log y*(-β))*Real.exp (β*Real.log y) = 1:=by
    rw [← Real.exp_add,show Real.log y*(-β)+β*Real.log y = 0 by ring,Real.exp_zero]
  calc
    _ = (Real.exp (Real.log y*(-β))*Real.exp (β*Real.log y))*kz620 β Λ hp (kz592 0 y hy f):=by rw [hinv,one_mul]
    _ = _:=by rw [mul_assoc,he]
lemma kz625 (β:ℝ) (Λ:C(kz140,ℝ) →L[ℝ] ℝ)
    (hp:∀ f,0 ≤ f → 0 ≤ Λ f)
    (hh:∀ u f,Λ (kz569 (kz563 u) f) = Λ f)
    (u:ℝ) (f:C(kz140,ℝ)) :
    kz620 β Λ hp (kz569 (kz563 u) f) = kz620 β Λ hp f:=by
  rw [kz621,kz621]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← mul_apply_eq_comp,kz618,mul_apply_eq_comp,hh]
def kz626:ℝ:=growthRate kz581 kz585
def kz627:ℝ:=Real.log kz626/Real.log 2
lemma kz628 (hρ:2 < kz626):1 < kz627:=by
  apply (lt_div_iff₀ (Real.log_pos (by norm_num:(1:ℝ) < 2))).mpr
  rw [one_mul]
  exact Real.log_lt_log (by norm_num) hρ
lemma kz629 (hρ:2 < kz626) :
    ∃ P:ProbabilityMeasure kz140,∀ z:kz145,∀ f:C(kz140,ℝ),
      (∫ g,kz198 g z*f (kz192 g z) ∂(P:Measure kz140)) =
        (z.val.im)^(-kz627)*(∫ g,f g ∂(P:Measure kz140)):=by
  obtain ⟨μ,hμ⟩:=exists_growth_eigenmeasure kz581 kz582 kz585
  let Λ:=probabilityFunctional μ
  have hp:∀ f,0 ≤ f → 0 ≤ Λ f:=probabilityFunctional_pos μ
  have h1:Λ 1 = 1:=probabilityFunctional_one μ
  have heig:∀ f,Λ (kz581 f) = kz626*Λ f:=hμ
  have hper:=kz600 Λ kz626 hρ heig
  let H:=kz604 Λ hp
  have hH:∀ f,0 ≤ f → 0 ≤ H f:=kz606 Λ hp
  have hH1:0 < H 1:=kz607 Λ hp (by rw [h1]; norm_num)
  have hHper:∀ f,H (kz612 kz627 (Real.log 2) f) = H f :=
    kz619 Λ hp hper kz626 (by linarith) heig
  have hHh:∀ u f,H (kz569 (kz563 u) f) = H f:=kz610 Λ hp hper
  let ν:=kz620 kz627 H hH
  have hν:∀ f,0 ≤ f → 0 ≤ ν f:=kz622 kz627 H hH
  have hν1:0 < ν 1:=kz623 kz627 H hH hH1
  have hνh:∀ u f,ν (kz569 (kz563 u) f) = ν f:=kz625 kz627 H hH hHh
  have hνs:∀ y (hy:0 < y) f,ν (kz592 0 y hy f) = y^(-kz627)*ν f :=
    kz624 kz627 H hH hHper
  let PiF:C(kz140,ℝ) →L[ℝ] ℝ:=(ν 1)⁻¹ • ν
  have hPiF:∀ f,0 ≤ f → 0 ≤ PiF f:=fun f hf => mul_nonneg (inv_nonneg.mpr hν1.le) (hν f hf)
  have hPiF1:PiF 1 = 1:=by change (ν 1)⁻¹*ν 1 = 1; exact inv_mul_cancel₀ (ne_of_gt hν1)
  obtain ⟨P,hP⟩:=probability_of_positive_functional PiF hPiF hPiF1
  refine ⟨P,fun z f => ?_⟩
  have hz:0 < z.val.im:=z.2
  have hez:kz569 z = kz569 (kz563 z.val.re)*kz592 0 z.val.im hz:=by
    rw [← kz595,kz593]
    congr 1
    apply Subtype.ext
    simpa only [kz562,mul_zero,add_zero,one_mul] using z.val.re_add_im.symm
  change (∫ g,(kz569 z f) g ∂(P:Measure kz140)) = _
  rw [hP,hP]
  change (ν 1)⁻¹*ν (kz569 z f) = _
  rw [hez,mul_apply_eq_comp,hνh,hνs]
  change (ν 1)⁻¹*((z.val.im)^(-kz627)*ν f) = (z.val.im)^(-kz627)*((ν 1)⁻¹*ν f)
  ring
lemma weighted_measure_eq.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ:Measure X) [IsFiniteMeasure μ] (w:C(X,ℝ)) (hw:∀ x,0 ≤ w x)
    (T:C(X,X)) (c:ℝ) (hc:0 ≤ c)
    (he:∀ f:C(X,ℝ),(∫ x,w x*f (T x) ∂μ) = c*∫ x,f x ∂μ) :
    Measure.map T (μ.withDensity (fun x => ENNReal.ofReal (w x))) = ENNReal.ofReal c • μ:=by
  let ν:=μ.withDensity (fun x => ENNReal.ofReal (w x))
  have:IsFiniteMeasure ν:=isFiniteMeasure_withDensity_ofReal
    (w.continuous.integrable_of_hasCompactSupport (μ:=μ) (HasCompactSupport.of_compactSpace w)).hasFiniteIntegral
  have:(ENNReal.ofReal c • μ).Regular:=Measure.Regular.smul (μ:=μ) ENNReal.ofReal_ne_top
  have hwmeas:Measurable (fun x => ENNReal.ofReal (w x)):=w.continuous.measurable.ennreal_ofReal
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x,f.toContinuousMap x ∂Measure.map T (μ.withDensity (fun x => ENNReal.ofReal (w x)))) = ∫ x,f.toContinuousMap x ∂ENNReal.ofReal c • μ
  rw [integral_map T.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul hwmeas (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  rw [he f.toContinuousMap,integral_smul_measure,ENNReal.toReal_ofReal hc,smul_eq_mul]
lemma weighted_lintegral_of_continuous.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ:Measure X) [IsFiniteMeasure μ] (w:C(X,ℝ)) (hw:∀ x,0 ≤ w x)
    (T:C(X,X)) (c:ℝ) (hc:0 ≤ c)
    (he:∀ f:C(X,ℝ),(∫ x,w x*f (T x) ∂μ) = c*∫ x,f x ∂μ)
    (f:X → ℝ≥0∞) (hf:Measurable f) :
    (∫⁻ x,ENNReal.ofReal (w x)*f (T x) ∂μ) = ENNReal.ofReal c*∫⁻ x,f x ∂μ:=by
  have hh:=weighted_measure_eq μ w hw T c hc he
  have hi:=congrArg (fun ν:Measure X => ∫⁻ x,f x ∂ν) hh
  rw [lintegral_map hf T.continuous.measurable,lintegral_smul_measure] at hi
  change (∫⁻ x,(f ∘ T) x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = _ at hi
  rw [lintegral_withDensity_eq_lintegral_mul μ w.continuous.measurable.ennreal_ofReal (hf.comp T.continuous.measurable)] at hi
  simpa only [Pi.mul_apply,smul_eq_mul,Function.comp_def] using hi
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
seal kz192
instance:PseudoMetrizableSpace kz140:=inferInstanceAs (PseudoMetrizableSpace kz137)
def kz630 (z:ℂ):kz145:=if h:z ∈ kz145 then ⟨z,h⟩ else kz440
lemma kz631 {z:ℂ} (hz:z ∈ kz145):kz630 z = ⟨z,hz⟩:=by
  simp only [kz630,dif_pos hz]
lemma kz632:Measurable kz630:=by
  have hm:Measurable (fun z:ℂ => (kz630 z:ℂ)):=by
    have he:(fun z:ℂ => (kz630 z:ℂ)) = (fun z => if z ∈ kz145 then z else Complex.I):=by
      funext z
      by_cases hz:z ∈ kz145 <;> simp [kz630,kz440,hz]
    rw [he]
    exact measurable_id.piecewise kz146.measurableSet measurable_const
  exact hm.subtype_mk
def kz633 (β:ℝ) (Φ:kz140 → ℝ≥0∞) (p:kz140 × ℂ):ℝ≥0∞ :=
  {p:kz140 × ℂ | p.2 ∈ kz145}.indicator
    (fun p => ENNReal.ofReal (p.2.im^(β-1)) * ENNReal.ofReal (kz198 p.1 (kz630 p.2)) *
      Φ (kz192 p.1 (kz630 p.2))) p
lemma kz634 (β:ℝ) {Φ:kz140 → ℝ≥0∞} (hΦ:Measurable Φ) :
    Measurable (kz633 β Φ):=by
  have hm:Measurable (fun p:kz140 × ℂ => (p.1,kz630 p.2)) :=
    measurable_fst.prodMk (kz632.comp measurable_snd)
  exact ((((Complex.measurable_im.comp measurable_snd).pow_const (β-1)).ennreal_ofReal.mul
    (kz200.measurable.comp hm).ennreal_ofReal).mul
    (hΦ.comp (kz194.measurable.comp hm))).indicator
      (kz146.measurableSet.preimage measurable_snd)
lemma kz635 (β:ℝ) (Φ:kz140 → ℝ≥0∞) (g:kz140) (z:kz145) :
    kz633 β Φ (g,z) = kz452 g β z * Φ (kz192 g z):=by
  rw [kz633,indicator_of_mem (show (g,(z:ℂ)) ∈ {p:kz140 × ℂ | p.2 ∈ kz145} from z.property)]
  simp only [kz631 z.property]
  rw [kz452,ENNReal.ofReal_mul (Real.rpow_nonneg z.property.le _)]
  simp only [kz198]
lemma kz636 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:∀ z:kz145,∀ f:kz140 → ℝ≥0∞,Measurable f →
      (∫⁻ g,ENNReal.ofReal (kz198 g z)*f (kz192 g z) ∂(P:Measure kz140)) =
        ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g,f g ∂(P:Measure kz140)))
    {Φ:kz140 → ℝ≥0∞} (hΦ:Measurable Φ) (z:kz145) :
    (∫⁻ g,kz633 β Φ (g,z) ∂(P:Measure kz140)) =
      ENNReal.ofReal (z.val.im⁻¹) * ∫⁻ g,Φ g ∂(P:Measure kz140):=by
  have hm:Measurable (fun g:kz140 => ENNReal.ofReal (kz198 g z)*Φ (kz192 g z)):=by
    have hp:Measurable (fun g:kz140 => (g,z)):=measurable_id.prodMk measurable_const
    exact ((kz200.measurable.comp hp).ennreal_ofReal).mul
      (hΦ.comp (kz194.measurable.comp hp))
  have he:(fun g:kz140 => kz633 β Φ (g,z)) =
      fun g => ENNReal.ofReal (z.val.im^(β-1)) *
        (ENNReal.ofReal (kz198 g z)*Φ (kz192 g z)):=by
    funext g
    rw [kz633,indicator_of_mem (show (g,(z:ℂ)) ∈ {p:kz140 × ℂ | p.2 ∈ kz145} from z.property)]
    simp only [kz631 z.property,mul_assoc]
  rw [he,lintegral_const_mul _ hm,hP z Φ hΦ,← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg z.property.le _),← Real.rpow_add z.property]
  congr 2
  rw [show β-1 + -β = (-1:ℝ) from by ring,Real.rpow_neg_one]
lemma kz637 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:∀ z:kz145,∀ f:kz140 → ℝ≥0∞,Measurable f →
      (∫⁻ g,ENNReal.ofReal (kz198 g z)*f (kz192 g z) ∂(P:Measure kz140)) =
        ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g,f g ∂(P:Measure kz140)))
    {Φ:kz140 → ℝ≥0∞} (hΦ:Measurable Φ)
    (hzero:∀ᵐ g ∂(P:Measure kz140),(∫⁻ z in kz145,kz633 β Φ (g,z)) = 0) :
    (∫⁻ g,Φ g ∂(P:Measure kz140)) = 0:=by
  have hm:=kz634 β hΦ
  have hz:(∫⁻ z in kz145,∫⁻ g,kz633 β Φ (g,z) ∂(P:Measure kz140)) = 0 :=
    (lintegral_lintegral_swap (f:=fun g z => kz633 β Φ (g,z)) (μ:=(P:Measure kz140)) (ν:=volume.restrict kz145) hm.aemeasurable).symm.trans (lintegral_eq_zero_of_ae_eq_zero hzero)
  have ha:=(lintegral_eq_zero_iff hm.lintegral_prod_left').mp hz
  have:(ae (volume.restrict kz145)).NeBot:=ae_restrict_neBot.mpr
    (ne_of_gt (kz146.measure_pos volume ⟨Complex.I,by simp [kz145]⟩))
  obtain ⟨z,hz,hz0⟩:=((ae_restrict_mem kz146.measurableSet).and ha).exists
  have he:=kz636 P β hP hΦ ⟨z,hz⟩
  change (∫⁻ g,kz633 β Φ (g,z) ∂(P:Measure kz140)) = 0 at hz0
  exact (mul_eq_zero.mp (he.symm.trans hz0)).resolve_left (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hz)))
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
seal kz192
def kz638 (z:ℂ):ℂ:=(-(z.re:ℂ)+Complex.I)/(z.im:ℂ)
lemma kz639 (z:ℂ):(kz638 z).re = -z.re/z.im:=by
  simp [kz638,Complex.div_ofReal_re]
lemma kz640 (z:ℂ):(kz638 z).im = z.im⁻¹:=by
  simp [kz638,Complex.div_ofReal_im]
lemma kz641 {z:ℂ} (hz:z ∈ kz145):kz638 z ∈ kz145:=by
  simpa only [kz145,mem_ofPred_eq,kz640] using inv_pos.mpr hz
lemma kz642 {z:ℂ} (hz:z ∈ kz145):kz638 (kz638 z) = z:=by
  have hn:z.im ≠ 0:=ne_of_gt hz
  apply Complex.ext
  · simp only [kz639,kz640,neg_div,neg_neg,div_inv_eq_mul]
    exact div_mul_cancel₀ _ hn
  · simp only [kz640,inv_inv]
lemma kz643:InjOn kz638 kz145:=by
  intro z hz w hw he
  simpa only [kz642 hz,kz642 hw] using congrArg kz638 he
lemma kz644 {z:ℂ} (hz:z ∈ kz145):kz148 z (kz638 z) = Complex.I:=by
  have hn:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [kz148,kz638,mul_div_cancel₀ _ hn]
  ring
lemma kz645 {z:ℂ} (hz:z ∈ kz145) :
    HasFDerivAt kz638
      (((z.im:ℂ)⁻¹) • (-(Complex.ofRealCLM.comp Complex.reCLM)) +
        (-(z.re:ℂ)+Complex.I) •
          ((-((z.im:ℂ)^2)⁻¹) • (Complex.ofRealCLM.comp Complex.imCLM))) z:=by
  have hn:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hi:=(hasFDerivAt_inv' (𝕜:=ℝ) hn).comp z
    (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt
  have h:=((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt.neg.add_const Complex.I).mul hi
  convert! h using 1
  ext v
  simp only [add_apply,smul_apply,neg_apply,Pi.neg_apply,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    ContinuousLinearMap.mulLeftRight_apply,Function.comp_apply,smul_eq_mul]
  ring
lemma kz646 {z:ℂ} (hz:z ∈ kz145):DifferentiableAt ℝ kz638 z :=
  (kz645 hz).differentiableAt
lemma kz647 {z:ℂ} (hz:z ∈ kz145) (v:ℂ) :
    fderiv ℝ kz638 z v =
      (-(v.re:ℂ)*(z.im:ℂ)-(-(z.re:ℂ)+Complex.I)*(v.im:ℂ))/(z.im:ℂ)^2:=by
  have hn:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [(kz645 hz).fderiv]
  simp only [add_apply,smul_apply,neg_apply,
    ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,Complex.reCLM_apply,Complex.imCLM_apply,
    smul_eq_mul]
  field_simp
  ring
lemma kz648 {z:ℂ} (hz:z ∈ kz145) :
    (fderiv ℝ kz638 z).det = z.im⁻¹^3:=by
  change LinearMap.det (fderiv ℝ kz638 z).toLinearMap = _
  rw [kz12]
  change (fderiv ℝ kz638 z 1).re*(fderiv ℝ kz638 z Complex.I).im-
    (fderiv ℝ kz638 z Complex.I).re*(fderiv ℝ kz638 z 1).im = _
  rw [kz647 hz,kz647 hz]
  simp only [Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,Complex.ofReal_one,
    Complex.ofReal_zero,neg_zero,zero_mul,mul_zero,mul_one,sub_zero,zero_sub,neg_mul,
    ← Complex.ofReal_pow,Complex.div_ofReal_re,Complex.div_ofReal_im,
    Complex.neg_re,Complex.neg_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im]
  field_simp [ne_of_gt (show 0 < z.im from hz)]
  ring
lemma kz649 {s:Set ℂ} (hs:MeasurableSet s) (hsub:s ⊆ kz145)
    (hInv:kz638 '' s = s) (f:ℂ → ℝ≥0∞) :
    (∫⁻ z in s,f z ∂volume) = ∫⁻ z in s,ENNReal.ofReal (z.im⁻¹^3)*f (kz638 z) ∂volume:=by
  have h:=lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (kz646 (hsub hz)).hasFDerivAt.hasFDerivWithinAt)
    (kz643.mono hsub) f
  rw [hInv] at h
  refine h.trans (setLIntegral_congr_fun hs (fun z hz => ?_))
  rw [kz648 (hsub hz),abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hsub hz).le) _)]
lemma kz650 {z:ℂ} (hz:z ∈ kz145) :
    kz162 (kz638 z) = (z-Complex.I)/(star (z+Complex.I)):=by
  have hy:(z.im:ℂ) ≠ 0:=Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have h₁:kz638 z-Complex.I = -(z-Complex.I)/(z.im:ℂ):=by
    rw [kz638,div_sub' hy]
    congr 1
    apply Complex.ext <;> simp
  have h₂:kz638 z+Complex.I = -star (z+Complex.I)/(z.im:ℂ):=by
    rw [kz638,div_add' _ _ _ hy]
    congr 1
    apply Complex.ext <;> simp
  rw [kz162,h₁,h₂,div_div_div_cancel_right₀ hy,neg_div_neg_eq]
lemma kz651 {z:ℂ} (hz:z ∈ kz145) :
    ‖kz162 (kz638 z)‖ = ‖kz162 z‖:=by
  rw [kz650 hz,kz162,norm_div,norm_div,norm_star]
lemma kz652 {z:ℂ} (hz:z ∈ kz459):kz638 z ∈ kz459 :=
  ⟨kz641 hz.1,by simpa only [kz651 hz.1] using hz.2⟩
lemma kz653:kz638 '' kz459 = kz459:=by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact kz652 hw
  · intro hz
    exact ⟨kz638 z,kz652 hz,kz642 hz.1⟩
lemma kz654 (g:kz140) {z:ℂ} (hz:z ∈ kz145) :
    kz183 (kz192 g ⟨z,hz⟩) (kz638 z) =
      -kz183 g z/((z.im:ℂ)*deriv (kz183 g) z):=by
  rw [kz193 g ⟨z,hz⟩ (kz641 hz)]
  simp only [kz155,kz644 hz,(kz184 g).2.1,zero_sub]
lemma kz655 (g:kz140) {z:ℂ} (hz:z ∈ kz459) :
    kz198 g ⟨z,hz.1⟩ *
      ‖kz183 (kz192 g ⟨z,hz.1⟩) (kz638 z)‖⁻¹^4 =
    z.im^4*(‖deriv (kz183 g) z‖^2*‖kz183 g z‖⁻¹^4):=by
  have hn:=kz463 g hz
  have hd:=kz91 kz146 (kz184 g).1 hz.1
  have hy:0 < z.im:=hz.1
  rw [kz198,kz160,kz654 g hz.1]
  simp only [norm_inv,norm_div,norm_neg,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hy]
  field_simp
lemma kz656 {f:ℂ → ℂ} {s:Set ℂ} (hs:MeasurableSet s)
    (hf:∀ z ∈ s,DifferentiableAt ℂ f z) (hi:InjOn f s)
    (hmin:∀ z ∈ s,(1/16:ℝ) ≤ ‖f z‖) :
    (∫⁻ z in s,ENNReal.ofReal (‖deriv f z‖^2*‖f z‖⁻¹^4)) ≤
      ENNReal.ofReal (256*Real.pi):=by
  have hn (z:ℂ) (hz:z ∈ s):f z ≠ 0:=by
    have:=hmin z hz
    exact norm_ne_zero_iff.mp (ne_of_gt (by linarith))
  have hd (z:ℂ) (hz:z ∈ s):=(hf z hz).hasDerivAt.inv (hn z hz)
  have hhi:InjOn (fun z => (f z)⁻¹) s:=by
    intro z hz w hw he
    exact hi hz hw (inv_inj.mp he)
  have he:=lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hhi (fun _ => (1:ℝ≥0∞))
  have hJac (z:ℂ) (hz:z ∈ s) :
      |(fderiv ℝ (fun z => (f z)⁻¹) z).det| = ‖deriv f z‖^2*‖f z‖⁻¹^4:=by
    have hdet:(fderiv ℝ (fun z => (f z)⁻¹) z).det = ‖deriv (fun z => (f z)⁻¹) z‖^2:=by
      exact kz76 (hd z hz).differentiableAt
    rw [hdet,abs_of_nonneg (sq_nonneg _)]
    have hdr:deriv (fun z => (f z)⁻¹) z = -deriv f z/f z^2:=(hd z hz).deriv
    rw [hdr]
    change ‖(-deriv f z/f z^2:ℂ)‖^2 = ‖deriv f z‖^2*‖f z‖⁻¹^4
    rw [Complex.norm_div,norm_neg,Complex.norm_pow]
    simp only [div_eq_mul_inv,inv_pow]
    ring
  have he':(∫⁻ z in s,ENNReal.ofReal (‖deriv f z‖^2*‖f z‖⁻¹^4)) =
      volume ((fun z => (f z)⁻¹) '' s):=by
    simp only [lintegral_const,one_mul,Measure.restrict_apply_univ] at he
    change _ = volume (f⁻¹ '' s)
    rw [he]
    apply setLIntegral_congr_fun hs
    intro z hz
    dsimp only
    rw [mul_one]
    have hfm:=(hd z hz).hasFDerivAt.restrictScalars ℝ
    have hh:(ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (-deriv f z/f z^2))) =
        fderiv ℝ (fun z => (f z)⁻¹) z:=by
      exact hfm.fderiv.symm
    rw [hh,hJac z hz]
  rw [he']
  have hsub:(fun z => (f z)⁻¹) '' s ⊆ Metric.closedBall 0 16:=by
    rintro _ ⟨z,hz,rfl⟩
    simp only [Metric.mem_closedBall,dist_zero_right,norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.mpr (hn z hz)) (by norm_num)).mpr (by simpa using hmin z hz)
  calc
    _ ≤ volume (Metric.closedBall (0:ℂ) 16):=measure_mono hsub
    _ = _:=by
      rw [Complex.volume_closedBall]
      have hp:(NNReal.pi:ℝ≥0∞) = ENNReal.ofReal Real.pi:=by
        rw [ENNReal.ofReal,ENNReal.coe_inj]
        apply Subtype.ext
        exact (Real.coe_toNNReal Real.pi Real.pi_pos.le).symm
      rw [hp,ENNReal.ofReal_mul (by norm_num:(0:ℝ) ≤ 256)]
      norm_num [mul_comm]
def kz657 (g:kz140) (z:ℂ):ℂ :=
  by classical exact if z ∈ kz145 then deriv (kz183 g) z else 0
lemma kz658:Measurable (fun p:kz140 × ℂ => kz657 p.1 p.2):=by
  classical
  let s:Set (kz140 × ℂ):=Prod.snd ⁻¹' kz145
  have hc:Continuous (fun p:s => deriv (kz183 p.val.1) p.val.2):=by
    have h:Continuous (fun p:kz140 × kz145 => deriv (kz183 p.1) p.2):=by
      simpa only [iteratedDeriv_one] using kz191 1
    exact h.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2)))
  simpa only [kz657,s,Set.mem_preimage,dite_eq_ite] using
    hc.measurable.dite (measurable_const (a:=(0:ℂ)))
      (kz146.measurableSet.preimage measurable_snd)
lemma kz659 (g:kz140) {z:ℂ} (hz:z ∈ kz145) :
    kz657 g z = deriv (kz183 g) z:=by simp [kz657,hz]
def kz660 (g:kz140) (z:ℂ):ℝ≥0∞ :=
  ENNReal.ofReal (‖kz464 g z‖⁻¹^4)
def kz661 (g:kz140) (z:ℂ):ℝ≥0∞ :=
  ENNReal.ofReal (‖kz657 g z‖^2*‖kz464 g z‖⁻¹^4)
def kz662 (β:ℝ) (g:kz140):ℝ≥0∞ :=
  ∫⁻ z in kz459,ENNReal.ofReal (z.im^(β+1))*kz660 g z
lemma kz663:Measurable (Function.uncurry kz660) :=
  (kz465.norm.inv.pow_const 4).ennreal_ofReal
lemma kz664:Measurable (Function.uncurry kz661) :=
  ((kz658.norm.pow_const 2).mul
    (kz465.norm.inv.pow_const 4)).ennreal_ofReal
lemma kz665 (β:ℝ):Measurable (kz662 β):=by
  apply Measurable.lintegral_prod_right
  exact (((Complex.continuous_im.comp continuous_snd).measurable.pow measurable_const).ennreal_ofReal).mul
    kz663
lemma kz666 (g:kz140) :
    (∫⁻ z in kz459,kz661 g z) ≤ ENNReal.ofReal (256*Real.pi):=by
  have he:(∫⁻ z in kz459,kz661 g z) =
      ∫⁻ z in kz459,ENNReal.ofReal (‖deriv (kz183 g) z‖^2*‖kz183 g z‖⁻¹^4):=by
    apply setLIntegral_congr_fun kz461
    intro z hz
    simp only [kz661,kz466 g hz.1,kz659 g hz.1]
  rw [he]
  exact kz656 kz461
    (fun _ hz => (kz184 g).1.1.differentiableAt (kz146.mem_nhds hz.1))
    ((kz184 g).1.2.mono (fun _ h => h.1))
    (fun _ hz => kz462 g hz)
def kz667 (P:ProbabilityMeasure kz140) (β:ℝ):Prop :=
  ∀ z:kz145,∀ f:kz140 → ℝ≥0∞,Measurable f →
    (∫⁻ g,ENNReal.ofReal (kz198 g z)*f (kz192 g z) ∂(P:Measure kz140)) =
      ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g,f g ∂(P:Measure kz140))
seal kz660 kz661
lemma kz668 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:kz667 P β) {z:ℂ} (hz:z ∈ kz459) :
    (∫⁻ g,kz661 g z ∂(P:Measure kz140)) =
      ENNReal.ofReal (z.im^(-β-4)) *
        (∫⁻ g,kz660 g (kz638 z) ∂(P:Measure kz140)):=by
  have hy:0 < z.im:=hz.1
  have hden:Measurable (fun g => kz660 g (kz638 z)) :=
    kz663.comp (measurable_id.prodMk measurable_const)
  have he:=hP ⟨z,hz.1⟩ _ hden
  have hid (g:kz140) :
      ENNReal.ofReal (kz198 g ⟨z,hz.1⟩)*kz660 (kz192 g ⟨z,hz.1⟩) (kz638 z) =
        ENNReal.ofReal (z.im^4)*kz661 g z:=by
    simp only [kz660,kz661,kz466 _ (kz641 hz.1),
      kz466 _ hz.1,kz659 _ hz.1]
    rw [← ENNReal.ofReal_mul (kz199 g ⟨z,hz.1⟩).le,
      kz655 g hz,ENNReal.ofReal_mul (pow_nonneg hy.le 4)]
  simp_rw [hid] at he
  have hJac:Measurable (fun g => kz661 g z) :=
    kz664.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_const_mul _ hJac] at he
  have hpow:ENNReal.ofReal (z.im^4) * ENNReal.ofReal (z.im^(-β-4)) = ENNReal.ofReal (z.im^(-β)):=by
    rw [← ENNReal.ofReal_mul (pow_nonneg hy.le 4),← Real.rpow_natCast,← Real.rpow_add hy]
    congr 1
    congr 1
    ring
  apply (ENNReal.mul_right_inj (by positivity:ENNReal.ofReal (z.im^4) ≠ 0) ENNReal.ofReal_ne_top).mp
  rw [← mul_assoc,hpow]
  exact he
lemma kz669 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:kz667 P β) :
    (∫⁻ g,kz662 β g ∂(P:Measure kz140)) ≤ ENNReal.ofReal (256*Real.pi):=by
  let A (z:ℂ):=∫⁻ g,kz661 g z ∂(P:Measure kz140)
  let B (z:ℂ):=∫⁻ g,kz660 g z ∂(P:Measure kz140)
  have hswap:(∫⁻ g,kz662 β g ∂(P:Measure kz140)) =
      ∫⁻ z in kz459,ENNReal.ofReal (z.im^(β+1))*B z:=by
    unfold kz662
    rw [lintegral_lintegral_swap]
    · apply lintegral_congr
      intro z
      have hm:Measurable (fun g => kz660 g z) :=
        kz663.comp (measurable_id.prodMk measurable_const)
      exact lintegral_const_mul _ hm
    · exact ((((Complex.continuous_im.comp continuous_snd).measurable.pow measurable_const).ennreal_ofReal).mul
        kz663).aemeasurable
  have hpoint (z:ℂ) (hz:z ∈ kz459) :
      ENNReal.ofReal (z.im^(β+1))*B z = ENNReal.ofReal (z.im⁻¹^3)*A (kz638 z):=by
    have hy:0 < z.im:=hz.1
    dsimp only [A]
    rw [kz668 P β hP (kz652 hz),
      kz642 hz.1,kz640,← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hy.le) 3)]
    congr 1
    rw [Real.inv_rpow hy.le]
    have he:(z.im⁻¹^3:ℝ) = z.im^(-3:ℝ):=by
      rw [Real.rpow_neg hy.le]
      norm_cast
      simp
    rw [he,← Real.rpow_neg hy.le,← Real.rpow_add hy]
    congr 1
    ring
  rw [hswap,setLIntegral_congr_fun kz461 hpoint,
    ← kz649 kz461 (fun _ h => h.1)
      kz653 A]
  have hswap₂:(∫⁻ z in kz459,A z) =
      ∫⁻ g,(∫⁻ z in kz459,kz661 g z) ∂(P:Measure kz140):=by
    exact (lintegral_lintegral_swap kz664.aemeasurable).symm
  rw [hswap₂]
  calc
    _ ≤ ∫⁻ _:kz140,ENNReal.ofReal (256*Real.pi) ∂(P:Measure kz140) :=
      lintegral_mono kz666
    _ = _:=by simp
lemma kz670 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:kz667 P β) :
    ∀ᵐ g ∂(P:Measure kz140),kz662 β g < ∞ :=
  ae_lt_top (kz665 β)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (kz669 P β hP))
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
seal kz192
seal kz660 kz661
lemma kz671 {a b:ℝ} (ha:0 < a) (hab:a ≤ b) :
    (∫⁻ y in Icc a b,ENNReal.ofReal y⁻¹) = ENNReal.ofReal (Real.log (b/a)):=by
  have hc:ContinuousOn (fun y:ℝ => y⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun y hy => ne_of_gt (ha.trans_le hy.1))
  have hi:IntegrableOn (fun y:ℝ => y⁻¹) (Icc a b) volume:=hc.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab,integral_inv_of_pos ha (ha.trans_le hab)]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact inv_nonneg.mpr (ha.le.trans hy.1)
lemma kz672 {R a b:ℝ} (hR:0 ≤ R) (ha:0 < a) (hab:a ≤ b) :
    (∫⁻ z in kz555 R a b,ENNReal.ofReal z.im⁻¹) =
      ENNReal.ofReal (2*R*Real.log (b/a)):=by
  have he:Complex.measurableEquivRealProd ⁻¹' (Icc (-R) R ×ˢ Icc a b) = kz555 R a b:=by
    ext z
    simp only [Complex.measurableEquivRealProd_apply,mem_preimage,mem_prod,mem_Icc,kz555,mem_ofPred_eq,abs_le]
  have hprod:=Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p:ℝ × ℝ => ENNReal.ofReal p.2⁻¹)
    (Icc (-R) R ×ˢ Icc a b)
  rw [he] at hprod
  change (∫⁻ z in kz555 R a b,ENNReal.ofReal z.im⁻¹) = _ at hprod
  rw [hprod,show (volume:Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setLIntegral_prod _ (by fun_prop)]
  dsimp only
  rw [kz671 ha hab,
    lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
  rw [show R - -R = 2*R from by ring,mul_comm,← ENNReal.ofReal_mul (by positivity:0 ≤ 2*R)]
def kz673 (k σ:ℝ) (g:kz140):ℝ≥0∞ :=
  ENNReal.ofReal (σ * kz205 (kz183 g) k Complex.I)
lemma kz674 (k σ:ℝ):Measurable (kz673 k σ):=by
  exact (measurable_const.mul ((kz374 k).comp
    (continuous_id.prodMk (continuous_const (y:=kz440)))).measurable).ennreal_ofReal
lemma kz675 (g:kz140) {k:ℝ} (hk:0 < k) (σ:ℝ) (z:kz145) :
    kz673 k σ (kz192 g z) = ENNReal.ofReal (σ * kz205 (kz183 g) k z):=by
  rw [kz673,kz444 g hk z]
def kz676 (k N:ℝ):Set kz140:={g | (g,kz440) ∈ kz544 k N}
def kz677 (k N:ℝ):kz140 → ℝ≥0∞:=(kz676 k N).indicator (kz673 k 1)
lemma kz678 {k:ℝ} (hk:0 < k) (N:ℝ):MeasurableSet (kz676 k N) :=
  (kz545 hk N).preimage (measurable_id.prodMk measurable_const)
lemma kz679 {k:ℝ} (hk:0 < k) (N:ℝ):Measurable (kz677 k N) :=
  (kz674 k 1).indicator (kz678 hk N)
lemma kz680 (g:kz140) (β:ℝ) {k:ℝ} (hk:0 < k) (N:ℝ) (z:kz145) :
    kz633 β (kz677 k N) (g,z) =
      kz452 g β z * ENNReal.ofReal (kz205 (kz183 g) k z) *
        (kz552 g k N).indicator 1 z:=by
  rw [kz635,kz677]
  have he:kz192 g z ∈ kz676 k N ↔ z.val ∈ kz552 g k N :=
    (kz547 g hk N z).trans (kz553 g k N z).symm
  by_cases hz:z.val ∈ kz552 g k N
  · rw [indicator_of_mem (he.mpr hz),kz675 g hk 1 z,one_mul,indicator_of_mem hz]
    simp
  · rw [indicator_of_notMem (fun h => hz (he.mp h)),indicator_of_notMem hz]
    simp
def kz681 (k:ℝ):Set kz140 :=
  {g | ¬kz215 (kz183 g) k (kz204 (kz183 g) k Complex.I)}
def kz682 (k:ℝ):kz140 → ℝ≥0∞:=(kz681 k).indicator (kz673 k 1)
lemma kz683 {k:ℝ} (hk:0 < k):MeasurableSet (kz681 k):=by
  have hm:Measurable (fun g:kz140 => (g,kz204 (kz183 g) k Complex.I)) :=
    continuous_id.measurable.prodMk (((kz372 k).comp
      (continuous_id.prodMk (continuous_const (y:=kz440)))).measurable)
  exact ((kz537 hk.le).preimage hm).compl
lemma kz684 {k:ℝ} (hk:0 < k):Measurable (kz682 k) :=
  (kz674 k 1).indicator (kz683 hk)
lemma kz685 (g:kz140) (β:ℝ) {k:ℝ} (hk:0 < k) (z:kz145) :
    kz633 β (kz682 k) (g,z) =
      kz452 g β z * ENNReal.ofReal (kz205 (kz183 g) k z) *
        {z:ℂ | z ∈ kz145 ∧ ¬kz215 (kz183 g) k (kz204 (kz183 g) k z)}.indicator 1 z:=by
  rw [kz635,kz682]
  have he:=kz445 g hk z
  by_cases hg:kz215 (kz183 g) k (kz204 (kz183 g) k z)
  · rw [indicator_of_notMem (show kz192 g z ∉ kz681 k from fun h => h (he.mpr hg)),
      indicator_of_notMem (show z.val ∉ {z:ℂ | z ∈ kz145 ∧ ¬kz215 (kz183 g) k (kz204 (kz183 g) k z)} from fun h => h.2 hg)]
    simp
  · rw [indicator_of_mem (show kz192 g z ∈ kz681 k from fun h => hg (he.mp h)),
      kz675 g hk 1 z,one_mul,indicator_of_mem (show z.val ∈ {z:ℂ | z ∈ kz145 ∧ ¬kz215 (kz183 g) k (kz204 (kz183 g) k z)} from ⟨z.property,hg⟩)]
    simp
lemma kz686 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:kz667 P β) {k:ℝ} (hk:0 < k)
    (hg:∀ᵐ g ∂(P:Measure kz140),∀ᵐ ξ:ℂ,kz215 (kz183 g) k ξ) :
    (∫⁻ g,kz682 k g ∂(P:Measure kz140)) = 0:=by
  apply kz637 P β hP (kz684 hk)
  filter_upwards [hg] with g hg
  refine Eq.trans ?_ (kz560 g (β:=β) hk hg)
  apply setLIntegral_congr_fun kz146.measurableSet
  intro z hz
  exact kz685 g β hk ⟨z,hz⟩
lemma kz687 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:kz667 P β) {Φ:kz140 → ℝ≥0∞} (hΦ:Measurable Φ)
    {R a b:ℝ} (hR:0 ≤ R) (ha:0 < a) (hab:a ≤ b) :
    (∫⁻ g,∫⁻ z in kz555 R a b,kz633 β Φ (g,z) ∂volume ∂(P:Measure kz140)) =
      ENNReal.ofReal (2*R*Real.log (b/a)) * ∫⁻ g,Φ g ∂(P:Measure kz140):=by
  rw [lintegral_lintegral_swap (f:=fun g z => kz633 β Φ (g,z)) (μ:=(P:Measure kz140)) (ν:=volume.restrict (kz555 R a b)) (kz634 β hΦ).aemeasurable]
  have he:(∫⁻ z in kz555 R a b,∫⁻ g,kz633 β Φ (g,z) ∂(P:Measure kz140)) =
      ∫⁻ z in kz555 R a b,ENNReal.ofReal z.im⁻¹ * ∫⁻ g,Φ g ∂(P:Measure kz140):=by
    apply setLIntegral_congr_fun (kz556 R a b)
    intro z hz
    exact kz636 P β hP hΦ ⟨z,ha.trans_le hz.2.1⟩
  rw [he,lintegral_mul_const _ (by fun_prop),kz672 hR ha hab]
lemma kz688 {S T:Set ℂ} (hS:MeasurableSet S) (hST:S ⊆ T)
    (f:ℂ → ℝ≥0∞) :
    (∫⁻ z in T,f z * S.indicator 1 z) = ∫⁻ z in S,f z:=by
  have he:(fun z => f z * S.indicator 1 z) = S.indicator f:=by
    funext z
    by_cases hz:z ∈ S <;> simp [hz]
  rw [he,setLIntegral_indicator hS,inter_eq_left.mpr hST]
lemma kz689 (g:kz140) {β k N R Y:ℝ} (hk:0 < k)
    (hb:β-1 = 4*(k-1)) (hN:1 ≤ N) :
    (∫⁻ z in kz555 R 1 Y,kz633 β (kz677 k N) (g,z)) ≤
      ∫⁻ z in kz555 (R+N*Y) (1/N) (N*Y),kz633 β (kz673 k (-1)) (g,z):=by
  have hn:0 < N:=lt_of_lt_of_le zero_lt_one hN
  have hB:kz555 R 1 Y ⊆ kz145:=fun z hz => lt_of_lt_of_le zero_lt_one hz.2.1
  have hB':kz555 (R+N*Y) (1/N) (N*Y) ⊆ kz145:=fun z hz =>
    lt_of_lt_of_le (one_div_pos.mpr hn) hz.2.1
  have he:=kz558 g hk hb hN (R:=R) (Y:=Y)
  have hp:(∫⁻ z in kz145,kz452 g β z*ENNReal.ofReal (kz205 (kz183 g) k z)*
      (kz552 g k N ∩ kz555 R 1 Y).indicator 1 z) =
      ∫⁻ z in kz555 R 1 Y,kz633 β (kz677 k N) (g,z):=by
    have hid:(fun z => kz452 g β z*ENNReal.ofReal (kz205 (kz183 g) k z)*
      (kz552 g k N ∩ kz555 R 1 Y).indicator 1 z) =
      fun z => (kz452 g β z*ENNReal.ofReal (kz205 (kz183 g) k z)*
        (kz552 g k N).indicator 1 z)*(kz555 R 1 Y).indicator 1 z:=by
      funext z
      rw [inter_indicator_one]
      simp only [Pi.mul_apply,mul_assoc]
    rw [hid,kz688 (kz556 _ _ _) hB]
    apply setLIntegral_congr_fun (kz556 _ _ _)
    intro z hz
    exact (kz680 g β hk N ⟨z,hB hz⟩).symm
  have hm:(∫⁻ z in kz145,kz452 g β z*ENNReal.ofReal (-kz205 (kz183 g) k z)*
      (kz555 (R+N*Y) (1/N) (N*Y)).indicator 1 z) =
      ∫⁻ z in kz555 (R+N*Y) (1/N) (N*Y),kz633 β (kz673 k (-1)) (g,z):=by
    rw [kz688 (kz556 _ _ _) hB']
    apply setLIntegral_congr_fun (kz556 _ _ _)
    intro z hz
    symm
    exact (kz635 β (kz673 k (-1)) g ⟨z,hB' hz⟩).trans
      (congrArg (kz452 g β z * ·) (by simpa only [neg_one_mul] using kz675 g hk (-1) ⟨z,hB' hz⟩))
  exact hp.symm.trans_le (he.trans_eq hm)
lemma kz690 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:kz667 P β) {k N R Y:ℝ} (hk:0 < k)
    (hb:β-1 = 4*(k-1)) (hN:1 ≤ N) (hR:0 ≤ R) (hY:1 ≤ Y) :
    ENNReal.ofReal (2*R*Real.log Y) * (∫⁻ g,kz677 k N g ∂(P:Measure kz140)) ≤
      ENNReal.ofReal (2*(R+N*Y)*Real.log (N^2*Y)) * (∫⁻ g,kz673 k (-1) g ∂(P:Measure kz140)):=by
  have hn:0 < N:=lt_of_lt_of_le zero_lt_one hN
  have hny:1 / N ≤ N*Y:=by
    rw [div_le_iff₀ hn]
    have hc:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY hn.le) hn.le
    nlinarith [sq_nonneg (N-1)]
  have hp:=kz687 P β hP (kz679 hk N) hR zero_lt_one hY
  have hm:=kz687 P β hP (kz674 k (-1))
    (add_nonneg hR (mul_nonneg hn.le (zero_le_one.trans hY))) (one_div_pos.mpr hn) hny
  simp only [div_one] at hp
  rw [show N*Y/(1/N) = N^2*Y from by field_simp] at hm
  rw [← hp,← hm]
  exact lintegral_mono (fun g => kz689 g hk hb hN)
lemma kz691 (N:ℝ) :
    Tendsto (fun Y:ℝ => (1+N/Y)*(1+2*Real.log N/Real.log Y)) atTop (𝓝 1):=by
  have h1:Tendsto (fun Y:ℝ => N/Y) atTop (𝓝 0):=tendsto_const_nhds.div_atTop tendsto_id
  have h2:Tendsto (fun Y:ℝ => 2*Real.log N/Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  simpa using ((tendsto_const_nhds (x:=(1:ℝ))).add h1).mul ((tendsto_const_nhds (x:=(1:ℝ))).add h2)
lemma kz692 {A B:ℝ≥0∞} (hA:A ≠ ∞) (hB:B ≠ ∞)
    {N:ℝ} (hN:1 ≤ N)
    (h:∀ Y:ℝ,1 < Y →
      ENNReal.ofReal (2*Y^2*Real.log Y)*A ≤
        ENNReal.ofReal (2*(Y^2+N*Y)*Real.log (N^2*Y))*B):A ≤ B:=by
  have hn:0 < N:=zero_lt_one.trans_le hN
  have hineq:∀ Y:ℝ,1 < Y → A.toReal ≤ (1+N/Y)*(1+2*Real.log N/Real.log Y)*B.toReal:=by
    intro Y hY
    have hy:0 < Y:=zero_lt_one.trans hY
    have hl:0 < Real.log Y:=Real.log_pos hY
    have hny:1 < N^2*Y:=by nlinarith [sq_nonneg (N-1)]
    have hlny:0 ≤ Real.log (N^2*Y):=Real.log_nonneg hny.le
    have hb:=ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) (h Y hY)
    rw [ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity:0 ≤ 2*Y^2*Real.log Y),
      ENNReal.toReal_ofReal (by positivity:0 ≤ 2*(Y^2+N*Y)*Real.log (N^2*Y))] at hb
    have hlog:Real.log (N^2*Y) = 2*Real.log N + Real.log Y:=by
      rw [Real.log_mul (by positivity) (ne_of_gt hy),Real.log_pow]
      norm_num
    rw [hlog] at hb
    apply (mul_le_mul_iff_right₀ (show 0 < 2*Y^2*Real.log Y by positivity)).mp
    calc
      _ ≤ 2*(Y^2+N*Y)*(2*Real.log N+Real.log Y)*B.toReal:=hb
      _ = _:=by field_simp; ring
  apply (ENNReal.toReal_le_toReal hA hB).mp
  have ht:=(kz691 N).mul_const B.toReal
  simp only [one_mul] at ht
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop (1:ℝ)] with Y hY
  exact hineq Y hY
lemma kz693 (P:ProbabilityMeasure kz140) (k σ:ℝ) :
    (∫⁻ g,kz673 k σ g ∂(P:Measure kz140)) < ∞:=by
  have hc:Continuous (fun g:kz140 => σ*kz205 (kz183 g) k Complex.I) :=
    continuous_const.mul ((kz374 k).comp
      (continuous_id.prodMk (continuous_const (y:=kz440))))
  have hi:Integrable (fun g:kz140 => σ*kz205 (kz183 g) k Complex.I) (P:Measure kz140) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply lt_of_le_of_lt (lintegral_mono (fun g => ENNReal.ofReal_le_ofReal (le_abs_self _)))
  exact (hasFiniteIntegral_iff_norm _).mp hi.2
lemma kz694 (k N:ℝ) (g:kz140):kz677 k N g ≤ kz673 k 1 g:=by
  by_cases hg:g ∈ kz676 k N <;> simp [kz677,indicator_of_mem,indicator_of_notMem,hg]
lemma kz695 (P:ProbabilityMeasure kz140) (k N:ℝ) :
    (∫⁻ g,kz677 k N g ∂(P:Measure kz140)) < ∞ :=
  (lintegral_mono (kz694 k N)).trans_lt (kz693 P k 1)
lemma kz696 {k:ℝ} (hk:0 < k) :
    Monotone (fun n:ℕ => kz677 k (n+1)):=by
  intro n m hnm g
  have hs:kz676 k (n+1) ⊆ kz676 k (m+1) :=
    fun g hg => kz550 hk (by exact_mod_cast Nat.add_le_add_right hnm 1) hg
  by_cases hg:g ∈ kz676 k (n+1)
  · simp only [kz677,indicator_of_mem hg,indicator_of_mem (hs hg),le_refl]
  · simp only [kz677,indicator_of_notMem hg]
    exact bot_le
lemma kz697 {k:ℝ} (hk:0 < k) (g:kz140) :
    (⨆ n:ℕ,kz677 k (n+1) g) =
      {g:kz140 | (g,kz440) ∈ kz539 k}.indicator (kz673 k 1) g:=by
  by_cases hg:(g,kz440) ∈ kz539 k
  · rw [indicator_of_mem (show g ∈ {g:kz140 | (g,kz440) ∈ kz539 k} from hg)]
    apply le_antisymm (iSup_le (fun n:ℕ => kz694 k (n+1) g))
    have hu:(g,kz440) ∈ ⋃ n:ℕ,kz544 k (n+1):=(kz551 hk).symm ▸ hg
    obtain ⟨n,hn⟩:=mem_iUnion.mp hu
    have he:kz677 k (n+1) g = kz673 k 1 g:=indicator_of_mem (show g ∈ kz676 k (n+1) from hn) _
    exact he ▸ le_iSup (fun n:ℕ => kz677 k (n+1) g) n
  · rw [indicator_of_notMem (show g ∉ {g:kz140 | (g,kz440) ∈ kz539 k} from hg)]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro n
    apply le_of_eq
    apply indicator_of_notMem
    intro hn
    exact hg hn.1
lemma kz698 {k:ℝ} (hk:0 < k) (g:kz140) :
    kz673 k 1 g = (⨆ n:ℕ,kz677 k (n+1) g) + kz682 k g:=by
  rw [kz697 hk g,kz682]
  by_cases hG:kz215 (kz183 g) k (kz204 (kz183 g) k Complex.I)
  · rw [indicator_of_notMem (show g ∉ kz681 k from fun h => h hG),add_zero]
    by_cases hJ:0 < kz205 (kz183 g) k Complex.I
    · exact (indicator_of_mem (show g ∈ {g:kz140 | (g,kz440) ∈ kz539 k} from ⟨hJ,hG⟩) _).symm
    · rw [indicator_of_notMem (show g ∉ {g:kz140 | (g,kz440) ∈ kz539 k} from fun h => hJ h.1)]
      exact ENNReal.ofReal_eq_zero.mpr (by simpa only [one_mul] using le_of_not_gt hJ)
  · rw [indicator_of_mem (show g ∈ kz681 k from hG),indicator_of_notMem (show g ∉ {g:kz140 | (g,kz440) ∈ kz539 k} from fun h => hG h.2),zero_add]
lemma kz699 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:kz667 P β) {k:ℝ} (hk:0 < k)
    (hb:β-1 = 4*(k-1))
    (hg:∀ᵐ g ∂(P:Measure kz140),∀ᵐ ξ:ℂ,kz215 (kz183 g) k ξ) :
    (∫⁻ g,kz673 k 1 g ∂(P:Measure kz140)) ≤ ∫⁻ g,kz673 k (-1) g ∂(P:Measure kz140):=by
  have hw (n:ℕ):(∫⁻ g,kz677 k (n+1) g ∂(P:Measure kz140)) ≤ ∫⁻ g,kz673 k (-1) g ∂(P:Measure kz140):=by
    apply kz692 (N:=(n:ℝ)+1) (kz695 P k (n+1)).ne (kz693 P k (-1)).ne
      (by have h:=Nat.cast_nonneg (α:=ℝ) n; linarith:(1:ℝ) ≤ n+1)
    intro Y hY
    exact kz690 P β hP hk hb (by have h:=Nat.cast_nonneg (α:=ℝ) n; linarith) (sq_nonneg Y) hY.le
  have he (g:kz140):=kz698 hk g
  simp_rw [he]
  rw [lintegral_add_left (Measurable.iSup (fun n:ℕ => kz679 hk (n+1))),
    kz686 P β hP hk hg,add_zero,lintegral_iSup (fun n:ℕ => kz679 hk (n+1)) (kz696 hk)]
  exact iSup_le hw
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
seal kz198
seal kz183
seal kz192
seal kz660 kz661
lemma kz700 (g:kz140) :
    DifferentiableOn ℂ (kz160 (kz183 g)) kz145 :=
  fun _ hz => (kz210 (kz184 g).1 hz).differentiableAt.differentiableWithinAt
lemma kz701 :
    Continuous (fun p:kz140 × kz145 => kz160 (kz183 p.1) p.2):=by
  have hd:Continuous (fun p:kz140 × kz145 => deriv (kz183 p.1) p.2):=by
    simpa only [iteratedDeriv_one] using kz191 1
  exact hd.inv₀ (fun p => kz91 kz146 (kz184 p.1).1 p.2.2)
def kz702 (n:ℕ) (g:kz140):C(kz145,ℂ) :=
  ⟨fun z => iteratedDeriv n (kz160 (kz183 g)) z,continuousOn_iff_continuous_domRestrict.mp
    (kz188 kz146 (kz700 g) n).continuousOn⟩
lemma kz703 (n:ℕ):Continuous (kz702 n):=by
  have hc:Continuous (kz702 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ kz701
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv:=ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h:TendstoLocallyUniformlyOn (fun a => kz160 (kz183 a))
      (kz160 (kz183 g)) (𝓝 g) kz145 :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open kz146 h
      (Eventually.of_forall kz700) n)
lemma kz704 (n:ℕ) :
    Continuous (fun p:kz140 × kz145 => iteratedDeriv n (kz160 (kz183 p.1)) p.2) :=
  continuous_eval.comp ((kz703 n).prodMap continuous_id)
lemma kz705 (g:kz140):kz160 (kz183 g) Complex.I = 1:=by
  rw [kz160,(kz184 g).2.2,inv_one]
lemma hasDerivAt_integral_compact.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    (F F':ℝ → X → ℝ) {U:Set ℝ} (hU:IsOpen U)
    (hF:∀ x ∈ U,Continuous (F x))
    (hc:ContinuousOn (fun p:ℝ × X => F' p.1 p.2) (U ×ˢ univ))
    (hd:∀ x ∈ U,∀ a,HasDerivAt (fun t => F t a) (F' x a) x)
    {x:ℝ} (hx:x ∈ U) :
    HasDerivAt (fun t => ∫ a,F t a ∂μ) (∫ a,F' x a ∂μ) x:=by
  obtain ⟨r,hr,hsub⟩:=Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hr2:0 < r/2:=half_pos hr
  have hsub':Metric.closedBall x (r/2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hsub
  have hk:IsCompact (Metric.closedBall x (r/2) ×ˢ (univ:Set X)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨C,hC⟩:=hk.exists_bound_of_continuousOn (hc.mono (Set.prod_mono hsub' Subset.rfl))
  have hc0:Continuous (F' x):=by
    have hs:Continuous (fun a:X => (x,a)):=continuous_const.prodMk continuous_id
    exact continuousOn_univ.mp
      (hc.comp hs.continuousOn (fun a _ => ⟨hx,mem_univ a⟩))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Metric.ball x (r/2)) (bound:=fun _:X => C) (Metric.ball_mem_nhds _ hr2)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hF y hy).aestronglyMeasurable
  · exact (hF x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hc0.aestronglyMeasurable
  · exact Eventually.of_forall (fun a y hy => hC (y,a) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le,mem_univ a⟩)
  · exact integrable_const C
  · exact Eventually.of_forall (fun a y hy => hd y (hsub' (Metric.ball_subset_closedBall hy)) a)
lemma kz706 {Q:ℂ → ℂ} {z d v:ℂ} {t:ℝ}
    (hQ:HasDerivAt Q d (z+(t:ℂ)*v)) :
    HasDerivAt (fun s:ℝ => Q (z+(s:ℂ)*v)) (d*v) t:=by
  have hv:HasDerivAt (fun s:ℝ => z+(s:ℂ)*v) v t:=by
    simpa using ((Complex.ofRealCLM.hasDerivAt.mul_const v).const_add z :
      HasDerivAt (fun s:ℝ => z+Complex.ofRealCLM s*v) (Complex.ofRealCLM 1*v) t)
  convert HasDerivAt.comp (𝕜:=ℝ) t hQ hv using 1 <;> rfl
def kz707 (q d v:ℂ):ℝ:=2*inner ℝ q (d*v)
def kz708 (q d e v:ℂ):ℝ :=
  2*(inner ℝ (d*v) (d*v)+inner ℝ q ((e*v)*v))
lemma kz709 {Q:ℂ → ℂ} {z d v:ℂ} {t:ℝ}
    (hQ:HasDerivAt Q d (z+(t:ℂ)*v)) :
    HasDerivAt (fun s:ℝ => ‖Q (z+(s:ℂ)*v)‖^2)
      (kz707 (Q (z+(t:ℂ)*v)) d v) t :=
  (kz706 hQ).norm_sq
lemma kz710 {Q D:ℂ → ℂ} {z d e v:ℂ} {t:ℝ}
    (hQ:HasDerivAt Q d (z+(t:ℂ)*v))
    (hD:HasDerivAt D e (z+(t:ℂ)*v)) :
    HasDerivAt (fun s:ℝ => kz707 (Q (z+(s:ℂ)*v)) (D (z+(s:ℂ)*v)) v)
      (2*(inner ℝ (d*v) (D (z+(t:ℂ)*v)*v)+inner ℝ (Q (z+(t:ℂ)*v)) ((e*v)*v))) t:=by
  simpa only [kz707,add_comm] using ((kz706 hQ).inner ℝ ((kz706 hD).mul_const v)).const_mul 2
lemma kz711 (d:ℂ):kz707 1 d 1 = 2*d.re:=by
  simp [kz707,Complex.inner]
lemma kz712 (d:ℂ):kz707 1 d Complex.I = -2*d.im:=by
  simp [kz707,Complex.inner]
lemma kz713 (q d e:ℂ) :
    kz708 q d e 1+kz708 q d e Complex.I = 4*‖d‖^2:=by
  simp only [kz708,mul_one]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  simp only [Complex.norm_mul,Complex.norm_I,mul_one]
  have he:(e*Complex.I)*Complex.I = -e:=by rw [mul_assoc,Complex.I_mul_I,mul_neg_one]
  rw [he,inner_neg_right]
  ring
lemma kz714:Continuous (fun p:ℂ × ℂ × ℂ × ℂ => kz708 p.1 p.2.1 p.2.2.1 p.2.2.2):=by
  unfold kz708
  fun_prop
def kz715 (v:ℂ) (t:ℝ):ℂ:=Complex.I+(t:ℂ)*v
def kz716 (v:ℂ):Set ℝ:={t | 0 < 1+t*v.im}
lemma kz717 (v:ℂ):IsOpen (kz716 v) :=
  isOpen_lt continuous_const (by fun_prop)
lemma kz718 (v:ℂ) (t:ℝ):(kz715 v t).im = 1+t*v.im:=by
  simp [kz715,Complex.mul_im]
lemma kz719 {v:ℂ} {t:ℝ} (ht:t ∈ kz716 v) :
    0 < (kz715 v t).im:=(kz718 v t).symm ▸ ht
@[simp] lemma kz720 (v:ℂ):kz715 v 0 = Complex.I:=by simp [kz715]
lemma kz721 (v:ℂ):(0:ℝ) ∈ kz716 v:=by simp [kz716]
lemma continuousOn_complexLine.{u_1} {X:Type u_1} [TopologicalSpace X] (G:X → ℂ → ℂ)
    (hG:Continuous (fun p:X × {z:ℂ | 0 < z.im} => G p.1 p.2)) (v:ℂ) :
    ContinuousOn (fun p:ℝ × X => G p.2 (kz715 v p.1)) (kz716 v ×ˢ univ):=by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let H:(kz716 v ×ˢ (univ:Set X)) → X × {z:ℂ | 0 < z.im} :=
    fun p => (p.val.2,⟨kz715 v p.val.1,kz719 p.2.1⟩)
  have hH:Continuous H:=by
    apply Continuous.prodMk
    · exact continuous_snd.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_const.add (((Complex.continuous_ofReal.comp continuous_fst).comp continuous_subtype_val).mul continuous_const)
  exact hG.comp hH
lemma continuous_prod_section.{u_1} {X:Type u_1} [TopologicalSpace X]
    {U:Set ℝ} {G:ℝ × X → ℝ} (hG:ContinuousOn G (U ×ˢ univ)) {t:ℝ} (ht:t ∈ U) :
    Continuous (fun a => G (t,a)) :=
  continuousOn_univ.mp (hG.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨ht,mem_univ _⟩))
lemma continuousOn_normFirst_line.{u_1} {X:Type u_1} [TopologicalSpace X]
    (Q D:X → ℂ → ℂ)
    (hQc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => D p.1 p.2)) (v:ℂ) :
    ContinuousOn (fun p:ℝ × X => kz707 (Q p.2 (kz715 v p.1)) (D p.2 (kz715 v p.1)) v) (kz716 v ×ˢ univ):=by
  unfold kz707
  exact continuousOn_const.mul ((continuousOn_complexLine Q hQc v).inner ((continuousOn_complexLine D hDc v).mul continuousOn_const))
lemma integral_norm_line_derivative.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    (Q D:X → ℂ → ℂ)
    (hQc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => D p.1 p.2))
    (hD:∀ a z,0 < z.im → HasDerivAt (Q a) (D a z) z)
    (v:ℂ) {t:ℝ} (ht:t ∈ kz716 v) :
    HasDerivAt (fun s => ∫ a,‖Q a (kz715 v s)‖^2 ∂μ)
      (∫ a,kz707 (Q a (kz715 v t)) (D a (kz715 v t)) v ∂μ) t:=by
  refine hasDerivAt_integral_compact μ
    (fun s a => ‖Q a (kz715 v s)‖^2)
    (fun s a => kz707 (Q a (kz715 v s)) (D a (kz715 v s)) v)
    (kz717 v) ?_ ?_ ?_ ht
  · intro s hs
    exact continuous_prod_section ((continuousOn_complexLine Q hQc v).norm.pow 2) hs
  · exact continuousOn_normFirst_line Q D hQc hDc v
  · intro s hs a
    exact kz709 (hD a _ (kz719 hs))
lemma integral_normFirst_line_derivative.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    (Q D E:X → ℂ → ℂ)
    (hQc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => D p.1 p.2))
    (hEc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => E p.1 p.2))
    (hD:∀ a z,0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE:∀ a z,0 < z.im → HasDerivAt (D a) (E a z) z)
    (v:ℂ) {t:ℝ} (ht:t ∈ kz716 v) :
    HasDerivAt (fun s => ∫ a,kz707 (Q a (kz715 v s)) (D a (kz715 v s)) v ∂μ)
      (∫ a,kz708 (Q a (kz715 v t)) (D a (kz715 v t)) (E a (kz715 v t)) v ∂μ) t:=by
  refine hasDerivAt_integral_compact μ
    (fun s a => kz707 (Q a (kz715 v s)) (D a (kz715 v s)) v)
    (fun s a => kz708 (Q a (kz715 v s)) (D a (kz715 v s)) (E a (kz715 v s)) v)
    (kz717 v) ?_ ?_ ?_ ht
  · intro s hs
    exact continuous_prod_section (continuousOn_normFirst_line Q D hQc hDc v) hs
  · have hcQ:=continuousOn_complexLine Q hQc v
    have hcD:=continuousOn_complexLine D hDc v
    have hcE:=continuousOn_complexLine E hEc v
    unfold kz708
    exact continuousOn_const.mul (((hcD.mul continuousOn_const).inner (hcD.mul continuousOn_const)).add
      (hcQ.inner ((hcE.mul continuousOn_const).mul continuousOn_const)))
  · intro s hs a
    exact kz710 (hD a _ (kz719 hs)) (hE a _ (kz719 hs))
lemma normFirst_expected.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    (Q D:X → ℂ → ℂ)
    (hQc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => D p.1 p.2))
    (hD:∀ a z,0 < z.im → HasDerivAt (Q a) (D a z) z)
    (β:ℝ) (hmean:∀ z:ℂ,0 < z.im → (∫ a,‖Q a z‖^2 ∂μ) = z.im^(-β))
    (v:ℂ) {t:ℝ} (ht:t ∈ kz716 v) :
    (∫ a,kz707 (Q a (kz715 v t)) (D a (kz715 v t)) v ∂μ) =
      v.im*(-β)*(1+t*v.im)^(-β-1):=by
  have hdR:=(((hasDerivAt_id t).mul_const v.im).const_add 1).rpow_const
    (p:=-β) (Or.inl (ne_of_gt ht))
  simp only [one_mul,id_eq] at hdR
  apply (integral_norm_line_derivative μ Q D hQc hDc hD v ht).unique
  apply hdR.congr_of_eventuallyEq
  filter_upwards [(kz717 v).mem_nhds ht] with s hs
  exact (hmean (kz715 v s) (kz719 hs)).trans
    (congrArg (fun x:ℝ => x^(-β)) (kz718 v s))
lemma compact_holomorphic_line_moments.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    (Q D E:X → ℂ → ℂ)
    (hQc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => D p.1 p.2))
    (hEc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => E p.1 p.2))
    (hD:∀ a z,0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE:∀ a z,0 < z.im → HasDerivAt (D a) (E a z) z)
    (β:ℝ) (hmean:∀ z:ℂ,0 < z.im → (∫ a,‖Q a z‖^2 ∂μ) = z.im^(-β))
    (v:ℂ) :
    (∫ a,kz707 (Q a Complex.I) (D a Complex.I) v ∂μ) = -β*v.im ∧
    (∫ a,kz708 (Q a Complex.I) (D a Complex.I) (E a Complex.I) v ∂μ) =
      β*(β+1)*v.im^2:=by
  have hm' {t:ℝ} (ht:t ∈ kz716 v):=normFirst_expected μ Q D hQc hDc hD β hmean v ht
  constructor
  · simpa only [kz720,zero_mul,add_zero,Real.one_rpow,mul_one,mul_comm,mul_zero] using hm' (kz721 v)
  · have hdR:=(((((hasDerivAt_id (0:ℝ)).mul_const v.im).const_add 1).rpow_const
        (p:=-β-1) (Or.inl (by norm_num))).const_mul (v.im*(-β)))
    have he:(∫ a,kz708 (Q a (kz715 v 0)) (D a (kz715 v 0)) (E a (kz715 v 0)) v ∂μ) =
        v.im*(-β)*(1*v.im*(-β-1)*(1+0*v.im)^((-β-1)-1)):=by
      apply (integral_normFirst_line_derivative μ Q D E hQc hDc hEc hD hE v (kz721 v)).unique
      apply hdR.congr_of_eventuallyEq
      filter_upwards [(kz717 v).mem_nhds (kz721 v)] with s hs
      exact hm' hs
    simp only [kz720,one_mul,zero_mul,add_zero,Real.one_rpow,mul_one] at he
    exact he.trans (by ring)
lemma compact_holomorphic_moments.{u_1} {X:Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ:Measure X) [IsFiniteMeasure μ]
    (Q D E:X → ℂ → ℂ)
    (hQc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => D p.1 p.2))
    (hEc:Continuous (fun p:X × {z:ℂ | 0 < z.im} => E p.1 p.2))
    (hD:∀ a z,0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE:∀ a z,0 < z.im → HasDerivAt (D a) (E a z) z)
    (hQ1:∀ a,Q a Complex.I = 1)
    (β:ℝ) (hmean:∀ z:ℂ,0 < z.im → (∫ a,‖Q a z‖^2 ∂μ) = z.im^(-β)) :
    (∫ a,(Complex.I*D a Complex.I).re ∂μ) = -β/2 ∧
    (∫ a,(Complex.I*D a Complex.I).im ∂μ) = 0 ∧
    (∫ a,‖Complex.I*D a Complex.I‖^2 ∂μ) = β*(β+1)/4:=by
  obtain ⟨hx,hxx⟩:=compact_holomorphic_line_moments μ Q D E hQc hDc hEc hD hE β hmean 1
  obtain ⟨hy,hyy⟩:=compact_holomorphic_line_moments μ Q D E hQc hDc hEc hD hE β hmean Complex.I
  have hx':=hx
  have hy':=hy
  simp_rw [hQ1,kz711] at hx'
  simp_rw [hQ1,kz712] at hy'
  rw [integral_const_mul] at hx' hy'
  simp only [Complex.one_im,Complex.I_im,mul_zero,mul_one] at hx' hy' hxx hyy
  have hDc0:Continuous (fun a => D a Complex.I) :=
    hDc.comp (continuous_id.prodMk (continuous_const (y:=(⟨Complex.I,by simp⟩:{z:ℂ | 0 < z.im}))))
  have hQc0:Continuous (fun a => Q a Complex.I) :=
    hQc.comp (continuous_id.prodMk (continuous_const (y:=(⟨Complex.I,by simp⟩:{z:ℂ | 0 < z.im}))))
  have hEc0:Continuous (fun a => E a Complex.I) :=
    hEc.comp (continuous_id.prodMk (continuous_const (y:=(⟨Complex.I,by simp⟩:{z:ℂ | 0 < z.im}))))
  have hi (v:ℂ):Integrable (fun a => kz708 (Q a Complex.I) (D a Complex.I) (E a Complex.I) v) μ:=by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact kz714.comp (hQc0.prodMk (hDc0.prodMk (hEc0.prodMk continuous_const)))
  have hsum:4*(∫ a,‖D a Complex.I‖^2 ∂μ) = β*(β+1):=by
    rw [← integral_const_mul]
    calc
      _ = ∫ a,kz708 (Q a Complex.I) (D a Complex.I) (E a Complex.I) 1+
          kz708 (Q a Complex.I) (D a Complex.I) (E a Complex.I) Complex.I ∂μ:=by
        apply integral_congr_ae
        exact Eventually.of_forall (fun a => (kz713 _ _ _).symm)
      _ = _:=by rw [integral_add (hi 1) (hi Complex.I),hxx,hyy]; norm_num
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    zero_sub,zero_add,Complex.norm_mul,Complex.norm_I]
  rw [integral_neg]
  exact ⟨by linarith,by linarith,by linarith⟩
lemma kz722 (g:kz140) :
    kz202 (kz183 g) Complex.I = Complex.I*deriv (kz160 (kz183 g)) Complex.I:=by
  simp only [kz202,Complex.I_im,Complex.ofReal_one,mul_one,kz705,div_one]
lemma kz723:Continuous (fun g:kz140 => kz202 (kz183 g) Complex.I):=by
  simp_rw [kz722]
  have hc:Continuous (fun p:kz140 × kz145 => deriv (kz160 (kz183 p.1)) p.2):=by
    simpa only [iteratedDeriv_one] using kz704 1
  exact (hc.comp (continuous_id.prodMk (continuous_const (y:=(⟨Complex.I,by simp [kz145]⟩:kz145))))).const_mul _
lemma kz724 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:∀ z:kz145,∀ f:C(kz140,ℝ),
      (∫ g,kz198 g z*f (kz192 g z) ∂(P:Measure kz140)) =
        (z.val.im)^(-β)*(∫ g,f g ∂(P:Measure kz140))) :
    (∫ g,(kz202 (kz183 g) Complex.I).re ∂(P:Measure kz140)) = -β/2 ∧
    (∫ g,(kz202 (kz183 g) Complex.I).im ∂(P:Measure kz140)) = 0 ∧
    (∫ g,‖kz202 (kz183 g) Complex.I‖^2 ∂(P:Measure kz140)) = β*(β+1)/4:=by
  have hcD:Continuous (fun p:kz140 × kz145 => deriv (kz160 (kz183 p.1)) p.2):=by
    simpa only [iteratedDeriv_one] using kz704 1
  have hcE:Continuous (fun p:kz140 × kz145 => deriv (deriv (kz160 (kz183 p.1))) p.2):=by
    simpa only [show (2:ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using kz704 2
  have hm (z:ℂ) (hz:0 < z.im) :
      (∫ g,‖kz160 (kz183 g) z‖^2 ∂(P:Measure kz140)) = z.im^(-β):=by
    simpa only [kz198,ContinuousMap.one_apply,mul_one,integral_const,ProbabilityMeasure.coeFn_univ,
      probReal_univ,smul_eq_mul,one_mul] using hP ⟨z,hz⟩ 1
  have hE (g:kz140) (z:ℂ) (hz:0 < z.im) :
      HasDerivAt (deriv (kz160 (kz183 g)))
        (deriv (deriv (kz160 (kz183 g))) z) z :=
    ((kz700 g).analyticOnNhd kz146 z hz).deriv.differentiableAt.hasDerivAt
  simp_rw [kz722]
  exact compact_holomorphic_moments (P:Measure kz140)
    (fun g => kz160 (kz183 g)) (fun g => deriv (kz160 (kz183 g)))
    (fun g => deriv (deriv (kz160 (kz183 g))))
    kz701 hcD hcE
    (fun g z hz => kz210 (kz184 g).1 hz)
    hE kz705 β hm
lemma kz725 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:kz667 P β) (hβ:1 < β) :
    (∫ g,kz205 (kz183 g) ((β+3)/4) Complex.I ∂(P:Measure kz140)) ≤ 0:=by
  have hk:0 < (β+3)/4:=by linarith
  have hg:∀ᵐ g ∂(P:Measure kz140),∀ᵐ ξ:ℂ,kz215 (kz183 g) ((β+3)/4) ξ:=by
    filter_upwards [kz670 P β hP] with g hg
    apply kz538 g hβ
    have he:kz662 β g = (∫⁻ z in kz459,
        ENNReal.ofReal (z.im^(β+1)*‖kz183 g z‖⁻¹^4)):=by
      simp only [kz662,kz660]
      apply setLIntegral_congr_fun kz461
      intro z hz
      dsimp only
      rw [kz466 g hz.1,ENNReal.ofReal_mul (Real.rpow_nonneg hz.1.le _)]
    exact he ▸ hg
  have hi:=kz699 P β hP hk (by ring) hg
  have hc:Continuous (fun g:kz140 => kz205 (kz183 g) ((β+3)/4) Complex.I) :=
    (kz374 _).comp
      (continuous_id.prodMk (continuous_const (y:=kz440)))
  have hInt:=hc.integrable_of_hasCompactSupport (μ:=(P:Measure kz140)) (HasCompactSupport.of_compactSpace _)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt]
  have ht:=ENNReal.toReal_mono (kz693 P ((β+3)/4) (-1)).ne hi
  simpa only [kz673,one_mul,neg_one_mul,sub_nonpos] using ht
lemma kz726 (P:ProbabilityMeasure kz140) (β:ℝ)
    (hP:∀ z:kz145,∀ f:C(kz140,ℝ),
      (∫ g,kz198 g z*f (kz192 g z) ∂(P:Measure kz140)) =
        (z.val.im)^(-β)*(∫ g,f g ∂(P:Measure kz140)))
    {k:ℝ} (hk:k ≠ 0) :
    k^2 * (∫ g,kz205 (kz183 g) k Complex.I ∂(P:Measure kz140)) =
      k*(k-1) - (2*k-1)*β/2 + β*(β+1)/4:=by
  obtain ⟨hr,-,hs⟩:=kz724 P β hP
  have hiR:Integrable (fun g:kz140 => (2*k-1)*(kz202 (kz183 g) Complex.I).re) (P:Measure kz140) :=
    (continuous_const.mul (Complex.continuous_re.comp kz723)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS:Integrable (fun g:kz140 => ‖kz202 (kz183 g) Complex.I‖^2) (P:Measure kz140) :=
    (kz723.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_const_mul]
  calc
    _ = ∫ g,k*(k-1)+(2*k-1)*(kz202 (kz183 g) Complex.I).re+
        ‖kz202 (kz183 g) Complex.I‖^2 ∂(P:Measure kz140):=by
      apply integral_congr_ae
      exact Eventually.of_forall (fun g => kz209 (kz184 g).1 (by simp [kz145]) k hk)
    _ = _:=by
      have h1:=integral_add ((integrable_const (k*(k-1))).add hiR) hiS
      have h2:=integral_add (integrable_const (k*(k-1))) hiR
      simp only [Pi.add_apply] at h1 h2
      rw [h1,h2]
      simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,hr,hs]
      ring
theorem kz727:kz626 ≤ 2:=by
  by_contra! hρ
  obtain ⟨P,hP⟩:=kz629 hρ
  have hPb:kz667 P kz627:=by
    intro z f hf
    exact weighted_lintegral_of_continuous (P:Measure kz140) (kz567 z)
      (fun g => (kz199 g z).le) (kz568 z) ((z.val.im)^(-kz627))
      (Real.rpow_nonneg z.2.le _) (hP z) f hf
  have hβ:=kz628 hρ
  have hn:=kz725 P kz627 hPb hβ
  have hv:=kz726 P kz627 hP (k:=(kz627+3)/4) (by linarith)
  have hp:0 < ((kz627+3)/4)*((kz627+3)/4-1):=mul_pos (by linarith) (by linarith)
  have he:((kz627+3)/4)*((kz627+3)/4-1) -
      (2*((kz627+3)/4)-1)*kz627/2 + kz627*(kz627+1)/4 =
      ((kz627+3)/4)*((kz627+3)/4-1):=by ring
  rw [he] at hv
  have hnon:=mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ((kz627+3)/4)) hn
  linarith
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
def kz728 (r θ:ℝ):ℂ:=(r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)
def kz729:Set ℝ:=Icc (-Real.pi/4) (Real.pi/4)
def arcD (r θ:ℝ):ℝ:=1+2*r*Real.cos θ+r^2
def arcX (r θ:ℝ):ℝ:=2*r*Real.sin θ/arcD r θ
def arcY (r θ:ℝ):ℝ:=(1-r^2)/arcD r θ
def kz730 (r θ:ℝ):ℝ:=(4*r^2+2*r*(1+r^2)*Real.cos θ)/(arcD r θ)^2
lemma kz731 {θ:ℝ} (hθ:θ ∈ kz729):0 ≤ Real.cos θ:=by
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> have hp:=Real.pi_pos <;> dsimp [kz729] at hθ <;> linarith [hθ.1,hθ.2]
lemma kz732 {r θ:ℝ} (hr:1/2 ≤ r) (hr1:r < 1) (hθ:θ ∈ kz729) :
    1 ≤ arcD r θ ∧ arcD r θ ≤ (1+r)^2 ∧ arcD r θ ≤ 4:=by
  have hc:=kz731 hθ
  have hc1:=Real.cos_le_one θ
  have hr0:0 ≤ r:=by linarith
  have hr2:0 ≤ 2*r:=by positivity
  dsimp [arcD]
  have hm:=mul_nonneg hr2 hc
  have hm1:=mul_le_mul_of_nonneg_left hc1 hr2
  constructor
  · nlinarith [sq_nonneg r]
  constructor <;> nlinarith
lemma kz733 {r θ:ℝ} (hr:1/2 ≤ r) (hr1:r < 1) (hθ:θ ∈ kz729) :
    arcX r θ ∈ Icc (-1) 1:=by
  have hd:=kz732 hr hr1 hθ
  have hD:0 < arcD r θ:=by linarith [hd.1]
  have hc:=kz731 hθ
  have hs:=Real.neg_one_le_sin θ
  have hs1:=Real.sin_le_one θ
  have h2r:0 ≤ 2*r:=by linarith
  have hm1:=mul_le_mul_of_nonneg_left hs h2r
  have hm2:=mul_le_mul_of_nonneg_left hs1 h2r
  have hD2:2*r ≤ arcD r θ:=by
    dsimp [arcD]
    nlinarith [mul_nonneg h2r hc,sq_nonneg (r-1)]
  constructor
  · exact (le_div_iff₀ hD).mpr (by nlinarith)
  · exact (div_le_iff₀ hD).mpr (by nlinarith)
lemma kz734 {r θ:ℝ} (hr:1/2 ≤ r) (hr1:r < 1) (hθ:θ ∈ kz729) :
    (1-r)/2 ≤ arcY r θ ∧ arcY r θ ≤ 2*(1-r):=by
  have hd:=kz732 hr hr1 hθ
  have hD:0 < arcD r θ:=by linarith [hd.1]
  have hr0:0 ≤ r:=by linarith
  have hd0:0 ≤ 1-r:=by linarith
  constructor
  · apply (le_div_iff₀ hD).mpr
    have h:=mul_le_mul_of_nonneg_left hd.2.1 (by positivity:0 ≤ (1-r)/2)
    have hb:(1-r)/2*(1+r)^2 ≤ 1-r^2:=by nlinarith [mul_nonneg hd0 (sq_nonneg (1+r))]
    exact h.trans hb
  · apply (div_le_iff₀ hD).mpr
    have h:=mul_le_mul_of_nonneg_left hd.1 (by positivity:0 ≤ 2*(1-r))
    nlinarith [sq_nonneg (r-1)]
lemma kz735 {r θ:ℝ} (hD:arcD r θ ≠ 0) :
    HasDerivAt (arcX r) (kz730 r θ) θ:=by
  have hn:=(Real.hasDerivAt_sin θ).const_mul (2*r)
  have hd:=(((Real.hasDerivAt_cos θ).const_mul (2*r)).const_add 1).add_const (r^2)
  have h:=hn.div hd hD
  change HasDerivAt (arcX r) _ θ at h
  have he:kz730 r θ =
      (2*r*Real.cos θ*arcD r θ-2*r*Real.sin θ*(2*r * -Real.sin θ))/(arcD r θ)^2:=by
    unfold kz730 arcD
    congr 1
    have hc:=Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg r]
  rw [he]
  exact h
lemma kz736 {r θ:ℝ} (hr:1/2 ≤ r) (hr1:r < 1) (hθ:θ ∈ kz729) :
    1/16 ≤ kz730 r θ:=by
  have hd:=kz732 hr hr1 hθ
  have hD:0 < arcD r θ:=by linarith [hd.1]
  have hc:=kz731 hθ
  dsimp only [kz730]
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  have hm:0 ≤ 2*r*(1+r^2)*Real.cos θ:=mul_nonneg (by positivity) hc
  have hsq:(arcD r θ)^2 ≤ 16:=by nlinarith [hd.2.2]
  nlinarith [sq_nonneg (r-1/2)]
lemma kz737 {r:ℝ} (hr:1/2 ≤ r) (hr1:r < 1) :
    ContinuousOn (kz730 r) kz729:=by
  apply ContinuousOn.div
  · fun_prop
  · unfold arcD
    fun_prop
  · intro θ hθ
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (kz732 hr hr1 hθ).1))
lemma kz738 {r:ℝ} (hr:1/2 ≤ r) (hr1:r < 1):MonotoneOn (arcX r) kz729:=by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro θ hθ
    exact (kz735 (ne_of_gt (lt_of_lt_of_le zero_lt_one (kz732 hr hr1 hθ).1))).continuousAt.continuousWithinAt
  · intro θ hθ
    exact (kz735 (ne_of_gt (lt_of_lt_of_le zero_lt_one (kz732 hr hr1 (interior_subset hθ)).1))).hasDerivWithinAt
  · intro θ hθ
    exact le_trans (by norm_num) (kz736 hr hr1 (interior_subset hθ))
lemma kz739 (r θ:ℝ):‖kz728 r θ‖ = |r|:=by
  simp [kz728,Complex.norm_exp]
lemma kz740 (r θ:ℝ):(kz728 r θ).re = r*Real.cos θ:=by
  simp [kz728,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
lemma kz741 (r θ:ℝ):(kz728 r θ).im = r*Real.sin θ:=by
  simp [kz728,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]
lemma kz742 (r θ:ℝ):‖1+kz728 r θ‖^2 = arcD r θ:=by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,kz740,kz741,zero_add]
  dsimp [arcD]
  nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg r]
end Brennan
end
noncomputable section
namespace Brennan
seal kz183 kz198 kz192
lemma kz743 {r:ℝ} (hr:0 ≤ r) (hr1:r < 1) (θ:ℝ):kz728 r θ ∈ disk:=by
  simpa [disk,kz739,abs_of_nonneg hr] using hr1
lemma kz744 {r:ℝ} (hr:0 ≤ r) (hr1:r < 1) (θ:ℝ) : -kz728 r θ ∈ disk:=by
  simpa only [disk,Metric.mem_ball,dist_zero_right,norm_neg] using kz743 hr hr1 θ
lemma kz745 (z:ℂ):(kz163 z).re = -2*z.im/‖1-z‖^2:=by
  simp only [kz163,Complex.div_re,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.add_re,Complex.add_im,Complex.one_re,
    Complex.one_im,Complex.sub_re,Complex.sub_im,Complex.sq_norm,Complex.normSq_apply]
  ring
lemma kz746 {r:ℝ} (hr:0 ≤ r) (hr1:r < 1) (θ:ℝ) :
    kz163 (-kz728 r θ) = (arcX r θ:ℂ)+(arcY r θ:ℂ)*Complex.I:=by
  have hz:=kz744 hr hr1 θ
  apply Complex.ext
  · rw [kz745]
    simp only [Complex.neg_im,kz741,sub_neg_eq_add,kz742,
      Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im]
    dsimp [arcX]
    ring
  · rw [kz167 hz]
    simp only [norm_neg,kz739,abs_of_nonneg hr,sub_neg_eq_add,kz742,
      Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.ofReal_re,Complex.I_im]
    simp [arcY]
lemma kz747 (g:kz140) {η:ℝ} (hη:1/2 ≤ η) (hη4:η ≤ 4) :
    kz198 g (kz562 0 η (by linarith)) ≤ 1562500:=by
  let z:=kz562 0 η (by linarith:0 < η)
  have hb:=kz589 g z
  have he:‖z.val+Complex.I‖ = η+1:=by
    have hz:z.val+Complex.I = ((η+1:ℝ):ℂ)*Complex.I:=by
      dsimp [z,kz562]
      push_cast
      ring
    rw [hz,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  have hη0:0 < η:=by linarith
  have ht:‖kz160 (kz183 g) z‖ ≤ 1250:=by
    rw [he] at hb
    simp only [z,kz562,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hb
    have hp:(η+1)^4 ≤ (5:ℝ)^4:=pow_le_pow_left₀ (by linarith) (by linarith) _
    apply hb.trans
    apply (div_le_iff₀ hη0).mpr
    norm_num at hp
    linarith
  unfold kz198
  change ‖kz160 (kz183 g) z‖^2 ≤ _
  nlinarith [norm_nonneg (kz160 (kz183 g) z)]
lemma kz748 (g:kz140) (x v y:ℝ) (hv:0 < v)
    (hy:v/2 ≤ y) (hy4:y ≤ 4*v) :
    kz198 g (kz562 x y (by linarith)) ≤
      1562500*kz198 g (kz562 x v hv):=by
  have hη:1/2 ≤ y/v:=(le_div_iff₀ hv).mpr (by linarith)
  have hη4:y/v ≤ 4:=(div_le_iff₀ hv).mpr hy4
  have hη0:0 < y/v:=by linarith
  have he:kz561 (kz562 x v hv) (kz562 0 (y/v) hη0) = kz562 x y (by linarith):=by
    rw [kz564]
    apply Subtype.ext
    dsimp [kz562]
    congr 2 <;> simp [mul_div_cancel₀ y hv.ne']
  have hc:=kz201 g (kz562 x v hv) (kz562 0 (y/v) hη0)
  change _ = kz198 g (kz561 _ _) at hc
  rw [he] at hc
  rw [← hc,mul_comm (1562500:ℝ)]
  exact mul_le_mul_of_nonneg_left (kz747 _ hη hη4) (kz199 g _).le
lemma kz749 {f:ℂ → ℂ} (hf:kz2 f) {w:ℂ} (hw:w ∈ disk) :
    ‖deriv f w‖^(-2:ℝ) ≤ 16*kz198 (kz185 (kz175 f) (kz179 hf))
      ⟨kz163 w,kz168 hw⟩:=by
  let g:=kz185 (kz175 f) (kz179 hf)
  let z:kz145:=⟨kz163 w,kz168 hw⟩
  have he:=(kz186 (kz179 hf)).deriv kz146 z.2
  have hfhe:EqOn (kz176 (kz175 f)) f disk:=fun _ hz => kz182 hz
  have hd:=(kz178 (kz179 hf).1.1 hw).deriv
  rw [hfhe.deriv Metric.isOpen_ball hw] at hd
  have hw1:‖w‖ < 1:=by simpa [disk] using hw
  have hb:‖1-w‖ ≤ 2:=(norm_sub_le _ _).trans (by simpa using (show 1+‖w‖ ≤ 2 by linarith))
  have ha:0 < ‖deriv (kz175 f) (kz163 w)‖:=norm_pos_iff.mpr
    (kz91 kz146 (kz179 hf).1 z.2)
  rw [hd,norm_div,norm_pow,Real.rpow_neg (by positivity),Real.rpow_two]
  unfold kz198
  change _ ≤ 16*‖kz160 (kz183 g) z‖^2
  rw [kz160,he,norm_inv]
  have hb4:‖1-w‖^4 ≤ (2:ℝ)^4:=pow_le_pow_left₀ (norm_nonneg _) hb _
  have hz0:‖1-w‖ ≠ 0:=norm_ne_zero_iff.mpr (kz165 hw)
  dsimp only [z]
  field_simp [ha.ne',hz0]
  nlinarith
end Brennan
end
noncomputable section
namespace Brennan
seal kz183 kz198 kz192
lemma kz750:Continuous kz567:=by
  have he:kz567 = fun z => kz569 z 1:=by
    funext z
    ext g
    simp only [kz570,ContinuousMap.one_apply,mul_one]
    rfl
  rw [he]
  exact kz574 1
def kz751 (v:ℝ) (hv:0 < v):C(kz140,ℝ) :=
  ∫ x in (-1:ℝ)..1,kz567 (kz562 x v hv)
lemma kz752 (v:ℝ) (hv:0 < v) (g:kz140) :
    kz751 v hv g = ∫ x in (-1:ℝ)..1,kz198 g (kz562 x v hv):=by
  exact ((ContinuousMap.evalCLM ℝ g).intervalIntegral_comp_comm
    ((kz750.comp (continuous_halfPoint continuous_id continuous_const (fun _ => hv))).intervalIntegrable (μ:=volume) _ _)).symm
lemma kz753 (g:kz140) (v:ℝ) (hv:0 < v) :
    Continuous (fun x => kz198 g (kz562 x v hv)) :=
  kz200.comp (continuous_const.prodMk
    (continuous_halfPoint continuous_id continuous_const (fun _ => hv)))
lemma kz754 (v:ℝ) (hv:0 < v) :
    kz751 (v/2) (by positivity) = kz581 (kz751 v hv):=by
  ext g
  rw [kz752]
  change _ = (1/2:ℝ)*(kz198 g kz579 * kz751 v hv (kz192 g kz579)+
    kz198 g kz580 * kz751 v hv (kz192 g kz580))
  rw [kz752,kz752,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have hL (x:ℝ):kz198 g kz579 * kz198 (kz192 g kz579) (kz562 x v hv) =
      kz198 g (kz562 ((1/2)*x+(-(1/2))) (v/2) (by positivity)):=by
    rw [kz201]
    congr 1
    apply Subtype.ext
    apply Complex.ext <;> simp [kz579,kz562,kz148] <;> ring
  have hR (x:ℝ):kz198 g kz580 * kz198 (kz192 g kz580) (kz562 x v hv) =
      kz198 g (kz562 ((1/2)*x+1/2) (v/2) (by positivity)):=by
    rw [kz201]
    congr 1
    apply Subtype.ext
    apply Complex.ext <;> simp [kz580,kz562,kz148] <;> ring
  simp_rw [hL,hR]
  have hl:=intervalIntegral.integral_comp_mul_add
    (f:=fun x => kz198 g (kz562 x (v/2) (by positivity)))
    (a:=(-1:ℝ)) (b:=1) (by norm_num:(1/2:ℝ) ≠ 0) (-1/2)
  have hr:=intervalIntegral.integral_comp_mul_add
    (f:=fun x => kz198 g (kz562 x (v/2) (by positivity)))
    (a:=(-1:ℝ)) (b:=1) (by norm_num:(1/2:ℝ) ≠ 0) (1/2)
  norm_num at hl hr
  have hi:=(kz753 g (v/2) (by positivity)).intervalIntegrable (μ:=volume)
  have hs:=intervalIntegral.integral_add_adjacent_intervals (hi (-1) 0) (hi 0 1)
  rw [hl,hr]
  linarith [hs]
lemma kz755 (n:ℕ) :
    kz751 ((1/2:ℝ)^n) (by positivity) = (kz581^n) (kz751 1 zero_lt_one):=by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he:(1/2:ℝ)^(n+1) = (1/2:ℝ)^n/2:=by rw [pow_succ]; ring
    have hm:kz751 ((1/2:ℝ)^(n+1)) (by positivity) = kz751 ((1/2:ℝ)^n/2) (by positivity):=by congr 1
    rw [hm,kz754 _ (by positivity),ih,pow_succ',mul_apply_eq_comp]
lemma kz756 (n:ℕ) (g:kz140) :
    (∫ x in (-1:ℝ)..1,kz198 g (kz562 x ((1/2:ℝ)^n) (by positivity))) ≤
      ‖kz751 1 zero_lt_one‖*‖kz581^n‖:=by
  rw [← kz752,kz755,mul_comm]
  exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm _ _).trans ((kz581^n).le_opNorm _))
lemma kz757 {lam:ℝ} (hlam:2 < lam) :
    ∃ C:ℝ,0 < C ∧ ∀ n:ℕ,‖kz581^n‖ ≤ C*lam^n:=by
  have hl:0 < lam:=by linarith
  obtain ⟨N,hN⟩:=eventually_atTop.mp (norm_pow_eventually_le kz581 kz585
    (lt_of_le_of_lt kz727 hlam))
  let C:ℝ:=1 + ∑ j ∈ Finset.range N,‖kz581^j‖/lam^j
  have hC:1 ≤ C:=le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => div_nonneg (norm_nonneg (kz581^j)) (pow_pos hl j).le))
  refine ⟨C,zero_lt_one.trans_le hC,fun n => ?_⟩
  by_cases hn:N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (pow_pos hl n).le hC)
  · have hs:‖kz581^n‖/lam^n ≤ ∑ j ∈ Finset.range N,‖kz581^j‖/lam^j :=
      Finset.single_le_sum (fun j _ => div_nonneg (norm_nonneg (kz581^j)) (pow_pos hl j).le) (Finset.mem_range.mpr (lt_of_not_ge hn))
    apply (div_le_iff₀ (pow_pos hl n)).mp
    exact hs.trans (by dsimp [C]; linarith)
end Brennan
end
noncomputable section
namespace Brennan
seal kz183 kz198 kz192
lemma kz758 (r:ℝ):Continuous (kz728 r):=by
  unfold kz728
  fun_prop
lemma kz759 {f:ℂ → ℂ} (hf:kz1 f disk)
    {r:ℝ} (hr:0 ≤ r) (hr1:r < 1) (t:ℝ) :
    Continuous (fun θ => ‖deriv f (kz728 r θ)‖^t):=by
  have hc:Continuous (fun θ => deriv f (kz728 r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (kz758 r)
      (kz743 hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (kz91 Metric.isOpen_ball hf (kz743 hr hr1 θ))))
lemma kz760 {f:ℂ → ℂ} (hf:kz1 f disk)
    {r:ℝ} (hr:0 ≤ r) (hr1:r < 1) (t:ℝ) :
    Continuous (fun θ => ‖deriv f (-kz728 r θ)‖^t):=by
  have hc:Continuous (fun θ => deriv f (-kz728 r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (kz758 r).neg
      (kz744 hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (kz91 Metric.isOpen_ball hf (kz744 hr hr1 θ))))
lemma kz761 {f:ℂ → ℂ} (hf:kz2 f) {r v:ℝ}
    (hr:1/2 ≤ r) (hr1:r < 1) (hv:0 < v) (hvδ:v ≤ 1-r) (hδv:1-r ≤ 2*v) :
    (∫ θ in (-Real.pi/4)..(Real.pi/4),‖deriv f (-kz728 r θ)‖^(-2:ℝ)) ≤
      400000000 * kz751 v hv (kz185 (kz175 f) (kz179 hf)):=by
  let g:=kz185 (kz175 f) (kz179 hf)
  let W:ℝ → ℝ:=fun x => kz198 g (kz562 x v hv)
  have hW:Continuous W:=kz753 g v hv
  have hab : -Real.pi/4 ≤ Real.pi/4:=by linarith [Real.pi_pos]
  have hu:uIcc (-Real.pi/4) (Real.pi/4) = kz729:=uIcc_of_le hab
  have hX (θ:ℝ) (hθ:θ ∈ kz729):HasDerivAt (arcX r) (kz730 r θ) θ :=
    kz735 (ne_of_gt (lt_of_lt_of_le zero_lt_one (kz732 hr hr1 hθ).1))
  have hXc:ContinuousOn (arcX r) kz729:=fun θ hθ => (hX θ hθ).continuousAt.continuousWithinAt
  have hprod:ContinuousOn (fun θ => W (arcX r θ)*kz730 r θ) kz729 :=
    (hW.comp_continuousOn hXc).mul (kz737 hr hr1)
  have hi:=intervalIntegral.integral_mono_on hab
    ((kz760 hf.1 (by linarith) hr1 (-2)).intervalIntegrable (μ:=volume) _ _)
    ((hprod.const_mul 400000000).intervalIntegrable_of_Icc hab)
    (fun θ hθ => show ‖deriv f (-kz728 r θ)‖^(-2:ℝ) ≤
      400000000*(W (arcX r θ)*kz730 r θ) from by
      have hθ':θ ∈ kz729:=hθ
      have hy:=kz734 hr hr1 hθ'
      have hz:(⟨kz163 (-kz728 r θ),kz168 (kz744 (by linarith) hr1 θ)⟩:kz145) =
          kz562 (arcX r θ) (arcY r θ) (by linarith) :=
        Subtype.ext (kz746 (by linarith) hr1 θ)
      have hc:=kz749 hf (kz744 (by linarith) hr1 θ)
      rw [hz] at hc
      have hb:=kz748 g (arcX r θ) v (arcY r θ) hv (by linarith) (by linarith)
      have hd:=kz736 hr hr1 hθ'
      have hWp:0 ≤ W (arcX r θ):=(kz199 g _).le
      have hm:=mul_nonneg hWp (sub_nonneg.mpr hd)
      change _ ≤ 16*kz198 g _ at hc
      change kz198 g _ ≤ 1562500*W (arcX r θ) at hb
      nlinarith)
  rw [intervalIntegral.integral_const_mul] at hi
  have hchange:=intervalIntegral.integral_comp_mul_deriv
    (fun θ hθ => hX θ (hu ▸ hθ)) (hu ▸ kz737 hr hr1) hW
  change (∫ θ in (-Real.pi/4)..(Real.pi/4),W (arcX r θ)*kz730 r θ) = _ at hchange
  rw [hchange] at hi
  have hlo : -Real.pi/4 ∈ kz729:=⟨le_rfl,hab⟩
  have hhi:Real.pi/4 ∈ kz729:=⟨hab,le_rfl⟩
  have hm:=kz738 hr hr1 hlo hhi hab
  have hb:=intervalIntegral.integral_mono_interval (kz733 hr hr1 hlo).1 hm
    (kz733 hr hr1 hhi).2
    (Eventually.of_forall (fun x => (kz199 g (kz562 x v hv)).le))
    (hW.intervalIntegrable (μ:=volume) (-1) 1)
  rw [kz752]
  exact hi.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
lemma kz762 {f:ℂ → ℂ} (hf:kz2 f) {r:ℝ}
    (hr:1/2 ≤ r) (hr1:r < 1) (n:ℕ)
    (hvδ:(1/2:ℝ)^n ≤ 1-r) (hδv:1-r ≤ 2*(1/2:ℝ)^n) :
    (∫ θ in (-Real.pi/4)..(Real.pi/4),‖deriv f (-kz728 r θ)‖^(-2:ℝ)) ≤
      (400000000*‖kz751 1 zero_lt_one‖)*‖kz581^n‖:=by
  have hb:=kz761 hf hr hr1 (by positivity) hvδ hδv
  have hm:=kz756 n (kz185 (kz175 f) (kz179 hf))
  rw [← kz752] at hm
  exact hb.trans ((mul_le_mul_of_nonneg_left hm (by norm_num)).trans_eq (by ring))
end Brennan
end
noncomputable section
namespace Brennan
seal kz183 kz198 kz192
def kz763 (f:ℂ → ℂ) (α z:ℂ):ℂ:=f (α*z)/α
lemma kz764 {α:ℂ} (hα:‖α‖ = 1):MapsTo (fun z => α*z) disk disk:=by
  intro z hz
  simpa [disk,norm_mul,hα] using hz
lemma kz765 {f:ℂ → ℂ} (hf:DifferentiableOn ℂ f disk)
    {α z:ℂ} (hα:‖α‖ = 1) (hz:z ∈ disk) :
    HasDerivAt (kz763 f α) (deriv f (α*z)) z:=by
  have hα0:α ≠ 0:=by intro h; simp [h] at hα
  have hd:=((hf _ (kz764 hα hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (kz764 hα hz))).hasDerivAt
  convert (hd.comp z ((hasDerivAt_id z).const_mul α)).div_const α using 1 <;> try rfl
  simp [hα0]
lemma kz766 {f:ℂ → ℂ} (hf:kz2 f) {α:ℂ} (hα:‖α‖ = 1) :
    kz2 (kz763 f α):=by
  have hα0:α ≠ 0:=by intro h; simp [h] at hα
  refine ⟨⟨fun z hz => (kz765 hf.1.1 hα hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    exact mul_left_cancel₀ hα0 (hf.1.2 (kz764 hα hz) (kz764 hα hw)
      ((div_left_inj' hα0).mp he))
  · simp [kz763,hf.2.1]
  · rw [(kz765 hf.1.1 hα (show (0:ℂ) ∈ disk by simp [disk])).deriv]
    simpa using hf.2.2
lemma kz767 (r θ c:ℝ) :
    (-Complex.exp ((c:ℂ)*Complex.I))*(-kz728 r θ) = kz728 r (θ+c):=by
  simp only [kz728,Complex.ofReal_add,add_mul,Complex.exp_add,neg_mul_neg]
  ring
lemma kz768 {f:ℂ → ℂ} (hf:kz2 f) {r:ℝ}
    (hr:1/2 ≤ r) (hr1:r < 1) (n:ℕ)
    (hvδ:(1/2:ℝ)^n ≤ 1-r) (hδv:1-r ≤ 2*(1/2:ℝ)^n) (c:ℝ) :
    (∫ θ in (c-Real.pi/4)..(c+Real.pi/4),‖deriv f (kz728 r θ)‖^(-2:ℝ)) ≤
      (400000000*‖kz751 1 zero_lt_one‖)*‖kz581^n‖:=by
  let α:=-Complex.exp ((c:ℂ)*Complex.I)
  have hα:‖α‖ = 1:=by simp [α,Complex.norm_exp]
  have hb:=kz762 (kz766 hf hα) hr hr1 n hvδ hδv
  have he (θ:ℝ):deriv (kz763 f α) (-kz728 r θ) = deriv f (kz728 r (θ+c)):=by
    rw [(kz765 hf.1.1 hα (kz744 (by linarith) hr1 θ)).deriv]
    rw [show α*(-kz728 r θ) = kz728 r (θ+c) from kz767 r θ c]
  simp_rw [he] at hb
  rw [intervalIntegral.integral_comp_add_right (f:=fun θ => ‖deriv f (kz728 r θ)‖^(-2:ℝ)) c] at hb
  convert hb using 1
  congr 1 <;> ring
lemma kz769 (r:ℝ):Periodic (kz728 r) (2*Real.pi):=by
  simpa [kz728,circleMap] using periodic_circleMap (0:ℂ) r
lemma kz770 {f:ℂ → ℂ} (hf:kz2 f) {r:ℝ}
    (hr:1/2 ≤ r) (hr1:r < 1) (n:ℕ)
    (hvδ:(1/2:ℝ)^n ≤ 1-r) (hδv:1-r ≤ 2*(1/2:ℝ)^n) :
    (∫ θ in -Real.pi..Real.pi,‖deriv f (kz728 r θ)‖^(-2:ℝ)) ≤
      (1600000000*‖kz751 1 zero_lt_one‖)*‖kz581^n‖:=by
  let F:ℝ → ℝ:=fun θ => ‖deriv f (kz728 r θ)‖^(-2:ℝ)
  have hF:=(kz759 hf.1 (by linarith) hr1 (-2)).intervalIntegrable (μ:=volume)
  have hper:Periodic F (2*Real.pi):=(kz769 r).comp (fun z => ‖deriv f z‖^(-2:ℝ))
  have hshift:=hper.intervalIntegral_add_eq (-Real.pi) (-Real.pi/4)
  have h1:=kz768 hf hr hr1 n hvδ hδv 0
  have h2:=kz768 hf hr hr1 n hvδ hδv (Real.pi/2)
  have h3:=kz768 hf hr hr1 n hvδ hδv Real.pi
  have h4:=kz768 hf hr hr1 n hvδ hδv (3*Real.pi/2)
  have e1:(0:ℝ)-Real.pi/4 = -Real.pi/4:=by ring
  have e2:(0:ℝ)+Real.pi/4 = Real.pi/4:=by ring
  have e3:Real.pi/2-Real.pi/4 = Real.pi/4:=by ring
  have e4:Real.pi/2+Real.pi/4 = 3*Real.pi/4:=by ring
  have e5:Real.pi-Real.pi/4 = 3*Real.pi/4:=by ring
  have e6:Real.pi+Real.pi/4 = 5*Real.pi/4:=by ring
  have e7:3*Real.pi/2-Real.pi/4 = 5*Real.pi/4:=by ring
  have e8:3*Real.pi/2+Real.pi/4 = 7*Real.pi/4:=by ring
  rw [e1,e2] at h1
  rw [e3,e4] at h2
  rw [e5,e6] at h3
  rw [e7,e8] at h4
  have ha:=intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (Real.pi/4)) (hF (Real.pi/4) (3*Real.pi/4))
  have hb:=intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (3*Real.pi/4)) (hF (3*Real.pi/4) (5*Real.pi/4))
  have hc:=intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (5*Real.pi/4)) (hF (5*Real.pi/4) (7*Real.pi/4))
  have es1 : -Real.pi+2*Real.pi = Real.pi:=by ring
  have es2 : -Real.pi/4+2*Real.pi = 7*Real.pi/4:=by ring
  rw [es1,es2] at hshift
  dsimp only [F] at hshift
  linarith
end Brennan
end
noncomputable section
namespace Brennan
lemma kz771 {a δ:ℝ} (ha:0 ≤ a) (hδ:0 < δ) {n:ℕ}
    (hn:δ ≤ 2*(1/2:ℝ)^n) :
    ((2:ℝ)^a)^n ≤ (2:ℝ)^a * δ^(-a):=by
  have hv:0 < (1/2:ℝ)^n:=by positivity
  have he:((2:ℝ)^a)^n = ((1/2:ℝ)^n)^(-a):=by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),← Real.rpow_natCast (1/2:ℝ),
      ← Real.rpow_mul (by norm_num)]
    rw [show (1/2:ℝ) = 2^(-1:ℝ) by norm_num,← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [he]
  have hb:=Real.rpow_le_rpow_of_nonpos (by positivity:0 < δ/2)
    (show δ/2 ≤ (1/2:ℝ)^n by linarith) (neg_nonpos.mpr ha)
  refine hb.trans_eq ?_
  rw [Real.div_rpow hδ.le (by norm_num),Real.rpow_neg (by norm_num:(0:ℝ) ≤ 2),div_inv_eq_mul,mul_comm]
lemma kz772 (ε:ℝ) (hε:0 < ε) :
    ∃ C:ℝ,0 < C ∧ ∀ f:ℂ → ℂ,kz2 f → ∀ r:ℝ,1/2 ≤ r → r < 1 →
      kz3 f (-2) r ≤ C*(1-r)^(-1-ε):=by
  have hlam:2 < (2:ℝ)^(1+ε):=by
    calc
      (2:ℝ) = 2^(1:ℝ):=by rw [Real.rpow_one]
      _ < 2^(1+ε):=Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  obtain ⟨K,hK,hKn⟩:=kz757 hlam
  let A:=(2*Real.pi)⁻¹*(1600000000*‖kz751 1 zero_lt_one‖)*K*(2:ℝ)^(1+ε)
  have hA:0 ≤ A:=by dsimp [A]; positivity
  refine ⟨A+1,by linarith,fun f hf r hr hr1 => ?_⟩
  obtain ⟨n,hn1,hn2⟩:=exists_nat_pow_near_of_lt_one (by linarith:0 < 1-r)
    (by linarith:1-r ≤ 1) (by norm_num:(0:ℝ) < 1/2) (by norm_num:(1/2:ℝ) < 1)
  have hn:1-r ≤ 2*(1/2:ℝ)^(n+1):=by rw [pow_succ]; nlinarith
  have hb:=kz770 hf hr hr1 (n+1) hn1.le hn
  have hc:=kz771 (by linarith:0 ≤ 1+ε) (by linarith:0 < 1-r) hn
  have hx:0 ≤ (2*Real.pi)⁻¹:=by positivity
  have hy:0 ≤ 1600000000*‖kz751 1 zero_lt_one‖:=by positivity
  have he:(-1-ε:ℝ) = -(1+ε):=by ring
  change (2*Real.pi)⁻¹*(∫ θ in -Real.pi..Real.pi,‖deriv f (kz728 r θ)‖^(-2:ℝ)) ≤ _
  calc
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖kz751 1 zero_lt_one‖)*‖kz581^(n+1)‖) :=
      mul_le_mul_of_nonneg_left hb hx
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖kz751 1 zero_lt_one‖)*(K*((2:ℝ)^(1+ε))^(n+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hKn (n+1)) hy) hx
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖kz751 1 zero_lt_one‖)*(K*((2:ℝ)^(1+ε)*(1-r)^(-(1+ε))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hK.le) hy) hx
    _ = A*(1-r)^(-1-ε):=by rw [he]; dsimp [A]; ring
    _ ≤ (A+1)*(1-r)^(-1-ε):=mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
noncomputable section
namespace Brennan
end Brennan
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Brennan
end Brennan
end
end OAI
end
namespace KBridgeBr
open BrennanConjecture Complex Filter MeasureTheory Set Topology

lemma kz773:unitDisk = Metric.ball (0:ℂ) 1:=by
  ext z; simp [unitDisk,Metric.mem_ball,dist_zero_right]

lemma kz774 {f:ℂ → ℂ} (hf:IsUnivalentNormalized f):OAI.Brennan.kz2 f:=by
  refine ⟨⟨?_,?_⟩,hf.map_zero,hf.deriv_zero⟩
  · have:=hf.analyticOn.differentiableOn
    rw [kz773] at this
    exact this
  · have:=hf.injOn
    rw [kz773] at this
    exact this

/-- The FC integral equals `2π` times the integral mean. -/
lemma kz775 (f:ℂ → ℂ) (r:ℝ) :
    (∫ θ in Ioc (-Real.pi) Real.pi,‖deriv f (r • exp (Complex.I * θ))‖ ^ (-2:ℝ))
      = 2 * Real.pi * OAI.Brennan.kz3 f (-2) r:=by
  unfold OAI.Brennan.kz3
  rw [← mul_assoc,mul_inv_cancel₀ (by positivity),one_mul,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  congr 1
  ext θ
  rw [Complex.real_smul,mul_comm Complex.I]

lemma kz776:Tendsto (fun r:ℝ => -Real.log (1 - r)) (𝓝[<] (1:ℝ)) atTop:=by
  have hsub:Tendsto (fun r:ℝ => 1 - r) (𝓝[<] (1:ℝ)) (𝓝[>] 0):=by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (eventually_nhdsWithin_of_forall fun r hr => mem_Ioi.mpr (sub_pos.mpr hr))
    simpa using ((continuous_sub_left (1:ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds
  exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hsub)

lemma kz777:∀ᶠ r in 𝓝[<] (1:ℝ),1/2 ≤ r ∧ r < 1:=by
  have:Ioo (1/2:ℝ) 1 ∈ 𝓝[<] (1:ℝ):=Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [this] with r hr
  exact ⟨hr.1.le,hr.2⟩

/-- The eventual upper bound `1 + 2ε`. -/
lemma kz778 {f:ℂ → ℂ} (hf:IsUnivalentNormalized f) (ε:ℝ) (hε:0 < ε) :
    ∀ᶠ r in 𝓝[<] (1:ℝ),
      Real.log (∫ θ in Ioc (-Real.pi) Real.pi,‖deriv f (r • exp (Complex.I * θ))‖ ^ (-2:ℝ)) /
        |Real.log (1 - r)| ≤ 1 + 2 * ε:=by
  obtain ⟨C,hC,hbound⟩:=OAI.Brennan.kz772 ε hε
  have hsch:=kz774 hf
  have hL:=kz776
  have hbig:∀ᶠ r in 𝓝[<] (1:ℝ),|Real.log (2 * Real.pi * C)| / ε + 1 ≤ -Real.log (1 - r) :=
    hL.eventually (eventually_ge_atTop _)
  filter_upwards [kz777,hbig] with r ⟨hr1,hr2⟩ hb
  have hd:0 < 1 - r:=by linarith
  have hlog:Real.log (1 - r) < 0:=Real.log_neg hd (by linarith)
  set L:=-Real.log (1 - r) with hLdef
  have hLpos:0 < L:=by linarith
  have habs:|Real.log (1 - r)| = L:=by rw [abs_of_neg hlog]
  have hY0:0 ≤ ∫ θ in Ioc (-Real.pi) Real.pi,‖deriv f (r • exp (Complex.I * θ))‖ ^ (-2:ℝ) :=
    integral_nonneg fun θ => Real.rpow_nonneg (norm_nonneg _) _
  rw [habs]
  rw [kz775] at hY0 ⊢
  set X:=2 * Real.pi * OAI.Brennan.kz3 f (-2) r with hX
  have hXle:X ≤ 2 * Real.pi * C * (1 - r) ^ (-1 - ε):=by
    have hb1:=hbound f hsch r hr1 hr2
    have h2:0 ≤ 2 * Real.pi:=by positivity
    calc X = 2 * Real.pi * OAI.Brennan.kz3 f (-2) r:=hX
      _ ≤ 2 * Real.pi * (C * (1 - r) ^ (-1 - ε)):=mul_le_mul_of_nonneg_left hb1 h2
      _ = 2 * Real.pi * C * (1 - r) ^ (-1 - ε):=by ring
  have hεL:|Real.log (2 * Real.pi * C)| ≤ ε * L:=by
    have:=(div_le_iff₀ hε).mp (by linarith:|Real.log (2 * Real.pi * C)| / ε ≤ L)
    linarith
  rw [div_le_iff₀ hLpos]
  by_cases hX0:X ≤ 0
  · have hX00:X = 0:=le_antisymm hX0 hY0
    rw [hX00,Real.log_zero]
    nlinarith
  · push Not at hX0
    have h1:Real.log X ≤ Real.log (2 * Real.pi * C * (1 - r) ^ (-1 - ε)) :=
      Real.log_le_log hX0 hXle
    have hCpos:0 < 2 * Real.pi * C:=mul_pos (by positivity) hC
    rw [Real.log_mul (x:=2 * Real.pi * C) hCpos.ne' (Real.rpow_pos_of_pos hd _).ne',
      Real.log_rpow hd] at h1
    have e3:(-1 - ε) * Real.log (1 - r) = (1 + ε) * L:=by rw [hLdef]; ring
    rw [e3] at h1
    have h2:Real.log (2 * Real.pi * C) ≤ ε * L:=le_trans (le_abs_self _) hεL
    nlinarith

lemma kz779 {f:ℂ → ℂ} (hf:IsUnivalentNormalized f) :
    integralMeansSpectrum f (-2) ≤ 1:=by
  unfold integralMeansSpectrum
  rw [Filter.limsup_eq]
  set S:={a:ℝ | ∀ᶠ r in 𝓝[Iio 1] (1:ℝ),
    Real.log (∫ θ in Ioc (-Real.pi) Real.pi,‖deriv f (r • exp (Complex.I * θ))‖ ^ (-2:ℝ)) /
        |Real.log (1 - r)| ≤ a} with hS
  by_cases hb:BddBelow S
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hmem:1 + 2 * (ε / 4) ∈ S:=kz778 hf (ε / 4) (by positivity)
    have:=csInf_le hb hmem
    linarith
  · rw [Real.sInf_of_not_bddBelow hb]
    norm_num

/-- The explicit bounded univalent function `z - z^2/2`. -/
noncomputable def p (z:ℂ):ℂ:=z - z ^ 2 / 2

lemma kz780 (w:ℂ):HasDerivAt p (1 - w) w:=by
  have h1:HasDerivAt (fun z:ℂ => z ^ 2 / 2) w w:=by
    exact ((hasDerivAt_pow 2 w).div_const 2).congr_deriv (by norm_num)
  exact (hasDerivAt_id' w).sub h1

lemma kz781 (w:ℂ):deriv p w = 1 - w:=(kz780 w).deriv

lemma kz782:IsUnivalentNormalized p:=by
  refine ⟨?_,?_,?_,?_⟩
  · intro z _
    have:AnalyticAt ℂ p z:=by
      unfold p
      fun_prop
    exact this.analyticWithinAt
  · intro a ha b hb hab
    simp only [unitDisk,mem_ofPred_eq] at ha hb
    unfold p at hab
    by_contra hne
    have h1:(a - b) * (2 - (a + b)) = 0:=by linear_combination 2 * hab
    rcases mul_eq_zero.mp h1 with h | h
    · exact hne (sub_eq_zero.mp h)
    · have h2:a + b = 2:=by linear_combination -h
      have:‖a + b‖ < 2:=lt_of_le_of_lt (norm_add_le a b) (by linarith)
      rw [h2] at this
      norm_num at this
  · simp [p]
  · rw [kz781]; simp

lemma kz783:Bornology.IsBounded (p '' unitDisk):=by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2,?_⟩
  rintro _ ⟨z,hz,rfl⟩
  simp only [unitDisk,mem_ofPred_eq] at hz
  unfold p
  calc ‖z - z ^ 2 / 2‖ ≤ ‖z‖ + ‖z ^ 2 / 2‖:=norm_sub_le _ _
    _ = ‖z‖ + ‖z‖ ^ 2 / 2:=by rw [norm_div,norm_pow]; norm_num
    _ ≤ 2:=by nlinarith [norm_nonneg z]

lemma kz784 (r θ:ℝ) (hr:r < 1) (hr0:0 ≤ r) :
    1 - r ≤ ‖1 - (r • exp (Complex.I * θ))‖:=by
  have h1:‖(r • exp (Complex.I * θ))‖ = r:=by
    rw [norm_smul,Complex.norm_exp_I_mul_ofReal,mul_one,Real.norm_eq_abs,abs_of_nonneg hr0]
  have:=norm_sub_norm_le (1:ℂ) (r • exp (Complex.I * θ))
  rw [h1,norm_one] at this
  exact this

lemma kz785 (r θ:ℝ) (hr0:0 ≤ r) (hr:r ≤ 1) :
    ‖1 - (r • exp (Complex.I * θ))‖ ≤ (1 - r) + |θ|:=by
  have e:(1:ℂ) - r • exp (Complex.I * θ) = (1 - r) + r • (1 - exp (Complex.I * θ)):=by
    rw [Complex.real_smul,Complex.real_smul]; push_cast; ring
  rw [e]
  calc ‖((1:ℂ) - r) + r • (1 - exp (Complex.I * θ))‖
      ≤ ‖((1:ℂ) - r)‖ + ‖r • (1 - exp (Complex.I * θ))‖:=norm_add_le _ _
    _ ≤ (1 - r) + |θ|:=by
      gcongr
      · have:((1:ℂ) - r) = ((1 - r:ℝ):ℂ):=by push_cast; ring
        rw [this,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]
        have hb:‖1 - exp (Complex.I * θ)‖ ≤ |θ|:=by
          have:=Real.norm_exp_I_mul_ofReal_sub_one_le (x:=θ)
          rw [norm_sub_rev]
          simpa [Real.norm_eq_abs] using this
        calc r * ‖1 - exp (Complex.I * θ)‖ ≤ 1 * ‖1 - exp (Complex.I * θ)‖:=by
              gcongr
          _ ≤ |θ|:=by rw [one_mul]; exact hb

lemma kz786 (r:ℝ) (hr1:1/2 ≤ r) (hr2:r < 1) :
    1 / (2 * (1 - r)) ≤
      ∫ θ in Ioc (-Real.pi) Real.pi,‖deriv p (r • exp (Complex.I * θ))‖ ^ (-2:ℝ):=by
  set δ:=1 - r with hδ
  have hd:0 < δ:=by linarith
  have hdpi:δ ≤ Real.pi:=by linarith [Real.pi_gt_three]
  set F:ℝ → ℝ:=fun θ => ‖deriv p (r • exp (Complex.I * θ))‖ ^ (-2:ℝ) with hF
  have hpos:∀ θ:ℝ,0 < ‖deriv p (r • exp (Complex.I * θ))‖:=by
    intro θ
    rw [kz781]
    exact lt_of_lt_of_le hd (kz784 r θ hr2 (by linarith))
  have hcont:Continuous F:=by
    have h1:Continuous fun θ:ℝ => ‖deriv p (r • exp (Complex.I * θ))‖:=by
      simp_rw [kz781]
      fun_prop
    exact h1.rpow_const (fun θ => Or.inl (hpos θ).ne')
  have hFnn:∀ θ,0 ≤ F θ:=fun θ => Real.rpow_nonneg (norm_nonneg _) _
  have hint:IntegrableOn F (Ioc (-Real.pi) Real.pi) :=
    (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hsub:Icc (-δ) δ ⊆ Ioc (-Real.pi) Real.pi:=by
    intro x hx
    exact ⟨by linarith [hx.1,Real.pi_gt_three],le_trans hx.2 hdpi⟩
  have hmono : ∫ θ in Icc (-δ) δ,F θ ≤ ∫ θ in Ioc (-Real.pi) Real.pi,F θ :=
    setIntegral_mono_set hint (Eventually.of_forall fun θ => hFnn θ) hsub.eventuallyLE
  have hlow:∀ θ ∈ Icc (-δ) δ,(2 * δ) ^ (-2:ℝ) ≤ F θ:=by
    intro θ hθ
    have hθ':|θ| ≤ δ:=abs_le.mpr ⟨hθ.1,hθ.2⟩
    have hu:‖deriv p (r • exp (Complex.I * θ))‖ ≤ 2 * δ:=by
      rw [kz781]
      have:=kz785 r θ (by linarith) hr2.le
      linarith
    exact Real.rpow_le_rpow_of_nonpos (hpos θ) hu (by norm_num)
  have hconst : ∫ θ in Icc (-δ) δ,(2 * δ) ^ (-2:ℝ) ≤ ∫ θ in Icc (-δ) δ,F θ :=
    setIntegral_mono_on (integrableOn_const (by simp)) (hcont.integrableOn_Icc) measurableSet_Icc hlow
  have hval : ∫ θ in Icc (-δ) δ,(2 * δ) ^ (-2:ℝ) = 1 / (2 * δ):=by
    rw [setIntegral_const,Measure.real,Real.volume_Icc,ENNReal.toReal_ofReal (by linarith),
      smul_eq_mul,Real.rpow_neg (by positivity),Real.rpow_two]
    field_simp
    ring
  linarith

lemma kz787 (ε:ℝ) (hε:0 < ε) :
    ∀ᶠ r in 𝓝[<] (1:ℝ),1 - ε ≤
      Real.log (∫ θ in Ioc (-Real.pi) Real.pi,‖deriv p (r • exp (Complex.I * θ))‖ ^ (-2:ℝ)) /
        |Real.log (1 - r)|:=by
  have hbig:∀ᶠ r in 𝓝[<] (1:ℝ),Real.log 2 / ε + 1 ≤ -Real.log (1 - r) :=
    kz776.eventually (eventually_ge_atTop _)
  filter_upwards [kz777,hbig] with r ⟨hr1,hr2⟩ hb
  have hd:0 < 1 - r:=by linarith
  have hlog:Real.log (1 - r) < 0:=Real.log_neg hd (by linarith)
  have habs:|Real.log (1 - r)| = -Real.log (1 - r):=abs_of_neg hlog
  have hLpos:0 < -Real.log (1 - r):=by linarith
  rw [habs,le_div_iff₀ hLpos]
  have hI:=kz786 r hr1 hr2
  have h1:Real.log (1 / (2 * (1 - r))) ≤
      Real.log (∫ θ in Ioc (-Real.pi) Real.pi,‖deriv p (r • exp (Complex.I * θ))‖ ^ (-2:ℝ)) :=
    Real.log_le_log (by positivity) hI
  rw [one_div,Real.log_inv,Real.log_mul (by norm_num) hd.ne'] at h1
  have hε2:Real.log 2 ≤ ε * (-Real.log (1 - r)):=by
    have:=(div_le_iff₀ hε).mp (by linarith:Real.log 2 / ε ≤ -Real.log (1 - r))
    linarith
  nlinarith

lemma kz788:integralMeansSpectrum p (-2) = 1:=by
  refine le_antisymm (kz779 kz782) ?_
  have hbdd:IsBoundedUnder (· ≤ ·) (𝓝[Iio 1] (1:ℝ)) (fun r =>
      Real.log (∫ θ in Ioc (-Real.pi) Real.pi,‖deriv p (r • exp (Complex.I * θ))‖ ^ (-2:ℝ)) /
        |Real.log (1 - r)|) :=
    ⟨1 + 2 * 1,kz778 kz782 1 one_pos⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have h:=le_limsup_of_frequently_le (kz787 (ε / 2) (by positivity)).frequently hbdd
  unfold integralMeansSpectrum
  linarith

theorem bridge:universalSpectrumBounded (-2) = 1:=by
  unfold universalSpectrumBounded
  apply IsGreatest.csSup_eq
  refine ⟨⟨p,kz782,kz783,kz788.symm⟩,?_⟩
  rintro β ⟨f,hf,_,rfl⟩
  exact kz779 hf

end KBridgeBr

theorem OMA.solution:type_of% @BrennanConjecture.brennan_universalSpectrumBounded :=
  KBridgeBr.bridge

