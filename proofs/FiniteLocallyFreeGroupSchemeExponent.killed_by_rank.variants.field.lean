import FormalConjectures.Paper.FiniteLocallyFreeGroupSchemeExponent

/-!
# SGA 3 Exp. VIIA, Prop. 8.5: Finite group schemes over a field are killed by their rank
-/

namespace FiniteLocallyFreeGroupSchemeExponent

open WithConv Coalgebra Bialgebra HopfAlgebra TensorProduct

section FieldProof

private lemma ideal_pow_mono {R : Type*} [CommSemiring R] {I J : Ideal R} (hIJ : I ≤ J) :
    ∀ t : ℕ, I ^ t ≤ J ^ t
  | 0 => by simp
  | t + 1 => by rw [pow_succ, pow_succ]; exact Ideal.mul_mono (ideal_pow_mono hIJ t) hIJ

private lemma ideal_sup_pow_le {R : Type*} [CommSemiring R] (I J : Ideal R) :
    ∀ n a b : ℕ, a + b ≤ n + 1 → (I ⊔ J) ^ n ≤ I ^ a ⊔ J ^ b := by
  intro n
  induction n with
  | zero =>
    intro a b hab
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · have hb : b = 0 := by omega
      subst hb; simp
  | succ n ih =>
    intro a b hab
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    rcases eq_or_ne b 0 with rfl | hb
    · simp
    rw [pow_succ', Ideal.sup_mul]
    refine sup_le ?_ ?_
    · have h1 := ih (a - 1) b (by omega)
      refine (Ideal.mul_mono_right h1).trans ?_
      rw [Ideal.mul_sup]
      refine sup_le ?_ (le_sup_of_le_right Ideal.mul_le_right)
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero ha)]
      exact le_sup_left
    · have h2 := ih a (b - 1) (by omega)
      refine (Ideal.mul_mono_right h2).trans ?_
      rw [Ideal.mul_sup]
      refine sup_le (le_sup_of_le_left Ideal.mul_le_right) ?_
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hb)]
      exact le_sup_right

private lemma exists_le_ker_of_not_mem {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (p : Submodule k M) (x : M) (hx : x ∉ p) :
    ∃ f : M →ₗ[k] k, (∀ y ∈ p, f y = 0) ∧ f x ≠ 0 := by
  have hq : p.mkQ x ≠ 0 := by
    intro h
    exact hx ((Submodule.Quotient.mk_eq_zero p).mp h)
  let b := Module.Basis.ofVectorSpace k (M ⧸ p)
  have hrepr : b.repr (p.mkQ x) ≠ 0 := by
    intro h
    exact hq (b.repr.injective (h.trans (map_zero b.repr).symm))
  have hex : ∃ i, b.repr (p.mkQ x) i ≠ 0 := by
    by_contra h
    push Not at h
    exact hrepr (Finsupp.ext h)
  rcases hex with ⟨i, hi⟩
  refine ⟨(b.coord i).comp p.mkQ, ?_, hi⟩
  intro y hy
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [(Submodule.Quotient.mk_eq_zero p).mpr hy, map_zero]

private lemma tensorMap_injective {k M₁ M₂ N₁ N₂ : Type*} [Field k]
    [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
    [AddCommGroup N₁] [Module k N₁] [AddCommGroup N₂] [Module k N₂]
    {f : M₁ →ₗ[k] N₁} {g : M₂ →ₗ[k] N₂}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  obtain ⟨f', hf'⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  obtain ⟨g', hg'⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
  have hcomp : (TensorProduct.map f' g').comp (TensorProduct.map f g) = LinearMap.id := by
    rw [← TensorProduct.map_comp, hf', hg', TensorProduct.map_id]
  exact Function.LeftInverse.injective (fun z => by
    have := LinearMap.congr_fun hcomp z
    simpa using this)

private lemma sum_smul_counit {R A ι : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
    [Coalgebra R A] {a : A} (r : Coalgebra.Repr R a ι) :
    ∑ i ∈ r.index, Coalgebra.counit (R := R) (r.right i) • r.left i = a := by
  have h := congrArg (TensorProduct.rid R A) (Coalgebra.sum_tmul_counit_eq (R := R) r)
  simpa only [map_sum, TensorProduct.rid_tmul, one_smul] using h

private lemma convPow_includeRight {k K A : Type*} [CommRing k] [CommRing K] [Algebra k K]
    [CommRing A] [HopfAlgebra k A] (m : ℕ) (a : A) :
    (toConv (AlgHom.id K (K ⊗[k] A)) ^ m).ofConv (1 ⊗ₜ[k] a) =
      1 ⊗ₜ[k] ((toConv (AlgHom.id k A) ^ m).ofConv a) := by
  induction m generalizing a with
  | zero =>
    simp [AlgHom.convOne_def, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  | succ m ih =>
    rw [pow_succ, AlgHom.convMul_apply, pow_succ, AlgHom.convMul_apply]
    have hcomul : Coalgebra.comul (R := K) ((1 : K) ⊗ₜ[k] a) =
        ∑ i ∈ (ℛ k a).index, ((1 : K) ⊗ₜ[k] (ℛ k a).left i) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] (ℛ k a).right i) := by
      change AlgebraTensorModule.tensorTensorTensorComm k K k K K K A A
        ((Coalgebra.comul (R := K) (1 : K)) ⊗ₜ[k] (Coalgebra.comul (R := k) a)) = _
      rw [← (ℛ k a).eq]
      change AlgebraTensorModule.tensorTensorTensorComm k K k K K K A A
        (((1 : K) ⊗ₜ[K] (1 : K)) ⊗ₜ[k] ∑ i ∈ (ℛ k a).index, (ℛ k a).left i ⊗ₜ[k] (ℛ k a).right i) = _
      simp [map_sum, TensorProduct.tmul_sum]
    rw [hcomul, map_sum]
    rw [← (ℛ k a).eq, map_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ih, Algebra.TensorProduct.tmul_mul_tmul]

private lemma isKilledBy_of_baseChange {k K A : Type*} [Field k] [Field K] [Algebra k K]
    [CommRing A] [HopfAlgebra k A] {m : ℕ} (h : IsKilledBy K (K ⊗[k] A) m) :
    IsKilledBy k A m := by
  refine WithConv.ext (AlgHom.ext fun a => ?_)
  have h1 := DFunLike.congr_fun (congrArg WithConv.ofConv h) (1 ⊗ₜ[k] a)
  rw [convPow_includeRight] at h1
  have h2 : (1 : WithConv ((K ⊗[k] A) →ₐ[K] (K ⊗[k] A))).ofConv (1 ⊗ₜ[k] a) =
      1 ⊗ₜ[k] ((1 : WithConv (A →ₐ[k] A)).ofConv a) := by
    simp [AlgHom.convOne_def, Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def]
  rw [h2] at h1
  have hinj : Function.Injective (fun x : A => (1 : K) ⊗ₜ[k] x) := by
    intro x y hxy
    obtain ⟨f, _, hf1⟩ := exists_le_ker_of_not_mem (⊥ : Submodule k K) (1 : K)
      (by simp [one_ne_zero])
    have hfx := congrArg ((TensorProduct.lid k A).toLinearMap ∘ₗ LinearMap.rTensor A f) hxy
    simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at hfx
    exact smul_right_injective A hf1 hfx
  exact hinj h1

private noncomputable def leftTrans {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (g : WithConv (A →ₐ[k] k)) : A →ₐ[k] A :=
  (Algebra.TensorProduct.lift (AlgHom.id k A) ((Algebra.ofId k A).comp g.ofConv)
    (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom k A)

private lemma leftTrans_apply {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (g : WithConv (A →ₐ[k] k)) (a : A) :
    leftTrans g a = ∑ i ∈ (ℛ k a).index, (ℛ k a).left i * algebraMap k A (g.ofConv ((ℛ k a).right i)) := by
  dsimp [leftTrans]
  rw [Bialgebra.comulAlgHom_apply, ← (ℛ k a).eq, map_sum]
  simp

private lemma leftTrans_one {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A] :
    leftTrans (1 : WithConv (A →ₐ[k] k)) = AlgHom.id k A := by
  ext a
  rw [leftTrans_apply]
  have h : ∑ i ∈ (ℛ k a).index, (ℛ k a).left i *
      algebraMap k A ((1 : WithConv (A →ₐ[k] k)).ofConv ((ℛ k a).right i)) =
      ∑ i ∈ (ℛ k a).index, Coalgebra.counit (R := k) ((ℛ k a).right i) • (ℛ k a).left i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    change (ℛ k a).left i * algebraMap k A (Coalgebra.counit (R := k) ((ℛ k a).right i)) = _
    rw [Algebra.smul_def, mul_comm]
  rw [h]
  exact sum_smul_counit (ℛ k a)

private lemma leftTrans_mul {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (g₁ g₂ : WithConv (A →ₐ[k] k)) :
    leftTrans (g₁ * g₂) = (leftTrans g₁).comp (leftTrans g₂) := by
  ext a
  have hlin : ∀ (g : WithConv (A →ₐ[k] k)),
      (leftTrans g).toLinearMap =
        (TensorProduct.rid k A).toLinearMap ∘ₗ (LinearMap.lTensor A g.ofConv.toLinearMap) ∘ₗ
          Coalgebra.comul (R := k) := by
    intro g
    ext x
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, leftTrans_apply]
    rw [← (ℛ k x).eq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.smul_def, mul_comm]
  change (leftTrans (g₁ * g₂)).toLinearMap a =
    ((leftTrans g₁).toLinearMap ∘ₗ (leftTrans g₂).toLinearMap) a
  congr 1
  rw [hlin (g₁ * g₂), hlin g₁, hlin g₂]
  have hco := Coalgebra.coassoc (R := k) (A := A)
  have hcomm : (Coalgebra.comul (R := k) (A := A)) ∘ₗ
      ((TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A g₂.ofConv.toLinearMap) =
      (TensorProduct.rid k (A ⊗[k] A)).toLinearMap ∘ₗ
        LinearMap.lTensor (A ⊗[k] A) g₂.ofConv.toLinearMap ∘ₗ
        LinearMap.rTensor A (Coalgebra.comul (R := k) (A := A)) := by
    apply TensorProduct.ext'
    intro x y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.rid_tmul,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_smul]
  calc (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A (g₁ * g₂).ofConv.toLinearMap ∘ₗ
        Coalgebra.comul (R := k)
      = (TensorProduct.rid k A).toLinearMap ∘ₗ
          LinearMap.lTensor A (LinearMap.mul' k k ∘ₗ
            TensorProduct.map g₁.ofConv.toLinearMap g₂.ofConv.toLinearMap ∘ₗ
            Coalgebra.comul (R := k)) ∘ₗ
          Coalgebra.comul (R := k) := by rfl
    _ = (TensorProduct.rid k A).toLinearMap ∘ₗ
          LinearMap.lTensor A (LinearMap.mul' k k) ∘ₗ
          LinearMap.lTensor A (TensorProduct.map g₁.ofConv.toLinearMap g₂.ofConv.toLinearMap) ∘ₗ
          LinearMap.lTensor A (Coalgebra.comul (R := k)) ∘ₗ
          Coalgebra.comul (R := k) := by
        simp [LinearMap.lTensor_comp, LinearMap.comp_assoc]
    _ = (TensorProduct.rid k A).toLinearMap ∘ₗ
          LinearMap.lTensor A (LinearMap.mul' k k) ∘ₗ
          LinearMap.lTensor A (TensorProduct.map g₁.ofConv.toLinearMap g₂.ofConv.toLinearMap) ∘ₗ
          (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
          LinearMap.rTensor A (Coalgebra.comul (R := k)) ∘ₗ
          Coalgebra.comul (R := k) := by
        congr 1; congr 1; congr 1
        exact hco.symm
    _ = ((TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A g₁.ofConv.toLinearMap) ∘ₗ
          ((TensorProduct.rid k (A ⊗[k] A)).toLinearMap ∘ₗ
            LinearMap.lTensor (A ⊗[k] A) g₂.ofConv.toLinearMap) ∘ₗ
          LinearMap.rTensor A (Coalgebra.comul (R := k)) ∘ₗ
          Coalgebra.comul (R := k) := by
        simp only [← LinearMap.comp_assoc]
        congr 1; congr 1
        apply TensorProduct.ext'
        intro xy z
        induction xy using TensorProduct.induction_on with
        | zero => simp
        | tmul x y =>
          simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
            LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.mul'_apply,
            TensorProduct.rid_tmul, AlgHom.toLinearMap_apply, map_smul]
          rw [mul_smul, smul_comm]
        | add u v ihu ihv => simp [TensorProduct.add_tmul, map_add, ihu, ihv]
    _ = ((TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A g₁.ofConv.toLinearMap) ∘ₗ
          (Coalgebra.comul (R := k) ∘ₗ
            ((TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A g₂.ofConv.toLinearMap)) ∘ₗ
          Coalgebra.comul (R := k) := by
        congr 1
        ext x
        simp only [LinearMap.comp_apply]
        exact LinearMap.congr_fun hcomm.symm (Coalgebra.comul (R := k) x)
    _ = ((TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A g₁.ofConv.toLinearMap ∘ₗ
          Coalgebra.comul (R := k)) ∘ₗ
          ((TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A g₂.ofConv.toLinearMap ∘ₗ
            Coalgebra.comul (R := k)) := by
        simp [LinearMap.comp_assoc]

private noncomputable def leftTransEquiv {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (g : WithConv (A →ₐ[k] k)) : A ≃ₐ[k] A :=
  AlgEquiv.ofAlgHom (leftTrans g) (leftTrans g⁻¹)
    (by rw [← leftTrans_mul, mul_inv_cancel, leftTrans_one])
    (by rw [← leftTrans_mul, inv_mul_cancel, leftTrans_one])

private lemma counit_comp_leftTrans {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (g : WithConv (A →ₐ[k] k)) :
    (Bialgebra.counitAlgHom k A).comp (leftTrans g) = g.ofConv := by
  ext a
  simp only [AlgHom.comp_apply, leftTrans_apply, map_sum, map_mul, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply]
  have h : ∑ i ∈ (ℛ k a).index,
      (Bialgebra.counitAlgHom k A) ((ℛ k a).left i) * g.ofConv ((ℛ k a).right i) =
      g.ofConv (∑ i ∈ (ℛ k a).index,
        Coalgebra.counit (R := k) ((ℛ k a).left i) • (ℛ k a).right i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.smul_def]
  rw [h, Coalgebra.sum_counit_smul (ℛ k a)]

private lemma comp_convPow {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (g : WithConv (A →ₐ[k] k)) (t : ℕ) :
    g.ofConv.comp ((toConv (AlgHom.id k A) ^ t).ofConv) = (g ^ t).ofConv := by
  induction t with
  | zero =>
    ext a
    simp [AlgHom.convOne_def]
  | succ t ih =>
    rw [pow_succ, pow_succ, AlgHom.comp_convMul_distrib]
    congr 1
    rw [ih]
    rfl

-- Every maximal ideal of a finite-dimensional algebra over an algebraically closed field
-- is the kernel of a unique k-algebra hom A →ₐ[k] k.
private lemma algHom_of_maximal {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A]
    [Algebra k A] [Module.Finite k A] (M : MaximalSpectrum A) :
    ∃! g : A →ₐ[k] k, RingHom.ker g = M.asIdeal := by
  have : M.asIdeal.IsMaximal := M.isMaximal
  let : Field (A ⧸ M.asIdeal) := Ideal.Quotient.field M.asIdeal
  have : Module.Finite k (A ⧸ M.asIdeal) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ k M.asIdeal).toLinearMap Ideal.Quotient.mk_surjective
  have hbij : Function.Bijective (algebraMap k (A ⧸ M.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] (A ⧸ M.asIdeal) := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ M.asIdeal)) hbij
  let g : A →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k M.asIdeal)
  refine ⟨g, ?_, ?_⟩
  · ext x
    simp only [RingHom.mem_ker, g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Ideal.Quotient.mkₐ_eq_mk]
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  · intro g' hg'
    ext x
    have hmem : x - algebraMap k A (g' x) ∈ M.asIdeal := by
      rw [← hg', RingHom.mem_ker]
      simp
    have hgx : g (x - algebraMap k A (g' x)) = 0 := by
      have : RingHom.ker g = M.asIdeal := by
        ext y
        simp only [RingHom.mem_ker, g, AlgHom.comp_apply,
          AlgEquiv.coe_toAlgHom, Ideal.Quotient.mkₐ_eq_mk]
        rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
      rw [← this] at hmem
      exact hmem
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at hgx
    exact hgx.symm

-- Local finite-dimensional commutative Hopf algebra over an algebraically closed field:
-- In characteristic 0, dim_k A = 1.
-- In characteristic p > 0, dim_k A = p^r for some r.

private lemma point_deriv_exists {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (ε : A →ₐ[k] k) (x : A) (hx : x ∈ RingHom.ker ε) (hx2 : x ∉ (RingHom.ker ε) ^ 2) :
    ∃ D : A →ₗ[k] k, D 1 = 0 ∧ (∀ y ∈ (RingHom.ker ε) ^ 2, D y = 0) ∧ D x = 1 := by
  let S : Submodule k A := Submodule.span k {(1 : A)} ⊔ ((RingHom.ker ε) ^ 2).restrictScalars k
  have hxS : x ∉ S := by
    intro hmem
    rw [Submodule.mem_sup] at hmem
    rcases hmem with ⟨u, hu, v, hv, huv⟩
    rw [Submodule.mem_span_singleton] at hu
    rcases hu with ⟨c, rfl⟩
    have hε : ε (c • (1 : A) + v) = ε x := congrArg ε huv
    have hvε : ε v = 0 := by
      have hle : (RingHom.ker ε) ^ 2 ≤ RingHom.ker ε := Ideal.pow_le_self (by decide)
      exact hle hv
    rw [map_add, map_smul, map_one, smul_eq_mul, mul_one, hvε, add_zero] at hε
    have hx0 : ε x = 0 := hx
    rw [hx0] at hε
    rw [hε, zero_smul, zero_add] at huv
    rw [huv] at hv
    exact hx2 hv
  obtain ⟨D, hDS, hDx⟩ := exists_le_ker_of_not_mem S x hxS
  refine ⟨(D x)⁻¹ • D, ?_, ?_, ?_⟩
  · simp [LinearMap.smul_apply, hDS _ (Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton 1)))]
  · intro y hy
    simp [LinearMap.smul_apply, hDS _ (Submodule.mem_sup_right hy)]
  · simp [LinearMap.smul_apply, inv_mul_cancel₀ hDx]

private lemma point_deriv_mul {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (ε : A →ₐ[k] k) (D : A →ₗ[k] k) (hD1 : D 1 = 0) (hD2 : ∀ y ∈ (RingHom.ker ε) ^ 2, D y = 0)
    (a b : A) :
    D (a * b) = ε a * D b + D a * ε b := by
  have ha : a - ε a • (1 : A) ∈ RingHom.ker ε := by
    simp [RingHom.mem_ker, Algebra.smul_def]
  have hb : b - ε b • (1 : A) ∈ RingHom.ker ε := by
    simp [RingHom.mem_ker, Algebra.smul_def]
  have hab : (a - ε a • (1 : A)) * (b - ε b • (1 : A)) ∈ (RingHom.ker ε) ^ 2 := by
    rw [sq]
    exact Ideal.mul_mem_mul ha hb
  have h0 := hD2 _ hab
  have hexp : (a - ε a • (1 : A)) * (b - ε b • (1 : A)) =
      a * b - ε a • b - ε b • a + (ε a * ε b) • (1 : A) := by
    simp only [Algebra.smul_def, mul_one, map_mul]
    ring
  rw [hexp, map_add, map_sub, map_sub, map_smul, map_smul, map_smul, hD1, smul_zero, add_zero] at h0
  simp only [smul_eq_mul] at h0
  linear_combination h0

private noncomputable def leftInvDeriv {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
    (D : A →ₗ[k] k) : A →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap ∘ₗ (LinearMap.lTensor A D) ∘ₗ Coalgebra.comul (R := k)

private lemma leftInvDeriv_apply {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
    (D : A →ₗ[k] k) (a : A) :
    leftInvDeriv D a = ∑ i ∈ (ℛ k a).index, D ((ℛ k a).right i) • (ℛ k a).left i := by
  dsimp [leftInvDeriv]
  rw [← (ℛ k a).eq, map_sum, map_sum]
  simp

private lemma leftInvDeriv_mul {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
    (D : A →ₗ[k] k) (hD1 : D 1 = 0)
    (hD2 : ∀ y ∈ (RingHom.ker (Bialgebra.counitAlgHom k A)) ^ 2, D y = 0)
    (a b : A) :
    leftInvDeriv D (a * b) = a * leftInvDeriv D b + leftInvDeriv D a * b := by
  let r := (ℛ k a).mul (ℛ k b)
  have hrepr : leftInvDeriv D (a * b) = ∑ i ∈ r.index, D (r.right i) • r.left i := by
    dsimp [leftInvDeriv]
    rw [← r.eq, map_sum, map_sum]
    simp
  rw [hrepr]
  simp only [r, Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left, Coalgebra.Repr.mul_right,
    Finset.sum_product]
  have hpt : ∀ i j,
      D ((ℛ k a).right i * (ℛ k b).right j) • ((ℛ k a).left i * (ℛ k b).left j) =
        (Coalgebra.counit (R := k) ((ℛ k a).right i) • (ℛ k a).left i) *
          (D ((ℛ k b).right j) • (ℛ k b).left j) +
        (D ((ℛ k a).right i) • (ℛ k a).left i) *
          (Coalgebra.counit (R := k) ((ℛ k b).right j) • (ℛ k b).left j) := by
    intro i j
    rw [point_deriv_mul (Bialgebra.counitAlgHom k A) D hD1 hD2]
    change (Coalgebra.counit (R := k) ((ℛ k a).right i) * D ((ℛ k b).right j) +
      D ((ℛ k a).right i) * Coalgebra.counit (R := k) ((ℛ k b).right j)) • _ = _
    rw [add_smul, smul_mul_smul_comm, smul_mul_smul_comm]
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    sum_smul_counit (ℛ k a), sum_smul_counit (ℛ k b)]
  rw [leftInvDeriv_apply, leftInvDeriv_apply]

private lemma leftInvDeriv_pow {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (δ : A →ₗ[k] A) (hδ : ∀ a b, δ (a * b) = a * δ b + δ a * b) (a : A) :
    ∀ r : ℕ, δ (a ^ r) = r • (a ^ (r - 1) * δ a)
  | 0 => by
    have h1 : δ 1 = 0 := by
      have h0 : δ 1 = δ 1 + δ 1 := by simpa using hδ 1 1
      linear_combination -h0
    simp [h1]
  | 1 => by simp
  | r + 2 => by
    rw [pow_succ, hδ, leftInvDeriv_pow δ hδ a (r + 1)]
    have hsub1 : r + 1 - 1 = r := Nat.add_sub_cancel r 1
    have hsub2 : r + 2 - 1 = r + 1 := Nat.add_sub_cancel (r + 1) 1
    rw [hsub1, hsub2, pow_succ]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

private lemma counit_leftInvDeriv {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
    (D : A →ₗ[k] k) (a : A) :
    Coalgebra.counit (R := k) (leftInvDeriv D a) = D a := by
  rw [leftInvDeriv_apply, map_sum]
  have h : ∑ i ∈ (ℛ k a).index, Coalgebra.counit (R := k) (D ((ℛ k a).right i) • (ℛ k a).left i) =
      D (∑ i ∈ (ℛ k a).index, Coalgebra.counit (R := k) ((ℛ k a).left i) • (ℛ k a).right i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  rw [h, Coalgebra.sum_counit_smul (ℛ k a)]

private lemma isUnit_of_counit_ne_zero {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (ε : A →ₐ[k] k) {N : ℕ} (hN : (RingHom.ker ε) ^ N = ⊥) {a : A} (ha : ε a ≠ 0) :
    IsUnit a := by
  have hy : a - ε a • (1 : A) ∈ RingHom.ker ε := by
    simp [RingHom.mem_ker, Algebra.smul_def]
  have hnil : IsNilpotent (a - ε a • (1 : A)) := by
    refine ⟨N, ?_⟩
    have : (a - ε a • (1 : A)) ^ N ∈ (RingHom.ker ε) ^ N := Ideal.pow_mem_pow hy N
    rwa [hN, Ideal.mem_bot] at this
  have hu : IsUnit (ε a • (1 : A)) := by
    rw [Algebra.smul_def, mul_one]
    exact (IsUnit.mk0 (ε a) ha).map (algebraMap k A)
  have heq : a = ε a • (1 : A) + (a - ε a • (1 : A)) := by ring
  rw [heq]
  exact hnil.isUnit_add_left_of_commute hu (Commute.all _ _)

private lemma local_hopf_charZero {k A : Type*} [Field k] [CharZero k] [CommRing A]
    [HopfAlgebra k A] {N : ℕ} (hN : (RingHom.ker (Bialgebra.counitAlgHom k A)) ^ N = ⊥) :
    RingHom.ker (Bialgebra.counitAlgHom k A) = ⊥ := by
  set 𝔪 := RingHom.ker (Bialgebra.counitAlgHom k A)
  by_contra hne
  have hlt : 𝔪 ^ 2 ≠ 𝔪 := by
    intro heq
    have hpow : ∀ t : ℕ, 𝔪 ^ (t + 1) = 𝔪 := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, ih, ← sq, heq]
    have : 𝔪 = ⊥ := by
      rcases eq_or_ne N 0 with rfl | hN0
      · simp at hN
        have h1 : (1 : A) = 0 := by
          have : (1 : A) ∈ (⊥ : Ideal A) := by rw [← hN]; trivial
          simpa using this
        ext x
        simp [show x = 0 by rw [← mul_one x, h1, mul_zero]]
      · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
        rw [← hpow t, hN]
    exact hne this
  have hle : 𝔪 ^ 2 ≤ 𝔪 := Ideal.pow_le_self (by decide)
  have hex : ∃ x ∈ 𝔪, x ∉ 𝔪 ^ 2 := by
    by_contra h
    push_neg at h
    exact hlt (le_antisymm hle h)
  rcases hex with ⟨x, hx, hx2⟩
  obtain ⟨D, hD1, hD2, hDx⟩ := point_deriv_exists (Bialgebra.counitAlgHom k A) x hx hx2
  let δ := leftInvDeriv D
  have hδmul : ∀ a b, δ (a * b) = a * δ b + δ a * b := leftInvDeriv_mul D hD1 hD2
  have hδx_unit : IsUnit (δ x) := by
    apply isUnit_of_counit_ne_zero (Bialgebra.counitAlgHom k A) hN
    change Coalgebra.counit (R := k) (leftInvDeriv D x) ≠ 0
    rw [counit_leftInvDeriv, hDx]
    exact one_ne_zero
  have hxnil : ∃ r : ℕ, x ^ r = 0 := by
    refine ⟨N, ?_⟩
    have : x ^ N ∈ 𝔪 ^ N := Ideal.pow_mem_pow hx N
    rwa [hN, Ideal.mem_bot] at this
  classical
  let r := Nat.find hxnil
  have hr : x ^ r = 0 := Nat.find_spec hxnil
  have hr0 : r ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hr
    have h10 : (1 : k) = 0 := by
      have := congrArg (Bialgebra.counitAlgHom k A) hr
      simpa using this
    exact one_ne_zero h10
  have hδ0 : δ (x ^ r) = 0 := by rw [hr, map_zero]
  rw [leftInvDeriv_pow δ hδmul x r] at hδ0
  have hsmul : (r : k) • (x ^ (r - 1) * δ x) = 0 := by
    simpa [nsmul_eq_mul, Algebra.smul_def] using hδ0
  have hrk : (r : k) ≠ 0 := Nat.cast_ne_zero.mpr hr0
  have hmul0 : x ^ (r - 1) * δ x = 0 := (smul_eq_zero.mp hsmul).resolve_left hrk
  have hxpred : x ^ (r - 1) = 0 := hδx_unit.mul_left_eq_zero.mp hmul0
  exact Nat.find_min hxnil (Nat.sub_lt (Nat.pos_of_ne_zero hr0) Nat.one_pos) hxpred

-- Helper for CharP case: Frobenius subalgebra A^p of a local finite-dim Hopf algebra over alg closed k
private def frobSubalgebra (k A : Type*) (p : ℕ) [Field k] [IsAlgClosed k] [CharP k p]
    [Fact p.Prime] [CommRing A] [Algebra k A] : Subalgebra k A where
  carrier := {b : A | ∃ a : A, a ^ p = b}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, mul_pow a b p⟩
  one_mem' := ⟨1, one_pow p⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    by_cases hnt : Nontrivial A
    · have : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
      exact ⟨a + b, add_pow_char a b p⟩
    · rw [not_nontrivial_iff_subsingleton] at hnt
      exact ⟨0, Subsingleton.elim _ _⟩
  zero_mem' := ⟨0, zero_pow (Fact.out : p.Prime).ne_zero⟩
  algebraMap_mem' := fun c => by
    obtain ⟨c', hc'⟩ := IsAlgClosed.exists_pow_nat_eq c (Fact.out : p.Prime).pos
    exact ⟨algebraMap k A c', by rw [← map_pow, hc']⟩

-- Define HopfAlgebra structure on S = frobSubalgebra k A p
private lemma comul_mem_frob_tensor {k A : Type*} {p : ℕ} [Field k] [IsAlgClosed k] [CharP k p]
    [Fact p.Prime] [CommRing A] [HopfAlgebra k A] (a : A) :
    Coalgebra.comul (R := k) (a ^ p) ∈
      LinearMap.range (TensorProduct.map
        (frobSubalgebra k A p).val.toLinearMap
        (frobSubalgebra k A p).val.toLinearMap) := by
  by_cases hnt : Nontrivial (A ⊗[k] A)
  · have : CharP (A ⊗[k] A) p := charP_of_injective_algebraMap (algebraMap k (A ⊗[k] A)).injective p
    have h1 : Coalgebra.comul (R := k) (a ^ p) = (Coalgebra.comul (R := k) a) ^ p := by
      change (Bialgebra.comulAlgHom k A) (a ^ p) = ((Bialgebra.comulAlgHom k A) a) ^ p
      exact map_pow _ a p
    rw [h1, ← (ℛ k a).eq, sum_pow_char]
    refine Submodule.sum_mem _ fun i _ => ?_
    have htmul : ((ℛ k a).left i ⊗ₜ[k] (ℛ k a).right i) ^ p =
        ((ℛ k a).left i ^ p) ⊗ₜ[k] ((ℛ k a).right i ^ p) := by
      have : ∀ m : ℕ, ((ℛ k a).left i ⊗ₜ[k] (ℛ k a).right i) ^ m =
          ((ℛ k a).left i ^ m) ⊗ₜ[k] ((ℛ k a).right i ^ m) := by
        intro m
        induction m with
        | zero => simp [Algebra.TensorProduct.one_def]
        | succ m ih => rw [pow_succ, pow_succ, pow_succ, ih, Algebra.TensorProduct.tmul_mul_tmul]
      exact this p
    rw [htmul]
    exact ⟨⟨(ℛ k a).left i ^ p, ⟨_, rfl⟩⟩ ⊗ₜ[k] ⟨(ℛ k a).right i ^ p, ⟨_, rfl⟩⟩, rfl⟩
  · rw [not_nontrivial_iff_subsingleton] at hnt
    exact ⟨0, Subsingleton.elim _ _⟩

private noncomputable def frobHopfAlgebra {k A : Type*} {p : ℕ} [Field k] [IsAlgClosed k]
    [CharP k p] [Fact p.Prime] [CommRing A] [HopfAlgebra k A] :
    HopfAlgebra k (frobSubalgebra k A p) := by
  let S := frobSubalgebra k A p
  let ι : S →ₐ[k] A := S.val
  have hι_inj : Function.Injective ι := Subtype.val_injective
  have hmap_inj : Function.Injective (TensorProduct.map ι.toLinearMap ι.toLinearMap) :=
    tensorMap_injective hι_inj hι_inj
  let fcomul : S →ₗ[k] S ⊗[k] S :=
    (LinearEquiv.ofInjective (TensorProduct.map ι.toLinearMap ι.toLinearMap) hmap_inj).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict _ (Coalgebra.comul (R := k) ∘ₗ ι.toLinearMap)
        (by rintro ⟨b, ⟨a, rfl⟩⟩; exact comul_mem_frob_tensor a)
  have hfcomul : ∀ s : S,
      TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul s) = Coalgebra.comul (R := k) (ι s) := by
    intro s
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective (TensorProduct.map ι.toLinearMap ι.toLinearMap) hmap_inj).apply_symm_apply
        (LinearMap.codRestrict _ (Coalgebra.comul (R := k) ∘ₗ ι.toLinearMap)
          (by rintro ⟨b, ⟨a, rfl⟩⟩; exact comul_mem_frob_tensor a) s))
    exact h
  let fcounit : S →ₗ[k] k := Coalgebra.counit (R := k) ∘ₗ ι.toLinearMap
  have hcoassoc : (TensorProduct.assoc k S S S).toLinearMap ∘ₗ LinearMap.rTensor S fcomul ∘ₗ fcomul =
      LinearMap.lTensor S fcomul ∘ₗ fcomul := by
    have hinj3 : Function.Injective
        (TensorProduct.map ι.toLinearMap (TensorProduct.map ι.toLinearMap ι.toLinearMap)) :=
      tensorMap_injective hι_inj hmap_inj
    ext s
    apply hinj3
    have h1 : TensorProduct.map ι.toLinearMap (TensorProduct.map ι.toLinearMap ι.toLinearMap)
        ((TensorProduct.assoc k S S S).toLinearMap (LinearMap.rTensor S fcomul (fcomul s))) =
        (TensorProduct.assoc k A A A).toLinearMap (LinearMap.rTensor A (Coalgebra.comul (R := k))
          (Coalgebra.comul (R := k) (ι s))) := by
      have hcomm : (TensorProduct.map ι.toLinearMap (TensorProduct.map ι.toLinearMap ι.toLinearMap)).comp
          (TensorProduct.assoc k S S S).toLinearMap =
          (TensorProduct.assoc k A A A).toLinearMap.comp
          (TensorProduct.map (TensorProduct.map ι.toLinearMap ι.toLinearMap) ι.toLinearMap) := by
        ext x y z; rfl
      change ((TensorProduct.map ι.toLinearMap (TensorProduct.map ι.toLinearMap ι.toLinearMap)).comp
        (TensorProduct.assoc k S S S).toLinearMap) _ = _
      rw [hcomm, LinearMap.comp_apply]
      congr 1
      have hcomm2 : (TensorProduct.map (TensorProduct.map ι.toLinearMap ι.toLinearMap) ι.toLinearMap).comp
          (LinearMap.rTensor S fcomul) =
          (LinearMap.rTensor A (Coalgebra.comul (R := k))).comp
            (TensorProduct.map ι.toLinearMap ι.toLinearMap) := by
        ext x y
        change TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul x) ⊗ₜ[k] ι y =
          Coalgebra.comul (R := k) (ι x) ⊗ₜ[k] ι y
        rw [hfcomul]
      change ((TensorProduct.map (TensorProduct.map ι.toLinearMap ι.toLinearMap) ι.toLinearMap).comp
        (LinearMap.rTensor S fcomul)) (fcomul s) = _
      rw [hcomm2, LinearMap.comp_apply, hfcomul]
    have h2 : TensorProduct.map ι.toLinearMap (TensorProduct.map ι.toLinearMap ι.toLinearMap)
        (LinearMap.lTensor S fcomul (fcomul s)) =
        LinearMap.lTensor A (Coalgebra.comul (R := k)) (Coalgebra.comul (R := k) (ι s)) := by
      have hcomm2 : (TensorProduct.map ι.toLinearMap (TensorProduct.map ι.toLinearMap ι.toLinearMap)).comp
          (LinearMap.lTensor S fcomul) =
          (LinearMap.lTensor A (Coalgebra.comul (R := k))).comp
            (TensorProduct.map ι.toLinearMap ι.toLinearMap) := by
        ext x y
        change ι x ⊗ₜ[k] TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul y) =
          ι x ⊗ₜ[k] Coalgebra.comul (R := k) (ι y)
        rw [hfcomul]
      change ((TensorProduct.map ι.toLinearMap (TensorProduct.map ι.toLinearMap ι.toLinearMap)).comp
        (LinearMap.lTensor S fcomul)) (fcomul s) = _
      rw [hcomm2, LinearMap.comp_apply, hfcomul]
    simp only [LinearMap.comp_apply]
    rw [h1, h2]
    exact LinearMap.congr_fun (Coalgebra.coassoc (R := k) (A := A)) (ι s)
  have hrTensor : LinearMap.rTensor S fcounit ∘ₗ fcomul = (TensorProduct.lid k S).symm.toLinearMap := by
    have hinj2 : Function.Injective (LinearMap.lTensor k ι.toLinearMap) :=
      tensorMap_injective Function.injective_id hι_inj
    ext s
    apply hinj2
    simp only [LinearMap.comp_apply, TensorProduct.lid_symm_apply]
    have hcomm : (LinearMap.lTensor k ι.toLinearMap).comp (LinearMap.rTensor S fcounit) =
        (LinearMap.rTensor A (Coalgebra.counit (R := k))).comp
          (TensorProduct.map ι.toLinearMap ι.toLinearMap) := by
      ext x y; rfl
    change ((LinearMap.lTensor k ι.toLinearMap).comp (LinearMap.rTensor S fcounit)) (fcomul s) = _
    rw [hcomm, LinearMap.comp_apply, hfcomul, Coalgebra.rTensor_counit_comul]
    rfl
  have hlTensor : LinearMap.lTensor S fcounit ∘ₗ fcomul = (TensorProduct.rid k S).symm.toLinearMap := by
    have hinj2 : Function.Injective (LinearMap.rTensor k ι.toLinearMap) :=
      tensorMap_injective hι_inj Function.injective_id
    ext s
    apply hinj2
    simp only [LinearMap.comp_apply, TensorProduct.rid_symm_apply]
    have hcomm : (LinearMap.rTensor k ι.toLinearMap).comp (LinearMap.lTensor S fcounit) =
        (LinearMap.lTensor A (Coalgebra.counit (R := k))).comp
          (TensorProduct.map ι.toLinearMap ι.toLinearMap) := by
      ext x y; rfl
    change ((LinearMap.rTensor k ι.toLinearMap).comp (LinearMap.lTensor S fcounit)) (fcomul s) = _
    rw [hcomm, LinearMap.comp_apply, hfcomul, Coalgebra.lTensor_counit_comul]
    rfl
  let fantipode : S →ₗ[k] S :=
    LinearMap.codRestrict S.toSubmodule (HopfAlgebra.antipode k ∘ₗ ι.toLinearMap)
      (by
        rintro ⟨b, ⟨a, rfl⟩⟩
        refine ⟨HopfAlgebra.antipode k a, ?_⟩
        change (HopfAlgebra.antipodeAlgHom k A a) ^ p = HopfAlgebra.antipodeAlgHom k A (a ^ p)
        exact (map_pow _ a p).symm)
  have hfantipode : ∀ s : S, ι (fantipode s) = HopfAlgebra.antipode k (ι s) := fun _ => rfl
  letI : Coalgebra k S :=
    { comul := fcomul
      counit := fcounit
      coassoc := hcoassoc
      rTensor_counit_comp_comul := hrTensor
      lTensor_counit_comp_comul := hlTensor }
  letI : Bialgebra k S :=
    { counit_one := by change Coalgebra.counit (R := k) (1 : A) = 1; simp
      mul_compr₂_counit := by
        ext x y
        change Coalgebra.counit (R := k) (ι x * ι y) =
          Coalgebra.counit (R := k) (ι x) * Coalgebra.counit (R := k) (ι y)
        exact Bialgebra.counit_mul (ι x) (ι y)
      comul_one := by
        apply hmap_inj
        change TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul 1) = _
        rw [hfcomul]
        simp [Algebra.TensorProduct.one_def]
      mul_compr₂_comul := by
        ext x y
        apply hmap_inj
        change TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul (x * y)) =
          TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul x * fcomul y)
        rw [hfcomul]
        have hmul : TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul x * fcomul y) =
            TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul x) *
            TensorProduct.map ι.toLinearMap ι.toLinearMap (fcomul y) := by
          change (Algebra.TensorProduct.map ι ι) (fcomul x * fcomul y) = _
          exact map_mul (Algebra.TensorProduct.map ι ι) (fcomul x) (fcomul y)
        rw [hmul, hfcomul, hfcomul, map_mul, Bialgebra.comul_mul] }
  refine
    { antipode := fantipode
      mul_antipode_rTensor_comul := by
        ext s
        simp only [LinearMap.comp_apply]
        have hcomm : ι.toLinearMap.comp (LinearMap.mul' k S) =
            (LinearMap.mul' k A).comp (TensorProduct.map ι.toLinearMap ι.toLinearMap) := by
          ext x y; simp
        change (ι.toLinearMap.comp (LinearMap.mul' k S)) (LinearMap.rTensor S fantipode (fcomul s)) = _
        rw [hcomm, LinearMap.comp_apply]
        have hcomm2 : (TensorProduct.map ι.toLinearMap ι.toLinearMap).comp (LinearMap.rTensor S fantipode) =
            (LinearMap.rTensor A (HopfAlgebra.antipode k)).comp
              (TensorProduct.map ι.toLinearMap ι.toLinearMap) := by
          ext x y; rfl
        change (LinearMap.mul' k A)
          (((TensorProduct.map ι.toLinearMap ι.toLinearMap).comp (LinearMap.rTensor S fantipode)) (fcomul s)) = _
        rw [hcomm2, LinearMap.comp_apply, hfcomul, HopfAlgebra.mul_antipode_rTensor_comul_apply]
        rfl
      mul_antipode_lTensor_comul := by
        ext s
        simp only [LinearMap.comp_apply]
        have hcomm : ι.toLinearMap.comp (LinearMap.mul' k S) =
            (LinearMap.mul' k A).comp (TensorProduct.map ι.toLinearMap ι.toLinearMap) := by
          ext x y; simp
        change (ι.toLinearMap.comp (LinearMap.mul' k S)) (LinearMap.lTensor S fantipode (fcomul s)) = _
        rw [hcomm, LinearMap.comp_apply]
        have hcomm2 : (TensorProduct.map ι.toLinearMap ι.toLinearMap).comp (LinearMap.lTensor S fantipode) =
            (LinearMap.lTensor A (HopfAlgebra.antipode k)).comp
              (TensorProduct.map ι.toLinearMap ι.toLinearMap) := by
          ext x y; rfl
        change (LinearMap.mul' k A)
          (((TensorProduct.map ι.toLinearMap ι.toLinearMap).comp (LinearMap.lTensor S fantipode)) (fcomul s)) = _
        rw [hcomm2, LinearMap.comp_apply, hfcomul, HopfAlgebra.mul_antipode_lTensor_comul_apply]
        rfl }

-- Apply an iterated S-linear derivation dOp_i^e to a monomial ∏_j x_j^(α j)
private lemma deriv_iter_monomial {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    {s : ℕ} (x : Fin s → A) (dOp : Fin s → (A →ₗ[k] A))
    (hdOpmul : ∀ j a b, dOp j (a * b) = a * dOp j b + dOp j a * b)
    (hdOpx : ∀ j i, dOp j (x i) = if j = i then 1 else 0) :
    ∀ (j : Fin s) (α : Fin s → ℕ) (e : ℕ),
      (dOp j ^ e) (∏ i : Fin s, x i ^ α i) =
        if e ≤ α j then
          ((Nat.descFactorial (α j) e : ℕ) : k) •
            ∏ i : Fin s, x i ^ (if i = j then α j - e else α i)
        else 0 := by
  intro j α e
  have hdOp1 : dOp j 1 = 0 := by
    have h0 : dOp j 1 = dOp j 1 + dOp j 1 := by simpa using hdOpmul j 1 1
    linear_combination -h0
  have hdOpprod_ne : ∀ (β : Fin s → ℕ) (S : Finset (Fin s)), j ∉ S → dOp j (∏ i ∈ S, x i ^ β i) = 0 := by
    intro β S hS
    induction S using Finset.cons_induction with
    | empty => simpa using hdOp1
    | cons a S ha ih =>
      rw [Finset.prod_cons, hdOpmul]
      have hja : j ≠ a := fun h => hS (h ▸ Finset.mem_cons_self a S)
      have hjS : j ∉ S := fun h => hS (Finset.mem_cons_of_mem h)
      rw [ih hjS, mul_zero, zero_add, leftInvDeriv_pow (dOp j) (hdOpmul j) (x a) (β a),
        hdOpx j a, if_neg hja, mul_zero, smul_zero, zero_mul]
  have hstep : ∀ (β : Fin s → ℕ),
      dOp j (∏ i : Fin s, x i ^ β i) =
        if 0 < β j then
          (β j : k) • ∏ i : Fin s, x i ^ (if i = j then β j - 1 else β i)
        else 0 := by
    intro β
    have hsplit : ∏ i : Fin s, x i ^ β i =
        x j ^ β j * ∏ i ∈ Finset.univ.erase j, x i ^ β i := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i => x i ^ β i) (Finset.mem_univ j)]
    rw [hsplit, hdOpmul, hdOpprod_ne β (Finset.univ.erase j) (Finset.notMem_erase j _),
      mul_zero, zero_add, leftInvDeriv_pow (dOp j) (hdOpmul j) (x j) (β j), hdOpx j j, if_pos rfl,
      mul_one]
    by_cases hpos : 0 < β j
    · rw [if_pos hpos]
      have hsplit2 : ∏ i : Fin s, x i ^ (if i = j then β j - 1 else β i) =
          x j ^ (β j - 1) * ∏ i ∈ Finset.univ.erase j, x i ^ β i := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        simp only [if_pos rfl]
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [if_neg (Finset.ne_of_mem_erase hi)]
      rw [hsplit2, nsmul_eq_mul, Algebra.smul_def, map_natCast, mul_assoc]
    · rw [if_neg hpos]
      have h0 : β j = 0 := Nat.eq_zero_of_not_pos hpos
      simp [h0]
  induction e with
  | zero =>
    simp only [Nat.zero_le, ↓reduceIte, Nat.descFactorial_zero, Nat.cast_one, one_smul,
      Nat.sub_zero, pow_zero, Module.End.one_apply]
    congr 1
    ext i
    split_ifs with h <;> simp [h]
  | succ e ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    split_ifs with h1 h2
    · -- e ≤ α j and e + 1 ≤ α j
      rw [map_smul, hstep]
      have hpos : 0 < (if j = j then α j - e else α j) := by
        simp only [↓reduceIte]
        omega
      rw [if_pos hpos]
      simp only [↓reduceIte, smul_smul]
      congr 1
      · rw [Nat.descFactorial_succ, Nat.cast_mul, mul_comm]
      · refine Finset.prod_congr rfl fun i _ => ?_
        split_ifs with hij
        · subst hij; simp [Nat.sub_sub]
        · rfl
    · -- e ≤ α j, ¬ (e + 1 ≤ α j), so α j = e
      rw [map_smul, hstep]
      have h0 : ¬ 0 < (if j = j then α j - e else α j) := by
        simp only [↓reduceIte]; omega
      rw [if_neg h0, smul_zero]
    · -- ¬ (e ≤ α j), so ¬ (e + 1 ≤ α j)
      omega
    · rw [map_zero]

private lemma local_hopf_charP_aux (k : Type*) (p : ℕ) [Field k] [IsAlgClosed k] [CharP k p]
    [Fact p.Prime] :
    ∀ (d : ℕ) (A : Type v) [CommRing A] [HopfAlgebra k A] [Module.Finite k A],
      Module.finrank k A = d →
      (∃ N : ℕ, (RingHom.ker (Bialgebra.counitAlgHom k A)) ^ N = ⊥) →
      ∃ r : ℕ, d = p ^ r := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro A _ _ _ hd ⟨N, hN⟩
    set 𝔪 := RingHom.ker (Bialgebra.counitAlgHom k A)
    by_cases h𝔪 : 𝔪 = ⊥
    · -- A ≅ k so finrank = 1 = p^0
      refine ⟨0, ?_⟩
      rw [pow_zero, ← hd]
      have hinj : Function.Injective (Bialgebra.counitAlgHom k A) := by
        rw [RingHom.injective_iff_ker_eq_bot]
        exact h𝔪
      have hsurj : Function.Surjective (Bialgebra.counitAlgHom k A) :=
        fun c => ⟨algebraMap k A c, by simp⟩
      exact (LinearEquiv.ofBijective (Bialgebra.counitAlgHom k A).toLinearMap
        ⟨hinj, hsurj⟩).finrank_eq.trans (Module.finrank_self k)
    · -- 𝔪 ≠ ⊥: S = frobSubalgebra k A p has strictly smaller finrank and is a local Hopf algebra
      let S := frobSubalgebra k A p
      letI : HopfAlgebra k S := frobHopfAlgebra
      have hfinS_inst : Module.Finite k S := Module.Finite.of_injective S.val.toLinearMap Subtype.val_injective
      -- 𝔪^2 ≠ 𝔪
      have hlt2 : 𝔪 ^ 2 ≠ 𝔪 := by
        intro heq
        have hpow : ∀ t : ℕ, 𝔪 ^ (t + 1) = 𝔪 := by
          intro t
          induction t with
          | zero => simp
          | succ t iht => rw [pow_succ, iht, ← sq, heq]
        rcases eq_or_ne N 0 with rfl | hN0
        · simp at hN
          have h1 : (1 : A) = 0 := by
            have : (1 : A) ∈ (⊥ : Ideal A) := by rw [← hN]; trivial
            simpa using this
          exact h𝔪 (by ext x; simp [show x = 0 by rw [← mul_one x, h1, mul_zero]])
        · obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
          exact h𝔪 (by rw [← hpow t, hN])
      have hex : ∃ x ∈ 𝔪, x ∉ 𝔪 ^ 2 := by
        by_contra h
        push Not at h
        exact hlt2 (le_antisymm (Ideal.pow_le_self (by decide)) h)
      rcases hex with ⟨x₀, hx₀, hx₀2⟩
      have hx₀S : x₀ ∉ S := by
        rintro ⟨a, ha⟩
        have hεa : Bialgebra.counitAlgHom k A a = 0 := by
          have : (Bialgebra.counitAlgHom k A a) ^ p = 0 := by
            rw [← map_pow, ha]; exact hx₀
          exact eq_zero_of_pow_eq_zero this
        have ha𝔪 : a ∈ 𝔪 := hεa
        have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
        have hmem : a ^ p ∈ 𝔪 ^ 2 :=
          Ideal.pow_le_pow_right hp2 (Ideal.pow_mem_pow ha𝔪 p)
        rw [ha] at hmem
        exact hx₀2 hmem
      have hS_lt : Module.finrank k S < d := by
        rw [← hd]
        exact Submodule.finrank_lt (s := S.toSubmodule) fun htop =>
          hx₀S (by rw [← Subalgebra.mem_toSubmodule, htop]; trivial)
      have hSN : (RingHom.ker (Bialgebra.counitAlgHom k S)) ^ N = ⊥ := by
        ext ⟨s, hs⟩
        simp only [Ideal.mem_bot]
        constructor
        · intro hmem
          have hmap : S.val ⟨s, hs⟩ ∈ Ideal.map S.val ((RingHom.ker (Bialgebra.counitAlgHom k S)) ^ N) :=
            Ideal.mem_map_of_mem _ hmem
          rw [Ideal.map_pow] at hmap
          have hle : Ideal.map S.val (RingHom.ker (Bialgebra.counitAlgHom k S)) ≤ 𝔪 := by
            rw [Ideal.map_le_iff_le_comap]
            intro y hy
            exact hy
          have hpow_le : ∀ t : ℕ, Ideal.map S.val (RingHom.ker (Bialgebra.counitAlgHom k S)) ^ t ≤ 𝔪 ^ t := by
            intro t
            induction t with
            | zero => simp
            | succ t iht => rw [pow_succ, pow_succ]; exact Ideal.mul_mono iht hle
          have hmem2 : s ∈ 𝔪 ^ N := hpow_le N hmap
          rw [hN, Ideal.mem_bot] at hmem2
          exact Subtype.ext hmem2
        · intro h0
          rw [h0]
          exact zero_mem _
      obtain ⟨r₀, hr₀⟩ := @ih (Module.finrank k S) hS_lt S _ _ hfinS_inst rfl ⟨N, hSN⟩
      -- Now show A is free over S of rank p^s where s = dim_k (𝔪 / 𝔪^2)
      -- Let V = 𝔪.restrictScalars k, W = (𝔪^2).restrictScalars k ≤ V
      let V : Submodule k A := 𝔪.restrictScalars k
      let W : Submodule k A := (𝔪 ^ 2).restrictScalars k
      have hWV : W ≤ V := Ideal.pow_le_self (by decide)
      let Q := V ⧸ (W.comap V.subtype)
      have : Module.Finite k Q := Module.Finite.of_surjective
        (Submodule.mkQ _ ∘ₗ LinearMap.id) (Submodule.mkQ_surjective _)
      let s := Module.finrank k Q
      let bQ : Module.Basis (Fin s) k Q := Module.finBasis k Q
      -- Lift basis vectors to x : Fin s → A with x i ∈ 𝔪
      have hlift : ∀ i : Fin s, ∃ v : V, Submodule.Quotient.mk v = bQ i :=
        fun i => Submodule.Quotient.mk_surjective _ (bQ i)
      choose v hv using hlift
      let x : Fin s → A := fun i => (v i : A)
      -- Construct dual functionals D : Fin s → (A →ₗ[k] k) vanishing on k•1 + 𝔪^2 with D j (x i) = δ_{ij}
      let proj𝔪 : A →ₗ[k] V :=
        { toFun := fun a => ⟨a - (Bialgebra.counitAlgHom k A a) • (1 : A), by
            change a - _ ∈ 𝔪
            simp [𝔪, RingHom.mem_ker, Algebra.smul_def]⟩
          map_add' := fun a b => by
            ext; simp [map_add, add_smul]; abel
          map_smul' := fun c a => by
            ext; simp [map_smul, smul_sub, mul_smul] }
      let D : Fin s → (A →ₗ[k] k) := fun j =>
        (bQ.coord j) ∘ₗ (Submodule.mkQ (W.comap V.subtype)) ∘ₗ proj𝔪
      have hD1 : ∀ j, D j 1 = 0 := by
        intro j
        have : proj𝔪 1 = 0 := by ext; simp [proj𝔪]
        simp [D, this]
      have hD2 : ∀ j y, y ∈ 𝔪 ^ 2 → D j y = 0 := by
        intro j y hy
        have hyV : y ∈ V := Ideal.pow_le_self (by decide) hy
        have hεy : Bialgebra.counitAlgHom k A y = 0 := hyV
        have hp : proj𝔪 y = ⟨y, hyV⟩ := by
          ext; dsimp [proj𝔪]; rw [hεy, zero_smul, sub_zero]
        simp only [D, LinearMap.comp_apply, hp]
        change (bQ.coord j) (Submodule.Quotient.mk (p := W.comap V.subtype) ⟨y, hyV⟩) = 0
        have hq : Submodule.Quotient.mk (p := W.comap V.subtype) ⟨y, hyV⟩ = 0 := by
          rw [Submodule.Quotient.mk_eq_zero]
          exact hy
        rw [hq, map_zero]
      have hDx : ∀ j i, D j (x i) = if j = i then 1 else 0 := by
        intro j i
        have hεx : Bialgebra.counitAlgHom k A (x i) = 0 := (v i).2
        have hp : proj𝔪 (x i) = v i := by
          ext; dsimp [proj𝔪, x]; rw [hεx, zero_smul, sub_zero]
        simp only [D, LinearMap.comp_apply, hp, bQ.coord_apply]
        change (bQ.repr (Submodule.Quotient.mk (p := W.comap V.subtype) (v i))) j = _
        rw [hv, bQ.repr_self, Finsupp.single_apply]
        by_cases h1 : i = j
        · subst h1; simp
        · have h2 : j ≠ i := Ne.symm h1; simp [h1, h2]
      let δ : Fin s → (A →ₗ[k] A) := fun j => leftInvDeriv (D j)
      have hδmul : ∀ j a b, δ j (a * b) = a * δ j b + δ j a * b :=
        fun j => leftInvDeriv_mul (D j) (hD1 j) (hD2 j)
      -- Matrix M_{j, i} = δ j (x i) has counit(M_{j,i}) = δ_{j,i}, so det M is a unit in A
      let M : Matrix (Fin s) (Fin s) A := Matrix.of fun j i => δ j (x i)
      have hM_counit : (Bialgebra.counitAlgHom k A).mapMatrix M = 1 := by
        ext j i
        simp only [M, Matrix.one_apply]
        change Coalgebra.counit (R := k) (leftInvDeriv (D j) (x i)) = _
        rw [counit_leftInvDeriv, hDx]
      have hdet_unit : IsUnit M.det := by
        apply isUnit_of_counit_ne_zero (Bialgebra.counitAlgHom k A) hN
        have h1 : Bialgebra.counitAlgHom k A M.det =
            ((Bialgebra.counitAlgHom k A).mapMatrix M).det :=
          RingHom.map_det (Bialgebra.counitAlgHom k A).toRingHom M
        rw [h1, hM_counit, Matrix.det_one]
        exact one_ne_zero
      obtain ⟨uDet, huDet⟩ := hdet_unit
      let Minv : Matrix (Fin s) (Fin s) A := ((uDet⁻¹ : Aˣ) : A) • M.adjugate
      have hMinvM : Minv * M = 1 := by
        dsimp [Minv]
        rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, ← huDet,
          ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      -- Define normalized derivations dOp_k = ∑_j Minv_{k, j} • δ_j
      let dOp : Fin s → (A →ₗ[k] A) := fun i =>
        ∑ j : Fin s, (LinearMap.mulLeft k (Minv i j)) ∘ₗ δ j
      have hdOpmul : ∀ i a b, dOp i (a * b) = a * dOp i b + dOp i a * b := by
        intro i a b
        simp only [dOp, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
          hδmul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
        congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring
      have hdOpx : ∀ i l, dOp i (x l) = if i = l then 1 else 0 := by
        intro i l
        simp only [dOp, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
        have h := congrFun (congrFun hMinvM i) l
        simpa [Matrix.mul_apply, M, Matrix.one_apply] using h
      have hdOpS : ∀ i (c : S) (a : A), dOp i ((c : A) * a) = (c : A) * dOp i a := by
        intro i ⟨c, ⟨u, hu⟩⟩ a
        rw [hdOpmul]
        have h0 : dOp i c = 0 := by
          rw [← hu, leftInvDeriv_pow (dOp i) (hdOpmul i) u p]
          by_cases hnt : Nontrivial A
          · have : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
            simp [CharP.cast_eq_zero]
          · rw [not_nontrivial_iff_subsingleton] at hnt
            exact Subsingleton.elim _ _
        rw [h0, zero_mul, add_zero]
      -- Monomials indexed by α : Fin s → Fin p
      let mon : (Fin s → Fin p) → A := fun α => ∏ i : Fin s, x i ^ (α i : ℕ)
      -- 1) Linear independence of `mon` over S (as S-module)
      have hlinind : LinearIndependent S mon := by
        classical
        rw [Fintype.linearIndependent_iff]
        intro c hc
        by_contra hne
        push Not at hne
        -- Pick β maximizing total degree ∑ i, (β i : ℕ) among {β | c β ≠ 0}
        let T : Finset (Fin s → Fin p) := Finset.univ.filter fun α => c α ≠ 0
        have hT : T.Nonempty := by
          rcases hne with ⟨α, hα⟩
          exact ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩⟩
        obtain ⟨β, hβT, hβmax⟩ := Finset.exists_max_image T (fun α => ∑ i : Fin s, (α i : ℕ)) hT
        have hcβ : c β ≠ 0 := (Finset.mem_filter.mp hβT).2
        -- Define iterated differential operator L = ∏_j (dOp j ^ (β j : ℕ)) via list fold
        let op : (Fin s → ℕ) → (A →ₗ[k] A) := fun e =>
          (List.finRange s).foldl (fun acc j => (dOp j ^ e j) ∘ₗ acc) LinearMap.id
        -- Prove by induction on prefix that applying dOp_j^(e j) commutes with S-scalars and acts on monomials
        have hopS : ∀ (l : List (Fin s)) (e : Fin s → ℕ) (u : S) (a : A),
            (l.foldl (fun acc j => (dOp j ^ e j) ∘ₗ acc) LinearMap.id) ((u : A) * a) =
              (u : A) * (l.foldl (fun acc j => (dOp j ^ e j) ∘ₗ acc) LinearMap.id) a := by
          intro l e u
          have hpowS : ∀ (j : Fin s) (t : ℕ) (a : A),
              (dOp j ^ t) ((u : A) * a) = (u : A) * (dOp j ^ t) a := by
            intro j t
            induction t with
            | zero => intro a; rfl
            | succ t iht =>
              intro a
              rw [pow_succ', Module.End.mul_apply, iht, hdOpS]
              rfl
          have hgen : ∀ (l : List (Fin s)) (f : A →ₗ[k] A),
              (∀ a, f ((u : A) * a) = (u : A) * f a) →
              ∀ a, (l.foldl (fun acc j => (dOp j ^ e j) ∘ₗ acc) f) ((u : A) * a) =
                (u : A) * (l.foldl (fun acc j => (dOp j ^ e j) ∘ₗ acc) f) a := by
            intro l
            induction l with
            | nil => intro f hf a; exact hf a
            | cons j l ihl =>
              intro f hf a
              simp only [List.foldl_cons]
              exact ihl ((dOp j ^ e j) ∘ₗ f) (fun y => by simp [hf, hpowS]) a
          exact hgen l LinearMap.id (fun _ => rfl)
        -- Compute action of foldl on any monomial ∏ i, x i ^ (α i)
        have hopMon : ∀ (l : List (Fin s)), l.Nodup →
            ∀ (e α : Fin s → ℕ),
              (l.foldl (fun acc j => (dOp j ^ e j) ∘ₗ acc) LinearMap.id) (∏ i : Fin s, x i ^ α i) =
                if ∀ j ∈ l, e j ≤ α j then
                  (∏ j ∈ l.toFinset, ((Nat.descFactorial (α j) (e j) : ℕ) : k)) •
                    ∏ i : Fin s, x i ^ (if i ∈ l then α i - e i else α i)
                else 0 := by
          intro l hnd e
          induction l using List.reverseRecOn with
          | nil =>
            intro α
            simp
          | append_singleton l j ih =>
            intro α
            rw [List.nodup_append] at hnd
            rcases hnd with ⟨hnd_l, _, hdisj⟩
            have hj_not_l : j ∉ l := fun h => hdisj j h j (List.mem_singleton_self j) rfl
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil, LinearMap.comp_apply,
              ih hnd_l α]
            by_cases h_l : ∀ y ∈ l, e y ≤ α y
            · rw [if_pos h_l]
              by_cases h_all : ∀ y ∈ l ++ [j], e y ≤ α y
              · rw [if_pos h_all, map_smul, deriv_iter_monomial x dOp hdOpmul hdOpx j]
                have hjle : e j ≤ (if j ∈ l then α j - e j else α j) := by
                  rw [if_neg hj_not_l]
                  exact h_all j (List.mem_append_right l (List.mem_singleton_self j))
                rw [if_pos hjle, smul_smul]
                congr 1
                · rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
                    Finset.union_insert, Finset.union_empty,
                    Finset.prod_insert (by simpa using hj_not_l),
                    if_neg hj_not_l, mul_comm]
                · refine Finset.prod_congr rfl fun i _ => ?_
                  by_cases hij : i = j
                  · subst hij
                    simp [hj_not_l]
                  · simp [hij]
              · rw [if_neg h_all, map_smul, deriv_iter_monomial x dOp hdOpmul hdOpx j]
                have hjgt : ¬ e j ≤ (if j ∈ l then α j - e j else α j) := by
                  rw [if_neg hj_not_l]
                  intro hle
                  apply h_all
                  intro y hy
                  rw [List.mem_append, List.mem_singleton] at hy
                  rcases hy with hy | rfl
                  · exact h_l y hy
                  · exact hle
                rw [if_neg hjgt, smul_zero]
            · rw [if_neg h_l, map_zero]
              have h_not_all : ¬ ∀ y ∈ l ++ [j], e y ≤ α y :=
                fun h_all => h_l fun y hy => h_all y (List.mem_append_left [j] hy)
              rw [if_neg h_not_all]
        -- Apply op (fun i => (β i : ℕ)) to hc
        let eβ : Fin s → ℕ := fun i => (β i : ℕ)
        have h0 : op eβ (∑ α : Fin s → Fin p, c α • mon α) = 0 := by rw [hc, map_zero]
        rw [map_sum] at h0
        have hterm : ∀ α : Fin s → Fin p,
            op eβ (c α • mon α) =
              if α = β then
                (∏ j : Fin s, (((β j : ℕ).factorial : ℕ) : k)) • (c β : A)
              else 0 := by
          intro α
          change op eβ ((c α : A) * mon α) = _
          rw [hopS (List.finRange s) eβ (c α) (mon α)]
          have hm := hopMon (List.finRange s) (List.nodup_finRange s) eβ (fun i => (α i : ℕ))
          dsimp [op, mon] at hm ⊢
          rw [hm]
          by_cases hαβ : α = β
          · subst hαβ
            rw [if_pos rfl, if_pos (fun j _ => le_refl _)]
            have hprod1 : ∏ i : Fin s, x i ^ (if i ∈ List.finRange s then (α i : ℕ) - (α i : ℕ) else (α i : ℕ)) = 1 := by
              refine Finset.prod_eq_one fun i _ => ?_
              simp [List.mem_finRange]
            rw [hprod1, mul_smul_comm, mul_one]
            congr 1
            have htoFinset : (List.finRange s).toFinset = Finset.univ := by
              ext j; simp [List.mem_finRange]
            rw [htoFinset]
            refine Finset.prod_congr rfl fun j _ => ?_
            simp [eβ, Nat.descFactorial_self]
          · rw [if_neg hαβ]
            by_cases hcα : c α = 0
            · simp [hcα]
            · have hαT : α ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcα⟩
              have hsumle : ∑ i : Fin s, (α i : ℕ) ≤ ∑ i : Fin s, (β i : ℕ) := hβmax α hαT
              have hnotle : ¬ ∀ j ∈ List.finRange s, eβ j ≤ (α j : ℕ) := by
                intro hle
                have hle' : ∀ j : Fin s, (β j : ℕ) ≤ (α j : ℕ) :=
                  fun j => hle j (List.mem_finRange j)
                have heq : ∀ j : Fin s, (β j : ℕ) = (α j : ℕ) := by
                  have hsum_eq : ∑ j : Fin s, (β j : ℕ) = ∑ j : Fin s, (α j : ℕ) :=
                    le_antisymm (Finset.sum_le_sum fun j _ => hle' j) hsumle
                  intro j
                  by_contra hne'
                  have hlt' : (β j : ℕ) < (α j : ℕ) := lt_of_le_of_ne (hle' j) hne'
                  have hlt_sum : ∑ i : Fin s, (β i : ℕ) < ∑ i : Fin s, (α i : ℕ) :=
                    Finset.sum_lt_sum (fun i _ => hle' i) ⟨j, Finset.mem_univ j, hlt'⟩
                  omega
                exact hαβ (funext fun j => Fin.ext (heq j).symm)
              rw [if_neg hnotle, mul_zero]
        simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
        have hfac_ne : (∏ j : Fin s, (((β j : ℕ).factorial : ℕ) : k)) ≠ 0 := by
          rw [Finset.prod_ne_zero_iff]
          intro j _
          rw [Ne, CharP.cast_eq_zero_iff k p]
          intro hdvd
          have hle := (Fact.out : p.Prime).dvd_factorial.mp hdvd
          exact absurd hle (not_le.mpr (β j).isLt)
        have hcβ0 : (c β : A) = 0 := (smul_eq_zero.mp h0).resolve_left hfac_ne
        exact hcβ (Subtype.ext hcβ0)
      -- 2) Spanning of `mon` over S
      have hspan : Submodule.span S (Set.range mon) = ⊤ := by
        let Msub : Submodule S A := Submodule.span S (Set.range mon)
        -- Msub contains 1
        have hone : (1 : A) ∈ Msub := by
          have h0 : mon (fun _ => ⟨0, (Fact.out : p.Prime).pos⟩) = 1 := by
            simp [mon]
          rw [← h0]
          exact Submodule.subset_span ⟨_, rfl⟩
        -- Msub is closed under multiplication by x i
        have hmul_x : ∀ (i : Fin s) (a : A), a ∈ Msub → x i * a ∈ Msub := by
          intro i a ha
          refine Submodule.span_induction (p := fun y _ => x i * y ∈ Msub) ?_ ?_ ?_ ?_ ha
          · rintro _ ⟨α, rfl⟩
            by_cases hlt : (α i : ℕ) + 1 < p
            · let β : Fin s → Fin p := Function.update α i ⟨(α i : ℕ) + 1, hlt⟩
              have hEq : x i * mon α = mon β := by
                dsimp [mon, β]
                rw [← Finset.mul_prod_erase Finset.univ (fun j => x j ^ (α j : ℕ)) (Finset.mem_univ i),
                  ← Finset.mul_prod_erase Finset.univ (fun j => x j ^ (Function.update α i ⟨(α i : ℕ) + 1, hlt⟩ j : ℕ)) (Finset.mem_univ i)]
                simp only [Function.update_self, ← mul_assoc, pow_succ']
                congr 1
                refine Finset.prod_congr rfl fun j hj => ?_
                simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
              rw [hEq]
              exact Submodule.subset_span ⟨β, rfl⟩
            · have heq : (α i : ℕ) + 1 = p := by omega
              let β : Fin s → Fin p := Function.update α i ⟨0, (Fact.out : p.Prime).pos⟩
              have hEq : x i * mon α = (⟨x i ^ p, ⟨x i, rfl⟩⟩ : S) • mon β := by
                change x i * (∏ j : Fin s, x j ^ (α j : ℕ)) = x i ^ p * (∏ j : Fin s, x j ^ (β j : ℕ))
                rw [← Finset.mul_prod_erase Finset.univ (fun j => x j ^ (α j : ℕ)) (Finset.mem_univ i),
                  ← Finset.mul_prod_erase Finset.univ (fun j => x j ^ (β j : ℕ)) (Finset.mem_univ i)]
                have hβi : (β i : ℕ) = 0 := by simp [β]
                rw [hβi, pow_zero, one_mul, ← mul_assoc, ← pow_succ', heq]
                congr 1
                refine Finset.prod_congr rfl fun j hj => ?_
                simp [β, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
              rw [hEq]
              exact Submodule.smul_mem Msub _ (Submodule.subset_span ⟨β, rfl⟩)
          · simp
          · intro y z _ _ hy hz; rw [mul_add]; exact add_mem hy hz
          · intro c y _ hy
            change x i * ((c : A) * y) ∈ Msub
            rw [mul_left_comm]
            exact Submodule.smul_mem Msub c hy
        -- Hence Msub is closed under multiplication!
        have hmul : ∀ a ∈ Msub, ∀ b ∈ Msub, a * b ∈ Msub := by
          intro a ha b hb
          refine Submodule.span_induction (p := fun y _ => y * b ∈ Msub) ?_ ?_ ?_ ?_ ha
          · rintro _ ⟨α, rfl⟩
            -- mon α * b ∈ Msub by induction on Finset.univ
            have hprod : ∀ (T : Finset (Fin s)) (y : A), y ∈ Msub →
                (∏ i ∈ T, x i ^ (α i : ℕ)) * y ∈ Msub := by
              intro T
              induction T using Finset.cons_induction with
              | empty => intro y hy; simpa using hy
              | cons i T hi ih =>
                intro y hy
                rw [Finset.prod_cons, mul_assoc]
                have hpow : ∀ (e : ℕ) (z : A), z ∈ Msub → x i ^ e * z ∈ Msub := by
                  intro e
                  induction e with
                  | zero => intro z hz; simpa using hz
                  | succ e ihe =>
                    intro z hz
                    rw [pow_succ', mul_assoc]
                    exact hmul_x i _ (ihe z hz)
                exact hpow (α i : ℕ) _ (ih y hy)
            exact hprod Finset.univ b hb
          · simp
          · intro y z _ _ hy hz; rw [add_mul]; exact add_mem hy hz
          · intro c y _ hy
            change ((c : A) * y) * b ∈ Msub
            rw [mul_assoc]
            exact Submodule.smul_mem Msub c hy
        -- Msub contains k • 1 and x i for all i
        have hmem_k : ∀ c : k, algebraMap k A c ∈ Msub := fun c => by
          have : algebraMap k A c = (algebraMap k S c) • (1 : A) := by
            change algebraMap k A c = algebraMap k A c * 1
            rw [mul_one]
          rw [this]
          exact Submodule.smul_mem Msub _ hone
        have hmem_x : ∀ i : Fin s, x i ∈ Msub := fun i => by
          simpa using hmul_x i 1 hone
        -- Every y ∈ 𝔪 lies in Msub + 𝔪^2
        have hstep1 : ∀ y ∈ 𝔪, ∃ u ∈ Msub, ∃ w ∈ 𝔪 ^ 2, y = u + w := by
          intro y hy
          let q : Q := Submodule.Quotient.mk ⟨y, hy⟩
          have hq : q = ∑ i : Fin s, (bQ.repr q i) • bQ i := (bQ.sum_repr q).symm
          let u : A := ∑ i : Fin s, (bQ.repr q i) • x i
          have hu : u ∈ Msub := by
            refine sum_mem fun i _ => ?_
            rw [Algebra.smul_def]
            exact hmul _ (hmem_k _) _ (hmem_x i)
          have hw : y - u ∈ 𝔪 ^ 2 := by
            have hu𝔪 : u ∈ 𝔪 := sum_mem fun i _ => by
              rw [Algebra.smul_def]; exact Ideal.mul_mem_left 𝔪 _ (v i).2
            have hdiff : Submodule.Quotient.mk (p := W.comap V.subtype)
                ⟨y - u, sub_mem hy hu𝔪⟩ = 0 := by
              have hmk_u : Submodule.Quotient.mk (p := W.comap V.subtype)
                  ⟨u, hu𝔪⟩ = q := by
                rw [hq]
                have hsum : (⟨u, hu𝔪⟩ : V) = ∑ i : Fin s, (bQ.repr q i) • v i := by
                  ext; simp [u, x]
                change (W.comap V.subtype).mkQ ⟨u, hu𝔪⟩ = _
                rw [hsum, map_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [map_smul]
                exact congrArg ((bQ.repr q i) • ·) (hv i)
              have hsub : (⟨y - u, sub_mem hy hu𝔪⟩ : V) = ⟨y, hy⟩ - ⟨u, hu𝔪⟩ := by ext; rfl
              change (W.comap V.subtype).mkQ ⟨y - u, sub_mem hy hu𝔪⟩ = 0
              rw [hsub, map_sub]
              change q - Submodule.Quotient.mk (p := W.comap V.subtype) ⟨u, hu𝔪⟩ = 0
              rw [hmk_u, sub_self]
            rwa [Submodule.Quotient.mk_eq_zero] at hdiff
          exact ⟨u, hu, y - u, hw, by ring⟩
        -- By induction on t, 𝔪^t ⊆ Msub + 𝔪^(t+1)
        have hstep_t : ∀ t : ℕ, ∀ y ∈ 𝔪 ^ t, ∃ u ∈ Msub, ∃ w ∈ 𝔪 ^ (t + 1), y = u + w := by
          intro t
          induction t with
          | zero =>
            intro y _
            have hε : y - (Bialgebra.counitAlgHom k A y) • (1 : A) ∈ 𝔪 ^ 1 := by
              rw [pow_one]
              simp [𝔪, RingHom.mem_ker, Algebra.smul_def]
            refine ⟨(Bialgebra.counitAlgHom k A y) • (1 : A), ?_,
              y - (Bialgebra.counitAlgHom k A y) • (1 : A), hε, by ring⟩
            rw [Algebra.smul_def, mul_one]
            exact hmem_k _
          | succ t iht =>
            intro y hy
            rw [pow_succ] at hy
            refine Submodule.mul_induction_on hy ?_ ?_
            · intro a ha b hb
              obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := iht a ha
              obtain ⟨u₂, hu₂, w₂, hw₂, rfl⟩ := hstep1 b hb
              refine ⟨u₁ * u₂, hmul u₁ hu₁ u₂ hu₂,
                u₁ * w₂ + w₁ * u₂ + w₁ * w₂, ?_, by ring⟩
              have hu₁𝔪 : u₁ ∈ 𝔪 ^ t := by
                have hw₁' : w₁ ∈ 𝔪 ^ t := Ideal.pow_le_pow_right (Nat.le_succ t) hw₁
                have := sub_mem ha hw₁'
                simpa using this
              have hu₂𝔪 : u₂ ∈ 𝔪 := by
                have hw₂' : w₂ ∈ 𝔪 := Ideal.pow_le_self (by decide) hw₂
                have := sub_mem hb hw₂'
                simpa using this
              have h1 : u₁ * w₂ ∈ 𝔪 ^ (t + 2) := by
                rw [pow_add]; exact Ideal.mul_mem_mul hu₁𝔪 hw₂
              have h2 : w₁ * u₂ ∈ 𝔪 ^ (t + 2) := by
                rw [pow_succ]; exact Ideal.mul_mem_mul hw₁ hu₂𝔪
              have h3 : w₁ * w₂ ∈ 𝔪 ^ (t + 2) := by
                have : w₂ ∈ 𝔪 := Ideal.pow_le_self (by decide) hw₂
                rw [pow_succ]; exact Ideal.mul_mem_mul hw₁ this
              exact add_mem (add_mem h1 h2) h3
            · rintro a b ⟨u₁, hu₁, w₁, hw₁, ha⟩ ⟨u₂, hu₂, w₂, hw₂, hb⟩
              exact ⟨u₁ + u₂, add_mem hu₁ hu₂, w₁ + w₂, add_mem hw₁ hw₂, by rw [ha, hb]; ring⟩
        -- Descending induction from t = N to t = 0 shows 𝔪^t ⊆ Msub
        have hdesc : ∀ j : ℕ, j ≤ N → ∀ y ∈ 𝔪 ^ (N - j), y ∈ Msub := by
          intro j
          induction j with
          | zero =>
            intro _ y hy
            rw [Nat.sub_zero, hN, Ideal.mem_bot] at hy
            subst hy
            exact zero_mem _
          | succ j ihj =>
            intro hj y hy
            obtain ⟨u, hu, w, hw, rfl⟩ := hstep_t (N - (j + 1)) y hy
            have hsub : N - (j + 1) + 1 = N - j := by omega
            rw [hsub] at hw
            exact add_mem hu (ihj (Nat.le_of_succ_le hj) w hw)
        rw [eq_top_iff]
        intro y _
        have hy0 : y ∈ 𝔪 ^ (N - N) := by simp
        exact hdesc N (le_refl N) y hy0
      -- Combine linear independence + spanning to get an S-basis of A of size p^s
      let bSA : Module.Basis (Fin s → Fin p) S A := Module.Basis.mk hlinind (le_of_eq hspan.symm)
      let eFun : A ≃ₗ[k] ((Fin s → Fin p) → S) := bSA.equivFun.restrictScalars k
      have hmul_fin : Module.finrank k A = p ^ s * Module.finrank k S := by
        rw [eFun.finrank_eq, Module.finrank_pi_fintype]
        simp [Finset.sum_const, smul_eq_mul]
      refine ⟨s + r₀, ?_⟩
      rw [← hd, hmul_fin, hr₀, pow_add]

-- Regular representation τ_f on A ⊗[k] A for the kill shot
private noncomputable def regRep {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (f : A →ₐ[k] A) : (A ⊗[k] A) →ₗ[k] (A ⊗[k] A) :=
  (LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
    (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
    (LinearMap.rTensor A (LinearMap.lTensor A f.toLinearMap ∘ₗ Coalgebra.comul (R := k)))

private lemma regRep_tmul {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (f : A →ₐ[k] A) (a b : A) :
    regRep f (a ⊗ₜ[k] b) = ∑ i ∈ (ℛ k a).index, (ℛ k a).left i ⊗ₜ[k] (f ((ℛ k a).right i) * b) := by
  dsimp [regRep]
  rw [← (ℛ k a).eq, map_sum, TensorProduct.sum_tmul, map_sum, map_sum]
  simp

private lemma regRep_one {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A] :
    regRep ((1 : WithConv (A →ₐ[k] A)).ofConv) = LinearMap.id := by
  apply TensorProduct.ext'
  intro a b
  rw [LinearMap.id_apply, regRep_tmul]
  have h : ∑ i ∈ (ℛ k a).index,
      (ℛ k a).left i ⊗ₜ[k] ((1 : WithConv (A →ₐ[k] A)).ofConv ((ℛ k a).right i) * b) =
      (∑ i ∈ (ℛ k a).index, Coalgebra.counit (R := k) ((ℛ k a).right i) • (ℛ k a).left i) ⊗ₜ[k] b := by
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (ℛ k a).left i ⊗ₜ[k] (algebraMap k A (Coalgebra.counit (R := k) ((ℛ k a).right i)) * b) = _
    rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [h, sum_smul_counit (ℛ k a)]

private lemma regRep_mul {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (f₁ f₂ : WithConv (A →ₐ[k] A)) :
    regRep (f₁ * f₂).ofConv = (regRep f₁.ofConv) ∘ₗ (regRep f₂.ofConv) := by
  apply TensorProduct.ext'
  intro a b
  simp only [LinearMap.comp_apply]
  -- Prove using coassociativity at the LinearMap level
  have hco := Coalgebra.coassoc (R := k) (A := A)
  have hL : (regRep (f₁ * f₂).ofConv) (a ⊗ₜ[k] b) =
      ((LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A (LinearMap.mul' k A) ∘ₗ
          LinearMap.lTensor A (TensorProduct.map f₁.ofConv.toLinearMap f₂.ofConv.toLinearMap) ∘ₗ
          (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
          LinearMap.rTensor A (Coalgebra.comul (R := k)) ∘ₗ
          Coalgebra.comul (R := k)))) (a ⊗ₜ[k] b) := by
    have h1 : LinearMap.lTensor A (f₁ * f₂).ofConv.toLinearMap ∘ₗ Coalgebra.comul (R := k) =
        LinearMap.lTensor A (LinearMap.mul' k A) ∘ₗ
          LinearMap.lTensor A (TensorProduct.map f₁.ofConv.toLinearMap f₂.ofConv.toLinearMap) ∘ₗ
          (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
          LinearMap.rTensor A (Coalgebra.comul (R := k)) ∘ₗ
          Coalgebra.comul (R := k) := by
      calc LinearMap.lTensor A (f₁ * f₂).ofConv.toLinearMap ∘ₗ Coalgebra.comul (R := k)
          = LinearMap.lTensor A (LinearMap.mul' k A ∘ₗ
              TensorProduct.map f₁.ofConv.toLinearMap f₂.ofConv.toLinearMap ∘ₗ
              Coalgebra.comul (R := k)) ∘ₗ Coalgebra.comul (R := k) := rfl
        _ = LinearMap.lTensor A (LinearMap.mul' k A) ∘ₗ
              LinearMap.lTensor A (TensorProduct.map f₁.ofConv.toLinearMap f₂.ofConv.toLinearMap) ∘ₗ
              LinearMap.lTensor A (Coalgebra.comul (R := k)) ∘ₗ Coalgebra.comul (R := k) := by
            simp [LinearMap.lTensor_comp, LinearMap.comp_assoc]
        _ = _ := by
            congr 1; congr 1
            exact hco.symm
    dsimp [regRep]
    have h1a := LinearMap.congr_fun h1 a
    simp only [LinearMap.comp_apply] at h1a
    rw [h1a]
    rfl
  rw [hL]
  -- Now compare both sides as linear maps applied to (rTensor comul (comul a)) ⊗ₜ b
  have hR : regRep f₁.ofConv (regRep f₂.ofConv (a ⊗ₜ[k] b)) =
      ((LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A f₁.ofConv.toLinearMap ∘ₗ Coalgebra.comul (R := k))) ∘ₗ
        (LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A f₂.ofConv.toLinearMap ∘ₗ Coalgebra.comul (R := k))))
      (a ⊗ₜ[k] b) := rfl
  rw [hR]
  -- Pull comul through lTensor (mul') and assoc
  have hstep : ∀ (x y z : A),
      ((LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A (LinearMap.mul' k A) ∘ₗ
          LinearMap.lTensor A (TensorProduct.map f₁.ofConv.toLinearMap f₂.ofConv.toLinearMap) ∘ₗ
          (TensorProduct.assoc k A A A).toLinearMap))) (((x ⊗ₜ[k] y) ⊗ₜ[k] z) ⊗ₜ[k] b) =
      ((LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A f₁.ofConv.toLinearMap)))
        ((x ⊗ₜ[k] y) ⊗ₜ[k] (f₂.ofConv z * b)) := by
    intro x y z
    simp [mul_assoc]
  -- Apply to (rTensor comul (comul a))
  have hLHS : ∀ t : (A ⊗[k] A) ⊗[k] A,
      ((LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A (LinearMap.mul' k A) ∘ₗ
          LinearMap.lTensor A (TensorProduct.map f₁.ofConv.toLinearMap f₂.ofConv.toLinearMap) ∘ₗ
          (TensorProduct.assoc k A A A).toLinearMap))) (t ⊗ₜ[k] b) =
      ((LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A f₁.ofConv.toLinearMap)) ∘ₗ
        (LinearMap.lTensor (A ⊗[k] A) (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k (A ⊗[k] A) A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor (A ⊗[k] A) f₂.ofConv.toLinearMap))) (t ⊗ₜ[k] b) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul xy z =>
      induction xy using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => exact hstep x y z
      | add xy₁ xy₂ ih₁ ih₂ => simp [TensorProduct.add_tmul, map_add, ih₁, ih₂]
    | add t₁ t₂ ih₁ ih₂ => simp [TensorProduct.add_tmul, map_add, ih₁, ih₂]
  have h1 := hLHS (LinearMap.rTensor A (Coalgebra.comul (R := k)) (Coalgebra.comul (R := k) a))
  have h2 : ∀ u : A ⊗[k] A,
      ((LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A f₁.ofConv.toLinearMap)) ∘ₗ
        (LinearMap.lTensor (A ⊗[k] A) (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k (A ⊗[k] A) A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor (A ⊗[k] A) f₂.ofConv.toLinearMap)))
        ((LinearMap.rTensor A (Coalgebra.comul (R := k)) u) ⊗ₜ[k] b) =
      ((LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A f₁.ofConv.toLinearMap ∘ₗ Coalgebra.comul (R := k))) ∘ₗ
        (LinearMap.lTensor A (LinearMap.mul' k A)) ∘ₗ
        (TensorProduct.assoc k A A A).toLinearMap ∘ₗ
        (LinearMap.rTensor A (LinearMap.lTensor A f₂.ofConv.toLinearMap))) (u ⊗ₜ[k] b) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul x z =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.rTensor_tmul,
        LinearMap.lTensor_tmul, TensorProduct.assoc_tmul, LinearMap.mul'_apply]
    | add u₁ u₂ ih₁ ih₂ => simp [TensorProduct.add_tmul, map_add, ih₁, ih₂]
  simpa only [LinearMap.comp_apply, LinearMap.rTensor_tmul] using h1.trans (h2 (Coalgebra.comul (R := k) a))

private lemma regRep_pow {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (f : WithConv (A →ₐ[k] A)) (t : ℕ) :
    regRep (f ^ t).ofConv = (regRep f.ofConv) ^ t := by
  induction t with
  | zero => exact regRep_one
  | succ t ih =>
    rw [pow_succ, regRep_mul, ih, pow_succ]
    rfl

private lemma regRep_sub_id_pow_mem {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (h : A →ₐ[k] A) (I : Ideal A)
    (hh : ∀ x ∈ RingHom.ker (Bialgebra.counitAlgHom k A), h x ∈ I) :
    ∀ (t : ℕ) (z : A ⊗[k] A),
      (((regRep h - LinearMap.id : Module.End k (A ⊗[k] A)) ^ t)) z ∈
        LinearMap.range (LinearMap.lTensor A ((I ^ t).restrictScalars k).subtype) := by
  intro t
  induction t with
  | zero =>
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact zero_mem _
    | tmul a b =>
      refine ⟨a ⊗ₜ[k] ⟨b, by simp⟩, rfl⟩
    | add z₁ z₂ ih₁ ih₂ => exact add_mem ih₁ ih₂
  | succ t iht =>
    intro z
    rw [pow_succ' (regRep h - LinearMap.id : Module.End k (A ⊗[k] A)) t, Module.End.mul_apply]
    obtain ⟨w, hw⟩ := iht z
    rw [← hw]
    clear hw
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [LinearMap.lTensor_tmul, Submodule.coe_subtype, LinearMap.sub_apply,
        LinearMap.id_apply, regRep_tmul]
      have hdiff : ∑ i ∈ (ℛ k a).index, (ℛ k a).left i ⊗ₜ[k] (h ((ℛ k a).right i) * (b : A)) -
          a ⊗ₜ[k] (b : A) =
          ∑ i ∈ (ℛ k a).index, (ℛ k a).left i ⊗ₜ[k]
            (h ((ℛ k a).right i - algebraMap k A (Coalgebra.counit (R := k) ((ℛ k a).right i))) * (b : A)) := by
        have ha : a ⊗ₜ[k] (b : A) =
            ∑ i ∈ (ℛ k a).index, (ℛ k a).left i ⊗ₜ[k]
              (algebraMap k A (Coalgebra.counit (R := k) ((ℛ k a).right i)) * (b : A)) := by
          conv_lhs => rw [← sum_smul_counit (ℛ k a)]
          rw [TensorProduct.sum_tmul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        rw [ha, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← TensorProduct.tmul_sub, ← sub_mul, map_sub, AlgHom.commutes]
      rw [hdiff]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hker : (ℛ k a).right i - algebraMap k A (Coalgebra.counit (R := k) ((ℛ k a).right i)) ∈
          RingHom.ker (Bialgebra.counitAlgHom k A) := by
        simp [RingHom.mem_ker]
      have hmem : h ((ℛ k a).right i - algebraMap k A (Coalgebra.counit (R := k) ((ℛ k a).right i))) *
          (b : A) ∈ I ^ (t + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hh _ hker) b.2
      exact ⟨(ℛ k a).left i ⊗ₜ[k] ⟨_, hmem⟩, rfl⟩
    | add w₁ w₂ ih₁ ih₂ => rw [map_add, map_add]; exact add_mem ih₁ ih₂

private lemma eq_one_of_regRep_eq_id {k A : Type*} [CommRing k] [CommRing A] [HopfAlgebra k A]
    (f : WithConv (A →ₐ[k] A)) (hf : regRep f.ofConv = LinearMap.id) : f = 1 := by
  refine WithConv.ext (AlgHom.ext fun a => ?_)
  have h1 := LinearMap.congr_fun hf (a ⊗ₜ[k] (1 : A))
  rw [regRep_tmul, LinearMap.id_apply] at h1
  let proj : (A ⊗[k] A) →ₗ[k] A :=
    (TensorProduct.lid k A).toLinearMap ∘ₗ LinearMap.rTensor A (Coalgebra.counit (R := k))
  have h2 := congrArg proj h1
  simp only [proj, LinearMap.comp_apply, map_sum, LinearMap.rTensor_tmul, mul_one,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul] at h2
  have h3 : ∑ i ∈ (ℛ k a).index,
      Coalgebra.counit (R := k) ((ℛ k a).left i) • f.ofConv ((ℛ k a).right i) =
      f.ofConv (∑ i ∈ (ℛ k a).index,
        Coalgebra.counit (R := k) ((ℛ k a).left i) • (ℛ k a).right i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => by rw [map_smul]
  rw [h3, Coalgebra.sum_counit_smul (ℛ k a)] at h2
  simpa [AlgHom.convOne_def, Algebra.smul_def] using h2

-- Main proof over an algebraically closed field
private lemma killed_by_rank_algClosed (n : ℕ+) (k : Type*) [Field k] [IsAlgClosed k]
    (A : Type*) [CommRing A] [HopfAlgebra k A] [Module.Finite k A]
    (hn : Module.finrank k A = (n : ℕ)) :
    IsKilledBy k A n := by
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : Nontrivial A := Module.nontrivial_of_finrank_pos (R := k) (M := A) (by rw [hn]; exact n.pos)
  -- Bijection between G = WithConv (A →ₐ[k] k) and MaximalSpectrum A
  let toMax : WithConv (A →ₐ[k] k) → MaximalSpectrum A := fun g =>
    ⟨RingHom.ker g.ofConv, RingHom.ker_isMaximal_of_surjective g.ofConv
      (fun c => ⟨algebraMap k A c, by simp⟩)⟩
  have htoMax_bij : Function.Bijective toMax := by
    constructor
    · intro g₁ g₂ h
      have hker : RingHom.ker g₁.ofConv = RingHom.ker g₂.ofConv := congrArg MaximalSpectrum.asIdeal h
      obtain ⟨g, _, huniq⟩ := algHom_of_maximal (k := k) (toMax g₂)
      exact WithConv.ext ((huniq g₁.ofConv hker).trans (huniq g₂.ofConv rfl).symm)
    · intro M
      obtain ⟨g, hg, _⟩ := algHom_of_maximal (k := k) M
      exact ⟨toConv g, MaximalSpectrum.ext hg⟩
  let eG : WithConv (A →ₐ[k] k) ≃ MaximalSpectrum A := Equiv.ofBijective toMax htoMax_bij
  have : Fintype (MaximalSpectrum A) := Fintype.ofFinite (MaximalSpectrum A)
  let : Fintype (WithConv (A →ₐ[k] k)) := Fintype.ofEquiv (MaximalSpectrum A) eG.symm
  let d := Fintype.card (WithConv (A →ₐ[k] k))
  -- Nilradical is nilpotent
  obtain ⟨N₀, hN₀⟩ := IsArtinianRing.isNilpotent_nilradical (R := A)
  let N := max N₀ 1
  have hN : nilradical A ^ N = ⊥ :=
    le_antisymm ((Ideal.pow_le_pow_right (le_max_left N₀ 1)).trans (le_of_eq hN₀)) bot_le
  have hNpos : 1 ≤ N := le_max_right N₀ 1
  -- Artinian product decomposition A ≃ₐ[k] ∀ M : MaximalSpectrum A, A ⧸ M.asIdeal ^ N
  let eProdA : A ≃ₐ[A] ∀ M : MaximalSpectrum A, A ⧸ M.asIdeal ^ N :=
    (AlgEquiv.quotientBot A A).symm.trans <|
      (Ideal.quotientEquivAlgOfEq A hN.symm).trans
        (IsArtinianRing.quotNilradicalPowEquivPi A N)
  let eProd : A ≃ₐ[k] ∀ M : MaximalSpectrum A, A ⧸ M.asIdeal ^ N :=
    { eProdA with
      commutes' := fun c => by
        ext M
        exact congrFun (eProdA.commutes (algebraMap k A c)) M }
  -- Local factor at ker(counit)
  let I₀ : Ideal A := RingHom.ker (Bialgebra.counitAlgHom k A)
  let M₀ : MaximalSpectrum A := toMax 1
  have hM₀ : M₀.asIdeal = I₀ := rfl
  let A₁ := A ⧸ I₀ ^ N
  -- Every factor A ⧸ M.asIdeal ^ N is k-algebra isomorphic to A₁ via leftTrans
  have hfactor : ∀ M : MaximalSpectrum A, Nonempty ((A ⧸ M.asIdeal ^ N) ≃ₐ[k] A₁) := by
    intro M
    let g := eG.symm M
    have hg : M.asIdeal = RingHom.ker g.ofConv := by
      have : toMax g = M := eG.apply_symm_apply M
      rw [← this]
    let φ : A ≃ₐ[k] A := leftTransEquiv g
    have hcomap : Ideal.comap φ.toRingHom I₀ = M.asIdeal := by
      rw [hg]
      ext x
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgEquiv.coe_ringHom_commutes,
        I₀, AlgHom.coe_toRingHom, φ, leftTransEquiv, AlgEquiv.ofAlgHom_apply]
      have h := DFunLike.congr_fun (counit_comp_leftTrans g) x
      simpa using Iff.of_eq (congrArg (· = 0) h)
    have hmap : I₀ ^ N = Ideal.map φ.toRingHom (M.asIdeal ^ N) := by
      rw [Ideal.map_pow, ← hcomap, Ideal.map_comap_of_surjective φ.toRingHom φ.surjective I₀]
    exact ⟨Ideal.quotientEquivAlg (M.asIdeal ^ N) (I₀ ^ N) φ hmap⟩
  -- Compute finrank k A = d * finrank k A₁
  let m := Module.finrank k A₁
  have hfin_eq : (n : ℕ) = d * m := by
    rw [← hn, eProd.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    have hconst : ∀ M : MaximalSpectrum A, Module.finrank k (A ⧸ M.asIdeal ^ N) = m := fun M =>
      (hfactor M).some.toLinearEquiv.finrank_eq
    simp_rw [hconst, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    dsimp [d]
    rw [Fintype.card_congr eG]
  -- Show nilradical A ^ m = ⊥
  have hI₀_nil : (Ideal.map (Ideal.Quotient.mk (I₀ ^ N)) I₀) ^ m = ⊥ := by
    set J := Ideal.map (Ideal.Quotient.mk (I₀ ^ N)) I₀
    have hJN : J ^ N = ⊥ := by
      rw [← Ideal.map_pow]
      ext x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      constructor
      · intro h
        have hle : Ideal.map (Ideal.Quotient.mk (I₀ ^ N)) (I₀ ^ N) = ⊥ := by
          rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
        rw [hle, Ideal.mem_bot] at h
        exact Ideal.Quotient.eq_zero_iff_mem.mp h
      · intro h
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr h]
        exact zero_mem _
    have : Module.Finite k A₁ := Module.Finite.of_surjective
      (Ideal.Quotient.mkₐ k (I₀ ^ N)).toLinearMap Ideal.Quotient.mk_surjective
    -- Show by induction on t that either J^t = ⊥ or finrank k (J^t) + t ≤ m - 1 (for t ≥ 1)
    -- Simpler: finrank k (J^1) < m, and if J^t ≠ ⊥ then finrank k (J^(t+1)) < finrank k (J^t)
    have hJ1_lt : Module.finrank k (J.restrictScalars k) < m := by
      apply Submodule.finrank_lt (s := J.restrictScalars k)
      intro htop
      have h1J : (1 : A₁) ∈ J := by
        have : (1 : A₁) ∈ J.restrictScalars k := by rw [htop]; trivial
        exact this
      have h1I : (1 : A) ∈ I₀ := by
        have hmap : Ideal.comap (Ideal.Quotient.mk (I₀ ^ N)) J = I₀ := by
          rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
            ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
          exact sup_eq_left.mpr (Ideal.pow_le_self (by omega))
        rw [← hmap]
        exact h1J
      have h10 : (1 : k) = 0 := by
        simp [I₀, RingHom.mem_ker] at h1I
      exact one_ne_zero h10
    have hstep : ∀ t : ℕ, J ^ t ≠ ⊥ → J ^ (t + 1) < J ^ t := by
      intro t ht
      refine lt_of_le_of_ne (Ideal.pow_le_pow_right (Nat.le_succ t)) fun heq => ht ?_
      have hconst : ∀ r : ℕ, J ^ (t + r) = J ^ t := by
        intro r
        induction r with
        | zero => rfl
        | succ r ihr => rw [← Nat.add_assoc, pow_succ, ihr, ← pow_succ, heq]
      have hle : J ^ (t + N) ≤ J ^ N := Ideal.pow_le_pow_right (Nat.le_add_left N t)
      rw [hconst N, hJN] at hle
      exact le_antisymm hle bot_le
    have hbound : ∀ t : ℕ, 1 ≤ t → J ^ t = ⊥ ∨ Module.finrank k ((J ^ t).restrictScalars k) + t ≤ m := by
      intro t ht
      induction t with
      | zero => omega
      | succ t ih =>
        rcases eq_or_ne t 0 with rfl | ht0
        · right
          have h01 : J ^ (0 + 1) = J := by rw [Nat.zero_add, pow_one]
          rw [h01]
          omega
        · rcases ih (Nat.pos_of_ne_zero ht0) with hbot | hfin
          · left
            exact le_antisymm ((Ideal.pow_le_pow_right (Nat.le_succ t)).trans (le_of_eq hbot)) bot_le
          · by_cases hbot' : J ^ t = ⊥
            · left
              exact le_antisymm ((Ideal.pow_le_pow_right (Nat.le_succ t)).trans (le_of_eq hbot')) bot_le
            · right
              have hlt : Module.finrank k ((J ^ (t + 1)).restrictScalars k) <
                  Module.finrank k ((J ^ t).restrictScalars k) :=
                Submodule.finrank_lt_finrank_of_lt (hstep t hbot')
              omega
    have hmpos : 1 ≤ m := by
      have hn0 : 0 < (n : ℕ) := n.pos
      rw [hfin_eq] at hn0
      exact Nat.pos_of_mul_pos_left hn0
    rcases hbound m hmpos with hbot | hfin
    · exact hbot
    · have h0 : Module.finrank k ((J ^ m).restrictScalars k) = 0 := by omega
      have hbot : (J ^ m).restrictScalars k = ⊥ := Submodule.finrank_eq_zero.mp h0
      exact Ideal.ext fun x => by
        change x ∈ (J ^ m).restrictScalars k ↔ x ∈ (⊥ : Submodule k A₁)
        rw [hbot]
  have hnil_m : nilradical A ^ m = ⊥ := by
    rw [IsArtinianRing.nilradical_pow_eq_iInf]
    ext a
    simp only [Ideal.mem_iInf, Ideal.mem_bot]
    constructor
    · intro ha
      apply eProd.injective
      ext M
      rw [map_zero, Pi.zero_apply]
      let eM : (A ⧸ M.asIdeal ^ N) ≃ₐ[k] A₁ := (hfactor M).some
      -- Show eProd a M ∈ (M.asIdeal / M.asIdeal^N)^m = ⊥
      have hM_nil : (Ideal.map (Ideal.Quotient.mk (M.asIdeal ^ N)) M.asIdeal) ^ m = ⊥ := by
        -- Transport via eM: the maximal ideal of A ⧸ M^N maps to the maximal ideal of A₁
        have hmap : Ideal.map eM.toRingHom (Ideal.map (Ideal.Quotient.mk (M.asIdeal ^ N)) M.asIdeal) =
            Ideal.map (Ideal.Quotient.mk (I₀ ^ N)) I₀ := by
          -- Both are the unique maximal ideal (nilradical) of their local rings!
          have h1 : Ideal.map (Ideal.Quotient.mk (M.asIdeal ^ N)) M.asIdeal =
              nilradical (A ⧸ M.asIdeal ^ N) := by
            ext x
            obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
            rw [mem_nilradical]
            constructor
            · intro hy
              rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy
              rcases hy with ⟨z, hz, hzy⟩
              refine ⟨N, ?_⟩
              rw [← hzy, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
              exact Ideal.pow_mem_pow hz N
            · rintro ⟨r, hr⟩
              rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hr
              have hyM : y ∈ M.asIdeal := by
                have hle : M.asIdeal ^ N ≤ M.asIdeal := Ideal.pow_le_self (by omega)
                exact M.isMaximal.isPrime.mem_of_pow_mem r (hle hr)
              exact Ideal.mem_map_of_mem _ hyM
          have h2 : Ideal.map (Ideal.Quotient.mk (I₀ ^ N)) I₀ = nilradical A₁ := by
            ext x
            obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
            rw [mem_nilradical]
            constructor
            · intro hy
              rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy
              rcases hy with ⟨z, hz, hzy⟩
              refine ⟨N, ?_⟩
              rw [← hzy, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
              exact Ideal.pow_mem_pow hz N
            · rintro ⟨r, hr⟩
              rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hr
              have hyI : y ∈ I₀ := by
                have hle : I₀ ^ N ≤ I₀ := Ideal.pow_le_self (by omega)
                exact M₀.isMaximal.isPrime.mem_of_pow_mem r (hle hr)
              exact Ideal.mem_map_of_mem _ hyI
          rw [h1, h2]
          ext x
          obtain ⟨y, rfl⟩ := eM.surjective x
          have heM_surj : Function.Surjective eM.toRingHom := eM.surjective
          simp only [Ideal.mem_map_iff_of_surjective _ heM_surj, mem_nilradical]
          constructor
          · rintro ⟨z, ⟨r, hr⟩, hzy⟩
            have : z = y := eM.injective hzy
            subst this
            exact ⟨r, by rw [← map_pow, hr, map_zero]⟩
          · rintro ⟨r, hr⟩
            refine ⟨y, ⟨r, ?_⟩, rfl⟩
            apply eM.injective
            rw [map_pow, map_zero]
            exact hr
        have hpow : Ideal.map eM.toRingHom
            ((Ideal.map (Ideal.Quotient.mk (M.asIdeal ^ N)) M.asIdeal) ^ m) = ⊥ := by
          rw [Ideal.map_pow, hmap, hI₀_nil]
        ext x
        simp only [Ideal.mem_bot]
        constructor
        · intro hx
          have : eM x ∈ (⊥ : Ideal A₁) := by rw [← hpow]; exact Ideal.mem_map_of_mem _ hx
          rw [Ideal.mem_bot] at this
          exact eM.injective (this.trans (map_zero eM).symm)
        · intro hx; subst hx; exact zero_mem _
      have hmem : eProd a M ∈ (Ideal.map (Ideal.Quotient.mk (M.asIdeal ^ N)) M.asIdeal) ^ m := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ (ha M)
      rwa [hM_nil, Ideal.mem_bot] at hmem
    · intro ha; subst ha; intro M; exact zero_mem _
  -- Show I₀ ^ N is a Hopf ideal, so A₁ = A ⧸ I₀ ^ N is a local Hopf algebra!
  have hI₀N_idem : I₀ ^ N = I₀ ^ (2 * N) := by
    classical
    apply le_antisymm _ (Ideal.pow_le_pow_right (by omega))
    -- Use idempotent e₁ corresponding to M₀ in eProd
    let e₁ : A := eProd.symm (fun M => if M = M₀ then 1 else 0)
    have he₁_idem : (1 - e₁) * (1 - e₁) = 1 - e₁ := by
      apply eProd.injective
      ext M
      simp only [map_mul, map_sub, map_one, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, e₁,
        AlgEquiv.apply_symm_apply]
      split_ifs <;> simp
    have hmem_iff : ∀ x : A, x ∈ I₀ ^ N ↔ x = (1 - e₁) * x := by
      intro x
      constructor
      · intro hx
        apply eProd.injective
        ext M
        simp only [map_mul, map_sub, map_one, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, e₁,
          AlgEquiv.apply_symm_apply]
        by_cases hM : M = M₀
        · subst hM
          simp only [↓reduceIte, sub_self, zero_mul]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
        · simp [hM]
      · intro hx
        have hM0 := congrFun (congrArg eProd hx) M₀
        simp only [map_mul, map_sub, map_one, Pi.mul_apply, Pi.sub_apply, Pi.one_apply, e₁,
          AlgEquiv.apply_symm_apply, ↓reduceIte, sub_self, zero_mul] at hM0
        exact Ideal.Quotient.eq_zero_iff_mem.mp hM0
    intro x hx
    have hx1 : x = (1 - e₁) * x := (hmem_iff x).mp hx
    have h1e : 1 - e₁ ∈ I₀ ^ N := (hmem_iff (1 - e₁)).mpr he₁_idem.symm
    rw [two_mul, pow_add, hx1]
    exact Ideal.mul_mem_mul h1e hx
  have : ((I₀ ^ N).restrictScalars k).IsCoideal := by
    constructor
    · intro x hx
      have hle : I₀ ^ N ≤ I₀ := Ideal.pow_le_self (by omega)
      exact hle hx
    · intro x hx
      let q : A →ₐ[k] A₁ := Ideal.Quotient.mkₐ k (I₀ ^ N)
      let φ : A →ₐ[k] (A₁ ⊗[k] A₁) :=
        (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom k A)
      change φ x = 0
      let J := Ideal.map (Ideal.Quotient.mk (I₀ ^ N)) I₀
      have hJN : J ^ N = ⊥ := by
        rw [← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      let K₁ : Ideal (A₁ ⊗[k] A₁) := Ideal.map (Algebra.TensorProduct.includeLeft : A₁ →ₐ[k] A₁ ⊗[k] A₁) J
      let K₂ : Ideal (A₁ ⊗[k] A₁) := Ideal.map (Algebra.TensorProduct.includeRight : A₁ →ₐ[k] A₁ ⊗[k] A₁) J
      have hK₁ : K₁ ^ N = ⊥ := by rw [← Ideal.map_pow, hJN, Ideal.map_bot]
      have hK₂ : K₂ ^ N = ⊥ := by rw [← Ideal.map_pow, hJN, Ideal.map_bot]
      have hK12 : (K₁ ⊔ K₂) ^ (2 * N) = ⊥ := by
        have hle : (K₁ ⊔ K₂) ^ (2 * N) ≤ K₁ ^ N ⊔ K₂ ^ N :=
          ideal_sup_pow_le K₁ K₂ (2 * N) N N (by omega)
        rw [hK₁, hK₂, sup_bot_eq] at hle
        exact le_antisymm hle bot_le
      -- Show φ(I₀) ⊆ K₁ ⊔ K₂
      have hφI₀ : ∀ a ∈ I₀, φ a ∈ K₁ ⊔ K₂ := by
        intro a ha
        have hsplit : φ a = (φ a - 1 ⊗ₜ[k] q a) + 1 ⊗ₜ[k] q a := by ring
        rw [hsplit]
        refine Ideal.add_mem _ ?_ ?_
        · -- φ a - 1 ⊗ₜ q a ∈ K₁
          have h1 : φ a - 1 ⊗ₜ[k] q a =
              ∑ i ∈ (ℛ k a).index,
                (q ((ℛ k a).left i) - algebraMap k A₁ (Coalgebra.counit (R := k) ((ℛ k a).left i))) ⊗ₜ[k]
                  q ((ℛ k a).right i) := by
            dsimp [φ]
            rw [Bialgebra.comulAlgHom_apply, ← (ℛ k a).eq, map_sum]
            have ha' : (1 : A₁) ⊗ₜ[k] q a =
                ∑ i ∈ (ℛ k a).index,
                  algebraMap k A₁ (Coalgebra.counit (R := k) ((ℛ k a).left i)) ⊗ₜ[k]
                    q ((ℛ k a).right i) := by
              conv_lhs => rw [← Coalgebra.sum_counit_smul (ℛ k a), map_sum, TensorProduct.tmul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
                Algebra.smul_def, mul_one]
            rw [ha', ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [TensorProduct.sub_tmul]
          rw [h1]
          refine Ideal.sum_mem _ fun i _ => ?_
          have hker : (ℛ k a).left i - algebraMap k A (Coalgebra.counit (R := k) ((ℛ k a).left i)) ∈ I₀ := by
            simp [I₀, RingHom.mem_ker]
          have hqker : q ((ℛ k a).left i) - algebraMap k A₁ (Coalgebra.counit (R := k) ((ℛ k a).left i)) ∈ J := by
            have : q ((ℛ k a).left i) - algebraMap k A₁ (Coalgebra.counit (R := k) ((ℛ k a).left i)) =
                Ideal.Quotient.mk (I₀ ^ N)
                  ((ℛ k a).left i - algebraMap k A (Coalgebra.counit (R := k) ((ℛ k a).left i))) := by
              rw [map_sub]; rfl
            rw [this]
            exact Ideal.mem_map_of_mem _ hker
          have hmul : (q ((ℛ k a).left i) - algebraMap k A₁ (Coalgebra.counit (R := k) ((ℛ k a).left i))) ⊗ₜ[k]
              q ((ℛ k a).right i) =
              ((q ((ℛ k a).left i) - algebraMap k A₁ (Coalgebra.counit (R := k) ((ℛ k a).left i))) ⊗ₜ[k] 1) *
              (1 ⊗ₜ[k] q ((ℛ k a).right i)) := by
            simp [Algebra.TensorProduct.tmul_mul_tmul]
          rw [hmul]
          exact Ideal.mem_sup_left (Ideal.mul_mem_right _ K₁ (Ideal.mem_map_of_mem _ hqker))
        · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha))
      have hx2N : x ∈ I₀ ^ (2 * N) := hI₀N_idem ▸ hx
      have hφx : φ x ∈ (K₁ ⊔ K₂) ^ (2 * N) := by
        have hle : Ideal.map φ.toRingHom I₀ ≤ K₁ ⊔ K₂ := by
          rw [Ideal.map_le_iff_le_comap]
          exact hφI₀
        have : φ x ∈ Ideal.map φ.toRingHom (I₀ ^ (2 * N)) := Ideal.mem_map_of_mem _ hx2N
        rw [Ideal.map_pow] at this
        exact ideal_pow_mono hle (2 * N) this
      rwa [hK12, Ideal.mem_bot] at hφx
  have : (I₀ ^ N).IsHopfIdeal k :=
    { antipode_mem := fun x hx => by
        have hle : Ideal.map (HopfAlgebra.antipodeAlgHom k A).toRingHom I₀ ≤ I₀ := by
          rw [Ideal.map_le_iff_le_comap]
          intro y hy
          simpa [I₀, RingHom.mem_ker] using hy
        have hmem : HopfAlgebra.antipodeAlgHom k A x ∈
            Ideal.map (HopfAlgebra.antipodeAlgHom k A).toRingHom (I₀ ^ N) :=
          Ideal.mem_map_of_mem _ hx
        rw [Ideal.map_pow] at hmem
        exact ideal_pow_mono hle N hmem }
  -- Now A₁ has a HopfAlgebra k A₁ instance!
  have : Module.Finite k A₁ := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ k (I₀ ^ N)).toLinearMap Ideal.Quotient.mk_surjective
  have hA₁_N : (RingHom.ker (Bialgebra.counitAlgHom k A₁)) ^ N = ⊥ := by
    have hker : RingHom.ker (Bialgebra.counitAlgHom k A₁) =
        Ideal.map (Ideal.Quotient.mk (I₀ ^ N)) I₀ := by
      ext x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [RingHom.mem_ker, AlgHom.coe_toRingHom,
        Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
      constructor
      · intro ha
        exact ⟨a, ha, rfl⟩
      · rintro ⟨b, hb, hba⟩
        have hdiff : b - a ∈ I₀ ^ N := Ideal.Quotient.eq.mp hba
        have hle : I₀ ^ N ≤ I₀ := Ideal.pow_le_self (by omega)
        have haI : a ∈ I₀ := by
          have := sub_mem hb (hle hdiff)
          simpa using this
        exact haI
    rw [hker, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  -- Define h = (toConv (AlgHom.id k A) ^ d).ofConv
  let h : A →ₐ[k] A := (toConv (AlgHom.id k A) ^ d).ofConv
  have hh_nil : ∀ x ∈ I₀, h x ∈ nilradical A := by
    intro x hx
    rw [IsArtinianRing.nilradical_eq_iInf, Ideal.mem_iInf]
    intro M
    let g := eG.symm M
    have hg : M.asIdeal = RingHom.ker g.ofConv := by
      have : toMax g = M := eG.apply_symm_apply M
      rw [← this]
    rw [hg, RingHom.mem_ker]
    have hcomp := DFunLike.congr_fun (comp_convPow g d) x
    simp only [AlgHom.comp_apply] at hcomp
    have hgd : g ^ d = 1 := pow_card_eq_one
    rw [hgd] at hcomp
    exact hcomp.trans hx
  -- Split by characteristic of k: CharZero vs CharP p (p prime)
  rcases CharP.exists k with ⟨p, hp⟩
  have : CharP k p := hp
  rcases eq_or_ne p 0 with rfl | hp0
  · -- Characteristic 0: m = 1, nilradical A = ⊥
    have : CharZero k := CharP.charP_to_charZero k
    have hker0 : RingHom.ker (Bialgebra.counitAlgHom k A₁) = ⊥ := local_hopf_charZero hA₁_N
    have hm1 : m = 1 := by
      have hinj : Function.Injective (Bialgebra.counitAlgHom k A₁) :=
        (RingHom.injective_iff_ker_eq_bot (Bialgebra.counitAlgHom k A₁).toRingHom).mpr hker0
      have hsurj : Function.Surjective (Bialgebra.counitAlgHom k A₁) :=
        fun c => ⟨algebraMap k A₁ c, by simp⟩
      exact (LinearEquiv.ofBijective (Bialgebra.counitAlgHom k A₁).toLinearMap
        ⟨hinj, hsurj⟩).finrank_eq.trans (Module.finrank_self k)
    rw [hm1, pow_one] at hnil_m
    rw [IsKilledBy, hfin_eq, hm1, mul_one]
    refine WithConv.ext (AlgHom.ext fun a => ?_)
    have hker : a - algebraMap k A (Coalgebra.counit (R := k) a) ∈ I₀ := by
      simp [I₀, RingHom.mem_ker]
    have h0 := hh_nil _ hker
    rw [hnil_m, Ideal.mem_bot, map_sub, AlgHom.commutes, sub_eq_zero] at h0
    exact h0
  · -- Characteristic p > 0: p is prime, m = p ^ r
    have hprime : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp0
    have : Fact p.Prime := ⟨hprime⟩
    obtain ⟨r, hr⟩ := local_hopf_charP_aux k p m A₁ rfl ⟨N, hA₁_N⟩
    have htau_nil : (regRep h - LinearMap.id : Module.End k (A ⊗[k] A)) ^ (p ^ r) = 0 := by
      apply LinearMap.ext
      intro z
      have hmem := regRep_sub_id_pow_mem h (nilradical A) hh_nil (p ^ r) z
      rw [← hr, hnil_m] at hmem
      obtain ⟨w, hw⟩ := hmem
      rw [← hr, ← hw]
      clear hw
      induction w using TensorProduct.induction_on with
      | zero => exact map_zero _
      | tmul a b =>
        have hb : (b : A) = 0 := Ideal.mem_bot.mp b.2
        change a ⊗ₜ[k] (b : A) = (0 : Module.End k (A ⊗[k] A)) z
        rw [hb, TensorProduct.tmul_zero]
        rfl
      | add w₁ w₂ ih₁ ih₂ => rw [map_add, ih₁, ih₂]; simp
    have : CharP (Module.End k (A ⊗[k] A)) p :=
      charP_of_injective_algebraMap (algebraMap k (Module.End k (A ⊗[k] A))).injective p
    have htau_pow : (regRep h) ^ (p ^ r) = LinearMap.id := by
      have heq : regRep h = (1 : Module.End k (A ⊗[k] A)) + (regRep h - LinearMap.id) := by
        change regRep h = LinearMap.id + (regRep h - LinearMap.id)
        abel
      rw [heq, add_pow_char_pow_of_commute p r (Commute.one_left _), one_pow, htau_nil, add_zero]
      rfl
    rw [IsKilledBy, hfin_eq, pow_mul]
    apply eq_one_of_regRep_eq_id
    rw [regRep_pow]
    change (regRep h) ^ m = LinearMap.id
    rw [hr]
    exact htau_pow

private lemma killed_by_rank_field (n : ℕ+) (k : Type*) [Field k] (A : Type*) [CommRing A]
    [HopfAlgebra k A] [Module.Finite k A] (hn : Module.finrank k A = (n : ℕ)) :
    IsKilledBy k A n := by
  let K := AlgebraicClosure k
  have hfin : Module.finrank K (K ⊗[k] A) = (n : ℕ) := by
    let b := Module.finBasis k A
    rw [Module.finrank_eq_card_basis (b.baseChange K), Fintype.card_fin, hn]
  exact isKilledBy_of_baseChange (K := K) (killed_by_rank_algClosed n K (K ⊗[k] A) hfin)

end FieldProof

end FiniteLocallyFreeGroupSchemeExponent

theorem OMA.solution :
    type_of% @FiniteLocallyFreeGroupSchemeExponent.killed_by_rank.variants.field :=
  FiniteLocallyFreeGroupSchemeExponent.killed_by_rank_field
