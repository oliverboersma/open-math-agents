import FormalConjectures.Other.GerstenhaberThreeMatrices
import Mathlib

-- The Gerstenhaber problem for three commuting matrices.
--
-- The mathematics below is NOT the work of the submitter. It is a port of the proof
-- published by Yan-cheng Lin:
--   Source: https://github.com/lin522026298/three-commuting-matrices
--   Commit: 54c3e27589c55fa18f8679ef01b1e30feb2a9915 (registered in the Palomar registry)
--   Paper: Yan-cheng Lin, A Solution to the Gerstenhaber Problem for Three Commuting
--   Matrices, https://doi.org/10.5281/zenodo.24346423
-- Licence of the source (double quotes of the original text written as single quotes,
-- because this site forbids the double-quote character):
--
--   MIT License
--   Copyright (c) 2026 Yan-cheng Lin
--   Permission is hereby granted, free of charge, to any person obtaining a copy of this
--   software and associated documentation files (the 'Software'), to deal in the Software
--   without restriction, including without limitation the rights to use, copy, modify,
--   merge, publish, distribute, sublicense, and/or sell copies of the Software, and to
--   permit persons to whom the Software is furnished to do so, subject to the following
--   conditions: The above copyright notice and this permission notice shall be included in
--   all copies or substantial portions of the Software.
--   THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
--   INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
--   PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE
--   FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
--   OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
--   DEALINGS IN THE SOFTWARE.
--
-- Changes made for this site (one file of at most 512 KiB, Lean 4.33.1 with its Mathlib,
-- restricted syntax): the modules reachable from the source's Solution.lean are concatenated
-- in dependency order with each module's sections closed; comments, blank lines and
-- theorems the final theorem does not depend on are removed to fit the size limit; file-level
-- options are attached to the declarations they covered; attribute commands that made
-- structure fields instances are replaced by instance declarations; a few lemma names of
-- the newer Mathlib are replaced by their names here, with four small helper lemmas at the
-- top and a handful of proof steps rewritten for the older Lean. Only those adaptations and
-- the final theorem OMA.solution (the body of the source's Solution.lean) are new.

universe u
theorem PowerSeries.nat_le_order_iff {R : Type*} [Semiring R] {φ : PowerSeries R} {n : ℕ} :
    (n : ℕ∞) ≤ φ.order ↔ ∀ i < n, PowerSeries.coeff i φ = 0 :=
  ⟨fun h i hi => PowerSeries.coeff_of_lt_order i (lt_of_lt_of_le (by exact_mod_cast hi) h),
    PowerSeries.nat_le_order φ n⟩
theorem OMAGerst.finiteType_adjoin_singleton {A B : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] (x : B) : Algebra.FiniteType A (Algebra.adjoin A ({x} : Set B)) :=
  ⟨(Subalgebra.fg_top _).mpr ⟨{x}, by simp⟩⟩
theorem Submodule.le_of_le_smul_of_le_jacobson {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ Ring.jacobson R) (hNN : N' ≤ N ⊔ I • N') : N' ≤ N :=
  Submodule.le_of_le_smul_of_le_jacobson_bot hN' (hIJ.trans Ideal.jacobson_bot.ge) hNN
theorem Submodule.eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {I : Ideal R} {N N' : Submodule R M} (hN : N.FG)
    (hIjac : I ≤ Ring.jacobson R)
    (hmaple : Submodule.map (I • N).mkQ N = Submodule.map (I • N).mkQ N') : N = N' :=
  Submodule.eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot hN
    (hIjac.trans Ideal.jacobson_bot.ge) hmaple
noncomputable section
open scoped TensorProduct
namespace G3Scalar
open Module
variable (k : Type*) (L : Type*) [Field k] [Field L] [Algebra k L]
variable {n : ℕ}
abbrev extendMatrix : Matrix (Fin n) (Fin n) k →ₐ[k] Matrix (Fin n) (Fin n) L :=
  (Algebra.ofId k L).mapMatrix
variable (A : Subalgebra k (Matrix (Fin n) (Fin n) k))
def tensorActor : L ⊗[k] A →ₐ[L] Matrix (Fin n) (Fin n) L :=
  AlgHom.liftEquiv k L _ _ ((extendMatrix k L).comp A.val)
@[simp] theorem tensorActor_tmul (a : L) (M : A) :
    tensorActor k L A (a ⊗ₜ[k] M) = a • extendMatrix k L M := rfl
theorem tensorActor_injective : Function.Injective (tensorActor k L A) := by
  let f := A.val.toLinearMap.lTensor L
  have h (z : L ⊗[k] A) :
      tensorActor k L A z = (matrixEquivTensor (Fin n) k L).symm (f z) := by
    induction z with
    | zero => simp
    | tmul a m => rfl
    | add a b ha hb => simpa only [map_add] using congrArg₂ (·+·) ha hb
  intro x y hxy
  rw [h,h] at hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap A.val.toLinearMap Subtype.val_injective
    ((matrixEquivTensor (Fin n) k L).symm.injective hxy)
variable (S : Set (Matrix (Fin n) (Fin n) k))
theorem tensorActor_range :
    (tensorActor k L (Algebra.adjoin k S)).range =
      Algebra.adjoin L (extendMatrix k L '' S) := by
  let B := Algebra.adjoin L (extendMatrix k L '' S)
  have hA : Algebra.adjoin k S ≤ (B.restrictScalars k).comap (extendMatrix k L) := by
    apply Algebra.adjoin_le
    intro x hx
    exact Algebra.subset_adjoin ⟨x,hx,rfl⟩
  apply le_antisymm
  · rintro x ⟨z,rfl⟩
    induction z with
    | zero => rw [map_zero]; exact B.zero_mem
    | tmul a m => exact B.smul_mem (hA m.property) a
    | add x y hx hy => rw [map_add]; exact B.add_mem hx hy
  · apply Algebra.adjoin_le
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨1 ⊗ₜ[k] ⟨s, Algebra.subset_adjoin hs⟩, by simp⟩
def adjoinTensorEquiv :
    L ⊗[k] (Algebra.adjoin k S) ≃ₐ[L] Algebra.adjoin L (extendMatrix k L '' S) :=
  (AlgEquiv.ofInjective (tensorActor k L _) (tensorActor_injective k L _)).trans
    (Subalgebra.equivOfEq _ _ (tensorActor_range k L S))
@[simp] theorem adjoinTensorEquiv_tmul (a : L) (s : Algebra.adjoin k S) :
    (adjoinTensorEquiv k L S (a ⊗ₜ[k] s) : Matrix (Fin n) (Fin n) L) =
      a • extendMatrix k L s := rfl
theorem finrank_adjoin_map :
    finrank k (Algebra.adjoin k S) = finrank L (Algebra.adjoin L (extendMatrix k L '' S)) := by
  rw [← Module.finrank_baseChange (R := L) (S := k)]
  exact (adjoinTensorEquiv k L S).toLinearEquiv.finrank_eq
end G3Scalar
end
noncomputable section
namespace G3Scalar
open Module
theorem finrank_family_map {k L : Type*} [Field k] [Field L] (f : k →+* L)
    {n : ℕ} {ι : Type*} (A : ι → Matrix (Fin n) (Fin n) k) :
    finrank k (Algebra.adjoin k (Set.range A)) =
      finrank L (Algebra.adjoin L (Set.range fun i => f.mapMatrix (A i))) := by
  let := f.toAlgebra
  have h := finrank_adjoin_map k L (Set.range A)
  rw [← Set.range_comp] at h
  exact h
def ClosedFieldBound : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) k),
    (∀ i j, Commute (A i) (A j)) → finrank k (Algebra.adjoin k (Set.range A)) ≤ n
theorem field_small_of_closed (bound : ClosedFieldBound) (k : Type) [Field k] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank k (Algebra.adjoin k (Set.range A)) ≤ n := by
  let f := algebraMap k (AlgebraicClosure k)
  rw [finrank_family_map f A]
  exact bound _ n _ fun i j => (hc i j).map f.mapMatrix
private inductive Expr (ι : Type) where
  | atom (i : ι) | zero | one
  | add (a b : Expr ι) | mul (a b : Expr ι)
  | neg (a : Expr ι) | inv (a : Expr ι)
private def Expr.eval {ι : Type} {K : Type*} [Field K] (c : ι → K) : Expr ι → K
  | .atom i => c i | .zero => 0 | .one => 1
  | .add a b => a.eval c + b.eval c | .mul a b => a.eval c * b.eval c
  | .neg a => -a.eval c | .inv a => (a.eval c)⁻¹
private def coefficients {ι : Type} {K : Type*} [Field K] (c : ι → K) : Subfield K where
  carrier := Set.range (Expr.eval c)
  zero_mem' := ⟨.zero,rfl⟩
  one_mem' := ⟨.one,rfl⟩
  add_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨.add a b,rfl⟩
  mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨.mul a b,rfl⟩
  neg_mem' := by rintro _ ⟨a,rfl⟩; exact ⟨.neg a,rfl⟩
  inv_mem' := by rintro _ ⟨a,rfl⟩; exact ⟨.inv a,rfl⟩
theorem field_triple_bound_of_closed (bound : ClosedFieldBound) (K : Type*) [Field K] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) K) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank K (Algebra.adjoin K (Set.range A)) ≤ n := by
  let c : Fin 3 × Fin n × Fin n → K := fun p => A p.1 p.2.1 p.2.2
  let E := coefficients c
  let : Small.{0} E := inferInstanceAs (Small.{0} (Set.range (Expr.eval c)))
  let e : Shrink.{0} E ≃+* E := Shrink.ringEquiv E
  let f : Shrink.{0} E →+* K := E.subtype.comp e.toRingHom
  let B : Fin 3 → Matrix (Fin n) (Fin n) (Shrink.{0} E) :=
    fun s i j => e.symm ⟨A s i j, Expr.atom (s,i,j), rfl⟩
  have mapped (i : Fin 3) : f.mapMatrix (B i) = A i := by
    ext x y
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hinj : Function.Injective (f.mapMatrix (m := Fin n)) := by
    intro M N h
    apply Matrix.ext
    intro i j
    exact f.injective (congrFun (congrFun h i) j)
  have comm (i j : Fin 3) : Commute (B i) (B j) := by
    apply hinj
    simpa only [map_mul,mapped] using (hc i j).eq
  have hdim := finrank_family_map f B
  have eqf : (fun i => f.mapMatrix (B i)) = A := funext mapped
  rw [eqf] at hdim
  rw [← hdim]
  exact field_small_of_closed bound _ n B comm
end G3Scalar
end
noncomputable section
namespace GKDivisor
open scoped nonZeroDivisors
theorem exists_heightOne_containing {R : Type*} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (q : R) (hq : q ≠ 0) (hn : ¬ IsUnit q) :
    ∃ P : Ideal R, P.IsPrime ∧ q ∈ P ∧ P.height = 1 := by
  let I := Ideal.span ({q} : Set R)
  obtain ⟨P, hP⟩ := I.nonempty_minimalPrimes (by simpa [I] using hn)
  haveI hp : P.IsPrime := hP.isPrime
  have hone : I.height = 1 := Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hq) hn
  refine ⟨P, hp, hP.1.2 (Ideal.subset_span (by simp)), le_antisymm ?_ ?_⟩
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I P hP
  · rw [← hone]; exact Ideal.height_mono hP.1.2
theorem atPrime_isDVR {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  let L := Localization.AtPrime P
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  haveI : IsIntegrallyClosed L :=
    isIntegrallyClosed_of_isLocalization L P.primeCompl P.primeCompl_le_nonZeroDivisors
  haveI : Ring.KrullDimLE 1 L := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P L, hP]; simp)
  haveI : Ring.DimensionLEOne L := ⟨fun h hpr => hpr.isMaximal_of_ne_bot h⟩
  haveI : IsDedekindDomain L := {}
  exact ((IsDiscreteValuationRing.TFAE L
    (IsLocalization.AtPrime.not_isField R (Ideal.ne_bot_of_height_eq_one hP) L)).out 0 2).mpr
      (inferInstance : IsDedekindDomain L)
theorem nonunit_divisor {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (q : R) (hq : q ≠ 0) (hn : ¬ IsUnit q) :
    ∃ P : Ideal R, ∃ hp : P.IsPrime, q ∈ P ∧ P.height = 1 ∧
      IsDiscreteValuationRing (@Localization.AtPrime R _ P hp) := by
  obtain ⟨P,hp,hqP,hheight⟩ := exists_heightOne_containing q hq hn
  exact ⟨P,hp,hqP,hheight,atPrime_isDVR P hheight⟩
end GKDivisor
end
namespace GKDivisor
theorem finite_iterateFrobenius (k R : Type*) [Field k] [PerfectField k]
    [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (p : ℕ) [ExpChar k p] [ExpChar R p] (e : ℕ) :
    (iterateFrobenius R p e).Finite := by
  apply RingHom.finite_iff_isIntegral_and_finiteType.mpr
  constructor
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C _ (expChar_pow_pos R p e).ne', ?_⟩
    simp [Polynomial.eval₂_sub, iterateFrobenius_def]
  · apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k R)
    have h : (iterateFrobenius R p e).comp (algebraMap k R) =
        (algebraMap k R).comp (iterateFrobenius k p e) := by
      ext x
      simp [RingHom.comp_apply, iterateFrobenius_def]
    rw [h]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (RingHom.FiniteType.of_surjective _ (iterateFrobeniusEquiv k p e).surjective)
end GKDivisor
noncomputable section
namespace GKDivisor
open scoped nonZeroDivisors
set_option maxHeartbeats 1600000 in
private theorem finite_left_of_injective {A B C : Type*}
    [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
    (f : A →+* B) (g : B →+* C) (hg : Function.Injective g)
    (h : (g.comp f).Finite) : f.Finite := by
  algebraize [f, g, g.comp f]
  exact Module.Finite.of_injective ((Algebra.linearMap B C).restrictScalars A) hg
set_option maxHeartbeats 1600000 in
private theorem finite_integralClosure_over_polynomial (k S K L : Type*)
    [Field k] [PerfectField k] [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [IsNoetherianRing S] [Algebra k S] [Algebra.FiniteType k S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L]
    [Algebra S L] [Algebra K L] [IsScalarTower S K L] [FiniteDimensional K L] :
    Module.Finite S (integralClosure S L) := by
  let T := separableClosure K L
  letI : Algebra S T := ((algebraMap K T).comp (algebraMap S K)).toAlgebra
  haveI : IsScalarTower S K T := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S T L := IsScalarTower.of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply S K L x
  haveI : FiniteDimensional K T := inferInstanceAs (FiniteDimensional K (separableClosure K L))
  haveI : Algebra.IsSeparable K T := inferInstanceAs (Algebra.IsSeparable K (separableClosure K L))
  haveI : IsPurelyInseparable T L := inferInstanceAs (IsPurelyInseparable (separableClosure K L) L)
  haveI : FiniteDimensional T L := Module.Finite.of_restrictScalars_finite K T L
  let D := integralClosure S L
  let C := integralClosure S T
  haveI : Module.Finite S C := IsIntegralClosure.finite S K T C
  obtain ⟨p, hp⟩ := ExpChar.exists k
  haveI : ExpChar S p := expChar_of_injective_algebraMap (algebraMap k S).injective p
  haveI : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective S K) p
  haveI : ExpChar T p := expChar_of_injective_algebraMap (algebraMap K T).injective p
  haveI : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  let e := IsPurelyInseparable.exponent T L
  have hpow (x : L) : x ^ p ^ e ∈ T := by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' T p x
    rw [← hy]
    exact y.property
  let ψ : L →+* T := (iterateFrobenius L p e).codRestrict T.toSubfield.toSubring hpow
  let g : D →+* C := (ψ.comp D.val.toRingHom).codRestrict C.toSubring fun x ↦ by
    change IsIntegral S (ψ x.val)
    apply (isIntegral_algebraMap_iff (B := L) (algebraMap T L).injective).mp
    exact x.property.pow _
  have heq : g.comp (algebraMap S D) = (algebraMap S C).comp (iterateFrobenius S p e) := by
    ext x
    change (algebraMap S L x) ^ p ^ e = algebraMap T L (algebraMap S T (x ^ p ^ e))
    rw [← IsScalarTower.algebraMap_apply, map_pow]
  have hg : Function.Injective g := by
    intro a b h
    exact Subtype.ext (ψ.injective (congrArg Subtype.val h))
  apply (RingHom.finite_algebraMap).mp
  apply finite_left_of_injective _ g hg
  rw [heq]
  exact (RingHom.finite_algebraMap.mpr inferInstance).comp (finite_iterateFrobenius k S p e)
set_option maxHeartbeats 1600000 in
theorem finite_affine_normalization (k R : Type*) [Field k] [PerfectField k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R] :
    Module.Finite R (integralClosure R (FractionRing R)) := by
  obtain ⟨n, f, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let S := MvPolynomial (Fin n) k
  let K := FractionRing S
  let L := FractionRing R
  let B := integralClosure R L
  letI : Algebra S R := f.toRingHom.toAlgebra
  haveI : FaithfulSMul S R := (faithfulSMul_iff_algebraMap_injective S R).mpr hinj
  haveI : Module.Finite S R := hfin
  haveI : IsScalarTower S R L := inferInstance
  haveI : FaithfulSMul S L := inferInstance
  letI : Algebra K L := FractionRing.liftAlgebra S L
  haveI : IsScalarTower S K L := FractionRing.isScalarTower_liftAlgebra S L
  haveI : FiniteDimensional K L := Module.Finite.of_isLocalization S R S⁰
  letI : Algebra S B := ((algebraMap R B).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower S R B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower S B L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.IsIntegral S B := Algebra.IsIntegral.trans R
  haveI : IsIntegrallyClosedIn B L := IsIntegrallyClosedIn.of_isIntegralClosure R
  haveI : IsIntegralClosure B S L := IsIntegralClosure.of_isIntegrallyClosedIn
  haveI : Module.Finite S (integralClosure S L) := finite_integralClosure_over_polynomial k S K L
  haveI : Module.Finite S B := Module.Finite.equiv
    (IsIntegralClosure.equiv S (integralClosure S L) L B).toLinearEquiv
  exact Module.Finite.of_restrictScalars_finite S R B
set_option maxHeartbeats 1600000 in
theorem affine_nonunit_divisor (k R : Type*) [Field k] [PerfectField k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (q : R) (hq : q ≠ 0) (hn : ¬ IsUnit q) :
    let N := integralClosure R (FractionRing R)
    ∃ P : Ideal N, ∃ hp : P.IsPrime, algebraMap R N q ∈ P ∧ P.height = 1 ∧
      IsDiscreteValuationRing (@Localization.AtPrime N _ P hp) := by
  let N := integralClosure R (FractionRing R)
  haveI : Module.Finite R N := finite_affine_normalization k R
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  haveI : IsNoetherianRing N := IsNoetherianRing.of_finite R N
  haveI : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R)
  have hI : Function.Injective (algebraMap R N) := fun a b h =>
    IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)
  haveI : FaithfulSMul R N := (faithfulSMul_iff_algebraMap_injective R N).mpr hI
  apply nonunit_divisor (algebraMap R N q) ((map_ne_zero_iff _ hI).mpr hq)
  exact fun h => hn (isUnit_of_map_unit (algebraMap R N) q h)
end GKDivisor
end
noncomputable section
namespace GKDivisor
open Polynomial Ideal
set_option maxHeartbeats 150000 in
theorem trdeg_integral_inj {k S A : Type u} [Field k] [CommRing S] [CommRing A]
    [IsDomain A] [Nontrivial S] [Algebra k S] [Algebra k A]
    (f : S →ₐ[k] A) (hi : Function.Injective f) (hI : f.IsIntegral) :
    Algebra.trdeg k A = Algebra.trdeg k S := by
  letI : Algebra S A := f.toRingHom.toAlgebra
  haveI : FaithfulSMul S A := (faithfulSMul_iff_algebraMap_injective S A).mpr hi
  haveI : IsScalarTower k S A := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : Algebra.IsIntegral S A := ⟨hI⟩
  rw [← trdeg_add_eq k S (A := A), trdeg_eq_zero (R := S) (A := A), add_zero]
set_option maxHeartbeats 150000 in
private theorem transport_exists_inj {k S B C : Type u} [Field k] [CommRing S]
    [CommRing B] [CommRing C] [Algebra k S] [Algebra k B] [Algebra k C]
    (g : S →ₐ[k] B) (hg : Function.Injective g) (hgm : g.IsIntegral)
    (e : B ≃ₐ[k] C) :
    ∃ h : S →ₐ[k] C, Function.Injective h ∧ h.IsIntegral := by
  refine ⟨e.toAlgHom.comp g, e.injective.comp hg, ?_⟩
  exact hgm.trans g.toRingHom e.toRingEquiv.toRingHom
    (RingHom.isIntegral_of_surjective _ e.surjective)
set_option maxHeartbeats 150000 in
private theorem univariate_hypersurface {k S : Type u} [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] (F : S[X]) (hLC : IsUnit F.leadingCoeff) (hn : ¬IsUnit F) :
    ∃ h : S →ₐ[k] (S[X] ⧸ Ideal.span {F}), Function.Injective h ∧ h.IsIntegral := by
  have hF : F.degree ≠ 0 := by
    intro he
    have eq := Polynomial.eq_C_of_degree_eq_zero he
    have hh : IsUnit (F.coeff 0) := by simpa [Polynomial.leadingCoeff, Polynomial.natDegree, he] using hLC
    exact hn (by rw [eq]; exact hh.map Polynomial.C)
  let J := Ideal.span ({F} : Set S[X])
  let g := ((Ideal.Quotient.mkₐ S J).comp (Algebra.ofId S S[X])).restrictScalars k
  have hgi : Function.Injective g := AdjoinRoot.of.injective_of_degree_ne_zero hF
  have hgm : g.IsIntegral := (Polynomial.monic_of_isUnit_leadingCoeff_inv_smul hLC).quotient_isIntegral <|
    Submodule.smul_of_tower_mem _ _ (Ideal.subset_span (Set.mem_singleton F))
  exact ⟨g,hgi,hgm⟩
open private T T_leadingcoeff_isUnit from Mathlib.RingTheory.NoetherNormalization
set_option maxHeartbeats 150000 in
private noncomputable def nChange {k : Type u} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n+1)) k) :
    MvPolynomial (Fin (n+1)) k ≃ₐ[k] (MvPolynomial (Fin n) k)[X] :=
  (T f).trans (MvPolynomial.finSuccEquiv k n)
set_option maxHeartbeats 150000 in
private noncomputable def nQuot {k : Type u} [Field k] {n : ℕ} (f : MvPolynomial (Fin (n+1)) k) :
    (MvPolynomial (Fin (n+1)) k ⧸ Ideal.span {f}) ≃ₐ[k]
      ((MvPolynomial (Fin n) k)[X] ⧸ Ideal.span {nChange f f}) :=
  Ideal.quotientEquivAlg (R₁ := k) (Ideal.span {f}) (Ideal.span {nChange f f}) (nChange f)
    (by rw [Ideal.map_span,Set.image_singleton]; rfl)
set_option maxHeartbeats 150000 in
theorem hypersurface_integral_inj {k : Type u} [Field k] {n : ℕ}
    (f : MvPolynomial (Fin (n+1)) k) (hf : f ≠ 0) (hn : ¬ IsUnit f) :
    ∃ g : MvPolynomial (Fin n) k →ₐ[k]
      (MvPolynomial (Fin (n+1)) k ⧸ Ideal.span {f}), Function.Injective g ∧ g.IsIntegral := by
  have hLC : IsUnit (nChange f f).leadingCoeff := T_leadingcoeff_isUnit f hf
  have hnu : ¬ IsUnit (nChange f f) := fun h => hn (by simpa using h.map (nChange f).symm)
  obtain ⟨g, hi, hm⟩ := univariate_hypersurface (k := k) (nChange f f) hLC hnu
  exact transport_exists_inj g hi hm (nQuot f).symm
end GKDivisor
end
noncomputable section
namespace GKDivisor
theorem heightOne_under {S R : Type*} [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [IsNoetherianRing S] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Algebra S R] [FaithfulSMul S R] [Algebra.IsIntegral S R]
    (P : Ideal R) [P.IsPrime] (h : P.height = 1) : (P.under S).height = 1 := by
  have hn := P.under_ne_bot S (Ideal.ne_bot_of_height_eq_one h)
  apply le_antisymm
  · rw [← h, Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under S) P]
    exact le_self_add
  · exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hn)
end GKDivisor
end
noncomputable section
namespace GKDivisor
open Ideal
set_option maxHeartbeats 350000 in
theorem poly_trdeg (k : Type u) [Field k] (n : ℕ) :
    Algebra.trdeg k (MvPolynomial (Fin n) k) = n := by
  simp [MvPolynomial.trdeg_of_isDomain]
set_option maxHeartbeats 350000 in
theorem trdeg_polynomial_divisor {k : Type u} [Field k] {n : ℕ}
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] (hp : p.height = 1) :
    Algebra.trdeg k (MvPolynomial (Fin n) k ⧸ p) + 1 = n := by
  cases n with
  | zero =>
    obtain ⟨z,hz,hn⟩ := p.ne_bot_iff.mp (Ideal.ne_bot_of_height_eq_one hp)
    let e := MvPolynomial.isEmptyAlgEquiv k (Fin 0)
    have hu : IsUnit (e z) := isUnit_iff_ne_zero.mpr ((map_ne_zero_iff e e.injective).mpr hn)
    have hu' : IsUnit z := by simpa using hu.map e.symm
    exact False.elim ((Ideal.IsPrime.ne_top (I := p) inferInstance) (p.eq_top_of_isUnit_mem hz hu'))
  | succ n =>
    haveI : p.IsPrincipal := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp
    obtain ⟨f,hgen⟩ := Submodule.IsPrincipal.principal (S := p)
    change p = Ideal.span {f} at hgen
    have hne : f ≠ 0 := by
      intro e; apply Ideal.ne_bot_of_height_eq_one hp
      simpa [e] using hgen
    have hnu : ¬ IsUnit f := by
      intro h; apply Ideal.IsPrime.ne_top (I := p) inferInstance
      exact hgen.trans (Ideal.span_singleton_eq_top.mpr h)
    haveI hprime : (Ideal.span {f}).IsPrime := hgen ▸ ‹p.IsPrime›
    obtain ⟨g,hi,hm⟩ := hypersurface_integral_inj f hne hnu
    have ht := trdeg_integral_inj g hi hm
    rw [hgen, ht, poly_trdeg]; simp
set_option maxHeartbeats 350000 in
theorem affine_heightOne_dimension (k R : Type u) [Field k] [CommRing R] [IsDomain R]
    [Algebra k R] [Algebra.FiniteType k R] (P : Ideal R) [P.IsPrime] (hP : P.height = 1) :
    Algebra.trdeg k (R ⧸ P) + 1 = Algebra.trdeg k R := by
  obtain ⟨n,f,hi,hf⟩ := exists_finite_inj_algHom_of_fg k R
  let S := MvPolynomial (Fin n) k
  letI : Algebra S R := f.toRingHom.toAlgebra
  haveI : FaithfulSMul S R := (faithfulSMul_iff_algebraMap_injective S R).mpr hi
  haveI : Module.Finite S R := hf
  haveI : IsScalarTower k S R := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let p := P.under S
  have hp : p.height = 1 := heightOne_under P hP
  have hQ : Algebra.trdeg k (R ⧸ P) = Algebra.trdeg k (S ⧸ p) :=
    trdeg_integral_inj (IsScalarTower.toAlgHom k (S ⧸ p) (R ⧸ P))
      (FaithfulSMul.algebraMap_injective _ _)
      (algebraMap_isIntegral_iff.mpr inferInstance)
  rw [hQ,trdeg_polynomial_divisor p hp,trdeg_integral_inj f hi (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral S R)),poly_trdeg]
end GKDivisor
end
noncomputable section
namespace GKDivisor
theorem trdeg_residueField (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (P : Ideal R) [P.IsPrime] :
    Algebra.trdeg k P.ResidueField = Algebra.trdeg k (R ⧸ P) := by
  haveI : Algebra.IsAlgebraic (R ⧸ P) P.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (R ⧸ P))
  rw [← trdeg_add_eq k (R ⧸ P) (A := P.ResidueField), trdeg_eq_zero_iff.mpr this, add_zero]
abbrev Norm (R : Type*) [CommRing R] := integralClosure R (FractionRing R)
theorem affine_pole_residue (k R : Type u) [Field k] [PerfectField k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.FiniteType k R]
    (q : R) (hq : q ≠ 0) (hn : ¬ IsUnit q) :
    ∃ P : Ideal (Norm R), ∃ hp : P.IsPrime, algebraMap R (Norm R) q ∈ P ∧ P.height = 1 ∧
      IsDiscreteValuationRing (@Localization.AtPrime (Norm R) _ P hp) ∧
      Algebra.trdeg k (@Ideal.ResidueField (Norm R) _ P hp) + 1 = Algebra.trdeg k R := by
  obtain ⟨P,hp,hm,hheight,hdvr⟩ := affine_nonunit_divisor k R q hq hn
  haveI : P.IsPrime := hp
  haveI : Module.Finite R (Norm R) := finite_affine_normalization k R
  haveI : Algebra.FiniteType k (Norm R) := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k R) (inferInstance : Algebra.FiniteType R (Norm R))
  have hN : Algebra.trdeg k (Norm R) = Algebra.trdeg k R :=
    trdeg_integral_inj (IsScalarTower.toAlgHom k R (Norm R))
      (fun a b e => IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val e))
      (algebraMap_isIntegral_iff.mpr inferInstance)
  refine ⟨P,hp,hm,hheight,hdvr,?_⟩
  rw [trdeg_residueField, affine_heightOne_dimension k (Norm R) P hheight,hN]
end GKDivisor
end
noncomputable section
namespace GKGraph
open Matrix
variable (k : Type*) [Field k] (r : ℕ)
abbrev FreeVars (r : ℕ) := Fin 3 × Fin r × Fin r
abbrev AllVars (r : ℕ) := Fin 6 × Fin r × Fin r
abbrev Poly := MvPolynomial (FreeVars r) k
abbrev K := FractionRing (Poly k r)
abbrev Mat (R : Type*) (r : ℕ) := Matrix (Fin r) (Fin r) R
def base (i : Fin 3) : Mat (Poly k r) r :=
  fun a b => MvPolynomial.X (i,a,b)
def delta : Poly k r := (base k r 0).det
theorem delta_ne_zero : delta k r ≠ 0 := by
  let ev := MvPolynomial.eval (R := k) (fun z : FreeVars r => (1 : Mat k r) z.2.1 z.2.2)
  have he : ev.mapMatrix (base k r 0) = 1 := by
    ext i j
    simp [ev, base, RingHom.mapMatrix_apply, Matrix.map_apply]
  intro hz
  have h := ev.map_det (base k r 0)
  rw [← delta, hz, map_zero, he, det_one] at h
  exact zero_ne_one h
def generic (i : Fin 3) : Mat (K k r) r :=
  (algebraMap (Poly k r) (K k r)).mapMatrix (base k r i)
abbrev P := generic k r 0
abbrev Y := generic k r 1
abbrev Z := generic k r 2
def comm (a b : Mat (K k r) r) := a*b-b*a
def rightY := (P k r)⁻¹ * Y k r * P k r
def rightZ := (P k r)⁻¹ * Z k r * P k r
def defect := (P k r)⁻¹ * (comm k r (Y k r) (Z k r))
theorem p_isUnit : IsUnit (P k r).det := by
  change IsUnit (((algebraMap (Poly k r) (K k r)).mapMatrix (base k r 0)).det)
  rw [← RingHom.map_det, isUnit_iff_ne_zero]
  exact fun h => delta_ne_zero k r ((IsFractionRing.to_map_eq_zero_iff).mp h)
theorem graph_intertwine_Y : P k r * rightY k r = Y k r * P k r := by
  simp only [rightY, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (p_isUnit k r), one_mul]
theorem graph_intertwine_Z : P k r * rightZ k r = Z k r * P k r := by
  simp only [rightZ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (p_isUnit k r), one_mul]
theorem graph_comm_left : comm k r (Y k r) (Z k r) = P k r * defect k r := by
  simp only [defect, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (p_isUnit k r), one_mul]
def six : Fin 6 → Mat (K k r) r :=
  ![P k r, Y k r, Z k r, rightY k r, rightZ k r, defect k r]
def coord (x : AllVars r) : K k r := six k r x.1 x.2.1 x.2.2
def ring : Subalgebra k (K k r) := Algebra.adjoin k (Set.range (coord k r))
theorem coord_mem (x : AllVars r) : coord k r x ∈ ring k r :=
  Algebra.subset_adjoin (Set.mem_range_self _)
def gcoord (x : AllVars r) : ring k r := ⟨coord k r x, coord_mem k r x⟩
def gmat (i : Fin 6) : Mat (ring k r) r := fun a b => gcoord k r (i,a,b)
theorem coe_gmat (i : Fin 6) : (ring k r).val.mapMatrix (gmat k r i) = six k r i := rfl
theorem generators : Algebra.adjoin k (Set.range (gcoord k r)) = ⊤ := by
  apply Subalgebra.map_injective (f := (ring k r).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top]
  exact (Subalgebra.range_val _).symm
instance : Algebra.FiniteType k (ring k r) := by
  classical
  exact ⟨⟨Finset.univ.image (gcoord k r), by simpa using generators k r⟩⟩
end GKGraph
end
noncomputable section
namespace GKGraph
open Matrix IsLocalization
variable (k : Type*) [Field k] (r : ℕ)
def fromPoly : Poly k r →ₐ[k] ring k r :=
  MvPolynomial.aeval (fun z : FreeVars r => gcoord k r (z.1.castLE (by decide),z.2))
theorem fromPoly_val (x : Poly k r) : (fromPoly k r x : K k r) = algebraMap _ _ x := by
  have e : (ring k r).val.comp (fromPoly k r) = IsScalarTower.toAlgHom k (Poly k r) (K k r) := by
    apply MvPolynomial.algHom_ext
    intro a
    obtain ⟨i,u,v⟩ := a
    fin_cases i <;> simp [fromPoly, gcoord, coord, six, generic, base, RingHom.mapMatrix_apply,
      Matrix.map_apply]
  exact DFunLike.congr_fun e x
instance graphFraction : IsFractionRing (ring k r) (K k r) := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨x,y,_,e⟩ := IsFractionRing.div_surjective (Poly k r) z
  exact ⟨fromPoly k r x, fromPoly k r y, by change z = (fromPoly k r x : K k r) / (fromPoly k r y : K k r); rw [fromPoly_val, fromPoly_val]; exact e.symm⟩
def gdelta := fromPoly k r (delta k r)
abbrev openRing := Localization.subalgebra.ofField (K k r) (Submonoid.powers (delta k r))
  (powers_le_nonZeroDivisors_of_noZeroDivisors (delta_ne_zero k r))
abbrev openBase (b : Fin 3) : Mat (openRing k r) r :=
  (algebraMap (Poly k r) (openRing k r)).mapMatrix (base k r b)
theorem openUnit : IsUnit (openBase k r 0).det := by
  rw [openBase, ← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (delta k r)
abbrev openVal := (openRing k r).val.toRingHom
theorem openBase_val (i : Fin 3) : (openVal k r).mapMatrix (openBase k r i) = generic k r i := rfl
theorem openInv_val : (openVal k r).mapMatrix (openBase k r 0)⁻¹ = (P k r)⁻¹ := by
  apply left_inv_eq_right_inv (a := P k r)
  · change _ * (openVal k r).mapMatrix (openBase k r 0) = 1
    rw [← map_mul, Matrix.nonsing_inv_mul _ (openUnit k r), map_one]
  · exact Matrix.mul_nonsing_inv _ (p_isUnit k r)
def openSix : Fin 6 → Mat (openRing k r) r :=
  let p := openBase k r 0
  let y := openBase k r 1
  let z := openBase k r 2
  ![p,y,z,p⁻¹*y*p,p⁻¹*z*p,p⁻¹*(y*z-z*y)]
theorem openSix_val (b : Fin 6) :
    (openVal k r).mapMatrix (openSix k r b) = six k r b := by
  fin_cases b
  · rfl
  · rfl
  · rfl
  · change (openVal k r).mapMatrix ((openBase k r 0)⁻¹ * openBase k r 1 * openBase k r 0) = _
    rw [map_mul, map_mul, openInv_val]; rfl
  · change (openVal k r).mapMatrix ((openBase k r 0)⁻¹ * openBase k r 2 * openBase k r 0) = _
    rw [map_mul, map_mul, openInv_val]; rfl
  · change (openVal k r).mapMatrix ((openBase k r 0)⁻¹ * _) = _
    rw [map_mul, openInv_val, map_sub, map_mul, map_mul]; rfl
theorem incl_open : ring k r ≤ (openRing k r).restrictScalars k := by
  apply Algebra.adjoin_le
  rintro x ⟨b,rfl⟩
  have e := congrFun (congrFun (openSix_val k r b.1) b.2.1) b.2.2
  change six k r b.1 b.2.1 b.2.2 ∈ openRing k r
  rw [← e]
  exact (openSix k r b.1 b.2.1 b.2.2).property
def toOpen : ring k r →ₐ[k] openRing k r := Subalgebra.inclusion (incl_open k r)
instance graphOpenAlg : Algebra (ring k r) (openRing k r) := (toOpen k r).toRingHom.toAlgebra
theorem toOpen_fromPoly (x : Poly k r) :
    toOpen k r (fromPoly k r x) = algebraMap _ (openRing k r) x :=
  Subtype.ext (fromPoly_val k r x)
theorem algebraMap_graphOpen (x : ring k r) :
    algebraMap _ (openRing k r) x = toOpen k r x := rfl
instance openGraph : IsLocalization.Away (gdelta k r) (openRing k r) := by
  apply IsLocalization.Away.mk
  · rw [algebraMap_graphOpen, gdelta, toOpen_fromPoly]
    exact IsLocalization.Away.algebraMap_isUnit _
  · intro s
    obtain ⟨n,a,h⟩ := IsLocalization.Away.surj (delta k r) s
    exact ⟨n, fromPoly k r a, by simpa only [algebraMap_graphOpen, gdelta, toOpen_fromPoly] using h⟩
  · intro a b h
    have eqab : a = b := Subtype.ext (congrArg (fun x : openRing k r => (x : K k r)) h)
    subst b; exact ⟨0,rfl⟩
end GKGraph
end
noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
theorem field_trdeg : Algebra.trdeg k (K k r) = (3*r*r : ℕ) := by
  have := IsLocalization.isAlgebraic (K k r) (nonZeroDivisors (Poly k r))
  rw [← trdeg_add_eq k (Poly k r) (A := K k r),
    trdeg_eq_zero_iff.2 this, add_zero, MvPolynomial.trdeg_of_isDomain]
  simp [FreeVars, mul_assoc]
theorem ring_trdeg : Algebra.trdeg k (ring k r) = (3*r*r : ℕ) := by
  have := IsLocalization.isAlgebraic (K k r) (nonZeroDivisors (ring k r))
  have h := trdeg_add_eq k (ring k r) (A := K k r)
  rw [trdeg_eq_zero_iff.2 this, add_zero, field_trdeg] at h
  exact h
private theorem mat_inj : Function.Injective (fun a : Mat (ring k r) r => (ring k r).val.mapMatrix a) := by
  intro a b h
  ext i j
  exact congrFun (congrFun h i) j
theorem ring_Y : gmat k r 0 * gmat k r 3 = gmat k r 1 * gmat k r 0 := by
  apply mat_inj k r
  simp only [map_mul, coe_gmat]
  exact graph_intertwine_Y k r
theorem ring_Z : gmat k r 0 * gmat k r 4 = gmat k r 2 * gmat k r 0 := by
  apply mat_inj k r
  simp only [map_mul, coe_gmat]
  exact graph_intertwine_Z k r
theorem ring_comm_left :
    gmat k r 1 * gmat k r 2 - gmat k r 2 * gmat k r 1 = gmat k r 0 * gmat k r 5 := by
  apply mat_inj k r
  simp only [map_sub, map_mul, coe_gmat]
  exact graph_comm_left k r
theorem det_gmat : (gmat k r 0).det = gdelta k r := by
  apply Subtype.ext
  change (ring k r).val ((gmat k r 0).det) = (fromPoly k r (delta k r) : K k r)
  rw [fromPoly_val, AlgHom.map_det,coe_gmat]
  exact ((algebraMap (Poly k r) (K k r)).map_det (base k r 0)).symm
end GKGraph
end
noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
variable {F : Type*} [Field F] [Algebra k F]
def freeEval (T : Fin 3 → Mat F r) : Poly k r →ₐ[k] F :=
  MvPolynomial.aeval (fun z : FreeVars r => T z.1 z.2.1 z.2.2)
theorem freeEval_base (T : Fin 3 → Mat F r) (b : Fin 3) :
    (freeEval k r T).mapMatrix (base k r b) = T b := by
  ext i j
  exact MvPolynomial.aeval_X _ _
theorem freeEval_delta (T : Fin 3 → Mat F r) :
    freeEval k r T (delta k r) = (T 0).det := by
  rw [delta, AlgHom.map_det, freeEval_base]
def specOpen (T : Fin 3 → Mat F r) (h : IsUnit (T 0).det) : openRing k r →ₐ[k] F :=
  IsLocalization.Away.liftAlgHom (delta k r) (f := freeEval k r T)
    ((freeEval_delta k r T).symm ▸ h)
def specField (T : Fin 3 → Mat F r) (h : IsUnit (T 0).det) : ring k r →ₐ[k] F :=
  (specOpen k r T h).comp (toOpen k r)
theorem specField_poly (T : Fin 3 → Mat F r) (h : IsUnit (T 0).det) (x : Poly k r) :
    specField k r T h (fromPoly k r x) = freeEval k r T x := by
  change specOpen k r T h (toOpen k r (fromPoly k r x)) = _
  rw [toOpen_fromPoly]
  exact IsLocalization.Away.lift_eq (delta k r) ((freeEval_delta k r T).symm ▸ h) x
theorem specField_first (T : Fin 3 → Mat F r) (h : IsUnit (T 0).det) (b : Fin 3) :
    (specField k r T h).mapMatrix (gmat k r (b.castLE (by decide))) = T b := by
  ext i j
  have e := specField_poly k r T h (MvPolynomial.X (b,i,j))
  simpa [fromPoly, freeEval, gmat, AlgHom.mapMatrix_apply,Matrix.map_apply] using e
section IntegralPoint
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra k R]
def pointBase (T : Fin 6 → Mat R r) : Fin 3 → Mat (FractionRing R) r :=
  fun b => (algebraMap R (FractionRing R)).mapMatrix (T (b.castLE (by decide)))
theorem pointUnit (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) :
    IsUnit ((pointBase r T) 0).det := by
  change IsUnit (((algebraMap R (FractionRing R)).mapMatrix (T 0)).det)
  rw [← RingHom.map_det,isUnit_iff_ne_zero]
  exact (IsFractionRing.to_map_eq_zero_iff.not).2 hP
structure Relations (T : Fin 6 → Mat R r) : Prop where
  y : T 0 * T 3 = T 1 * T 0
  z : T 0 * T 4 = T 2 * T 0
  comm : T 0 * T 5 = T 1 * T 2 - T 2 * T 1
def pointField (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) : ring k r →ₐ[k] FractionRing R :=
  specField k r (pointBase r T) (pointUnit r T hP)
theorem point_value (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0)
    (hT : Relations r T) (i : Fin 6) :
    (pointField k r T hP).mapMatrix (gmat k r i) =
      (algebraMap R (FractionRing R)).mapMatrix (T i) := by
  let φ : Mat (ring k r) r →ₐ[k] Mat (FractionRing R) r := (pointField k r T hP).mapMatrix
  let α : Mat R r →+* Mat (FractionRing R) r := (algebraMap R (FractionRing R)).mapMatrix
  have e0 : φ (gmat k r 0) = α (T 0) := specField_first k r _ _ 0
  have e1 : φ (gmat k r 1) = α (T 1) := specField_first k r _ _ 1
  have e2 : φ (gmat k r 2) = α (T 2) := specField_first k r _ _ 2
  have cancel {a b : Mat (FractionRing R) r} (hh : α (T 0) * a = α (T 0) * b) : a=b := by
    have p := congrArg (fun v => (α (T 0))⁻¹ * v) hh
    have hu : IsUnit (α (T 0)).det := pointUnit r T hP
    simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul] using p
  change φ (gmat k r i) = α (T i)
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · change φ (gmat k r 3) = α (T 3)
    apply cancel
    calc _ = φ (gmat k r 0 * gmat k r 3) := by rw [map_mul,e0]
         _ = _ := by rw [ring_Y, map_mul,e1,e0,← map_mul,←hT.y,map_mul]
  · change φ (gmat k r 4) = α (T 4)
    apply cancel
    calc _ = φ (gmat k r 0 * gmat k r 4) := by rw [map_mul,e0]
         _ = _ := by rw [ring_Z, map_mul,e2,e0,← map_mul,←hT.z,map_mul]
  · change φ (gmat k r 5) = α (T 5)
    apply cancel
    calc _ = φ (gmat k r 0 * gmat k r 5) := by rw [map_mul,e0]
         _ = _ := by rw [← ring_comm_left,map_sub,map_mul,map_mul,e1,e2,←map_mul,←map_mul,
                       ←map_sub,←hT.comm,map_mul]
end IntegralPoint
end GKGraph
end
noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
section Images
variable {A : Type*} [CommRing A] [Algebra k A]
theorem range_generated (φ : ring k r →ₐ[k] A) :
    φ.range = Algebra.adjoin k (Set.range (φ ∘ gcoord k r)) := by
  rw [← Algebra.map_top, ← generators k r, AlgHom.map_adjoin, Set.range_comp]
end Images
section Integral
variable {R : Type*} [CommRing R] [IsDomain R] [Algebra k R]
abbrev incl : R →ₐ[k] FractionRing R := IsScalarTower.toAlgHom k R (FractionRing R)
theorem whole_range (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0)
    (hT : Relations r T) :
    (pointField k r T hP).range ≤ (incl k (R := R)).range := by
  rw [range_generated]
  apply Algebra.adjoin_le
  rintro _ ⟨i,rfl⟩
  exact ⟨T i.1 i.2.1 i.2.2, (congrFun (congrFun (point_value k r T hP hT i.1) i.2.1) i.2.2).symm⟩
def point (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) (hT : Relations r T) :
    ring k r →ₐ[k] R :=
  (AlgEquiv.ofInjective (incl k (R := R)) (IsFractionRing.injective _ _)).symm.toAlgHom.comp
    ((pointField k r T hP).codRestrict (incl k (R := R)).range
      (fun a => whole_range k r T hP hT ⟨a,rfl⟩))
theorem point_coe (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) (hT : Relations r T)
    (a : ring k r) : incl k (point k r T hP hT a) = pointField k r T hP a := by
  let e := AlgEquiv.ofInjective (incl k (R := R)) (IsFractionRing.injective _ _)
  exact congrArg Subtype.val (e.apply_symm_apply ⟨_, whole_range k r T hP hT ⟨a,rfl⟩⟩)
theorem point_matrix (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) (hT : Relations r T)
    (b : Fin 6) : (point k r T hP hT).mapMatrix (gmat k r b) = T b := by
  ext i j
  apply IsFractionRing.injective R (FractionRing R)
  change incl k (point k r T hP hT (gmat k r b i j)) = _
  rw [point_coe]
  exact congrFun (congrFun (point_value k r T hP hT b) i) j
theorem point_det (T : Fin 6 → Mat R r) (hP : (T 0).det ≠ 0) (hT : Relations r T) :
    point k r T hP hT (gdelta k r) = (T 0).det := by
  rw [←det_gmat, AlgHom.map_det, point_matrix]
end Integral
end GKGraph
end
noncomputable section
namespace GKRational
variable {A K O : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing O] [IsDomain O]
def rat (a b : A) : K := algebraMap A K a / algebraMap A K b
abbrev adj (a b : A) := Algebra.adjoin A ({rat (K := K) a b} : Set K)
def q (a b : A) : adj (K := K) a b := ⟨rat a b, Algebra.subset_adjoin rfl⟩
abbrev opn (b : A) (hb : b ≠ 0) := Localization.subalgebra.ofField K (Submonoid.powers b)
  (powers_le_nonZeroDivisors_of_noZeroDivisors hb)
theorem toOpen (a b : A) (hb : b ≠ 0) : adj (K := K) a b ≤ opn b hb := by
  apply Algebra.adjoin_le
  rintro _ rfl
  exact ⟨a,b,Submonoid.mem_powers _, div_eq_mul_inv ..⟩
omit [IsDomain A] in
theorem qmul (a b : A) (hb : b ≠ 0) :
    q (K := K) a b * algebraMap A (adj a b) b = algebraMap A (adj a b) a := by
  apply Subtype.ext
  exact div_mul_cancel₀ _ ((IsFractionRing.to_map_eq_zero_iff.not).mpr hb)
variable (f : A →+* O) (a b : A) (hb : f b ≠ 0)
omit [IsDomain A] [IsDomain O] in
include hb in
theorem bne : b ≠ 0 := fun e => hb (by rw [e,map_zero])
def fracEval : adj (K := K) a b →+* FractionRing O :=
  let g := (algebraMap O (FractionRing O)).comp f
  let hgb : IsUnit (g b) := isUnit_iff_ne_zero.mpr ((IsFractionRing.to_map_eq_zero_iff.not).2 hb)
  (IsLocalization.Away.lift b (S := opn (K := K) b (bne f b hb)) hgb).comp
    (Subalgebra.inclusion (toOpen a b (bne f b hb))).toRingHom
theorem fracEval_base (x : A) : fracEval (K := K) f a b hb (algebraMap A (adj a b) x) =
    algebraMap O (FractionRing O) (f x) := by
  let g := (algebraMap O (FractionRing O)).comp f
  have hg : IsUnit (g b) := isUnit_iff_ne_zero.mpr ((IsFractionRing.to_map_eq_zero_iff.not).2 hb)
  exact IsLocalization.Away.lift_eq (S := opn (K := K) b (bne f b hb)) b hg x
variable (w : O) (hw : w * f b = f a)
include hw in
theorem fracEval_q : fracEval (K := K) f a b hb (q a b) = algebraMap O (FractionRing O) w := by
  have h := congrArg (fracEval (K := K) f a b hb) (qmul a b (bne f b hb))
  rw [map_mul, fracEval_base,fracEval_base,←hw,map_mul] at h
  exact mul_right_cancel₀ ((IsFractionRing.to_map_eq_zero_iff.not).2 hb) h
omit [IsDomain A] [IsFractionRing A K] in
private theorem top_q :
    Algebra.adjoin A ({q (K := K) a b} : Set (adj a b)) = ⊤ := by
  apply Subalgebra.map_injective (f := (adj a b).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Set.image_singleton,Algebra.map_top,Subalgebra.range_val]
  rfl
include hw in
theorem fracEval_range (x : adj (K := K) a b) :
    fracEval f a b hb x ∈ (algebraMap O (FractionRing O)).range := by
  let T : Subalgebra A (adj (K := K) a b) :=
    { (algebraMap O (FractionRing O)).range.comap (fracEval f a b hb) with
      algebraMap_mem' := fun y => ⟨f y, (fracEval_base f a b hb y).symm⟩ }
  have hq : q a b ∈ T := ⟨w, (fracEval_q f a b hb w hw).symm⟩
  have ht : ⊤ ≤ T := by
    rw [←top_q a b]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hq)
  exact ht (show x ∈ (⊤ : Subalgebra A _) from Algebra.mem_top)
def descend {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    (h : C →+* D) (hi : Function.Injective h) (g : B →+* D)
    (hg : ∀ x, g x ∈ h.range) : B →+* C where
  toFun x := (hg x).choose
  map_zero' := hi (by rw [(hg 0).choose_spec,map_zero,map_zero])
  map_one' := hi (by rw [(hg 1).choose_spec,map_one,map_one])
  map_add' x y := hi (by rw [(hg (x+y)).choose_spec,map_add,map_add,(hg x).choose_spec,(hg y).choose_spec])
  map_mul' x y := hi (by rw [(hg (x*y)).choose_spec,map_mul,map_mul,(hg x).choose_spec,(hg y).choose_spec])
def specialize : adj (K := K) a b →+* O :=
  descend (algebraMap O (FractionRing O)) (IsFractionRing.injective _ _)
    (fracEval f a b hb) (fracEval_range f a b hb w hw)
theorem spec_base (x : A) :
    specialize (K := K) f a b hb w hw (algebraMap A (adj a b) x) = f x := by
  apply IsFractionRing.injective O (FractionRing O)
  exact ((fracEval_range (K := K) f a b hb w hw _).choose_spec).trans (fracEval_base f a b hb x)
theorem spec_q : specialize (K := K) f a b hb w hw (q a b) = w := by
  apply IsFractionRing.injective O (FractionRing O)
  exact ((fracEval_range (K := K) f a b hb w hw _).choose_spec).trans (fracEval_q f a b hb w hw)
include hw hb in
theorem q_nonunit (hn : ¬ IsUnit w) : ¬ IsUnit (q (K := K) a b) := by
  intro hu
  exact hn ((spec_q (K := K) f a b hb w hw) ▸ hu.map (specialize f a b hb w hw))
omit [IsDomain A] in
theorem q_ne_zero (ha : a ≠ 0) (hb' : b ≠ 0) : q (K := K) a b ≠ 0 := by
  intro e
  exact div_ne_zero ((IsFractionRing.to_map_eq_zero_iff.not).2 ha)
    ((IsFractionRing.to_map_eq_zero_iff.not).2 hb') (congrArg Subtype.val e)
end GKRational
end
noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
variable {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
theorem gdelta_ne_zero : gdelta k r ≠ 0 := by
  intro h
  have hh := congrArg (fun x : ring k r => (x : K k r)) h
  change (fromPoly k r (delta k r) : K k r) = 0 at hh
  rw [fromPoly_val,IsFractionRing.to_map_eq_zero_iff] at hh
  exact delta_ne_zero k r hh
theorem nonunit_inverse_point (T : Fin 6 → Mat O r) (hP : (T 0).det ≠ 0) (hT : Relations r T)
    (h : ring k r) (B : point k r T hP hT h ≠ 0) (w : O)
    (hw : w * point k r T hP hT h = (T 0).det^(r-1)) (hn : ¬ IsUnit w) :
    ∃ f : GKRational.adj (K := K k r) ((gdelta k r)^(r-1)) h →+* O,
      (∀ x : ring k r, f (algebraMap _ _ x) = point k r T hP hT x) ∧
      f (GKRational.q _ _) = w ∧
      GKRational.q (K := K k r) ((gdelta k r)^(r-1)) h ≠ 0 ∧
      ¬ IsUnit (GKRational.q (K := K k r) ((gdelta k r)^(r-1)) h) := by
  let f := (point k r T hP hT).toRingHom
  let a := (gdelta k r)^(r-1)
  have ha : a ≠ 0 := pow_ne_zero _ (gdelta_ne_zero k r)
  have he : w * f h = f a := by simpa only [f, a, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_pow,point_det] using hw
  refine ⟨GKRational.specialize (K := K k r) f a h B w he,
    GKRational.spec_base _ _ _ _ _ _, GKRational.spec_q _ _ _ _ _ _, ?_, ?_⟩
  · exact GKRational.q_ne_zero _ _ ha (fun e => B (by rw [e,map_zero]))
  · exact GKRational.q_nonunit f a h B w he hn
end GKGraph
end
noncomputable section
namespace GKDivisor
variable (k : Type u) [Field k] [PerfectField k] (r : ℕ)
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
abbrev invGraph (h : GKGraph.ring k r) :=
  GKRational.adj (K := GKGraph.K k r) ((GKGraph.gdelta k r) ^ (r-1)) h
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
abbrev invCoord (h : GKGraph.ring k r) : invGraph k r h :=
  GKRational.q (K := GKGraph.K k r) _ _
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
omit [PerfectField k] in
theorem invGraph_trdeg (h : GKGraph.ring k r) :
    Algebra.trdeg k (invGraph k r h) = (3*r*r : ℕ) := by
  apply le_antisymm
  · rw [← GKGraph.field_trdeg k r]
    exact trdeg_le_of_injective ((invGraph k r h).val.restrictScalars k) Subtype.val_injective
  · rw [← GKGraph.ring_trdeg k r]
    exact trdeg_le_of_injective (IsScalarTower.toAlgHom k (GKGraph.ring k r) (invGraph k r h))
      (fun x y e => Subtype.ext (congrArg (fun z : invGraph k r h => (z : GKGraph.K k r)) e))
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
def PoleData (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] (q : A) (dim : ℕ) : Prop :=
  ∃ P : Ideal (Norm A), ∃ hp : P.IsPrime,
    algebraMap A (Norm A) q ∈ P ∧ P.height = 1 ∧
    IsDiscreteValuationRing (@Localization.AtPrime _ _ P hp) ∧
    Algebra.trdeg k (@Ideal.ResidueField _ _ P hp) + 1 = dim
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem mkPoleData (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] (q : A) (hq : q ≠ 0) (hn : ¬ IsUnit q) (dim : ℕ)
    (hd : Algebra.trdeg k A = dim) : PoleData k A q dim := by
  obtain ⟨P,hp,hm,hh,hv,ht⟩ := affine_pole_residue k A q hq hn
  exact ⟨P,hp,hm,hh,hv,ht.trans hd⟩
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem trueGraph_pole {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
    (T : Fin 6 → GKGraph.Mat O r) (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T)
    (h : GKGraph.ring k r) (hd : GKGraph.point k r T ht hT h ≠ 0)
    (w : O) (hw : w * GKGraph.point k r T ht hT h = (T 0).det^(r-1)) (hn : ¬IsUnit w) :
    PoleData k (invGraph k r h) (invCoord k r h) (3*r*r) := by
  obtain ⟨_,_,_,hq,hnq⟩ := GKGraph.nonunit_inverse_point k r T ht hT h hd w hw hn
  haveI : Algebra.FiniteType k (invGraph k r h) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k (GKGraph.ring k r))
      (OMAGerst.finiteType_adjoin_singleton _)
  exact mkPoleData k _ (invCoord k r h) hq hnq _ (invGraph_trdeg k r h)
end GKDivisor
end
noncomputable section
namespace GKRational
variable {A K B : Type*} [CommRing A] [Field K] [Algebra A K] [CommRing B]
variable (a b : A)
theorem range_eq_base_of_q_zero (ψ : adj (K := K) a b →+* B)
    (hq : ψ (q a b) = 0) : ψ.range = (ψ.comp (algebraMap A (adj a b))).range := by
  apply le_antisymm _ (by rintro _ ⟨x,rfl⟩; exact ⟨_,rfl⟩)
  rintro _ ⟨x,rfl⟩
  let T : Subalgebra A (adj (K := K) a b) :=
    { (ψ.comp (algebraMap A (adj a b))).range.comap ψ with
      algebraMap_mem' := fun y => ⟨y,rfl⟩ }
  have hq' : q a b ∈ T := ⟨0, by rw [map_zero,hq]⟩
  have ht : Algebra.adjoin A ({q a b} : Set (adj (K := K) a b)) = ⊤ := by
    apply Subalgebra.map_injective (f := (adj a b).val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Set.image_singleton, Algebra.map_top, Subalgebra.range_val]
    rfl
  have hh : ⊤ ≤ T := by rw [←ht]; exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hq')
  exact hh (show x ∈ (⊤ : Subalgebra A _) from Algebra.mem_top)
theorem residue_surjective (P : Ideal (adj (K := K) a b)) (hq : q a b ∈ P) :
    Function.Surjective ((Ideal.Quotient.mk P).comp (algebraMap A (adj a b))) := by
  intro x
  have H : x ∈ (Ideal.Quotient.mk P).range := Ideal.Quotient.mk_surjective x
  rw [range_eq_base_of_q_zero a b _ (Ideal.Quotient.eq_zero_iff_mem.mpr hq)] at H
  exact H
end GKRational
end
noncomputable section
namespace GKDivisor
theorem trdeg_center_eq (k G A N : Type u) [Field k] [CommRing G] [CommRing A] [CommRing N]
    [Algebra k G] [Algebra k A] [Algebra k N] [Algebra G A] [Algebra A N]
    [IsScalarTower k G A] [IsScalarTower k A N] [Module.Finite A N]
    (P : Ideal N) [P.IsPrime]
    (hs : Function.Surjective ((Ideal.Quotient.mk (P.under A)).comp (algebraMap G A))) :
    Algebra.trdeg k P.ResidueField = Algebra.trdeg k (G ⧸ (P.under A).under G) := by
  let Q := P.under A
  let J := Q.under G
  have hfin : Algebra.trdeg k (N ⧸ P) = Algebra.trdeg k (A ⧸ Q) :=
    trdeg_integral_inj (IsScalarTower.toAlgHom k (A ⧸ Q) (N ⧸ P))
      (FaithfulSMul.algebraMap_injective _ _) (algebraMap_isIntegral_iff.mpr inferInstance)
  have hsurj : Function.Surjective (algebraMap (G ⧸ J) (A ⧸ Q)) := by
    intro v
    obtain ⟨w,hw⟩ := hs v
    exact ⟨Ideal.Quotient.mk J w,hw⟩
  have hinteg : (algebraMap (G ⧸ J) (A ⧸ Q)).IsIntegral :=
    RingHom.isIntegral_of_surjective _ hsurj
  rw [trdeg_residueField, hfin]
  exact trdeg_integral_inj (IsScalarTower.toAlgHom k (G ⧸ J) (A ⧸ Q))
    (FaithfulSMul.algebraMap_injective _ _) hinteg
def CenterData (k G A : Type u) [Field k] [CommRing G] [CommRing A] [IsDomain A]
    [Algebra k G] [Algebra k A] [Algebra G A] (q : A) (dim : ℕ) : Prop :=
  ∃ P : Ideal (Norm A), ∃ hp : P.IsPrime,
    algebraMap A (Norm A) q ∈ P ∧ P.height = 1 ∧
    IsDiscreteValuationRing (@Localization.AtPrime _ _ P hp) ∧
    Algebra.trdeg k (@Ideal.ResidueField _ _ P hp) + 1 = dim ∧
    Algebra.trdeg k (G ⧸ (P.under A).under G) + 1 = dim ∧
    Algebra.EssFiniteType k (@Ideal.ResidueField _ _ P hp)
theorem mkCenterData (k G A : Type u) [Field k] [PerfectField k] [CommRing G] [CommRing A] [IsDomain A]
    [Algebra k G] [Algebra k A] [Algebra.FiniteType k A] [Algebra G A] [IsScalarTower k G A]
    (q : A) (m : ℕ) (H : PoleData k A q m)
    (he : ∀ Q : Ideal A, q ∈ Q → Function.Surjective ((Ideal.Quotient.mk Q).comp (algebraMap G A))) :
    CenterData k G A q m := by
  obtain ⟨P,hp,hm,hh,hv,ht⟩ := H
  letI := hp
  letI : Module.Finite A (Norm A) := finite_affine_normalization k A
  letI : Algebra.FiniteType k (Norm A) := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k A) (inferInstance : Algebra.FiniteType A (Norm A))
  exact ⟨P,hp,hm,hh,hv,ht,(trdeg_center_eq k G A (Norm A) P (he _ hm)) ▸ ht,
    Algebra.EssFiniteType.comp k (Norm A) P.ResidueField⟩
variable (k : Type u) [Field k] [PerfectField k] (r : ℕ)
theorem trueGraph_pole_center {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
    (T : Fin 6 → GKGraph.Mat O r) (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T)
    (h : GKGraph.ring k r) (hd : GKGraph.point k r T ht hT h ≠ 0)
    (w : O) (hw : w * GKGraph.point k r T ht hT h = (T 0).det^(r-1)) (hn : ¬IsUnit w) :
    CenterData k (GKGraph.ring k r) (invGraph k r h) (invCoord k r h) (3*r*r) := by
  haveI : Algebra.FiniteType k (invGraph k r h) :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k (GKGraph.ring k r))
      (OMAGerst.finiteType_adjoin_singleton _)
  exact mkCenterData k _ _ _ _ (trueGraph_pole k r T ht hT h hd w hw hn)
    (GKRational.residue_surjective _ _)
end GKDivisor
end
noncomputable section
namespace GKDivisor
def centerMap (k G A N : Type u) [Field k] [CommRing G] [CommRing A] [CommRing N]
    [Algebra k G] [Algebra k A] [Algebra k N] [Algebra G A] [Algebra A N]
    [IsScalarTower k G A] [IsScalarTower k A N] (P : Ideal N) [P.IsPrime] :
    G →ₐ[k] P.ResidueField :=
  (IsScalarTower.toAlgHom k N P.ResidueField).comp
    ((IsScalarTower.toAlgHom k A N).comp (IsScalarTower.toAlgHom k G A))
theorem centerMap_range_trdeg (k G A N : Type u) [Field k] [CommRing G] [CommRing A] [CommRing N]
    [Algebra k G] [Algebra k A] [Algebra k N] [Algebra G A] [Algebra A N]
    [IsScalarTower k G A] [IsScalarTower k A N] (P : Ideal N) [P.IsPrime] :
    Algebra.trdeg k (centerMap k G A N P).range = Algebra.trdeg k (G ⧸ (P.under A).under G) := by
  let f := centerMap k G A N P
  have he : RingHom.ker f = (P.under A).under G := by
    ext x
    exact Ideal.algebraMap_residueField_eq_zero
  exact (Ideal.quotientKerEquivRange f).trdeg_eq.symm.trans (congrArg (fun I : Ideal G => Algebra.trdeg k (G ⧸ I)) he)
theorem six_coordinate_count (k : Type u) [Field k] (r : ℕ) (A N : Type u)
    [CommRing A] [CommRing N] [Algebra k A] [Algebra k N]
    [Algebra (GKGraph.ring k r) A] [Algebra A N]
    [IsScalarTower k (GKGraph.ring k r) A] [IsScalarTower k A N]
    (P : Ideal N) [P.IsPrime] :
    let ψ := centerMap k (GKGraph.ring k r) A N P
    Algebra.trdeg k (Algebra.adjoin k (Set.range (ψ ∘ GKGraph.gcoord k r))) =
      Algebra.trdeg k ((GKGraph.ring k r) ⧸ (P.under A).under (GKGraph.ring k r)) := by
  dsimp only
  rw [← GKGraph.range_generated]
  exact centerMap_range_trdeg k _ _ _ P
end GKDivisor
end
noncomputable section
namespace GKDivisor
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
structure BadPole (k : Type u) [Field k] (r : ℕ) (h : GKGraph.ring k r) where
  V : Type u
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [alg : Algebra k V]
  [residue_ess : Algebra.EssFiniteType k (IsLocalRing.ResidueField V)]
  f : GKGraph.ring k r →ₐ[k] V
  inj : Function.Injective f
  w : V
  nonunit : ¬ IsUnit w
  equation : w * f h = (f (GKGraph.gdelta k r))^(r-1)
  count :
    let ψ := (IsScalarTower.toAlgHom k V (IsLocalRing.ResidueField V)).comp f
    Algebra.trdeg k (Algebra.adjoin k (Set.range (ψ ∘ GKGraph.gcoord k r))) + 1 = (3*r*r : ℕ)
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
theorem realizePole (k : Type u) [Field k] (r : ℕ) (h : GKGraph.ring k r)
    (A : Type u) [CommRing A] [IsDomain A] [Algebra k A] [Algebra (GKGraph.ring k r) A]
    [IsScalarTower k (GKGraph.ring k r) A]
    (inj : Function.Injective (algebraMap (GKGraph.ring k r) A)) (q : A)
    (he : q * algebraMap _ A h = algebraMap _ A ((GKGraph.gdelta k r)^(r-1)))
    (H : CenterData k (GKGraph.ring k r) A q (3*r*r)) : Nonempty (BadPole k r h) := by
  obtain ⟨P,hp,hm,-,hv,-,hc,hess⟩ := H
  letI := hp
  let N := Norm A
  let V := Localization.AtPrime P
  letI : IsDiscreteValuationRing V := hv
  let g := (IsScalarTower.toAlgHom k N V).comp (IsScalarTower.toAlgHom k A N)
  let f := g.comp (IsScalarTower.toAlgHom k (GKGraph.ring k r) A)
  have hin : Function.Injective (IsScalarTower.toAlgHom k A N) := fun a b e =>
    IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val e)
  have hiv : Function.Injective (IsScalarTower.toAlgHom k N V) :=
    IsLocalization.injective V P.primeCompl_le_nonZeroDivisors
  refine ⟨{ V := V
            residue_ess := hess
            f := f
            inj := hiv.comp (hin.comp inj)
            w := g q
            nonunit := ?_
            equation := ?_
            count := ?_ }⟩
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff V P _).mpr hm
  · change g q * g (algebraMap _ A h) = (g ((algebraMap _ A) (GKGraph.gdelta k r)))^(r-1)
    rw [←map_mul, he, map_pow, map_pow]
  · have ht := six_coordinate_count k r A N P
    exact (congrArg (· + 1) ht).trans hc
set_option synthInstance.maxHeartbeats 80000 in
set_option maxHeartbeats 900000 in
theorem trueGraph_concrete_pole (k : Type u) [Field k] [PerfectField k] (r : ℕ)
    {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
    (T : Fin 6 → GKGraph.Mat O r) (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T)
    (h : GKGraph.ring k r) (hd : GKGraph.point k r T ht hT h ≠ 0)
    (w : O) (hw : w * GKGraph.point k r T ht hT h = (T 0).det^(r-1)) (hn : ¬IsUnit w) :
    Nonempty (BadPole k r h) := by
  have hne : h ≠ 0 := fun e => hd (by rw [e,map_zero])
  exact realizePole k r h (invGraph k r h)
    (fun x y e => Subtype.ext (congrArg (fun z : invGraph k r h => (z : GKGraph.K k r)) e))
    (invCoord k r h) (GKRational.qmul _ _ hne) (trueGraph_pole_center k r T ht hT h hd w hw hn)
end GKDivisor
end
noncomputable section
namespace DivisorG3
open Module
section Volume
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι]
def latticeVolume (b : Basis ι R M) (N : Submodule R M) : N [⋀^ι]→ₗ[R] R :=
  b.det.compLinearMap N.subtype
def latticeVolumeIdeal (b : Basis ι R M) (N : Submodule R M) : Ideal R :=
  Ideal.span (Set.range (latticeVolume b N))
theorem latticeVolumeIdeal_eq_span_basis (b : Basis ι R M) (N : Submodule R M)
    (bN : Basis ι R N) :
    latticeVolumeIdeal b N = Ideal.span {latticeVolume b N bN} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨v, rfl⟩
    change latticeVolume b N v ∈
      (Ideal.span ({latticeVolume b N bN} : Set R) : Ideal R)
    apply Ideal.mem_span_singleton.mpr
    refine ⟨bN.det v, ?_⟩
    have h := congrArg (fun f : N [⋀^ι]→ₗ[R] R => f v)
      ((latticeVolume b N).eq_smul_basis_det bN)
    simpa [smul_eq_mul, mul_comm] using h
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact Ideal.subset_span ⟨bN, rfl⟩
end Volume
section SmithVolume
variable {R M ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
theorem latticeVolumeIdeal_eq_span_smith (b : Basis ι R M) (N : Submodule R M)
    (h : Module.finrank R N = Module.finrank R M) :
    latticeVolumeIdeal b N =
      Ideal.span {∏ i, Submodule.smithNormalFormCoeffs b h i} := by
  let bM := Submodule.smithNormalFormTopBasis b h
  let bN := Submodule.smithNormalFormBotBasis b h
  let a := Submodule.smithNormalFormCoeffs b h
  have ha (i : ι) : (bN i : M) = a i • bM i :=
    Submodule.smithNormalFormBotBasis_def b h i
  have hd : latticeVolume b N bN = (∏ i, a i) * b.det bM := by
    change b.det (fun i => (bN i : M)) = _
    simp_rw [ha]
    simpa only [smul_eq_mul] using b.det.map_smul_univ a bM
  rw [latticeVolumeIdeal_eq_span_basis b N bN, hd,
    Ideal.span_singleton_mul_right_unit (b.isUnit_det bM)]
end SmithVolume
section MatrixVolumes
variable {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def matrixColumnLattice (A : Matrix ι κ R) :
    Submodule R (ι → R) := A.mulVecLin.range
def allColumnMinorIdeal (A : Matrix ι κ R) : Ideal R :=
  Ideal.span (Set.range fun s : ι → κ => (A.submatrix id s).det)
def columnInLattice (A : Matrix ι κ R) (j : κ) :
    matrixColumnLattice A :=
  ⟨A.col j, ⟨Pi.single j 1, by simp⟩⟩
omit [Fintype κ] [DecidableEq κ] in
theorem columnVolume_eq_minor (A : Matrix ι κ R)
    (s : ι → κ) :
    (Pi.basisFun R ι).det (fun i => A.col (s i)) =
      (A.submatrix id s).det := by
  rw [Pi.basisFun_det_apply]
  change (A.submatrix id s).transpose.det = _
  exact Matrix.det_transpose _
theorem latticeVolumeIdeal_matrixColumnLattice
    (A : Matrix ι κ R) :
    latticeVolumeIdeal (Pi.basisFun R ι) (matrixColumnLattice A) =
      allColumnMinorIdeal A := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨v, rfl⟩
    have hv (i : ι) : ∃ w, A.mulVecLin w = (v i : ι → R) :=
      (v i).property
    choose w hw using hv
    have hs (i : ι) : (v i : ι → R) =
        ∑ j, w i j • A.col j := by
      rw [← hw i]
      ext k
      simp [Matrix.mulVec, dotProduct, mul_comm]
    change (Pi.basisFun R ι).det.toMultilinearMap
      (fun i => (v i : ι → R)) ∈ allColumnMinorIdeal A
    simp_rw [hs]
    rw [MultilinearMap.map_sum]
    apply Submodule.sum_mem
    intro s _
    change (Pi.basisFun R ι).det (fun i => w i (s i) • A.col (s i)) ∈ _
    rw [AlternatingMap.map_smul_univ]
    apply (allColumnMinorIdeal A).smul_mem
    rw [columnVolume_eq_minor]
    exact Ideal.subset_span ⟨s, rfl⟩
  · apply Ideal.span_le.mpr
    rintro x ⟨s, rfl⟩
    apply Ideal.subset_span
    refine ⟨fun i => columnInLattice A (s i), ?_⟩
    change (Pi.basisFun R ι).det (fun i => A.col (s i)) = _
    exact columnVolume_eq_minor A s
end MatrixVolumes
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module IsDiscreteValuationRing
variable {V ι κ : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
abbrev colQuot (A : Matrix ι κ V) := (ι → V) ⧸ matrixColumnLattice A
theorem valuation_prod {α : Type*} (s : Finset α) (f : α → V) :
    addVal V (∏ i ∈ s, f i) = ∑ i ∈ s, addVal V (f i) := by
  classical induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hx ih => simp [hx,ih]
theorem intrinsic_smith (A : Matrix ι κ V) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    ∃ g : V, g≠0 ∧ allColumnMinorIdeal A = Ideal.span ({g}:Set _) ∧
      length V (colQuot A) = addVal V g := by
  let b := Pi.basisFun V ι
  let N := matrixColumnLattice A
  have h : finrank V N = finrank V (ι→V) := by
    rw [Module.finrank_pi]
    change A.rank = Fintype.card ι
    exact le_antisymm A.rank_le_card_height (Matrix.rank_of_det_ne_zero hs ▸ A.rank_submatrix_le id s)
  let a := Submodule.smithNormalFormCoeffs b h
  have ha (i) : a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h i
  refine ⟨∏ i,a i,Finset.prod_ne_zero_iff.mpr (fun i _ => ha i),?_,?_⟩
  · rw [←latticeVolumeIdeal_matrixColumnLattice,latticeVolumeIdeal_eq_span_smith b _ h]
  · rw [(N.quotientEquivPiSpan b h).length_eq,Module.length_pi_of_fintype,valuation_prod]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)
theorem intrinsic_colength (A : Matrix ι κ V) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    length V (V ⧸ allColumnMinorIdeal A) = length V (colQuot A) ∧ IsFiniteLength V (colQuot A) := by
  obtain ⟨g,hg,he,hl⟩ := intrinsic_smith A s hs
  refine ⟨?_,Module.length_ne_top_iff.mp (hl ▸ addVal_eq_top_iff.not.mpr hg)⟩
  rw [he,hl]
  exact Ring.ord_eq_addVal g
theorem intrinsic_witness (A : Matrix ι κ V) (s : ι → κ) (hs : (A.submatrix id s).det≠0) (c : V) :
    length V (colQuot A) < addVal V c ↔ ∃ j : ι → κ, addVal V (A.submatrix id j).det < addVal V c := by
  obtain ⟨g,_,he,hl⟩ := intrinsic_smith A s hs
  rw [hl]
  constructor
  · intro hn
    by_contra! h
    have le : allColumnMinorIdeal A ≤ Ideal.span ({c}:Set V) :=
      Ideal.span_le.mpr fun _ ⟨j,ej⟩ => ej ▸ Ideal.mem_span_singleton.mpr (addVal_le_iff_dvd.mp (h j))
    exact (not_le_of_gt hn) (addVal_le_iff_dvd.mpr (Ideal.mem_span_singleton.mp
      (le (he ▸ Ideal.subset_span (Set.mem_singleton g)))))
  · rintro ⟨j,hj⟩
    apply lt_of_le_of_lt _ hj
    apply addVal_le_iff_dvd.mpr
    apply Ideal.mem_span_singleton.mp
    rw [←he]
    exact Ideal.subset_span ⟨j,rfl⟩
omit [IsDomain V] [IsDiscreteValuationRing V] in
theorem square_minor_ideal (P : Matrix ι ι V) : allColumnMinorIdeal P = Ideal.span ({P.det}:Set V) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨s,rfl⟩
    apply Ideal.mem_span_singleton.mpr
    let E := (1 : Matrix ι ι V).submatrix id s
    have he : P.submatrix id s = P * E := by ext i j; simp [E,Matrix.mul_apply,Matrix.one_apply]
    exact ⟨E.det,(congrArg Matrix.det he).trans (Matrix.det_mul P E)⟩
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    apply Ideal.subset_span
    exact ⟨id,rfl⟩
theorem intrinsic_square (P : Matrix ι ι V) (hp : P.det≠0) :
    length V (colQuot P) = addVal V P.det := by
  obtain ⟨h,_⟩ := intrinsic_colength P id (by exact hp)
  rw [←h,square_minor_ideal]
  exact Ring.ord_eq_addVal _
end DivisorG3
end
noncomputable section
namespace DivisorG3
open LinearMap Module Submodule
variable {R F : Type*} [CommRing R] [AddCommGroup F] [Module R F]
abbrev Coker (P : Module.End R F) := F ⧸ P.range
def times (t : R) (F : Type*) [AddCommGroup F] [Module R F] : Module.End R F := t • LinearMap.id
variable (t : R) (P Q : Module.End R F)
abbrev Tail := (times t (Coker P)).ker
def toTail (fac : ∀ x, P x = t • Q x) : F →ₗ[R] Tail t P :=
  (P.range.mkQ.comp Q).codRestrict _ fun x => by
    change t • P.range.mkQ (Q x) = 0
    rw [← map_smul,←fac]
    exact (Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩
theorem toTail_surj (fac : ∀ x, P x = t • Q x)
    (reg : Function.Injective (fun x : F => t • x)) : Function.Surjective (toTail t P Q fac) := by
  rintro ⟨w,hw⟩
  obtain ⟨v,rfl⟩ := P.range.mkQ_surjective w
  change t • P.range.mkQ v=0 at hw
  rw [←map_smul] at hw
  obtain ⟨z,hz⟩ := (Quotient.mk_eq_zero _).mp hw
  have eq : Q z=v := reg ((fac z).symm.trans hz)
  exact ⟨z,Subtype.ext (congrArg P.range.mkQ eq)⟩
theorem toTail_ker (fac : ∀ x, P x = t • Q x) (inj : Function.Injective P) :
    (toTail t P Q fac).ker = (times t F).range := by
  ext x
  change (toTail t P Q fac x = 0) ↔ ∃ z, t • z = x
  rw [Subtype.ext_iff]
  change P.range.mkQ (Q x) = 0 ↔ _
  rw [mkQ_apply,Quotient.mk_eq_zero]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,inj ?_⟩
    rw [map_smul,fac x,←hz]
  · rintro ⟨z,rfl⟩
    exact ⟨z,(fac z).trans (Q.map_smul t z).symm⟩
def tailEquiv (fac : ∀ x, P x = t • Q x) (inj : Function.Injective P)
    (reg : Function.Injective (fun x : F => t • x)) :
    Coker (times t F) ≃ₗ[R] Tail t P :=
  (Submodule.quotEquivOfEq _ _ (toTail_ker t P Q fac inj).symm) ≪≫ₗ
   (toTail t P Q fac).quotKerEquivOfSurjective (toTail_surj t P Q fac reg)
theorem tail_formula (fac : ∀ x, P x = t • Q x) (inj : Function.Injective P)
    (reg : Function.Injective (fun x : F => t • x)) (x : F) :
    (tailEquiv t P Q fac inj reg ((times t F).range.mkQ x)).val = P.range.mkQ (Q x) := rfl
theorem tail_intertwines (Y Y' : Module.End R F) (fac : ∀ x, P x = t • Q x)
    (reg : Function.Injective (fun x : F => t • x)) (square : ∀ x, Y (P x) = P (Y' x)) (x : F) :
    P.range.mkQ (Q (Y' x)) = P.range.mkQ (Y (Q x)) := by
  apply congrArg _
  apply reg
  change t • Q (Y' x) = t • Y (Q x)
  rw [←fac,←Y.map_smul,←fac, square]
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module LinearMap Submodule Matrix IsDiscreteValuationRing
open scoped Matrix
variable {R ι β : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]
abbrev QP (P : Matrix ι ι R) := Coker P.mulVecLin
def diagP (P : Matrix ι ι R) := blockDiagonal fun _ : ι => P
def columnMap (P : Matrix ι ι R) : ((ι×ι)→R) →ₗ[R] (ι → QP P) where
  toFun v j := P.mulVecLin.range.mkQ (fun i => v (i,j))
  map_add' _ _ := by ext; apply map_add
  map_smul' c v := by funext j; exact P.mulVecLin.range.mkQ.map_smul c (fun i => v (i,j))
omit [DecidableEq ι] in
theorem column_surj (P : Matrix ι ι R) : Function.Surjective (columnMap P) := by
  intro z
  choose v hv using fun j => P.mulVecLin.range.mkQ_surjective (z j)
  exact ⟨fun a => v a.2 a.1,funext hv⟩
theorem diag_apply (P : Matrix ι ι R) (w : (ι×ι)→R) (i j : ι) :
    (diagP P).mulVecLin w (i,j) = (P.mulVecLin (fun a => w (a,j))) i := by
  classical
  simp [diagP,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply,ite_mul]
theorem column_ker (P : Matrix ι ι R) : (columnMap P).ker = matrixColumnLattice (diagP P) := by
  ext v
  constructor
  · intro hv
    have hv' (j : ι) : (fun i => v (i,j)) ∈ P.mulVecLin.range :=
      (Quotient.mk_eq_zero _).mp (congrFun (show columnMap P v=0 from hv) j)
    choose w hw using hv'
    exact ⟨fun a => w a.2 a.1,funext fun ⟨i,j⟩ => (diag_apply P _ i j).trans (congrFun (hw j) i)⟩
  · rintro ⟨w,rfl⟩
    change columnMap P _ = 0
    funext j
    apply (Quotient.mk_eq_zero _).mpr
    exact ⟨fun i => w (i,j),funext fun i => (diag_apply P _ i j).symm⟩
def blockColumns (P : Matrix ι ι R) (B : β → Matrix ι ι R) : Matrix (ι×ι) ((ι×ι)⊕β) R :=
  fromCols (diagP P) (fun ij l => B l ij.1 ij.2)
def wordImage (P : Matrix ι ι R) (B : β → Matrix ι ι R) : Submodule R (ι → QP P) :=
  span R (Set.range fun l : β => fun j => P.mulVecLin.range.mkQ ((B l).col j))
omit [DecidableEq β] in
theorem block_ker_le (P : Matrix ι ι R) (B : β → Matrix ι ι R) :
    (columnMap P).ker ≤ matrixColumnLattice (blockColumns P B) := by
  rw [column_ker]
  change (diagP P).mulVecLin.range ≤ (blockColumns P B).mulVecLin.range
  rw [Matrix.range_mulVecLin,Matrix.range_mulVecLin]
  exact Submodule.span_mono fun _ ⟨ij,e⟩ => ⟨.inl ij,e⟩
omit [DecidableEq β] in
theorem block_image (P : Matrix ι ι R) (B : β → Matrix ι ι R) :
    (matrixColumnLattice (blockColumns P B)).map (columnMap P) = wordImage P B := by
  rw [matrixColumnLattice,Matrix.range_mulVecLin (blockColumns P B),Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_,⟨ij,rfl⟩,rfl⟩
    cases ij with
    | inl j =>
      have hz : (diagP P).col j ∈ (columnMap P).ker := by
        rw [column_ker,matrixColumnLattice,Matrix.range_mulVecLin (diagP P)]
        exact subset_span ⟨j,rfl⟩
      exact (show columnMap P ((diagP P).col j)=0 from hz) ▸ zero_mem _
    | inr l => exact subset_span ⟨l,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨l,rfl⟩
    exact subset_span ⟨_,⟨Sum.inr l,rfl⟩,rfl⟩
def blockQuotEquiv (P : Matrix ι ι R) (B : β → Matrix ι ι R) :
    colQuot (blockColumns P B) ≃ₗ[R] (ι → QP P) ⧸ wordImage P B := by
  let f := columnMap P
  let L := matrixColumnLattice (blockColumns P B)
  let N := wordImage P B
  let g := N.mkQ.comp f
  have h : g.ker=L := by
    rw [ker_comp,ker_mkQ]; dsimp only [N,L,f]; rw [←block_image P B,Submodule.comap_map_eq,sup_eq_left.mpr (block_ker_le P B)]
  exact (Submodule.quotEquivOfEq _ _ h.symm) ≪≫ₗ g.quotKerEquivOfSurjective (N.mkQ_surjective.comp (column_surj P))
variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
omit [Fintype β] [DecidableEq β] in
theorem block_minor_nonzero (P : Matrix ι ι V) (hp : P.det≠0) (B : β → Matrix ι ι V) :
    ((blockColumns P B).submatrix _root_.id Sum.inl).det ≠ 0 := by
  change (blockDiagonal (fun _ : ι => P)).det≠0
  rw [det_blockDiagonal]; exact Finset.prod_ne_zero_iff.mpr fun _ _ => hp
theorem block_index (P : Matrix ι ι V) (hp : P.det≠0) (B : β → Matrix ι ι V) :
    length V (V ⧸ allColumnMinorIdeal (blockColumns P B)) + length V (wordImage P B) =
      Fintype.card ι * length V (QP P) := by
  rw [(intrinsic_colength _ _ (block_minor_nonzero P hp B)).1,(blockQuotEquiv P B).length_eq]
  have e := length_eq_add_of_exact (wordImage P B).subtype (wordImage P B).mkQ
    (wordImage P B).subtype_injective (wordImage P B).mkQ_surjective
    (LinearMap.exact_subtype_mkQ _)
  rw [add_comm,← e,Module.length_pi_of_fintype]
  simp
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module Submodule Polynomial
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
abbrev box (x y : A) (m n : ℕ) := fun ij : Fin m × Fin n => x^ij.1.val * y^ij.2.val
variable [Nontrivial R]
theorem pow_reduce (x : A) (p : R[X]) (hp : p.Monic) (hx : aeval x p=0) (a : ℕ) :
    x^a ∈ span R (Set.range fun i : Fin p.natDegree => x^i.val) := by
  apply PowerBasis.mem_span_pow'.mpr
  refine ⟨X^a %ₘ p,(degree_modByMonic_lt _ hp).trans_le degree_le_natDegree,?_⟩
  rw [aeval_modByMonic_eq_self_of_root hx,map_pow,aeval_X]
theorem adjoin_box (x y : A) (h : Commute x y)
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) (hx : aeval x p=0) (hy : aeval y q=0) :
    (Algebra.adjoin R ({x,y} : Set A)).toSubmodule =
      span R (Set.range (box x y p.natDegree q.natDegree)) := by
  let L := span R (Set.range (box x y p.natDegree q.natDegree))
  have red (a b : ℕ) : x^a * y^b ∈ L := by
    have redL (i : Fin p.natDegree) (z : A) (hz : z ∈ span R (Set.range fun j : Fin q.natDegree => y^j.val)) : x^i.val*z ∈ L := by
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨j,rfl⟩ := hz; exact subset_span ⟨(i,j),rfl⟩
      | zero => simp
      | add _ _ _ _ hv hw => simpa [mul_add] using L.add_mem hv hw
      | smul c z _ hz => simpa [mul_smul_comm] using L.smul_mem c hz
    have hyb := pow_reduce y q hq hy b
    have hxa := pow_reduce x p hp hx a
    generalize x^a = v at hxa ⊢
    induction hxa using Submodule.span_induction with
    | mem z hz => obtain ⟨i,rfl⟩ := hz; exact redL i _ hyb
    | zero => simp
    | add _ _ _ _ hv hw => simpa [add_mul] using L.add_mem hv hw
    | smul c z _ hz => simpa [smul_mul_assoc] using L.smul_mem c hz
  let U : Submonoid A := {
    carrier := {a | ∃ m n : ℕ, a=x^m*y^n}
    one_mem' := ⟨0,0,by simp⟩
    mul_mem' := by
      rintro _ _ ⟨a,b,rfl⟩ ⟨c,d,rfl⟩
      exact ⟨a+c,b+d,by
        rw [pow_add,pow_add,←mul_assoc, mul_assoc (x^a) (y^b) (x^c), ((h.pow_pow c b).symm).eq]
        simp only [mul_assoc]⟩ }
  have hU : Submonoid.closure ({x,y}:Set A) ≤ U := by
    apply Submonoid.closure_le.mpr
    rintro z (rfl | hz)
    · exact ⟨1,0,by simp⟩
    · obtain rfl := Set.mem_singleton_iff.mp hz; exact ⟨0,1,by simp⟩
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span]
    exact span_le.mpr fun z hz => by obtain ⟨m,n,rfl⟩:=hU hz; exact red m n
  · apply span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    have hx' : x ∈ Algebra.adjoin R ({x,y}:Set A) := Algebra.subset_adjoin (Set.mem_insert _ _)
    have hy' : y ∈ Algebra.adjoin R ({x,y}:Set A) :=
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
    show x ^ i.val * y ^ j.val ∈ Algebra.adjoin R ({x,y}:Set A)
    exact mul_mem (pow_mem hx' _) (pow_mem hy' _)
end DivisorG3
end
noncomputable section
namespace GKGraph
variable (k : Type*) [Field k] (r : ℕ)
abbrev Row (r : ℕ) := Fin r × Fin r
abbrev Col (r : ℕ) := Row r ⊕ Row r
abbrev selectCols (r : ℕ) := Row r → Col r
variable {A B : Type*} [CommRing A] [CommRing B]
def hMatrix (P Y Z : Mat A r) : Matrix (Row r) (Col r) A :=
  DivisorG3.blockColumns P (DivisorG3.box Y Z r r)
def fullMinor (P Y Z : Mat A r) (s : selectCols r) := ((hMatrix r P Y Z).submatrix id s).det
theorem hMatrix_map (f : A →+* B) (P Y Z : Mat A r) :
    (hMatrix r P Y Z).map f = hMatrix r (f.mapMatrix P) (f.mapMatrix Y) (f.mapMatrix Z) := by
  ext ⟨i,j⟩ a
  cases a with
  | inl a =>
    simp [hMatrix,DivisorG3.blockColumns,DivisorG3.diagP,Matrix.blockDiagonal_apply,
      Matrix.fromCols,Matrix.map_apply,apply_ite f,RingHom.mapMatrix_apply]
  | inr a =>
    change f.mapMatrix (Y^a.1.val*Z^a.2.val) i j = (f.mapMatrix Y^a.1.val*f.mapMatrix Z^a.2.val) i j
    simp only [map_mul,map_pow]
theorem fullMinor_map (f : A →+* B) (P Y Z : Mat A r) (s : selectCols r) :
    f (fullMinor r P Y Z s) = fullMinor r (f.mapMatrix P) (f.mapMatrix Y) (f.mapMatrix Z) s := by
  unfold fullMinor
  rw [RingHom.map_det]
  change (((hMatrix r P Y Z).map f).submatrix id s).det = _
  rw [hMatrix_map]
def universalMinor (s : selectCols r) : ring k r := fullMinor r (gmat k r 0) (gmat k r 1) (gmat k r 2) s
variable {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
variable (T : Fin 6 → Mat O r) (hp : (T 0).det ≠ 0) (ht : Relations r T)
theorem point_minor (s : selectCols r) :
    point k r T hp ht (universalMinor k r s) = fullMinor r (T 0) (T 1) (T 2) s := by
  change (point k r T hp ht).toRingHom (fullMinor r _ _ _ s) = _
  rw [fullMinor_map]
  change fullMinor r ((point k r T hp ht).mapMatrix _) ((point k r T hp ht).mapMatrix _)
    ((point k r T hp ht).mapMatrix _) s = _
  rw [point_matrix,point_matrix,point_matrix]
open IsDiscreteValuationRing
variable [IsDiscreteValuationRing O]
end GKGraph
end
noncomputable section
namespace GKDivisor
open IsDiscreteValuationRing
local instance BadPole.instCr1 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom1 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr1 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg1 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
theorem strict_pole_of_real_minor (k : Type u) [Field k] [PerfectField k] (r : ℕ)
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra k O]
    (T : Fin 6 → GKGraph.Mat O r) (ht : (T 0).det ≠ 0) (hT : GKGraph.Relations r T)
    (s : GKGraph.selectCols r)
    (hs : addVal O (GKGraph.fullMinor r (T 0) (T 1) (T 2) s) < addVal O ((T 0).det^(r-1))) :
    Nonempty (BadPole k r (GKGraph.universalMinor k r s)) := by
  obtain ⟨w,hw⟩ := addVal_le_iff_dvd.mp hs.le
  have hn : ¬ IsUnit w := by
    intro hu
    rw [hw,AddValuation.map_mul,addVal_eq_zero_iff.mpr hu,add_zero] at hs
    exact lt_irrefl _ hs
  have hz : GKGraph.fullMinor r (T 0) (T 1) (T 2) s ≠ 0 := by
    intro e; rw [e,AddValuation.map_zero] at hs; exact not_top_lt hs
  exact trueGraph_concrete_pole k r T ht hT (GKGraph.universalMinor k r s)
    (by rw [GKGraph.point_minor]; exact hz) w (by rw [GKGraph.point_minor,mul_comm]; exact hw.symm) hn
lemma strict_value_of_nonunit_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (w a b : O) (hn : ¬IsUnit w) (hb : b ≠ 0) (he : w*a=b) : addVal O a < addVal O b := by
  apply lt_of_le_of_ne
  · exact addVal_le_iff_dvd.mpr ⟨w,by rw [← he,mul_comm]⟩
  · intro e
    obtain ⟨d,hd⟩ := addVal_le_iff_dvd.mp e.ge
    have he' : b * (w*d) = b * 1 := by
      calc _ = w * (b*d) := by ring
           _ = b * 1 := by rw [←hd,he,mul_one]
    exact hn (isUnit_iff_exists_inv.mpr ⟨d,mul_left_cancel₀ hb he'⟩)
namespace BadPole
variable {k : Type u} [Field k] {r : ℕ} {s : GKGraph.selectCols r}
variable (B : BadPole k r (GKGraph.universalMinor k r s))
def matrices : Fin 6 → GKGraph.Mat B.V r := fun i => B.f.mapMatrix (GKGraph.gmat k r i)
theorem det_ne_zero : (B.matrices 0).det ≠ 0 := by
  rw [matrices,←AlgHom.map_det,GKGraph.det_gmat]
  exact (map_ne_zero_iff _ B.inj).mpr (GKGraph.gdelta_ne_zero k r)
theorem matrix_relations : GKGraph.Relations r B.matrices := by
  refine ⟨?_,?_,?_⟩
  · exact (map_mul ..).symm.trans ((congrArg B.f.mapMatrix (GKGraph.ring_Y k r)).trans (map_mul ..))
  · exact (map_mul ..).symm.trans ((congrArg B.f.mapMatrix (GKGraph.ring_Z k r)).trans (map_mul ..))
  · simpa only [matrices,map_sub,map_mul] using congrArg B.f.mapMatrix (GKGraph.ring_comm_left k r).symm
theorem same_minor_strict :
    addVal B.V (GKGraph.fullMinor r (B.matrices 0) (B.matrices 1) (B.matrices 2) s) <
      addVal B.V ((B.matrices 0).det^(r-1)) := by
  have e := B.equation
  have hh : B.f (GKGraph.universalMinor k r s) =
      GKGraph.fullMinor r (B.matrices 0) (B.matrices 1) (B.matrices 2) s :=
    GKGraph.fullMinor_map r B.f.toRingHom _ _ _ _
  have hd : B.f (GKGraph.gdelta k r) = (B.matrices 0).det := by
    rw [←GKGraph.det_gmat,AlgHom.map_det]; rfl
  rw [hh,hd] at e
  exact strict_value_of_nonunit_mul B.w _ _ B.nonunit (pow_ne_zero _ B.det_ne_zero) e
end BadPole
end GKDivisor
end
noncomputable section
namespace DivisorG3
open Module Submodule LinearMap Matrix Polynomial
open scoped Matrix
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
def liftEnd (P Y Y' : Matrix ι ι R) (sy : Y*P=P*Y') : End R (QP P) :=
  P.mulVecLin.range.mapQ _ Y.mulVecLin <| by
    rintro _ ⟨u,rfl⟩
    refine ⟨Y' *ᵥ u,?_⟩
    change P *ᵥ (Y' *ᵥ u) = Y *ᵥ (P *ᵥ u)
    simp only [mulVec_mulVec,sy]
omit [DecidableEq ι] in
theorem lift_apply (P Y Y' : Matrix ι ι R) (sy : Y*P=P*Y') (v) :
    liftEnd P Y Y' sy (P.mulVecLin.range.mkQ v) = P.mulVecLin.range.mkQ (Y *ᵥ v) := rfl
omit [DecidableEq ι] in
theorem lift_comm (P Y Y' Z Z' C : Matrix ι ι R) (sy : Y*P=P*Y') (sz : Z*P=P*Z')
    (sc : Y*Z-Z*Y=P*C) : Commute (liftEnd P Y Y' sy) (liftEnd P Z Z' sz) := by
  apply LinearMap.ext; intro w
  obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  change P.mulVecLin.range.mkQ (Y *ᵥ (Z *ᵥ v)) = P.mulVecLin.range.mkQ (Z *ᵥ (Y *ᵥ v))
  rw [← sub_eq_zero,←map_sub]; apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨C *ᵥ v,?_⟩
  change P *ᵥ (C *ᵥ v) = Y *ᵥ (Z *ᵥ v) - Z *ᵥ (Y *ᵥ v)
  rw [mulVec_mulVec,mulVec_mulVec,mulVec_mulVec,←sub_mulVec,sc]
theorem power_intertwines (P Y : Matrix ι ι R) (y : End R (QP P))
    (hy : ∀ v, y (P.mulVecLin.range.mkQ v)=P.mulVecLin.range.mkQ (Y *ᵥ v)) (a : ℕ) (v) :
    (y^a) (P.mulVecLin.range.mkQ v) = P.mulVecLin.range.mkQ ((Y^a) *ᵥ v) := by
  induction a generalizing v with
  | zero => simp
  | succ a ih =>
    rw [pow_succ',pow_succ',Module.End.mul_apply,ih,hy,mulVec_mulVec]
theorem poly_intertwines (P Y : Matrix ι ι R) (y : End R (QP P))
    (hy : ∀ v, y (P.mulVecLin.range.mkQ v)=P.mulVecLin.range.mkQ (Y *ᵥ v)) (p : R[X]) (v) :
    (aeval y p) (P.mulVecLin.range.mkQ v) = P.mulVecLin.range.mkQ ((aeval Y p) *ᵥ v) := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add,LinearMap.add_apply,add_mulVec,hf,hg]
  | monomial n c =>
    rw [aeval_monomial,aeval_monomial,←Algebra.smul_def,←Algebra.smul_def,
      LinearMap.smul_apply,smul_mulVec,map_smul,power_intertwines _ _ _ hy]
theorem local_charpoly (P Y Y' : Matrix ι ι R) (sy : Y*P=P*Y') :
    aeval (liftEnd P Y Y' sy) Y.charpoly = 0 := by
  apply LinearMap.ext; intro w
  obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  simpa [Matrix.aeval_self_charpoly] using poly_intertwines P Y _ (lift_apply P Y Y' sy) Y.charpoly v
def evalAll (P : Matrix ι ι R) : End R (QP P) →ₗ[R] (ι → QP P) :=
  { toFun := fun f j => f (P.mulVecLin.range.mkQ ((Pi.basisFun R ι) j))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
omit [DecidableEq ι] in
theorem evalAll_inj (P : Matrix ι ι R) : Function.Injective (evalAll P) := by
  intro f g eq
  have h : f.comp P.mulVecLin.range.mkQ = g.comp P.mulVecLin.range.mkQ :=
    (Pi.basisFun R ι).ext fun j => congrFun eq j
  apply LinearMap.ext; intro w; obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  exact LinearMap.congr_fun h v
variable [Nontrivial R]
theorem box_image_eq (P Y Y' Z Z' C : Matrix ι ι R) (sy : Y*P=P*Y') (sz : Z*P=P*Z')
    (sc : Y*Z-Z*Y=P*C) :
    ((Algebra.adjoin R ({liftEnd P Y Y' sy,liftEnd P Z Z' sz}:Set _)).toSubmodule).map (evalAll P) =
    wordImage P (box Y Z (Fintype.card ι) (Fintype.card ι)) := by
  let y := liftEnd P Y Y' sy
  let z := liftEnd P Z Z' sz
  have hb := adjoin_box y z (lift_comm _ _ _ _ _ _ sy sz sc) Y.charpoly Z.charpoly
    Y.charpoly_monic Z.charpoly_monic (local_charpoly _ _ _ sy) (local_charpoly _ _ _ sz)
  rw [Matrix.charpoly_natDegree_eq_dim,Matrix.charpoly_natDegree_eq_dim] at hb
  change (Algebra.adjoin R ({y,z}:Set _)).toSubmodule.map (evalAll P) = _
  rw [hb,Submodule.map_span,←Set.range_comp,wordImage]
  congr 2; funext ij j
  change (y^ij.1.val) ((z^ij.2.val) (P.mulVecLin.range.mkQ ((Pi.basisFun R ι) j))) =
    P.mulVecLin.range.mkQ ((Y^ij.1.val * Z^ij.2.val).col j)
  rw [power_intertwines _ _ _ (lift_apply P Z Z' sz),power_intertwines _ _ _ (lift_apply P Y Y' sy),mulVec_mulVec]
  simp [Pi.basisFun_apply]
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module Matrix IsDiscreteValuationRing
variable {V ι : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Fintype ι] [DecidableEq ι]
abbrev wordLattice (P Y Z : Matrix ι ι V) := blockColumns P (box Y Z (Fintype.card ι) (Fintype.card ι))
abbrev actor (P Y Y' Z Z' : Matrix ι ι V) (sy : Y*P=P*Y') (sz : Z*P=P*Z') :=
  Algebra.adjoin V ({liftEnd P Y Y' sy,liftEnd P Z Z' sz}:Set _)
theorem actor_ledger (P Y Y' Z Z' C : Matrix ι ι V) (hp : P.det≠0) (sy : Y*P=P*Y')
    (sz : Z*P=P*Z') (sc : Y*Z-Z*Y=P*C) :
    length V (colQuot (wordLattice P Y Z)) + length V (actor P Y Y' Z Z' sy sz) =
      Fintype.card ι * length V (QP P) := by
  let A := actor P Y Y' Z Z' sy sz
  let B := box Y Z (Fintype.card ι) (Fintype.card ι)
  have he : length V A.toSubmodule = length V (A.toSubmodule.map (evalAll P)) :=
    LinearEquiv.length_eq (R:=V) (Submodule.equivMapOfInjective (evalAll P) (evalAll_inj P) A.toSubmodule)
  change length V A = length V (A.toSubmodule.map (evalAll P)) at he
  rw [show A.toSubmodule.map (evalAll P)=wordImage P B from box_image_eq _ _ _ _ _ _ sy sz sc] at he
  change length V (colQuot (blockColumns P B)) + length V A = _
  rw [he,
    ←(intrinsic_colength _ _ (block_minor_nonzero P hp B)).1]
  exact block_index P hp B
private theorem ledger_lt (r : ℕ) (hr : 0<r) (h b n : ℕ∞) (hf : n≠⊤) (e : h+b=r*n) :
    n<b ↔ h<(r-1) • n := by
  lift n to ℕ using hf
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hh : h≠⊤ := by intro ht; rw [ht,top_add] at e; exact ENat.natCast_ne_top ((r+1)*n) (by exact_mod_cast e.symm)
  have bh : b≠⊤ := by intro ht; rw [ht,add_top] at e; exact ENat.natCast_ne_top ((r+1)*n) (by exact_mod_cast e.symm)
  lift h to ℕ using hh
  lift b to ℕ using bh
  simp only [Nat.succ_sub_one,nsmul_eq_mul]
  have en : h+b=(r+1)*n := by exact_mod_cast e
  suffices n<b ↔ h<r*n by exact_mod_cast this
  rw [Nat.add_mul,one_mul] at en
  omega
theorem bad_iff_minor (P Y Y' Z Z' C : Matrix ι ι V) (hp : P.det≠0) (hr : 0<Fintype.card ι)
    (sy : Y*P=P*Y') (sz : Z*P=P*Z') (sc : Y*Z-Z*Y=P*C) :
    length V (QP P) < length V (actor P Y Y' Z Z' sy sz) ↔
    ∃ j, addVal V ((wordLattice P Y Z).submatrix id j).det < addVal V (P.det^(Fintype.card ι-1)) := by
  let B := box Y Z (Fintype.card ι) (Fintype.card ι)
  rw [←intrinsic_witness _ _ (block_minor_nonzero P hp B),addVal_pow,←intrinsic_square P hp]
  exact ledger_lt _ hr _ _ _ (Module.length_ne_top_iff.mpr (intrinsic_colength P id (by exact hp)).2)
    (actor_ledger _ _ _ _ _ _ hp sy sz sc)
end DivisorG3
end
noncomputable section
namespace GKGraph
variable (k : Type u) [Field k] {F : Type u} [Field F] [Algebra k F]
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem trdeg_adjoin_family {ι : Type} [Fintype ι] (x : ι → F) :
    Algebra.trdeg k (IntermediateField.adjoin k (Set.range x)) ≤ (Fintype.card ι : ℕ) := by
  let S := Set.range x
  have hi : Algebra.IsAlgebraic (Algebra.adjoin k S) (IntermediateField.adjoin k S) := inferInstance
  change Algebra.trdeg k (IntermediateField.adjoin k S) ≤ _
  rw [← trdeg_add_eq k (Algebra.adjoin k S) (A := IntermediateField.adjoin k S),
      trdeg_eq_zero_iff.2 hi, add_zero]
  dsimp only [S]
  rw [Algebra.adjoin_range_eq_range_aeval]
  let f := (MvPolynomial.aeval x : MvPolynomial ι k →ₐ[k] F)
  have hf : Function.Surjective f.rangeRestrict := by rintro ⟨_,y,rfl⟩; exact ⟨y,rfl⟩
  have h := trdeg_le_of_surjective f.rangeRestrict hf
  simpa [MvPolynomial.trdeg_of_isDomain] using h
variable (r : ℕ) (φ : ring k r →ₐ[k] F)
def residueCoordinates := IntermediateField.adjoin k (Set.range (φ ∘ gcoord k r))
def reducedMatrices (i : Fin 6) := φ.mapMatrix (gmat k r i)
theorem reduced_entry (l : Fin 6) (i j : Fin r) :
    reducedMatrices k r φ l i j = φ (gcoord k r (l,i,j)) := rfl
def pairField {n : ℕ} (center : Fin 2 → F) (u : Fin n → F) :=
  IntermediateField.adjoin k (Set.range (Sum.elim center u))
theorem joint_coordinate_budget {s t : ℕ} (center : Fin 2 → F)
    (u : Fin s → F) (v : Fin t → F)
    (h0 : reducedMatrices k r φ 0 = 0)
    (h1 : ∀ i j, reducedMatrices k r φ 1 i j ∈ pairField k center u)
    (h2 : ∀ i j, reducedMatrices k r φ 2 i j ∈ pairField k center u)
    (h3 : ∀ i j, reducedMatrices k r φ 3 i j ∈ pairField k center v)
    (h4 : ∀ i j, reducedMatrices k r φ 4 i j ∈ pairField k center v) :
    Algebra.trdeg k (residueCoordinates k r φ) ≤ (2 + s + t + r*r : ℕ) := by
  let q := fun z : Fin r × Fin r => reducedMatrices k r φ 5 z.1 z.2
  let w := Sum.elim center (Sum.elim u (Sum.elim v q))
  let E := IntermediateField.adjoin k (Set.range w)
  have hw : ∀ j, w j ∈ E := fun j => IntermediateField.subset_adjoin _ _ ⟨j,rfl⟩
  have hu : pairField k center u ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl i => exact hw (.inl i)
    | inr i => exact hw (.inr (.inl i))
  have hv : pairField k center v ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl i => exact hw (.inl i)
    | inr i => exact hw (.inr (.inr (.inl i)))
  have he : residueCoordinates k r φ ≤ E := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨⟨p,i,j⟩,rfl⟩
    change reducedMatrices k r φ p i j ∈ E
    fin_cases p
    · exact (congrFun (congrFun h0 i) j).symm ▸ E.zero_mem
    · exact hu (h1 _ _)
    · exact hu (h2 _ _)
    · exact hv (h3 _ _)
    · exact hv (h4 _ _)
    · exact hw (.inr (.inr (.inr (i,j))))
  refine (trdeg_le_of_injective (IntermediateField.inclusion he)
    (IntermediateField.inclusion he).injective).trans ?_
  simpa [E,w,Fintype.card_sum,Fintype.card_prod,Nat.add_assoc] using trdeg_adjoin_family k w
end GKGraph
end
noncomputable section
namespace GKDivisor
local instance BadPole.instCr2 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom2 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr2 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg2 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
variable {k : Type u} [Field k] {r : ℕ}
open IsDiscreteValuationRing
def BadDatum {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (T : Fin 6 → GKGraph.Mat V r) (rel : GKGraph.Relations r T) : Prop :=
  Module.length V (DivisorG3.QP (T 0)) <
    Module.length V (DivisorG3.actor (T 0) (T 1) (T 3) (T 2) (T 4) rel.y.symm rel.z.symm)
theorem badDatum_iff_strict {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (T : Fin 6 → GKGraph.Mat V r) (rel : GKGraph.Relations r T) (hd : (T 0).det ≠ 0)
    (hr : 0 < r) :
    BadDatum T rel ↔ ∃ s, addVal V (GKGraph.fullMinor r (T 0) (T 1) (T 2) s) <
      addVal V ((T 0).det^(r-1)) := by
  let M := fun (m : ℕ) => ∃ j : (Fin r × Fin r) → (Fin r × Fin r) ⊕ (Fin m × Fin m),
    addVal V (((DivisorG3.blockColumns (T 0) (DivisorG3.box (T 1) (T 2) m m)).submatrix id j).det) <
      addVal V ((T 0).det^(m-1))
  have hh : BadDatum T rel ↔ M (Fintype.card (Fin r)) :=
    DivisorG3.bad_iff_minor (T 0) (T 1) (T 3) (T 2) (T 4) (T 5) hd
      (by simpa using hr) rel.y.symm rel.z.symm rel.comm.symm
  rw [Fintype.card_fin] at hh
  exact hh
namespace BadPole
variable {s : GKGraph.selectCols r} (B : BadPole k r (GKGraph.universalMinor k r s))
def residualMap := (IsScalarTower.toAlgHom k B.V (IsLocalRing.ResidueField B.V)).comp B.f
open scoped IntermediateField.algebraAdjoinAdjoin in
theorem field_count :
    Algebra.trdeg k (GKGraph.residueCoordinates k r B.residualMap) + 1 = (3*r*r : ℕ) := by
  let S := Set.range (B.residualMap ∘ GKGraph.gcoord k r)
  have hi : Algebra.IsAlgebraic (Algebra.adjoin k S) (IntermediateField.adjoin k S) := inferInstance
  change Algebra.trdeg k (IntermediateField.adjoin k S) + 1 = _
  rw [← trdeg_add_eq k (Algebra.adjoin k S) (A := IntermediateField.adjoin k S),
    trdeg_eq_zero_iff.mpr hi, add_zero]
  exact B.count
end BadPole
end GKDivisor
end
noncomputable section
namespace GKDivisor.Jet
open PowerSeries IsDiscreteValuationRing
theorem series_value {F : Type*} [Field F] (f : PowerSeries F) : addVal _ f = f.order := by
  rw [PowerSeries.order_eq_emultiplicity_X,addVal,multiplicity_addValuation_apply]
  exact emultiplicity_eq_of_associated_left
    (associated_of_irreducible _ (PowerSeries.X_irreducible (R:=F)) (Classical.choose_spec (exists_prime _)).irreducible)
theorem count_extension {k F E : Type u} [Field k] [Field F] [Field E] [Algebra k F] [Algebra k E]
    {ι : Type*} (e : F →ₐ[k] E) (x : ι → F) :
    Algebra.trdeg k (Algebra.adjoin k (Set.range (e ∘ x))) =
      Algebra.trdeg k (Algebra.adjoin k (Set.range x)) := by
  rw [Set.range_comp,← AlgHom.map_adjoin]
  exact (Subalgebra.equivMapOfInjective (Algebra.adjoin k (Set.range x)) e e.injective).trdeg_eq.symm
end GKDivisor.Jet
end
noncomputable section
namespace DVRMinimal
open Polynomial
theorem finiteJet_section {k B F : Type*} [Field k]
    [CommRing B] [Field F] [Algebra k B] [Algebra k F] [Algebra.FormallySmooth k F] (q : B →ₐ[k] F)
    (hq : Function.Surjective q) (hn : IsNilpotent (RingHom.ker q.toRingHom)) :
    ∃ s : F →ₐ[k] B, ∀ a, q (s a) = a := by
  exact ⟨Algebra.FormallySmooth.liftOfSurjective (AlgHom.id k F) q hq hn,
    Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _⟩
theorem polynomial_jet (B F : Type*) [CommRing B] [Field F] (q : B →+* F)
    (s : F →+* B) (hs : ∀ a, q (s a)=a) (u : B)
    (hk : RingHom.ker q = Ideal.span {u}) (hn : IsNilpotent u) :
    Function.Surjective (Polynomial.eval₂RingHom s u) := by
  obtain ⟨N,hN⟩ := hn
  have aux (j : ℕ) (x : B) : ∃ p : F[X], ∃ v : B,
      x = (Polynomial.eval₂RingHom s u) p + u^j*v := by
    induction j generalizing x with
    | zero => exact ⟨0,x,by simp⟩
    | succ j ih =>
      have hz : x-s (q x) ∈ RingHom.ker q := by
        rw [RingHom.mem_ker,map_sub,hs,sub_self]
      rw [hk,Ideal.mem_span_singleton] at hz
      obtain ⟨b,hb⟩ := hz
      obtain ⟨p,v,hv⟩ := ih b
      refine ⟨C (q x)+X*p,v,?_⟩
      simp only [map_add,map_mul,coe_eval₂RingHom,eval₂_C,eval₂_X,pow_succ']
      rw [hv] at hb; change x = s (q x)+u*((eval₂RingHom s u) p) + (u*u^j)*v; linear_combination hb
  intro x
  obtain ⟨p,v,hp⟩ := aux N x
  exact ⟨p,by simpa [hN] using hp.symm⟩
theorem coefficient_truncation {k V : Type*} [Field k] [CommRing V]
    [Algebra k V] (m : Ideal V) [m.IsMaximal] [Algebra.FormallySmooth k (V ⧸ m)] (N : ℕ) (hN : 0<N) :
    ∃ s : (V ⧸ m) →ₐ[k] (V ⧸ m^N), ∀ a,
        Ideal.Quotient.factorₐ k (Ideal.pow_le_self hN.ne' : m^N ≤ m) (s a)=a := by
  letI : Field (V ⧸ m) := Ideal.Quotient.field m
  let q := Ideal.Quotient.factorₐ k (Ideal.pow_le_self hN.ne' : m^N ≤ m)
  apply finiteJet_section q
  · exact Ideal.Quotient.factor_surjective (Ideal.pow_le_self hN.ne' : m^N ≤ m)
  · change IsNilpotent (RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hN.ne' : m^N ≤ m)))
    refine ⟨N,?_⟩
    rw [Ideal.Quotient.factor_ker,←Ideal.map_pow,Ideal.map_quotient_self]; rfl
end DVRMinimal
end
noncomputable section
namespace DVRMinimal
open Polynomial Ideal
theorem jet_exact_ker {F B : Type*} [Field F] [CommRing B] (s : F →+* B)
    (u : B) (N : ℕ) (hN : u^N=0) (hlt : ∀ j < N, u^j ≠ 0) :
    RingHom.ker (Polynomial.eval₂RingHom s u) = Ideal.span {(X:F[X])^N} := by
  let f := Polynomial.eval₂RingHom s u
  have hu : f X = u := eval₂_X ..
  let g := Submodule.IsPrincipal.generator (RingHom.ker f)
  have hg : RingHom.ker f = Ideal.span {g} := (Ideal.span_singleton_generator _).symm
  have he : (X:F[X])^N ∈ RingHom.ker f := by rw [RingHom.mem_ker,map_pow,hu,hN]
  have hd : g ∣ X^N := Ideal.mem_span_singleton.mp (hg ▸ he)
  obtain ⟨j,hj,ha⟩ := (dvd_prime_pow (Polynomial.prime_X (R:=F)) N).mp hd
  have eq : RingHom.ker f = Ideal.span {(X:F[X])^j} := hg.trans (Ideal.span_singleton_eq_span_singleton.mpr ha)
  have hz : (X:F[X])^j ∈ RingHom.ker f := eq ▸ Ideal.subset_span (Set.mem_singleton _)
  rw [RingHom.mem_ker,map_pow,hu] at hz
  have hje : j = N := le_antisymm hj (le_of_not_gt (fun h => hlt j h hz))
  rwa [hje] at eq
theorem jetRingEquiv {B F : Type*} [CommRing B] [Field F] (q : B →+* F)
    (s : F →+* B) (hs : ∀ a,q (s a)=a) (u : B)
    (hk : RingHom.ker q = Ideal.span {u}) (N : ℕ) (hN : u^N=0)
    (hlt : ∀ j<N, u^j≠0) :
    ∃ e : (F[X] ⧸ Ideal.span {(X:F[X])^N}) ≃+* B,
      ∀ p : F[X], e (Ideal.Quotient.mk _ p) = (eval₂RingHom s u) p := by
  let f := eval₂RingHom s u
  let h := jet_exact_ker s u N hN hlt
  let e := (Ideal.quotEquivOfEq h.symm).trans
    (RingHom.quotientKerEquivOfSurjective (polynomial_jet B F q s hs u hk ⟨N,hN⟩))
  exact ⟨e,fun p => rfl⟩
end DVRMinimal
end
noncomputable section
namespace DVRMinimal
open Polynomial
variable {k V : Type*} [Field k] [CommRing V] [IsDomain V] [Algebra k V]
theorem uniformizer_jet_iso (k : Type*) [Field k] [Algebra k V] (u : V) (hu : Irreducible u)
    (m : Ideal V) [m.IsMaximal] [Algebra.FormallySmooth k (V ⧸ m)] (hm : m=Ideal.span {u}) (N : ℕ) (hn : 0<N) :
    ∃ e : ((V ⧸ m)[X] ⧸ Ideal.span {(X:(V ⧸ m)[X])^N}) ≃+* (V ⧸ m^N),
      e (Ideal.Quotient.mk _ X) = Ideal.Quotient.mk (m^N) u ∧
      ∀ a : V ⧸ m, Ideal.Quotient.factor (Ideal.pow_le_self hn.ne' : m^N ≤ m)
          (e (Ideal.Quotient.mk _ (C a))) = a := by
  letI := Ideal.Quotient.field m
  let a := Ideal.Quotient.mk (m^N)
  let t := a u
  let q := Ideal.Quotient.factor (Ideal.pow_le_self hn.ne' : m^N ≤ m)
  obtain ⟨s,hs⟩ := coefficient_truncation (k:=k) m N hn
  have hk : RingHom.ker q = Ideal.span {t} := by
    rw [Ideal.Quotient.factor_ker]
    calc m.map a = (Ideal.span {u}).map a := congrArg (Ideal.map a) hm
         _ = Ideal.span {t} := by rw [Ideal.map_span, Set.image_singleton]
  have ht (j : ℕ) : t^j=0 ↔ N≤j := by
    change (a u)^j=0 ↔ _
    rw [← map_pow,Ideal.Quotient.eq_zero_iff_mem,hm,Ideal.span_singleton_pow,Ideal.mem_span_singleton]
    exact pow_dvd_pow_iff hu.ne_zero hu.not_isUnit
  obtain ⟨e,he⟩ := jetRingEquiv q s.toRingHom hs t hk N ((ht N).mpr le_rfl)
    (fun j hj => fun z => (not_le_of_gt hj) ((ht j).mp z))
  refine ⟨e,?_,?_⟩
  · rw [he,coe_eval₂RingHom,eval₂_X]
  · intro c; rw [he,coe_eval₂RingHom,eval₂_C]; exact hs c
end DVRMinimal
end
noncomputable section
namespace DVRMinimal
open Polynomial
variable (F : Type*) [Field F] (N : ℕ)
def polyToSeriesJet := (Ideal.Quotient.mk (Ideal.span {PowerSeries.X^N} : Ideal (PowerSeries F))).comp
  (Polynomial.coeToPowerSeries.ringHom : F[X] →+* PowerSeries F)
theorem seriesJet_ker : RingHom.ker (polyToSeriesJet F N)=Ideal.span {(X:F[X])^N} := by
  ext p
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk _ (p : PowerSeries F)=0 ↔ p∈_
  rw [Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton,Ideal.mem_span_singleton,
    Polynomial.X_pow_dvd_iff,PowerSeries.X_pow_dvd_iff]
  simp only [Polynomial.coeff_coe]
theorem seriesJet_surj : Function.Surjective (polyToSeriesJet F N) := by
  rintro y
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨f.trunc N,?_⟩
  change Ideal.Quotient.mk _ (f.trunc N : PowerSeries F)=Ideal.Quotient.mk _ f
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton,PowerSeries.X_pow_dvd_iff]
  intro i hi
  rw [map_sub,PowerSeries.coeff_coe_trunc_of_lt hi,sub_self]
def polySeriesJetEquiv :
    (F[X] ⧸ Ideal.span {(X:F[X])^N}) ≃+* PowerSeries F ⧸ Ideal.span {(PowerSeries.X:PowerSeries F)^N} :=
  (Ideal.quotEquivOfEq (seriesJet_ker F N).symm).trans
    (RingHom.quotientKerEquivOfSurjective (seriesJet_surj F N))
theorem polySeriesJetEquiv_apply (p : F[X]) :
    polySeriesJetEquiv F N (Ideal.Quotient.mk _ p)=Ideal.Quotient.mk _ (p : PowerSeries F) := rfl
end DVRMinimal
end
noncomputable section
namespace DVRMinimal
open Ideal
abbrev JetI {R : Type*} [CommRing R] (t : R) (N : ℕ) := Ideal.span {t^N}
abbrev jetMk {R : Type*} [CommRing R] (t : R) (N : ℕ) := Ideal.Quotient.mk (JetI t N)
theorem jet_dvd {R : Type*} [CommRing R] (t a : R) {j N : ℕ} (hj : j ≤ N) :
    (jetMk t N t)^j ∣ jetMk t N a ↔ t^j ∣ a := by
  constructor
  · rintro ⟨w,h⟩
    obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective w
    have hz : jetMk t N (a-t^j*v)=0 := by rw [map_sub,map_mul,map_pow,h,sub_self]
    have hd : t^N ∣ a-t^j*v := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hz)
    have he := (pow_dvd_pow t hj).trans hd
    exact (dvd_sub_left (dvd_mul_right (t^j) v)).mp he
  · intro d
    simpa only [map_pow] using map_dvd (jetMk t N) d
theorem jet_div_preserved {R S : Type*} [CommRing R] [CommRing S] {t : R} {u : S} {N : ℕ}
    (e : R ⧸ JetI t N ≃+* S ⧸ JetI u N) (et : e (jetMk t N t) = jetMk u N u)
    {a : R} {b : S} (hab : e (jetMk t N a) = jetMk u N b) {j : ℕ} (hj : j≤N) :
    t^j ∣ a ↔ u^j ∣ b := by
  rw [←jet_dvd t a hj,←jet_dvd u b hj,←hab,←et]
  constructor
  · exact fun h => by simpa only [map_pow] using map_dvd e h
  · exact fun h => by simpa only [map_pow,e.symm_apply_apply] using map_dvd e.symm h
open IsDiscreteValuationRing PowerSeries in
theorem exact_preserved_order {R F : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field F] {t : R} (ht : Irreducible t) {N : ℕ}
    (e : R ⧸ JetI t N ≃+* PowerSeries F ⧸ JetI X N)
    (et : e (jetMk t N t) = jetMk X N X)
    {a : R} {b : PowerSeries F} (hab : e (jetMk t N a)=jetMk X N b)
    {j : ℕ} (ha : addVal R a=j) (hj : j<N) : b.order=j := by
  have eq (i : ℕ) (hi : i≤N) : (i:ℕ∞)≤(j:ℕ∞) ↔ (i:ℕ∞)≤b.order := by
    nth_rw 1 [←ht.addVal_pow i]
    rw [←ha,addVal_le_iff_dvd]
    exact (jet_div_preserved e et hab hi).trans (X_pow_dvd_iff.trans nat_le_order_iff.symm)
  apply le_antisymm _ ((eq j hj.le).mp le_rfl)
  by_contra! H
  have next : (↑(j+1):ℕ∞)≤b.order := Order.add_one_le_of_lt H
  exact (not_le_of_gt (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self j) : (j:ℕ∞)<↑(j+1))) ((eq (j+1) hj).mpr next)
end DVRMinimal
end
noncomputable section
namespace DVRMinimal
open Polynomial
open scoped PowerSeries
variable {V : Type*} [CommRing V] [IsDomain V]
theorem dvrJetTransfer (k : Type*) [Field k] [Algebra k V]
    (t : V) (ht : Irreducible t) (m : Ideal V) [m.IsMaximal] [Algebra.FormallySmooth k (V ⧸ m)] (hm : m=Ideal.span {t})
    (N : ℕ) (hN : 0<N) :
    let F := V ⧸ m
    ∃ e : (V ⧸ JetI t N) ≃+* (PowerSeries F ⧸ JetI PowerSeries.X N),
      e (jetMk t N t) = jetMk PowerSeries.X N PowerSeries.X ∧
        ∀ (a : V) (b : PowerSeries F), e (jetMk t N a) = jetMk PowerSeries.X N b →
          PowerSeries.constantCoeff b = Ideal.Quotient.mk m a := by
  letI := Ideal.Quotient.field m
  let F := V ⧸ m
  obtain ⟨e0,ex,ec⟩ := uniformizer_jet_iso k t ht m hm N hN
  have hI : m^N = JetI t N := by rw [hm,Ideal.span_singleton_pow]
  let etr := Ideal.quotEquivOfEq hI
  let pl := polySeriesJetEquiv F N
  let e := etr.symm.trans (e0.symm.trans pl)
  have he (p : F[X]) : e (etr (e0 (Ideal.Quotient.mk _ p))) =
      jetMk PowerSeries.X N (p : PowerSeries F) := by
    simp only [e,RingEquiv.trans_apply,etr.symm_apply_apply,e0.symm_apply_apply]
    rfl
  have hmk (v : V) : etr (Ideal.Quotient.mk (m^N) v) = jetMk t N v := rfl
  have het : e (jetMk t N t)=jetMk PowerSeries.X N PowerSeries.X := by
    have h := he (X : F[X]); rw [ex,hmk,Polynomial.coe_X] at h; exact h
  refine ⟨e,het,?_⟩
  intro a b hab
  let c := Ideal.Quotient.mk m a
  obtain ⟨v,hv⟩ := Ideal.Quotient.mk_surjective (e0 (Ideal.Quotient.mk _ (C c)))
  have hc : Ideal.Quotient.mk m v=c := by
    have h := ec c
    rw [←hv] at h; exact h
  have hc' : e (jetMk t N v)=jetMk PowerSeries.X N (PowerSeries.C c) := by
    have h := he (C c); rw [←hv,hmk,Polynomial.coe_C] at h; exact h
  have ha : t ∣ a-v := by
    apply Ideal.mem_span_singleton.mp
    rw [←hm,←Ideal.Quotient.eq_zero_iff_mem,map_sub,hc,sub_self]
  have hb : PowerSeries.X ∣ b-PowerSeries.C c := by
    have hsub : e (jetMk t N (a-v))=jetMk PowerSeries.X N (b-PowerSeries.C c) := by
      rw [map_sub,map_sub,hab,hc',map_sub]
    have d := (jet_div_preserved e het hsub (j:=1) hN).mp (by simpa using ha)
    simpa using d
  have hz := PowerSeries.X_dvd_iff.mp hb
  rw [map_sub,PowerSeries.constantCoeff_C,sub_eq_zero] at hz
  exact hz
end DVRMinimal
end
noncomputable section
namespace DVRMinimal
open Matrix
open scoped Matrix
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
abbrev MatS (ι R : Type*) := Matrix ι ι R
theorem repairLeft (t : R) (P A L : MatS ι R)
    (h : ∀ i j,t*P.det ∣ (A-P*L) i j) :
    ∃ L₁ : MatS ι R, P*L₁=A ∧ ∀ i j,t ∣ (L₁-L) i j := by
  choose b hb using h
  let B : MatS ι R := Matrix.of b
  have e : A-P*L=(t*P.det) • B := Matrix.ext fun i j => hb i j
  refine ⟨L+t • (P.adjugate*B),?_,?_⟩
  · rw [Matrix.mul_add,Matrix.mul_smul,←Matrix.mul_assoc,Matrix.mul_adjugate,Matrix.smul_mul,
        Matrix.one_mul,smul_smul,←e]; abel
  · intro i j
    rw [add_sub_cancel_left]
    exact ⟨_,rfl⟩
theorem repairSix (t : R) (P Y Z B D C : MatS ι R) (N : ℕ)
    (hprec : t*P.det ∣ t^N)
    (hY : ∀ i j,t^N ∣ (Y*P-P*B) i j)
    (hZ : ∀ i j,t^N ∣ (Z*P-P*D) i j)
    (hC : ∀ i j,t^N ∣ (Y*Z-Z*Y-P*C) i j) :
    ∃ B' D' C' : MatS ι R, Y*P=P*B' ∧ Z*P=P*D' ∧ Y*Z-Z*Y=P*C' ∧
      (∀ i j,t∣(B'-B) i j) ∧ (∀ i j,t∣(D'-D) i j) ∧ (∀ i j,t∣(C'-C) i j) := by
  obtain ⟨B',eB,dB⟩ := repairLeft t P (Y*P) B fun i j => hprec.trans (hY i j)
  obtain ⟨D',eD,dD⟩ := repairLeft t P (Z*P) D fun i j => hprec.trans (hZ i j)
  obtain ⟨C',eC,dC⟩ := repairLeft t P (Y*Z-Z*Y) C fun i j => hprec.trans (hC i j)
  exact ⟨B',D',C',eB.symm,eD.symm,eC.symm,dB,dD,dC⟩
open PowerSeries in
theorem exact_order_precision {k : Type*} [Field k] (p : PowerSeries k) (N : ℕ)
    (ha : p.order < N) : (X:PowerSeries k)*p ∣ X^N := by
  have hp : p ≠ 0 := by intro eq; simp [eq] at ha
  have hlt : p.order.toNat < N := by
    rwa [←coe_toNat_order hp,ENat.natCast_lt_natCast] at ha
  have hd : p.divXPowOrder ∣ (1:PowerSeries k) := (isUnit_divided_by_X_pow_order hp).dvd
  obtain ⟨v,hv⟩ := hd
  let a := p.order.toNat
  let j := N-(a+1)
  have hj : 1+a+j = N := by dsimp [a,j]; omega
  have hfac : X^a*p.divXPowOrder=p := X_pow_order_mul_divXPowOrder
  refine ⟨X^j*v,?_⟩
  calc
    (X : PowerSeries k)^N = X^(1+a+j) := by rw [hj]
    _ = (X*X^a*X^j)*1 := by rw [pow_add,pow_add,pow_one,mul_one]
    _ = X*p*(X^j*v) := by
      calc
        _ = (X*X^a*X^j)*(p.divXPowOrder*v) := congrArg ((X*X^a*X^j)*·) hv
        _ = X*(X^a*p.divXPowOrder)*(X^j*v) := by ring
        _ = _ := congrArg (fun b : PowerSeries k => X*b*(X^j*v)) hfac
end DVRMinimal
end
noncomputable section
namespace DVRMinimal
open scoped Matrix
open GKGraph PowerSeries IsDiscreteValuationRing IsLocalRing
variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable (r : ℕ)
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem six_jet_over (F : Type*) [Field F] (ρ : V →+* F)
    (T : Fin 6 → GKGraph.Mat V r) (hT : Relations r T) (s : selectCols r)
    (u : V) (hu : Irreducible u) (a d N : ℕ) (hA : addVal V (T 0).det=a)
    (hD : addVal V (fullMinor r (T 0) (T 1) (T 2) s)=d)
    (ha : a<N) (hd : d<N)
    (e : V ⧸ JetI u N ≃+* PowerSeries F ⧸ JetI X N)
    (et : e (jetMk u N u)=jetMk X N X)
    (ec : ∀ (x : V) (v : PowerSeries F), e (jetMk u N x)=jetMk X N v → constantCoeff v=ρ x) :
    ∃ S : Fin 6 → GKGraph.Mat (PowerSeries F) r,
      Relations r S ∧ (S 0).det.order=a ∧ (fullMinor r (S 0) (S 1) (S 2) s).order=d ∧
        ∀ l i j, constantCoeff (S l i j) = ρ (T l i j) := by
  classical
  let O := PowerSeries F
  let g := e.toRingHom.comp (jetMk u N)
  let f := jetMk (X : O) N
  choose L hL using fun x : V => (Ideal.Quotient.mk_surjective (g x))
  let A : Fin 6 → GKGraph.Mat O r := fun i => (T i).map L
  have h (i) : f.mapMatrix (A i) = g.mapMatrix (T i) := Matrix.ext fun b c => hL (T i b c)
  have ea : e (jetMk u N (T 0).det) = f (A 0).det := by
    change g (T 0).det=f (A 0).det
    simp only [RingHom.map_det,h]
  have ed : e (jetMk u N (fullMinor r (T 0) (T 1) (T 2) s)) =
      f (fullMinor r (A 0) (A 1) (A 2) s) := by
    change g _=f _
    simp only [fullMinor_map,h]
  have hdet := exact_preserved_order (F:=F) (t:=u) (N:=N) hu e et ea hA ha
  have hminor := exact_preserved_order (F:=F) (t:=u) (N:=N) hu e et ed hD hd
  have hz (B : GKGraph.Mat O r) (hh : f.mapMatrix B=0) :
      ∀ i j,(X : O)^N ∣ B i j := by
    intro i j
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    exact congrArg (fun M : GKGraph.Mat _ r => M i j) hh
  have y : f.mapMatrix (A 1*A 0-A 0*A 3)=0 := by
    rw [map_sub,map_mul,map_mul,h,h,h,←map_mul,←map_mul,hT.y,sub_self]
  have z : f.mapMatrix (A 2*A 0-A 0*A 4)=0 := by
    rw [map_sub,map_mul,map_mul,h,h,h,←map_mul,←map_mul,hT.z,sub_self]
  have c : f.mapMatrix (A 1*A 2-A 2*A 1-A 0*A 5)=0 := by
    rw [map_sub,map_sub,map_mul,map_mul,map_mul,h,h,h,h,←map_mul,←map_mul,←map_sub,←map_mul,hT.comm,sub_self]
  obtain ⟨B,D,C,hB,hD',hC,dB,dD,dC⟩ := repairSix (X : O) (A 0) (A 1) (A 2)
    (A 3) (A 4) (A 5) N (exact_order_precision _ N (hdet ▸ ENat.natCast_lt_natCast.mpr ha))
    (hz _ y) (hz _ z) (hz _ c)
  let S : Fin 6 → GKGraph.Mat O r := ![A 0,A 1,A 2,B,D,C]
  have hec (l i j) : constantCoeff (A l i j)=ρ (T l i j) :=
    ec _ _ (hL _).symm
  have pres (i j : Fin r) (X' : GKGraph.Mat O r) (l) (hx : ∀ i j, X ∣ (X'-A l) i j) :
      constantCoeff (X' i j)=ρ (T l i j) := by
    have hh := X_dvd_iff.mp (hx i j)
    change constantCoeff (X' i j-A l i j)=0 at hh
    rw [map_sub,sub_eq_zero] at hh
    exact hh.trans (hec l i j)
  refine ⟨S,⟨hB.symm,hD'.symm,hC.symm⟩,hdet,hminor,?_⟩
  intro l i j
  fin_cases l
  · exact hec 0 i j
  · exact hec 1 i j
  · exact hec 2 i j
  · exact pres i j B 3 dB
  · exact pres i j D 4 dD
  · exact pres i j C 5 dC
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem actual_six_jet (k : Type*) [Field k] [Algebra k V]
    [Algebra.FormallySmooth k (ResidueField V)]
    (T : Fin 6 → GKGraph.Mat V r) (hT : Relations r T) (s : selectCols r)
    (u : V) (hu : Irreducible u) (a d N : ℕ) (hA : addVal V (T 0).det=a)
    (hD : addVal V (fullMinor r (T 0) (T 1) (T 2) s)=d)
    (ha : a<N) (hd : d<N) :
    ∃ S : Fin 6 → GKGraph.Mat (PowerSeries (ResidueField V)) r,
      Relations r S ∧ (S 0).det.order=a ∧ (fullMinor r (S 0) (S 1) (S 2) s).order=d ∧
        ∀ l i j, constantCoeff (S l i j) = residue V (T l i j) := by
  let m := IsLocalRing.maximalIdeal V
  letI : Algebra.FormallySmooth k (V ⧸ m) := ‹Algebra.FormallySmooth k (ResidueField V)›
  have hm : m=Ideal.span {u} := (irreducible_iff_uniformizer u).mp hu
  obtain ⟨e,et,ec⟩ := dvrJetTransfer k u hu m hm N (by omega)
  exact six_jet_over r (ResidueField V) (residue V) T hT s u hu a d N hA hD ha hd e et ec
end DVRMinimal
end
noncomputable section
namespace GKDivisor.Jet
open PowerSeries IsDiscreteValuationRing
local instance BadPole.instCr3 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom3 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr3 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg3 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
local instance BadPole.instEss3 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra.EssFiniteType k (IsLocalRing.ResidueField P.V) := P.residue_ess
variable {k : Type u} [Field k] {r : ℕ} {s : GKGraph.selectCols r}
def constEntries {E : Type*} [Field E] (T : Fin 6 → GKGraph.Mat (PowerSeries E) r) :
    GKGraph.AllVars r → E := fun z => constantCoeff (T z.1 z.2.1 z.2.2)
structure SeriesPole (k E : Type u) [Field k] [Field E] [Algebra k E]
    (r : ℕ) (s : GKGraph.selectCols r) where
  T : Fin 6 → GKGraph.Mat (PowerSeries E) r
  relations : GKGraph.Relations r T
  det_ne : (T 0).det ≠ 0
  strict : addVal _ (GKGraph.fullMinor r (T 0) (T 1) (T 2) s) < addVal _ ((T 0).det^(r-1))
  count : Algebra.trdeg k (Algebra.adjoin k (Set.range (constEntries T))) + 1 = (3*r*r : ℕ)
theorem pole_orders (B : BadPole k r (GKGraph.universalMinor k r s)) :
    ∃ a d : ℕ, addVal B.V (B.matrices 0).det = a ∧
      addVal B.V (GKGraph.fullMinor r (B.matrices 0) (B.matrices 1) (B.matrices 2) s) = d ∧
      (d:ℕ∞) < (r-1) • (a:ℕ∞) := by
  have hd := B.same_minor_strict
  have hA := B.det_ne_zero
  rw [addVal_pow] at hd
  let n := addVal B.V (B.matrices 0).det
  let v := addVal B.V (GKGraph.fullMinor r (B.matrices 0) (B.matrices 1) (B.matrices 2) s)
  have hn : n ≠ ⊤ := addVal_eq_top_iff.not.mpr hA
  have hv : v ≠ ⊤ := ne_top_of_lt hd
  exact ⟨n.toNat,v.toNat,(ENat.natCast_toNat_eq_self.mpr hn).symm,(ENat.natCast_toNat_eq_self.mpr hv).symm,
    by simpa only [ENat.natCast_toNat_eq_self.mpr hn,ENat.natCast_toNat_eq_self.mpr hv] using hd⟩
theorem realize_series {E : Type u} [Field E] [Algebra k E]
    (B : BadPole k r (GKGraph.universalMinor k r s))
    (e : IsLocalRing.ResidueField B.V →ₐ[k] E)
    (a d : ℕ) (hd : (d:ℕ∞) < (r-1) • (a:ℕ∞))
    (T : Fin 6 → GKGraph.Mat (PowerSeries E) r) (rel : GKGraph.Relations r T)
    (ha : (T 0).det.order = a) (hv : (GKGraph.fullMinor r (T 0) (T 1) (T 2) s).order = d)
    (hc : ∀ l i j, constantCoeff (T l i j) = e (IsLocalRing.residue B.V (B.matrices l i j))) :
    ∃ S : SeriesPole k E r s, S.T = T ∧ constEntries S.T = e ∘ B.residualMap ∘ GKGraph.gcoord k r := by
  have se : constEntries T = e ∘ B.residualMap ∘ GKGraph.gcoord k r := by
    funext z
    exact hc z.1 z.2.1 z.2.2
  have he := count_extension e (B.residualMap ∘ GKGraph.gcoord k r)
  have hn : (T 0).det ≠ 0 := by intro eq; rw [eq,PowerSeries.order_zero] at ha; exact ENat.natCast_ne_top a ha.symm
  refine ⟨⟨T, rel, hn, ?_, ?_⟩,rfl,se⟩
  · rw [addVal_pow,series_value,series_value,ha,hv]
    exact hd
  · rw [se,he]
    exact B.count
end GKDivisor.Jet
end
noncomputable section
namespace DVRMinimal
open scoped Matrix
open GKGraph PowerSeries IsDiscreteValuationRing IsLocalRing
variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
theorem order_injective_map {F L : Type*} [Field F] [Field L] (φ : F →+* L)
    {x : PowerSeries F} {j : ℕ} (hj : x.order=j) : (PowerSeries.map φ x).order=j := by
  obtain ⟨ne,h⟩ := PowerSeries.order_eq_nat.mp hj
  apply PowerSeries.order_eq_nat.mpr
  exact ⟨by rwa [coeff_map,ne_eq,map_eq_zero_iff φ φ.injective], fun i hi => by rw [coeff_map,h i hi,map_zero]⟩
theorem actual_closed_jet (r : ℕ) (k : Type*) [Field k] [Algebra k V]
    [Algebra.FormallySmooth k (ResidueField V)]
    (L : Type*) [Field L] (φ : ResidueField V →+* L)
    (T : Fin 6 → GKGraph.Mat V r) (hT : Relations r T) (s : selectCols r)
    (u : V) (hu : Irreducible u) (a d N : ℕ) (hA : addVal V (T 0).det=a)
    (hD : addVal V (fullMinor r (T 0) (T 1) (T 2) s)=d)
    (ha : a<N) (hd : d<N) :
    ∃ S : Fin 6 → GKGraph.Mat (PowerSeries L) r,
      Relations r S ∧ (S 0).det.order=a ∧ (fullMinor r (S 0) (S 1) (S 2) s).order=d ∧
        ∀ l i j, constantCoeff (S l i j) = φ (residue V (T l i j)) := by
  obtain ⟨A,hrel,hp,hm,hres⟩ := actual_six_jet r k T hT s u hu a d N hA hD ha hd
  let g := PowerSeries.map φ
  let S : Fin 6 → GKGraph.Mat (PowerSeries L) r := fun i => g.mapMatrix (A i)
  have s1 : Relations r S := by
    constructor
    · exact (map_mul _ _ _).symm.trans ((congrArg g.mapMatrix hrel.y).trans (map_mul _ _ _))
    · exact (map_mul _ _ _).symm.trans ((congrArg g.mapMatrix hrel.z).trans (map_mul _ _ _))
    · have hh := congrArg g.mapMatrix hrel.comm
      simpa only [S,map_mul,map_sub] using hh
  refine ⟨S,s1,?_,?_,?_⟩
  · change (g.mapMatrix (A 0)).det.order=a
    rw [←RingHom.map_det]; exact order_injective_map φ hp
  · change (fullMinor r (g.mapMatrix _) (g.mapMatrix _) (g.mapMatrix _) s).order=d
    rw [←fullMinor_map]; exact order_injective_map φ hm
  · intro l i j
    change constantCoeff (PowerSeries.map φ (A l i j)) = _
    rw [←coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply,hres]
end DVRMinimal
end
noncomputable section
namespace GKDivisor.Jet
open PowerSeries IsDiscreteValuationRing
local instance BadPole.instCr4 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom4 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr4 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg4 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
local instance BadPole.instEss4 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra.EssFiniteType k (IsLocalRing.ResidueField P.V) := P.residue_ess
variable {k : Type u} [Field k] [PerfectField k] {r : ℕ} {s : GKGraph.selectCols r}
theorem pole_to_extended_series (B : BadPole k r (GKGraph.universalMinor k r s))
    {E : Type u} [Field E] [Algebra k E] (e : IsLocalRing.ResidueField B.V →ₐ[k] E) :
    ∃ S : SeriesPole k E r s, constEntries S.T = e ∘ B.residualMap ∘ GKGraph.gcoord k r := by
  obtain ⟨a,d,ha,hd,hl⟩ := pole_orders B
  obtain ⟨t,ht⟩ := exists_irreducible B.V
  obtain ⟨T,rel,hA,hD,hc⟩ := DVRMinimal.actual_closed_jet r k E e.toRingHom B.matrices B.matrix_relations
    s t ht a d (a+d+1) ha hd (by omega) (by omega)
  obtain ⟨S,_,hs⟩ := realize_series B e a d hl T rel hA hD hc
  exact ⟨S,hs⟩
theorem pole_to_algebraic_closure (B : BadPole k r (GKGraph.universalMinor k r s)) :
    ∃ S : SeriesPole k (AlgebraicClosure (IsLocalRing.ResidueField B.V)) r s,
      constEntries S.T =
        (algebraMap (IsLocalRing.ResidueField B.V) (AlgebraicClosure (IsLocalRing.ResidueField B.V))) ∘
          B.residualMap ∘ GKGraph.gcoord k r := by
  exact pole_to_extended_series B (IsScalarTower.toAlgHom k _ _)
end GKDivisor.Jet
end
noncomputable section
namespace DivisorG3
open PowerSeries Module LinearMap
variable {k : Type*} [Field k]
abbrev O (k : Type*) := PowerSeries k
def firstCoeffs (k : Type*) [Field k] (n : ℕ) : O k →ₗ[k] Fin n → k :=
  LinearMap.pi fun i => PowerSeries.coeff i.val
theorem firstCoeffs_surj (n : ℕ) : Function.Surjective (firstCoeffs k n) := by
  intro c
  refine ⟨PowerSeries.mk fun j => if h : j<n then c ⟨j,h⟩ else 0,?_⟩
  funext i
  simp [firstCoeffs,i.isLt]
theorem firstCoeffs_ker (n : ℕ) :
    (firstCoeffs k n).ker = (Ideal.span ({(PowerSeries.X : O k)^n} : Set _)).restrictScalars k := by
  ext f
  change (fun i : Fin n => coeff i.val f) = 0 ↔ f ∈ Ideal.span _
  rw [Ideal.mem_span_singleton,X_pow_dvd_iff]
  constructor
  · intro h j hj; exact congrFun h ⟨j,hj⟩
  · intro h; funext i; exact h i.val i.isLt
def principalJetEquiv (f : O k) (h : f ≠ 0) :
    (O k ⧸ Ideal.span ({f} : Set _)) ≃ₗ[k] (Fin f.order.toNat → k) := by
  have he : Ideal.span ({f} : Set _) = Ideal.span ({(PowerSeries.X : O k)^f.order.toNat} : Set _) := by
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f:=f)]
    exact Ideal.span_singleton_mul_right_unit (isUnit_divided_by_X_pow_order h) _
  let e := (firstCoeffs k f.order.toNat).quotKerEquivOfSurjective (firstCoeffs_surj _)
  exact (Submodule.Quotient.restrictScalarsEquiv k _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (he ▸ (firstCoeffs_ker _).symm) ≪≫ₗ e
theorem principal_length (f : O k) (h : f≠0) :
    finrank k (O k ⧸ Ideal.span ({f} : Set _)) = f.order.toNat := by
  rw [(principalJetEquiv f h).finrank_eq,Module.finrank_pi,Fintype.card_fin]
theorem principal_finite (f : O k) (h : f≠0) :
    Module.Finite k (O k ⧸ Ideal.span ({f} : Set _)) :=
  Module.Finite.of_surjective (principalJetEquiv f h).symm.toLinearMap (principalJetEquiv f h).symm.surjective
end DivisorG3
end
noncomputable section
namespace DivisorG3
open PowerSeries Module LinearMap Submodule
open scoped Matrix
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev Row (k ι : Type*) := ι → O k
abbrev sq (k ι : Type*) := Matrix ι ι (O k)
def reduceVec (k ι : Type*) [Field k] : Row k ι →ₗ[k] ι → k where
  toFun v i := constantCoeff (v i)
  map_add' v w := by ext; simp
  map_smul' c v := by ext i; change constantCoeff (c • v i) = c * _; rw [PowerSeries.smul_eq_C_mul,map_mul,constantCoeff_C]
omit [Fintype ι] [DecidableEq ι] in
theorem reduceVec_surj : Function.Surjective (reduceVec k ι) := fun u =>
  ⟨fun i => C (u i),funext fun _ => constantCoeff_C _⟩
omit [Fintype ι] [DecidableEq ι] in
theorem reduceVec_ker : (reduceVec k ι).ker = ((times (PowerSeries.X : O k) (Row k ι)).range).restrictScalars k := by
  ext v
  change (fun i => constantCoeff (v i)) = 0 ↔ ∃ w : Row k ι, (fun i => X * w i) = v
  constructor
  · intro h
    choose w hw using fun i => X_dvd_iff.mpr (congrFun h i)
    exact ⟨w,funext fun i => (hw i).symm⟩
  · rintro ⟨v,rfl⟩; funext i; simp
def reduceEquiv : Coker (times (PowerSeries.X : O k) (Row k ι)) ≃ₗ[k] (ι → k) :=
  (Submodule.Quotient.restrictScalarsEquiv k _).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ reduceVec_ker.symm ≪≫ₗ
    (reduceVec k ι).quotKerEquivOfSurjective reduceVec_surj
omit [DecidableEq ι] in
theorem factor_X (P : sq k ι) (hp : ∀ i j, constantCoeff (P i j)=0) :
    ∃ Q : sq k ι, ∀ v, P.mulVecLin v = (PowerSeries.X : O k) • Q.mulVecLin v := by
  choose Q hQ using fun i j => X_dvd_iff.mpr (hp i j)
  refine ⟨Q,fun v => ?_⟩
  have hP : P = (PowerSeries.X : O k) • Q := Matrix.ext fun i j => hQ i j
  rw [hP]
  exact Matrix.smul_mulVec _ _ _
omit [Fintype ι] [DecidableEq ι] in
theorem xReg : Function.Injective (fun v : Row k ι => (PowerSeries.X : O k) • v) := by
  intro v w h
  funext i
  exact mul_left_cancel₀ PowerSeries.X_ne_zero (congrFun h i)
theorem actual_tail (P : sq k ι) (p : P.det≠0) (p0 : ∀ i j, constantCoeff (P i j)=0) :
    ∃ Q : sq k ι, ∃ e : (ι → k) ≃ₗ[k] Tail (PowerSeries.X : O k) P.mulVecLin,
      (∀ v, P.mulVecLin v = (PowerSeries.X : O k) • Q.mulVecLin v) ∧
      (∀ v, (e (reduceVec k ι v)).val = P.mulVecLin.range.mkQ (Q.mulVecLin v)) ∧
      (∀ Y Y' : sq k ι, Y * P = P * Y' → ∀ v,
        (e (reduceVec k ι (Y'.mulVecLin v))).val = P.mulVecLin.range.mkQ (Y.mulVecLin (Q.mulVecLin v))) := by
  obtain ⟨Q,fac⟩ := factor_X P p0
  let inj := Matrix.mulVec_injective_of_det_ne_zero p
  let z := tailEquiv _ _ _ fac inj xReg
  let e := reduceEquiv.symm ≪≫ₗ z.restrictScalars k
  have h (v) : (e (reduceVec k ι v)).val = P.mulVecLin.range.mkQ (Q.mulVecLin v) := by
    have hr : reduceEquiv ((times (PowerSeries.X : O k) (Row k ι)).range.mkQ v) = reduceVec k ι v := rfl
    rw [←hr]; simp only [e,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply]
    exact tail_formula _ _ _ fac inj xReg v
  refine ⟨Q,e,fac,h,?_⟩
  intro Y Y' eq v
  rw [h]
  apply tail_intertwines _ _ _ _ _ fac xReg _ v
  intro w
  change Y *ᵥ (P *ᵥ w) = P *ᵥ (Y' *ᵥ w)
  simp only [Matrix.mulVec_mulVec,eq]
end DivisorG3
end
noncomputable section
namespace GKDivisor.Jet
open PowerSeries DivisorG3 Module LinearMap Submodule
open scoped Matrix
variable {F : Type*} [Field F] {r : ℕ}
abbrev redP (P : Matrix (Fin r) (Fin r) (PowerSeries F)) :=
  (PowerSeries.constantCoeff (R:=F)).mapMatrix P
def cvec : (Fin r → F) →ₗ[F] (Fin r → PowerSeries F) where
  toFun v i := C (v i)
  map_add' _ _ := funext fun _ => map_add ..
  map_smul' x v := by funext i; change C (x * v i) = x • C (v i); rw [map_mul,PowerSeries.smul_eq_C_mul]
section
variable (P : Matrix (Fin r) (Fin r) (PowerSeries F))
variable (t : Module.End F (QP P)) (hx : ∀ w, t w = (PowerSeries.X : PowerSeries F) • w)
def headMap := t.range.mkQ.comp (P.mulVecLin.range.mkQ.restrictScalars F)
def headFromConstants := (headMap P t).comp cvec
end
end GKDivisor.Jet
end
noncomputable section
namespace DivisorG3
open Module PowerSeries
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
theorem series_of_nil (T : End k W) (ht : IsNilpotent T) :
    ∃ ρ : O k →ₐ[k] End k W, ρ X=T ∧ ρ.range=Algebra.adjoin k ({T}:Set _) := by
  let A := Algebra.adjoin k ({T}:Set _)
  let _ : CommRing A := {(inferInstance : Ring A) with mul_comm := fun x y => mul_comm' x y}
  let u : A := ⟨T,Algebra.self_mem_adjoin_singleton k T⟩
  have hu : IsNilpotent u := by obtain ⟨e,he⟩:=ht; exact ⟨e,Subtype.ext he⟩
  let c : PowerSeries A := C u
  have hc : HasSubst c := by change IsNilpotent (constantCoeff (C u)); simpa using hu
  let sub : O k →ₐ[k] PowerSeries A := substAlgHom hc
  let cc : PowerSeries A →ₐ[k] A := {
    toRingHom := constantCoeff
    commutes' := fun x => constantCoeff_C _ }
  let ρ := A.val.comp (cc.comp sub)
  have hx : ρ X=T := by change ↑(constantCoeff (sub X)) = T; rw [show sub X=c from substAlgHom_X hc]; exact congrArg Subtype.val (constantCoeff_C u)
  refine ⟨ρ,hx,le_antisymm ?_ (Algebra.adjoin_le ?_)⟩
  · rintro _ ⟨z,rfl⟩; exact (cc (sub z)).property
  · rintro _ rfl; exact ⟨X,hx⟩
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module IsLocalRing PowerSeries
variable (k : Type*) [Field k]
theorem same_residue : Function.Surjective (algebraMap (ResidueField k) (ResidueField (O k))) := by
  intro a
  obtain ⟨f,rfl⟩ := residue_surjective a
  refine ⟨residue k (constantCoeff f),?_⟩
  rw [ResidueField.algebraMap_residue]
  apply Ideal.Quotient.eq.mpr
  rw [←PowerSeries.ker_coeff_eq_max_ideal]
  change constantCoeff (C (constantCoeff f)-f)=0
  simp
theorem actual_length (W : Type*) [AddCommGroup W] [Module k W] [Module (O k) W]
    [IsScalarTower k (O k) W] [Module.Finite k W] : length (O k) W = finrank k W := by
  have h := IsLocalRing.length_restrictScalars k (O k) W
  rw [Module.length_eq_of_surjective (M:=ResidueField (O k)) (same_residue k)] at h
  simpa [Module.length_eq_finrank] using h.symm
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module PowerSeries LinearMap
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
theorem original_action (T : End k W) (ht : IsNilpotent T) :
    ∃ ρ : O k →ₐ[k] End k W, ∃ _ : Module (O k) W, ∃ _ : IsScalarTower k (O k) W,
      ρ X=T ∧ ρ.range=Algebra.adjoin k ({T}:Set _) ∧
      (∀ s : O k, ∀ w : W, s • w=ρ s w) ∧
      (∃ a : O k, a≠0 ∧ ∀ w : W, a • w=0) ∧
      (∀ Y : End k W, Commute Y T → ∃ y : End (O k) W, y.restrictScalars k=Y) := by
  obtain ⟨ρ,hx,hr⟩ := series_of_nil T ht
  let _ : Module (O k) W := Module.compHom W ρ.toRingHom
  let _ : IsScalarTower k (O k) W := IsScalarTower.of_algebraMap_smul fun c w => by
    change ρ (algebraMap k (O k) c) w = c • w
    rw [ρ.commutes]; rfl
  refine ⟨ρ,inferInstance,inferInstance,hx,hr,fun _ _ => rfl,?_,?_⟩
  · obtain ⟨e,he⟩ := ht
    refine ⟨X^e,pow_ne_zero _ X_ne_zero,fun w => ?_⟩
    change ρ (X^e) w=0
    rw [map_pow,hx,he]; rfl
  · intro Y hY
    refine ⟨{ toFun:=Y
              map_add':=Y.map_add
              map_smul':=fun s w => ?_ },rfl⟩
    change Y (ρ s w) = ρ s (Y w)
    exact LinearMap.congr_fun (Algebra.commute_of_mem_adjoin_singleton_of_commute
      (show ρ s ∈ Algebra.adjoin k ({T}:Set _) from hr ▸ ⟨s,rfl⟩) hY).eq w
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module LinearMap PowerSeries
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [Module (O k) W] [IsScalarTower k (O k) W]
def forgetEnd : End (O k) W →ₐ[k] End k W where
  toFun f := f.restrictScalars k
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_zero' := rfl
  commutes' _ := rfl
abbrev triple (t y z : End k W) := Algebra.adjoin k ({t,y,z}:Set _)
abbrev pair (y z : End (O k) W) := Algebra.adjoin (O k) ({y,z}:Set _)
set_option maxHeartbeats 1000000 in
theorem exact_origin_actor (ρ : O k →ₐ[k] End k W) (T : End k W) (hX : ρ X=T)
    (hr : ρ.range=Algebra.adjoin k ({T}:Set _)) (hρ : ∀ s : O k, ∀ w : W, s • w=ρ s w)
    (y z : End (O k) W) :
    ((pair y z).restrictScalars k).map forgetEnd = triple T (y.restrictScalars k) (z.restrictScalars k) := by
  let D := triple T (y.restrictScalars k) (z.restrictScalars k)
  have ev (s : O k) : forgetEnd (algebraMap (O k) (End (O k) W) s)=ρ s := LinearMap.ext (hρ s)
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    change a ∈ Algebra.adjoin (O k) ({y,z}:Set _) at ha
    change forgetEnd a ∈ D
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rcases Set.mem_insert_iff.mp ha with h|h
      · subst a; exact Algebra.subset_adjoin (Or.inr (Or.inl rfl))
      · have h' := Set.mem_singleton_iff.mp h; subst a; exact Algebra.subset_adjoin (Or.inr (Or.inr rfl))
    | algebraMap s =>
      rw [ev]
      apply Algebra.adjoin_mono (s:=({T}:Set _)) (by rintro u rfl; exact Or.inl rfl)
      rw [←hr]; exact ⟨s,rfl⟩
    | add a b _ _ ha hb => exact D.add_mem ha hb
    | mul a b _ _ ha hb => exact D.mul_mem ha hb
  · apply Algebra.adjoin_le
    intro a ha
    rcases Set.mem_insert_iff.mp ha with h|h
    · subst a; exact ⟨_,(pair y z).algebraMap_mem X,(ev X).trans hX⟩
    · rcases Set.mem_insert_iff.mp h with h|h
      · subst a; exact ⟨y,Algebra.subset_adjoin (by simp),rfl⟩
      · have hh := Set.mem_singleton_iff.mp h; subst a; exact ⟨z,Algebra.subset_adjoin (by simp),rfl⟩
theorem origin_actor_length [FiniteDimensional k W] (ρ : O k →ₐ[k] End k W) (T : End k W) (hX : ρ X=T)
    (hr : ρ.range=Algebra.adjoin k ({T}:Set _)) (hρ : ∀ s : O k, ∀ w : W, s • w=ρ s w)
    (y z : End (O k) W) :
    length (O k) (pair y z) = finrank k (triple T (y.restrictScalars k) (z.restrictScalars k)) := by
  let A := (pair y z).restrictScalars k
  let D := triple T (y.restrictScalars k) (z.restrictScalars k)
  let f := Subalgebra.equivMapOfInjective A forgetEnd (fun _ _ h => LinearMap.ext fun w => congrArg (fun f : End k W => f w) h)
  have he : finrank k (pair y z)=finrank k D := by
    change finrank k A=finrank k (triple T (y.restrictScalars k) (z.restrictScalars k))
    rw [←exact_origin_actor ρ T hX hr hρ y z]
    exact f.toLinearEquiv.finrank_eq
  let e := f.toLinearMap
  let _ : Module.Finite k (pair y z) := Module.Finite.of_injective e f.injective
  exact (actual_length k (pair y z)).trans (congrArg Nat.cast he)
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module PowerSeries
variable {k ι κ : Type*} [Field k] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
abbrev matQuot (A : Matrix ι κ (O k)) := (ι → O k) ⧸ matrixColumnLattice A
omit [DecidableEq κ] in
theorem full_of_minor (A : Matrix ι κ (O k)) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    finrank (O k) (matrixColumnLattice A) = finrank (O k) (ι → O k) := by
  rw [Module.finrank_pi]
  change A.rank = Fintype.card ι
  exact le_antisymm A.rank_le_card_height (Matrix.rank_of_det_ne_zero hs ▸ A.rank_submatrix_le id s)
theorem smith_colength (A : Matrix ι κ (O k)) (s : ι → κ) (hs : (A.submatrix id s).det≠0) :
    ∃ g : O k, g≠0 ∧ allColumnMinorIdeal A = Ideal.span ({g}:Set _) ∧
      finrank k (matQuot A) = g.order.toNat ∧ Module.Finite k (matQuot A) := by
  let b := Pi.basisFun (O k) ι
  let N := matrixColumnLattice A
  have h := full_of_minor A s hs
  let a := Submodule.smithNormalFormCoeffs b h
  have ha (i) : a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h i
  let (i : ι) : FiniteDimensional k (O k ⧸ Ideal.span ({a i}:Set _)) := principal_finite _ (ha i)
  refine ⟨∏ i,a i,Finset.prod_ne_zero_iff.mpr (fun i _ => ha i),?_,?_,?_⟩
  · rw [←latticeVolumeIdeal_matrixColumnLattice, latticeVolumeIdeal_eq_span_smith b _ h]
  · change finrank k ((ι→O k) ⧸ N) = _
    rw [N.finrank_quotient_eq_sum k b h,order_prod,ENat.toNat_sum (fun i _ => order_eq_top.not.mpr (ha i))]
    exact Finset.sum_congr rfl fun i _ => principal_length _ (ha i)
  · let e := (N.quotientEquivPiSpan b h).restrictScalars k
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module LinearMap Matrix PowerSeries
open scoped Matrix
variable {k ι W : Type*} [Field k] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module k W] [Module (O k) W] [IsScalarTower k (O k) W]
abbrev seriesAct (k W : Type*) [Field k] [AddCommGroup W] [Module k W] [Module (O k) W]
    [IsScalarTower k (O k) W] : O k →ₐ[k] End k W := Algebra.lsmul k k W
omit [Module (O k) W] [IsScalarTower k (O k) W] in
theorem finite_series_range (ρ : O k →ₐ[k] End k W) (e : ℕ) (nil : ρ X ^ e=0) :
    ρ.range=Algebra.adjoin k ({ρ X}:Set _) := by
  apply le_antisymm _ (Algebra.adjoin_le fun _ h => Set.mem_singleton_iff.mp h ▸ ⟨X,rfl⟩)
  rintro _ ⟨s,rfl⟩
  let p := trunc e s
  have divi : (X:O k)^e ∣ s-(p:O k) := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    simp [p,Polynomial.coeff_coe,coeff_trunc,hi]
  obtain ⟨g,hg⟩ := divi
  have eq : ρ s=ρ (p:O k) := by rw [←sub_eq_zero,←map_sub,hg,map_mul,map_pow,nil,zero_mul]
  let incl : Polynomial k →ₐ[k] O k := Polynomial.coeToPowerSeries.algHom k
  have inclEq : (ρ.comp incl) = Polynomial.aeval (ρ X) := by
    apply Polynomial.algHom_ext
    simp [incl]
  change ρ s ∈ Algebra.adjoin k ({ρ X}:Set _)
  rw [eq,Algebra.adjoin_singleton_eq_range_aeval]
  refine ⟨p,?_⟩
  rw [←inclEq]
  simp [incl]
theorem native_nil (P : Matrix ι ι (O k)) (hp : P.det≠0) :
    IsNilpotent (seriesAct k (QP P) X) := by
  let e := P.det.order.toNat
  have he : Ideal.span ({P.det}:Set (O k)) = Ideal.span ({(X : O k)^e}:Set _) := by
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f:=P.det)]
    exact Ideal.span_singleton_mul_right_unit (isUnit_divided_by_X_pow_order hp) _
  have dvd : P.det ∣ (X : O k)^e :=
    Ideal.mem_span_singleton.mp (he ▸ Ideal.subset_span (Set.mem_singleton _))
  have kill (w : QP P) : P.det • w=0 := by
    obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
    rw [←map_smul]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨P.adjugate *ᵥ v,?_⟩
    change P *ᵥ (P.adjugate *ᵥ v)=P.det • v
    rw [mulVec_mulVec,mul_adjugate,smul_mulVec,one_mulVec]
  obtain ⟨c,hc⟩ := dvd
  refine ⟨e,LinearMap.ext fun w => ?_⟩
  rw [←map_pow]
  change (X:O k)^e • w=0
  rw [hc,mul_smul,kill]
theorem native_graph (P Y Y' Z Z' C : Matrix ι ι (O k)) (hp : P.det≠0) (sy : Y*P=P*Y')
    (sz : Z*P=P*Z') (sc : Y*Z-Z*Y=P*C) :
    let T := seriesAct k (QP P) X
    let y := (liftEnd P Y Y' sy).restrictScalars k
    let z := (liftEnd P Z Z' sz).restrictScalars k
    FiniteDimensional k (QP P) ∧ IsNilpotent T ∧ Commute T y ∧ Commute T z ∧ Commute y z ∧
      length (O k) (QP P)=finrank k (QP P) ∧
      length (O k) (actor P Y Y' Z Z' sy sz)=finrank k (triple T y z) := by
  obtain ⟨_,_,_,_,fin⟩ := smith_colength P _root_.id (by exact hp)
  let _ : FiniteDimensional k (QP P) := fin
  let ρ := seriesAct k (QP P)
  have hn := native_nil P hp
  obtain ⟨e,he⟩ := hn
  refine ⟨fin,⟨e,he⟩,?_,?_,?_,actual_length k (QP P),?_⟩
  · apply LinearMap.ext; intro w; exact ((liftEnd P Y Y' sy).map_smul X w).symm
  · apply LinearMap.ext; intro w; exact ((liftEnd P Z Z' sz).map_smul X w).symm
  · exact LinearMap.ext fun w => LinearMap.congr_fun (lift_comm _ _ _ _ _ _ sy sz sc).eq w
  · exact origin_actor_length ρ (ρ X) rfl (finite_series_range ρ e he) (fun _ _ => rfl) _ _
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module LinearMap
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
def triples (t y z : End k W) : Fin 3 → End k W := ![t,y,z]
theorem family_adjoin (S : Fin 3 → End k W) : Algebra.adjoin k (Set.range S)=triple (S 0) (S 1) (S 2) := by
  congr 1
  ext v
  constructor
  · rintro ⟨i,rfl⟩; fin_cases i <;> simp
  · rintro (h|h|h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,(Set.mem_singleton_iff.mp h).symm⟩
theorem triples_comm {t y z : End k W} (hy : Commute t y) (hz : Commute t z) (hp : Commute y z) :
    ∀ i j, Commute (triples t y z i) (triples t y z j) := by
  intro i j; fin_cases i <;> fin_cases j <;>
    first | exact Commute.refl _ | exact hy | exact hz | exact hp | exact hy.symm | exact hz.symm | exact hp.symm
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module LinearMap Matrix PowerSeries IsDiscreteValuationRing
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev nativeTriple (P Y Y' Z Z' : Matrix ι ι (O k)) (sy : Y*P=P*Y') (sz : Z*P=P*Z') :=
  triples (seriesAct k (QP P) X) ((liftEnd P Y Y' sy).restrictScalars k) ((liftEnd P Z Z' sz).restrictScalars k)
theorem strict_to_native (P Y Y' Z Z' C : Matrix ι ι (O k)) (hp : P.det≠0) (hr : 0<Fintype.card ι)
    (sy : Y*P=P*Y') (sz : Z*P=P*Z') (sc : Y*Z-Z*Y=P*C)
    (low : ∃ j, addVal (O k) ((wordLattice P Y Z).submatrix _root_.id j).det <
        addVal (O k) (P.det^(Fintype.card ι-1))) :
    let S := nativeTriple P Y Y' Z Z' sy sz
    FiniteDimensional k (QP P) ∧ IsNilpotent (S 0) ∧ (∀ i j, Commute (S i) (S j)) ∧
      finrank k (QP P)<finrank k (Algebra.adjoin k (Set.range S)) := by
  obtain ⟨fin,hn,hy,hz,hc,nw,nb⟩ := native_graph _ _ _ _ _ _ hp sy sz sc
  refine ⟨fin,hn,triples_comm hy hz hc,?_⟩
  rw [family_adjoin]
  have small := (bad_iff_minor _ _ _ _ _ _ hp hr sy sz sc).mpr low
  rw [nw,nb] at small
  exact_mod_cast small
end DivisorG3
end
noncomputable section
namespace Gerstenhaber.FourBlocks.PrimaryDecomposition
open Module LinearMap
variable {K V ι η : Type*} [Field K] [AddCommGroup V] [Module K V]
set_option maxHeartbeats 800000 in
abbrev Generated (T : ι → Module.End K V) := Algebra.adjoin K (Set.range T)
set_option maxHeartbeats 800000 in
def root (T : ι → Module.End K V) (i : ι) : Generated T :=
  ⟨T i,Algebra.subset_adjoin ⟨i,rfl⟩⟩
set_option maxHeartbeats 800000 in
theorem root_adjoin (T : ι → Module.End K V) :
    Algebra.adjoin K (Set.range (root T))=⊤ := by
  apply Subalgebra.map_injective (f := (Generated T).val) Subtype.val_injective
  rw [AlgHom.map_adjoin,Algebra.map_top,Subalgebra.range_val]
  have hs : (Generated T).val '' Set.range (root T)=Set.range T := by
    ext f
    constructor
    · rintro ⟨a,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨root T i,⟨i,rfl⟩,rfl⟩
  rw [hs]
set_option maxHeartbeats 800000 in
theorem adjoin_mapsTo (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) (a : Generated T) :
    Set.MapsTo (a : Module.End K V) P P := by
  have hs : ∀ f ∈ Algebra.adjoin K (Set.range T), Set.MapsTo f P P := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨i,rfl⟩ := hf
      exact hP i
    | algebraMap k =>
      intro x hx
      exact P.smul_mem k hx
    | add f g _ _ hf hg =>
      intro x hx
      exact P.add_mem (hf hx) (hg hx)
    | mul f g _ _ hf hg =>
      intro x hx
      exact hf (hg hx)
  exact hs a a.property
set_option maxHeartbeats 800000 in
def restrictionHom (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) : Generated T →ₐ[K] Module.End K P where
  toFun a := (a : Module.End K V).restrict (adjoin_mapsTo T P hP a)
  map_zero' := by ext x; rfl
  map_one' := by ext x; rfl
  map_add' a b := by ext x; rfl
  map_mul' a b := by ext x; rfl
  commutes' k := by ext x; rfl
set_option maxHeartbeats 800000 in
def restricted (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) : ι → Module.End K P :=
  fun i => (T i).restrict (hP i)
set_option maxHeartbeats 800000 in
@[simp] theorem restrictionHom_root (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) (i : ι) :
    restrictionHom T P hP (root T i)=restricted T P hP i := rfl
set_option maxHeartbeats 800000 in
@[simp] theorem restricted_coe (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) (i : ι) (x : P) :
    (restricted T P hP i x : V)=T i x := rfl
set_option maxHeartbeats 800000 in
theorem restrictionHom_range (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) :
    (restrictionHom T P hP).range=Generated (restricted T P hP) := by
  have h := AlgHom.map_adjoin (restrictionHom T P hP) (Set.range (root T))
  rw [root_adjoin,Algebra.map_top] at h
  have hs : restrictionHom T P hP '' Set.range (root T)=Set.range (restricted T P hP) := by
    ext f
    constructor
    · rintro ⟨a,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨root T i,⟨i,rfl⟩,rfl⟩
  rw [hs] at h
  exact h
set_option maxHeartbeats 800000 in
def allRestrictions (T : ι → Module.End K V) (P : η → Submodule K V)
    (hP : ∀ i j, Set.MapsTo (T j) (P i) (P i)) :
    Generated T →ₗ[K] ∀ i, (restrictionHom T (P i) (hP i)).range :=
  LinearMap.pi fun i => (restrictionHom T (P i) (hP i)).rangeRestrict.toLinearMap
set_option maxHeartbeats 800000 in
theorem allRestrictions_injective (T : ι → Module.End K V) (P : η → Submodule K V)
    (hP : ∀ i j, Set.MapsTo (T j) (P i) (P i)) (hspan : ⨆ i, P i=⊤) :
    Function.Injective (allRestrictions T P hP) := by
  intro a b hab
  apply Subtype.ext
  let f : Module.End K V := (a : Module.End K V)-(b : Module.End K V)
  have hle : ⨆ i, P i ≤ f.ker := by
    apply iSup_le
    intro i x hx
    have h := congrArg (fun z => ((z i : Module.End K (P i)) ⟨x,hx⟩ : V)) hab
    change (a : Module.End K V) x=(b : Module.End K V) x at h
    exact sub_eq_zero.mpr h
  rw [hspan] at hle
  apply LinearMap.ext
  intro x
  have hx := hle (show x ∈ (⊤ : Submodule K V) from trivial)
  exact sub_eq_zero.mp hx
set_option maxHeartbeats 800000 in
theorem generated_finrank_le_sum [Fintype η] [FiniteDimensional K V]
    (T : ι → Module.End K V) (P : η → Submodule K V)
    (hP : ∀ i j, Set.MapsTo (T j) (P i) (P i)) (hspan : ⨆ i, P i=⊤)
    (hbound : ∀ i, finrank K (Generated (restricted T (P i) (hP i))) ≤ finrank K (P i)) :
    finrank K (Generated T) ≤ ∑ i, finrank K (P i) := by
  have : ∀ i, Module.Free K (restrictionHom T (P i) (hP i)).range :=
    fun i => Module.Free.of_divisionRing K (restrictionHom T (P i) (hP i)).range
  have : ∀ i, Module.Finite K (restrictionHom T (P i) (hP i)).range := fun i => inferInstance
  have h := LinearMap.finrank_le_finrank_of_injective (allRestrictions_injective T P hP hspan)
  rw [Module.finrank_pi_fintype] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro i _
  rw [restrictionHom_range]
  exact hbound i
set_option maxHeartbeats 800000 in
def shifted (T : ι → Module.End K V) (chi : ι → K) : ι → Module.End K V :=
  fun i => T i-chi i • 1
set_option maxHeartbeats 800000 in
theorem adjoin_shifted (T : ι → Module.End K V) (chi : ι → K) :
    Generated (shifted T chi)=Generated T := by
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro f ⟨i,rfl⟩
    exact (Generated T).sub_mem (Algebra.subset_adjoin ⟨i,rfl⟩)
      ((Generated T).algebraMap_mem (chi i))
  · apply Algebra.adjoin_le
    rintro f ⟨i,rfl⟩
    have h1 : shifted T chi i ∈ Generated (shifted T chi) := Algebra.subset_adjoin ⟨i,rfl⟩
    have h2 : (chi i • (1 : Module.End K V)) ∈ Generated (shifted T chi) :=
      (Generated (shifted T chi)).algebraMap_mem (chi i)
    simpa only [shifted,sub_add_cancel,SetLike.mem_coe] using (Generated (shifted T chi)).add_mem h1 h2
end Gerstenhaber.FourBlocks.PrimaryDecomposition
end
noncomputable section
namespace Gerstenhaber.FourBlocks
open Polynomial
end Gerstenhaber.FourBlocks
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap Polynomial
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
def blockLift (f : V →ₗ[K] W) : Module.End K (V × W) :=
  (LinearMap.inr K V W).comp (f.comp (LinearMap.fst K V W))
@[simp] theorem blockLift_apply (f : V →ₗ[K] W) (v : V) (w : W) :
    blockLift f (v,w) = (0,f v) := rfl
def blockRangeEquiv (f : V →ₗ[K] W) :
    LinearMap.range (blockLift f) ≃ₗ[K] LinearMap.range f where
  toFun y := ⟨y.1.2, by
    obtain ⟨x,hx⟩ := y.2
    exact ⟨x.1, congrArg Prod.snd hx⟩⟩
  invFun y := ⟨(0,y.1), by
    obtain ⟨x,hx⟩ := y.2
    exact ⟨(x,0), by simp [hx]⟩⟩
  left_inv y := by
    apply Subtype.ext
    obtain ⟨x,hx⟩ := y.2
    have hz : y.1.1 = 0 := by
      have := congrArg Prod.fst hx
      simpa [blockLift] using this.symm
    exact Prod.ext hz.symm rfl
  right_inv y := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
variable {E F : Type*} [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
theorem finrank_ker_eq_quotient_range [FiniteDimensional K V] (f : Module.End K V) :
    finrank K (LinearMap.ker f) = finrank K (V ⧸ LinearMap.range f) := by
  have hker := f.finrank_range_add_finrank_ker
  have hquot := (LinearMap.range f).finrank_quotient_add_finrank
  omega
def intertwiningKernelMap (f : Module.End K V) (g : Module.End K W)
    (i : V →ₗ[K] W) (hi : ∀ x, i (f x)=g (i x)) :
    LinearMap.ker f →ₗ[K] LinearMap.ker g where
  toFun x := ⟨i x,by
    change g (i x)=0
    rw [← hi,x.2,map_zero]⟩
  map_add' x y := Subtype.ext (i.map_add x y)
  map_smul' a x := Subtype.ext (i.map_smul a x)
theorem finrank_ker_le_of_injective_intertwining [FiniteDimensional K W]
    (f : Module.End K V) (g : Module.End K W) (i : V →ₗ[K] W)
    (hi : Function.Injective i) (hcomm : ∀ x, i (f x)=g (i x)) :
    finrank K (LinearMap.ker f) ≤ finrank K (LinearMap.ker g) := by
  apply LinearMap.finrank_le_finrank_of_injective
    (f := intertwiningKernelMap f g i hcomm)
  intro x y hxy
  apply Subtype.ext
  exact hi (congrArg (fun z : LinearMap.ker g => (z : W)) hxy)
def intertwiningCokernelMap (f : Module.End K V) (g : Module.End K W)
    (p : V →ₗ[K] W) (hcomm : ∀ x, p (f x)=g (p x)) :
    (V ⧸ LinearMap.range f) →ₗ[K] (W ⧸ LinearMap.range g) :=
  (LinearMap.range f).liftQ ((LinearMap.range g).mkQ.comp p) (by
    rintro _ ⟨x,rfl⟩
    change (LinearMap.range g).mkQ (p (f x))=0
    rw [hcomm]
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨p x,rfl⟩)
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.PrimaryDecomposition
open Module LinearMap
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
set_option maxHeartbeats 800000 in
def jointSpace (T : ι → Module.End K V) (chi : ι → K) : Submodule K V :=
  ⨅ i, (T i).maxGenEigenspace (chi i)
set_option maxHeartbeats 800000 in
abbrev JointCharacters (T : ι → Module.End K V) :=
  {chi : ι → K // jointSpace T chi ≠ ⊥}
set_option maxHeartbeats 800000 in
theorem jointSpace_stable (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) (chi : ι → K) (i : ι) :
    Set.MapsTo (T i) (jointSpace T chi) (jointSpace T chi) := by
  intro x hx
  change T i x ∈ jointSpace T chi
  apply (Submodule.mem_iInf (fun j => (T j).maxGenEigenspace (chi j))).mpr
  intro j
  exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) (chi j)
    ((iInf_le (fun j => (T j).maxGenEigenspace (chi j)) j) hx)
set_option maxHeartbeats 800000 in
theorem jointSpace_independent (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) : iSupIndep (jointSpace T) := by
  exact Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo T
    (fun i j phi => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) phi)
set_option maxHeartbeats 800000 in
noncomputable abbrev jointCharactersFintype [FiniteDimensional K V]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j)) :
    Fintype (JointCharacters T) :=
  (jointSpace_independent T hcomm).fintypeNeBotOfFiniteDimensional
set_option maxHeartbeats 800000 in
theorem jointSpace_iSup [FiniteDimensional K V] [IsAlgClosed K]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j)) :
    ⨆ chi, jointSpace T chi=⊤ := by
  exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo T
    (fun i j phi => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm j i) phi)
    (fun i => (T i).iSup_maxGenEigenspace_eq_top)
set_option maxHeartbeats 800000 in
theorem jointSpace_isInternal [FiniteDimensional K V] [IsAlgClosed K]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    [DecidableEq (JointCharacters T)] :
    DirectSum.IsInternal (fun chi : JointCharacters T => jointSpace T chi.val) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (jointSpace_independent T hcomm).comp Subtype.val_injective
  · apply top_unique
    rw [←jointSpace_iSup T hcomm]
    apply iSup_le
    intro chi
    by_cases hchi : jointSpace T chi=⊥
    · rw [hchi]
      exact bot_le
    · exact le_iSup (fun chi : JointCharacters T => jointSpace T chi.val) ⟨chi,hchi⟩
set_option maxHeartbeats 800000 in
theorem jointCharacters_iSup [FiniteDimensional K V] [IsAlgClosed K]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j)) :
    ⨆ chi : JointCharacters T, jointSpace T chi.val=⊤ := by
  classical
  exact (jointSpace_isInternal T hcomm).submodule_iSup_eq_top
set_option maxHeartbeats 800000 in
theorem sum_finrank_jointSpace [FiniteDimensional K V] [IsAlgClosed K]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    [Fintype (JointCharacters T)] :
    (∑ chi : JointCharacters T, finrank K (jointSpace T chi.val))=finrank K V := by
  classical
  let e := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun chi : JointCharacters T => jointSpace T chi.val))
    (jointSpace_isInternal T hcomm)
  have h := e.finrank_eq
  rw [Module.finrank_directSum] at h
  exact h
set_option maxHeartbeats 800000 in
theorem restricted_commute (T : ι → Module.End K V) (P : Submodule K V)
    (hP : ∀ i, Set.MapsTo (T i) P P) (hcomm : ∀ i j, Commute (T i) (T j)) (i j : ι) :
    Commute (restricted T P hP i) (restricted T P hP j) :=
  LinearMap.restrict_commute (hcomm i j) (hP i) (hP j)
set_option maxHeartbeats 800000 in
theorem shifted_commute (T : ι → Module.End K V) (chi : ι → K)
    (hcomm : ∀ i j, Commute (T i) (T j)) (i j : ι) :
    Commute (shifted T chi i) (shifted T chi j) := by
  change Commute (T i-algebraMap K (Module.End K V) (chi i))
    (T j-algebraMap K (Module.End K V) (chi j))
  exact ((hcomm i j).sub_left (Algebra.commute_algebraMap_left (chi i) (T j))).sub_right
    (Algebra.commute_algebraMap_right (chi j) (T i-algebraMap K (Module.End K V) (chi i)))
set_option maxHeartbeats 800000 in
theorem joint_shift_nilpotent [FiniteDimensional K V]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    (chi : ι → K) (i : ι) :
    IsNilpotent (shifted (restricted T (jointSpace T chi) (jointSpace_stable T hcomm chi)) chi i) := by
  have hs : Set.MapsTo (T i-chi i • (1 : Module.End K V)) (jointSpace T chi) (jointSpace T chi) := by
    intro x hx
    exact (jointSpace T chi).sub_mem (jointSpace_stable T hcomm chi i hx)
      ((jointSpace T chi).smul_mem (chi i) hx)
  have heq : shifted (restricted T (jointSpace T chi) (jointSpace_stable T hcomm chi)) chi i =
      (T i-chi i • (1 : Module.End K V)).restrict hs := by ext x; rfl
  rw [heq]
  exact Module.End.isNilpotent_restrict_of_le (iInf_le _ i)
    ((T i).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap (chi i))
set_option maxHeartbeats 800000 in
theorem joint_shift_kernel_le [FiniteDimensional K V]
    (T : ι → Module.End K V) (hcomm : ∀ i j, Commute (T i) (T j))
    (chi : ι → K) (i : ι) :
    finrank K (shifted (restricted T (jointSpace T chi) (jointSpace_stable T hcomm chi)) chi i).ker ≤
      finrank K (T i-chi i • 1).ker := by
  apply Gerstenhaber.FourBlocks.MinimalSource.finrank_ker_le_of_injective_intertwining
    _ _ (jointSpace T chi).subtype (jointSpace T chi).injective_subtype
  intro x
  rfl
end Gerstenhaber.FourBlocks.PrimaryDecomposition
end
noncomputable section
namespace Gerstenhaber.FourBlocks.PrimaryDecomposition
open Module LinearMap
set_option maxHeartbeats 800000 in
def NilTripleKernelBound (K : Type u) [Field K] (k : ℕ) : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (T : Fin 3 → Module.End K V),
    (∀ i j, Commute (T i) (T j)) → (∀ i, IsNilpotent (T i)) →
    finrank K (T 0).ker ≤ k →
      finrank K (Algebra.adjoin K (Set.range T)) ≤ finrank K V
variable {K V : Type u} [Field K] [IsAlgClosed K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
set_option maxHeartbeats 800000 in
theorem commuting_triple_bound_of_nilpotent_bound (k : ℕ)
    (hnil : NilTripleKernelBound K k) (T : Fin 3 → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hfirst : ∀ lambda : K, finrank K (T 0-lambda • 1).ker ≤ k) :
    finrank K (Algebra.adjoin K (Set.range T)) ≤ finrank K V := by
  let := jointCharactersFintype T hcomm
  have hlocal (chi : JointCharacters T) :
      finrank K (Generated (restricted T (jointSpace T chi.val)
        (jointSpace_stable T hcomm chi.val))) ≤ finrank K (jointSpace T chi.val) := by
    have h := hnil (jointSpace T chi.val)
      (shifted (restricted T (jointSpace T chi.val) (jointSpace_stable T hcomm chi.val)) chi.val)
      (shifted_commute _ chi.val (restricted_commute T _ _ hcomm))
      (joint_shift_nilpotent T hcomm chi.val)
      ((joint_shift_kernel_le T hcomm chi.val 0).trans (hfirst (chi.val 0)))
    change finrank K (Generated (shifted (restricted T (jointSpace T chi.val)
      (jointSpace_stable T hcomm chi.val)) chi.val)) ≤ _ at h
    rw [adjoin_shifted] at h
    exact h
  have h := generated_finrank_le_sum T
    (fun chi : JointCharacters T => jointSpace T chi.val)
    (fun chi => jointSpace_stable T hcomm chi.val) (jointCharacters_iSup T hcomm) hlocal
  rw [sum_finrank_jointSpace T hcomm] at h
  exact h
set_option maxHeartbeats 800000 in
theorem matrix_triple_bound_of_nilpotent_bound (k : ℕ)
    (hnil : NilTripleKernelBound K k) (n : ℕ)
    (T : Fin 3 → Matrix (Fin n) (Fin n) K)
    (hcomm : ∀ i j, Commute (T i) (T j))
    (hfirst : ∀ lambda : K,
      finrank K (Matrix.toLin' (T 0-lambda • 1)).ker ≤ k) :
    finrank K (Algebra.adjoin K (Set.range T)) ≤ n := by
  let e : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K) := Matrix.toLinAlgEquiv'
  let U : Fin 3 → Module.End K (Fin n → K) := fun i => e (T i)
  have hUcomm : ∀ i j, Commute (U i) (U j) := fun i j => (hcomm i j).map e.toAlgHom
  have hUfirst : ∀ lambda : K, finrank K (U 0-lambda • 1).ker ≤ k := by
    intro lambda
    have h := hfirst lambda
    have heq : U 0-lambda • 1=e (T 0-lambda • 1) := by simp [U]
    rw [heq]
    exact h
  have hbound := commuting_triple_bound_of_nilpotent_bound k hnil U hUcomm hUfirst
  have hmap : Generated U=(Algebra.adjoin K (Set.range T)).map e.toAlgHom := by
    rw [AlgHom.map_adjoin,←Set.range_comp]
    rfl
  have hdim : finrank K ((Algebra.adjoin K (Set.range T)).map e.toAlgHom)=
      finrank K (Algebra.adjoin K (Set.range T)) :=
    e.toLinearEquiv.finrank_map_eq (Algebra.adjoin K (Set.range T)).toSubmodule
  change finrank K (Generated U) ≤ _ at hbound
  rw [hmap,hdim] at hbound
  simpa using hbound
end Gerstenhaber.FourBlocks.PrimaryDecomposition
end
noncomputable section
namespace DVRMinimal
open Module LinearMap
open Gerstenhaber.FourBlocks.PrimaryDecomposition
def SafeAt (k : Type u) [Field k] (r : ℕ) : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : Fin 3 → Module.End k W), (∀ i j, Commute (T i) (T j)) →
      IsNilpotent (T 0) → finrank k (T 0).ker = r →
      finrank k (Generated T) ≤ finrank k W
variable {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
theorem nil_kernel_vector [Nontrivial W] (t : Module.End k W) (ht : IsNilpotent t) :
    ∃ w : W, t w=0 ∧ w≠0 := by
  by_contra! h
  have hker : t.ker = ⊥ := by
    apply bot_unique
    exact fun x hx => (Submodule.mem_bot k).mpr (h x hx)
  obtain ⟨n,hn⟩ := ht
  have hi : Function.Injective ⇑(t^n) := by
    rw [Module.End.coe_pow]; exact (LinearMap.ker_eq_bot.mp hker).iterate n
  obtain ⟨x,hx⟩ := exists_ne (0 : W)
  exact hx (hi (by rw [hn]; rfl))
theorem kernel_strict (t : Module.End k W) (ht : IsNilpotent t)
    (P Q : Submodule k W) (hp : Set.MapsTo t P P) (hq : Set.MapsTo t Q Q)
    (hQ : Q ≠ ⊥) (hd : Disjoint P Q) :
    finrank k (t.restrict hp).ker < finrank k t.ker := by
  let f : (t.restrict hp).ker →ₗ[k] t.ker :=
    (P.subtype.comp (t.restrict hp).ker.subtype).codRestrict _ fun x => congrArg Subtype.val x.2
  have hfi : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : t.ker => z.val) h))
  letI : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
  obtain ⟨q,hqzero,hqne⟩ := nil_kernel_vector (t.restrict hq) (Module.End.isNilpotent.restrict hq ht)
  let v : t.ker := ⟨q.val,congrArg Subtype.val hqzero⟩
  have hns : ¬Function.Surjective f := by
    intro hs
    obtain ⟨x,hx⟩ := hs v
    have hxq : (x.val : W) = q.val := congrArg Subtype.val hx
    exact hqne (Subtype.ext (Submodule.disjoint_def.mp hd _ (hxq ▸ x.val.2) q.2))
  have eqr := LinearMap.finrank_range_of_inj hfi
  have lt := Submodule.finrank_lt_finrank_of_lt
    (lt_top_iff_ne_top.mpr (mt LinearMap.range_eq_top.mp hns))
  rw [finrank_top,eqr] at lt
  exact lt
variable [IsAlgClosed k]
theorem least_bad_joint_top (T : Fin 3 → Module.End k W)
    (hc : ∀ i j, Commute (T i) (T j)) (hn : IsNilpotent (T 0))
    (bad : finrank k W < finrank k (Generated T))
    (small : ∀ j < finrank k (T 0).ker, SafeAt k j) :
    ∃ chi : Fin 3 → k, jointSpace T chi = ⊤ := by
  classical
  letI := jointCharactersFintype T hc
  have hex : ∃ c : JointCharacters T, finrank k (jointSpace T c.val) <
      finrank k (Generated (restricted T (jointSpace T c.val) (jointSpace_stable T hc c.val))) := by
    by_contra! he
    have b := generated_finrank_le_sum T (fun c : JointCharacters T => jointSpace T c.val)
      (fun c => jointSpace_stable T hc c.val) (jointCharacters_iSup T hc) he
    rw [sum_finrank_jointSpace T hc] at b
    omega
  obtain ⟨c,bc⟩ := hex
  have uniq (v : JointCharacters T) : c=v := by
    by_contra h
    have hv : c.val ≠ v.val := fun he => h (Subtype.ext he)
    have lt := kernel_strict (T 0) hn (jointSpace T c.val) (jointSpace T v.val)
      (jointSpace_stable T hc c.val 0) (jointSpace_stable T hc v.val 0) v.2
      ((jointSpace_independent T hc).pairwiseDisjoint hv)
    let U := restricted T (jointSpace T c.val) (jointSpace_stable T hc c.val)
    have hn' : IsNilpotent (U 0) := Module.End.isNilpotent.restrict _ hn
    have bs := small _ lt (jointSpace T c.val) U (restricted_commute _ _ _ hc) hn' rfl
    exact (not_lt_of_ge bs) bc
  refine ⟨c.val,top_unique ?_⟩
  rw [←jointCharacters_iSup T hc]
  exact iSup_le fun v => by rw [←uniq v]
theorem least_bad_single_spectrum (T : Fin 3 → Module.End k W)
    (hc : ∀ i j, Commute (T i) (T j)) (hn : IsNilpotent (T 0))
    (bad : finrank k W < finrank k (Generated T))
    (small : ∀ j < finrank k (T 0).ker, SafeAt k j) :
    ∃ chi : Fin 3 → k, ∀ i, IsNilpotent (T i-chi i • 1) := by
  obtain ⟨chi,hchi⟩ := least_bad_joint_top T hc hn bad small
  refine ⟨chi,fun i => ?_⟩
  have hs : Set.MapsTo (T i-chi i • (1 : Module.End k W)) (jointSpace T chi) (jointSpace T chi) :=
    fun w h => (jointSpace T chi).sub_mem (jointSpace_stable T hc chi i h) ((jointSpace T chi).smul_mem _ h)
  have hnil : IsNilpotent ((T i-chi i • (1 : Module.End k W)).restrict hs) := by
    have eq : (T i-chi i • (1 : Module.End k W)).restrict hs =
        shifted (restricted T (jointSpace T chi) (jointSpace_stable T hc chi)) chi i := by ext w; rfl
    rw [eq]; exact joint_shift_nilpotent _ hc _ _
  obtain ⟨n,he⟩ := hnil
  refine ⟨n,?_⟩
  ext w
  let v : jointSpace T chi := ⟨w,hchi ▸ Submodule.mem_top⟩
  have hh (j : ℕ) : ((T i - chi i • (1 : Module.End k W)).restrict hs ^ j) v =
      (⟨((T i - chi i • 1)^j) w, by
         change ((T i - chi i • (1 : Module.End k W))^j) v.val ∈ jointSpace T chi
         exact (Submodule.eq_top_iff'.mp hchi) _⟩ : jointSpace T chi) := by
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ',pow_succ',Module.End.mul_apply,ih]; rfl
  have e0 := hh n
  rw [he] at e0
  exact (congrArg Subtype.val e0).symm
end DVRMinimal
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K U V : Type*} [Field K]
  [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
def rankOne : V →ₗ[K] Module.Dual K U →ₗ[K] (U →ₗ[K] V) where
  toFun v :=
    { toFun := fun φ => φ.smulRight v
      map_add' := by intros; ext; simp [add_smul]
      map_smul' := by intros; ext; simp [smul_smul] }
  map_add' := by intros; ext; simp [smul_add]
  map_smul' := by intros; ext; simp [smul_smul,mul_comm]
@[simp] theorem rankOne_apply (v : V) (φ : Module.Dual K U) (u : U) :
    rankOne v φ u = φ u • v := rfl
def quotientRankOne (T : Submodule K (U →ₗ[K] V)) :
    V →ₗ[K] Module.Dual K U →ₗ[K] ((U →ₗ[K] V) ⧸ T) where
  toFun v := T.mkQ.comp (rankOne v)
  map_add' := by intro v w; ext φ; simp [map_add]
  map_smul' := by intro a v; ext φ; simp [map_smul]
@[simp] theorem quotientRankOne_apply (T : Submodule K (U →ₗ[K] V))
    (v : V) (φ : Module.Dual K U) :
    quotientRankOne T v φ = T.mkQ (φ.smulRight v) := rfl
def fixedFunctionalFiber (T : Submodule K (U →ₗ[K] V)) (φ : Module.Dual K U) :
    Submodule K V := LinearMap.ker ((quotientRankOne T).flip φ)
def fixedVectorFiber (T : Submodule K (U →ₗ[K] V)) (v : V) :
    Submodule K (Module.Dual K U) := LinearMap.ker (quotientRankOne T v)
@[simp] theorem mem_fixedFunctionalFiber (T : Submodule K (U →ₗ[K] V))
    (φ : Module.Dual K U) (v : V) :
    v ∈ fixedFunctionalFiber T φ ↔ φ.smulRight v ∈ T := by
  simp [fixedFunctionalFiber,LinearMap.mem_ker,Submodule.Quotient.mk_eq_zero]
@[simp] theorem mem_fixedVectorFiber (T : Submodule K (U →ₗ[K] V))
    (v : V) (φ : Module.Dual K U) :
    φ ∈ fixedVectorFiber T v ↔ φ.smulRight v ∈ T := by
  simp [fixedVectorFiber,LinearMap.mem_ker,Submodule.Quotient.mk_eq_zero]
@[simp] theorem fixedFunctionalFiber_zero (T : Submodule K (U →ₗ[K] V)) :
    fixedFunctionalFiber T 0 = ⊤ := by
  ext v
  simp
@[simp] theorem fixedVectorFiber_zero (T : Submodule K (U →ₗ[K] V)) :
    fixedVectorFiber T 0 = ⊤ := by
  ext φ
  simp
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M]
set_option maxHeartbeats 800000 in
def moduleRadical (eps : A →ₐ[K] K) : Submodule A M :=
  Submodule.span A {z : M | ∃ a : A, eps a = 0 ∧ ∃ x : M, a • x = z}
set_option maxHeartbeats 800000 in
theorem smul_mem_moduleRadical (eps : A →ₐ[K] K) (a : A) (ha : eps a = 0) (x : M) :
    a • x ∈ moduleRadical eps :=
  Submodule.subset_span ⟨a,ha,x,rfl⟩
set_option maxHeartbeats 800000 in
def moduleSocle (eps : A →ₐ[K] K) : Submodule A M where
  carrier := {x | ∀ a : A, eps a = 0 → a • x = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy a ha; rw [smul_add,hx a ha,hy a ha,add_zero]
  smul_mem' := by
    intro r x hx a ha
    rw [← mul_smul,mul_comm a r,mul_smul,hx a ha,smul_zero]
set_option maxHeartbeats 800000 in
@[simp] theorem mem_moduleSocle (eps : A →ₐ[K] K) (x : M) :
    x ∈ moduleSocle eps ↔ ∀ a : A, eps a = 0 → a • x = 0 := Iff.rfl
set_option maxHeartbeats 800000 in
def algebraSocle (eps : A →ₐ[K] K) : Ideal A where
  carrier := {s | ∀ a : A, eps a = 0 → s*a = 0}
  zero_mem' := by simp
  add_mem' := by intro s t hs ht a ha; rw [add_mul,hs a ha,ht a ha,add_zero]
  smul_mem' := by
    intro r s hs a ha
    change (r*s)*a=0
    rw [mul_assoc,hs a ha,mul_zero]
set_option maxHeartbeats 800000 in
@[simp] theorem mem_algebraSocle (eps : A →ₐ[K] K) (s : A) :
    s ∈ algebraSocle eps ↔ ∀ a : A, eps a = 0 → s*a=0 := Iff.rfl
set_option maxHeartbeats 800000 in
abbrev Top (eps : A →ₐ[K] K) := M ⧸ moduleRadical (M := M) eps
set_option maxHeartbeats 800000 in
def socleMul (eps : A →ₐ[K] K) (s : algebraSocle eps) :
    M →ₗ[A] moduleSocle (M := M) eps where
  toFun x := ⟨s.1 • x,by
    intro a ha
    rw [← mul_smul,mul_comm a s.1,s.2 a ha,zero_smul]⟩
  map_add' := by intro x y; apply Subtype.ext; exact smul_add _ _ _
  map_smul' := by
    intro a x
    apply Subtype.ext
    change s.1 • (a • x) = a • (s.1 • x)
    rw [← mul_smul,← mul_smul,mul_comm]
set_option maxHeartbeats 800000 in
theorem moduleRadical_le_ker_socleMul (eps : A →ₐ[K] K) (s : algebraSocle eps) :
    moduleRadical eps ≤ LinearMap.ker (socleMul (M := M) eps s) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,x,rfl⟩
  apply Subtype.ext
  change s.1 • (a • x) = 0
  rw [← mul_smul,s.2 a ha,zero_smul]
variable [Module K M] [IsScalarTower K A M]
set_option maxHeartbeats 800000 in
def socleAction (eps : A →ₐ[K] K) :
    algebraSocle eps →ₗ[K] (Top (M := M) eps →ₗ[K] moduleSocle (M := M) eps) where
  toFun s := ((moduleRadical eps).liftQ (socleMul eps s)
    (moduleRadical_le_ker_socleMul eps s)).restrictScalars K
  map_add' := by
    intro s t
    apply LinearMap.ext
    intro q
    obtain ⟨x,rfl⟩ := (moduleRadical (M := M) eps).mkQ_surjective q
    apply Subtype.ext
    change (s.1+t.1) • x = s.1 • x+t.1 • x
    exact add_smul _ _ _
  map_smul' := by
    intro c s
    apply LinearMap.ext
    intro q
    obtain ⟨x,rfl⟩ := (moduleRadical (M := M) eps).mkQ_surjective q
    apply Subtype.ext
    change (c • s.1) • x = c • (s.1 • x)
    exact smul_assoc _ _ _
set_option maxHeartbeats 800000 in
@[simp] theorem socleAction_mk (eps : A →ₐ[K] K) (s : algebraSocle eps) (x : M) :
    (socleAction (M := M) eps s ((moduleRadical eps).mkQ x) : M) = s.1 • x := rfl
set_option maxHeartbeats 800000 in
theorem socleAction_injective [FaithfulSMul A M] (eps : A →ₐ[K] K) :
    Function.Injective (socleAction (M := M) eps) := by
  intro s t hst
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := M)
  intro x
  have h := congrArg (fun F => (F ((moduleRadical eps).mkQ x) : M)) hst
  exact h
set_option maxHeartbeats 800000 in
def topProjection (eps : A →ₐ[K] K) : M →ₗ[K] Top (M := M) eps :=
  (moduleRadical eps).mkQ.restrictScalars K
set_option maxHeartbeats 800000 in
theorem topProjection_surjective (eps : A →ₐ[K] K) :
    Function.Surjective (topProjection (M := M) eps) :=
  (moduleRadical eps).mkQ_surjective
set_option maxHeartbeats 800000 in
theorem sub_eps_smul_mem_radical (eps : A →ₐ[K] K) (a : A) (x : M) :
    a • x - eps a • x ∈ moduleRadical eps := by
  have h := smul_mem_moduleRadical eps (a-algebraMap K A (eps a)) (by simp) x
  simpa only [sub_smul,IsScalarTower.algebraMap_smul] using h
set_option maxHeartbeats 800000 in
theorem topProjection_smul (eps : A →ₐ[K] K) (a : A) (x : M) :
    topProjection eps (a • x) = eps a • topProjection eps x := by
  have h := (Submodule.Quotient.mk_eq_zero (moduleRadical eps)).mpr
    (sub_eps_smul_mem_radical eps a x)
  change topProjection eps (a • x-eps a • x) = 0 at h
  rw [map_sub,(topProjection eps).map_smul (eps a) x] at h
  exact sub_eq_zero.mp h
set_option maxHeartbeats 800000 in
theorem smul_eq_eps_smul_of_mem_socle (eps : A →ₐ[K] K) (x : M)
    (hx : x ∈ moduleSocle eps) (a : A) : a • x = eps a • x := by
  have h := hx (a-algebraMap K A (eps a)) (by simp)
  rw [sub_smul,IsScalarTower.algebraMap_smul] at h
  exact sub_eq_zero.mp h
set_option maxHeartbeats 800000 in
def topHyperplane (eps : A →ₐ[K] K) (φ : Module.Dual K (Top (M := M) eps)) :
    Submodule A M where
  carrier := {x | φ (topProjection eps x) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change φ (topProjection eps x) = 0 at hx
    change φ (topProjection eps y) = 0 at hy
    change φ (topProjection eps (x+y)) = 0
    rw [map_add,map_add,hx,hy,add_zero]
  smul_mem' := by
    intro a x hx
    change φ (topProjection eps x) = 0 at hx
    change φ (topProjection eps (a • x)) = 0
    rw [topProjection_smul,map_smul,hx,smul_zero]
set_option maxHeartbeats 800000 in
@[simp] theorem mem_topHyperplane (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (x : M) :
    x ∈ topHyperplane eps φ ↔ φ (topProjection eps x) = 0 := Iff.rfl
set_option maxHeartbeats 800000 in
theorem moduleRadical_le_topHyperplane (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) : moduleRadical eps ≤ topHyperplane eps φ := by
  intro x hx
  have h : topProjection eps x = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hx
  change φ (topProjection eps x) = 0
  rw [h,map_zero]
set_option maxHeartbeats 800000 in
def socleLine (eps : A →ₐ[K] K) (v : moduleSocle (M := M) eps) : Submodule A M where
  carrier := {x | ∃ c : K, c • v.1 = x}
  zero_mem' := ⟨0,zero_smul _ _⟩
  add_mem' := by
    rintro x y ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨a+b,add_smul _ _ _⟩
  smul_mem' := by
    rintro a x ⟨c,rfl⟩
    refine ⟨c*eps a,?_⟩
    rw [smul_comm a c,smul_eq_eps_smul_of_mem_socle eps v.1 v.2,smul_smul]
set_option maxHeartbeats 800000 in
@[simp] theorem mem_socleLine (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (x : M) :
    x ∈ socleLine eps v ↔ ∃ c : K, c • v.1 = x := Iff.rfl
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
set_option maxHeartbeats 800000 in
theorem mem_annihilator_submodule_iff (N : Submodule A M) (g : A) :
    g ∈ Module.annihilator A N ↔ ∀ x : M, x ∈ N → g • x = 0 := by
  rw [Module.mem_annihilator]
  constructor
  · intro h x hx
    exact congrArg Subtype.val (h ⟨x,hx⟩)
  · intro h x
    apply Subtype.ext
    exact h x.1 x.2
set_option maxHeartbeats 800000 in
theorem mem_annihilator_quotient_iff (N : Submodule A M) (g : A) :
    g ∈ Module.annihilator A (M ⧸ N) ↔ ∀ x : M, g • x ∈ N := by
  rw [Module.mem_annihilator]
  constructor
  · intro h x
    exact (Submodule.Quotient.mk_eq_zero N).mp (h (N.mkQ x))
  · intro h q
    obtain ⟨x,rfl⟩ := N.mkQ_surjective q
    exact (Submodule.Quotient.mk_eq_zero N).mpr (h x)
set_option maxHeartbeats 800000 in
omit [Module K M] [IsScalarTower K A M] in
theorem annihilator_le_algebraSocle_of_radical_le [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (N : Submodule A M) (hN : moduleRadical eps ≤ N) :
    Module.annihilator A N ≤ algebraSocle eps := by
  intro g hg a ha
  apply eq_of_smul_eq_smul (α := M)
  intro x
  rw [zero_smul,mul_smul]
  exact (mem_annihilator_submodule_iff N g).mp hg (a • x)
    (hN (smul_mem_moduleRadical eps a ha x))
set_option maxHeartbeats 800000 in
theorem socleLine_le_moduleSocle (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) : socleLine eps v ≤ moduleSocle eps := by
  rintro x ⟨c,rfl⟩
  exact ((moduleSocle eps).restrictScalars K).smul_mem c v.2
set_option maxHeartbeats 800000 in
omit [Module K M] [IsScalarTower K A M] in
theorem quotient_annihilator_le_algebraSocle [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (N : Submodule A M) (hN : N ≤ moduleSocle eps) :
    Module.annihilator A (M ⧸ N) ≤ algebraSocle eps := by
  intro g hg a ha
  apply eq_of_smul_eq_smul (α := M)
  intro x
  rw [zero_smul,mul_smul,smul_comm]
  exact hN ((mem_annihilator_quotient_iff N g).mp hg x) a ha
set_option maxHeartbeats 800000 in
def socleTensor (eps : A →ₐ[K] K) :
    Submodule K (Top (M := M) eps →ₗ[K] moduleSocle (M := M) eps) :=
  LinearMap.range (socleAction (M := M) eps)
set_option maxHeartbeats 800000 in
def hyperplaneAnnToSocle [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) :
    Module.annihilator A (topHyperplane eps φ) →ₗ[K] algebraSocle eps where
  toFun g := ⟨g.1,annihilator_le_algebraSocle_of_radical_le eps _
    (moduleRadical_le_topHyperplane eps φ) g.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
set_option maxHeartbeats 800000 in
def lineQuotientAnnToSocle [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) :
    Module.annihilator A (M ⧸ socleLine eps v) →ₗ[K] algebraSocle eps where
  toFun g := ⟨g.1,quotient_annihilator_le_algebraSocle eps _
    (socleLine_le_moduleSocle eps v) g.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
set_option maxHeartbeats 800000 in
theorem hyperplane_ann_action_kills_kernel [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (φ : Module.Dual K (Top (M := M) eps))
    (g : Module.annihilator A (topHyperplane eps φ)) (q : Top (M := M) eps)
    (hq : φ q = 0) : socleAction eps (hyperplaneAnnToSocle eps φ g) q = 0 := by
  obtain ⟨x,rfl⟩ := topProjection_surjective eps q
  apply Subtype.ext
  exact (mem_annihilator_submodule_iff _ _).mp g.2 x hq
set_option maxHeartbeats 800000 in
theorem line_quotient_ann_action_range [FaithfulSMul A M]
    (eps : A →ₐ[K] K) (v : moduleSocle (M := M) eps)
    (g : Module.annihilator A (M ⧸ socleLine eps v)) (q : Top (M := M) eps) :
    ∃ c : K, c • v = socleAction eps (lineQuotientAnnToSocle eps v g) q := by
  obtain ⟨x,rfl⟩ := topProjection_surjective eps q
  obtain ⟨c,hc⟩ := (mem_annihilator_quotient_iff _ _).mp g.2 x
  exact ⟨c,Subtype.ext hc⟩
section RankOneFactor
variable {U V : Type*} [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
set_option maxHeartbeats 800000 in
theorem eq_smulRight_of_kills_kernel (f : U →ₗ[K] V) (φ : Module.Dual K U)
    (u0 : U) (hu0 : φ u0=1) (hker : ∀ u, φ u=0 → f u=0) :
    f = φ.smulRight (f u0) := by
  ext u
  change f u = φ u • f u0
  have hz : φ (u-φ u • u0)=0 := by simp [hu0]
  have h := hker _ hz
  rw [map_sub,map_smul] at h
  exact sub_eq_zero.mp h
set_option maxHeartbeats 800000 in
theorem eq_smulRight_of_range_line (f : U →ₗ[K] V) (v : V)
    (ψ : Module.Dual K V) (hψ : ψ v=1)
    (hline : ∀ u, ∃ c : K, c • v=f u) : f = (ψ.comp f).smulRight v := by
  ext u
  change f u = ψ (f u) • v
  obtain ⟨c,hc⟩ := hline u
  rw [← hc,map_smul,hψ,smul_eq_mul,mul_one]
end RankOneFactor
set_option maxHeartbeats 800000 in
def hyperplaneAnnEval [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (u0 : Top (M := M) eps) :
    Module.annihilator A (topHyperplane eps φ) →ₗ[K] moduleSocle (M := M) eps where
  toFun g := socleAction eps (hyperplaneAnnToSocle eps φ g) u0
  map_add' := by
    intro g h
    change socleAction eps (hyperplaneAnnToSocle eps φ g+hyperplaneAnnToSocle eps φ h) u0 = _
    rw [map_add,LinearMap.add_apply]
  map_smul' := by
    intro c g
    change socleAction eps (c • hyperplaneAnnToSocle eps φ g) u0 = _
    rw [map_smul,LinearMap.smul_apply]
    rfl
set_option maxHeartbeats 800000 in
theorem hyperplane_ann_factor [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (u0 : Top (M := M) eps) (hu0 : φ u0=1)
    (g : Module.annihilator A (topHyperplane eps φ)) :
    socleAction eps (hyperplaneAnnToSocle eps φ g) =
      φ.smulRight (hyperplaneAnnEval eps φ u0 g) :=
  eq_smulRight_of_kills_kernel _ φ u0 hu0 (hyperplane_ann_action_kills_kernel eps φ g)
set_option maxHeartbeats 800000 in
theorem hyperplaneAnnEval_injective [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (u0 : Top (M := M) eps) (hu0 : φ u0=1) :
    Function.Injective (hyperplaneAnnEval eps φ u0) := by
  intro g h hgh
  have hs := socleAction_injective (M := M) eps (show
      socleAction eps (hyperplaneAnnToSocle eps φ g) =
        socleAction eps (hyperplaneAnnToSocle eps φ h) by
    rw [hyperplane_ann_factor eps φ u0 hu0 g,hyperplane_ann_factor eps φ u0 hu0 h,hgh])
  exact Subtype.ext (congrArg (fun s : algebraSocle eps => (s : A)) hs)
set_option maxHeartbeats 800000 in
theorem range_hyperplaneAnnEval [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (u0 : Top (M := M) eps) (hu0 : φ u0=1) :
    LinearMap.range (hyperplaneAnnEval eps φ u0) = fixedFunctionalFiber (socleTensor eps) φ := by
  ext v
  constructor
  · rintro ⟨g,rfl⟩
    rw [mem_fixedFunctionalFiber]
    exact ⟨hyperplaneAnnToSocle eps φ g,hyperplane_ann_factor eps φ u0 hu0 g⟩
  · intro hv
    rw [mem_fixedFunctionalFiber] at hv
    obtain ⟨s,hs⟩ := hv
    have hann : s.1 ∈ Module.annihilator A (topHyperplane eps φ) := by
      rw [mem_annihilator_submodule_iff]
      intro x hx
      have h := congrArg (fun F => (F (topProjection eps x) : M)) hs
      change s.1 • x = φ (topProjection eps x) • v.1 at h
      rw [h,(mem_topHyperplane eps φ x).mp hx,zero_smul]
    refine ⟨⟨s.1,hann⟩,?_⟩
    change socleAction eps s u0 = v
    rw [hs]
    change φ u0 • v=v
    rw [hu0,one_smul]
set_option maxHeartbeats 800000 in
def hyperplaneAnnFiberEquiv [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (φ : Module.Dual K (Top (M := M) eps)) (hφ : φ ≠ 0) :
    Module.annihilator A (topHyperplane eps φ) ≃ₗ[K]
      fixedFunctionalFiber (socleTensor eps) φ := by
  classical
  let u0 := Classical.choose (LinearMap.surjective hφ (1 : K))
  have hu0 : φ u0=1 := Classical.choose_spec (LinearMap.surjective hφ (1 : K))
  let f := hyperplaneAnnEval eps φ u0
  let f' : Module.annihilator A (topHyperplane eps φ) →ₗ[K]
      fixedFunctionalFiber (socleTensor eps) φ := f.codRestrict _ (fun g => by
    rw [← range_hyperplaneAnnEval eps φ u0 hu0]
    exact ⟨g,rfl⟩)
  apply LinearEquiv.ofBijective f'
  constructor
  · intro g h hgh
    exact hyperplaneAnnEval_injective eps φ u0 hu0 (congrArg Subtype.val hgh)
  · intro v
    have hv : v.1 ∈ LinearMap.range f := by
      rw [range_hyperplaneAnnEval eps φ u0 hu0]
      exact v.2
    obtain ⟨g,hg⟩ := hv
    exact ⟨g,Subtype.ext hg⟩
set_option maxHeartbeats 800000 in
set_option maxHeartbeats 6400000 in
def lineQuotientAnnFunctional [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (ψ : Module.Dual K (moduleSocle (M := M) eps)) :
    Module.annihilator A (M ⧸ socleLine eps v) →ₗ[K] Module.Dual K (Top (M := M) eps) where
  toFun g := ψ.comp (socleAction eps (lineQuotientAnnToSocle eps v g))
  map_add' := by
    intro g h
    ext q
    change ψ (socleAction eps
      (lineQuotientAnnToSocle eps v g+lineQuotientAnnToSocle eps v h) q) = _
    rw [map_add,LinearMap.add_apply,map_add]
    rfl
  map_smul' := by
    intro c g
    ext q
    change ψ (socleAction eps (c • lineQuotientAnnToSocle eps v g) q) = _
    rw [map_smul,LinearMap.smul_apply,map_smul]
    rfl
set_option maxHeartbeats 800000 in
theorem line_quotient_ann_factor [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (ψ : Module.Dual K (moduleSocle (M := M) eps))
    (hψ : ψ v=1) (g : Module.annihilator A (M ⧸ socleLine eps v)) :
    socleAction eps (lineQuotientAnnToSocle eps v g) =
      (lineQuotientAnnFunctional eps v ψ g).smulRight v :=
  eq_smulRight_of_range_line _ v ψ hψ (line_quotient_ann_action_range eps v g)
set_option maxHeartbeats 800000 in
theorem lineQuotientAnnFunctional_injective [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (ψ : Module.Dual K (moduleSocle (M := M) eps))
    (hψ : ψ v=1) : Function.Injective (lineQuotientAnnFunctional eps v ψ) := by
  intro g h hgh
  have hs := socleAction_injective (M := M) eps (show
      socleAction eps (lineQuotientAnnToSocle eps v g) =
        socleAction eps (lineQuotientAnnToSocle eps v h) by
    rw [line_quotient_ann_factor eps v ψ hψ g,line_quotient_ann_factor eps v ψ hψ h,hgh])
  exact Subtype.ext (congrArg (fun s : algebraSocle eps => (s : A)) hs)
set_option maxHeartbeats 800000 in
theorem range_lineQuotientAnnFunctional [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (ψ : Module.Dual K (moduleSocle (M := M) eps))
    (hψ : ψ v=1) : LinearMap.range (lineQuotientAnnFunctional eps v ψ) =
      fixedVectorFiber (socleTensor eps) v := by
  ext φ
  constructor
  · rintro ⟨g,rfl⟩
    rw [mem_fixedVectorFiber]
    exact ⟨lineQuotientAnnToSocle eps v g,line_quotient_ann_factor eps v ψ hψ g⟩
  · intro hφ
    rw [mem_fixedVectorFiber] at hφ
    obtain ⟨s,hs⟩ := hφ
    have hann : s.1 ∈ Module.annihilator A (M ⧸ socleLine eps v) := by
      rw [mem_annihilator_quotient_iff]
      intro x
      refine ⟨φ (topProjection eps x),?_⟩
      have h := congrArg (fun F => (F (topProjection eps x) : M)) hs
      exact h.symm
    refine ⟨⟨s.1,hann⟩,?_⟩
    apply LinearMap.ext
    intro q
    change ψ (socleAction eps s q) = φ q
    rw [hs]
    change ψ (φ q • v) = φ q
    rw [map_smul,hψ,smul_eq_mul,mul_one]
set_option maxHeartbeats 800000 in
def lineQuotientAnnFiberEquiv [FaithfulSMul A M] (eps : A →ₐ[K] K)
    (v : moduleSocle (M := M) eps) (hv : v ≠ 0) :
    Module.annihilator A (M ⧸ socleLine eps v) ≃ₗ[K]
      fixedVectorFiber (socleTensor eps) v := by
  classical
  let ψ := Classical.choose (Module.Projective.exists_dual_eq_one K hv)
  have hψ : ψ v=1 := Classical.choose_spec (Module.Projective.exists_dual_eq_one K hv)
  let f := lineQuotientAnnFunctional eps v ψ
  let f' : Module.annihilator A (M ⧸ socleLine eps v) →ₗ[K]
      fixedVectorFiber (socleTensor eps) v := f.codRestrict _ (fun g => by
    rw [← range_lineQuotientAnnFunctional eps v ψ hψ]
    exact ⟨g,rfl⟩)
  apply LinearEquiv.ofBijective f'
  constructor
  · intro g h hgh
    exact lineQuotientAnnFunctional_injective eps v ψ hψ (congrArg Subtype.val hgh)
  · intro φ
    have hφ : φ.1 ∈ LinearMap.range f := by
      rw [range_lineQuotientAnnFunctional eps v ψ hψ]
      exact φ.2
    obtain ⟨g,hg⟩ := hφ
    exact ⟨g,Subtype.ext hg⟩
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M]
def augmentationIdeal (eps : A →ₐ[K] K) : Ideal A := RingHom.ker eps.toRingHom
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
set_option maxHeartbeats 800000 in
abbrev actualActionImage := (Algebra.lsmul K K M : A →ₐ[K] Module.End K M).range
set_option maxHeartbeats 800000 in
theorem actualActionImage_finrank :
    finrank K (actualActionImage (K := K) (A := A) (M := M)) =
      finrank K (A ⧸ Module.annihilator A M) := by
  have hker : RingHom.ker (Algebra.lsmul K K M : A →ₐ[K] Module.End K M) =
      Module.annihilator A M := by
    ext a
    rw [RingHom.mem_ker,Module.mem_annihilator]
    constructor
    · intro h x
      exact LinearMap.congr_fun h x
    · intro h
      exact LinearMap.ext h
  rw [← hker]
  exact (Ideal.quotientKerEquivRange
    (Algebra.lsmul K K M : A →ₐ[K] Module.End K M)).toLinearEquiv.finrank_eq.symm
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
def RestrictedSafeBelow (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (t : A) (n r : ℕ) : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
    [FiniteDimensional K N],
    finrank K N<n → finrank K (LinearMap.ker (Algebra.lsmul K K N t)) ≤ r →
      finrank K (actualActionImage (K := K) (A := A) (M := N)) ≤ finrank K N
variable {K A M : Type u} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.DP2
open Module Matrix
set_option maxHeartbeats 400000 in
def scalarMulVec {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : Matrix (Fin 2) (Fin 2) R) : (Fin 2 → R) →ₗ[K] (Fin 2 → R) :=
  (Matrix.toLin' L).restrictScalars K
set_option maxHeartbeats 400000 in
def fieldRank (K : Type*) [Field K] {R : Type*} [CommRing R] [Algebra K R]
    (L : Matrix (Fin 2) (Fin 2) R) : ℕ :=
  Module.finrank K (LinearMap.range (scalarMulVec (K := K) L))
end Gerstenhaber.DP2
end
noncomputable section
namespace Gerstenhaber.IdealQuotient
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : Type*} [CommRing B] [Algebra K B]
def dualRep (ρ : B →ₐ[K] Module.End K V) : B →ₐ[K] Module.End K (Module.Dual K V) where
  toFun b := (ρ b).dualMap
  map_one' := by ext φ v; simp
  map_mul' a b := by
    ext φ v
    change φ (ρ (a*b) v) = φ (ρ b (ρ a v))
    rw [mul_comm a b, map_mul]
    rfl
  map_zero' := by ext φ v; simp
  map_add' a b := by ext φ v; simp
  commutes' c := by
    ext φ v
    change φ (ρ (algebraMap K B c) v) = c * φ v
    rw [ρ.commutes]
    simp
abbrev dualModule (ρ : B →ₐ[K] Module.End K V) : Module B (Module.Dual K V) :=
  Module.compHom _ (dualRep ρ).toRingHom
theorem dualModule_tower (ρ : B →ₐ[K] Module.End K V) :
    letI := dualModule ρ
    IsScalarTower K B (Module.Dual K V) := by
  letI := dualModule ρ
  refine ⟨fun c b φ => ?_⟩
  ext v
  change φ (ρ (c • b) v) = c * φ (ρ b v)
  rw [map_smul]
  simp
section RelativeCH
variable {A : Type*} [CommRing A] [Algebra K A]
def relativeDualRep (ρ : A →ₐ[K] Module.End K V) (B : Subalgebra K A) :
    letI := dualModule (ρ.comp B.val)
    A →ₐ[B] Module.End B (Module.Dual K V) := by
  letI := dualModule (ρ.comp B.val)
  refine
    { toFun := fun a =>
        { toFun := (ρ a).dualMap
          map_add' := fun φ ψ => by ext v; simp
          map_smul' := fun b φ => ?_ }
      map_one' := ?_
      map_mul' := ?_
      map_zero' := ?_
      map_add' := ?_
      commutes' := ?_ }
  · ext v
    change φ (ρ (b : A) (ρ a v)) = φ (ρ a (ρ (b : A) v))
    have hc : ρ (b : A) * ρ a = ρ a * ρ (b : A) := by
      rw [← map_mul, ← map_mul, mul_comm]
    exact congrArg (fun h : Module.End K V => φ (h v)) hc
  · ext φ v; simp
  · intro a b
    ext φ v
    change φ (ρ (a*b) v) = φ (ρ b (ρ a v))
    rw [mul_comm a b, map_mul]
    rfl
  · ext φ v; simp
  · intro a b; ext φ v; simp
  · intro b; ext φ v; rfl
variable {Q : Type*} [CommRing Q] [Algebra K Q]
end RelativeCH
section QuotientBridge
variable {S : Type*} [CommRing S] [Algebra K S]
def quotientIdealModule (N P : Ideal S) : Submodule S (S ⧸ N) := Submodule.map N.mkQ P
def quotientIdealAnnihilator (N P : Ideal S) : Ideal S := N.colon (P : Set S)
def quotientIdealModuleEquiv (N P : Ideal S) :
    (P ⧸ Submodule.comap P.subtype N) ≃ₗ[S] quotientIdealModule N P := by
  let f : P →ₗ[S] S ⧸ N := N.mkQ.comp P.subtype
  have hker : LinearMap.ker f = Submodule.comap P.subtype N := by
    simp only [f, LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range f = quotientIdealModule N P := by
    simp only [f, LinearMap.range_comp, Submodule.range_subtype, quotientIdealModule]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))
theorem annihilator_quotientIdealModule (N P : Ideal S) :
    Module.annihilator S (quotientIdealModule N P) = quotientIdealAnnihilator N P := by
  exact Submodule.annihilator_map_mkQ_eq_colon
def killedByIdeal (I : Ideal S) (M : Type*) [AddCommGroup M] [Module K M] [Module S M]
    [IsScalarTower K S M] : Submodule K M where
  carrier := {v | ∀ r ∈ I, r • v = 0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv r hr; simp only [smul_add, hu r hr, hv r hr, add_zero]
  smul_mem' := by
    intro c v hv r hr
    rw [smul_comm r c, hv r hr, smul_zero]
def quotientFactor (N J : Ideal S) (hNJ : N ≤ J) : (S ⧸ N) →ₐ[K] S ⧸ J :=
  Ideal.quotientMapₐ J (AlgHom.id K S) (by simpa using hNJ)
def quotientIdealToAlgebra (N P : Ideal S) :
    quotientIdealModule N P →ₗ[K] S ⧸ quotientIdealAnnihilator N P :=
  (quotientFactor N (quotientIdealAnnihilator N P) Ideal.le_colon).toLinearMap.comp
    ((quotientIdealModule N P).subtype.restrictScalars K)
@[simp] theorem quotientIdealToAlgebra_mk (N P : Ideal S) (p : S) (hp : p ∈ P) :
    quotientIdealToAlgebra (K := K) N P ⟨N.mkQ p, Submodule.mem_map_of_mem hp⟩ =
      Ideal.Quotient.mk (quotientIdealAnnihilator N P) p := rfl
def imageIdeal (N P : Ideal S) : Ideal (S ⧸ quotientIdealAnnihilator N P) :=
  P.map (Ideal.Quotient.mk (quotientIdealAnnihilator N P))
def quotientIdealRep (N P : Ideal S) :
    (S ⧸ quotientIdealAnnihilator N P) →ₐ[K] Module.End K (quotientIdealModule N P) :=
  Ideal.Quotient.liftₐ (quotientIdealAnnihilator N P)
    (Algebra.lsmul K K (quotientIdealModule N P)) (by
      intro r hr
      apply LinearMap.ext
      intro m
      have hm : r ∈ Module.annihilator S (quotientIdealModule N P) := by
        rwa [annihilator_quotientIdealModule]
      exact (Module.mem_annihilator.mp hm) m)
@[simp] theorem quotientIdealRep_mk (N P : Ideal S) (r : S) :
    quotientIdealRep (K := K) N P (Ideal.Quotient.mk (quotientIdealAnnihilator N P) r) =
      Algebra.lsmul K K (quotientIdealModule N P) r := rfl
variable {Q : Type*} [CommRing Q] [Algebra K Q]
end QuotientBridge
end Gerstenhaber.IdealQuotient
end
noncomputable section
namespace Gerstenhaber.DP2
open Module Matrix
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T]
set_option maxHeartbeats 800000 in
def linearColumnMap (a b : T) : T →ₗ[T] (Fin 2 → T) where
  toFun c := ![a*c,b*c]
  map_add' c d := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' c d := by ext i; fin_cases i <;> simp [mul_left_comm]
set_option maxHeartbeats 800000 in
@[simp] theorem linearColumnMap_apply (a b c : T) :
    linearColumnMap a b c = ![a*c,b*c] := rfl
set_option maxHeartbeats 800000 in
def linearColumnMatrix (f g y z : T) : Matrix (Fin 2) (Fin 2) T :=
  !![f,y;g,z]
set_option maxHeartbeats 800000 in
def columnClassMap (f g y z : T) :
    T →ₗ[T] ((Fin 2 → T) ⧸ LinearMap.range (linearColumnMap y z)) :=
  (LinearMap.range (linearColumnMap y z)).mkQ.comp (linearColumnMap f g)
set_option maxHeartbeats 800000 in
def columnClassIdeal (f g y z : T) : Ideal T :=
  LinearMap.ker (columnClassMap f g y z)
end Gerstenhaber.DP2
end
noncomputable section
namespace Gerstenhaber.FourBlocks
open scoped Matrix
open Matrix Module Polynomial
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
def LiteralThreeFrame (U V : Module.End K E) : Prop :=
  ∃ u, LinearIndependent K (![u,U u,V u] : Fin 3 → E)
def LocallyDependentTriple (U V : Module.End K E) : Prop :=
  ∀ u, ¬ LinearIndependent K (![u,U u,V u] : Fin 3 → E)
@[simp] theorem alt_three_repeat_left (f : E [⋀^Fin 3]→ₗ[K] K) (a b : E) :
    f ![a,b,a]=0 :=
  f.map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)
@[simp] theorem alt_three_repeat_right (f : E [⋀^Fin 3]→ₗ[K] K) (a b : E) :
    f ![a,b,b]=0 :=
  f.map_eq_zero_of_eq _ (i := 1) (j := 2) rfl (by decide)
section MatrixCorollaries
variable {n : Type*} [Fintype n] [DecidableEq n]
end MatrixCorollaries
end Gerstenhaber.FourBlocks
end
noncomputable section
namespace Gerstenhaber.DP2
open Module Matrix
section LocalGeneration
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T]
set_option maxHeartbeats 1000000 in
theorem scalar_mod_ideal_of_adjoin_eq_top (m : Ideal T) (s : Set T)
    (hs : s ⊆ m) (hgen : Algebra.adjoin K s=⊤) :
    ∀ a : T, ∃ c : K, a-algebraMap K T c ∈ m := by
  let q : T →ₐ[K] T ⧸ m := Ideal.Quotient.mkₐ K m
  have hle : Algebra.adjoin K s ≤ (⊥ : Subalgebra K (T ⧸ m)).comap q := by
    apply Algebra.adjoin_le
    intro a ha
    change q a ∈ (⊥ : Subalgebra K (T ⧸ m))
    have hz : q a=0 := Ideal.Quotient.eq_zero_iff_mem.mpr (hs ha)
    rw [hz]
    exact Subalgebra.zero_mem _
  intro a
  obtain ⟨c,hc⟩ := Algebra.mem_bot.mp (hle (by rw [hgen]; trivial) :
    q a ∈ (⊥ : Subalgebra K (T ⧸ m)))
  refine ⟨c,Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  change q (a-algebraMap K T c)=0
  rw [map_sub,AlgHom.commutes,hc]
  exact sub_self (q a)
end LocalGeneration
end Gerstenhaber.DP2
namespace Gerstenhaber.DP2
open Module Matrix
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
end Gerstenhaber.DP2
namespace Gerstenhaber.DP2
open Module Matrix
variable {K T : Type*} [Field K] [CommRing T] [Algebra K T]
set_option maxHeartbeats 1000000 in
def matrixEntryIdeal (L : Matrix (Fin 2) (Fin 2) T) : Ideal T :=
  Ideal.span (Set.range (fun p : Fin 2 × Fin 2 => L p.1 p.2))
end Gerstenhaber.DP2
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module
variable {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
def nilGeneratorIdeal (r : ι → A) : Ideal A := Ideal.span (Set.range r)
theorem nilGeneratorIdeal_le_nilradical (r : ι → A) (hnil : ∀ i, IsNilpotent (r i)) :
    nilGeneratorIdeal r ≤ nilradical A := by
  apply Ideal.span_le.mpr
  rintro a ⟨i,rfl⟩
  exact mem_nilradical.mpr (hnil i)
theorem nilGeneratorIdeal_ne_top [Nontrivial A]
    (r : ι → A) (hnil : ∀ i, IsNilpotent (r i)) : nilGeneratorIdeal r ≠ ⊤ := by
  intro htop
  have hnilone : IsNilpotent (1 : A) :=
    mem_nilradical.mp (nilGeneratorIdeal_le_nilradical r hnil (by rw [htop]; trivial))
  exact not_isNilpotent_one hnilone
theorem scalar_residue_bijective [Nontrivial A] (r : ι → A)
    (hnil : ∀ i, IsNilpotent (r i))
    (hgen : Algebra.adjoin K (Set.range r) = ⊤) :
    Function.Bijective (algebraMap K (A ⧸ nilGeneratorIdeal r)) := by
  let : Nontrivial (A ⧸ nilGeneratorIdeal r) :=
    Ideal.Quotient.nontrivial_iff.mpr (nilGeneratorIdeal_ne_top r hnil)
  refine ⟨(algebraMap K (A ⧸ nilGeneratorIdeal r)).injective, ?_⟩
  intro q
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨c,hc⟩ := Gerstenhaber.DP2.scalar_mod_ideal_of_adjoin_eq_top
    (nilGeneratorIdeal r) (Set.range r) Ideal.subset_span hgen a
  refine ⟨c, ?_⟩
  change Ideal.Quotient.mk (nilGeneratorIdeal r) (algebraMap K A c) =
    Ideal.Quotient.mk (nilGeneratorIdeal r) a
  exact (Ideal.Quotient.eq.mpr hc).symm
def scalarResidueEquiv [Nontrivial A] (r : ι → A)
    (hnil : ∀ i, IsNilpotent (r i))
    (hgen : Algebra.adjoin K (Set.range r) = ⊤) :
    K ≃ₐ[K] A ⧸ nilGeneratorIdeal r :=
  AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ nilGeneratorIdeal r))
    (scalar_residue_bijective r hnil hgen)
def nilGeneratorAugmentation [Nontrivial A] (r : ι → A)
    (hnil : ∀ i, IsNilpotent (r i))
    (hgen : Algebra.adjoin K (Set.range r) = ⊤) : A →ₐ[K] K :=
  (scalarResidueEquiv r hnil hgen).symm.toAlgHom.comp
    (Ideal.Quotient.mkₐ K (nilGeneratorIdeal r))
theorem nilGeneratorAugmentation_ker [Nontrivial A] (r : ι → A)
    (hnil : ∀ i, IsNilpotent (r i))
    (hgen : Algebra.adjoin K (Set.range r) = ⊤) :
    augmentationIdeal (nilGeneratorAugmentation r hnil hgen) = nilGeneratorIdeal r := by
  ext a
  change (scalarResidueEquiv r hnil hgen).symm
    (Ideal.Quotient.mk (nilGeneratorIdeal r) a) = 0 ↔ a ∈ nilGeneratorIdeal r
  rw [map_eq_zero_iff _ (scalarResidueEquiv r hnil hgen).symm.injective]
  exact Ideal.Quotient.eq_zero_iff_mem
@[simp] theorem nilGeneratorAugmentation_root [Nontrivial A] (r : ι → A)
    (hnil : ∀ i, IsNilpotent (r i))
    (hgen : Algebra.adjoin K (Set.range r) = ⊤) (i : ι) :
    nilGeneratorAugmentation r hnil hgen (r i) = 0 := by
  change r i ∈ augmentationIdeal (nilGeneratorAugmentation r hnil hgen)
  rw [nilGeneratorAugmentation_ker]
  exact Ideal.subset_span ⟨i,rfl⟩
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
def NilThreeSafeBelow (K : Type u) [Field K] (n r : ℕ) : Prop :=
  ∀ (N : Type u) [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (X : Fin 3 → Module.End K N),
    (∀ i j, Commute (X i) (X j)) → (∀ i, IsNilpotent (X i)) →
    finrank K N < n → finrank K (LinearMap.ker (X 0)) ≤ r →
      finrank K (Algebra.adjoin K (Set.range X)) ≤ finrank K N
variable {K A M : Type u} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
def inducedTriple (r : Fin 3 → A) : Fin 3 → Module.End K M :=
  fun i => Algebra.lsmul K K M (r i)
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
open scoped IsMulCommutative
structure FiniteNilTriple (K : Type u) [Field K] where
  Carrier : Type u
  [addCommGroup : AddCommGroup Carrier]
  [module : Module K Carrier]
  [finiteDimensional : FiniteDimensional K Carrier]
  operator : Fin 3 → Module.End K Carrier
  commute : ∀ i j, Commute (operator i) (operator j)
  nilpotent : ∀ i, IsNilpotent (operator i)
instance FiniteNilTriple.instAddCommGroup {K : Type u} [Field K] (X : FiniteNilTriple K) :
    AddCommGroup X.Carrier := X.addCommGroup
instance FiniteNilTriple.instModule {K : Type u} [Field K] (X : FiniteNilTriple K) :
    Module K X.Carrier := X.module
instance FiniteNilTriple.instFiniteDimensional {K : Type u} [Field K] (X : FiniteNilTriple K) :
    FiniteDimensional K X.Carrier := X.finiteDimensional
variable {K : Type u} [Field K]
abbrev FiniteNilTriple.of (M : Type u) [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (X : Fin 3 → Module.End K M)
    (hcomm : ∀ i j, Commute (X i) (X j)) (hnil : ∀ i, IsNilpotent (X i)) :
    FiniteNilTriple K := ⟨M,X,hcomm,hnil⟩
def sourceAlgebra (X : FiniteNilTriple K) :
    Subalgebra K (Module.End K X.Carrier) :=
  Algebra.adjoin K (Set.range X.operator)
abbrev SourceAlgebra (X : FiniteNilTriple K) := sourceAlgebra X
instance sourceAlgebra_commutative (X : FiniteNilTriple K) :
    IsMulCommutative (SourceAlgebra X) := by
  apply Algebra.isMulCommutative_adjoin
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
  exact (X.commute i j).eq
instance sourceAlgebra_commRing (X : FiniteNilTriple K) : CommRing (SourceAlgebra X) :=
  inferInstance
instance sourceAlgebra_tower (X : FiniteNilTriple K) :
    IsScalarTower K (SourceAlgebra X) X.Carrier := ⟨fun _ _ _ => rfl⟩
instance sourceAlgebra_faithful (X : FiniteNilTriple K) :
    FaithfulSMul (SourceAlgebra X) X.Carrier :=
  ⟨fun h => Subtype.ext (LinearMap.ext h)⟩
def sourceRoot (X : FiniteNilTriple K) (i : Fin 3) : SourceAlgebra X :=
  ⟨X.operator i,Algebra.subset_adjoin ⟨i,rfl⟩⟩
@[simp] theorem sourceRoot_val (X : FiniteNilTriple K) (i : Fin 3) :
    (sourceRoot X i : Module.End K X.Carrier) = X.operator i := rfl
@[simp] theorem sourceRoot_lsmul (X : FiniteNilTriple K) (i : Fin 3) :
    Algebra.lsmul K K X.Carrier (sourceRoot X i) = X.operator i := rfl
theorem sourceRoot_nilpotent (X : FiniteNilTriple K) (i : Fin 3) :
    IsNilpotent (sourceRoot X i) := by
  exact (IsNilpotent.map_iff (f := (sourceAlgebra X).val) Subtype.val_injective).mp
    (X.nilpotent i)
theorem sourceRoot_adjoin_eq_top (X : FiniteNilTriple K) :
    Algebra.adjoin K (Set.range (sourceRoot X)) = ⊤ := by
  apply Subalgebra.map_injective (f := (sourceAlgebra X).val) Subtype.val_injective
  rw [AlgHom.map_adjoin,Algebra.map_top,Subalgebra.range_val]
  have hs : (sourceAlgebra X).val '' Set.range (sourceRoot X) =
      Set.range X.operator := by
    ext y
    constructor
    · rintro ⟨a,⟨i,rfl⟩,rfl⟩
      exact ⟨i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨sourceRoot X i,⟨i,rfl⟩,rfl⟩
  rw [hs]
  rfl
theorem sourceActionImage_eq (X : FiniteNilTriple K) :
    actualActionImage (K := K) (A := SourceAlgebra X) (M := X.Carrier) = sourceAlgebra X := by
  ext f
  constructor
  · rintro ⟨a,rfl⟩
    exact a.property
  · intro hf
    exact ⟨⟨f,hf⟩,rfl⟩
theorem sourceAlgebra_finrank_le_square (X : FiniteNilTriple K) :
    finrank K (SourceAlgebra X) ≤ (finrank K X.Carrier)^2 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := (sourceAlgebra X).val.toLinearMap) Subtype.val_injective
  rw [Module.finrank_linearMap] at h
  simpa only [pow_two] using h
theorem sourceCarrier_nontrivial_of_failure (X : FiniteNilTriple K)
    (hbad : finrank K X.Carrier < finrank K (SourceAlgebra X)) : Nontrivial X.Carrier := by
  by_contra h
  let : Subsingleton X.Carrier := not_nontrivial_iff_subsingleton.mp h
  have hzero : finrank K X.Carrier = 0 := Module.finrank_zero_of_subsingleton
  have hle := sourceAlgebra_finrank_le_square X
  rw [hzero] at hbad hle
  omega
def sourceAugmentation (X : FiniteNilTriple K) [Nontrivial X.Carrier] :
    SourceAlgebra X →ₐ[K] K :=
  nilGeneratorAugmentation (sourceRoot X) (sourceRoot_nilpotent X)
    (sourceRoot_adjoin_eq_top X)
@[simp] theorem sourceAugmentation_root (X : FiniteNilTriple K) [Nontrivial X.Carrier]
    (i : Fin 3) : sourceAugmentation X (sourceRoot X i) = 0 :=
  nilGeneratorAugmentation_root _ _ _ i
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K : Type u} [Field K]
def NilThreeCounterAt (K : Type u) [Field K] (k n : ℕ) : Prop :=
  ∃ X : FiniteNilTriple K,
    finrank K X.Carrier = n ∧ finrank K (LinearMap.ker (X.operator 0)) ≤ k ∧
      finrank K X.Carrier < finrank K (SourceAlgebra X)
structure MinimalNilThreeCounter (K : Type u) [Field K] (k : ℕ) where
  source : FiniteNilTriple K
  block_bound : finrank K (LinearMap.ker (source.operator 0)) ≤ k
  failure : finrank K source.Carrier < finrank K (SourceAlgebra source)
  shorter_safe : NilThreeSafeBelow K (finrank K source.Carrier) k
namespace MinimalNilThreeCounter
variable {k : ℕ} (X : MinimalNilThreeCounter K k)
instance carrier_nontrivial : Nontrivial X.source.Carrier :=
  sourceCarrier_nontrivial_of_failure X.source X.failure
def excess : ℕ := finrank K (SourceAlgebra X.source)-finrank K X.source.Carrier
def augmentation : SourceAlgebra X.source →ₐ[K] K := sourceAugmentation X.source
end MinimalNilThreeCounter
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.CanonicalExtension
open Module
variable {K A R0 : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing R0] [Algebra K R0]
abbrev canonicalParentModule (pi : A →ₐ[K] R0) : Module A (Module.Dual K R0) :=
  Gerstenhaber.IdealQuotient.dualModule
    ((Algebra.lsmul K K R0 : R0 →ₐ[K] Module.End K R0).comp pi)
end Gerstenhaber.CanonicalExtension
end
noncomputable section
namespace Gerstenhaber.DP2.LinearRow
variable {B : Type*} [CommRing B]
variable {P Q T : Type*} [AddCommGroup P] [Module B P]
  [AddCommGroup Q] [Module B Q] [AddCommGroup T] [Module B T]
def mapPullback (f : P →ₗ[B] T) (g : Q →ₗ[B] T) : Submodule B (P × Q) where
  carrier := {v | f v.1 = g v.2}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw; simpa using congrArg₂ HAdd.hAdd hv hw
  smul_mem' := by intro b v hv; simpa using congrArg (b • ·) hv
def mapPullbackSplit (f : P →ₗ[B] T) (g : Q →ₗ[B] T)
    (l : P →ₗ[B] Q) (hl : g.comp l = f) :
    (LinearMap.ker g × P) ≃ₗ[B] mapPullback f g where
  toFun v := ⟨(v.2,v.1+l v.2),by
    change f v.2 = g (↑v.1 + l v.2)
    rw [map_add,v.1.property,zero_add]
    exact (DFunLike.congr_fun hl v.2).symm⟩
  invFun v := (⟨v.1.2-l v.1.1,by
    change g (v.1.2-l v.1.1)=0
    have hlv : g (l v.1.1)=f v.1.1 := DFunLike.congr_fun hl v.1.1
    rw [map_sub,hlv]
    exact sub_eq_zero.mpr v.property.symm⟩,v.1.1)
  left_inv v := by ext <;> simp
  right_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show (v.1.2 - l v.1.1) + l v.1.1 = v.1.2
      abel
  map_add' v w := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show ((v.1 + w.1 : LinearMap.ker g) : Q) + l (v.2 + w.2) =
        ((v.1 : Q) + l v.2) + ((w.1 : Q) + l w.2)
      rw [map_add, Submodule.coe_add]
      abel
  map_smul' b v := by ext <;> simp [smul_add]
def mapPullbackSwap (f : P →ₗ[B] T) (g : Q →ₗ[B] T) :
    mapPullback f g ≃ₗ[B] mapPullback g f where
  toFun v := ⟨(v.1.2,v.1.1),v.property.symm⟩
  invFun v := ⟨(v.1.2,v.1.1),v.property.symm⟩
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' b v := rfl
def schanuelEquiv [Module.Projective B P] [Module.Projective B Q]
    (f : P →ₗ[B] T) (g : Q →ₗ[B] T)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (LinearMap.ker f × Q) ≃ₗ[B] (LinearMap.ker g × P) := by
  let l := Classical.choose (Module.projective_lifting_property g f hg)
  have hl := Classical.choose_spec (Module.projective_lifting_property g f hg)
  let m := Classical.choose (Module.projective_lifting_property f g hf)
  have hm := Classical.choose_spec (Module.projective_lifting_property f g hf)
  exact (mapPullbackSplit g f m hm).trans
    ((mapPullbackSwap g f).trans (mapPullbackSplit f g l hl).symm)
def kernelProdIdEquiv (f : P →ₗ[B] T) (Q : Type*)
    [AddCommGroup Q] [Module B Q] :
    LinearMap.ker (f.prodMap (LinearMap.id : Q →ₗ[B] Q)) ≃ₗ[B]
      LinearMap.ker f where
  toFun v := ⟨v.1.1,by
    have hv := congrArg Prod.fst v.property
    exact hv⟩
  invFun v := ⟨(v.1,0),by
    apply Prod.ext
    · exact v.property
    · rfl⟩
  left_inv v := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hv := congrArg Prod.snd v.property
      exact hv.symm
  right_inv v := rfl
  map_add' v w := rfl
  map_smul' b v := rfl
def syzygyMap {P₁ : Type*} [AddCommGroup P₁] [Module B P₁]
    (f₀ : P →ₗ[B] T) (f₁ : P₁ →ₗ[B] P) (hzero : f₀.comp f₁=0) :
    P₁ →ₗ[B] LinearMap.ker f₀ :=
  f₁.codRestrict (LinearMap.ker f₀) (fun p => DFunLike.congr_fun hzero p)
end Gerstenhaber.DP2.LinearRow
end
noncomputable section
namespace Gerstenhaber.DP2.LinearRow
variable {B R : Type*} [CommRing B] [CommRing R] [Algebra B R]
set_option maxHeartbeats 600000 in
def frobeniusPairing (τ : R →ₗ[B] B) : R →ₗ[B] Module.Dual B R where
  toFun a :=
    { toFun := fun b => τ (a*b)
      map_add' b c := by simp [mul_add]
      map_smul' b c := by
        change τ (a*(b • c))=b • τ (a*c)
        rw [Algebra.mul_smul_comm,τ.map_smul] }
  map_add' a b := by ext c; simp [add_mul]
  map_smul' b a := by
    ext c
    change τ ((b • a)*c)=b • τ (a*c)
    rw [Algebra.smul_mul_assoc,τ.map_smul]
set_option maxHeartbeats 600000 in
@[simp] theorem frobeniusPairing_apply (τ : R →ₗ[B] B) (a b : R) :
    frobeniusPairing τ a b=τ (a*b) := rfl
variable {M : Type*} [AddCommGroup M] [Module B M] [Module R M]
  [IsScalarTower B R M]
set_option maxHeartbeats 600000 in
def actionFunctional (l : M →ₗ[B] B) : M →ₗ[B] Module.Dual B R where
  toFun m :=
    { toFun := fun r => l (r • m)
      map_add' r s := by simp [add_smul]
      map_smul' b r := by rw [smul_assoc,l.map_smul]; rfl }
  map_add' m n := by ext r; simp [smul_add]
  map_smul' b m := by
    ext r
    change l (r • (b • m))=b • l (r • m)
    rw [smul_comm,l.map_smul]
set_option maxHeartbeats 600000 in
@[simp] theorem actionFunctional_apply (l : M →ₗ[B] B) (m : M) (r : R) :
    actionFunctional l m r=l (r • m) := rfl
set_option maxHeartbeats 600000 in
def frobeniusInverseMap (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ)) (l : M →ₗ[B] B) :
    M →ₗ[R] R where
  toFun m := (LinearEquiv.ofBijective (frobeniusPairing τ) hτ).symm (actionFunctional l m)
  map_add' m n := by simp only [map_add]
  map_smul' a m := by
    apply hτ.injective
    ext r
    have h (m : M) (r : R) :
        τ ((LinearEquiv.ofBijective (frobeniusPairing τ) hτ).symm
          (actionFunctional l m)*r)=l (r • m) := by
      exact congrArg (fun f : Module.Dual B R => f r)
        ((LinearEquiv.ofBijective (frobeniusPairing τ) hτ).apply_symm_apply
          (actionFunctional l m))
    change τ (_*r)=τ ((a*_)*r)
    rw [h,show (a*(LinearEquiv.ofBijective (frobeniusPairing τ) hτ).symm
      (actionFunctional l m))*r=
      ((LinearEquiv.ofBijective (frobeniusPairing τ) hτ).symm
        (actionFunctional l m))*(r*a) by ring,h]
    rw [mul_smul]
set_option maxHeartbeats 600000 in
theorem frobeniusInverseMap_spec (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ)) (l : M →ₗ[B] B)
    (m : M) (r : R) :
    τ (frobeniusInverseMap τ hτ l m*r)=l (r • m) :=
  congrArg (fun f : Module.Dual B R => f r)
    ((LinearEquiv.ofBijective (frobeniusPairing τ) hτ).apply_symm_apply
      (actionFunctional l m))
set_option maxHeartbeats 600000 in
def frobeniusDualEquiv (τ : R →ₗ[B] B)
    (hτ : Function.Bijective (frobeniusPairing τ)) :
    (M →ₗ[R] R) ≃ₗ[B] (M →ₗ[B] B) where
  toFun f := τ.comp (f.restrictScalars B)
  invFun := frobeniusInverseMap τ hτ
  left_inv f := by
    apply LinearMap.ext
    intro m
    apply hτ.injective
    ext r
    rw [frobeniusPairing_apply,frobeniusInverseMap_spec]
    change τ (f (r • m))=τ (f m*r)
    rw [f.map_smul]
    congr 1
    exact mul_comm _ _
  right_inv l := by
    apply LinearMap.ext
    intro m
    have h := frobeniusInverseMap_spec τ hτ l m 1
    simpa using h
  map_add' f g := by ext m; simp
  map_smul' b f := by ext m; simp
section KernelSplitting
variable {X F : Type*} [AddCommGroup X] [Module B X]
  [AddCommGroup F] [Module B F]
end KernelSplitting
section RelativeInjectivity
variable {X F D : Type*} [AddCommGroup X] [Module B X] [Module R X]
  [IsScalarTower B R X] [AddCommGroup F] [Module B F] [Module R F]
  [IsScalarTower B R F] [AddCommGroup D] [Module B D] [Module R D]
  [IsScalarTower B R D]
end RelativeInjectivity
end Gerstenhaber.DP2.LinearRow
end
noncomputable section
namespace Gerstenhaber.DP2.LinearRow
open Module Polynomial
variable {B : Type*} [CommRing B] [Nontrivial B] {P : B[X]}
set_option maxHeartbeats 1000000 in
def monicCoeffTrace (hP : P.Monic) : AdjoinRoot P →ₗ[B] B :=
  (Polynomial.lcoeff B (P.natDegree-1)).comp (AdjoinRoot.modByMonicHom hP)
set_option maxHeartbeats 1000000 in
omit [Nontrivial B] in
@[simp] theorem monicCoeffTrace_apply (hP : P.Monic) (a : AdjoinRoot P) :
    monicCoeffTrace hP a =
      (AdjoinRoot.modByMonicHom hP a).coeff (P.natDegree-1) := rfl
set_option maxHeartbeats 1000000 in
omit [Nontrivial B] in
@[simp] theorem monicCoeffTrace_mk (hP : P.Monic) (q : B[X]) :
    monicCoeffTrace hP (AdjoinRoot.mk P q) =
      (q %ₘ P).coeff (P.natDegree-1) := rfl
set_option maxHeartbeats 1000000 in
def monicFrobeniusPairing (hP : P.Monic) :
    AdjoinRoot P →ₗ[B] Module.Dual B (AdjoinRoot P) where
  toFun a :=
    { toFun := fun b => monicCoeffTrace hP (a*b)
      map_add' := by intro b c; simp [mul_add]
      map_smul' := by intro b c; simp }
  map_add' a b := by ext c; simp [add_mul]
  map_smul' b a := by ext c; simp
set_option maxHeartbeats 1000000 in
omit [Nontrivial B] in
@[simp] theorem monicFrobeniusPairing_apply (hP : P.Monic) (a b : AdjoinRoot P) :
    monicFrobeniusPairing hP a b = monicCoeffTrace hP (a*b) := rfl
set_option maxHeartbeats 1000000 in
theorem monicCoeffTrace_root_pow (hP : P.Monic) {n : ℕ} (hn : n<P.natDegree) :
    monicCoeffTrace hP (AdjoinRoot.root P ^ n) =
      if P.natDegree-1=n then 1 else 0 := by
  have hpow : AdjoinRoot.mk P (X^n) = AdjoinRoot.root P ^ n := by simp
  rw [← hpow, monicCoeffTrace_mk,
    (Polynomial.modByMonic_eq_self_iff hP).mpr]
  · exact Polynomial.coeff_X_pow _ _
  · rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hP.ne_zero]
    exact_mod_cast hn
set_option maxHeartbeats 1000000 in
def monicPowerBasis (hP : P.Monic) : Basis (Fin P.natDegree) B (AdjoinRoot P) :=
  (AdjoinRoot.powerBasis' hP).basis
set_option maxHeartbeats 1000000 in
def monicReversePowerBasis (hP : P.Monic) : Basis (Fin P.natDegree) B (AdjoinRoot P) :=
  (monicPowerBasis hP).reindex Fin.revPerm
set_option maxHeartbeats 1000000 in
omit [Nontrivial B] in
@[simp] theorem monicPowerBasis_apply (hP : P.Monic) (i : Fin P.natDegree) :
    monicPowerBasis hP i = AdjoinRoot.root P ^ i.val := by
  exact (AdjoinRoot.powerBasis' hP).basis_eq_pow i
set_option maxHeartbeats 1000000 in
omit [Nontrivial B] in
@[simp] theorem monicReversePowerBasis_apply (hP : P.Monic) (i : Fin P.natDegree) :
    monicReversePowerBasis hP i = AdjoinRoot.root P ^ i.rev.val := by
  simp [monicReversePowerBasis, Basis.reindex_apply, Fin.revPerm_symm]
set_option maxHeartbeats 1000000 in
def monicReverseGram (hP : P.Monic) : Matrix (Fin P.natDegree) (Fin P.natDegree) B :=
  fun i j => monicCoeffTrace hP (AdjoinRoot.root P ^ (i.val+j.rev.val))
set_option maxHeartbeats 1000000 in
theorem monicReverseGram_lowerTriangular (hP : P.Monic) :
    (monicReverseGram hP).IsLowerTriangular := by
  intro i j hij
  have hij' : i.val<j.val := hij
  have hsum : i.val+j.rev.val<P.natDegree-1 := by
    simp only [Fin.val_rev]
    omega
  change monicCoeffTrace hP (AdjoinRoot.root P ^ (i.val+j.rev.val))=0
  rw [monicCoeffTrace_root_pow hP (by omega)]
  exact if_neg (ne_of_gt hsum)
set_option maxHeartbeats 1000000 in
@[simp] theorem monicReverseGram_diagonal (hP : P.Monic) (i : Fin P.natDegree) :
    monicReverseGram hP i i=1 := by
  have hsum : i.val+i.rev.val=P.natDegree-1 := by
    simp only [Fin.val_rev]
    omega
  change monicCoeffTrace hP (AdjoinRoot.root P ^ (i.val+i.rev.val))=1
  rw [monicCoeffTrace_root_pow hP (by omega)]
  exact if_pos hsum.symm
set_option maxHeartbeats 1000000 in
theorem monicReverseGram_det (hP : P.Monic) :
    (monicReverseGram hP).det=1 := by
  rw [Matrix.det_of_isLowerTriangular _ (monicReverseGram_lowerTriangular hP)]
  simp
set_option maxHeartbeats 1000000 in
omit [Nontrivial B] in
theorem monicFrobeniusPairing_matrix (hP : P.Monic) :
    LinearMap.toMatrix (monicReversePowerBasis hP) (monicPowerBasis hP).dualBasis
      (monicFrobeniusPairing hP) = monicReverseGram hP := by
  ext i j
  rw [LinearMap.toMatrix_apply, Basis.dualBasis_repr,
    monicFrobeniusPairing_apply, monicReversePowerBasis_apply, monicPowerBasis_apply,
    ← pow_add]
  change monicCoeffTrace hP (AdjoinRoot.root P ^ (j.rev.val+i.val)) =
    monicCoeffTrace hP (AdjoinRoot.root P ^ (i.val+j.rev.val))
  rw [Nat.add_comm]
set_option maxHeartbeats 1000000 in
theorem monicFrobeniusPairing_bijective (hP : P.Monic) :
    Function.Bijective (monicFrobeniusPairing hP) := by
  have hdet : IsUnit (LinearMap.toMatrix (monicReversePowerBasis hP)
      (monicPowerBasis hP).dualBasis (monicFrobeniusPairing hP)).det := by
    rw [monicFrobeniusPairing_matrix, monicReverseGram_det]
    exact isUnit_one
  exact (LinearEquiv.ofIsUnitDet hdet).bijective
set_option maxHeartbeats 1000000 in
def monicFrobeniusEquiv (hP : P.Monic) :
    AdjoinRoot P ≃ₗ[B] Module.Dual B (AdjoinRoot P) :=
  LinearEquiv.ofBijective (monicFrobeniusPairing hP) (monicFrobeniusPairing_bijective hP)
set_option maxHeartbeats 1000000 in
@[simp] theorem monicFrobeniusEquiv_apply (hP : P.Monic) (a b : AdjoinRoot P) :
    monicFrobeniusEquiv hP a b=monicCoeffTrace hP (a*b) := rfl
end Gerstenhaber.DP2.LinearRow
end
noncomputable section
namespace Gerstenhaber.CanonicalExtension
open Module LinearMap
open Gerstenhaber.DP2.LinearRow
variable {K B : Type*} [Field K] [CommRing B] [Algebra K B]
def determinantForm (tau : B →ₗ[K] K) : LinearMap.BilinForm K (B × B) :=
  (frobeniusPairing tau).compl₁₂ (LinearMap.fst K B B) (LinearMap.snd K B B) -
    (frobeniusPairing tau).compl₁₂ (LinearMap.snd K B B) (LinearMap.fst K B B)
@[simp] theorem determinantForm_apply (tau : B →ₗ[K] K) (x y : B × B) :
    determinantForm tau x y = tau (x.1 * y.2 - x.2 * y.1) := by
  simp [determinantForm, map_sub]
end Gerstenhaber.CanonicalExtension
end
noncomputable section
namespace Gerstenhaber.CanonicalExtension
open Gerstenhaber.DP2.LinearRow
variable {K A B : Type*} [Field K] [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B]
abbrev quotientKernelModule (pi : A →ₐ[K] B) : Module A B :=
  Module.compHom B pi.toRingHom
def kernelFrobeniusMap (pi : A →ₐ[K] B) (tau : B →ₗ[K] K) :
    letI := quotientKernelModule pi
    letI := canonicalParentModule pi
    B →ₗ[A] Module.Dual K B := by
  let := quotientKernelModule pi
  let := canonicalParentModule pi
  exact
    { toFun := frobeniusPairing tau
      map_add' := (frobeniusPairing tau).map_add
      map_smul' := by
        intro a b
        ext c
        change tau ((pi a*b)*c) = tau (b*(pi a*c))
        simp only [mul_assoc,mul_left_comm] }
theorem kernelFrobeniusMap_bijective (pi : A →ₐ[K] B) (tau : B →ₗ[K] K)
    (htau : Function.Bijective (frobeniusPairing tau)) :
    letI := quotientKernelModule pi
    letI := canonicalParentModule pi
    Function.Bijective (kernelFrobeniusMap pi tau) := by
  exact htau
def kernelFrobeniusEquiv (pi : A →ₐ[K] B) (tau : B →ₗ[K] K)
    (htau : Function.Bijective (frobeniusPairing tau)) :
    letI := quotientKernelModule pi
    letI := canonicalParentModule pi
    B ≃ₗ[A] Module.Dual K B := by
  let := quotientKernelModule pi
  let := canonicalParentModule pi
  exact LinearEquiv.ofBijective (kernelFrobeniusMap pi tau)
    (kernelFrobeniusMap_bijective pi tau htau)
end Gerstenhaber.CanonicalExtension
end
noncomputable section
namespace Gerstenhaber.CanonicalExtension
open Module
variable {K A M N Q : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
  [AddCommGroup Q] [Module A Q] [Module K Q] [IsScalarTower K A Q]
abbrev positiveDualModule : Module A (Module.Dual K M) :=
  Gerstenhaber.IdealQuotient.dualModule (Algebra.lsmul K K M)
theorem positiveDual_tower :
    letI := positiveDualModule (K := K) (A := A) (M := M)
    IsScalarTower K A (Module.Dual K M) :=
  Gerstenhaber.IdealQuotient.dualModule_tower _
def positiveDualMap (f : M →ₗ[A] N) :
    letI := positiveDualModule (K := K) (A := A) (M := N)
    letI := positiveDualModule (K := K) (A := A) (M := M)
    Module.Dual K N →ₗ[A] Module.Dual K M := by
  let := positiveDualModule (K := K) (A := A) (M := N)
  let := positiveDualModule (K := K) (A := A) (M := M)
  exact
    { toFun := (f.restrictScalars K).dualMap
      map_add' := (f.restrictScalars K).dualMap.map_add
      map_smul' := by
        intro a phi
        ext x
        change phi (a • f x) = phi (f (a • x))
        rw [f.map_smul] }
@[simp] theorem positiveDualMap_apply (f : M →ₗ[A] N)
    (phi : Module.Dual K N) (x : M) : positiveDualMap (K := K) f phi x = phi (f x) := rfl
theorem positiveDual_annihilator :
    letI := positiveDualModule (K := K) (A := A) (M := M)
    Module.annihilator A (Module.Dual K M) = Module.annihilator A M := by
  let := positiveDualModule (K := K) (A := A) (M := M)
  ext a
  rw [Module.mem_annihilator,Module.mem_annihilator]
  constructor
  · intro ha x
    apply (Module.forall_dual_apply_eq_zero_iff K (a • x)).mp
    intro phi
    exact LinearMap.congr_fun (ha phi) x
  · intro ha phi
    ext x
    change phi (a • x) = 0
    rw [ha,map_zero]
section Quotient
variable {B : Type*} [CommRing B] [Algebra K B]
theorem positiveDual_quotient_action (pi : A →ₐ[K] B) :
    letI := quotientKernelModule pi
    positiveDualModule (K := K) (A := A) (M := B) = canonicalParentModule pi := rfl
end Quotient
end Gerstenhaber.CanonicalExtension
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
open Gerstenhaber.CanonicalExtension
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
local instance (priority := 50) : Module A (Module.Dual K M) :=
  positiveDualModule (K := K) (A := A) (M := M)
local instance (priority := 50) : IsScalarTower K A (Module.Dual K M) :=
  positiveDual_tower (K := K) (A := A) (M := M)
theorem socle_dual_vanishes_radical (eps : A →ₐ[K] K) (phi : Module.Dual K M)
    (hphi : phi ∈ moduleSocle (M := Module.Dual K M) eps) :
    (moduleRadical (M := M) eps).restrictScalars K ≤ phi.ker := by
  intro x hx
  change phi x=0
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,ha,y,rfl⟩ := hx
    exact LinearMap.congr_fun (hphi a ha) y
  | zero => exact phi.map_zero
  | add x y _ _ hx hy => rw [map_add,hx,hy,add_zero]
  | smul a x _ hx =>
    have h := congrArg (fun psi : Module.Dual K M => psi x)
      (smul_eq_eps_smul_of_mem_socle eps phi hphi a)
    change phi (a • x)=0
    change phi (a • x)=eps a*phi x at h
    rw [h,hx,mul_zero]
def dualTopToSocle (eps : A →ₐ[K] K) :
    Module.Dual K (Top (M := M) eps) →ₗ[K] moduleSocle (M := Module.Dual K M) eps where
  toFun phi := ⟨phi.comp (topProjection eps),by
    intro a ha
    apply LinearMap.ext
    intro x
    change phi (topProjection eps (a • x))=0
    rw [topProjection_smul,ha,zero_smul,map_zero]⟩
  map_add' := by intro phi psi; rfl
  map_smul' := by intro k phi; rfl
@[simp] theorem dualTopToSocle_apply (eps : A →ₐ[K] K)
    (phi : Module.Dual K (Top (M := M) eps)) (x : M) :
    (dualTopToSocle eps phi : Module.Dual K M) x=phi (topProjection eps x) := rfl
theorem dualTopToSocle_bijective (eps : A →ₐ[K] K) :
    Function.Bijective (dualTopToSocle (M := M) eps) := by
  constructor
  · intro phi psi h
    apply LinearMap.ext
    intro q
    obtain ⟨x,rfl⟩ := topProjection_surjective eps q
    exact congrArg (fun f : moduleSocle (M := Module.Dual K M) eps => f.1 x) h
  · intro phi
    let f : (M ⧸ (moduleRadical (M := M) eps).restrictScalars K) →ₗ[K] K :=
      ((moduleRadical eps).restrictScalars K).liftQ phi.1
        (socle_dual_vanishes_radical eps phi.1 phi.2)
    let q : Top (M := M) eps ≃ₗ[K]
        M ⧸ (moduleRadical (M := M) eps).restrictScalars K :=
      (Submodule.Quotient.restrictScalarsEquiv K (moduleRadical eps)).symm
    refine ⟨f.comp q.toLinearMap,?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    rfl
def dualTopEquivSocle (eps : A →ₐ[K] K) :
    Module.Dual K (Top (M := M) eps) ≃ₗ[K] moduleSocle (M := Module.Dual K M) eps :=
  LinearEquiv.ofBijective (dualTopToSocle eps) (dualTopToSocle_bijective eps)
theorem dual_radical_coannihilator (eps : A →ₐ[K] K) :
    ((moduleRadical (M := Module.Dual K M) eps).restrictScalars K).dualCoannihilator =
      (moduleSocle (M := M) eps).restrictScalars K := by
  ext x
  constructor
  · intro hx a ha
    apply (Module.forall_dual_apply_eq_zero_iff K (a • x)).mp
    intro phi
    exact (Submodule.mem_dualCoannihilator _).mp hx _ (smul_mem_moduleRadical eps a ha phi)
  · intro hx
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro phi hphi
    induction hphi using Submodule.span_induction with
    | mem phi hphi =>
      obtain ⟨a,ha,psi,rfl⟩ := hphi
      change psi (a • x)=0
      rw [hx a ha,map_zero]
    | zero => rfl
    | add phi psi _ _ hp hq =>
      change phi x+psi x=0
      rw [hp,hq,add_zero]
    | smul a phi _ hp =>
      change phi (a • x)=0
      rw [smul_eq_eps_smul_of_mem_socle eps x hx a,phi.map_smul,hp,smul_zero]
theorem dual_radical_eq_annihilator_socle [FiniteDimensional K M] (eps : A →ₐ[K] K) :
    (moduleRadical (M := Module.Dual K M) eps).restrictScalars K =
      ((moduleSocle (M := M) eps).restrictScalars K).dualAnnihilator := by
  rw [← dual_radical_coannihilator eps]
  exact Subspace.dualCoannihilator_dualAnnihilator_eq.symm
def topDualEquivSocleDual [FiniteDimensional K M] (eps : A →ₐ[K] K) :
    Top (M := Module.Dual K M) eps ≃ₗ[K] Module.Dual K (moduleSocle (M := M) eps) :=
  (Submodule.Quotient.restrictScalarsEquiv K
    (moduleRadical (M := Module.Dual K M) eps)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (dual_radical_eq_annihilator_socle eps)).trans
      (Subspace.quotAnnihilatorEquiv ((moduleSocle (M := M) eps).restrictScalars K)))
@[simp] theorem topDualEquivSocleDual_mk [FiniteDimensional K M] (eps : A →ₐ[K] K)
    (phi : Module.Dual K M) (x : moduleSocle (M := M) eps) :
    topDualEquivSocleDual eps ((moduleRadical eps).mkQ phi) x=phi x := rfl
theorem dualMap_kernel_finrank [FiniteDimensional K M] (f : Module.End K M) :
    finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker f.dualMap
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,Subspace.dual_finrank_eq] at h2
  omega
theorem positiveDual_first_kernel_finrank [FiniteDimensional K M] (t : A) :
    finrank K (LinearMap.ker (Algebra.lsmul K K (Module.Dual K M) t)) =
      finrank K (LinearMap.ker (Algebra.lsmul K K M t)) :=
  dualMap_kernel_finrank (Algebra.lsmul K K M t)
theorem positiveDual_actionImage_finrank [FiniteDimensional K M] :
    finrank K (actualActionImage (K := K) (A := A) (M := Module.Dual K M)) =
      finrank K (actualActionImage (K := K) (A := A) (M := M)) := by
  rw [actualActionImage_finrank,actualActionImage_finrank,positiveDual_annihilator]
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.SmallHeads
open scoped Pointwise
variable {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M]
def scalarRange (t : S) : Submodule S M :=
  LinearMap.range (t • (LinearMap.id : M →ₗ[S] M))
end Gerstenhaber.FourBlocks.SmallHeads
end
noncomputable section
namespace Gerstenhaber.FourBlocks.HeadBounds
open Module LinearMap
open Gerstenhaber.FourBlocks.MinimalSource
variable {K A M N : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
  [AddCommGroup N] [Module A N] [Module K N] [IsScalarTower K A N]
def tImage (t : A) : Submodule A M :=
  (t • (LinearMap.id : M →ₗ[A] M)).range
abbrev ActualHead (t : A) := M ⧸ tImage (M := M) t
def headProjection (t : A) : M →ₗ[A] ActualHead (M := M) t := (tImage t).mkQ
theorem headProjection_surjective (t : A) :
    Function.Surjective (headProjection (M := M) t) := (tImage t).mkQ_surjective
theorem head_t_zero (t : A) (q : ActualHead (M := M) t) : t • q = 0 := by
  obtain ⟨x,rfl⟩ := headProjection_surjective t q
  exact (Submodule.Quotient.mk_eq_zero (tImage t)).mpr ⟨x,rfl⟩
theorem tImage_restrictScalars (t : A) :
    (tImage (M := M) t).restrictScalars K = (Algebra.lsmul K K M t).range := by
  ext x
  rfl
theorem actualHead_finrank [FiniteDimensional K M] (t : A) :
    finrank K (ActualHead (M := M) t) = finrank K (LinearMap.ker (Algebra.lsmul K K M t)) := by
  calc
    finrank K (ActualHead (M := M) t) =
        finrank K (M ⧸ (tImage t).restrictScalars K) :=
      (Submodule.Quotient.restrictScalarsEquiv K (tImage t)).finrank_eq.symm
    _ = finrank K (LinearMap.ker (Algebra.lsmul K K M t)) := by
      rw [tImage_restrictScalars]
      exact (finrank_ker_eq_quotient_range _).symm
omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem radical_map_le (eps : A →ₐ[K] K) (q : M →ₗ[A] N) :
    (moduleRadical (M := M) eps).map q ≤ moduleRadical (M := N) eps := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,x,rfl⟩
  change q (a • x) ∈ moduleRadical eps
  rw [q.map_smul]
  exact smul_mem_moduleRadical eps a ha (q x)
omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem radical_map_eq_of_surjective (eps : A →ₐ[K] K)
    (q : M →ₗ[A] N) (hq : Function.Surjective q) :
    (moduleRadical (M := M) eps).map q = moduleRadical (M := N) eps := by
  apply le_antisymm (radical_map_le eps q)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,y,rfl⟩
  obtain ⟨x,rfl⟩ := hq y
  exact Submodule.mem_map.mpr ⟨a • x,smul_mem_moduleRadical eps a ha x,q.map_smul a x⟩
omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
def actualTopMap (eps : A →ₐ[K] K) (q : M →ₗ[A] N) :
    Top (M := M) eps →ₗ[A] Top (M := N) eps :=
  (moduleRadical eps).mapQ (moduleRadical eps) q
    (Submodule.map_le_iff_le_comap.mp (radical_map_le eps q))
omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
@[simp] theorem actualTopMap_mk (eps : A →ₐ[K] K) (q : M →ₗ[A] N) (x : M) :
    actualTopMap eps q ((moduleRadical eps).mkQ x) = (moduleRadical eps).mkQ (q x) := rfl
omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem actualTopMap_surjective (eps : A →ₐ[K] K)
    (q : M →ₗ[A] N) (hq : Function.Surjective q) :
    Function.Surjective (actualTopMap eps q) := by
  intro z
  obtain ⟨y,rfl⟩ := (moduleRadical (M := N) eps).mkQ_surjective z
  obtain ⟨x,rfl⟩ := hq y
  exact ⟨(moduleRadical eps).mkQ x,rfl⟩
omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
theorem actualTopMap_injective (eps : A →ₐ[K] K)
    (q : M →ₗ[A] N) (hq : Function.Surjective q)
    (hker : q.ker ≤ moduleRadical (M := M) eps) :
    Function.Injective (actualTopMap eps q) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  obtain ⟨x,rfl⟩ := (moduleRadical (M := M) eps).mkQ_surjective z
  have hx : q x ∈ moduleRadical (M := N) eps :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  rw [← radical_map_eq_of_surjective eps q hq] at hx
  obtain ⟨y,hy,hyx⟩ := Submodule.mem_map.mp hx
  have hxy : x-y ∈ q.ker := by
    rw [LinearMap.mem_ker,map_sub,hyx,sub_self]
  have hrad : x ∈ moduleRadical (M := M) eps := by
    have h := (moduleRadical eps).add_mem (hker hxy) hy
    simpa only [sub_add_cancel] using h
  exact (Submodule.Quotient.mk_eq_zero _).mpr hrad
omit [Module K M] [IsScalarTower K A M] [Module K N] [IsScalarTower K A N] in
def actualTopEquivOfSurjective (eps : A →ₐ[K] K)
    (q : M →ₗ[A] N) (hq : Function.Surjective q)
    (hker : q.ker ≤ moduleRadical (M := M) eps) :
    Top (M := M) eps ≃ₗ[A] Top (M := N) eps :=
  LinearEquiv.ofBijective (actualTopMap eps q)
    ⟨actualTopMap_injective eps q hq hker,actualTopMap_surjective eps q hq⟩
omit [Module K M] [IsScalarTower K A M] in
theorem tImage_le_radical (eps : A →ₐ[K] K) (t : A) (ht : eps t=0) :
    tImage (M := M) t ≤ moduleRadical eps := by
  rintro _ ⟨x,rfl⟩
  exact smul_mem_moduleRadical eps t ht x
def headTopEquiv (eps : A →ₐ[K] K) (t : A) (ht : eps t=0) :
    Top (M := M) eps ≃ₗ[K] Top (M := ActualHead (M := M) t) eps :=
  (actualTopEquivOfSurjective eps (headProjection t) (headProjection_surjective t) (by
    change (tImage t).mkQ.ker ≤ moduleRadical eps
    rw [Submodule.ker_mkQ]
    exact tImage_le_radical eps t ht)).restrictScalars K
end Gerstenhaber.FourBlocks.HeadBounds
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
open Gerstenhaber.CanonicalExtension
open Gerstenhaber.FourBlocks.HeadBounds
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
local instance (priority := 50) : Module A (Module.Dual K M) :=
  positiveDualModule (K := K) (A := A) (M := M)
local instance (priority := 50) : IsScalarTower K A (Module.Dual K M) :=
  positiveDual_tower (K := K) (A := A) (M := M)
local instance (priority := 50) : Module A (Module.Dual K (Module.Dual K M)) :=
  positiveDualModule (K := K) (A := A) (M := Module.Dual K M)
local instance (priority := 50) : IsScalarTower K A (Module.Dual K (Module.Dual K M)) :=
  positiveDual_tower (K := K) (A := A) (M := Module.Dual K M)
def positiveBidualEvaluation : M →ₗ[A] Module.Dual K (Module.Dual K M) where
  toFun := Module.Dual.eval K M
  map_add' := (Module.Dual.eval K M).map_add
  map_smul' := by intro a x; ext phi; rfl
@[simp] theorem positiveBidualEvaluation_apply (x : M) (phi : Module.Dual K M) :
    positiveBidualEvaluation (A := A) x phi=phi x := rfl
def positiveBidualEquiv [FiniteDimensional K M] :
    M ≃ₗ[A] Module.Dual K (Module.Dual K M) :=
  LinearEquiv.ofBijective positiveBidualEvaluation (Module.bijective_dual_eval K M)
def tKernel (t : A) : Submodule A M := (t • (LinearMap.id : M →ₗ[A] M)).ker
@[simp] theorem mem_tKernel (t : A) (x : M) : x ∈ tKernel t ↔ t • x=0 := Iff.rfl
local instance (priority := 50) (t : A) :
    Module A (Module.Dual K (ActualHead (M := Module.Dual K M) t)) :=
  positiveDualModule (K := K) (A := A) (M := ActualHead (M := Module.Dual K M) t)
local instance (priority := 50) (t : A) :
    IsScalarTower K A (Module.Dual K (ActualHead (M := Module.Dual K M) t)) :=
  positiveDual_tower (K := K) (A := A) (M := ActualHead (M := Module.Dual K M) t)
def kernelHeadFunctional (t : A) (x : tKernel (M := M) t) :
    Module.Dual K (ActualHead (M := Module.Dual K M) t) :=
  let f := ((tImage (M := Module.Dual K M) t).restrictScalars K).liftQ
    (Module.Dual.eval K M x.1) (by
      rintro _ ⟨phi,rfl⟩
      change phi (t • x.1)=0
      have hx : t • x.1=0 := x.2
      rw [hx,map_zero])
  f.comp (Submodule.Quotient.restrictScalarsEquiv K (tImage (M := Module.Dual K M) t)).symm.toLinearMap
@[simp] theorem kernelHeadFunctional_mk (t : A) (x : tKernel (M := M) t)
    (phi : Module.Dual K M) :
    kernelHeadFunctional t x (headProjection t phi)=phi x.1 := rfl
def kernelToDualHead (t : A) :
    tKernel (M := M) t →ₗ[A] Module.Dual K (ActualHead (M := Module.Dual K M) t) where
  toFun := kernelHeadFunctional t
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro q
    obtain ⟨phi,rfl⟩ := headProjection_surjective (M := Module.Dual K M) t q
    exact phi.map_add x.1 y.1
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro q
    obtain ⟨phi,rfl⟩ := headProjection_surjective (M := Module.Dual K M) t q
    rfl
theorem kernelToDualHead_bijective [FiniteDimensional K M] (t : A) :
    Function.Bijective (kernelToDualHead (K := K) (M := M) t) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (Module.bijective_dual_eval K M).1
    apply LinearMap.ext
    intro phi
    exact congrArg (fun f => f (headProjection t phi)) hxy
  · intro f
    let g : Module.Dual K (Module.Dual K M) :=
      f.comp ((headProjection (M := Module.Dual K M) t).restrictScalars K)
    let x : M := (Module.evalEquiv K M).symm g
    have hx : t • x=0 := by
      apply (Module.forall_dual_apply_eq_zero_iff K (t • x)).mp
      intro phi
      change (t • phi) x=0
      rw [Module.apply_evalEquiv_symm_apply]
      change f (headProjection t (t • phi))=0
      rw [(headProjection t).map_smul,head_t_zero,map_zero]
    refine ⟨⟨x,hx⟩,?_⟩
    apply LinearMap.ext
    intro q
    obtain ⟨phi,rfl⟩ := headProjection_surjective (M := Module.Dual K M) t q
    change phi ((Module.evalEquiv K M).symm g)=f (headProjection t phi)
    exact Module.apply_evalEquiv_symm_apply K M phi g
def kernelDualHeadEquiv [FiniteDimensional K M] (t : A) :
    tKernel (M := M) t ≃ₗ[A] Module.Dual K (ActualHead (M := Module.Dual K M) t) :=
  LinearEquiv.ofBijective (kernelToDualHead t) (kernelToDualHead_bijective t)
@[simp] theorem kernelDualHeadEquiv_mk [FiniteDimensional K M] (t : A)
    (x : tKernel (M := M) t) (phi : Module.Dual K M) :
    kernelDualHeadEquiv t x (headProjection t phi)=phi x.1 := rfl
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
def cyclicModule (u : M) : Submodule A M := Submodule.span A {u}
def cyclicEvaluation : M →ₗ[K] A →ₗ[K] M :=
  (Algebra.lsmul K K M).toLinearMap.flip
@[simp] theorem cyclicEvaluation_apply (u : M) (a : A) :
    cyclicEvaluation (K := K) (A := A) u a=a • u := rfl
def IsMaximalCyclic (u : M) : Prop :=
  ∀ v : M, finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) v)) ≤
    finrank K (LinearMap.range (cyclicEvaluation (K := K) (A := A) u))
def cyclicSocleInclusion (eps : A →ₐ[K] K) (u : M) :
    moduleSocle (M := cyclicModule (A := A) u) eps →ₗ[K] moduleSocle (M := M) eps where
  toFun v := ⟨v.1.1,fun a ha => congrArg Subtype.val (v.2 a ha)⟩
  map_add' := by intro x y; rfl
  map_smul' := by intro k x; rfl
theorem cyclicSocleInclusion_injective (eps : A →ₐ[K] K) (u : M) :
    Function.Injective (cyclicSocleInclusion (K := K) eps u) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : moduleSocle (M := M) eps => (z : M)) h
def cyclicSocleEquiv (eps : A →ₐ[K] K) (u : M)
    (hsoc : moduleSocle (M := M) eps ≤ cyclicModule (A := A) u) :
    moduleSocle (M := cyclicModule (A := A) u) eps ≃ₗ[K] moduleSocle (M := M) eps :=
  LinearEquiv.ofBijective (cyclicSocleInclusion eps u) ⟨cyclicSocleInclusion_injective eps u,by
    intro v
    exact ⟨⟨⟨v.1,hsoc v.2⟩,fun a ha => Subtype.ext (v.2 a ha)⟩,rfl⟩⟩
theorem cyclic_annihilator_le_augmentation (eps : A →ₐ[K] K) (u : M)
    (hu : topProjection eps u ≠ 0) :
    Module.annihilator A (cyclicModule (A := A) u) ≤ augmentationIdeal eps := by
  intro a ha
  have hau : a • u=0 :=
    (mem_annihilator_submodule_iff (cyclicModule (A := A) u) a).mp ha u
      (Submodule.mem_span_singleton_self u)
  have hz : eps a • topProjection eps u=0 := by
    rw [← topProjection_smul,hau,map_zero]
  exact (smul_eq_zero.mp hz).resolve_right hu
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
variable {K A M : Type*} [Field K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M]
def cyclicGeneratorMap (u : M) : A →ₗ[A] cyclicModule (A := A) u where
  toFun a := ⟨a • u,Submodule.mem_span_singleton.mpr ⟨a,rfl⟩⟩
  map_add' := by intro a b; apply Subtype.ext; exact add_smul a b u
  map_smul' := by intro a b; apply Subtype.ext; exact mul_smul a b u
theorem cyclicGeneratorMap_surjective (u : M) :
    Function.Surjective (cyclicGeneratorMap (A := A) u) := by
  intro x
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp x.2
  exact ⟨a,Subtype.ext ha⟩
theorem cyclicGeneratorMap_kernel (u : M) :
    (cyclicGeneratorMap (A := A) u).ker = Module.annihilator A (cyclicModule (A := A) u) := by
  ext a
  constructor
  · intro ha
    have hau : a • u=0 := congrArg Subtype.val ha
    apply (mem_annihilator_submodule_iff (cyclicModule (A := A) u) a).mpr
    intro x hx
    obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [← mul_smul,mul_comm a b,mul_smul,hau,smul_zero]
  · intro ha
    apply Subtype.ext
    exact (mem_annihilator_submodule_iff (cyclicModule (A := A) u) a).mp ha u
      (Submodule.mem_span_singleton_self u)
abbrev CyclicParent (u : M) := A ⧸ Module.annihilator A (cyclicModule (A := A) u)
def cyclicParentEquiv (u : M) : CyclicParent (A := A) u ≃ₗ[A] cyclicModule (A := A) u :=
  (Submodule.quotEquivOfEq _ _ (cyclicGeneratorMap_kernel (A := A) u).symm).trans
    ((cyclicGeneratorMap (A := A) u).quotKerEquivOfSurjective (cyclicGeneratorMap_surjective u))
@[simp] theorem cyclicParentEquiv_mk (u : M) (a : A) :
    (cyclicParentEquiv (A := A) u
      (Ideal.Quotient.mk (Module.annihilator A (cyclicModule (A := A) u)) a) : M) = a • u := rfl
theorem cyclicParent_smul (u : M) (a : A) (r : CyclicParent (A := A) u) :
    a • r = Ideal.Quotient.mk (Module.annihilator A (cyclicModule (A := A) u)) a*r :=
  Algebra.smul_def a r
def cyclicParentAugmentation (eps : A →ₐ[K] K) (u : M) (hu : topProjection eps u ≠ 0) :
    CyclicParent (A := A) u →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ eps (fun _ ha => cyclic_annihilator_le_augmentation eps u hu ha)
@[simp] theorem cyclicParentAugmentation_mk (eps : A →ₐ[K] K) (u : M)
    (hu : topProjection eps u ≠ 0) (a : A) :
    cyclicParentAugmentation eps u hu
      (Ideal.Quotient.mk (Module.annihilator A (cyclicModule (A := A) u)) a) = eps a := rfl
def cyclicParentSocleMap (eps : A →ₐ[K] K) (u : M) (hu : topProjection eps u ≠ 0) :
    algebraSocle (cyclicParentAugmentation eps u hu) →ₗ[K]
      moduleSocle (M := cyclicModule (A := A) u) eps := by
  let f := (cyclicParentEquiv (A := A) u).restrictScalars K
  let g := f.toLinearMap.comp
    ((algebraSocle (cyclicParentAugmentation eps u hu)).subtype.restrictScalars K)
  refine g.codRestrict ((moduleSocle (M := cyclicModule (A := A) u) eps).restrictScalars K) ?_
  intro r a ha
  change a • cyclicParentEquiv u r.1=0
  rw [← (cyclicParentEquiv u).map_smul]
  have hz : a • r.1=0 := by
    rw [cyclicParent_smul,mul_comm]
    exact r.2 _ (by rw [cyclicParentAugmentation_mk]; exact ha)
  rw [hz,map_zero]
theorem cyclicParentSocleMap_bijective (eps : A →ₐ[K] K) (u : M)
    (hu : topProjection eps u ≠ 0) :
    Function.Bijective (cyclicParentSocleMap eps u hu) := by
  constructor
  · intro r s h
    apply Subtype.ext
    apply (cyclicParentEquiv (A := A) u).injective
    exact congrArg (fun x : moduleSocle (M := cyclicModule (A := A) u) eps => x.1) h
  · intro v
    let r := (cyclicParentEquiv (A := A) u).symm v.1
    have hr : r ∈ algebraSocle (cyclicParentAugmentation eps u hu) := by
      intro s hs
      obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective s
      have ha : eps a=0 := by rwa [cyclicParentAugmentation_mk] at hs
      apply (cyclicParentEquiv (A := A) u).injective
      rw [map_zero,mul_comm,← cyclicParent_smul,(cyclicParentEquiv u).map_smul]
      change a • (cyclicParentEquiv u) ((cyclicParentEquiv u).symm v.1)=0
      rw [LinearEquiv.apply_symm_apply]
      exact v.2 a ha
    refine ⟨⟨r,hr⟩,?_⟩
    apply Subtype.ext
    exact (cyclicParentEquiv (A := A) u).apply_symm_apply v.1
def cyclicParentSocleEquiv (eps : A →ₐ[K] K) (u : M) (hu : topProjection eps u ≠ 0) :
    algebraSocle (cyclicParentAugmentation eps u hu) ≃ₗ[K]
      moduleSocle (M := cyclicModule (A := A) u) eps :=
  LinearEquiv.ofBijective (cyclicParentSocleMap eps u hu) (cyclicParentSocleMap_bijective eps u hu)
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace Gerstenhaber.FourBlocks.MinimalSource
open Module LinearMap
open scoped IsMulCommutative
variable {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
abbrev UnaryAlgebra (f : Module.End K N) := Algebra.adjoin K ({f} : Set (Module.End K N))
instance unaryAlgebra_commRing (f : Module.End K N) : CommRing (UnaryAlgebra f) := inferInstance
instance unaryAlgebra_tower (f : Module.End K N) : IsScalarTower K (UnaryAlgebra f) N :=
  ⟨fun _ _ _ => rfl⟩
def unaryRoot (f : Module.End K N) : UnaryAlgebra f :=
  ⟨f,Algebra.subset_adjoin (Set.mem_singleton _)⟩
section ActualAlgebra
variable {A : Type*} [CommRing A] [Algebra K A] [Module A N] [IsScalarTower K A N]
end ActualAlgebra
end Gerstenhaber.FourBlocks.MinimalSource
end
noncomputable section
namespace DVRMinimal
open Module LinearMap
open Gerstenhaber.FourBlocks.HeadBounds Gerstenhaber.FourBlocks.MinimalSource
open Gerstenhaber.CanonicalExtension
variable {k A W : Type*} [Field k] [CommRing A] [Algebra k A]
  [AddCommGroup W] [Module A W] [Module k W] [IsScalarTower k A W]
def Cyc (A W : Type*) [CommRing A] [AddCommGroup W] [Module A W] : Prop :=
  ∃ w : W, ∀ x : W, ∃ a : A, a • w = x
theorem liftCyclic [Module.Finite k W] (t : A) (ht : IsNilpotent t)
    (h : Cyc A (ActualHead (M := W) t)) : Cyc A W := by
  obtain ⟨q,hq⟩ := h
  obtain ⟨w,rfl⟩ := headProjection_surjective t q
  let P : Submodule A W := Submodule.span A {w}
  let J : Ideal A := Ideal.span {t}
  letI : Module.Finite A W := Module.Finite.of_restrictScalars_finite k _ _
  have hJ : J ≤ Ring.jacobson A := by
    apply le_trans _ (nilradical_le_jacobson _)
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (mem_nilradical.mpr ht))
  have hh : (⊤ : Submodule A W) ≤ P ⊔ J • ⊤ := by
    intro x _
    obtain ⟨a,ha⟩ := hq (headProjection t x)
    have hz : x-a•w ∈ tImage t := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change headProjection t (x-a•w)=0
      rw [map_sub,map_smul,ha,sub_self]
    obtain ⟨y,hy⟩ := hz
    apply Submodule.mem_sup.mpr
    refine ⟨a•w,P.smul_mem _ (Submodule.mem_span_singleton_self w),t•y,?_,?_⟩
    · exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton t)) Submodule.mem_top
    · change t • y=x-a•w at hy
      rw [hy]; abel
  have hP := Submodule.le_of_le_smul_of_le_jacobson Module.Finite.fg_top hJ hh
  exact ⟨w, fun x => Submodule.mem_span_singleton.mp (hP (Submodule.mem_top (x:=x)))⟩
theorem cyc_of_dim_one [Module.Finite k W] (h : finrank k W=1) : Cyc A W := by
  obtain ⟨w,hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (show 0<finrank k W by omega)
  have hh := (finrank_eq_one_iff_of_nonzero w hw).mp h
  refine ⟨w,fun x => ?_⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (show x ∈ Submodule.span k {w} by rw [hh]; trivial)
  exact ⟨algebraMap k A c, by simpa only [IsScalarTower.algebraMap_smul] using hc⟩
theorem cyclic_payment [Module.Finite k W] (h : Cyc A W) :
    finrank k (actualActionImage (K:=k) (A:=A) (M:=W)) ≤ finrank k W := by
  obtain ⟨w,hw⟩ := h
  let E := actualActionImage (K:=k) (A:=A) (M:=W)
  let f : E →ₗ[k] W := (LinearMap.applyₗ w).comp E.val.toLinearMap
  apply LinearMap.finrank_le_finrank_of_injective (f:=f)
  rintro ⟨p,⟨a,rfl⟩⟩ ⟨q,⟨b,rfl⟩⟩ hab
  apply Subtype.ext
  ext v
  obtain ⟨c,rfl⟩ := hw v
  change a • w = b • w at hab
  change a • (c • w) = b • (c • w)
  rw [smul_comm a c,hab,smul_comm b c]
theorem regular_head_pay [Module.Finite k W] (t y : A)
    (ht : IsNilpotent t) (hy : IsNilpotent y)
    (h : finrank k (Algebra.lsmul k k (ActualHead (M:=W) t) y).ker = 1) :
    finrank k (actualActionImage (K:=k) (A:=A) (M:=W)) ≤ finrank k W := by
  apply cyclic_payment
  apply liftCyclic (k:=k) t ht
  apply liftCyclic (k:=k) y hy
  apply cyc_of_dim_one (k:=k)
  rw [actualHead_finrank]; exact h
local instance (priority := 50) : Module A (Module.Dual k W) := positiveDualModule
local instance (priority := 50) : IsScalarTower k A (Module.Dual k W) := positiveDual_tower
theorem regular_tail_pay [Module.Finite k W] (t y : A)
    (ht : IsNilpotent t) (hy : IsNilpotent y)
    (h : finrank k (Algebra.lsmul k k (tKernel (M:=W) t) y).ker = 1) :
    finrank k (actualActionImage (K:=k) (A:=A) (M:=W)) ≤ finrank k W := by
  let H := ActualHead (M:=Module.Dual k W) t
  letI : Module A (Module.Dual k H) := positiveDualModule
  letI : IsScalarTower k A (Module.Dual k H) := positiveDual_tower
  letI : FiniteDimensional k (tKernel (M:=W) t) := FiniteDimensional.of_injective ((tKernel (M:=W) t).subtype.restrictScalars k) (tKernel (M:=W) t).injective_subtype
  let e := (kernelDualHeadEquiv (K:=k) (M:=W) t).restrictScalars k
  have same : finrank k (Algebra.lsmul k k (tKernel (M:=W) t) y).ker =
      finrank k (Algebra.lsmul k k (Module.Dual k H) y).ker := by
    apply le_antisymm
    · apply finrank_ker_le_of_injective_intertwining _ _ e.toLinearMap e.injective
      intro x; exact (kernelDualHeadEquiv (K:=k) (M:=W) t).map_smul y x
    · apply finrank_ker_le_of_injective_intertwining _ _ e.symm.toLinearMap e.symm.injective
      intro x; exact (kernelDualHeadEquiv (K:=k) (M:=W) t).symm.map_smul y x
  have hH : finrank k (Algebra.lsmul k k H y).ker=1 := by
    rw [← positiveDual_first_kernel_finrank (K:=k) (M:=H) y,←same,h]
  have hh := regular_head_pay (k:=k) (W:=Module.Dual k W) t y ht hy hH
  rw [positiveDual_actionImage_finrank,Subspace.dual_finrank_eq] at hh
  exact hh
end DVRMinimal
end
noncomputable section
namespace DVRMinimal
open Module LinearMap
open Gerstenhaber.FourBlocks.PrimaryDecomposition Gerstenhaber.FourBlocks.MinimalSource
open Gerstenhaber.FourBlocks.HeadBounds
def SafeEverywhere (r : ℕ) : Prop := ∀ (k : Type u) [Field k] [IsAlgClosed k], SafeAt k r
theorem first_failure_any_field {s : ℕ} (hf : ¬SafeEverywhere.{u} s) :
    ∃ r ≤ s, (¬SafeEverywhere.{u} r) ∧ ∀ j<r, SafeEverywhere.{u} j := by
  classical
  have ex : ∃ r, ¬SafeEverywhere.{u} r := ⟨s,hf⟩
  exact ⟨Nat.find ex,Nat.find_min' ex hf,Nat.find_spec ex,fun j hj => not_not.mp (Nat.find_min ex hj)⟩
theorem ker_pos {k W : Type u} [Field k] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] [Nontrivial W] (y : Module.End k W) (hy : IsNilpotent y) :
    0<finrank k y.ker := by
  obtain ⟨w,hw,hne⟩ := nil_kernel_vector y hy
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨w,hw⟩,fun eq => hne (congrArg Subtype.val eq)⟩
variable {k : Type u} [Field k]
def TwoEnds (X : FiniteNilTriple k) : Prop :=
    let t := sourceRoot X 0
    let y := sourceRoot X 1
    2 ≤ finrank k (Algebra.lsmul k k (ActualHead (M:=X.Carrier) t) y).ker ∧
      2 ≤ finrank k (Algebra.lsmul k k (tKernel (M:=X.Carrier) t) y).ker
theorem nil_failure_two_at_each_end (X : FiniteNilTriple k)
    (hb : finrank k X.Carrier < finrank k (SourceAlgebra X)) : TwoEnds X := by
  let t := sourceRoot X 0
  let y := sourceRoot X 1
  let T := tKernel (M:=X.Carrier) t
  let H := ActualHead (M:=X.Carrier) t
  letI : Nontrivial X.Carrier := sourceCarrier_nontrivial_of_failure X hb
  have ht := sourceRoot_nilpotent X 0
  have hy := sourceRoot_nilpotent X 1
  have hk := ker_pos (X.operator 0) (X.nilpotent 0)
  letI : Nontrivial H := Module.nontrivial_of_finrank_pos (R:=k) (by
    change 0<finrank k (ActualHead (M:=X.Carrier) t); rw [actualHead_finrank]; exact hk)
  letI : FiniteDimensional k T := FiniteDimensional.of_injective
    ((tKernel (M:=X.Carrier) t).subtype.restrictScalars k) (tKernel (M:=X.Carrier) t).injective_subtype
  have ⟨w,hw,wn⟩ := nil_kernel_vector (X.operator 0) (X.nilpotent 0)
  letI : Nontrivial T := nontrivial_of_ne (⟨w,hw⟩ : T) 0 (fun eq => wn (congrArg Subtype.val eq))
  have bpH := ker_pos (Algebra.lsmul k k H y) (hy.map (Algebra.lsmul k k H))
  have bpT := ker_pos (Algebra.lsmul k k T y) (hy.map (Algebra.lsmul k k T))
  have nH : finrank k (Algebra.lsmul k k H y).ker ≠ 1 := by
    intro he; have b := regular_head_pay (k:=k) (W:=X.Carrier) t y ht hy he
    rw [sourceActionImage_eq] at b; exact (not_lt_of_ge b) hb
  have nT : finrank k (Algebra.lsmul k k T y).ker ≠ 1 := by
    intro he; have b := regular_tail_pay (k:=k) (W:=X.Carrier) t y ht hy he
    rw [sourceActionImage_eq] at b; exact (not_lt_of_ge b) hb
  change 2≤finrank k (Algebra.lsmul k k H y).ker ∧ 2≤finrank k (Algebra.lsmul k k T y).ker
  omega
variable [IsAlgClosed k] {W : Type u} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
theorem least_bad_shifted_two_ends (T : Fin 3 → Module.End k W)
    (hc : ∀ i j, Commute (T i) (T j)) (hn : IsNilpotent (T 0))
    (bad : finrank k W < finrank k (Generated T))
    (small : ∀ j < finrank k (T 0).ker, SafeEverywhere.{u} j) :
    ∃ (chi : Fin 3 → k) (_ : chi 0=0) (hnil : ∀ i,IsNilpotent (shifted T chi i)),
      TwoEnds (FiniteNilTriple.of W (shifted T chi) (shifted_commute T chi hc) hnil) := by
  obtain ⟨χ,hχ⟩ := least_bad_single_spectrum T hc hn bad (fun j hj => small j hj k)
  let c := Function.update χ 0 0
  have h0 : c 0=0 := Function.update_self ..
  have hn' (i) : IsNilpotent (shifted T c i) := by
    by_cases h : i=0
    · subst i; simpa only [shifted,h0,zero_smul,sub_zero] using hn
    · simpa only [shifted,c,Function.update_of_ne h] using hχ i
  refine ⟨c,h0,hn',nil_failure_two_at_each_end _ ?_⟩
  change finrank k W < finrank k (Generated (shifted T c))
  rwa [adjoin_shifted]
end DVRMinimal
end
noncomputable section
namespace GKDivisor.Jet
open PowerSeries DivisorG3 Module LinearMap
open Gerstenhaber.FourBlocks.PrimaryDecomposition Gerstenhaber.FourBlocks.MinimalSource
variable {k E : Type u} [Field k] [Field E] [Algebra k E] {r : ℕ} {s : GKGraph.selectCols r}
variable (D : SeriesPole k E r s)
abbrev SeriesPole.carrier := QP (D.T 0)
abbrev SeriesPole.native := nativeTriple (D.T 0) (D.T 1) (D.T 3) (D.T 2) (D.T 4)
  D.relations.y.symm D.relations.z.symm
end GKDivisor.Jet
end
noncomputable section
namespace GKGraph
variable (k : Type u) [Field k] {F : Type u} [Field F] [Algebra k F]
variable (r : ℕ) (φ : ring k r →ₐ[k] F)
def enumParam (s : Finset F) (i : Fin s.card) : F := (s.equivFin.symm i).1
theorem param_field_le (s : Finset F) (c : Fin 2 → F) :
    IntermediateField.adjoin k (s : Set F) ≤ pairField k c (enumParam s) := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  apply IntermediateField.subset_adjoin
  refine ⟨Sum.inr (s.equivFin ⟨x,hx⟩),?_⟩
  simp [enumParam]
theorem center_mem {n : ℕ} (u : Fin n → F) (c : Fin 2 → F) (j : Fin 2) :
    c j ∈ pairField k c u := IntermediateField.subset_adjoin _ _ ⟨Sum.inl j,rfl⟩
theorem entries_unshift (L : IntermediateField k F) (M : Mat F r) (a : F) (ha : a ∈ L)
    (hm : ∀ i j, (M - a • 1) i j ∈ L) : ∀ i j, M i j ∈ L := by
  intro i j
  have h : (a • (1 : Mat F r)) i j ∈ L := by
    by_cases e : i=j
    · subst j; simpa [Matrix.one_apply] using ha
    · simp [e]
  exact (sub_add_cancel (M i j) ((a • (1 : Mat F r)) i j)) ▸ L.add_mem (hm i j) h
theorem centered_parameter_bound (hr : 2 ≤ r) (c : Fin 2 → F) (s t : Finset F)
    (hs : s.card ≤ r*r-2) (ht : t.card ≤ r*r-2)
    (h0 : reducedMatrices k r φ 0 = 0)
    (h1 : ∀ i j, (reducedMatrices k r φ 1 - c 0 • 1) i j ∈ IntermediateField.adjoin k (s : Set F))
    (h2 : ∀ i j, (reducedMatrices k r φ 2 - c 1 • 1) i j ∈ IntermediateField.adjoin k (s : Set F))
    (h3 : ∀ i j, (reducedMatrices k r φ 3 - c 0 • 1) i j ∈ IntermediateField.adjoin k (t : Set F))
    (h4 : ∀ i j, (reducedMatrices k r φ 4 - c 1 • 1) i j ∈ IntermediateField.adjoin k (t : Set F)) :
    Algebra.trdeg k (residueCoordinates k r φ) ≤ (3*r*r-2 : ℕ) := by
  have h := joint_coordinate_budget k r φ c (enumParam s) (enumParam t) h0
    (entries_unshift k r _ _ _ (center_mem k (enumParam s) c 0)
      (fun i j => param_field_le k s c (h1 i j)))
    (entries_unshift k r _ _ _ (center_mem k (enumParam s) c 1)
      (fun i j => param_field_le k s c (h2 i j)))
    (entries_unshift k r _ _ _ (center_mem k (enumParam t) c 0)
      (fun i j => param_field_le k t c (h3 i j)))
    (entries_unshift k r _ _ _ (center_mem k (enumParam t) c 1)
      (fun i j => param_field_le k t c (h4 i j)))
  apply h.trans
  exact_mod_cast (show 2+s.card+t.card+r*r ≤ 3*r*r-2 by
    have hrr : 2 ≤ r*r := (by omega : 2 ≤ 2*2).trans (Nat.mul_le_mul hr hr)
    rw [Nat.mul_assoc]; omega)
theorem coords_map {F' : Type u} [Field F'] [Algebra k F'] (ι : F →ₐ[k] F') :
    (residueCoordinates k r φ).map ι = residueCoordinates k r (ι.comp φ) := by
  unfold residueCoordinates
  rw [IntermediateField.adjoin_map, ←Set.range_comp]; rfl
theorem coords_trdeg_map {F' : Type u} [Field F'] [Algebra k F'] (ι : F →ₐ[k] F') :
    Algebra.trdeg k (residueCoordinates k r φ) =
      Algebra.trdeg k (residueCoordinates k r (ι.comp φ)) := by
  rw [← coords_map]
  exact ((residueCoordinates k r φ).equivMap ι).trdeg_eq
end GKGraph
end
noncomputable section
namespace GKDivisor.Jet
open PowerSeries Module Gerstenhaber.FourBlocks.PrimaryDecomposition Gerstenhaber.FourBlocks.MinimalSource
local instance BadPole.instCr5 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom5 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr5 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg5 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
variable {k : Type u} [Field k] [PerfectField k] {r : ℕ} {s : GKGraph.selectCols r}
abbrev ClosedF (B : BadPole k r (GKGraph.universalMinor k r s)) :=
  AlgebraicClosure (IsLocalRing.ResidueField B.V)
def graphAtClosure (B : BadPole k r (GKGraph.universalMinor k r s)) : GKGraph.ring k r →ₐ[k] ClosedF B :=
  (IsScalarTower.toAlgHom k (IsLocalRing.ResidueField B.V) (ClosedF B)).comp B.residualMap
omit [PerfectField k] in
theorem closureField_count (B : BadPole k r (GKGraph.universalMinor k r s)) :
    Algebra.trdeg k (GKGraph.residueCoordinates k r (graphAtClosure B)) + 1 = (3*r*r : ℕ) := by
  rw [graphAtClosure,←GKGraph.coords_trdeg_map]
  exact B.field_count
end GKDivisor.Jet
end
noncomputable section
namespace DivisorG3
open Module LinearMap Submodule Matrix
variable {R W : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup W] [Module R W]
theorem square_cover {r : ℕ} (π : (Fin r → R) →ₗ[R] W) (on : Function.Surjective π)
    (a : R) (ha : a≠0) (ann : ∀ w : W, a • w=0) :
    ∃ P : Matrix (Fin r) (Fin r) R, P.det≠0 ∧ P.mulVecLin.range=π.ker ∧
        ∃ e : QP P ≃ₗ[R] W, ∀ v, e (P.mulVecLin.range.mkQ v)=π v := by
  let F := Fin r → R
  let A := times a F
  have hi : Function.Injective A := by
    intro x y h
    funext i
    exact mul_left_cancel₀ ha (congrFun h i)
  have incl : A.range ≤ π.ker := by
    rintro _ ⟨v,rfl⟩
    change π (a • v)=0
    rw [map_smul,ann]
  have dim : finrank R (LinearMap.ker π)=r := by
    have l := Submodule.finrank_mono incl
    rw [LinearMap.finrank_range_of_inj hi] at l
    have h := Submodule.finrank_le π.ker
    simpa [F] using le_antisymm h l
  let basis := Module.finBasisOfFinrankEq R (LinearMap.ker π) dim
  let f := π.ker.subtype.comp basis.equivFun.symm.toLinearMap
  let P := LinearMap.toMatrix' f
  have hf : P.mulVecLin=f := LinearMap.ext fun v => f.toMatrix'_mulVec v
  have his : Function.Injective P.mulVec := by
    change Function.Injective P.mulVecLin
    rw [hf]; exact π.ker.subtype_injective.comp basis.equivFun.symm.injective
  have ran : P.mulVecLin.range=π.ker := by
    rw [hf,show f=π.ker.subtype.comp basis.equivFun.symm.toLinearMap from rfl,LinearMap.range_comp,
      LinearEquiv.range,Submodule.map_top,Submodule.range_subtype]
  exact ⟨P,Matrix.nonsingular_iff_det_ne_zero.mp (.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp his)),
    ran,(Submodule.quotEquivOfEq _ _ ran) ≪≫ₗ π.quotKerEquivOfSurjective on,fun _ => rfl⟩
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module LinearMap Submodule Matrix
open scoped Matrix
variable {R W ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup W] [Module R W]
private theorem factor_matrix (P B : Matrix ι ι R) (h : ∀ v, B.mulVecLin v ∈ P.mulVecLin.range) :
    ∃ D, B=P*D := by
  let f := B.mulVecLin.codRestrict P.mulVecLin.range h
  obtain ⟨d,hd⟩ := Module.projective_lifting_property P.mulVecLin.rangeRestrict f P.mulVecLin.surjective_rangeRestrict
  refine ⟨LinearMap.toMatrix' d,Matrix.toLin'.injective ?_⟩
  rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro v
  exact (congrArg Subtype.val (LinearMap.congr_fun hd v)).symm
theorem graph_lifts (π : (ι → R) →ₗ[R] W) (on : Function.Surjective π)
    (P : Matrix ι ι R) (ran : P.mulVecLin.range=π.ker) (y z : End R W) (hc : Commute y z) :
    ∃ Y Y' Z Z' C : Matrix ι ι R, Y*P=P*Y' ∧ Z*P=P*Z' ∧ Y*Z-Z*Y=P*C ∧
      (∀ v, π (Y *ᵥ v)=y (π v)) ∧ (∀ v, π (Z *ᵥ v)=z (π v)) := by
  obtain ⟨f,hf⟩ := Module.projective_lifting_property π (y.comp π) on
  obtain ⟨g,hg⟩ := Module.projective_lifting_property π (z.comp π) on
  let Y := LinearMap.toMatrix' f
  let Z := LinearMap.toMatrix' g
  have hy (v) : π (Y *ᵥ v)=y (π v) := by rw [LinearMap.toMatrix'_mulVec]; exact LinearMap.congr_fun hf v
  have hz (v) : π (Z *ᵥ v)=z (π v) := by rw [LinearMap.toMatrix'_mulVec]; exact LinearMap.congr_fun hg v
  have nul (v) : π (P *ᵥ v)=0 := (show P.mulVecLin v ∈ π.ker from ran ▸ ⟨v,rfl⟩)
  obtain ⟨Y',sy⟩ := factor_matrix P (Y*P) fun v => by
    rw [ran]; change π ((Y*P) *ᵥ v)=0; rw [←mulVec_mulVec,hy,nul,map_zero]
  obtain ⟨Z',sz⟩ := factor_matrix P (Z*P) fun v => by
    rw [ran]; change π ((Z*P) *ᵥ v)=0; rw [←mulVec_mulVec,hz,nul,map_zero]
  obtain ⟨C,sc⟩ := factor_matrix P (Y*Z-Z*Y) fun v => by
    rw [ran]; change π ((Y*Z-Z*Y) *ᵥ v)=0
    rw [sub_mulVec,←mulVec_mulVec,←mulVec_mulVec,map_sub,hy,hz,hz,hy,sub_eq_zero]
    exact LinearMap.congr_fun hc.eq _
  exact ⟨Y,Y',Z,Z',C,sy,sz,sc,hy,hz⟩
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module LinearMap Matrix
open scoped Matrix
variable {V ι W : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module V W]
omit [IsDomain V] [IsDiscreteValuationRing V] [DecidableEq ι] in
theorem conjugate_length (P Y Y' Z Z' : Matrix ι ι V) (sy : Y*P=P*Y') (sz : Z*P=P*Z')
    (e : QP P ≃ₗ[V] W) (y z : End V W)
    (hy : ∀ v, e (P.mulVecLin.range.mkQ (Y *ᵥ v))= y (e (P.mulVecLin.range.mkQ v)))
    (hz : ∀ v, e (P.mulVecLin.range.mkQ (Z *ᵥ v))= z (e (P.mulVecLin.range.mkQ v))) :
    length V (actor P Y Y' Z Z' sy sz) = length V (Algebra.adjoin V ({y,z}:Set _)) := by
  let g := e.conjAlgEquiv V
  have trans (B B' : Matrix ι ι V) (s : B*P=P*B') (b : End V W)
      (hb : ∀ v, e (P.mulVecLin.range.mkQ (B *ᵥ v))=b (e (P.mulVecLin.range.mkQ v))) :
      g (liftEnd P B B' s)=b := by
    apply LinearMap.ext
    intro w
    obtain ⟨u,rfl⟩ := e.surjective w
    obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective u
    change e (liftEnd P B B' s (e.symm (e _))) = _
    rw [e.symm_apply_apply,lift_apply,hb]
  let A := actor P Y Y' Z Z' sy sz
  have hm : A.map g.toAlgHom = Algebra.adjoin V ({y,z}:Set _) := by
    rw [show A=Algebra.adjoin V ({liftEnd P Y Y' sy,liftEnd P Z Z' sz}:Set _) from rfl,
      AlgHom.map_adjoin,Set.image_insert_eq,Set.image_singleton]
    rw [show g.toAlgHom (liftEnd P Y Y' sy)=y from trans _ _ sy y hy,
      show g.toAlgHom (liftEnd P Z Z' sz)=z from trans _ _ sz z hz]
  change length V A=_
  rw [←hm]
  exact LinearEquiv.length_eq (R:=V) (Subalgebra.equivMapOfInjective A g.toAlgHom g.injective).toLinearEquiv
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module Submodule IsLocalRing PowerSeries
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
variable [Module (O k) W] [IsScalarTower k (O k) W]
theorem minimal_cover (T : End k W) (hx : ∀ w : W, (X : O k) • w=T w) :
    ∃ π : (Fin (finrank k (LinearMap.ker T)) → O k) →ₗ[O k] W, Function.Surjective π := by
  let N : Submodule (O k) W := maximalIdeal (O k) • ⊤
  have hr : N.restrictScalars k = T.range := by
    ext w
    simp only [N,PowerSeries.maximalIdeal_eq_span_X,Submodule.ideal_span_singleton_smul]
    change (∃ v ∈ (⊤ : Submodule (O k) W), (X : O k) • v=w) ↔ ∃ v, T v=w
    simp [hx]
  have dim : finrank k (W ⧸ N)=finrank k (LinearMap.ker T) := by
    rw [←(Submodule.Quotient.restrictScalarsEquiv k N).finrank_eq, hr]
    have h := T.finrank_range_add_finrank_ker
    have e := T.range.finrank_quotient_add_finrank
    omega
  let β := Module.finBasisOfFinrankEq k (W ⧸ N) dim
  choose b hb using fun i => N.mkQ_surjective (β i)
  have eqb : N.mkQ ∘ b = β := funext hb
  let _ : Module.Finite (O k) W := Module.Finite.of_restrictScalars_finite k _ _
  have spanb : span (O k) (Set.range b)=⊤ := by
    symm
    apply Submodule.eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson (I:=maximalIdeal (O k))
      Module.Finite.fg_top (ringJacobson_eq_maximalIdeal (O k)).ge
    change (⊤ : Submodule (O k) W).map N.mkQ = _
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr N.mkQ_surjective,Submodule.map_span,←Set.range_comp,eqb]
    symm; apply top_unique
    intro v _
    exact (Submodule.span_le_restrictScalars k (O k) (Set.range β)) (β.span_eq ▸ Submodule.mem_top)
  exact ⟨Fintype.linearCombination (O k) b,LinearMap.range_eq_top.mp ((Fintype.range_linearCombination _ _).trans spanb)⟩
end DivisorG3
end
noncomputable section
namespace DivisorG3
open Module LinearMap PowerSeries Matrix IsDiscreteValuationRing
open scoped Matrix
variable {k W : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
theorem original_graph (T Y Z : End k W) (ht : IsNilpotent T) (hY : Commute Y T)
    (hZ : Commute Z T) (hYZ : Commute Y Z) :
    let ι := Fin (finrank k T.ker)
    ∃ P U U' V V' C : Matrix ι ι (O k), ∃ _hp : P.det≠0, ∃ su : U*P=P*U', ∃ sv : V*P=P*V',
      U*V-V*U=P*C ∧ length (O k) (QP P) = finrank k W ∧
      length (O k) (actor P U U' V V' su sv)=finrank k (triple T Y Z) ∧
      (∃ E : QP P ≃ₗ[k] W, (∀ w, E ((X : O k) • w)=T (E w)) ∧
        (∀ w, E (liftEnd P U U' su w)=Y (E w)) ∧
        (∀ w, E (liftEnd P V V' sv w)=Z (E w))) ∧
      (finrank k W < finrank k (triple T Y Z) →
        ∃ j, addVal (O k) ((wordLattice P U V).submatrix _root_.id j).det <
          addVal (O k) (P.det^(Fintype.card ι-1))) := by
  obtain ⟨ρ,modW,tower,hX,hr,hρ,⟨a,ha,ann⟩,lift⟩ := original_action T ht
  let _ : Module (O k) W := modW
  let _ : IsScalarTower k (O k) W := tower
  obtain ⟨y,hy⟩ := lift Y hY
  obtain ⟨z,hz⟩ := lift Z hZ
  have comm : Commute y z := by
    apply LinearMap.ext; intro w
    exact LinearMap.congr_fun (show Commute (y.restrictScalars k) (z.restrictScalars k) from hy ▸ hz ▸ hYZ).eq w
  obtain ⟨π,on⟩ := minimal_cover T fun w => (hρ X w).trans (LinearMap.congr_fun hX w)
  obtain ⟨P,hp,ran,e,eq⟩ := square_cover π on a ha ann
  obtain ⟨U,U',V,V',C,su,sv,sc,hu,hv⟩ := graph_lifts π on P ran y z comm
  have nw : length (O k) (QP P)=finrank k W := e.length_eq.trans (actual_length k W)
  have nb : length (O k) (actor P U U' V V' su sv)=finrank k (triple T Y Z) := by
    rw [conjugate_length _ _ _ _ _ su sv e y z (fun w => by rw [eq,eq,hu]) (fun w => by rw [eq,eq,hv])]
    have he := origin_actor_length ρ T hX hr hρ y z
    change length (O k) (pair y z) = _
    convert he using 1; subst_vars; rfl
  refine ⟨P,U,U',V,V',C,hp,su,sv,sc,nw,nb,⟨e.restrictScalars k,?_,?_,?_⟩,?_⟩
  · intro w
    change e ((X : O k) • w)=T (e w)
    rw [map_smul,hρ,hX]
  · intro w
    obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
    change e (P.mulVecLin.range.mkQ (U *ᵥ v))=Y (e (P.mulVecLin.range.mkQ v))
    rw [eq,eq,hu]; exact LinearMap.congr_fun hy _
  · intro w
    obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
    change e (P.mulVecLin.range.mkQ (V *ᵥ v))=Z (e (P.mulVecLin.range.mkQ v))
    rw [eq,eq,hv]; exact LinearMap.congr_fun hz _
  intro bad
  have pos : 0 < finrank k T.ker := by
    by_contra! h
    let _ : IsEmpty (Fin (finrank k T.ker)) := ⟨fun i => by have := i.isLt; omega⟩
    let _ : Subsingleton W := on.subsingleton
    have hz0 : finrank k (triple T Y Z) = 0 := Module.finrank_zero_of_subsingleton
    omega
  apply (bad_iff_minor _ _ _ _ _ _ hp (by simpa using pos) su sv sc).mp
  rw [nw,nb]
  exact_mod_cast bad
end DivisorG3
end
namespace DVRMinimal
open Module Gerstenhaber.FourBlocks.PrimaryDecomposition
structure BadAt (r : ℕ) where
  k : Type u
  [field : Field k]
  [closed : IsAlgClosed k]
  W : Type u
  [group : AddCommGroup W]
  [module_ : Module k W]
  [finite : FiniteDimensional k W]
  T : Fin 3 → Module.End k W
  hc : ∀ i j, Commute (T i) (T j)
  hn : IsNilpotent (T 0)
  width : finrank k (T 0).ker=r
  bad : finrank k W<finrank k (Generated T)
instance BadAt.instField {r : ℕ} (X : BadAt.{u} r) : Field X.k := X.field
instance BadAt.instClosed {r : ℕ} (X : BadAt.{u} r) : IsAlgClosed X.k := X.closed
instance BadAt.instGroup {r : ℕ} (X : BadAt.{u} r) : AddCommGroup X.W := X.group
instance BadAt.instModule {r : ℕ} (X : BadAt.{u} r) : Module X.k X.W := X.module_
instance BadAt.instFinite {r : ℕ} (X : BadAt.{u} r) : FiniteDimensional X.k X.W := X.finite
theorem badAt_iff (r : ℕ) : Nonempty (BadAt.{u} r) ↔ ¬SafeEverywhere.{u} r := by
  constructor
  · rintro ⟨B⟩ safe
    exact (not_lt_of_ge (safe B.k B.W B.T B.hc B.hn B.width)) B.bad
  · classical
    intro h
    by_contra hn
    apply h
    intro k _ _ W _ _ _ T hc ht hr
    apply le_of_not_gt
    intro hb
    exact hn ⟨{k:=k,W:=W,T:=T,hc:=hc,hn:=ht,width:=hr,bad:=hb}⟩
theorem arbitrary_matrix_to_least (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j,Commute (A i) (A j))
    (hb : n<finrank k (Algebra.adjoin k (Set.range A))) :
    ∃ r ≤ n, Nonempty (BadAt.{u} r) ∧ ∀ j<r,SafeEverywhere.{u} j := by
  classical
  have hex : ∃ j ≤ n, ¬ SafeEverywhere.{u} j := by
    by_contra! h
    have pay := matrix_triple_bound_of_nilpotent_bound (K:=k) n (by
      intro W _ _ _ T ht hn hw
      exact h _ hw k W T ht (hn 0) rfl) n A hc (fun a => by
        have hh := (Matrix.toLin' (A 0-a • 1)).ker.finrank_le
        simpa only [Module.finrank_pi,Fintype.card_fin] using hh)
    exact (not_lt_of_ge pay) hb
  obtain ⟨j,hj,hbad⟩ := hex
  obtain ⟨r,hr,fail,hmin⟩ := first_failure_any_field hbad
  exact ⟨r,hr.trans hj,(badAt_iff r).mpr fail,hmin⟩
open Gerstenhaber.FourBlocks.HeadBounds Gerstenhaber.FourBlocks.MinimalSource
theorem twoEnds_width {k : Type u} [Field k] (A : FiniteNilTriple k) (hh : TwoEnds A) :
    2 ≤ finrank k (A.operator 0).ker := by
  let t := sourceRoot A 0
  let y := sourceRoot A 1
  let H := ActualHead (M:=A.Carrier) t
  have rank := (Algebra.lsmul k k H y).ker.finrank_le
  have h := hh.1.trans rank
  change 2≤finrank k (ActualHead (M:=A.Carrier) t) at h
  rw [actualHead_finrank] at h
  exact h
theorem minimal_width_at_least_two {r : ℕ} (B : BadAt.{u} r)
    (small : ∀ j<r,SafeEverywhere.{u} j) : 2 ≤ r := by
  have sm : ∀j<finrank B.k (B.T 0).ker,SafeEverywhere.{u} j := by rw [B.width];exact small
  obtain ⟨chi,h0,hn,hh⟩ := least_bad_shifted_two_ends B.T B.hc B.hn B.bad sm
  have h := twoEnds_width _ hh
  change 2≤finrank B.k (shifted B.T chi 0).ker at h
  have hz : shifted B.T chi 0 = B.T 0 := by
    change B.T 0 - chi 0 • 1 = B.T 0
    rw [h0,zero_smul,sub_zero]
  rw [hz,B.width] at h; exact h
theorem arbitrary_matrix_to_least_positive (k : Type u) [Field k] [IsAlgClosed k]
    (n : ℕ) (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j,Commute (A i) (A j))
    (hb : n<finrank k (Algebra.adjoin k (Set.range A))) :
    ∃ r, 2≤r ∧ r≤n ∧ Nonempty (BadAt.{u} r) ∧ ∀ j<r,SafeEverywhere.{u} j := by
  obtain ⟨r,rn,⟨B⟩,small⟩ := arbitrary_matrix_to_least k n A hc hb
  exact ⟨r,minimal_width_at_least_two B small,rn,⟨B⟩,small⟩
end DVRMinimal
noncomputable section
namespace G3Assembly
open Module LinearMap DivisorG3 GKDivisor GKDivisor.Jet GKGraph IsDiscreteValuationRing
open Gerstenhaber.FourBlocks.PrimaryDecomposition DVRMinimal
local instance BadPole.instCr6 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom6 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr6 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg6 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
structure RealWitness (k : Type u) [Field k] [IsAlgClosed k] (r : ℕ) where
  seed : Fin 6 → Mat (O k) r
  rel : Relations r seed
  det_ne : (seed 0).det ≠ 0
  s : selectCols r
  low : addVal (O k) (fullMinor r (seed 0) (seed 1) (seed 2) s) < addVal (O k) ((seed 0).det^(r-1))
  pole : BadPole k r (universalMinor k r s)
  arc : SeriesPole k (ClosedF pole) r s
  same_entries : constEntries arc.T = graphAtClosure pole ∘ gcoord k r
  count : Algebra.trdeg k (residueCoordinates k r (graphAtClosure pole)) + 1 = (3*r*r : ℕ)
theorem present_bad {k W : Type u} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : Fin 3 → End k W) (hc : ∀ i j, Commute (T i) (T j)) (nil : IsNilpotent (T 0))
    (bad : finrank k W < finrank k (Generated T)) :
    let r := finrank k (T 0).ker
    ∃ G : Fin 6 → Mat (O k) r, ∃ rel : Relations r G, (G 0).det ≠ 0 ∧ BadDatum G rel := by
  obtain ⟨P,U,U',V,V',C,hp,su,sv,sc,nw,nb,_,_⟩ :=
    original_graph (T 0) (T 1) (T 2) nil (hc 1 0) (hc 2 0) (hc 1 2)
  let G := ![P,U,V,U',V',C]
  have rel : Relations _ G := ⟨su.symm,sv.symm,sc.symm⟩
  refine ⟨G,rel,hp,?_⟩
  change length (O k) (QP P) < length (O k) (actor P U U' V V' su sv)
  rw [nw,nb]
  change finrank k W < finrank k (Algebra.adjoin k (Set.range T)) at bad
  rw [family_adjoin] at bad
  exact_mod_cast bad
theorem real_pole_at_minimum {r : ℕ} (A : BadAt.{u} r) (hr : 0<r) : Nonempty (RealWitness A.k r) := by
  have h := present_bad A.T A.hc A.hn A.bad
  dsimp only at h
  rw [A.width] at h
  obtain ⟨G,rel,hp,hb⟩ := h
  obtain ⟨s,low⟩ := (badDatum_iff_strict G rel hp hr).mp hb
  obtain ⟨B⟩ := strict_pole_of_real_minor A.k r G hp rel s low
  obtain ⟨S,hs⟩ := pole_to_algebraic_closure B
  exact ⟨⟨G,rel,hp,s,low,B,S,hs,closureField_count B⟩⟩
theorem original_matrix_pole (k : Type u) [Field k] [IsAlgClosed k] {n : ℕ}
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j))
    (bad : n<finrank k (Algebra.adjoin k (Set.range A))) :
    ∃ r, 2≤r ∧ r≤n ∧ (∀j<r,SafeEverywhere.{u} j) ∧
      ∃ B : BadAt.{u} r, Nonempty (RealWitness B.k r) := by
  obtain ⟨r,hr,rn,⟨B⟩,small⟩ := arbitrary_matrix_to_least_positive k n A hc bad
  exact ⟨r,hr,rn,small,B,real_pole_at_minimum B (by omega)⟩
end G3Assembly
end
noncomputable section
namespace GKEnds
open DivisorG3 Module LinearMap Submodule PowerSeries
open Gerstenhaber.FourBlocks.MinimalSource
open scoped Matrix
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev xop (P : sq k ι) : End k (QP P) := (times (X : O k) (QP P)).restrictScalars k
abbrev HH (P : sq k ι) := QP P ⧸ (xop P).range
def qHead (P : sq k ι) : Row k ι →ₗ[k] HH P :=
  (xop P).range.mkQ.comp (P.mulVecLin.range.mkQ.restrictScalars k)
def constVec (k ι : Type*) [Field k] : (ι → k) →ₗ[k] Row k ι where
  toFun v i := C (v i)
  map_add' v w := by ext i : 1; exact map_add C _ _
  map_smul' s v := by ext i : 1; change C (s*v i)=s • C (v i); rw [PowerSeries.smul_eq_C_mul,map_mul]
def headFrame (P : sq k ι) : (ι → k) →ₗ[k] HH P := (qHead P).comp (constVec k ι)
omit [DecidableEq ι] in
theorem frame_eq (P : sq k ι) (v : Row k ι) :
    headFrame P (reduceVec k ι v) = qHead P v := by
  have hz : constVec k ι (reduceVec k ι v) - v ∈ (reduceVec k ι).ker := by
    apply LinearMap.mem_ker.mpr
    rw [map_sub,sub_eq_zero]
    exact funext fun i => constantCoeff_C _
  rw [reduceVec_ker] at hz
  obtain ⟨z,ez⟩ := hz
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨P.mulVecLin.range.mkQ z,?_⟩
  change (X : O k) • P.mulVecLin.range.mkQ z =
    P.mulVecLin.range.mkQ (constVec k ι (reduceVec k ι v))-P.mulVecLin.range.mkQ v
  rw [←map_smul,←map_sub]
  exact congrArg P.mulVecLin.range.mkQ ez
omit [DecidableEq ι] in
theorem frame_surj (P : sq k ι) : Function.Surjective (headFrame P) := by
  intro x
  obtain ⟨w,rfl⟩ := (xop P).range.mkQ_surjective x
  obtain ⟨v,rfl⟩ := P.mulVecLin.range.mkQ_surjective w
  exact ⟨_,frame_eq P v⟩
omit [DecidableEq ι] in
theorem width_le (P : sq k ι) [FiniteDimensional k (QP P)] :
    finrank k (xop P).ker ≤ Fintype.card ι := by
  rw [finrank_ker_eq_quotient_range]
  simpa using (LinearMap.finrank_le_finrank_of_surjective (frame_surj P))
omit [DecidableEq ι] in
theorem frame_inj_of_eq (P : sq k ι) [FiniteDimensional k (QP P)]
    (h : finrank k (xop P).ker = Fintype.card ι) : Function.Injective (headFrame P) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [Module.finrank_pi,←h,finrank_ker_eq_quotient_range])).mpr (frame_surj P)
theorem constant_P_zero (P : sq k ι) [FiniteDimensional k (QP P)]
    (h : finrank k (xop P).ker = Fintype.card ι) : constantCoeff.mapMatrix P=0 := by
  have inj := frame_inj_of_eq P h
  ext i j
  have hz : headFrame P (reduceVec k ι (P.col j))=0 := by
    rw [frame_eq]; change (xop P).range.mkQ (P.mulVecLin.range.mkQ (P.col j))=0
    have mem : P.col j ∈ P.mulVecLin.range := ⟨Pi.single j 1, by simp⟩
    have hh : P.mulVecLin.range.mkQ (P.col j)=0 := (Submodule.Quotient.mk_eq_zero _).mpr mem
    rw [hh,map_zero]
  exact congrFun (inj (hz.trans (map_zero _).symm)) i
end GKEnds
end
noncomputable section
namespace GKEnds
open Module LinearMap Submodule PowerSeries DivisorG3
open Gerstenhaber.FourBlocks.HeadBounds Gerstenhaber.FourBlocks.MinimalSource
open scoped Matrix
variable {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι]
abbrev redM (Y : sq k ι) := constantCoeff.mapMatrix Y
theorem reduce_mv (Y : sq k ι) (v : Row k ι) :
    (redM Y).mulVecLin (reduceVec k ι v) = reduceVec k ι (Y.mulVecLin v) := by
  ext i
  change (∑ j,constantCoeff (Y i j) * constantCoeff (v j)) = constantCoeff (∑ j,Y i j*v j)
  rw [map_sum]; simp only [map_mul]
theorem reduce_shift (Y : sq k ι) (a : k) (v : Row k ι) :
    (redM Y-a • 1).mulVecLin (reduceVec k ι v) =
      reduceVec k ι (Y.mulVecLin v) - a • reduceVec k ι v := by
  change (redM Y-a • 1) *ᵥ (reduceVec k ι v) = _
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
  exact congrArg (· - a • reduceVec k ι v) (reduce_mv Y v)
section Source
variable {A : Type*} [CommRing A] [Algebra k A] (P : sq k ι)
variable [Module A (QP P)] [IsScalarTower k A (QP P)]
variable (t : A) (xt : ∀ w : QP P, t • w = (X : O k) • w)
def toSourceHead : HH P ≃ₗ[k] ActualHead (M:=QP P) t :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [tImage_restrictScalars]
    exact congrArg LinearMap.range (LinearMap.ext (fun w => (xt w).symm)))) ≪≫ₗ
    Submodule.Quotient.restrictScalarsEquiv k _
def sourceHead [FiniteDimensional k (QP P)] (hw : finrank k (xop P).ker=Fintype.card ι) :
    (ι → k) ≃ₗ[k] ActualHead (M:=QP P) t :=
  (LinearEquiv.ofBijective (headFrame P) ⟨frame_inj_of_eq P hw,frame_surj P⟩) ≪≫ₗ
    toSourceHead P t xt
omit [DecidableEq ι] in
theorem sourceHead_red [FiniteDimensional k (QP P)] (hw : finrank k (xop P).ker=Fintype.card ι)
    (v : Row k ι) : sourceHead P t xt hw (reduceVec k ι v) =
      headProjection t (P.mulVecLin.range.mkQ v) := by
  change toSourceHead P t xt (headFrame P (reduceVec k ι v)) = _
  rw [frame_eq]; rfl
def toSourceTail : Tail (X : O k) P.mulVecLin ≃ₗ[k] tKernel (M:=QP P) t where
  toFun w := ⟨w.1,(xt w.1).trans w.2⟩
  invFun w := ⟨w.1,(xt w.1).symm.trans w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
include xt in
theorem centered_frames [FiniteDimensional k (QP P)] (hw : finrank k (xop P).ker=Fintype.card ι)
    (hp : P.det ≠ 0) :
    ∃ (H : (ι → k) ≃ₗ[k] ActualHead (M:=QP P) t) (D : (ι → k) ≃ₗ[k] tKernel (M:=QP P) t),
      ∀ (Y Y' : sq k ι) (_eq : Y*P=P*Y') (a : k) (y : A),
        (∀ v, y • P.mulVecLin.range.mkQ v = P.mulVecLin.range.mkQ (Y.mulVecLin v) - a • P.mulVecLin.range.mkQ v) →
        (∀ v, H ((redM Y - a • 1).mulVecLin v) = y • H v) ∧
        (∀ v, D ((redM Y' - a • 1).mulVecLin v) = y • D v) := by
  have p0 := constant_P_zero P hw
  obtain ⟨Q,e,_,ev,et⟩ := actual_tail P hp (fun i j => congrFun (congrFun p0 i) j)
  let H := sourceHead P t xt hw
  let D := e ≪≫ₗ toSourceTail P t xt
  refine ⟨H,D,?_⟩
  intro Y Y' eq a y hy
  constructor
  · intro z
    obtain ⟨v,rfl⟩ := reduceVec_surj z
    have hh := congrArg ((headProjection t).restrictScalars k) (hy v)
    have eH (w : Row k ι) : H (reduceVec k ι w) = headProjection t (P.mulVecLin.range.mkQ w) :=
      sourceHead_red P t xt hw w
    rw [reduce_shift,map_sub,map_smul,eH,eH]
    calc _ = ((headProjection t).restrictScalars k) (y • P.mulVecLin.range.mkQ v) := by
               simpa only [map_sub,map_smul,LinearMap.restrictScalars_apply] using hh.symm
         _ = _ := (headProjection t).map_smul y _
  · intro z
    obtain ⟨v,rfl⟩ := reduceVec_surj z
    apply Subtype.ext
    rw [reduce_shift,map_sub,map_smul]
    change (e (reduceVec k ι (Y'.mulVecLin v))).val - a • (e (reduceVec k ι v)).val =
      y • (e (reduceVec k ι v)).val
    rw [et Y Y' eq,ev]
    exact (hy (Q.mulVecLin v)).symm
end Source
end GKEnds
end
noncomputable section
namespace GKEnds
open Module LinearMap
open Gerstenhaber.FourBlocks.MinimalSource
variable {k ι M A : Type*} [Field k] [Fintype ι] [DecidableEq ι]
variable [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
structure SubregularPair (U V : Matrix ι ι k) : Prop where
  comm : Commute U V
  nilY : IsNilpotent U
  nilZ : IsNilpotent V
  width : 2 ≤ finrank k U.mulVecLin.ker
theorem coordinate_criterion (e : (ι → k) ≃ₗ[k] M) (U V : Matrix ι ι k) (y z : A)
    (hy : IsNilpotent y) (hz : IsNilpotent z)
    (ey : ∀ v, e (U.mulVecLin v)=y • e v) (ez : ∀ v, e (V.mulVecLin v)=z • e v)
    (wide : 2 ≤ finrank k (Algebra.lsmul k k M y).ker) : SubregularPair U V := by
  let g : Matrix ι ι k ≃ₐ[k] End k M := Matrix.toLinAlgEquiv'.trans (e.conjAlgEquiv k)
  have rec_ (D : Matrix ι ι k) (a : A) (h : ∀v,e (D.mulVecLin v)=a • e v) :
      g D=Algebra.lsmul k k M a := by
    ext w
    obtain ⟨v,rfl⟩ := e.surjective w
    change e (D.mulVecLin (e.symm (e v))) = a • e v
    rw [e.symm_apply_apply]; exact h v
  have fy := rec_ U y ey
  have fz := rec_ V z ez
  refine ⟨Commute.of_map g.injective ?_,(IsNilpotent.map_iff g.injective).mp ?_,
    (IsNilpotent.map_iff g.injective).mp ?_,wide.trans ?_⟩
  · rw [fy,fz]; exact (Commute.all y z).map (Algebra.lsmul k k M)
  · rw [fy]; exact hy.map (Algebra.lsmul k k M)
  · rw [fz]; exact hz.map (Algebra.lsmul k k M)
  · apply finrank_ker_le_of_injective_intertwining _ _ e.symm.toLinearMap e.symm.injective
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    change e.symm (y • e v)=U.mulVecLin (e.symm (e v))
    rw [←ey,e.symm_apply_apply,e.symm_apply_apply]
end GKEnds
end
noncomputable section
namespace GKEnds
open Module LinearMap DivisorG3 PowerSeries
open Gerstenhaber.FourBlocks.HeadBounds Gerstenhaber.FourBlocks.MinimalSource
open Gerstenhaber.FourBlocks.PrimaryDecomposition
open DVRMinimal
variable {k : Type u} [Field k] [IsAlgClosed k] (r : ℕ)
variable (S : Fin 6 → GKGraph.Mat (O k) r)
abbrev r0 (l : Fin 6) := redM (S l)
theorem least_presented_ends (hp : (S 0).det≠0)
    (sy : S 1*S 0=S 0*S 3) (sz : S 2*S 0=S 0*S 4)
    [FiniteDimensional k (QP (S 0))]
    (T : Fin 3 → End k (QP (S 0))) (hc : ∀ i j, Commute (T i) (T j))
    (h0 : T 0=xop (S 0))
    (h1 : ∀ v, T 1 ((S 0).mulVecLin.range.mkQ v)=(S 0).mulVecLin.range.mkQ ((S 1).mulVecLin v))
    (h2 : ∀ v, T 2 ((S 0).mulVecLin.range.mkQ v)=(S 0).mulVecLin.range.mkQ ((S 2).mulVecLin v))
    (hnil : IsNilpotent (T 0)) (bad : finrank k (QP (S 0)) < finrank k (Generated T))
    (small : ∀ j<r, SafeEverywhere.{u} j) :
    r0 r S 0=0 ∧ ∃ a b : k, SubregularPair (r0 r S 1-a • 1) (r0 r S 2-b • 1) ∧
      SubregularPair (r0 r S 3-a • 1) (r0 r S 4-b • 1) := by
  have le : finrank k (xop (S 0)).ker ≤ r := by simpa only [Fintype.card_fin] using width_le (S 0)
  have eq : finrank k (xop (S 0)).ker = r := by
    apply le_antisymm le
    by_contra! lt
    have hh := small _ lt k (QP (S 0)) T hc hnil (congrArg (fun f : End k (QP (S 0)) => finrank k f.ker) h0)
    exact (not_lt_of_ge hh) bad
  have w : finrank k (xop (S 0)).ker=Fintype.card (Fin r) := eq.trans (Fintype.card_fin _).symm
  refine ⟨constant_P_zero (S 0) w,?_⟩
  obtain ⟨c,hc0,hn,wide⟩ := least_bad_shifted_two_ends T hc hnil bad (fun j hj => small j (by rwa [h0,eq] at hj))
  let U := FiniteNilTriple.of (QP (S 0)) (shifted T c) (shifted_commute T c hc) hn
  letI : CommRing (SourceAlgebra U) := sourceAlgebra_commRing U
  letI : Module (SourceAlgebra U) (QP (S 0)) := (inferInstance : Module (SourceAlgebra U) U.Carrier)
  letI : IsScalarTower k (SourceAlgebra U) (QP (S 0)) := sourceAlgebra_tower U
  let t := sourceRoot U 0
  let y := sourceRoot U 1
  let z := sourceRoot U 2
  have xt (v : QP (S 0)) : t • v = (X : O k) • v := by
    change (T 0 - c 0 • 1) v = _
    rw [hc0,zero_smul,sub_zero,h0]; rfl
  obtain ⟨H,D,act⟩ := centered_frames (A:=SourceAlgebra U) (S 0) t xt w hp
  have actY := act (S 1) (S 3) sy (c 1) y (fun v => by
    change T 1 _ - c 1 • _ = _; rw [h1]; rfl)
  have actZ := act (S 2) (S 4) sz (c 2) z (fun v => by
    change T 2 _ - c 2 • _ = _; rw [h2]; rfl)
  exact ⟨c 1,c 2,
    coordinate_criterion H _ _ y z (sourceRoot_nilpotent U 1) (sourceRoot_nilpotent U 2) actY.1 actZ.1 wide.1,
    coordinate_criterion D _ _ y z (sourceRoot_nilpotent U 1) (sourceRoot_nilpotent U 2) actY.2 actZ.2 wide.2⟩
end GKEnds
end
noncomputable section
namespace GKGraph
variable (k : Type u) [Field k] (r : ℕ)
variable {F : Type u} [Field F] [Algebra k F]
variable {O : Type*} [CommRing O] [IsDomain O]
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 100000 in
def datum (φ : ring k r →+* O) : Fin 6 → Mat O r := fun i => φ.mapMatrix (gmat k r i)
variable [IsDiscreteValuationRing O]
open IsDiscreteValuationRing
end GKGraph
end
noncomputable section
namespace GKGraph
open IsDiscreteValuationRing Module
variable (k : Type*) [Field k] (r : ℕ) {O : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]
set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 90000 in
abbrev bad (T : Fin 6 → Mat O r) (hT : Relations r T) :=
  length O (DivisorG3.QP (T 0)) <
    length O (DivisorG3.actor (T 0) (T 1) (T 3) (T 2) (T 4) hT.y.symm hT.z.symm)
set_option maxHeartbeats 900000 in
set_option synthInstance.maxHeartbeats 90000 in
theorem bad_iff_selected (T : Fin 6 → Mat O r) (hP : (T 0).det ≠ 0)
    (hT : Relations r T) (hr : 0 < r) :
    bad r T hT ↔ ∃ s : selectCols r,
      addVal O (fullMinor r (T 0) (T 1) (T 2) s) < addVal O ((T 0).det^(r-1)) := by
  have h := DivisorG3.bad_iff_minor (T 0) (T 1) (T 3) (T 2) (T 4) (T 5) hP
    (by simpa only [Fintype.card_fin] using hr) hT.y.symm hT.z.symm hT.comm.symm
  let f (n : ℕ) := ∃ s : Row r → Row r ⊕ (Fin n × Fin n),
    addVal O (((DivisorG3.blockColumns (T 0) (DivisorG3.box (T 1) (T 2) n n)).submatrix id s).det) <
      addVal O ((T 0).det^(n-1))
  change bad r T hT ↔ f (Fintype.card (Fin r)) at h
  rw [Fintype.card_fin] at h
  exact h
end GKGraph
end
noncomputable section
namespace GKEnds
open Module LinearMap DivisorG3 PowerSeries IsDiscreteValuationRing
open DVRMinimal GKGraph
variable {k : Type u} [Field k] [IsAlgClosed k] (r : ℕ)
theorem strict_end_coordinates (S : Fin 6 → Mat (O k) r)
    (sr : Relations r S) (hp : (S 0).det≠0) (hr : 0 < r)
    (s : selectCols r) (hs : addVal (O k) (fullMinor r (S 0) (S 1) (S 2) s) <
      addVal (O k) ((S 0).det^(r-1)))
    (small : ∀ j<r, SafeEverywhere.{u} j) :
    r0 r S 0=0 ∧ ∃ a b : k, SubregularPair (r0 r S 1-a • 1) (r0 r S 2-b • 1) ∧
      SubregularPair (r0 r S 3-a • 1) (r0 r S 4-b • 1) := by
  have pos : 0<Fintype.card (Fin r) := by simpa using hr
  have hb := (bad_iff_selected r S hp sr hr).mpr ⟨s,hs⟩
  have low := (bad_iff_minor _ _ _ _ _ _ hp pos sr.y.symm sr.z.symm sr.comm.symm).mp hb
  obtain ⟨fin,hn,hc,bad'⟩ := strict_to_native _ _ _ _ _ _ hp pos sr.y.symm sr.z.symm sr.comm.symm low
  letI := fin
  exact least_presented_ends r S hp sr.y.symm sr.z.symm _ hc rfl (fun _ => rfl) (fun _ => rfl) hn bad' small
end GKEnds
end
noncomputable section
namespace G3Assembly
open Module GKGraph GKDivisor GKDivisor.Jet GKEnds DVRMinimal
local instance BadPole.instCr7 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom7 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr7 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg7 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
variable {k : Type u} [Field k] [IsAlgClosed k] {r : ℕ}
theorem actual_center_pairs (W : RealWitness k r) (hr : 0<r) (small : ∀ j<r,SafeEverywhere.{u} j) :
    let R := reducedMatrices k r (graphAtClosure W.pole)
    R 0=0 ∧ ∃ a b : ClosedF W.pole, SubregularPair (R 1-a • 1) (R 2-b • 1) ∧
      SubregularPair (R 3-a • 1) (R 4-b • 1) := by
  have hs := strict_end_coordinates r W.arc.T W.arc.relations W.arc.det_ne hr W.s W.arc.strict small
  have eq (i : Fin 6) : reducedMatrices k r (graphAtClosure W.pole) i = r0 r W.arc.T i := by
    ext a b
    exact (congrFun W.same_entries (i,a,b)).symm
  dsimp only
  simp only [eq]
  exact hs
end G3Assembly
end
noncomputable section
namespace G3Assembly
open Module GKGraph GKDivisor GKDivisor.Jet DVRMinimal
local instance BadPole.instCr8 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom8 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr8 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg8 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
variable {k : Type u} [Field k] [IsAlgClosed k] {r : ℕ}
theorem witness_budget_impossible (W : RealWitness k r) (hr : 2≤r) (a b : ClosedF W.pole)
    (s t : Finset (ClosedF W.pole)) (hs : s.card≤r*r-2) (ht : t.card≤r*r-2)
    (h0 : reducedMatrices k r (graphAtClosure W.pole) 0=0)
    (h1 : ∀ i j, (reducedMatrices k r (graphAtClosure W.pole) 1 - a • 1) i j ∈ IntermediateField.adjoin k (s:Set _))
    (h2 : ∀ i j, (reducedMatrices k r (graphAtClosure W.pole) 2 - b • 1) i j ∈ IntermediateField.adjoin k (s:Set _))
    (h3 : ∀ i j, (reducedMatrices k r (graphAtClosure W.pole) 3 - a • 1) i j ∈ IntermediateField.adjoin k (t:Set _))
    (h4 : ∀ i j, (reducedMatrices k r (graphAtClosure W.pole) 4 - b • 1) i j ∈ IntermediateField.adjoin k (t:Set _)) :
    False := by
  have le := centered_parameter_bound k r (graphAtClosure W.pole) hr ![a,b] s t hs ht h0 h1 h2 h3 h4
  have cap := add_le_add_left le 1
  rw [W.count] at cap
  have hn : 3*r*r≤3*r*r-2+1 := by exact_mod_cast cap
  have hp : 2≤r*r := (by decide : 2≤2*2).trans (Nat.mul_le_mul hr hr)
  rw [Nat.mul_assoc] at hn
  omega
end G3Assembly
end
noncomputable section
namespace GKGauge
open Matrix MvPolynomial LinearMap Finset
variable {k F : Type*} [Field k] [Infinite k] [Field F] [Algebra k F]
theorem exists_base_eval {σ : Type*} (p : MvPolynomial σ F) (hp : p ≠ 0) :
    ∃ x : σ → k, MvPolynomial.eval (fun i => algebraMap k F (x i)) p ≠ 0 := by
  classical
  by_contra! h
  apply hp
  apply MvPolynomial.funext_set (fun _ : σ => Set.range (algebraMap k F))
    (fun _ => Set.infinite_range_of_injective (algebraMap k F).injective)
  intro t ht
  choose x hx using fun i => ht i (Set.mem_univ i)
  simpa only [← funext hx, map_zero] using h x
variable {σ n : Type*} [Fintype σ] [Fintype n] [DecidableEq n]
def genericMatrix (v : σ → Matrix n n F) : Matrix n n (MvPolynomial σ F) :=
  fun a b => ∑ i, C (v i a b) * X i
theorem eval_genericMatrix (v : σ → Matrix n n F) (x : σ → F) :
    (MvPolynomial.eval x).mapMatrix (genericMatrix v) = ∑ i, x i • v i := by
  classical
  ext a b
  simp [genericMatrix, Matrix.sum_apply, mul_comm]
theorem exists_base_invertible (v : σ → Matrix n n F) (h : ∃ x : σ → F, (∑ i, x i • v i).det ≠ 0) :
    ∃ x : σ → k, (∑ i, (algebraMap k F (x i)) • v i).det ≠ 0 := by
  classical
  obtain ⟨x,hx⟩ := h
  have hp : (genericMatrix v).det ≠ 0 := by
    intro hz
    apply hx
    rw [← eval_genericMatrix, ← RingHom.map_det, hz, map_zero]
  obtain ⟨a,ha⟩ := exists_base_eval (k:=k) _ hp
  refine ⟨a, ?_⟩
  rw [← eval_genericMatrix, ← RingHom.map_det]
  exact ha
end GKGauge
end
noncomputable section
namespace GKGauge
open LinearMap Module
variable {F : Type u} [Field F] {ι : Type u} [Fintype ι]
variable {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
theorem exists_chart (L : ι → V →ₗ[F] F) (hL : ∀ v ≠ (0 : V), ∃ i, L i v ≠ 0) :
    ∃ a : Fin (finrank F V) → ι, Function.Injective a ∧
      ∃ e : V ≃ₗ[F] (Fin (finrank F V) → F), ∀ v i, e v i = L (a i) v := by
  classical
  have hsp : Submodule.span F (Set.range L) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro v hv
    obtain ⟨i,hi⟩ := hL v hv
    exact ⟨_, ⟨i,rfl⟩, hi⟩
  obtain ⟨κ,a,ha,hsp',hli⟩ := exists_linearIndependent' F L
  let _ : Fintype κ := Fintype.ofInjective _ ha
  let b : Basis κ F (Module.Dual F V) := Basis.mk hli (by rw [hsp',hsp])
  have hcard : Fintype.card κ = finrank F V := by
    rw [← Module.finrank_eq_card_basis b, Subspace.dual_finrank_eq]
  let a' := (Fintype.equivFinOfCardEq hcard).symm
  let h := a' |>.trans (Equiv.refl κ)
  let b' := b.reindex h.symm
  let e := (Module.evalEquiv F V).trans (b'.constr F).symm
  refine ⟨a ∘ h, ha.comp h.injective, e, ?_⟩
  intro v i
  change ((b'.constr F).symm (Module.evalEquiv F V v)) i = _
  rw [Basis.constr_symm_apply]
  simp [b',b,Function.comp_def]
end GKGauge
end
noncomputable section
namespace GKGauge
open LinearMap Module Finset Matrix
variable {F k : Type u} [Field k] [Infinite k] [Field F] [Algebra k F]
variable {n : Type u} [Fintype n] [DecidableEq n]
def entry (S : Submodule F (Matrix n n F)) (p : n × n) : S →ₗ[F] F where
  toFun z := z.val p.1 p.2
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
theorem gauge_subspace (S : Submodule F (Matrix n n F))
    (h : ∃ z : S, z.val.det ≠ 0) :
    ∃ z : S, z.val.det ≠ 0 ∧ ∃ a : Fin (finrank F S) ↪ n × n,
      ∀ i, z.val (a i).1 (a i).2 ∈ Set.range (algebraMap k F) := by
  classical
  have sep : ∀ v ≠ 0, ∃ i, entry S i v ≠ 0 := by
    intro (v : S) hv
    by_contra! hh
    apply hv; apply Subtype.ext; ext i j
    exact hh (i,j)
  obtain ⟨a,ha,e,he⟩ := exists_chart (entry S) sep
  let κ := Fin (finrank F S)
  let B := Pi.basisFun F κ
  let v : κ → Matrix n n F := fun i => (e.symm (B i)).val
  have hsum (x : κ → F) : ∑ j, x j • v j = (e.symm x).val := by
    have hx := congrArg (fun y => (e.symm y).val) (B.sum_repr x)
    simpa [v,B,Pi.basisFun_repr] using hx
  obtain ⟨z,hz⟩ := h
  have hh : ∃ x : κ → F, (∑ i, x i • v i).det ≠ 0 :=
    ⟨e z, by rw [hsum, e.symm_apply_apply]; exact hz⟩
  obtain ⟨w,hw⟩ := exists_base_invertible (k:=k) v hh
  let w' : κ → F := fun i => algebraMap k F (w i)
  refine ⟨e.symm w', ?_, ⟨a,ha⟩, ?_⟩
  · rwa [← hsum]
  · intro i
    refine ⟨w i, ?_⟩
    have hi := he (e.symm w') i
    rw [e.apply_symm_apply] at hi
    exact hi
end GKGauge
end
noncomputable section
namespace GKGauge
open Module Matrix Finset
variable {F k : Type u} [Field k] [Infinite k] [Field F] [Algebra k F]
variable {n : Type u} [Fintype n] [DecidableEq n]
theorem gauge_parameters (S : Submodule F (Matrix n n F)) (h : ∃ z : S, z.val.det ≠ 0) :
    ∃ z : S, z.val.det ≠ 0 ∧ ∃ s : Finset F,
      s.card ≤ Fintype.card n * Fintype.card n - finrank F S ∧
      ∀ i j, z.val i j ∈ IntermediateField.adjoin k (s : Set F) := by
  classical
  obtain ⟨z,hz,a,ha⟩ := gauge_subspace (k:=k) S h
  let p : Finset (n × n) := univ.map a
  let g : n × n → F := fun t => z.val t.1 t.2
  let s := pᶜ.image g
  refine ⟨z,hz,s, ?_, ?_⟩
  · calc
      s.card ≤ pᶜ.card := card_image_le
      _ = _ := by rw [Finset.card_compl]; simp [p]
  · intro i j
    by_cases hi : (i,j) ∈ p
    · obtain ⟨l,_,hl⟩ := mem_map.mp hi
      have e := ha l; rw [hl] at e
      obtain ⟨v,hv⟩ := e
      rw [← hv]; exact IntermediateField.algebraMap_mem _ _
    · exact IntermediateField.subset_adjoin k _ (mem_image.mpr ⟨(i,j),mem_compl.mpr hi,rfl⟩)
omit [Infinite k] in
theorem recovery_mem (L : IntermediateField k F) (A H J : Matrix n n F)
    (hH : ∀ i j, H i j ∈ L) (hJ : ∀ i j, J i j ∈ L)
    (hdet : H.det ≠ 0) (hi : A * H = H * J) : ∀ i j, A i j ∈ L := by
  let H' : Matrix n n L := fun i j => ⟨_, hH i j⟩
  let J' : Matrix n n L := fun i j => ⟨_, hJ i j⟩
  let f : L →+* F := L.val.toRingHom
  have hf : f.mapMatrix H' = H := rfl
  have hj : f.mapMatrix J' = J := rfl
  have hd : H'.det ≠ 0 := by
    intro h; apply hdet
    rw [← hf, ← RingHom.map_det, h, map_zero]
  have hone : H * f.mapMatrix (H'⁻¹) = 1 := by
    rw [← hf, ← map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd), map_one]
  have he : f.mapMatrix (H' * J' * H'⁻¹) = A := by
    rw [map_mul,map_mul,hf,hj,← hi, Matrix.mul_assoc, hone, Matrix.mul_one]
  intro i j
  rw [← he]
  exact ((H' * J' * H'⁻¹) i j).property
end GKGauge
end
noncomputable section
namespace GKGauge
open Module Matrix
variable {k F : Type u} [Field k] [Infinite k] [Field F] [Algebra k F]
variable {n : Type u} [Fintype n] [DecidableEq n]
def intertwiner (A J : Matrix n n F) : Submodule F (Matrix n n F) where
  carrier := {H | A * H = H * J}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy; change A * (x+y)=(x+y)*J
    rw [mul_add,add_mul,hx,hy]
  smul_mem' := by
    intro a x hx; change A*(a • x)=(a • x)*J
    rw [Matrix.mul_smul,Matrix.smul_mul,hx]
@[simp] theorem mem_intertwiner (A J H : Matrix n n F) :
  H ∈ intertwiner A J ↔ A * H = H * J := Iff.rfl
def centralizerIso (A J H : Matrix n n F) (hH : H.det ≠ 0) (hc : A * H = H * J) :
  intertwiner J J ≃ₗ[F] intertwiner A J := by
  let hi : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH)
  let hi' : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH)
  have hc' : J * H⁻¹ = H⁻¹ * A := by
    calc
      J * H⁻¹ = (H⁻¹*H) * (J*H⁻¹) := by rw [hi,one_mul]
      _ = H⁻¹ * (H*J) * H⁻¹ := by simp only [mul_assoc]
      _ = H⁻¹ * A := by rw [← hc]; simp only [mul_assoc,hi',mul_one]
  exact {
    toFun := fun x => ⟨H*x.1, by
      change A*(H*x.val)=(H*x.val)*J
      rw [← mul_assoc,hc,mul_assoc,x.property,← mul_assoc]⟩
    invFun := fun x => ⟨H⁻¹*x.1,by
      change J*(H⁻¹*x.val)=(H⁻¹*x.val)*J
      rw [← mul_assoc,hc',mul_assoc,x.property,←mul_assoc]⟩
    left_inv := fun x => by
      apply Subtype.ext; change H⁻¹ * (H * x.val)=x.val
      rw [←mul_assoc,hi,one_mul]
    right_inv := fun x => by
      apply Subtype.ext; change H * (H⁻¹ * x.val)=x.val
      rw [←mul_assoc,hi',one_mul]
    map_add' := fun x y => by apply Subtype.ext; exact mul_add _ _ _
    map_smul' := fun a x => by apply Subtype.ext; exact Matrix.mul_smul _ _ _
  }
theorem orbit_parameters (A J : Matrix n n F)
    (h : ∃ H : Matrix n n F, H.det ≠ 0 ∧ A * H = H * J)
    (hJ : ∀ i j, J i j ∈ (algebraMap k F).range) :
    ∃ (s : Finset F) (H : Matrix n n F), s.card ≤
        Fintype.card n * Fintype.card n - finrank F (intertwiner J J) ∧
      H.det ≠ 0 ∧ A*H=H*J ∧
      (∀ i j, H i j ∈ IntermediateField.adjoin k (s : Set F)) ∧
      ∀ i j, A i j ∈ IntermediateField.adjoin k (s : Set F) := by
  obtain ⟨P,hp,he⟩ := h
  have hd := (centralizerIso A J P hp he).finrank_eq
  obtain ⟨z,hz,s,hs,hm⟩ := gauge_parameters (k:=k) (intertwiner A J) ⟨⟨P,he⟩,hp⟩
  rw [← hd] at hs
  refine ⟨s,z.val,hs,hz,z.property,hm,recovery_mem _ A z.val J hm ?_ hz z.property⟩
  intro i j
  obtain ⟨a,ha⟩ := hJ i j
  exact ha ▸ IntermediateField.algebraMap_mem _ a
end GKGauge
end
noncomputable section
namespace GKGauge
open Module Matrix Finset
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F]
set_option maxHeartbeats 45000 in
theorem finset_to_list (s : Finset F) (N : ℕ) (h : s.card ≤ N) :
    ∃ w : Fin N → F, ∀ L : IntermediateField k F, (∀ i, w i ∈ L) →
      IntermediateField.adjoin k (s : Set F) ≤ L := by
  classical
  let e : (s : Type) ≃ Fin s.card := Fintype.equivFinOfCardEq (by simp)
  let w : Fin N → F := fun i => if hi : i.val < s.card then (e.symm ⟨i.val,hi⟩).val else 0
  refine ⟨w,?_⟩
  intro L hL; apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  let j := e ⟨x,hx⟩
  let i : Fin N := ⟨j.val,lt_of_lt_of_le j.isLt h⟩
  have hmem := hL i
  change x ∈ L
  simpa only [w,i,dif_pos j.isLt,Fin.eta,j,e.symm_apply_apply] using hmem
end GKGauge
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
abbrev V (K : Type*) {H : ℕ} (m : Fin H → ℕ) :=
  (h : Fin H) → Fin (h.val+1) → (Fin (m h) → K)
abbrev B (K : Type*) {H : ℕ} (m : Fin H → ℕ) [Field K] :=
  (h : Fin H) → Module.End K (Fin (m h) → K)
def J : Module.End K (V K m) where
  toFun v h j := if hj : j.val + 1 < h.val + 1 then v h ⟨j.val+1,hj⟩ else 0
  map_add' v w := by ext h j a; dsimp; split <;> simp
  map_smul' u v := by ext h j a; dsimp; split <;> simp
theorem Jpow (k : ℕ) (v : V K m) (h : Fin H) (j : Fin (h.val+1)) :
    ((J m ^ k) v) h j =
    if hj : j.val+k < h.val+1 then v h ⟨j.val+k,hj⟩ else 0 := by
  induction k generalizing j with
  | zero => simp [j.isLt]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (if hc : j.val+1 < h.val+1 then ((J m ^ k) v) h ⟨j.val+1,hc⟩ else 0) = _
    split_ifs with hc hd
    · rw [ih]; simp [Nat.add_assoc, Nat.add_comm 1 k, hd]
    · rw [ih]; simp [show ¬ (j.val+1+k < h.val+1) by omega]
    · omega
    · rfl
abbrev Cent := Subalgebra.centralizer K ({J (K:=K) m} : Set (Module.End K (V K m)))
theorem commJ (z : Cent (K:=K) m) : Commute (z:Module.End K (V K m)) (J m) := by
  exact (z.property _ (Set.mem_singleton _)).symm
def Fl (k : ℕ) (v : V K m) : Prop :=
  ∀ (h : Fin H) (j : Fin (h.val+1)), j.val ≠ 0 ∨ h.val < k → v h j = 0
theorem fl_iff (k : ℕ) (v : V K m) :
    Fl m k v ↔ J m v = 0 ∧ ∃ w, (J m ^ k) w = v := by
  constructor
  · intro hv
    constructor
    · funext h j
      change (if hc : j.val + 1 < h.val+1 then v h ⟨j.val+1,hc⟩ else 0) = 0
      split <;> first | apply hv; exact Or.inl (Nat.succ_ne_zero _) | rfl
    · refine ⟨fun h i => if i.val = k then v h 0 else 0,?_⟩
      funext h j
      rw [Jpow]
      by_cases hz : j.val = 0
      · obtain rfl : j = 0 := Fin.ext hz
        simp only [Fin.val_zero,Nat.zero_add]
        split_ifs with hh
        · rfl
        · exact (hv h 0 (Or.inr (by omega))).symm
      · split_ifs with hh he
        · change j.val+k = k at he; omega
        · exact (hv h j (Or.inl hz)).symm
        · exact (hv h j (Or.inl hz)).symm
  · rintro ⟨hn,w,hw⟩ h j (hj|hh)
    · let i : Fin (h.val+1) := ⟨j.val-1,by have := j.isLt; omega⟩
      have hi : i.val+1 = j.val := by dsimp [i]; omega
      have hc := congrFun (congrFun hn h) i
      change (if hx : i.val+1<h.val+1 then v h ⟨i.val+1,hx⟩ else 0) = 0 at hc
      simpa [hi,j.isLt] using hc
    · rw [← hw,Jpow,dif_neg (by omega)]
theorem map_fl (z : Cent (K:=K) m) (k : ℕ) {v : V K m} (hv : Fl m k v) :
    Fl m k (z.1 v) := by
  rw [fl_iff] at hv ⊢
  obtain ⟨hzero,w,rfl⟩ := hv
  constructor
  · calc
      J m (z.1 ((J m ^ k) w)) = z.1 (J m ((J m ^ k) w)) :=
        congrArg (fun f : Module.End K (V K m) => f ((J m ^ k) w)) (commJ m z).eq.symm
      _ = 0 := by rw [hzero,map_zero]
  · exact ⟨z.1 w,congrArg (fun f : Module.End K (V K m) => f w)
        ((commJ m z).pow_right k).eq.symm⟩
def put (h : Fin H) : (Fin (m h) → K) →ₗ[K] V K m :=
  (LinearMap.single K _ h).comp (LinearMap.single K (fun _ : Fin (h.val+1) => Fin (m h) → K) 0)
@[simp] theorem put_at (h : Fin H) (u : Fin (m h) → K) :
    put m h u h 0 = u := by simp [put]
theorem put_fl (h : Fin H) (u : Fin (m h) → K) : Fl m h.val (put m h u) := by
  intro l j hj
  by_cases he : l=h
  · subst l
    have hj' : j ≠ 0 := fun hh => by subst j; simp at hj
    simp [put,Pi.single_eq_of_ne hj']
  · simp [put,Pi.single_eq_of_ne he]
theorem discard (h : Fin H) (v : V K m) (hv : Fl m h.val v) :
    Fl m (h.val+1) (v - put m h (v h 0)) := by
  intro l j hj
  by_cases hh : l=h
  · subst l
    by_cases hz : j=0
    · subst j; simp
    · have hj' : j.val ≠ 0 := fun e => hz (Fin.ext e)
      simp [put,Pi.single_eq_of_ne hz,hv h j (Or.inl hj')]
  · have hl : l.val ≠ h.val := fun e => hh (Fin.ext e)
    have hclean : j.val ≠ 0 ∨ l.val < h.val := by rcases hj with hj|hj <;> omega
    simp [put,Pi.single_eq_of_ne hh,hv l j hclean]
def part (z : Cent (K:=K) m) (h : Fin H) : Module.End K (Fin (m h) → K) :=
  (LinearMap.proj 0).comp ((LinearMap.proj h).comp (z.1.comp (put m h)))
theorem eval_fl (z : Cent (K:=K) m) (h : Fin H) (v : V K m) (hv : Fl m h.val v) :
    z.1 v h 0 = part m z h (v h 0) := by
  have he := map_fl m z (h.val+1) (discard m h v hv) h 0 (Or.inr (Nat.lt_succ_self _))
  change (z.1 (v - put m h (v h 0))) h 0 = 0 at he
  rw [map_sub] at he
  exact sub_eq_zero.mp he
def primitive : Cent (K:=K) m →ₐ[K] B K m where
  toFun := part m
  map_one' := by funext h; apply LinearMap.ext; intro u; exact put_at m h u
  map_mul' z w := by
    funext h
    apply LinearMap.ext
    intro u
    exact eval_fl m z h (w.1 (put m h u)) (map_fl m w _ (put_fl m h u))
  map_zero' := by funext h; apply LinearMap.ext; intro u; rfl
  map_add' z w := by funext h; apply LinearMap.ext; intro u; rfl
  commutes' c := by
    funext h
    apply LinearMap.ext
    intro u
    change c • put m h u h 0 = c • u
    rw [put_at]
def liftEnd (f : B K m) : Module.End K (V K m) where
  toFun v h i := f h (v h i)
  map_add' v w := by funext h i; exact (f h).map_add _ _
  map_smul' a v := by funext h i; exact (f h).map_smul a _
theorem lift_mem (f : B K m) : liftEnd m f ∈ Cent (K:=K) m := by
  apply (Subalgebra.mem_centralizer_iff K).mpr
  rintro _ ⟨rfl⟩
  apply LinearMap.ext
  intro v
  funext h j
  change (if hq : j.val+1<h.val+1 then f h (v h ⟨j.val+1,hq⟩) else 0) =
    f h (if hq : j.val+1<h.val+1 then v h ⟨j.val+1,hq⟩ else 0)
  split_ifs <;> simp
def sectionHom : B K m →ₐ[K] Cent (K:=K) m where
  toFun f := ⟨liftEnd m f,lift_mem m f⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
@[simp] theorem primitive_section (f : B K m) :
    primitive m (sectionHom m f) = f := by
  funext h
  apply LinearMap.ext
  intro v
  change f h (put m h v h 0) = f h v
  rw [put_at]
theorem primitive_surjective : Function.Surjective (primitive (K:=K) m) :=
  fun f => ⟨sectionHom m f, primitive_section m f⟩
theorem part_nilpotent (z : Cent (K:=K) m) (hz : IsNilpotent z.1) (h : Fin H) :
    IsNilpotent (part m z h) := by
  obtain ⟨n,hn⟩ := hz
  have hc : z ^ n = 0 := Subtype.ext (by simpa using hn)
  have he := congrArg (fun w : Cent (K:=K) m => primitive m w h) hc
  simpa [map_pow] using (show IsNilpotent (part m z h) from
    ⟨n,by change (primitive m z h)^n=0; simpa [map_pow] using he⟩)
theorem target_finrank : finrank K (B K m) = ∑ h, m h ^ 2 := by
  change finrank K ((h : Fin H) → Module.End K (Fin (m h) → K)) = _
  rw [finrank_pi_fintype]
  simp only [Module.End,finrank_linearMap,finrank_pi,Fintype.card_fin,pow_two]
theorem primitive_rank_nullity :
    (∑ h, m h ^ 2) + finrank K (LinearMap.ker (primitive (K:=K) m).toLinearMap) =
    finrank K (Cent (K:=K) m) := by
  have e := LinearMap.finrank_range_add_finrank_ker (K:=K)
    (V:=Cent (K:=K) m) (V₂:=B K m) (primitive (K:=K) m).toLinearMap
  rw [LinearMap.range_eq_top.mpr (primitive_surjective (K:=K) m),finrank_top,target_finrank] at e
  exact e
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
theorem kernel_push (z : Cent (K:=K) m) (hz : primitive m z = 0)
    (k : ℕ) (v : V K m) (hv : Fl m k v) : Fl m (k+1) (z.1 v) := by
  have hc := map_fl m z k hv
  intro h j hj
  by_cases he : h.val = k
  · by_cases hj0 : j = 0
    · subst j; subst k
      rw [eval_fl m z h v hv]
      have hp : part m z h = 0 := congrFun hz h
      rw [hp]; rfl
    · exact hc h j (Or.inl (fun e => hj0 (Fin.ext e)))
  · apply hc
    rcases hj with hj|hj
    · exact Or.inl hj
    · exact Or.inr (by omega)
theorem kernel_kills_socle (z : Cent (K:=K) m) (hz : primitive m z = 0)
    (v : V K m) (hv : J m v = 0) : (z.1 ^ H) v = 0 := by
  have hi (k : ℕ) : Fl m k ((z.1 ^ k) v) := by
    induction k with
    | zero =>
      rw [pow_zero]
      apply (fl_iff m 0 v).mpr
      exact ⟨hv,v,by simp⟩
    | succ k ih =>
      rw [pow_succ',Module.End.mul_apply]
      exact kernel_push m z hz k _ ih
  funext h j
  exact hi H h j (Or.inr h.isLt)
theorem commuting_kills_kernel_pow {M : Type*} [AddCommGroup M] [Module K M]
    (P T : Module.End K M) (hPT : Commute P T)
    (hker : ∀ v, T v = 0 → P v = 0) (k : ℕ) (v : M) (hv : (T^k) v = 0) :
    (P^k) v = 0 := by
  induction k generalizing v with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ,Module.End.mul_apply] at hv
    rw [pow_succ',Module.End.mul_apply]
    apply hker
    calc
      T ((P^k) v) = (P^k) (T v) := congrArg (fun f : Module.End K M => f v)
        (hPT.pow_left k).eq.symm
      _ = 0 := ih _ hv
theorem kernel_nilpotent_bound (z : Cent (K:=K) m) (hz : primitive m z = 0) :
    z.1 ^ (H*H) = 0 := by
  rw [pow_mul]
  apply LinearMap.ext
  intro v
  apply commuting_kills_kernel_pow _ (J m) ((commJ m z).pow_left H)
    (kernel_kills_socle m z hz) H v
  funext h j
  rw [Jpow, dif_neg (by have := h.isLt; omega)]
  rfl
theorem nilpotent_iff_blocks (z : Cent (K:=K) m) :
    IsNilpotent z.1 ↔ ∀ h, IsNilpotent (part m z h) := by
  refine ⟨part_nilpotent m z,?_⟩
  intro hp
  choose e he using hp
  let N := ∑ h, e h
  have hzero : primitive m (z^N) = 0 := by
    rw [map_pow]
    funext h
    change ((primitive m z) h)^N = 0
    apply pow_eq_zero_of_le (Finset.single_le_sum (fun i _ => Nat.zero_le (e i))
      (Finset.mem_univ h)) (he h)
  refine ⟨N*(H*H),?_⟩
  rw [pow_mul]
  exact kernel_nilpotent_bound m (z^N) hzero
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
abbrev Ix := (h : Fin H) × ((_p : Fin (h.val+1)) × Fin (m h))
def coordBasis : Basis (Ix m) K (V K m) :=
  Pi.basis fun h => Pi.basis fun _ => Pi.basisFun K (Fin (m h))
theorem coord_repr (v : V K m) (h : Fin H) (p : Fin (h.val+1)) (a : Fin (m h)) :
    (coordBasis m).repr v ⟨h,p,a⟩ = v h p a := by
  simp [coordBasis,Pi.basis_repr,Pi.basisFun_repr]
theorem coord_apply (h : Fin H) (p : Fin (h.val+1)) (a : Fin (m h)) :
    (coordBasis (K:=K) m) ⟨h,p,a⟩ = Pi.single h (Pi.single p (Pi.single a 1)) := by
  simp [coordBasis,Pi.basis_apply,Pi.basisFun_apply]
def matrixJ := LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m) (J m)
theorem matrixJ_apply (h : Fin H) (p q : Fin (h.val+1)) (a b : Fin (m h)) :
    matrixJ (K:=K) m ⟨h,p,a⟩ ⟨h,q,b⟩ =
      if p.val+1=q.val ∧ a=b then 1 else 0 := by
  rw [matrixJ,LinearMap.toMatrixAlgEquiv_apply,coord_repr,coord_apply]
  change (if hc : p.val+1 < h.val+1 then
    (Pi.single h (Pi.single q (Pi.single b (1:K))) : V K m) h ⟨p.val+1,hc⟩ else 0) a = _
  by_cases hs : p.val+1=q.val
  · have hq : q.val ≤ h.val := Nat.le_of_lt_succ q.isLt
    simp [hs,hq,Pi.single_apply]
  · by_cases hh : p.val+1<h.val+1
    · have hn : (⟨p.val+1,hh⟩ : Fin (h.val+1)) ≠ q := fun e => hs (congrArg Fin.val e)
      simp [hh,hs,Pi.single_eq_of_ne hn]
    · simp [hh,hs]
theorem matrixJ_other (h l : Fin H) (p : Fin (h.val+1)) (q : Fin (l.val+1))
    (a : Fin (m h)) (b : Fin (m l)) (hh : h≠l) :
    matrixJ (K:=K) m ⟨h,p,a⟩ ⟨l,q,b⟩ = 0 := by
  rw [matrixJ,LinearMap.toMatrixAlgEquiv_apply,coord_repr,coord_apply]
  change (if hc : p.val+1 < h.val+1 then
    (Pi.single l (Pi.single q (Pi.single b (1:K))) : V K m) h ⟨p.val+1,hc⟩ else 0) a = 0
  split <;> simp [Pi.single_eq_of_ne hh]
def rawBlock (Z : Matrix (Ix m) (Ix m) K) (h : Fin H) : Matrix (Fin (m h)) (Fin (m h)) K :=
  fun a b => Z ⟨h,0,a⟩ ⟨h,0,b⟩
def Bmat (K : Type*) {H : ℕ} (m : Fin H → ℕ) :=
  (h : Fin H) → Matrix (Fin (m h)) (Fin (m h)) K
theorem block_entry (z : Cent (K:=K) m) (h : Fin H) :
    LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin (m h))) (part m z h) =
      rawBlock m (LinearMap.toMatrixAlgEquiv (coordBasis m) z.1) h := by
  ext a b
  rw [LinearMap.toMatrixAlgEquiv_apply,Pi.basisFun_repr,
      Pi.basisFun_apply]
  change z.1 (put m h (Pi.single b 1)) h 0 a = _
  rw [rawBlock,LinearMap.toMatrixAlgEquiv_apply,coord_repr,coord_apply]
  rfl
def decode (Z : Matrix (Ix m) (Ix m) K) (hZ : Commute Z (matrixJ m)) : Cent (K:=K) m := by
  let e := LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m)
  refine ⟨e.symm Z, (Subalgebra.mem_centralizer_iff K).mpr ?_⟩
  rintro _ ⟨rfl⟩
  apply e.injective
  simpa [e,matrixJ] using hZ.eq.symm
@[simp] theorem encode_decode (Z : Matrix (Ix m) (Ix m) K) (hZ : Commute Z (matrixJ m)) :
    LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m) (decode m Z hZ).1 = Z :=
  AlgEquiv.apply_symm_apply _ _
theorem matrix_block_nilpotent_iff (Z : Matrix (Ix m) (Ix m) K)
    (hZ : Commute Z (matrixJ m)) :
    IsNilpotent Z ↔ ∀ h, IsNilpotent (rawBlock m Z h) := by
  let z := decode m Z hZ
  have htrans : IsNilpotent Z ↔ IsNilpotent z.1 := by
    rw [← encode_decode m Z hZ]
    exact IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv (coordBasis (K:=K) m)).injective
  rw [htrans,nilpotent_iff_blocks]
  apply forall_congr'
  intro h
  have e := block_entry m z h
  rw [show (LinearMap.toMatrixAlgEquiv (coordBasis m)) z.1=Z from encode_decode m Z hZ] at e
  rw [← e]
  exact (IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv (Pi.basisFun K (Fin (m h)))).injective).symm
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
def gen (h : Fin H) (a : Fin (m h)) : V K m :=
  coordBasis m ⟨h,Fin.last h.val,a⟩
theorem gen_level (h : Fin H) (p : Fin (h.val+1)) (a : Fin (m h)) :
    ((J m ^ (h.val-p.val)) (gen (K:=K) m h a)) = coordBasis m ⟨h,p,a⟩ := by
  funext l q
  rw [Jpow,gen,coord_apply,coord_apply]
  by_cases he : l=h
  · subst l
    by_cases hq : q=p
    · subst q
      have hu : p.val + (h.val-p.val) = h.val := by have := p.isLt; omega
      simp [hu,Pi.single_eq_same]
      exact Pi.single_eq_same _ _
    · have hne : q.val + (h.val-p.val) ≠ h.val := by
        have := p.isLt
        have hqp : q.val ≠ p.val := fun e => hq (Fin.ext e)
        omega
      simp only [Pi.single_eq_same,Pi.single_eq_of_ne hq]
      split_ifs with hc
      · exact Pi.single_eq_of_ne (fun e => hne (congrArg Fin.val e)) _
      · rfl
  · split_ifs <;> rw [Pi.single_eq_of_ne he] <;> simp [Pi.single_eq_of_ne he]
theorem gen_killed (h : Fin H) (a : Fin (m h)) :
    ((J m ^ (h.val+1)) (gen (K:=K) m h a)) = 0 := by
  funext l q
  rw [Jpow,gen,coord_apply]
  by_cases he : l=h
  · subst l; rw [dif_neg (by omega)]; rfl
  · split_ifs <;> simp [Pi.single_eq_of_ne he]
abbrev Coeff (K : Type*) [Field K] {H : ℕ} (m : Fin H → ℕ) :=
  (h : Fin H) → Fin (m h) → LinearMap.ker (J (K:=K) m ^ (h.val+1))
def ofCoeff (f : Coeff K m) : Module.End K (V K m) :=
  (coordBasis (K:=K) m).constr K
    (fun i => (J m ^ (i.1.val-i.2.1.val)) (f i.1 i.2.2).1)
theorem coeff_at (f : Coeff K m) (h : Fin H) (p : Fin (h.val+1)) (a : Fin (m h)) :
    ofCoeff m f (coordBasis m ⟨h,p,a⟩) = (J m ^ (h.val-p.val)) (f h a).1 := by
  apply Basis.constr_basis
theorem ofCoeff_comm (f : Coeff K m) : Commute (ofCoeff m f) (J m) := by
  apply (coordBasis m).ext
  rintro ⟨h,p,a⟩
  change ofCoeff m f (J m (coordBasis m ⟨h,p,a⟩)) =
    J m (ofCoeff m f (coordBasis m ⟨h,p,a⟩))
  rw [coeff_at,← gen_level]
  have step (k : ℕ) (v : V K m) : J m ((J m ^ k) v) = (J m ^ (k+1)) v := by
    rw [pow_succ',Module.End.mul_apply]
  rw [step,step]
  by_cases hp : p.val=0
  · rw [hp,Nat.sub_zero,gen_killed,map_zero]
    exact (f h a).2.symm
  · let q : Fin (h.val+1) := ⟨p.val-1,by have := p.isLt; omega⟩
    have hq : h.val-p.val+1 = h.val-q.val := by dsimp [q]; have := p.isLt; omega
    rw [hq,gen_level,coeff_at]
def coeffOf (z : Cent (K:=K) m) : Coeff K m :=
  fun h a => ⟨z.1 (gen m h a),by
    change (J m ^ (h.val+1)) (z.1 (gen m h a)) = 0
    have he := congrArg (fun g : Module.End K (V K m) => g (gen m h a))
      ((commJ m z).pow_right (h.val+1)).eq.symm
    simpa [Module.End.mul_apply,gen_killed] using he⟩
def toCent (f : Coeff K m) : Cent (K:=K) m := ⟨ofCoeff m f,by
  apply (Subalgebra.mem_centralizer_iff K).mpr
  rintro _ ⟨rfl⟩
  exact (ofCoeff_comm m f).eq.symm⟩
def coefficientEquiv : Cent (K:=K) m ≃ₗ[K] Coeff K m where
  toFun := coeffOf m
  invFun := toCent m
  left_inv z := by
    apply Subtype.ext
    apply (coordBasis m).ext
    rintro ⟨h,p,a⟩
    change ofCoeff m (coeffOf m z) (coordBasis m ⟨h,p,a⟩) =
      z.1 (coordBasis m ⟨h,p,a⟩)
    rw [coeff_at,← gen_level]
    exact congrArg (fun g : Module.End K (V K m) => g (gen m h a))
      ((commJ m z).pow_right _).eq.symm
  right_inv f := by
    funext h a
    apply Subtype.ext
    change ofCoeff m f (coordBasis m ⟨h,Fin.last h.val,a⟩) = (f h a).1
    simp [coeff_at]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
def kernelCoordinates (k : ℕ) : LinearMap.ker (J (K:=K) m ^ k) ≃ₗ[K]
    ((h : Fin H) → Fin (min k (h.val+1)) → Fin (m h) → K) where
  toFun v h j := v.1 h ⟨j.val,lt_of_lt_of_le j.isLt (min_le_right _ _)⟩
  invFun w := ⟨fun h j => if hj : j.val < k then w h ⟨j.val,lt_min hj j.isLt⟩ else 0,by
    change (J m ^ k) _ = 0
    funext h j
    rw [Jpow]
    split_ifs with hc he
    · change j.val+k < k at he
      omega
    · rfl
    · rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext h j
    by_cases hc : j.val < k
    · simp [hc]
    · have hk : k ≤ j.val := Nat.le_of_not_gt hc
      let p : Fin (h.val+1) := ⟨j.val-k,by have := j.isLt; omega⟩
      have hp : p.val+k = j.val := Nat.sub_add_cancel hk
      have hv : (J m ^ k) v.1 = 0 := v.2
      have he := congrFun (congrFun hv h) p
      rw [Jpow] at he
      simpa [hc,hp,j.isLt] using he.symm
  right_inv w := by funext h j; simp [lt_of_lt_of_le j.isLt (min_le_left _ _)]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem kernel_dimension (k : ℕ) : finrank K (LinearMap.ker (J (K:=K) m ^ k)) =
      ∑ h, min k (h.val+1) * m h := by
  rw [(kernelCoordinates (K:=K) m k).finrank_eq,finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [finrank_pi_fintype]
  simp
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
theorem centralizer_dimension : finrank K (Cent (K:=K) m) =
    ∑ h, m h * (∑ l, min (h.val+1) (l.val+1) * m l) := by
  rw [(coefficientEquiv (K:=K) m).finrank_eq]
  change finrank K ((h : Fin H) → Fin (m h) → LinearMap.ker (J (K:=K) m ^ (h.val+1))) = _
  rw [finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [finrank_pi_fintype]
  simp [kernel_dimension]
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
abbrev FreeIx := (h : Fin H) × (Fin (m h) × ((l : Fin H) ×
  (Fin (min (h.val+1) (l.val+1)) × Fin (m l))))
abbrev BlockIx := (h : Fin H) × (Fin (m h) × Fin (m h))
def slot (i : BlockIx m) : FreeIx m :=
  ⟨i.1,i.2.1,i.1,⟨i.1.val,by simp⟩,i.2.2⟩
theorem slot_inj : Function.Injective (slot m) := by
  rintro ⟨h,a,b⟩ ⟨l,c,d⟩ he
  cases he
  rfl
def coeff (z : Cent (K:=K) m) (i : FreeIx m) : K :=
  z.1 (gen m i.1 i.2.1) i.2.2.1
    ⟨i.2.2.2.1.val,lt_of_lt_of_le i.2.2.2.1.isLt (min_le_right _ _)⟩ i.2.2.2.2
theorem actual_entry (z : Cent (K:=K) m)
    (h l : Fin H) (a : Fin (m h)) (b : Fin (m l))
    (p : Fin (h.val+1)) (q : Fin (l.val+1)) :
    LinearMap.toMatrixAlgEquiv (coordBasis m) z.1 ⟨l,q,b⟩ ⟨h,p,a⟩ =
    if hj : q.val+(h.val-p.val) < min (h.val+1) (l.val+1)
    then coeff m z ⟨h,a,l,⟨q.val+(h.val-p.val),hj⟩,b⟩ else 0 := by
  rw [LinearMap.toMatrixAlgEquiv_apply,coord_repr,← gen_level]
  have hc := congrArg (fun g : Module.End K (V K m) => g (gen m h a))
      ((commJ m z).pow_right (h.val-p.val)).eq
  rw [show z.1 ((J m ^ (h.val-p.val)) (gen m h a)) =
     (J m ^ (h.val-p.val)) (z.1 (gen m h a)) from hc,Jpow]
  by_cases h₁ : q.val + (h.val - p.val) < min (h.val+1) (l.val+1)
  · rw [dif_pos (lt_min_iff.mp h₁).2,dif_pos h₁]
    rfl
  · rw [dif_neg h₁]
    split_ifs with ht
    · let k : Fin (l.val+1) := ⟨q.val + (h.val-p.val),ht⟩
      have hk : h.val+1 ≤ k.val := by dsimp [k]; rw [lt_min_iff] at h₁; omega
      let j : Fin (l.val+1) := ⟨k.val-(h.val+1),by have := k.isLt; omega⟩
      have hh : j.val+(h.val+1)=k.val := Nat.sub_add_cancel hk
      have he : (J m ^ (h.val+1)) (z.1 (gen m h a))=0 := (coeffOf m z h a).2
      have hs := congrFun (congrFun (congrFun he l) j) b
      rw [Jpow] at hs
      simpa [hh,k.isLt] using hs
    · rfl
theorem coeff_slot (z : Cent (K:=K) m) (i : BlockIx m) :
    coeff m z (slot m i) =
      rawBlock m (LinearMap.toMatrixAlgEquiv (coordBasis m) z.1) i.1 i.2.2 i.2.1 := by
  rcases i with ⟨h,a,b⟩
  change _ = LinearMap.toMatrixAlgEquiv (coordBasis m) z.1 ⟨h,0,b⟩ ⟨h,0,a⟩
  rw [actual_entry]
  simp [coeff,slot]
abbrev Residual := {i : FreeIx m // i ∉ Set.range (slot m)}
theorem entries_from_residual_and_blocks (Z : Matrix (Ix m) (Ix m) K)
    (hZ : Commute Z (matrixJ m)) (S : Set K) (h0 : 0 ∈ S)
    (hf : ∀ i : Residual m, coeff m (decode m Z hZ) i.1 ∈ S)
    (hb : ∀ (h : Fin H) (a b : Fin (m h)), rawBlock m Z h a b ∈ S) :
    ∀ i j, Z i j ∈ S := by
  let z := decode m Z hZ
  have hcoeff (i : FreeIx m) : coeff m z i ∈ S := by
    by_cases he : i ∈ Set.range (slot m)
    · obtain ⟨u,rfl⟩ := he
      rw [coeff_slot,show (LinearMap.toMatrixAlgEquiv (coordBasis m)) z.1= Z from encode_decode m Z hZ]
      exact hb _ _ _
    · exact hf ⟨i,he⟩
  rintro ⟨l,q,b⟩ ⟨h,p,a⟩
  rw [← encode_decode m Z hZ]
  rw [actual_entry]
  split <;> first | exact hcoeff _ | exact h0
theorem residual_card :
    Nat.card (Residual m) = finrank K (Cent (K:=K) m) - ∑ h, m h ^ 2 := by
  classical
  rw [Nat.card_eq_fintype_card,centralizer_dimension]
  change Fintype.card ((Set.range (slot m))ᶜ : Set (FreeIx m)) = _
  rw [Fintype.card_compl_set,Set.card_range_of_injective (slot_inj m)]
  simp [FreeIx,BlockIx,Fintype.card_sigma,pow_two]
theorem literal_parameter_list (Z : Matrix (Ix m) (Ix m) K) (hZ : Commute Z (matrixJ m)) :
    ∃ f : Fin (finrank K (Cent (K:=K) m) - ∑ h, m h ^ 2) → K,
      ∀ S : Set K, 0 ∈ S → (∀ i, f i ∈ S) →
      (∀ (h : Fin H) (a b : Fin (m h)), rawBlock m Z h a b ∈ S) →
      ∀ i j, Z i j ∈ S := by
  classical
  let e := Fintype.equivFinOfCardEq (α:=Residual m) (by
    simpa only [Nat.card_eq_fintype_card] using residual_card (K:=K) m)
  refine ⟨fun i => coeff m (decode m Z hZ) (e.symm i).1,?_⟩
  intro S h0 hf hb
  apply entries_from_residual_and_blocks m Z hZ S h0 _ hb
  intro i
  simpa using hf (e i)
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {k K : Type*} [Field k] [Field K] [Algebra k K] {H : ℕ} (m : Fin H → ℕ)
def FieldParams {I : Type*} (Z : Matrix I I K) (n : ℕ) : Prop :=
  ∃ w : Fin n → K, ∀ S : IntermediateField k K, (∀ i, w i ∈ S) → ∀ i j, Z i j ∈ S
theorem fixed_shape_budget_of_single_matrix
    (hsingle : ∀ (n : ℕ) (Q : Matrix (Fin n) (Fin n) K),
      IsNilpotent Q → FieldParams (k:=k) Q (n^2-n))
    (Z : Matrix (Ix m) (Ix m) K) (hZ : Commute Z (matrixJ m)) (hn : IsNilpotent Z) :
    FieldParams (k:=k) Z (finrank K (Cent (K:=K) m) - ∑ h, m h) := by
  classical
  obtain ⟨u,hu⟩ := literal_parameter_list m Z hZ
  have hblock := (matrix_block_nilpotent_iff m Z hZ).mp hn
  choose w hw using fun h => hsingle (m h) (rawBlock m Z h) (hblock h)
  let c := finrank K (Cent (K:=K) m)
  let I := Fin (c - ∑ h, m h ^ 2) ⊕ ((h : Fin H) × Fin ((m h)^2 - m h))
  have hm (h : Fin H) : m h ≤ m h ^ 2 := by
    by_cases hv : m h = 0
    · simp [hv]
    · have hp : 0 < m h := Nat.pos_of_ne_zero hv; nlinarith
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hm i)
  have hc := primitive_rank_nullity (K:=K) m
  have hI : Fintype.card I = c - ∑ h, m h := by
    simp only [I,Fintype.card_sum,Fintype.card_fin,Fintype.card_sigma]
    rw [Finset.sum_tsub_distrib _ (fun h _ => hm h)]
    dsimp [c]; omega
  let e : I ≃ Fin (c - ∑ h, m h) := Fintype.equivFinOfCardEq hI
  let raw : I → K := Sum.elim u (fun t => w t.1 t.2)
  refine ⟨fun i => raw (e.symm i),?_⟩
  intro S hS
  have hall (i : I) : raw i ∈ S := by simpa using hS (e i)
  apply hu S S.zero_mem (fun i => hall (Sum.inl i))
  intro h
  apply hw h S
  intro i
  exact hall (Sum.inr ⟨h,i⟩)
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
def socEmbed : ((h : Fin H) → Fin (m h) → K) →ₗ[K] V K m :=
  LinearMap.pi (fun h => (LinearMap.single K (fun _ : Fin (h.val+1) => Fin (m h) → K) 0).comp
    (LinearMap.proj h))
def ker_equiv : (LinearMap.ker (J (K:=K) m)) ≃ₗ[K] ((h : Fin H) → Fin (m h) → K) where
  toFun v h := v.1 h 0
  invFun w := ⟨socEmbed m w,by
    change J m (socEmbed m w) = 0
    apply ((fl_iff m 0 _).mp _).1
    intro h j hj
    have hj' : j ≠ 0 := fun e => by subst j; simp at hj
    simp [socEmbed,Pi.single_eq_of_ne hj']⟩
  left_inv v := by
    apply Subtype.ext
    funext h j
    by_cases hz : j=0
    · subst j; simp [socEmbed]
    · have hc := (fl_iff m 0 v.1).mpr ⟨v.2,v.1,by simp⟩
      have he := hc h j (Or.inl (fun e => hz (Fin.ext e)))
      simp [socEmbed,Pi.single_eq_of_ne hz,he]
  right_inv w := by funext h; simp [socEmbed]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem number_of_blocks_is_nullity :
    finrank K (LinearMap.ker (J (K:=K) m)) = ∑ h, m h := by
  rw [(ker_equiv (K:=K) m).finrank_eq,finrank_pi_fintype]
  simp
theorem total_dimension :
    finrank K (V K m) = ∑ h, (h.val+1)*m h := by
  change finrank K ((h : Fin H) → Fin (h.val+1) → (Fin (m h) → K)) = _
  rw [finrank_pi_fintype]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [finrank_pi_fintype]
  simp
end JordanPrimitive
end
noncomputable section
namespace JordanPrimitive
open Module
variable {K : Type*} [Field K] {H : ℕ} (m : Fin H → ℕ)
theorem total_le_centralizer : finrank K (V K m) ≤ finrank K (Cent (K:=K) m) := by
  rw [total_dimension,centralizer_dimension]
  apply Finset.sum_le_sum
  intro h _
  have hh := Finset.single_le_sum (s:=Finset.univ)
    (f:=fun l : Fin H => min (h.val+1) (l.val+1) * m l)
    (fun l _ => Nat.zero_le _) (Finset.mem_univ h)
  simp only [min_self] at hh
  by_cases hz : m h = 0
  · simp [hz]
  · have hp : 1 ≤ m h := Nat.one_le_iff_ne_zero.mpr hz
    calc
      (h.val+1)*m h ≤ 1 * ∑ l, min (h.val+1) (l.val+1) * m l := by simpa using hh
      _ ≤ _ := Nat.mul_le_mul_right _ hp
end JordanPrimitive
end
noncomputable section
namespace GKGauge
open JordanPrimitive Module Matrix Finset
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F] {d : ℕ} (m : Fin d → ℕ)
set_option maxHeartbeats 45000 in
def jCentEquiv :
    Cent (K:=F) m ≃ₗ[F] intertwiner (matrixJ (K:=F) m) (matrixJ m) where
  toFun a := ⟨LinearMap.toMatrixAlgEquiv (coordBasis m) a.val,
    ((commJ m a).map (LinearMap.toMatrixAlgEquiv (coordBasis m)).toAlgHom).eq.symm⟩
  invFun a := decode m a.val (show Commute a.val (matrixJ m) from a.property.symm)
  left_inv a := by apply Subtype.ext; exact AlgEquiv.symm_apply_apply _ _
  right_inv a := by apply Subtype.ext; exact encode_decode m a.val _
  map_add' a b := by apply Subtype.ext; exact (LinearMap.toMatrixAlgEquiv (coordBasis (K:=F) m)).map_add a.val b.val
  map_smul' t a := by apply Subtype.ext; exact (LinearMap.toMatrixAlgEquiv (coordBasis (K:=F) m)).toLinearEquiv.map_smul t a.val
set_option maxHeartbeats 45000 in
omit [Infinite k] in
theorem jordan_entries_base : ∀ i j, (matrixJ (K:=F) m) i j ∈ (algebraMap k F).range := by
  rintro ⟨h,p,a⟩ ⟨l,q,b⟩
  by_cases he : h=l
  · subst l; rw [matrixJ_apply]; split
    · exact (algebraMap k F).range.one_mem
    · exact (algebraMap k F).range.zero_mem
  · rw [matrixJ_other m h l p q a b he]
    exact (algebraMap k F).range.zero_mem
set_option maxHeartbeats 45000 in
theorem count_le_c : Fintype.card (Ix m) ≤ finrank F (Cent (K:=F) m) := by
  rw [← Module.finrank_eq_card_basis (coordBasis (K:=F) m)]
  exact total_le_centralizer m
set_option maxHeartbeats 45000 in
theorem single_given_shape (A : Matrix (Ix m) (Ix m) F)
    (h : ∃ H : Matrix _ _ F, H.det ≠ 0 ∧ A*H=H*matrixJ m) :
    FieldParams (k:=k) A ((Fintype.card (Ix m))^2-Fintype.card (Ix m)) := by
  obtain ⟨s,H,hs,_,_,_,hA⟩ := orbit_parameters A _ h (jordan_entries_base (k:=k) m)
  rw [← (jCentEquiv (F:=F) m).finrank_eq,←pow_two] at hs
  have hN := count_le_c (F:=F) m
  obtain ⟨w,hw⟩ := finset_to_list (k:=k) s _ (hs.trans (Nat.sub_le_sub_left hN _))
  exact ⟨w,fun L hi i j => hw L hi (hA i j)⟩
end GKGauge
end
noncomputable section
namespace GKGauge
open JordanPrimitive Module Matrix Finset
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F] {d : ℕ} (m : Fin d → ℕ)
theorem pair_given_shape (hsingle : ∀ (a : ℕ) (Q : Matrix (Fin a) (Fin a) F),
      IsNilpotent Q → FieldParams (k:=k) Q (a^2-a))
    (A B : Matrix (Ix m) (Ix m) F)
    (hc : Commute A B) (hB : IsNilpotent B)
    (hg : ∃ E : Matrix _ _ F, E.det ≠ 0 ∧ A*E=E*matrixJ m) :
    ∃ u : Finset F, u.card ≤ Fintype.card (Ix m)^2-∑ h, m h ∧
      (∀ i j, A i j ∈ IntermediateField.adjoin k (u : Set F)) ∧
      (∀ i j, B i j ∈ IntermediateField.adjoin k (u : Set F)) := by
  classical
  obtain ⟨s,H,hs,hdet,he,hH,hA⟩ := orbit_parameters A _ hg (jordan_entries_base (k:=k) m)
  have h1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hdet)
  have h2 := Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hdet)
  let Z := H⁻¹ * B * H
  have hb : B * H = H * Z := by
    dsimp [Z]; simp only [←mul_assoc,h2,one_mul]
  have hj : matrixJ (K:=F) m = H⁻¹ * A * H := by
    rw [mul_assoc,he,←mul_assoc,h1,one_mul]
  have clean (X Y : Matrix (Ix m) (Ix m) F) :
      H⁻¹ * X * H * (H⁻¹ * Y * H) = H⁻¹ * (X*Y) * H := by
    calc
      _ = (H⁻¹ * X) * (H*H⁻¹) * Y * H := by simp only [mul_assoc]
      _ = _ := by rw [h2,mul_one]; simp only [mul_assoc]
  have hcomm : Commute Z (matrixJ m) := by
    rw [hj]; change H⁻¹ * B * H * (H⁻¹ * A * H) = H⁻¹ * A * H * (H⁻¹ * B * H)
    calc
      _ = H⁻¹ * (B*A) * H := by rw [clean]
      _ = H⁻¹ * (A*B) * H := by rw [hc.eq]
      _ = _ := by rw [clean]
  have hnil : IsNilpotent Z := by
    obtain ⟨t,ht⟩ := hB
    have hgpow (n : ℕ) : Z^n = H⁻¹*B^n*H := by
      induction n with
      | zero => simp [h1]
      | succ n ih =>
        rw [pow_succ,pow_succ,ih]; dsimp [Z]
        exact clean _ _
    exact ⟨t,by simp [hgpow,ht]⟩
  obtain ⟨w,hw⟩ := fixed_shape_budget_of_single_matrix (k:=k) m hsingle Z hcomm hnil
  let v := Finset.univ.image w
  let u := s ∪ v
  let L := IntermediateField.adjoin k (u : Set F)
  have hsL : IntermediateField.adjoin k (s : Set F) ≤ L :=
    IntermediateField.adjoin_le_iff.mpr (fun x hx => IntermediateField.subset_adjoin k _ (Finset.mem_union_left _ hx))
  have hZL := hw L (fun i => IntermediateField.subset_adjoin k _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)))
  refine ⟨u,?_,fun i j => hsL (hA i j),recovery_mem L B H Z (fun i j => hsL (hH i j)) hZL hdet hb⟩
  have hvc : v.card ≤ finrank F (Cent (K:=F) m) - ∑ h, m h := by
    simpa [v] using (Finset.card_image_le (s:=Finset.univ) (f:=w))
  have hc1 : finrank F (Cent (K:=F) m) ≤ Fintype.card (Ix m)^2 := by
    rw [(jCentEquiv (F:=F) m).finrank_eq]
    apply le_trans (Submodule.finrank_le _)
    simp [Module.finrank_matrix,pow_two]
  have hc2 : (∑ h, m h) ≤ finrank F (Cent (K:=F) m) := by
    have he := primitive_rank_nullity (K:=F) m
    have hb' : (∑ h, m h) ≤ ∑ h, m h^2 := by
      apply Finset.sum_le_sum; intro i _; exact Nat.le_self_pow (by decide) _
    omega
  rw [← (jCentEquiv (F:=F) m).finrank_eq, ←pow_two] at hs
  exact (Finset.card_union_le _ _).trans (by omega)
end GKGauge
end
noncomputable section
namespace GKGauge
open JordanPrimitive Matrix Module
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F]
def JordanModels (F : Type) [Field F] : Prop := ∀ (n : ℕ) (U : Matrix (Fin n) (Fin n) F),
    IsNilpotent U → ∃ (d : ℕ) (m : Fin d → ℕ) (e : Ix m ≃ Fin n) (G : Matrix (Ix m) (Ix m) F),
      IsUnit G ∧ (U.submatrix e e)*G=G*matrixJ m ∧
      finrank F (LinearMap.ker (Matrix.toLinAlgEquiv' U)) = ∑ h, m h
theorem nil_matrix_parameters_of_jordan (JM : JordanModels F) (n : ℕ) (Q : Matrix (Fin n) (Fin n) F) (hn : IsNilpotent Q) :
    FieldParams (k:=k) Q (n^2-n) := by
  classical
  obtain ⟨d,m,e,G,hG,hI,hker⟩ := JM n Q hn
  have hcard : Fintype.card (Ix m)=n := (Fintype.card_congr e).trans (Fintype.card_fin n)
  have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  have hp := single_given_shape (k:=k) m _ ⟨G,hd,hI⟩
  rw [hcard] at hp
  obtain ⟨w,hw⟩ := hp
  refine ⟨w,?_⟩
  intro L h i j
  have hh := hw L h (e.symm i) (e.symm j)
  simpa [Matrix.submatrix_apply] using hh
theorem subregular_pair_parameters_of_jordan (JM : JordanModels F) {n : ℕ} (U V : Matrix (Fin n) (Fin n) F)
    (h : Commute U V) (hn : IsNilpotent U) (hz : IsNilpotent V)
    (hk : 2 ≤ finrank F U.mulVecLin.ker) :
    ∃ s : Finset F, s.card ≤ n*n-2 ∧
      (∀ i j, U i j ∈ IntermediateField.adjoin k (s : Set F)) ∧
      (∀ i j, V i j ∈ IntermediateField.adjoin k (s : Set F)) := by
  classical
  obtain ⟨d,m,e,G,hG,hI,hker⟩ := JM n U hn
  let f := Matrix.reindexAlgEquiv F F e.symm
  have hu (M : Matrix _ _ F) : f M = M.submatrix e e := rfl
  have hC := h.map f.toAlgHom
  have hN := hz.map f.toAlgHom
  change Commute (f U) (f V) at hC
  change IsNilpotent (f V) at hN
  rw [hu,hu] at hC
  rw [hu] at hN
  obtain ⟨s,hs,hU,hV⟩ := pair_given_shape (k:=k) m (nil_matrix_parameters_of_jordan (k:=k) JM) _ _ hC hN
    ⟨G,isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG),hI⟩
  have hcard : Fintype.card (Ix m)=n := (Fintype.card_congr e).trans (Fintype.card_fin n)
  rw [hcard,pow_two] at hs
  change 2 ≤ finrank F (Matrix.toLinAlgEquiv' U).ker at hk
  rw [hker] at hk
  refine ⟨s,hs.trans (Nat.sub_le_sub_left hk _),?_,?_⟩
  · intro i j; simpa [Matrix.submatrix_apply] using hU (e.symm i) (e.symm j)
  · intro i j; simpa [Matrix.submatrix_apply] using hV (e.symm i) (e.symm j)
end GKGauge
end
noncomputable section
open Module Polynomial
open scoped DirectSum
namespace ActualJordan
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
abbrev Tr (K : Type*) [Field K] (l : ℕ) := AdjoinRoot ((X : K[X])^l)
theorem exists_truncated_model (T : Module.End K M) (hn : IsNilpotent T) :
    ∃ (d : ℕ) (s : Fin d → ℕ) (e : M ≃ₗ[K] ((i : Fin d) → Tr K (s i))),
      ∀ (v : M) (i : Fin d), e (T v) i = AdjoinRoot.root ((X : K[X])^(s i)) * e v i := by
  classical
  have ht : Module.IsTorsion' (Module.AEval' T) (Submonoid.powers (X : K[X])) := by
    apply (Submodule.isTorsion'_powers_iff _).mpr
    obtain ⟨k,hk⟩ := hn
    intro v
    obtain ⟨v,rfl⟩ := (Module.AEval'.of T).surjective v
    exact ⟨k,by rw [Module.AEval'.X_pow_smul_of,hk,zero_smul,map_zero]⟩
  obtain ⟨d,s,⟨a⟩⟩ := Module.torsion_by_prime_power_decomposition
    (M:=Module.AEval' T) (Polynomial.irreducible_X (R:=K)) ht
  let f := a.trans (DFinsupp.linearEquivFunOnFintype)
  let e := (Module.AEval'.of T).trans (f.restrictScalars K)
  refine ⟨d,s,e,?_⟩
  intro v i
  change f (Module.AEval'.of T (T v)) i = _
  rw [← Module.AEval'.X_smul_of,map_smul]
  rfl
end ActualJordan
end
noncomputable section
namespace ActualJordan
abbrev GroupIx {H : ℕ} (m : Fin H → ℕ) := (h : Fin H) × ((_p : Fin (h.val+1)) × Fin (m h))
variable {d : ℕ} (s : Fin d → ℕ)
def height := ∑ i, s i
abbrev Fiber (h : Fin (height s)) := {i : Fin d // s i=h.val+1}
def multiplicity (h : Fin (height s)) := Fintype.card (Fiber s h)
def pick (h : Fin (height s)) (a : Fin (multiplicity s h)) : Fiber s h :=
  (Fintype.equivFin (Fiber s h)).symm a
abbrev Uix := (i : Fin d) × Fin (s i)
def toPowerIx : GroupIx (multiplicity s) → Uix s :=
  fun ⟨h,p,a⟩ => ⟨(pick s h a).val, Fin.cast (pick s h a).2.symm p.rev⟩
theorem toPower_inj : Function.Injective (toPowerIx s) := by
  rintro ⟨h,p,a⟩ ⟨l,q,b⟩ he
  have hi : (pick s h a).val = (pick s l b).val := congrArg Sigma.fst he
  have hil := congrArg s hi
  rw [(pick s h a).2,(pick s l b).2] at hil
  have hhl : h=l := Fin.ext (by omega)
  subst l
  have hab : a=b := (Fintype.equivFin (Fiber s h)).symm.injective (Subtype.ext hi)
  subst b
  have hpq : p.rev.val = q.rev.val := congrArg (fun x : Uix s => x.2.val) he
  have : p = q := Fin.rev_injective (Fin.ext hpq)
  subst q; rfl
private theorem cast_h {n k : ℕ} (e : n=k) (i : Fin n) : HEq (Fin.cast e i) i := by cases e; rfl
theorem powerIx_surj : Function.Surjective (toPowerIx s) := by
  rintro ⟨i,j⟩
  have hs : 0 < s i := Nat.zero_lt_of_lt j.isLt
  have hmax := Finset.single_le_sum (s:=Finset.univ)
    (f:=s) (fun l _ => Nat.zero_le _) (Finset.mem_univ i)
  let h : Fin (height s) := ⟨s i-1,by unfold height; omega⟩
  have hh : s i = h.val+1 := by dsimp [h]; omega
  let a := (Fintype.equivFin (Fiber s h)) ⟨i,hh⟩
  let p := (Fin.cast hh j).rev
  have ha : pick s h a = ⟨i,hh⟩ := (Fintype.equivFin (Fiber s h)).symm_apply_apply _
  refine ⟨⟨h,p,a⟩,?_⟩
  unfold toPowerIx
  simp [ha,p]
  exact cast_h _ _
def powerEquiv : GroupIx (multiplicity s) ≃ Uix s :=
  Equiv.ofBijective _ ⟨toPower_inj s,powerIx_surj s⟩
end ActualJordan
end
noncomputable section
open Module Polynomial JordanPrimitive
namespace ActualJordan
variable {K : Type*} [Field K] {d : ℕ} (s : Fin d → ℕ)
set_option maxHeartbeats 110000 in
def rt (n : ℕ) : Tr K n := AdjoinRoot.root ((X : K[X])^n)
set_option maxHeartbeats 110000 in
theorem rt_pow (n : ℕ) : (rt (K:=K) n)^n = 0 := by
  simpa [rt,Polynomial.eval₂_pow,Polynomial.eval₂_X] using AdjoinRoot.eval₂_root ((X : K[X])^n)
set_option maxHeartbeats 110000 in
def tb (n : ℕ) : Basis (Fin n) K (Tr K n) :=
  let pb := AdjoinRoot.powerBasis' ((Polynomial.monic_X : (X : K[X]).Monic).pow n)
  pb.basis.reindex (finCongr (by simp [pb]))
set_option maxHeartbeats 110000 in
theorem tb_pow (n : ℕ) (j : Fin n) : tb (K:=K) n j = (rt n)^j.val := by
  rw [tb,Basis.reindex_apply,PowerBasis.basis_eq_pow]; rfl
set_option maxHeartbeats 110000 in
def productBasis : Basis (Uix s) K ((i : Fin d) → Tr K (s i)) :=
  Pi.basis (fun i => tb (s i))
set_option maxHeartbeats 110000 in
def groupedToProduct : V K (multiplicity s) ≃ₗ[K] ((i : Fin d) → Tr K (s i)) :=
  (coordBasis (K:=K) (multiplicity s)).equiv (productBasis s) (powerEquiv s)
set_option maxHeartbeats 110000 in
theorem grouped_basis_value (h : Fin (height s)) (p : Fin (h.val+1)) (a : Fin (multiplicity s h)) :
    groupedToProduct (K:=K) s (coordBasis _ ⟨h,p,a⟩) =
      Pi.single (pick s h a).val ((rt (s (pick s h a).val))^(h.val-p.val)) := by
  rw [groupedToProduct,Basis.equiv_apply,productBasis,Pi.basis_apply,tb_pow]
  congr 2
  change p.rev.val = h.val - p.val
  rw [Fin.val_rev]
  omega
set_option maxHeartbeats 110000 in
def timesRoot : Module.End K ((i : Fin d) → Tr K (s i)) where
  toFun v i := rt (s i) * v i
  map_add' v w := by funext i; exact mul_add _ _ _
  map_smul' u v := by
    funext i
    change rt (s i) * (u • v i) = u • (rt (s i) * v i)
    exact Algebra.mul_smul_comm u (rt (s i)) (v i)
set_option maxHeartbeats 110000 in
theorem root_single (i : Fin d) (u : Tr K (s i)) :
    timesRoot s (Pi.single i u) = Pi.single i (rt _ * u) := by
  funext j
  change rt (s j) * (Pi.single i u : (l : Fin d) → Tr K (s l)) j = _
  by_cases hj : j=i
  · subst j; simp
  · simp [Pi.single_eq_of_ne hj]
set_option maxHeartbeats 110000 in
theorem shift_basis {N : ℕ} (m : Fin N → ℕ) (h : Fin N)
    (p : Fin (h.val+1)) (a : Fin (m h)) :
    J (K:=K) m (coordBasis m ⟨h,p,a⟩) =
      if hp : p.val = 0 then 0 else
        coordBasis m ⟨h,⟨p.val-1,by have := p.isLt; omega⟩,a⟩ := by
  rw [← gen_level (K:=K) m h p a]
  change ((J (K:=K) m * J (K:=K) m ^ (h.val-p.val)) (gen (K:=K) m h a)) = _
  rw [← pow_succ']
  split_ifs with hp
  · rw [hp,Nat.sub_zero,gen_killed]
  · let q : Fin (h.val+1) := ⟨p.val-1,by have := p.isLt; omega⟩
    have hq : h.val-p.val+1 = h.val-q.val := by dsimp [q]; have := p.isLt; omega
    rw [hq,gen_level]
set_option maxHeartbeats 110000 in
theorem grouped_on_basis (h : Fin (height s)) (p : Fin (h.val+1)) (a : Fin (multiplicity s h)) :
    groupedToProduct (K:=K) s (J (multiplicity s) (coordBasis (multiplicity s) ⟨h,p,a⟩)) =
    timesRoot (K:=K) s (groupedToProduct (K:=K) s (coordBasis (multiplicity s) ⟨h,p,a⟩)) := by
  rw [grouped_basis_value s h p a,root_single,← pow_succ' (rt (K:=K) (s (pick s h a).val)) _]
  rw [shift_basis]
  split_ifs with hp
  · have hz : (rt (K:=K) (s (pick s h a).val))^(h.val+1) = 0 := by
      simpa only [(pick s h a).2] using rt_pow (K:=K) (s (pick s h a).val)
    rw [hp,Nat.sub_zero,map_zero,hz,Pi.single_zero]
  · rw [grouped_basis_value]
    have hq : h.val-(p.val-1)=h.val-p.val+1 := by have := p.isLt; omega
    exact congrArg (fun n : ℕ => (Pi.single (pick s h a).val ((rt (K:=K) (s (pick s h a).val))^n) : (i : Fin d) → Tr K (s i))) hq
set_option maxHeartbeats 110000 in
theorem grouped_intertwine : (groupedToProduct (K:=K) s).toLinearMap.comp (J (multiplicity s)) =
    (timesRoot (K:=K) s).comp (groupedToProduct (K:=K) s).toLinearMap := by
  exact (coordBasis (K:=K) (multiplicity s)).ext fun ⟨h,p,a⟩ => grouped_on_basis (K:=K) s h p a
variable {M : Type*} [AddCommGroup M] [Module K M] [Module.Finite K M]
set_option maxHeartbeats 110000 in
theorem exists_grouped (T : Module.End K M) (hn : IsNilpotent T) :
    ∃ (H : ℕ) (m : Fin H → ℕ) (e : V K m ≃ₗ[K] M), ∀ v, T (e v) = e (J m v) := by
  obtain ⟨d,s,f,hf⟩ := exists_truncated_model T hn
  refine ⟨height s,multiplicity s,(groupedToProduct s).trans f.symm,?_⟩
  intro v
  apply f.injective
  change f (T (f.symm (groupedToProduct s v))) = f (f.symm (groupedToProduct s (J _ v)))
  rw [f.apply_symm_apply]
  have he := congrArg (fun g => (g : V K (multiplicity s) →ₗ[K] ((i : Fin d) → Tr K (s i))) v)
    (grouped_intertwine (K:=K) s)
  funext i
  rw [hf,f.apply_symm_apply]
  exact (congrFun he i).symm
end ActualJordan
end
noncomputable section
open Module Matrix JordanPrimitive
namespace ActualJordan
variable {K : Type*} [Field K] {n : ℕ}
theorem matrix_from_linear_model (U : Matrix (Fin n) (Fin n) K)
    {H : ℕ} (m : Fin H → ℕ) (a : V K m ≃ₗ[K] (Fin n → K))
    (ha : ∀ v, Matrix.toLinAlgEquiv' U (a v) = a (J m v)) :
    ∃ (e : Ix m ≃ Fin n)
      (G : Matrix (Ix m) (Ix m) K),
      IsUnit G ∧ (U.submatrix e e) * G = G * matrixJ m := by
  classical
  let T : Module.End K (Fin n → K) := Matrix.toLinAlgEquiv' U
  have hc : Fintype.card (Ix m) = n := by
    rw [← Module.finrank_eq_card_basis (coordBasis (K:=K) m),a.finrank_eq]
    simp
  let e : Ix m ≃ Fin n := Fintype.equivFinOfCardEq hc
  let b := (Pi.basisFun K (Fin n)).reindex e.symm
  let v := coordBasis (K:=K) m
  let G := LinearMap.toMatrix v b a.toLinearMap
  let D := LinearMap.toMatrix b v a.symm.toLinearMap
  have hGD : G*D=1 := by
    dsimp [G,D]
    rw [← LinearMap.toMatrix_comp]
    simp
  have hDG : D*G=1 := by
    dsimp [G,D]
    rw [← LinearMap.toMatrix_comp]
    simp
  have hU : LinearMap.toMatrix b b T = U.submatrix e e := by
    ext i j
    simp [LinearMap.toMatrix_apply,b,Basis.reindex_apply,
      T,Matrix.toLinAlgEquiv'_apply,Pi.basisFun_apply,Pi.basisFun_repr]
  refine ⟨e,G,⟨⟨G,D,hGD,hDG⟩,rfl⟩,?_⟩
  have he : T.comp a.toLinearMap = a.toLinearMap.comp (J m) := LinearMap.ext ha
  have hm := congrArg (LinearMap.toMatrix v b) he
  rw [LinearMap.toMatrix_comp v b b,LinearMap.toMatrix_comp v v b,hU] at hm
  exact hm
end ActualJordan
end
noncomputable section
open Module Matrix JordanPrimitive
namespace ActualJordan
variable {K : Type*} [Field K] {n : ℕ}
end ActualJordan
end
noncomputable section
open Module Matrix JordanPrimitive
namespace ActualJordan
variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] {H : ℕ} (m : Fin H → ℕ)
def identifiedKernel (T : Module.End K M) (a : V K m ≃ₗ[K] M)
    (ha : ∀ v, T (a v) = a (J m v)) : LinearMap.ker (J (K:=K) m) ≃ₗ[K] LinearMap.ker T where
  toFun x := ⟨a x.1,by change T _=0; rw [ha,x.2,map_zero]⟩
  invFun x := ⟨a.symm x,by
    apply a.injective
    change a ((J m) (a.symm _)) = a 0
    rw [← ha,a.apply_symm_apply,x.2,map_zero]⟩
  left_inv x := Subtype.ext (a.symm_apply_apply _)
  right_inv x := Subtype.ext (a.apply_symm_apply _)
  map_add' x y := Subtype.ext (a.map_add _ _)
  map_smul' x y := Subtype.ext (a.map_smul _ _)
variable {n : ℕ}
theorem exists_matrix_jordan_with_nullity (U : Matrix (Fin n) (Fin n) K) (hn : IsNilpotent U) :
    ∃ (H : ℕ) (m : Fin H → ℕ) (e : Ix m ≃ Fin n) (G : Matrix (Ix m) (Ix m) K),
      IsUnit G ∧ (U.submatrix e e)*G=G*matrixJ m ∧
      finrank K (LinearMap.ker (Matrix.toLinAlgEquiv' U)) = ∑ h, m h := by
  obtain ⟨H,m,a,ha⟩ := exists_grouped (Matrix.toLinAlgEquiv' U) (hn.map Matrix.toLinAlgEquiv')
  obtain ⟨e,G,hG,hi⟩ := matrix_from_linear_model U m a ha
  refine ⟨H,m,e,G,hG,hi,?_⟩
  rw [← (identifiedKernel m _ a ha).finrank_eq]
  exact number_of_blocks_is_nullity m
end ActualJordan
end
noncomputable section
namespace GKGauge
open JordanPrimitive ActualJordan Matrix Module
variable {k F : Type} [Field k] [Infinite k] [Field F] [Algebra k F]
theorem actual_jordan_models (F : Type) [Field F] : JordanModels F :=
  fun _ U h => ActualJordan.exists_matrix_jordan_with_nullity U h
theorem subregular_pair_parameters {n : ℕ} (U V : Matrix (Fin n) (Fin n) F)
    (h : Commute U V) (hn : IsNilpotent U) (hz : IsNilpotent V)
    (hk : 2 ≤ finrank F U.mulVecLin.ker) :
    ∃ s : Finset F, s.card ≤ n*n-2 ∧
      (∀ i j, U i j ∈ IntermediateField.adjoin k (s : Set F)) ∧
      (∀ i j, V i j ∈ IntermediateField.adjoin k (s : Set F)) :=
  subregular_pair_parameters_of_jordan (actual_jordan_models F) U V h hn hz hk
end GKGauge
end
noncomputable section
namespace G3Assembly
open Module GKGraph GKDivisor GKDivisor.Jet GKEnds DVRMinimal
local instance BadPole.instCr9 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : CommRing P.V := P.cr
local instance BadPole.instDom9 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDomain P.V := P.dom
local instance BadPole.instDvr9 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : IsDiscreteValuationRing P.V := P.dvr
local instance BadPole.instAlg9 {k : Type u} [Field k] {r : ℕ} {h : GKGraph.ring k r}
    (P : BadPole k r h) : Algebra k P.V := P.alg
theorem not_actual_witness {k : Type} [Field k] [IsAlgClosed k] {r : ℕ} (W : RealWitness k r)
    (hr : 2≤r) (small : ∀ j<r, SafeEverywhere.{0} j) : False := by
  obtain ⟨h0,a,b,ha,hb⟩ := actual_center_pairs W (by omega) small
  obtain ⟨s,hs,hs1,hs2⟩ := GKGauge.subregular_pair_parameters (k:=k) _ _ ha.comm ha.nilY ha.nilZ ha.width
  obtain ⟨t,ht,ht1,ht2⟩ := GKGauge.subregular_pair_parameters (k:=k) _ _ hb.comm hb.nilY hb.nilZ hb.width
  exact witness_budget_impossible W hr a b s t hs ht h0 hs1 hs2 ht1 ht2
theorem matrix_triple_bound (k : Type) [Field k] [IsAlgClosed k] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) k) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank k (Algebra.adjoin k (Set.range A))≤n := by
  by_contra! bad
  obtain ⟨r,hr,_,small,B,⟨W⟩⟩ := original_matrix_pole k A hc bad
  exact not_actual_witness W hr small
end G3Assembly
end
noncomputable section
namespace G3Scalar
open Module
theorem field_triple_bound (K : Type*) [Field K] (n : ℕ)
    (A : Fin 3 → Matrix (Fin n) (Fin n) K) (hc : ∀ i j, Commute (A i) (A j)) :
    finrank K (Algebra.adjoin K (Set.range A)) ≤ n :=
  field_triple_bound_of_closed G3Assembly.matrix_triple_bound K n A hc
theorem field_three_matrices {K : Type*} [Field K] {n : ℕ}
    (X Y Z : Matrix (Fin n) (Fin n) K) (hxy : Commute X Y) (hxz : Commute X Z)
    (hyz : Commute Y Z) : finrank K (Algebra.adjoin K ({X,Y,Z} : Set _)) ≤ n := by
  let A : Fin 3 → Matrix (Fin n) (Fin n) K := ![X,Y,Z]
  have comm (i j : Fin 3) : Commute (A i) (A j) := by
    fin_cases i <;> fin_cases j <;>
      first | exact Commute.refl _ | exact hxy | exact hxz | exact hyz | exact hxy.symm | exact hxz.symm | exact hyz.symm
  have range : Set.range A = ({X,Y,Z} : Set _) := by
    ext v
    constructor
    · rintro ⟨i,rfl⟩; fin_cases i <;> simp [A]
    · rintro (h|h|h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
      · exact ⟨2,(Set.mem_singleton_iff.mp h).symm⟩
  exact range ▸ field_triple_bound K n A comm
end G3Scalar
end
theorem OMA.solution : type_of% @Gerstenhaber.finrank_adjoin_triple_le := by
  intro K _ n A B C h
  have comm (X Y : Matrix (Fin n) (Fin n) K) (hx : X ∈ ({A, B, C} : Set _))
      (hy : Y ∈ ({A, B, C} : Set _)) : Commute X Y := by
    by_cases e : X = Y
    · subst Y
      exact Commute.refl X
    · exact h hx hy e
  exact G3Scalar.field_three_matrices A B C
    (comm A B (by simp) (by simp)) (comm A C (by simp) (by simp))
    (comm B C (by simp) (by simp))
