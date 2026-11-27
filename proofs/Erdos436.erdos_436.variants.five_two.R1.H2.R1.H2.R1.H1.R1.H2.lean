import OMAReductions.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1_H1_R1
import Mathlib

open NumberField
open scoped nonZeroDivisors
namespace OrderCompare

lemma restrictions {A C F : Type*} [CommRing A] [CommRing C] [Field F]
    (j : A →+* C) (hj : Function.Injective j) (s : A) (clear : ∀ x:C, ∃ y:A, j y = j s*x)
    (nz : ∀ f:A →+* F, f s ≠ 0) : Nonempty ((A →+* F) ≃ (C →+* F)) := by
  classical
  choose t ht using clear
  have one : t 1=s := hj (by rw [ht,mul_one])
  have zero : t 0=0 := hj (by rw [ht,mul_zero,map_zero])
  have add (x y : C) : t (x+y)=t x+t y := hj (by rw [map_add,ht,ht,ht,mul_add])
  have mul (x y:C) : t (x*y)*s=t x*t y := hj (by simp only [map_mul,ht]; ring)
  let res (g : C →+* F) := g.comp j
  refine ⟨(Equiv.ofBijective res ⟨?_,?_⟩).symm⟩
  · intro g h e
    have a (x:A) : g (j x)=h (j x) := DFunLike.congr_fun e x
    ext x
    apply mul_left_cancel₀ (nz (h.comp j))
    change h (j s)*g x=h (j s)*h x
    rw [←a s,←map_mul,←ht,a,ht,map_mul,a s]
  · intro f
    let g : C →+* F := {
      toFun := fun x => f (t x)/f s
      map_zero' := by simp [zero]
      map_one' := by simp [one,nz f]
      map_add' := fun x y => by rw [add,map_add,add_div]
      map_mul' := fun x y => by
        have eq := congrArg f (mul x y)
        simp only [map_mul] at eq
        field_simp [nz f]
        exact eq }
    refine ⟨g,?_⟩
    ext a
    have ta : t (j a)=s*a := hj (by rw [ht,map_mul])
    change f (t (j a))/f s=f a
    rw [ta,map_mul,mul_div_cancel_left₀ _ (nz f)]

lemma maximal_aux (L : Type) [Field L] [NumberField L] (R : Subalgebra ℤ (𝓞 L))
    (E : Type) [Field E] [NumberField E] [Algebra R E] [IsFractionRing R E] :
    ∃ B : ℕ, ∀ p > B, p.Prime →
      Nonempty ((R →+* ZMod p) ≃ (𝓞 E →+* ZMod p)) := by
  classical
  haveI : Module.Finite ℤ R := Module.Finite.of_injective R.val.toLinearMap Subtype.val_injective
  let j : R →+* 𝓞 E := (algebraMap R E).codRestrict (integralClosure ℤ E)
    (fun x => IsIntegral.map_of_comp_eq (RingHom.id ℤ) (algebraMap R E) (Subsingleton.elim _ _) (Algebra.IsIntegral.isIntegral (R := ℤ) x))
  have hj : Function.Injective j := fun x y e => (IsFractionRing.injective R E) (congrArg (fun q:𝓞 E => (q:E)) e)
  let b := Module.Free.chooseBasis ℤ (𝓞 E)
  obtain ⟨s,hs⟩ := IsLocalization.exist_integer_multiples_of_finite R⁰ (fun i => ((b i):E))
  have finite_clear (x : 𝓞 E) : ∃ y : R, j y=j (s:R)*x := by
    choose d hd using hs
    refine ⟨∑ i, (b.repr x i : ℤ) • d i,?_⟩
    have hb (i) : j (d i) = j (s:R)*b i := RingOfIntegers.ext (by
      change (algebraMap R E) (d i) = (algebraMap R E) (s:R)*(b i:E)
      simpa only [Algebra.smul_def] using hd i)
    rw [map_sum]
    conv_rhs => rw [← b.sum_repr x, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul,hb,mul_smul_comm]
  have sn : ((s:R):𝓞 L) ≠ 0 := fun eq => (nonZeroDivisors.coe_ne_zero s) (Subtype.ext eq)
  obtain ⟨B,hB⟩ := OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1_H1_R1.distinguish L (x := ((s:R):𝓞 L)) (y := 0) sn
  refine ⟨B,fun p hP hp => ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  apply restrictions j hj s finite_clear
  intro f hf
  obtain ⟨F,_,_,φ,hφ⟩ := OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1_H1_R1.lift_mod L R p f
  apply hB p hP F φ
  rw [map_zero,hφ (s:R),hf,map_zero]

lemma maximal (L : Type) [Field L] [NumberField L] (R : Subalgebra ℤ (𝓞 L)) :
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (B : ℕ), ∀ p > B, p.Prime →
      Nonempty ((R →+* ZMod p) ≃ (𝓞 E →+* ZMod p)) := by
  classical
  let E := FractionRing R
  let h : R →+* L := (algebraMap (𝓞 L) L).comp R.val.toRingHom
  have hi : Function.Injective h := (FaithfulSMul.algebraMap_injective (𝓞 L) L).comp Subtype.val_injective
  let u : E →+* L := IsFractionRing.lift hi
  letI : CharZero E := CharZero.of_addMonoidHom (algebraMap R E).toAddMonoidHom ((algebraMap R E).map_one) (IsFractionRing.injective R E)
  letI : FiniteDimensional ℚ E := FiniteDimensional.of_injective u.toRatAlgHom.toLinearMap u.injective
  letI : NumberField E := ⟨⟩
  exact ⟨E,inferInstance,inferInstance,maximal_aux L R E⟩

end OrderCompare

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1_H1_R1.H2 := OrderCompare.maximal
