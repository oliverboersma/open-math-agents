import OMAReductions.R_Erdos436_erdos_436_variants_three_three_R1_H2_R1
import Mathlib
open scoped BigOperators
namespace CubicKummer

lemma prime_independence {I F : Type} [Fintype I] [Field F] [CharZero F] [FiniteDimensional ℚ F]
    (hdeg : Module.finrank ℚ F ≤ 2) (p : I → ℕ) (hinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (a : I → ZMod 3) (x : F) (h : x^3 = ∏ i, (p i : F)^(a i).val) : a = 0 := by
  classical
  let N : ℕ := ∏ i, p i ^ (a i).val
  have eqn : x^3 = algebraMap ℚ F (N : ℚ) := by simpa [N] using h
  have eq' := congrArg (Algebra.norm ℚ) eqn
  simp only [map_pow,Algebra.norm_algebraMap] at eq'
  funext i
  haveI : Fact (p i).Prime := ⟨hp i⟩
  have fac : N.factorization (p i) = (a i).val := by
    unfold N
    rw [Nat.factorization_prod_apply (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
    rw [Finset.sum_eq_single i]
    · exact Nat.factorization_pow_self (hp i)
    · intro j _ hj
      rw [(hp j).factorization_pow,Finsupp.single_eq_of_ne (fun he => hj (hinj he.symm))]
    · simp
  have hv := congrArg (padicValRat (p i)) eq'
  simp only [padicValRat.pow,← padicValRat_of_nat] at hv
  rw [← Nat.factorization_def N (hp i),fac] at hv
  have degpos := Module.finrank_pos (R := ℚ) (M := F)
  have av := (a i).val_lt
  have eq0 : (a i).val = 0 := by
    have dg : Module.finrank ℚ F = 1 ∨ Module.finrank ℚ F = 2 := by omega
    have hv' : (3 : ℤ) * padicValRat (p i) (Algebra.norm ℚ x) = (Module.finrank ℚ F : ℤ) * ((a i).val : ℤ) := by exact hv
    rcases dg with t|t <;> rw [t] at hv' <;> push_cast at hv' <;> omega
  exact ZMod.val_injective 3 (by simpa using eq0)

lemma prescribe {I F E : Type} [Fintype I] [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (z : F) (hz : IsPrimitiveRoot z 3)
    (b : I → F) (r : I → E) (hr : ∀ i, (r i)^3 = algebraMap F E (b i)) (hne : ∀ i, r i ≠ 0)
    (hind : ∀ (a : I → ZMod 3) (x : F), x^3 = ∏ i, (b i)^(a i).val → a=0)
    (v : I → ZMod 3) : ∃ σ : E ≃ₐ[F] E, ∀ i, σ (r i) = r i * (algebraMap F E z)^(v i).val := by
  classical
  let u := algebraMap F E z
  have hu : IsPrimitiveRoot u 3 := hz.map_of_injective (algebraMap F E).injective
  have fixed (σ : E ≃ₐ[F] E) : σ u = u := σ.commutes z
  let S : AddSubmonoid (I → ZMod 3) := {
    carrier := {a | ∃ σ : E ≃ₐ[F] E, ∀ i, σ (r i) = r i * u^(a i).val}
    zero_mem' := ⟨AlgEquiv.refl,fun i => by simp⟩
    add_mem' := by
      rintro a b ⟨σ,hσ⟩ ⟨τ,hτ⟩
      refine ⟨τ.trans σ,fun i => ?_⟩
      simp only [AlgEquiv.trans_apply,hτ,map_mul,map_pow,hσ,fixed,Pi.add_apply,ZMod.val_add]
      have cyc (n : ℕ) : u^(n%3) = u^n := hu.eq_orderOf ▸ pow_mod_orderOf u n
      rw [cyc,pow_add,mul_assoc] }
  let W : Submodule (ZMod 3) (I → ZMod 3) := {
    S with
    smul_mem' := fun c a ha => by
      change c • a ∈ S
      have h := S.nsmul_mem ha c.val
      simpa only [← Nat.cast_smul_eq_nsmul (ZMod 3),ZMod.natCast_zmod_val] using h }
  suffices W = ⊤ from (show v ∈ W by rw [this]; trivial)
  by_contra hproper
  obtain ⟨g,hg,hker⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hproper)
  let a (i : I) := g (Pi.single i 1)
  have repr (t : I → ZMod 3) : g t = ∑ i, t i * a i := by
    have eqv : t = ∑ i, t i • Pi.single i (1 : ZMod 3) := by
      funext j
      simp [Finset.sum_apply,Pi.single_apply,ite_mul,mul_ite]
    conv_lhs => rw [eqv]
    simp [a]
  let w := ∏ i, (r i)^(a i).val
  have invari (σ : E ≃ₐ[F] E) : σ w = w := by
    have character (i : I) : ∃ c : ZMod 3, σ (r i) = r i*u^c.val := by
      have root : (σ (r i)/r i)^3 = 1 := by
        rw [div_pow,← map_pow,hr,σ.commutes,div_self]
        exact (hr i ▸ pow_ne_zero 3 (hne i))
      obtain ⟨k,hk,he⟩ := hu.eq_pow_of_pow_eq_one root
      refine ⟨k,?_⟩
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt hk]
      exact (div_eq_iff (hne i)).mp he.symm |>.trans (mul_comm ..)
    choose c hc using character
    have hcW : c ∈ W := ⟨σ,hc⟩
    have eqz : ∑ i, c i * a i = 0 := (repr c).symm.trans (hker hcW)
    have hd : 3 ∣ ∑ i, (c i).val * (a i).val := (ZMod.natCast_eq_zero_iff ..).mp (by simpa using eqz)
    change σ (∏ i, (r i)^(a i).val) = _
    simp only [map_prod,map_pow,hc,mul_pow,Finset.prod_mul_distrib,← pow_mul,Finset.prod_pow_eq_pow_sum]
    rw [hu.pow_eq_one_iff_dvd _ |>.mpr hd,mul_one]
  obtain ⟨x,hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed w).mpr invari
  have hx3 : x^3 = ∏ i, b i ^ (a i).val := (algebraMap F E).injective (by
    rw [map_pow,hx,map_prod]
    change (∏ i, (r i)^(a i).val)^3 = _
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul,Nat.mul_comm,pow_mul,hr,map_pow])
  have zero := hind a x hx3
  apply hg
  apply LinearMap.ext
  intro t
  simp [repr t,zero]

end CubicKummer
open Polynomial NumberField
open scoped IntermediateField
namespace CubicKummer

lemma lift_roots {I : Type} [Fintype I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (v : I → ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : NumberField L) (_ : IsGalois ℚ L)
      (σ : (𝓞 L) ≃+* (𝓞 L)) (u : 𝓞 L), u^2+u+1=0 ∧ σ u=u ∧
      ∀ i, ∃ r : 𝓞 L, r^3 = p i ∧ σ r=r*u^(v i) := by
  classical
  let g (i : I) : ℚ[X] := X^3 - C (p i : ℚ)
  let P := cyclotomic 3 ℚ * ∏ i, g i
  let L := P.SplittingField
  letI : Polynomial.IsSplittingField ℚ L P := Polynomial.IsSplittingField.splittingField P
  letI : NumberField L := ⟨⟩
  letI : IsGalois ℚ L := isGalois_iff.mpr ⟨inferInstance,Polynomial.SplittingField.instNormal P⟩
  have pg (i : I) : (g i).natDegree = 3 := natDegree_X_pow_sub_C
  have neP : P ≠ 0 := mul_ne_zero (cyclotomic_ne_zero 3 ℚ) (Finset.prod_ne_zero_iff.mpr
    (fun i _ h => by have := pg i; simp [h] at this))
  have root (f : ℚ[X]) (hf : f ∣ P) (hd : 0 < f.natDegree) : ∃ y : L, f.aeval y = 0 := by
    let j := algebraMap ℚ L
    have h := (IsSplittingField.splits L P).of_dvd (map_ne_zero (f := j) neP)
      (map_dvd (mapRingHom j) hf)
    have hd0 : (f.map j).natDegree ≠ 0 := by rw [natDegree_map]; exact hd.ne'
    obtain ⟨y,hy⟩ := h.exists_eval_eq_zero (degree_ne_of_natDegree_ne (n := 0) hd0)
    refine ⟨y,?_⟩
    rw [aeval_def,eval₂_eq_eval_map]
    exact hy
  obtain ⟨u,hu⟩ := root (cyclotomic 3 ℚ) (dvd_mul_right ..) (by rw [natDegree_cyclotomic]; decide)
  have prim : IsPrimitiveRoot u 3 := by
    apply isRoot_cyclotomic_iff.mp
    simpa [Polynomial.IsRoot.def,aeval_def,eval₂_eq_eval_map] using hu
  have cu : u^2+u+1=0 := by simpa [cyclotomic_three] using hu
  have each (i : I) : ∃ r : L, r^3 = p i := by
    obtain ⟨r,hr⟩ := root (g i) (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (dvd_mul_left ..))
      (by rw [pg]; decide)
    exact ⟨r,by simpa [g,sub_eq_zero] using hr⟩
  choose r hr using each
  let F : IntermediateField ℚ L := ℚ⟮u⟯
  let u' : F := ⟨u,IntermediateField.mem_adjoin_simple_self ℚ u⟩
  have hu' : IsPrimitiveRoot u' 3 := prim.of_map_of_injective (f := F.subtype) Subtype.val_injective
  have deg : Module.finrank ℚ F ≤ 2 := by
    rw [show Module.finrank ℚ F = (minpoly ℚ u).natDegree from IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ u),
      ← cyclotomic_eq_minpoly_rat prim (by decide),natDegree_cyclotomic]
    decide
  have rn (i : I) : r i ≠ 0 := by
    intro hz
    have h := hr i
    rw [hz,zero_pow (by decide : 3 ≠ 0)] at h
    exact (Nat.cast_ne_zero.mpr (hp i).ne_zero) h.symm
  obtain ⟨σ,hσ⟩ := prescribe u' hu' (fun i => (p i : F)) r (fun i => by simpa using hr i) rn
    (prime_independence deg p hinj hp) (fun i => (v i : ZMod 3))
  let τ := RingOfIntegers.mapRingEquiv σ.toRingEquiv
  let U : 𝓞 L := ⟨u,prim.isIntegral (by decide)⟩
  refine ⟨L,inferInstance,inferInstance,inferInstance,inferInstance,τ,U,?_,?_,?_⟩
  · exact Subtype.ext cu
  · exact Subtype.ext (σ.commutes u')
  · intro i
    have integral : IsIntegral ℤ (r i) := IsIntegral.of_pow (by decide : 0 < 3)
      ((hr i).symm ▸ (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L (p i : ℤ))))
    refine ⟨⟨r i,integral⟩,Subtype.ext (hr i),?_⟩
    apply Subtype.ext
    change σ (r i) = r i*u^(v i)
    have e := hσ i
    change σ (r i) = r i*u^((v i : ZMod 3).val) at e
    simpa only [ZMod.val_natCast,prim.eq_orderOf,pow_mod_orderOf] using e

end CubicKummer

theorem OMA.solution : OMA.R_Erdos436_erdos_436_variants_three_three_R1_H2_R1.H1 := by
  classical
  intro v M
  let T := (Finset.range (M+1)).filter Nat.Prime
  obtain ⟨L,field,char,num,gal,σ,u,hu,hs,hr⟩ := CubicKummer.lift_roots (fun i : T => i.val)
    (fun i => (Finset.mem_filter.mp i.property).2) Subtype.val_injective (fun i => v i.val)
  refine ⟨L,field,char,num,gal,σ,u,hu,hs,fun q hq hm => ?_⟩
  exact hr ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hq⟩⟩
