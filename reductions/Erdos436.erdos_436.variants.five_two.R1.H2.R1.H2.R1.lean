import OMAReductions.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1
import Mathlib

/-! The Galois action on fifth roots of the rational primes realizes every
prescription, by a norm and valuation argument followed by Kummer duality.
Only the existence of a prime of the fixed field and the action of its
residue Frobenius are left as separate inputs. -/
open scoped BigOperators
namespace QuinticKummer

lemma prime_independence {I F : Type} [Fintype I] [Field F] [CharZero F] [FiniteDimensional ℚ F]
    (hdeg : Module.finrank ℚ F ≤ 4) (p : I → ℕ) (hinj : Function.Injective p) (hp : ∀ i, (p i).Prime)
    (a : I → ZMod 5) (x : F) (h : x^5 = ∏ i, (p i : F)^(a i).val) : a = 0 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N : ℕ := ∏ i, p i ^ (a i).val
  have eqn : x^5 = algebraMap ℚ F (N : ℚ) := by simpa [N] using h
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
    have hv' : (5 : ℤ) * padicValRat (p i) (Algebra.norm ℚ x) = (Module.finrank ℚ F : ℤ) * ((a i).val : ℤ) := hv
    have hd : (5 : ℤ) ∣ (Module.finrank ℚ F : ℤ) * ((a i).val : ℤ) := ⟨_,hv'.symm⟩
    have hdN : 5 ∣ Module.finrank ℚ F * (a i).val := by exact_mod_cast hd
    rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp hdN with d|d <;> omega
  exact ZMod.val_injective 5 (by simpa using eq0)

lemma prescribe {I F E : Type} [Fintype I] [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (z : F) (hz : IsPrimitiveRoot z 5)
    (b : I → F) (r : I → E) (hr : ∀ i, (r i)^5 = algebraMap F E (b i)) (hne : ∀ i, r i ≠ 0)
    (hind : ∀ (a : I → ZMod 5) (x : F), x^5 = ∏ i, (b i)^(a i).val → a=0)
    (v : I → ZMod 5) : ∃ σ : E ≃ₐ[F] E, ∀ i, σ (r i) = r i * (algebraMap F E z)^(v i).val := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let u := algebraMap F E z
  have hu : IsPrimitiveRoot u 5 := hz.map_of_injective (algebraMap F E).injective
  have fixed (σ : E ≃ₐ[F] E) : σ u = u := σ.commutes z
  let S : AddSubmonoid (I → ZMod 5) := {
    carrier := {a | ∃ σ : E ≃ₐ[F] E, ∀ i, σ (r i) = r i * u^(a i).val}
    zero_mem' := ⟨AlgEquiv.refl,fun i => by simp⟩
    add_mem' := by
      rintro a b ⟨σ,hσ⟩ ⟨τ,hτ⟩
      refine ⟨τ.trans σ,fun i => ?_⟩
      simp only [AlgEquiv.trans_apply,hτ,map_mul,map_pow,hσ,fixed,Pi.add_apply,ZMod.val_add]
      have cyc (n : ℕ) : u^(n%5) = u^n := hu.eq_orderOf ▸ pow_mod_orderOf u n
      rw [cyc,pow_add,mul_assoc] }
  let W : Submodule (ZMod 5) (I → ZMod 5) := {
    S with
    smul_mem' := fun c a ha => by
      change c • a ∈ S
      have h := S.nsmul_mem ha c.val
      simpa only [← Nat.cast_smul_eq_nsmul (ZMod 5),ZMod.natCast_zmod_val] using h }
  suffices W = ⊤ from (show v ∈ W by rw [this]; trivial)
  by_contra hproper
  obtain ⟨g,hg,hker⟩ := W.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hproper)
  let a (i : I) := g (Pi.single i 1)
  have repr (t : I → ZMod 5) : g t = ∑ i, t i * a i := by
    have eqv : t = ∑ i, t i • Pi.single i (1 : ZMod 5) := by
      funext j
      simp [Finset.sum_apply,Pi.single_apply,ite_mul,mul_ite]
    conv_lhs => rw [eqv]
    simp [a]
  let w := ∏ i, (r i)^(a i).val
  have invari (σ : E ≃ₐ[F] E) : σ w = w := by
    have character (i : I) : ∃ c : ZMod 5, σ (r i) = r i*u^c.val := by
      have root : (σ (r i)/r i)^5 = 1 := by
        rw [div_pow,← map_pow,hr,σ.commutes,div_self]
        exact (hr i ▸ pow_ne_zero 5 (hne i))
      obtain ⟨k,hk,he⟩ := hu.eq_pow_of_pow_eq_one root
      refine ⟨k,?_⟩
      rw [ZMod.val_natCast,Nat.mod_eq_of_lt hk]
      exact (div_eq_iff (hne i)).mp he.symm |>.trans (mul_comm ..)
    choose c hc using character
    have hcW : c ∈ W := ⟨σ,hc⟩
    have eqz : ∑ i, c i * a i = 0 := (repr c).symm.trans (hker hcW)
    have hd : 5 ∣ ∑ i, (c i).val * (a i).val := (ZMod.natCast_eq_zero_iff ..).mp (by simpa using eqz)
    change σ (∏ i, (r i)^(a i).val) = _
    simp only [map_prod,map_pow,hc,mul_pow,Finset.prod_mul_distrib,← pow_mul,Finset.prod_pow_eq_pow_sum]
    rw [hu.pow_eq_one_iff_dvd _ |>.mpr hd,mul_one]
  obtain ⟨x,hx⟩ := (IsGalois.mem_range_algebraMap_iff_fixed w).mpr invari
  have hx3 : x^5 = ∏ i, b i ^ (a i).val := (algebraMap F E).injective (by
    rw [map_pow,hx,map_prod]
    change (∏ i, (r i)^(a i).val)^5 = _
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul,Nat.mul_comm,pow_mul,hr,map_pow])
  have zero := hind a x hx3
  apply hg
  apply LinearMap.ext
  intro t
  simp [repr t,zero]

end QuinticKummer
open Polynomial NumberField
open scoped IntermediateField
namespace QuinticKummer

lemma lift_roots {I : Type} [Fintype I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (v : I → ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : CharZero L) (_ : NumberField L) (_ : IsGalois ℚ L)
      (σ : (𝓞 L) ≃+* (𝓞 L)) (u : 𝓞 L), u^4+u^3+u^2+u+1=0 ∧ σ u=u ∧ (∃ m : ℕ, 0 < m ∧ ∀ x, (σ : 𝓞 L → 𝓞 L)^[m] x = x) ∧
      ∀ i, ∃ r : 𝓞 L, r^5 = p i ∧ σ r=r*u^(v i) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let g (i : I) : ℚ[X] := X^5 - C (p i : ℚ)
  let P := cyclotomic 5 ℚ * ∏ i, g i
  let L := P.SplittingField
  letI : Polynomial.IsSplittingField ℚ L P := Polynomial.IsSplittingField.splittingField P
  letI : NumberField L := ⟨⟩
  letI : IsGalois ℚ L := isGalois_iff.mpr ⟨inferInstance,Polynomial.SplittingField.instNormal P⟩
  have pg (i : I) : (g i).natDegree = 5 := natDegree_X_pow_sub_C
  have neP : P ≠ 0 := mul_ne_zero (cyclotomic_ne_zero 5 ℚ) (Finset.prod_ne_zero_iff.mpr
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
  obtain ⟨u,hu⟩ := root (cyclotomic 5 ℚ) (dvd_mul_right ..) (by rw [natDegree_cyclotomic]; decide)
  have prim : IsPrimitiveRoot u 5 := by
    apply isRoot_cyclotomic_iff.mp
    simpa [Polynomial.IsRoot.def,aeval_def,eval₂_eq_eval_map] using hu
  have cu : u^4+u^3+u^2+u+1=0 := by
    have hcy : cyclotomic 5 ℚ = X^4 + X^3 + X^2 + X + 1 := by
      rw [cyclotomic_prime ℚ 5]; norm_num [Finset.sum_range_succ] <;> ring
    simpa [hcy] using hu
  have each (i : I) : ∃ r : L, r^5 = p i := by
    obtain ⟨r,hr⟩ := root (g i) (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (dvd_mul_left ..))
      (by rw [pg]; decide)
    exact ⟨r,by simpa [g,sub_eq_zero] using hr⟩
  choose r hr using each
  let F : IntermediateField ℚ L := ℚ⟮u⟯
  let u' : F := ⟨u,IntermediateField.mem_adjoin_simple_self ℚ u⟩
  have hu' : IsPrimitiveRoot u' 5 := prim.of_map_of_injective (f := F.subtype) Subtype.val_injective
  have deg : Module.finrank ℚ F ≤ 4 := by
    rw [show Module.finrank ℚ F = (minpoly ℚ u).natDegree from IntermediateField.adjoin.finrank (IsIntegral.of_finite ℚ u),
      ← cyclotomic_eq_minpoly_rat prim (by decide),natDegree_cyclotomic]
    decide
  have rn (i : I) : r i ≠ 0 := by
    intro hz
    have h := hr i
    rw [hz,zero_pow (by decide : 5 ≠ 0)] at h
    exact (Nat.cast_ne_zero.mpr (hp i).ne_zero) h.symm
  obtain ⟨σ,hσ⟩ := prescribe u' hu' (fun i => (p i : F)) r (fun i => by simpa using hr i) rn
    (prime_independence deg p hinj hp) (fun i => (v i : ZMod 5))
  let τ := RingOfIntegers.mapRingEquiv σ.toRingEquiv
  let U : 𝓞 L := ⟨u,prim.isIntegral (by decide)⟩
  refine ⟨L,inferInstance,inferInstance,inferInstance,inferInstance,τ,U,?_,?_,?_,?_⟩
  · exact Subtype.ext cu
  · exact Subtype.ext (σ.commutes u')
  · refine ⟨orderOf σ,orderOf_pos _,fun x => Subtype.ext ?_⟩
    have it (j : ℕ) : (((τ : 𝓞 L → 𝓞 L)^[j] x : 𝓞 L) : L) = (σ^j) (x : L) := by
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply',pow_succ']
        exact congrArg σ ih
    exact (it _).trans (by rw [pow_orderOf_eq_one]; rfl)
  · intro i
    have integral : IsIntegral ℤ (r i) := IsIntegral.of_pow (by decide : 0 < 5)
      ((hr i).symm ▸ (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L (p i : ℤ))))
    refine ⟨⟨r i,integral⟩,Subtype.ext (hr i),?_⟩
    apply Subtype.ext
    change σ (r i) = r i*u^(v i)
    have e := hσ i
    change σ (r i) = r i*u^((v i : ZMod 5).val) at e
    simpa only [ZMod.val_natCast,prim.eq_orderOf,pow_mod_orderOf] using e

end QuinticKummer
namespace OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1
open NumberField

/-- A degree-one prime of the fixed field at which the distinguished element
of the extension has residue outside the prime field. -/
def H1 : Prop := ∀ (L : Type) [Field L] [CharZero L] [NumberField L] [IsGalois ℚ L]
    (σ : (𝓞 L) ≃+* (𝓞 L)) (z : 𝓞 L), σ z ≠ z → ∀ B : ℕ,
    ∃ p > B, p.Prime ∧ ∃ (F : Type) (_ : Field F) (_ : CharP F p) (φ : 𝓞 L →+* F),
      (∀ a : 𝓞 L, σ a = a → (φ a)^p=φ a) ∧ (φ z)^p ≠ φ z

/-- The residue Frobenius which fixes the invariant ring agrees everywhere
with a single power of the given finite-order ring automorphism. -/
def H2 : Prop := ∀ (R : Type) [CommRing R] (σ : R ≃+* R) (m p : ℕ),
    0 < m → (∀ x : R, (σ : R → R)^[m] x = x) → m*m < p → p.Prime →
    ∀ (F : Type) [Field F] [CharP F p] (φ : R →+* F),
      (∀ a : R, σ a = a → (φ a)^p = φ a) →
      ∃ t : ℕ, ∀ a : R, (φ a)^p = φ ((σ : R → R)^[t] a)

lemma iterate_radical {R : Type} [CommRing R] (σ : R ≃+* R) (u : R) (hu : σ u=u)
    (r : R) (k : ℕ) (hr : σ r=r*u^k) (t : ℕ) :
    (σ : R → R)^[t] r=r*(u^t)^k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply',ih,map_mul,map_pow,map_pow,hu,hr,pow_succ,mul_pow]
    ring

lemma descend {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [CharP F p]
    (y : F) (hy : y^p=y) : ∃ z : ZMod p, ZMod.castHom (m := p) dvd_rfl F z = y := by
  have h := (Subfield.mem_bot_iff_pow_eq_self F p).mpr hy
  rw [← ZMod.fieldRange_castHom_eq_bot p] at h
  exact h

theorem main : H1 → H2 → OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1.H2 := by
  classical
  intro existsPrime compare B
  let w (q : ℕ) : ℕ := if q ∈ ([3,5,29] : List ℕ) then 0 else
    if q ∈ ([13,19,23,31,41,43,211,277] : List ℕ) then 2 else 1
  let T := (Finset.range 7889).filter Nat.Prime
  obtain ⟨L,_,_,_,_,σ,u,hu,hs,⟨m,hm,hit⟩,roots⟩ := QuinticKummer.lift_roots
    (fun i : T => i.val) (fun i => (Finset.mem_filter.mp i.property).2) Subtype.val_injective (fun i => w i.val)
  have haveRoot (q : ℕ) (hq : q.Prime) (h : q≤7888) :
      ∃ r : 𝓞 L, r^5=q ∧ σ r=r*u^(w q) :=
    roots ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hq⟩⟩
  obtain ⟨r0,r5,rs⟩ := haveRoot 2 (by decide) (by decide)
  have rne : r0≠0 := by intro he; rw [he] at r5; norm_num at r5
  have w2 : w 2=1 := by decide
  rw [w2,pow_one] at rs
  have moved : σ r0≠r0 := by
    intro he
    have u1 : u=1 := mul_left_cancel₀ rne (rs.symm.trans (he.trans (mul_one r0).symm))
    rw [u1] at hu
    norm_num at hu
  obtain ⟨p,hpB,hp,F,_,_,φ,fixed,moves⟩ := existsPrime L σ r0 moved (max (max B 7888) (m*m))
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t,hF⟩ := compare (𝓞 L) σ m p hm hit (by omega) hp F φ fixed
  let j := ZMod.castHom (m := p) dvd_rfl F
  obtain ⟨z,hz⟩ := descend (φ u) (fixed u hs)
  change j z=φ u at hz
  have eqz : z^4+z^3+z^2+z+1=0 := j.injective (by simpa only [map_add,map_pow,map_one,map_zero,hz] using congrArg φ hu)
  have z5 : z^5=1 := by linear_combination (z-1)*eqz
  have wt : z^t≠1 := by
    intro he
    apply moves
    rw [hF,iterate_radical σ u hs r0 1 (by simpa using rs) t,pow_one,map_mul,map_pow,←hz,←map_pow,he,map_one,mul_one]
  have zt5 : (z^t)^5=1 := by rw [←pow_mul,Nat.mul_comm,pow_mul,z5,one_pow]
  have prim : IsPrimitiveRoot (z^t) 5 := isPrimitiveRoot_of_mem_nthRootsFinset (by decide)
    ((Polynomial.mem_nthRootsFinset (by decide : 0<5) 1).mpr zt5) wt
  have zne : z^t ≠ 0 := by intro he; simp [he] at zt5
  have pd := prim.dvd_of_pow_eq_one (p-1) (ZMod.pow_card_sub_one_eq_one zne)
  refine ⟨p,by omega,hp,pd,z^t,prim,fun q hq hM => ?_⟩
  obtain ⟨r,rc,rσ⟩ := haveRoot q hq hM
  have ec : (φ r)^5 = (q : F) := by simpa only [map_pow,map_natCast] using congrArg φ rc
  have en : (q : ZMod p) ≠ 0 := by
    intro he
    have := Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff _ _).mp he)
    omega
  have nz : φ r ≠ 0 := by
    intro er
    apply en
    apply j.injective
    simpa [er] using ec.symm
  have ep : (φ r)^(p-1) = ((φ u)^t)^(w q) := by
    apply mul_left_cancel₀ nz
    calc
      φ r*(φ r)^(p-1) = (φ r)^p := by rw [←pow_succ',Nat.sub_add_cancel hp.pos]
      _ = φ ((σ : 𝓞 L → 𝓞 L)^[t] r) := hF r
      _ = _ := by rw [iterate_radical σ u hs r (w q) rσ t,map_mul,map_pow,map_pow]
  apply j.injective
  simp only [map_pow,map_natCast,hz,← ec,← pow_mul,Nat.mul_div_cancel' pd,ep]
  rfl

end OMA.R_Erdos436_erdos_436_variants_five_two_R1_H2_R1_H2_R1
