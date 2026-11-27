import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2
import Mathlib
/-!
# Relative class-number Bernoulli criterion
Integration and exact-target bridge: Hanan Beer (@hananzlt).
The mathematical formalization is reused from Riccardo Brasca (@riccardobrasca)
and the KummerCriterion contributors, and from the flt-regular contributors.
Contributors to the reused source history include Ruben Van de Velde,
Chris Birkbeck, Andrew Yang, and Kim Morrison. Original work is retained
under the Apache License, Version 2.0.
KummerCriterion source: https://github.com/riccardobrasca/KummerCriterion/tree/470de714f3de5a1ec8c0f6209502c1c5272c2c43
flt-regular source: https://github.com/leanprover-community/flt-regular/tree/bd81b78ba6e9f1c57215ff096e9e8f45d5d4b54b
Reduction: @Tchikrazi. This proves its relative class-number criterion.
Reuses the infrastructure of Hanan Beer (@hananzlt), PR6541.
The degree-one boundary is informed by @chris01-dev, R2.H1 (PR2526).
-/
/-- Transparent short name for the repeatedly used maximal real subfield. -/
noncomputable abbrev oMR (K:Type*) [Field K] : Subfield K :=NumberField.maximalRealSubfield K
-- Source: KummerCriterion.PrimitiveRootUnits
/- Helper identifiers are shortened to satisfy the submission size limit.
The accompanying reversible JSON map associates each alias with its original name.
Map JSON SHA256: 165a2e4034b11605ace98d74e95ecfbcf6285ccf6c876d604e6795bf8cea8e86
-/
section Module0
noncomputable section
open NumberField
open scoped NumberField
namespace IsPrimitiveRoot
noncomputable def unit' {K:Type*} [Field K] [CharZero K] {ζ:K} {k:ℕ}
    [NeZero k] (hζ:IsPrimitiveRoot ζ k) : (𝓞 K)ˣ:=
  (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne k)).unit
lemma unit'_coe {K:Type*} [Field K] [CharZero K] {ζ:K} {k:ℕ}
    [NeZero k] (hζ:IsPrimitiveRoot ζ k) : IsPrimitiveRoot (hζ.unit':𝓞 K) k :=
  hζ.toInteger_isPrimitiveRoot
lemma x5 {K:Type*} [Field K] [CharZero K] {ζ:K} {k:ℕ}
    [NeZero k] (hζ:IsPrimitiveRoot ζ k) : hζ.unit'^k=1:=
  Units.ext hζ.toInteger_isPrimitiveRoot.pow_eq_one
lemma yN {A:Type*} [CommRing A] [IsDomain A] {ζ μ :A} {k:ℕ}
    [NeZero k] (hζ:IsPrimitiveRoot ζ k) (hμ:μ^k=1) :
    algebraMap A (A ⧸ Ideal.span ({ζ-1} : Set A)) μ =1:=by
  obtain ⟨i,-,hi⟩ :=hζ.eq_pow_of_pow_eq_one hμ
  rw [← hi,map_pow]
  have hζ_mod:algebraMap A (A ⧸ Ideal.span ({ζ-1} : Set A)) ζ =1:=by
    rw [← map_one (algebraMap A (A ⧸ Ideal.span ({ζ-1} : Set A))),← sub_eq_zero,
      ← map_sub,Ideal.Quotient.algebraMap_eq,Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hζ_mod,one_pow]
end IsPrimitiveRoot
end
end Module0
-- Source: KummerCriterion.TotallyRealSubfield.ZetaPrime
section Module2
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p:ℕ) [hp:Fact p.Prime] (hp_odd:p ≠ 2)
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem vZ:
    ((zeta_spec p ℚ K).toInteger:𝓞 K) ^ p=1:=
  (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
theorem rQ:
    ((zeta_spec p ℚ K).toInteger:𝓞 K) ^ (p-1) *
      ((zeta_spec p ℚ K).toInteger:𝓞 K) = 1:=by
  rw [← pow_succ,Nat.sub_one_add_one hp.1.ne_zero]
  exact vZ p K
noncomputable def qt:Ideal (𝓞 K) :=
  Ideal.span {((zeta_spec p ℚ K).toInteger-1:𝓞 K)}
instance zetaPrime_isPrime: (qt p K).IsPrime:=
  (Ideal.span_singleton_prime
    (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero).mpr
    (zeta_spec p ℚ K).zeta_sub_one_prime'
theorem v3:qt p K ≠ ⊥ :=by
  rw [qt,Ne,Ideal.span_singleton_eq_bot]
  exact (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero
noncomputable def qX [IsCMField K] : Ideal (𝓞 ((oMR K))) :=
  (qt p K).under (𝓞 ((oMR K)))
instance [IsCMField K] : (qX p K).IsPrime:=
  Ideal.IsPrime.under _ _
instance [IsCMField K] : (qt p K).LiesOver (qX p K) :=
  Ideal.over_under _
lemma rT [IsCMField K] :
    (ringOfIntegersComplexConj K (zeta_spec p ℚ K).toInteger:𝓞 K) =
      ((zeta_spec p ℚ K).toInteger:𝓞 K) ^ (p-1) :=by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hzeta_torsion:hζ.unit' ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2
      (isOfFinOrder_iff_pow_eq_one.2 ⟨p,hp.1.pos,hζ.x5⟩)
  have hconj:=unitsComplexConj_torsion (K:=K) ⟨hζ.unit',hzeta_torsion⟩
  have h1: (unitsComplexConj K hζ.unit':𝓞 K) = (hζ.unit'⁻¹: (𝓞 K)ˣ) :=
    congrArg ((↑·) : (𝓞 K)ˣ → 𝓞 K) hconj
  have h2: (hζ.unit'⁻¹: (𝓞 K)ˣ) = hζ.unit'^ (p-1) :=by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ,Nat.sub_one_add_one hp.1.ne_zero]
    ext;push_cast;exact hζ.pow_eq_one
  rw [show (ringOfIntegersComplexConj K hζ.toInteger:𝓞 K) =
    (unitsComplexConj K hζ.unit':𝓞 K) from rfl,h1,h2,Units.val_pow_eq_pow_val]
  rfl
theorem vd [IsCMField K] (x:𝓞 K) :
    (ringOfIntegersComplexConj K x:𝓞 K) - x ∈ qt p K:=by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have htop:Algebra.adjoin ℤ {hζ.toInteger} = ⊤ :=
    IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ
  have hx:x ∈ Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 K)) :=htop ▸ trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy=>
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    have hp_pow:hζ.toInteger^p=1:=vZ p K
    have hc_pow: (ringOfIntegersComplexConj K hζ.toInteger) ^ p=1:=by
      rw [← map_pow,hp_pow,map_one]
    have hmem_of_pow: ∀ μ:𝓞 K,μ^p=1 → μ-1 ∈ qt p K:=by
      intro μ hμ
      have h1:=hζ.unit'_coe.yN hμ
      have h2: (algebraMap (𝓞 K)
          (𝓞 K ⧸ Ideal.span ({(hζ.unit':𝓞 K) - 1} : Set (𝓞 K)))) (μ-1) = 0:=by
        rw [map_sub,h1,map_one,sub_self]
      rw [Ideal.Quotient.algebraMap_eq,Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    have h1: (hζ.toInteger:𝓞 K) - 1 ∈ qt p K:=hmem_of_pow _ hp_pow
    have h2: (ringOfIntegersComplexConj K hζ.toInteger:𝓞 K) - 1 ∈ qt p K:=
      hmem_of_pow _ hc_pow
    have: (ringOfIntegersComplexConj K hζ.toInteger:𝓞 K) - hζ.toInteger=
        ((ringOfIntegersComplexConj K hζ.toInteger:𝓞 K) - 1) -
          (hζ.toInteger-1) :=by ring
    rw [this]
    exact Ideal.sub_mem _ h2 h1
  | algebraMap r =>
    have:ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) r) =
        (algebraMap ℤ (𝓞 K)) r :=by
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 ((oMR K))) (𝓞 K),AlgEquiv.commutes]
    rw [this,sub_self]
    exact Ideal.zero_mem _
  | add x y _ _ hpx hpy=>
    have: (ringOfIntegersComplexConj K (x+y) : 𝓞 K) - (x+y) =
        ((ringOfIntegersComplexConj K x:𝓞 K) - x) +
          ((ringOfIntegersComplexConj K y:𝓞 K) - y) :=by
      push_cast [map_add];ring
    rw [this]
    exact Ideal.add_mem _ hpx hpy
  | mul x y _ _ hpx hpy=>
    have: (ringOfIntegersComplexConj K (x*y) : 𝓞 K) - (x*y) =
        ((ringOfIntegersComplexConj K x:𝓞 K) - x) *
            (ringOfIntegersComplexConj K y:𝓞 K) +
          x* ((ringOfIntegersComplexConj K y:𝓞 K) - y) :=by
      push_cast [map_mul];ring
    rw [this]
    exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ hpx)
      (Ideal.mul_mem_left _ _ hpy)
lemma yn [IsCMField K] :
    ((zeta_spec p ℚ K).toInteger-1:𝓞 K) *
      ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger-1) =
      -((zeta_spec p ℚ K).toInteger^ (p-1)) *
        ((zeta_spec p ℚ K).toInteger-1) ^ 2:=by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hc_pi: (ringOfIntegersComplexConj K (hζ.toInteger-1) : 𝓞 K) =
      hζ.toInteger^ (p-1) - 1:=by
    rw [map_sub,map_one,rT]
  have hpow_succ:hζ.toInteger^ (p-1) * hζ.toInteger=1:=
    rQ p K
  rw [hc_pi]
  linear_combination (hζ.toInteger-1) * hpow_succ
lemma uu [IsCMField K] :
    ringOfIntegersComplexConj K
        (((zeta_spec p ℚ K).toInteger-1) *
          ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger-1)) =
      ((zeta_spec p ℚ K).toInteger-1) *
        ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger-1) :=by
  rw [map_mul,mul_comm]
  congr 1
  ext
  exact complexConj_apply_apply K _
noncomputable def piPlus [IsCMField K] : 𝓞 ((oMR K)) :=by
  have hfix:=uu p K
  rw [RingOfIntegers.ext_iff,coe_ringOfIntegersComplexConj,
    RingOfIntegers.complexConj_eq_self_iff] at hfix
  exact hfix.choose
lemma ww [IsCMField K] :
    (algebraMap (𝓞 ((oMR K))) (𝓞 K)) (piPlus p K) =
      ((zeta_spec p ℚ K).toInteger-1:𝓞 K) *
        ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger-1) :=by
  have hfix:=uu p K
  rw [RingOfIntegers.ext_iff,coe_ringOfIntegersComplexConj,
    RingOfIntegers.complexConj_eq_self_iff] at hfix
  ext
  rw [← hfix.choose_spec];rfl
theorem zH [IsCMField K] :
    (Ideal.span {piPlus p K}).map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) =
      qt p K^2:=by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hζ_unit:IsUnit ((hζ.unit':𝓞 K) ^ (p-1)) := (hζ.unit'.isUnit.pow _)
  have hneg_unit:IsUnit (-(hζ.toInteger:𝓞 K) ^ (p-1)) :=by
    rw [show (hζ.toInteger:𝓞 K) = (hζ.unit':𝓞 K) from rfl]
    exact hζ_unit.neg
  rw [Ideal.map_span,Set.image_singleton,ww,
    yn,qt,Ideal.span_singleton_pow,
    show-(hζ.toInteger:𝓞 K) ^ (p-1) * ((hζ.toInteger-1) ^ 2) =
        ((hζ.toInteger-1) ^ 2) * -(hζ.toInteger) ^ (p-1) from by ring,
    Ideal.span_singleton_mul_right_unit hneg_unit]
include hp_odd in
theorem xk [IsCMField K]
    (x:𝓞 ((oMR K))) (hx:x ≠ 0) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger-1:𝓞 K)
                      (algebraMap (𝓞 ((oMR K))) (𝓞 K) x)) :=by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  set α :=algebraMap (𝓞 ((oMR K))) (𝓞 K) x with hα_def
  have hα:α ≠ 0:= (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hx
  have hπ_prime:Prime (hζ.toInteger-1:𝓞 K) :=hζ.zeta_sub_one_prime'
  have hfin:FiniteMultiplicity (hζ.toInteger-1:𝓞 K) α :=
    FiniteMultiplicity.of_prime_left hπ_prime hα
  obtain ⟨u,hαu,hπ_nd_u⟩ :=hfin.exists_eq_pow_mul_and_not_dvd
  set e :=multiplicity (hζ.toInteger-1:𝓞 K) α with he_def
  have hcα:ringOfIntegersComplexConj K α=α:=
    (ringOfIntegersComplexConj K).commutes x
  have hc_pi:ringOfIntegersComplexConj K (hζ.toInteger-1) =
      -hζ.toInteger^ (p-1) * (hζ.toInteger-1) :=by
    rw [map_sub,map_one,rT]
    linear_combination rQ p K
  have hcα_expand: (-hζ.toInteger^ (p-1) * (hζ.toInteger-1) : 𝓞 K) ^ e*
      ringOfIntegersComplexConj K u= (hζ.toInteger-1) ^ e*u:=by
    have:=hcα
    rw [hαu,map_mul,map_pow,hc_pi] at this
    exact this
  have hπ_ne: (hζ.toInteger-1:𝓞 K) ≠ 0:=hπ_prime.ne_zero
  have hcu_eq: ((-hζ.toInteger^ (p-1)) ^ e:𝓞 K) * ringOfIntegersComplexConj K u=u:=by
    have hreord: ((hζ.toInteger-1) ^ e:𝓞 K) *
        (((-hζ.toInteger^ (p-1)) ^ e) * ringOfIntegersComplexConj K u) =
        ((hζ.toInteger-1) ^ e:𝓞 K) * u:=by
      have hsplit: ((-hζ.toInteger^ (p-1) * (hζ.toInteger-1)) ^ e:𝓞 K) =
          ((hζ.toInteger-1) ^ e) * (((-hζ.toInteger^ (p-1)) ^ e)) :=by
        rw [mul_pow];ring
      rw [← hcα_expand,hsplit,mul_assoc]
    exact mul_left_cancel₀ (pow_ne_zero _ hπ_ne) hreord
  have hres: (ringOfIntegersComplexConj K u:𝓞 K) - u ∈ qt p K:=
    vd p K u
  have hpow_sub: ∀ n:ℕ,(hζ.toInteger^n-1:𝓞 K) ∈ qt p K:=by
    intro n
    rw [qt,Ideal.mem_span_singleton]
    have:=sub_dvd_pow_sub_pow hζ.toInteger (1:𝓞 K) n
    rwa [one_pow] at this
  have hneg_pow_sub: ((-hζ.toInteger^ (p-1)) ^ e- (-1) ^ e:𝓞 K) ∈ qt p K:=by
    have key: ((-hζ.toInteger^ (p-1)) ^ e- (-1) ^ e:𝓞 K) =
        (-1) ^ e* (hζ.toInteger^ ((p-1) * e) - 1) :=by
      rw [neg_pow,← pow_mul];ring
    rw [key]
    exact Ideal.mul_mem_left _ _ (hpow_sub _)
  have hkey: ((1- (-1) ^ e) * u:𝓞 K) ∈ qt p K:=by
    have h1: ((-hζ.toInteger^ (p-1)) ^ e:𝓞 K) * ringOfIntegersComplexConj K u-
        (-1) ^ e*u ∈ qt p K:=by
      have h1a: ((-hζ.toInteger^ (p-1)) ^ e:𝓞 K) * ringOfIntegersComplexConj K u-
          (-1) ^ e*u=
          (((-hζ.toInteger^ (p-1)) ^ e- (-1) ^ e) * ringOfIntegersComplexConj K u) +
          ((-1) ^ e) * (ringOfIntegersComplexConj K u-u) :=by ring
      rw [h1a]
      exact Ideal.add_mem _
        (Ideal.mul_mem_right _ _ hneg_pow_sub)
        (Ideal.mul_mem_left _ _ hres)
    rw [hcu_eq] at h1
    convert h1 using 1
    ring
  rcases Nat.even_or_odd e with he | he
  · exact he
  · exfalso
    have hp2:2 < p:=lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
    have h_two_u: (2*u:𝓞 K) ∈ qt p K:=by
      convert hkey using 2
      rw [Odd.neg_one_pow he];ring
    have h_prime:=zetaPrime_isPrime p K
    rcases h_prime.mem_or_mem h_two_u with h | h
    · exact IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' p (zeta_spec p ℚ K) hp2 h
    · rw [qt,Ideal.mem_span_singleton] at h
      exact hπ_nd_u h
include hp_odd in
theorem sf [IsCMField K] :
    (qX p K).map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) = (qt p K) ^ 2:=by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [qX] at hy
    rw [Ideal.mem_comap,qt,Ideal.mem_span_singleton] at hy
    by_cases hy0:y=0
    · simp [hy0]
    have heven:=xk p hp_odd K y hy0
    have hfin:FiniteMultiplicity
        ((zeta_spec p ℚ K).toInteger-1:𝓞 K)
        (algebraMap (𝓞 ((oMR K))) (𝓞 K) y) :=
      FiniteMultiplicity.of_prime_left (zeta_spec p ℚ K).zeta_sub_one_prime'
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hy0)
    have hge:1 ≤ multiplicity ((zeta_spec p ℚ K).toInteger-1:𝓞 K)
        (algebraMap (𝓞 ((oMR K))) (𝓞 K) y) :=
      hfin.pow_dvd_iff_le_multiplicity.mp (by rwa [pow_one])
    have h2le:2 ≤ multiplicity ((zeta_spec p ℚ K).toInteger-1:𝓞 K)
        (algebraMap (𝓞 ((oMR K))) (𝓞 K) y) :=by
      rcases heven with ⟨k,hk⟩
      omega
    rw [Ideal.mem_comap,show (qt p K) ^ 2=
        Ideal.span {((zeta_spec p ℚ K).toInteger-1:𝓞 K) ^ 2} from
      by rw [qt,Ideal.span_singleton_pow],Ideal.mem_span_singleton]
    exact hfin.pow_dvd_iff_le_multiplicity.mpr h2le
  · rw [← zH p K]
    refine Ideal.map_mono ?_
    rw [Ideal.span_singleton_le_iff_mem]
    rw [qX,Ideal.mem_comap,qt,ww,
      Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
end CyclotomicSetup
end KummerCriterion
end
end Module2
-- Source: FltRegular.NumberTheory.Cyclotomic.UnitLemmas
section Module3
variable {p:ℕ} [NeZero p] {K:Type*} [Field K]
variable {ζ:K} (hζ:IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open IsCyclotomicExtension NumberField Polynomial IsCMField
noncomputable section
theorem zq {A:Type*} [CommRing A] {t:A} :
    algebraMap A (A ⧸ Ideal.span ({t-1} : Set A)) t =1:=by
  rw [← map_one <| algebraMap A <| A ⧸ Ideal.span ({t-1} : Set A),← sub_eq_zero,← map_sub,
    Ideal.Quotient.algebraMap_eq,Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)
theorem aux {t} {l:𝓞 K} {f:Fin t → ℤ} {μ:K} (hμ:IsPrimitiveRoot μ p)
    (h: ∑ x:Fin t,f x • hμ.toInteger^ (x:ℕ) = l) :
    algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) l = ∑ x:Fin t,(f x :𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) :=by
  rw [← h,map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul]
  have:hμ.toInteger^p=1:=by
    ext
    push_cast
    exact hμ.pow_eq_one
  obtain ⟨k,-,hk⟩ :=hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one this
  have:algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) hμ.toInteger=1:=by
    rw [← hk,map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K)) ^ k=1
    rw [zq,one_pow]
  simp only [map_pow (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))))),this,one_pow,zsmul_one]
variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem wD (hpo:Odd p) (x:K)
    (h: ∃ (n:ℕ) (_:0 < n),x^n=1) :
    ∃ (m k :ℕ),x= (-1) ^ k* (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit).1:K) ^ m:=by
  obtain ⟨n,hn,hxn⟩ :=h
  have hη: (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit).1:K) = ζ:=by rw [IsUnit.unit_spec];rfl
  simp only [hη]
  obtain ⟨r,-,hr | hr⟩ :=hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hxn⟩)
  · exact ⟨r,2,by simp [hr]⟩
  · exact ⟨r,1,by simp [hr]⟩
lemma xq (u: (𝓞 K)ˣ) [Fact (p.Prime)] (hp:2 < p) :
    haveI:=IsCyclotomicExtension.Rat.isCMField (S:= {p}) K ⟨p,rfl,hp⟩
    algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (unitsMulComplexConjInv K u).1=1:=by
  have:=IsCyclotomicExtension.Rat.isCMField (S:= {p}) K ⟨p,rfl,hp⟩
  have:=Units.coe_map_inv (N:=𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))))) (unitsComplexConj K u)
  rw [unitsMulComplexConjInv_apply,Units.val_mul,map_mul,← MonoidHom.coe_coe,← this,
    Units.mul_inv_eq_one,Units.coe_map,MonoidHom.coe_coe]
  have:=Fact.mk hp
  have hu:=hζ.integralPowerBasis.basis.sum_repr u
  let a :=hζ.integralPowerBasis.basis.repr
  let φn:=hζ.integralPowerBasis.dim
  simp_rw [PowerBasis.basis_eq_pow,IsPrimitiveRoot.integralPowerBasis_gen] at hu
  have hu':=congr_arg (ringOfIntegersComplexConj K) hu
  replace hu': ∑ x:Fin φn,(a u) x • (ringOfIntegersComplexConj K)
      (hζ.toInteger^ (x:ℕ)) = unitsComplexConj K u:=by
    refine Eq.trans ?_ hu'
    rw [map_sum]
    congr 1
    ext x
    congr 1
    rw [map_zsmul]
  have: ∀ x:Fin φn,ringOfIntegersComplexConj K (hζ.toInteger^ (x:ℕ)) =
      hζ.inv.toInteger^ (x:ℕ) :=by
    intro x
    ext
    simp only [map_pow,coe_ringOfIntegersComplexConj]
    suffices ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ∈ Units.torsion K by
      have H :=RingOfIntegers.ext_iff.1 <|
        Units.ext_iff.1 <| unitsComplexConj_torsion K ⟨((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit),‹_›⟩
      have: ↑↑((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) = ζ:=rfl
      simp only [Units.coe_mapEquiv,RingEquiv.coe_toMulEquiv,RingOfIntegers.mapRingEquiv_apply,
        this,AlgEquiv.coe_ringEquiv,InvMemClass.coe_inv,map_units_inv] at H
      change (complexConj K) ζ ^ (x:ℕ) = ζ⁻¹^ (x:ℕ)
      rw [H]
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p,by lia,?_⟩)
    ext
    exact hζ.pow_eq_one
  conv_lhs at hu'=>
    congr
    congr
    ext a
    rw [this a]
  exact (aux hζ hζ hu).trans (aux hζ hζ.inv hu').symm
theorem zh (u: (𝓞 K)ˣ) (n:ℕ) [Fact (p.Prime)] (hp:2 < p) :
    haveI:=IsCyclotomicExtension.Rat.isCMField (S:= {p}) K ⟨p,rfl,hp⟩
    u* (unitsComplexConj K u)⁻¹ ≠ -((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ^ n:=by
  by_contra H
  have hμ:algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) = 1:=by
    have hpow: ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) ^ p=1:=by
      change (hζ.toInteger^n) ^ p=1
      rw [← pow_mul,mul_comm,pow_mul,hζ.toInteger_isPrimitiveRoot.pow_eq_one,one_pow]
    obtain ⟨k,-,hk⟩ :=hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hpow
    rw [← hk,map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K)) ^ k=1
    rw [zq,one_pow]
  have hμ':algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) = -1:=by
    rw [← neg_eq_iff_eq_neg,← map_neg,← Units.val_pow_eq_pow_val,← Units.val_neg,← H]
    apply xq hζ u hp
  have:=Fact.mk hp
  apply (IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' _ hζ hp: (2:𝓞 K) ∉ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1:𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))))
  rw [← Ideal.Quotient.eq_zero_iff_mem,map_ofNat,← one_add_one_eq_two,← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ
theorem uN (u: (𝓞 K)ˣ) [H:Fact (p.Prime)] (hp:2 < p) :
    haveI:=IsCyclotomicExtension.Rat.isCMField (S:= {p}) K ⟨p,rfl,hp⟩
    ∃ m :ℕ,u* (unitsComplexConj K u)⁻¹= (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ^ m) ^ 2:=by
  have:=IsCyclotomicExtension.Rat.isCMField (S:= {p}) K ⟨p,rfl,hp⟩
  have hpo:Odd p :=H.out.odd_of_ne_two hp.ne'
  let:NormedAlgebra ℚ ℂ:=normedAlgebraRat
  have:=Embeddings.pow_eq_one_of_norm_eq_one K ℂ (x:=u* (unitsComplexConj K u)⁻¹) ?_ ?_
  · have H :=wD hζ hpo (u* (unitsComplexConj K u)⁻¹:K) this
    obtain ⟨n,k,hz⟩ :=H
    simp_rw [← pow_mul]
    have hk:=Nat.even_or_odd k
    rcases hk with hk | hk
    · simp only [hk.neg_one_pow,one_mul] at hz
      rw [← map_mul,← Units.val_mul,← map_pow,← Units.val_pow_eq_pow_val] at hz
      norm_cast at hz
      rw [hz]
      refine (exists_congr fun a => ?_).mp
        ((hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).exists_pow_eq_pow_two_mul hpo n)
      · rw [mul_comm]
    · by_contra
      simp only [hk.neg_one_pow,neg_mul,one_mul] at hz
      rw [← map_mul,← Units.val_mul,← map_pow,← Units.val_pow_eq_pow_val,← map_neg] at hz
      norm_cast at hz
      simpa [hz] using zh hζ u n hp
  · apply RingHom.IsIntegralElem.mul
    · exact NumberField.RingOfIntegers.isIntegral_coe _
    · exact NumberField.RingOfIntegers.isIntegral_coe _
  · simp
end
end Module3
-- Source: KummerCriterion.TotallyRealSubfield.Conjugation
section Module4
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p:ℕ) [hp:Fact p.Prime] (hp_odd:p ≠ 2)
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem yy [IsCMField K] (a:𝓞 K) :
    (Ideal.span {a}).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom=
      Ideal.span {ringOfIntegersComplexConj K a} :=by
  simpa using
    (Ideal.map_span ((ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ({a} : Set (𝓞 K)))
theorem ideal_map_conj_eq [IsCMField K]
    (I:Ideal (𝓞 (oMR K))) :
    (I.map (algebraMap (𝓞 (oMR K)) (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom=
      I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) :=by
  rw [Ideal.map_map]
  congr
  ext x
  simp [RingHom.comp_apply,AlgEquiv.commutes]
theorem yk [IsCMField K]
    (a:𝓞 K) (_ha:a ≠ 0) (I:Ideal (𝓞 (oMR K)))
    (hIa:I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) = Ideal.span {a})
    (hIca:I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a}) :
    ∃ u : (𝓞 K)ˣ,ringOfIntegersComplexConj K a=u*a:=by
  let hspan:Ideal.span {a} = Ideal.span {ringOfIntegersComplexConj K a} :=hIa.symm.trans hIca
  obtain ⟨u,hu⟩ :=Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u,?_⟩
  simpa [mul_comm] using hu.symm
theorem yT [IsCMField K]
    (a:𝓞 K) (ha:a ≠ 0) (u: (𝓞 K)ˣ)
    (hu:ringOfIntegersComplexConj K a=u*a) :
    unitsComplexConj K u*u=1:=by
  have hcc:ringOfIntegersComplexConj K (ringOfIntegersComplexConj K a) = a:=by
    apply RingOfIntegers.ext
    simp [coe_ringOfIntegersComplexConj,complexConj_apply_apply]
  have hu1:a= (unitsComplexConj K u: (𝓞 K)ˣ) * ringOfIntegersComplexConj K a:=by
    simpa [hcc,unitsComplexConj,map_mul] using! congrArg (ringOfIntegersComplexConj K) hu
  rw [hu] at hu1
  have hu2:a= (((unitsComplexConj K u*u: (𝓞 K)ˣ) : 𝓞 K) * a) :=by
    simpa [mul_assoc] using hu1
  apply Units.ext
  apply mul_right_cancel₀ ha
  simpa [one_mul] using hu2.symm
include hp_odd in
theorem xZ [IsCMField K]
    {hζ:IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (u: (𝓞 K)ˣ) (_hu:unitsComplexConj K u*u=1) :
    ∃ m :ℕ,u* (unitsComplexConj K u)⁻¹= (hζ.unit'^m) ^ 2:=
  uN (hζ:=hζ) u
    (lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd))
include hp_odd in
theorem wd [IsCMField K]
    {hζ:IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (u: (𝓞 K)ˣ)
    (hu:unitsComplexConj K u*u=1) :
    ∃ n k:ℕ,u= (-1: (𝓞 K)ˣ) ^ k*hζ.unit'^n:=by
  obtain ⟨m,hm⟩ :=
    xZ (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ) u hu
  have hcu: (unitsComplexConj K u)⁻¹=u:=inv_eq_of_mul_eq_one_right hu
  have hu_sq:u^2= (hζ.unit'^m) ^ 2:=by
    simpa [pow_two,hcu] using hm
  have hu_fin: ∃ n:ℕ,∃ _:0 < n,(u:K) ^ n=1:=by
    refine ⟨2*p,Nat.mul_pos (by decide) hp.1.pos,?_⟩
    have hu_sqK:
        (u:K) ^ 2= (((((hζ.unit'^m) ^ 2: (𝓞 K)ˣ) : (𝓞 K)) : K)) :=
      congrArg (fun x : (𝓞 K)ˣ=> (((x: (𝓞 K)) : K))) hu_sq
    calc
      (u:K) ^ (2*p) = ((u:K) ^ 2) ^ p:=by rw [pow_mul]
      _= (((((hζ.unit'^m) ^ 2: (𝓞 K)ˣ) : (𝓞 K)) : K)) ^ p:=by rw [hu_sqK]
      _=1:=by
        let ν : (𝓞 K)ˣ:=hζ.unit'^m
        have hνp:ν^p=1:=by
          dsimp [ν]
          rw [← pow_mul,mul_comm,pow_mul,hζ.x5,one_pow]
        have hν2p: (ν^2) ^ p=1:=by
          rw [← pow_mul,mul_comm,pow_mul,hνp,one_pow]
        exact congrArg (fun x : (𝓞 K)ˣ=> (((x: (𝓞 K)) : K))) hν2p
  have hpo:Odd p :=hp.1.odd_of_ne_two hp_odd
  obtain ⟨n,k,hk⟩ :=wD (K:=K) (hζ:=hζ) hpo (u:K) hu_fin
  refine ⟨n,k,?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  have hunit_coe: ((((hζ.unit': (𝓞 K)ˣ) : 𝓞 K) : K)) =
      IsCyclotomicExtension.zeta p ℚ K :=by
    change (hζ.toInteger:K) = IsCyclotomicExtension.zeta p ℚ K
    exact hζ.coe_toInteger
  change (u:K) =
    (-1:K) ^ k*IsCyclotomicExtension.zeta p ℚ K ^n
  change (u:K) = (-1:K) ^ k*hζ.toInteger.1^n at hk
  rw [hζ.coe_toInteger] at hk
  exact hk
theorem conj_zeta_pow [IsCMField K]
    {hζ:IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (m:ℕ) :
    complexConj K (hζ.unit'^m: (𝓞 K)ˣ) = ((hζ.unit'^m)⁻¹: (𝓞 K)ˣ) :=by
  have hzeta_torsion:hζ.unit' ∈ NumberField.Units.torsion K :=by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p,hp.1.pos,?_⟩)
    exact hζ.x5
  have hbase:unitsComplexConj K hζ.unit'= (hζ.unit'⁻¹: (𝓞 K)ˣ) :=by
    simpa using unitsComplexConj_torsion K ⟨hζ.unit',hzeta_torsion⟩
  have hunits:
      unitsComplexConj K (hζ.unit'^m: (𝓞 K)ˣ) =
        ((hζ.unit'^m)⁻¹: (𝓞 K)ˣ) :=by
    calc
      unitsComplexConj K (hζ.unit'^m: (𝓞 K)ˣ) =
          (unitsComplexConj K hζ.unit') ^ m:=by simp
      _= ((hζ.unit')⁻¹: (𝓞 K)ˣ) ^ m:=by rw [hbase]
      _= ((hζ.unit'^m)⁻¹: (𝓞 K)ˣ) :=by simp
  have hro:
      ringOfIntegersComplexConj K (((hζ.unit'^m: (𝓞 K)ˣ) : 𝓞 K)) =
        (((hζ.unit'^m)⁻¹: (𝓞 K)ˣ) : 𝓞 K) :=Units.ext_iff.1 hunits
  exact RingOfIntegers.ext_iff.mp hro
include hp_odd in
theorem xA [IsCMField K] :
    (qt p K).ramificationIdx (𝓞 (oMR K)) = 2:=by
  have hmap0:Ideal.map (algebraMap (𝓞 (oMR K)) (𝓞 K))
      (qX p K) ≠ ⊥ :=by
    rw [sf p hp_odd K]
    exact pow_ne_zero 2 (v3 p K)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (qX p K) (qt p K)
    hmap0,sf p hp_odd K,multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (v3 p K) (zetaPrime_isPrime p K))]
include hp_odd in
theorem wL [IsCMField K]
    (I:Ideal (𝓞 (oMR K)))
    (a:𝓞 K) (ha:a ≠ 0)
    (hIa:
      I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) = Ideal.span {a}) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger-1:𝓞 K) a) :=by
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  let f :𝓞 (oMR K) →+*𝓞 K:=
    algebraMap (𝓞 (oMR K)) (𝓞 K)
  let P :Ideal (𝓞 K) :=qt p K
  let PPlus:Ideal (𝓞 (oMR K)) :=qX p K
  let π :𝓞 K:= (zeta_spec p ℚ K).toInteger-1
  have hI0:I ≠ ⊥ :=by
    intro hbot
    rw [hbot,Ideal.map_bot] at hIa
    exact ha (by simpa [Ideal.span_singleton_eq_bot] using hIa.symm)
  have hmap0:I.map f ≠ ⊥ :=by
    rw [hIa]
    simp [ha]
  have hP0:P ≠ ⊥ :=v3 p K
  have hPprime:P.IsPrime:=by
    dsimp [P]
    exact zetaPrime_isPrime p K
  have hPPlus0:PPlus ≠ ⊥ :=by
    intro hbot
    have hmap:Ideal.map f PPlus=P^2:=by
      simpa [f,P,PPlus] using sf p hp_odd K
    rw [hbot,Ideal.map_bot] at hmap
    exact (pow_ne_zero 2 hP0) hmap.symm
  have hPIrr:Irreducible P := (Ideal.prime_of_isPrime hP0 hPprime).irreducible
  have hPPlusIrr:Irreducible PPlus:=
    (Ideal.prime_of_isPrime hPPlus0 inferInstance).irreducible
  have hemul:emultiplicity P (I.map f) = PPlus.ramificationIdx' P *emultiplicity PPlus I :=by
    simpa [P,PPlus,f] using
      Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
        (R:=𝓞 (oMR K)) (S:=𝓞 K)
        (v:=PPlus) (w:=P) (I:=I) hI0 hPPlusIrr hPIrr hP0
  have hcount_even:
      Even (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I.map f))) :=by
    rw [Even]
    refine ⟨Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I),?_⟩
    have hemul':=hemul
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p:=PPlus) (q:=P) hPPlus0,
      xA (p:=p) (hp_odd:=hp_odd) (K:=K),
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPIrr hmap0,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPPlusIrr hI0,
      normalize_eq P,normalize_eq PPlus] at hemul'
    have hemul_nat:
        Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I.map f)) =
          2*Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I) :=by
      exact_mod_cast hemul'
    simpa [two_mul] using hemul_nat
  have hπPrime:Prime π :=by simpa [π] using hζ.zeta_sub_one_prime'
  let e :=multiplicity π a
  have hπFin:FiniteMultiplicity π a:=FiniteMultiplicity.of_prime_left hπPrime ha
  have hπe_dvd:π^e ∣ a:= (hπFin.pow_dvd_iff_le_multiplicity).2 le_rfl
  have hπe_not_dvd: ¬π^ (e+1) ∣ a:=by
    rw [hπFin.pow_dvd_iff_le_multiplicity]
    exact Nat.not_succ_le_self e
  have hcount_span:
      Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = e:=by
    apply Ideal.count_normalizedFactors_eq (p:=P) (x:=Ideal.span {a})
    · dsimp [P]
      rw [qt,Ideal.span_singleton_pow,Ideal.span_singleton_le_iff_mem,
        Ideal.mem_span_singleton]
      exact hπe_dvd
    · intro hle
      exact hπe_not_dvd <| by
        dsimp [P] at hle
        rw [qt,Ideal.span_singleton_pow,Ideal.span_singleton_le_iff_mem,
          Ideal.mem_span_singleton] at hle
        exact hle
  have:
      Even (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}))) :=by
    rw [← hIa]
    simpa [f] using hcount_even
  simpa [e,hcount_span] using this
end CyclotomicSetup
end KummerCriterion
end
end Module4
-- Source: KummerCriterion.TotallyRealSubfield.FixedAssociate
section Module5
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p:ℕ) [hp:Fact p.Prime] (hp_odd:p ≠ 2)
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
include hp_odd in
theorem yd [IsCMField K]
    {hζ:IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (I:Ideal (𝓞 (oMR K)))
    (a:𝓞 K) (u: (𝓞 K)ˣ)
    (ha:a ≠ 0)
    (hIa:I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) = Ideal.span {a})
    (hu:ringOfIntegersComplexConj K a=u*a)
    (hclass: ∃ n k:ℕ,u= (-1: (𝓞 K)ˣ) ^ k*hζ.unit'^n) :
    ∃ n :ℕ,u=hζ.unit'^n:=by
  obtain ⟨n,k,huk⟩ :=hclass
  by_cases hk_even:Even k
  · rcases hk_even with ⟨m,rfl⟩
    have hneg_even: (-1: (𝓞 K)ˣ) ^ (m+m) = 1:=
      Even.neg_one_pow (show Even (m+m) from ⟨m,rfl⟩)
    refine ⟨n,?_⟩
    calc
      u= (-1: (𝓞 K)ˣ) ^ (m+m) * hζ.unit'^n:=huk
      _=hζ.unit'^n:=by rw [hneg_even];simp
  · have hk_odd:Odd k :=Nat.not_even_iff_odd.mp hk_even
    let π :𝓞 K:=hζ.toInteger-1
    let P :Ideal (𝓞 K) :=qt p K
    let e :=multiplicity π a
    have heven:Even e :=
      wL (p:=p) (hp_odd:=hp_odd) (K:=K) I a ha hIa
    have hπPrime:Prime π :=by simpa [π] using hζ.zeta_sub_one_prime'
    have hπFin:FiniteMultiplicity π a:=FiniteMultiplicity.of_prime_left hπPrime ha
    obtain ⟨b,hpow,hnotdvd⟩ :=hπFin.exists_eq_pow_mul_and_not_dvd
    have hb_not_mem:b ∉ P:=by
      simpa [P,π,qt,Ideal.mem_span_singleton] using hnotdvd
    have hu_odd:u= (-1: (𝓞 K)ˣ) * hζ.unit'^n:=by
      calc
        u= (-1: (𝓞 K)ˣ) ^ k*hζ.unit'^n:=huk
        _= (-1: (𝓞 K)ˣ) * hζ.unit'^n:=by rw [Odd.neg_one_pow hk_odd]
    let γ : (𝓞 K)ˣ:= (-1: (𝓞 K)ˣ) * hζ.unit'^ (p-1)
    have hc_pi:ringOfIntegersComplexConj K π= (γ: (𝓞 K)ˣ) * π:=by
      have hc_pi':ringOfIntegersComplexConj K π= -hζ.toInteger^ (p-1) * π:=by
        rw [show π =hζ.toInteger-1 by rfl,map_sub,map_one,rT]
        linear_combination rQ p K
      simpa [γ,π,mul_assoc,mul_left_comm,mul_comm] using! hc_pi'
    have hγ_mul:γ^e*hζ.unit'^e=1:=by
      have hγhu:γ*hζ.unit'= (-1: (𝓞 K)ˣ) :=by
        dsimp [γ]
        rw [mul_assoc,← pow_succ,Nat.sub_one_add_one hp.1.ne_zero,hζ.x5,mul_one]
      have hmulpow:γ^e*hζ.unit'^e= (γ*hζ.unit') ^ e:=by
        simpa [mul_comm,mul_left_comm,mul_assoc] using (mul_pow γ (hζ.unit') e).symm
      calc
        γ^e*hζ.unit'^e= (γ*hζ.unit') ^ e:=hmulpow
        _= (-1: (𝓞 K)ˣ) ^ e:=by rw [hγhu]
        _=1:=by simpa using (Even.neg_one_pow heven: (-1: (𝓞 K)ˣ) ^ e=1)
    let u': (𝓞 K)ˣ:=hζ.unit'^e*u
    have hcb:ringOfIntegersComplexConj K b=u'*b:=by
      have hcalc:ringOfIntegersComplexConj K (π^e*b) = u* (π^e*b) :=by
        calc
          ringOfIntegersComplexConj K (π^e*b) = ringOfIntegersComplexConj K a:=by rw [hpow]
          _=u*a:=hu
          _=u* (π^e*b) :=by rw [hpow]
      rw [map_mul,map_pow,hc_pi,mul_pow] at hcalc
      have hcancel: (((γ^e: (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K b) =
          ((u: (𝓞 K)ˣ) : 𝓞 K) * b:=by
        have htmp:π^e* ((((γ^e: (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K b)) =
            π^e* ((((u: (𝓞 K)ˣ) : 𝓞 K) * b)) :=by
          simpa [mul_assoc,mul_left_comm,mul_comm] using hcalc
        exact mul_left_cancel₀ (pow_ne_zero _ hπPrime.ne_zero) htmp
      have hγ_mul':hζ.unit'^e*γ^e=1:=by simpa [mul_comm] using hγ_mul
      have hmult:=
        congrArg (fun x :𝓞 K=> (((hζ.unit'^e: (𝓞 K)ˣ) : 𝓞 K) * x)) hcancel
      have hγ_mul_coe: ((((hζ.unit'^e: (𝓞 K)ˣ) * γ^e: (𝓞 K)ˣ) : 𝓞 K)) = 1:=
        congrArg (fun x : (𝓞 K)ˣ=> (x:𝓞 K)) hγ_mul'
      have hmult'': ((((hζ.unit'^e: (𝓞 K)ˣ) * γ^e: (𝓞 K)ˣ) : 𝓞 K) *
          ringOfIntegersComplexConj K b) =
          ((((hζ.unit'^e: (𝓞 K)ˣ) * u: (𝓞 K)ˣ) : 𝓞 K) * b) :=by
        simpa [mul_assoc,mul_left_comm,mul_comm] using hmult
      have hmult':ringOfIntegersComplexConj K b=
          ((((hζ.unit'^e: (𝓞 K)ˣ) * u: (𝓞 K)ˣ) : 𝓞 K) * b) :=by
        calc
          ringOfIntegersComplexConj K b=
              ((((hζ.unit'^e: (𝓞 K)ˣ) * γ^e: (𝓞 K)ˣ) : 𝓞 K) *
                ringOfIntegersComplexConj K b) :=by rw [hγ_mul_coe];simp
          _=
              ((((hζ.unit'^e: (𝓞 K)ˣ) * u: (𝓞 K)ˣ) : 𝓞 K) * b) :=hmult''
      simpa [u',mul_assoc,mul_left_comm,mul_comm] using hmult'
    have hpow_sub: ∀ m:ℕ,(hζ.toInteger^m-1:𝓞 K) ∈ P:=by
      intro m
      dsimp [P]
      rw [qt,Ideal.mem_span_singleton]
      have hdiv:=sub_dvd_pow_sub_pow hζ.toInteger (1:𝓞 K) m
      rwa [one_pow] at hdiv
    have hu'_class:u'= (-1: (𝓞 K)ˣ) * hζ.unit'^ (e+n) :=by
      dsimp [u']
      calc
        hζ.unit'^e*u=
            hζ.unit'^e* ((-1: (𝓞 K)ˣ) * hζ.unit'^n) :=by rw [hu_odd]
        _= (-1: (𝓞 K)ˣ) * (hζ.unit'^e*hζ.unit'^n) :=by
          simp [mul_left_comm,mul_comm]
        _= (-1: (𝓞 K)ˣ) * hζ.unit'^ (e+n) :=by rw [← pow_add]
    have hu'_plus_mem: ((((u': (𝓞 K)ˣ) : 𝓞 K) + 1) : 𝓞 K) ∈ P:=by
      have hu'_plus_eq: (((u': (𝓞 K)ˣ) : 𝓞 K) + 1:𝓞 K) =
          (1-hζ.toInteger^e*hζ.toInteger^n:𝓞 K) :=by
        rw [hu'_class]
        simp only [Units.val_mul,Units.val_neg]
        rw [show (((hζ.unit'^ (e+n) : (𝓞 K)ˣ) : 𝓞 K)) =
          hζ.toInteger^ (e+n) by rfl]
        rw [pow_add]
        simp [sub_eq_add_neg,add_comm]
      have hpow_sub': (1-hζ.toInteger^e*hζ.toInteger^n:𝓞 K) ∈ P:=by
        have:
            (1-hζ.toInteger^e*hζ.toInteger^n:𝓞 K) =
              -(hζ.toInteger^ (e+n) - 1) :=by
          rw [pow_add]
          ring
        rw [this]
        exact P.neg_mem (hpow_sub (e+n))
      rw [hu'_plus_eq]
      exact hpow_sub'
    have hu'_minus_not_mem: ((((u': (𝓞 K)ˣ) : 𝓞 K) - 1) : 𝓞 K) ∉ P:=by
      intro hminus
      have hp2:2 < p:=lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
      have htwo: (2:𝓞 K) ∈ P:=by
        have hsub:=Ideal.sub_mem _ hu'_plus_mem hminus
        convert hsub using 1
        ring
      exact IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' p (zeta_spec p ℚ K) hp2 htwo
    have hprod_mem: ((((u': (𝓞 K)ˣ) : 𝓞 K) - 1) * b:𝓞 K) ∈ P:=by
      have hres: (ringOfIntegersComplexConj K b:𝓞 K) - b ∈ P:=
        vd p K b
      convert hres using 1
      rw [hcb]
      ring
    exfalso
    rcases (zetaPrime_isPrime p K).mem_or_mem hprod_mem with hunit_mem | hb_mem
    · exact hu'_minus_not_mem hunit_mem
    · exact hb_not_mem hb_mem
include hp_odd in
theorem xh [IsCMField K]
    {hζ:IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (a:𝓞 K) (u: (𝓞 K)ˣ)
    (hu:ringOfIntegersComplexConj K a=u*a)
    (hclass: ∃ n:ℕ,u=hζ.unit'^n) :
    ∃ b :𝓞 K,ringOfIntegersComplexConj K b=b ∧ Ideal.span {b} = Ideal.span {a} :=by
  have hpo:Odd p :=hp.1.odd_of_ne_two hp_odd
  obtain ⟨n,rfl⟩ :=hclass
  obtain ⟨m,hm⟩ :=exists_pow_eq_pow_two_mul hζ.x5 hpo n
  let μ : (𝓞 K)ˣ:=hζ.unit'^m
  have hμsq: (hζ.unit'^n: (𝓞 K)ˣ) = μ^2:=by
    dsimp [μ]
    calc
      (hζ.unit'^n: (𝓞 K)ˣ) = hζ.unit'^ (2*m) :=hm
      _= (hζ.unit'^m) ^ 2:=by simp [pow_mul,mul_comm]
  let b :𝓞 K:=a* (μ: (𝓞 K)ˣ)
  refine ⟨b,?_,?_⟩
  · have hμconj:complexConj K μ= (μ⁻¹: (𝓞 K)ˣ) :=by
      dsimp [μ]
      simpa using conj_zeta_pow (p:=p) (K:=K) (hζ:=hζ) m
    have hμcoe:
        ringOfIntegersComplexConj K ((μ: (𝓞 K)ˣ) : 𝓞 K) =
          ((μ⁻¹: (𝓞 K)ˣ) : 𝓞 K) :=by
      apply RingOfIntegers.ext
      simpa [coe_ringOfIntegersComplexConj] using hμconj
    have huμinv: (hζ.unit'^n: (𝓞 K)ˣ) * μ⁻¹=μ:=by
      rw [hμsq]
      simp [pow_two,mul_assoc]
    calc
      ringOfIntegersComplexConj K b=
          ringOfIntegersComplexConj K a*
            ringOfIntegersComplexConj K ((μ: (𝓞 K)ˣ) : 𝓞 K) :=by
            dsimp [b]
            simp
      _= ((hζ.unit'^n: (𝓞 K)ˣ) : 𝓞 K) * a* (((μ⁻¹: (𝓞 K)ˣ)) : 𝓞 K) :=by
            dsimp [b]
            simpa [mul_assoc,hμcoe] using congrArg
              (fun x :𝓞 K=>
                x*ringOfIntegersComplexConj K (((μ: (𝓞 K)ˣ) : 𝓞 K))) hu
      _=
          ((((hζ.unit'^n: (𝓞 K)ˣ) * μ⁻¹: (𝓞 K)ˣ) : 𝓞 K) * a) :=by
            simp [mul_assoc,mul_comm]
      _= (μ: (𝓞 K)ˣ) * a:=by rw [huμinv]
      _=b:=by dsimp [b];simp [mul_comm]
  · rw [Ideal.span_singleton_eq_span_singleton]
    dsimp [b]
    exact (associated_mul_unit_right a (μ: (𝓞 K)ˣ) μ.isUnit).symm
include hp_odd in
theorem wu [IsCMField K]
    {hζ:IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (I:Ideal (𝓞 (oMR K)))
    (a:𝓞 K) (u: (𝓞 K)ˣ)
    (hIa:I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) = Ideal.span {a})
    (hu:ringOfIntegersComplexConj K a=u*a)
    (hclass: ∃ n k:ℕ,u= (-1: (𝓞 K)ˣ) ^ k*hζ.unit'^n) :
    ∃ b :𝓞 K,ringOfIntegersComplexConj K b=b ∧ Ideal.span {b} = Ideal.span {a} :=by
  by_cases ha:a=0
  · refine ⟨0,?_,?_⟩ <;> simp [ha]
  · obtain ⟨n,hn⟩ :=
      yd (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ)
        I a u ha hIa hu hclass
    exact xh
      (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ) a u hu ⟨n,hn⟩
theorem zb [IsCMField K]
    (b:𝓞 K) (hb:ringOfIntegersComplexConj K b=b) :
    b ∈ Set.range (algebraMap (𝓞 (oMR K)) (𝓞 K)) :=
  (ringOfIntegersComplexConj_eq_self_iff K b).mp hb
end CyclotomicSetup
end KummerCriterion
end
end Module5
-- Source: KummerCriterion.TotallyRealSubfield.ClassGroup
section Module6
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p:ℕ) [hp:Fact p.Prime] (hp_odd:p ≠ 2)
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
include hp_odd in
theorem r0:IsCMField K :=
  Rat.isCMField (S:= {p}) _ ⟨p,by grind [hp.1.two_le]⟩
theorem sg [IsCMField K] :
    Module.finrank ((oMR K)) K =2:=
  IsQuadraticExtension.finrank_eq_two _ _
theorem uz [IsCMField K] :
    Module.finrank ℚ ((oMR K)) = (p-1) / 2:=by
  have h1:Module.finrank ((oMR K)) K =2:=sg K
  have h2:Module.finrank ℚ K=p-1:=by
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.1.pos),
        Nat.totient_prime hp.1]
  have htow:=Module.finrank_mul_finrank ℚ ((oMR K)) K
  rw [h1,h2] at htow
  exact (Nat.div_eq_of_eq_mul_left (by omega) htow.symm).symm
include hp_odd in
theorem yK [IsCMField K] :
    IsCMField.indexRealUnits K =1:=by
  have hp2:2 < p:=lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hzeta_torsion:hζ.unit' ∈ NumberField.Units.torsion K :=by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p,by omega,?_⟩)
    exact hζ.x5
  have hrange:
      (IsCMField.unitsMulComplexConjInv K).range=
        (powMonoidHom 2 :NumberField.Units.torsion K →*NumberField.Units.torsion K).range:=by
    refine le_antisymm ?_ ?_
    · rintro x ⟨u,rfl⟩
      obtain ⟨m,hm⟩ :=uN hζ u hp2
      refine ⟨⟨hζ.unit'^m,(NumberField.Units.torsion K).pow_mem hzeta_torsion m⟩,?_⟩
      apply Subtype.ext
      simpa [pow_two] using! hm.symm
    · rintro x ⟨u,rfl⟩
      exact ⟨u,by simp [pow_two]⟩
  have hrange_idx: (IsCMField.unitsMulComplexConjInv K).range.index=2:=by
    rw [hrange,IsCyclic.index_powMonoidHom_range,Nat.gcd_eq_right]
    exact even_iff_two_dvd.mp (NumberField.Units.even_torsionOrder K)
  have hmul:IsCMField.indexRealUnits K *2=2:=by
    simpa [hrange_idx] using IsCMField.indexRealUnits_mul_eq K
  omega
noncomputable def h :ℕ:=Fintype.card (ClassGroup (𝓞 K))
noncomputable def hPlus [IsCMField K] : ℕ:=Fintype.card (ClassGroup (𝓞 ((oMR K))))
end CyclotomicSetup
end KummerCriterion
end
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p:ℕ) [hp:Fact p.Prime] (hp_odd:p ≠ 2)
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem vz
    (L:Type*) [Field L] [NumberField L]
    (J:Ideal (𝓞 (oMR L))) :
    (J.map (algebraMap (𝓞 (oMR L)) (𝓞 L))).comap
        (algebraMap (𝓞 (oMR L)) (𝓞 L)) = J:=by
  simpa using Ideal.comap_map_eq_self_of_faithfullyFlat J
theorem wG
    (I:Ideal (𝓞 ((oMR K))))
    (b₀:𝓞 ((oMR K)))
    (hb:I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) =
      Ideal.span {algebraMap (𝓞 ((oMR K))) (𝓞 K) b₀}) :
    I.IsPrincipal:=by
  refine ⟨b₀,?_⟩
  let f :𝓞 ((oMR K)) →+*𝓞 K:=algebraMap (𝓞 ((oMR K))) (𝓞 K)
  have hbc:=congrArg (Ideal.comap f) hb
  have hspan:Ideal.comap f (Ideal.span {f b₀}) = Ideal.span {b₀} :=by
    calc
      Ideal.comap f (Ideal.span {f b₀}) = Ideal.comap f ((Ideal.span {b₀}).map f) :=by
        rw [Ideal.map_span,Set.image_singleton]
      _=Ideal.span {b₀} :=vz K (Ideal.span {b₀})
  calc
    I=Ideal.comap f (I.map f) := (vz K I).symm
    _=Ideal.comap f (Ideal.span {f b₀}) :=hbc
    _=Ideal.span {b₀} :=hspan
include hp_odd in
theorem xu [IsCMField K]
    (I:Ideal (𝓞 ((oMR K))))
    (hI: (I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal:=by
  obtain ⟨a,ha⟩ :=hI
  by_cases hzero:a=0
  · have:I= ⊥ :=by
      rw [← Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 ((oMR K))) (𝓞 K)),ha,hzero]
      simp
    exact this ▸ bot_isPrincipal
  have hIa:I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) = Ideal.span {a} :=ha
  have hIcon:=ideal_map_conj_eq (K:=K) I
  have hIca:I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a} :=by
    rw [← hIcon,hIa,yy]
  obtain ⟨u,hu⟩ :=yk (K:=K) a hzero I hIa hIca
  have hanti:=yT (K:=K) a hzero u hu
  have hζ:IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  obtain ⟨n,k,hclass⟩ :=
    wd
      (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ) u hanti
  obtain ⟨b,hb_conj,hb_span⟩ :=
    wu
      (p:=p) (hp_odd:=hp_odd) (K:=K) (hζ:=hζ) I a u hIa hu ⟨n,k,hclass⟩
  obtain ⟨b₀,hb₀⟩ :=zb (K:=K) b hb_conj
  have hspan:I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) = Ideal.span {b} :=by
    rw [hIa,← hb_span]
  rw [← hb₀] at hspan
  exact wG K I b₀ hspan
include hp_odd in
theorem xD [IsCMField K]
    (I:Ideal (𝓞 ((oMR K))))
    (hI: (I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal:=
  xu (p:=p) (hp_odd:=hp_odd) (K:=K) I hI
abbrev yA [IsCMField K] :
    ClassGroup (𝓞 ((oMR K))) →*ClassGroup (𝓞 K) :=
  ClassGroup.extendedHom (𝓞 ((oMR K))) (𝓞 K)
include hp_odd in
theorem yz [IsCMField K] :
    Function.Injective (yA K) :=by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨I,rfl⟩ :=ClassGroup.mk0_surjective c
  rw [ClassGroup.mk0_eq_one_iff I.2]
  refine xD (p:=p) (hp_odd:=hp_odd) (K:=K) I.1 ?_
  have hne:I.1.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective _ _)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hne),
    ← ClassGroup.extendedHom_mk0]
  exact hc
include hp_odd in
theorem hPlus_dvd_h [IsCMField K] : (KummerCriterion.hPlus K) ∣ (KummerCriterion.h K) :=by
  rw [KummerCriterion.hPlus,KummerCriterion.h,
    ← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_injective (yA K)
    (yz p hp_odd K)
noncomputable def hMinus [IsCMField K] : ℕ:= (KummerCriterion.h K) / (KummerCriterion.hPlus K)
include hp_odd in
theorem xf [IsCMField K] : (KummerCriterion.h K) = (KummerCriterion.hPlus K) * (KummerCriterion.hMinus K) :=by
  rw [hMinus,Nat.mul_div_cancel' (hPlus_dvd_h p hp_odd K)]
end CyclotomicSetup
end KummerCriterion
end
end Module6
-- Source: KummerCriterion.KummerCongruence.Characters
section Module7
noncomputable section
open Perfection PadicInt IsLocalRing
namespace KummerCriterion
variable (p:ℕ) [hp:Fact p.Prime]
noncomputable def rc:ℤ_[p] ⧸ maximalIdeal ℤ_[p] ≃+*ZMod p :=
  PadicInt.residueField
instance maximalIdealQuotient_charP:CharP (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) p :=
  charP_of_injective_ringHom (f:= (rc p).symm.toRingHom)
    (rc p).symm.injective p
instance maximalIdealQuotient_finite:Finite (ℤ_[p] ⧸ maximalIdeal ℤ_[p]) :=
  Finite.of_equiv _ (rc p).symm.toEquiv
noncomputable def r4:ZMod p →*₀ ℤ_[p] :=
  (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])).comp <|
    (PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv.toRingHom.toMonoidWithZeroHom.comp
      (rc p).symm.toRingHom.toMonoidWithZeroHom
variable {p}
@[simp]
lemma teichmuller_zero:r4 p 0=0:=map_zero _
@[simp]
lemma teichmuller_one:r4 p 1=1:=map_one _
@[simp]
lemma zi (a:ZMod p) : PadicInt.toZMod (r4 p a) = a:=by
  change PadicInt.toZMod
    (Perfection.teichmuller₀ p (maximalIdeal ℤ_[p])
      ((PerfectionMap.id p (ℤ_[p] ⧸ maximalIdeal ℤ_[p])).equiv
        ((rc p).symm a))) = a
  rw [PadicInt.toZMod_eq_residueField_comp_residue,RingHom.comp_apply]
  change PadicInt.residueField (Ideal.Quotient.mk _ _) = a
  rw [Perfection.mk_teichmuller₀,PerfectionMap.comp_equiv]
  exact (rc p).apply_symm_apply a
lemma yr {a:ZMod p} (ha:a ≠ 0) : r4 p a^ (p-1) = 1:=by
  rw [← map_pow,ZMod.pow_card_sub_one_eq_one ha,map_one]
lemma yI:Function.Injective (r4 p) :=fun _ _ hab=> by
  simpa using congrArg PadicInt.toZMod hab
lemma yQ (a:ZMod p) : r4 p a^p=r4 p a:=by
  rw [← map_pow,ZMod.pow_card]
lemma ya (a:ZMod p) :
    r4 p a ≡ (a.val:ℤ_[p]) ^ p [SMOD (maximalIdeal ℤ_[p]) ^ 2] :=by
  have h_base:r4 p a ≡ (a.val:ℤ_[p]) [SMOD maximalIdeal ℤ_[p]] :=by
    rw [SModEq.sub_mem,← ker_toZMod,RingHom.mem_ker,map_sub,zi,
      map_natCast,ZMod.natCast_val,ZMod.cast_id,sub_self]
  have hp_mem: ((p:ℕ) : ℤ_[p]) ∈ maximalIdeal ℤ_[p] :=by
    rw [maximalIdeal_eq_span_p];exact Ideal.subset_span rfl
  have h_pow:=h_base.pow_pow_add_one hp_mem 1
  rwa [pow_one,yQ] at h_pow
lemma xN (a:ZMod p) :
    r4 p a- (a.val:ℤ_[p]) ^ p ∈ (maximalIdeal ℤ_[p]) ^ 2:=
  SModEq.sub_mem.mp (ya a)
noncomputable def rp (p:ℕ) [Fact p.Prime] : DirichletCharacter ℤ_[p] p where
  toFun:=r4 p
  map_one':=map_one _
  map_mul':=map_mul _
  map_nonunit':=fun a ha=> by
    rw [show a =0 from by_contra fun hne=> ha (isUnit_iff_ne_zero.mpr hne),teichmuller_zero]
@[simp]
lemma rI (a:ZMod p) : rp p a=r4 p a:=rfl
lemma rH {g: (ZMod p)ˣ}
    (hg_gen: ∀ x: (ZMod p)ˣ,x ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (r4 p (g:ZMod p)) (p-1) :=by
  refine ⟨?_,fun l hl=> ?_⟩
  · rw [← map_pow,← Units.val_pow_eq_pow_val,ZMod.units_pow_card_sub_one_eq_one,
      Units.val_one,map_one]
  · have h_units:g^l=1:=Units.ext <| by
      rw [Units.val_pow_eq_pow_val,Units.val_one]
      exact yI (by rwa [map_pow,map_one])
    have h_order:orderOf g =p-1:=by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen,Nat.card_eq_fintype_card,ZMod.card_units]
    rw [← h_order];exact orderOf_dvd_of_pow_eq_one h_units
lemma ub: (rp p) ^ (p-1) = 1:=by
  ext a
  rw [MulChar.pow_apply_coe,rI,MulChar.one_apply_coe]
  exact yr a.ne_zero
lemma yt:orderOf (rp p) = p-1:=by
  refine Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (ub (p:=p))) ?_
  obtain ⟨g,hg_gen⟩ :=IsCyclic.exists_generator (α:= (ZMod p)ˣ)
  have h_apply:=congrArg (fun χ :DirichletCharacter ℤ_[p] p => χ (g:ZMod p))
    (pow_orderOf_eq_one (rp p))
  simp only [MulChar.pow_apply_coe,rI,MulChar.one_apply_coe] at h_apply
  exact (rH hg_gen).2 _ h_apply
lemma yW (hp_odd:p ≠ 2) : r4 p (-1) = -1:=by
  have h_sq:r4 p (-1:ZMod p) ^ 2=1:=by
    rw [sq,← map_mul,neg_one_mul,neg_neg,map_one]
  rcases sq_eq_one_iff.mp h_sq with h1 | h_neg
  · have:Fact (2 < p) := ⟨lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)⟩
    exact absurd (by simpa using congrArg PadicInt.toZMod h1) ZMod.neg_one_ne_one
  · exact h_neg
lemma zl (hp_odd:p ≠ 2) (i:ℕ) :
    ((rp p) ^ i) (-1:ZMod p) = (-1:ℤ_[p]) ^ i:=by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [pow_zero,pow_zero];exact MulChar.one_apply isUnit_one.neg
  · rw [MulChar.pow_apply' _ hi.ne',rI,yW hp_odd]
end KummerCriterion
end
end Module7
-- Source: KummerCriterion.KummerCongruence.BernoulliGeneralized
section Module8
noncomputable section
open Polynomial
namespace KummerCriterion
variable {N:ℕ} {R:Type*} [CommRing R] [Algebra ℚ R]
noncomputable def qf [NeZero N]
    (χ:DirichletCharacter R N) (n:ℕ) : R:=
  (N:R) ^ (n-1) *
    ∑ a :ZMod N,χ a*
      algebraMap ℚ R ((Polynomial.bernoulli n).eval ((a.val:ℚ) / N))
lemma vU [IsDomain R] [NeZero N]
    {χ:DirichletCharacter R N} (hχ:χ ≠ 1) :
    qf χ 1=
      ∑ a :ZMod N,χ a*algebraMap ℚ R ((a.val:ℚ) / N) :=by
  unfold qf
  rw [show (1-1:ℕ) = 0 from rfl,pow_zero,one_mul,Polynomial.bernoulli_one]
  simp_rw [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,map_sub,mul_sub]
  rw [Finset.sum_sub_distrib]
  conv_lhs=>
    rw [show (∑ a :ZMod N,χ a*algebraMap ℚ R (2⁻¹:ℚ))
          =algebraMap ℚ R (2⁻¹:ℚ) * ∑ a :ZMod N,χ a from by
      rw [Finset.mul_sum];exact Finset.sum_congr rfl fun a _=> mul_comm _ _]
  rw [MulChar.sum_eq_zero_of_ne_one hχ,mul_zero,sub_zero]
lemma rM [IsDomain R] [NeZero N]
    {χ:DirichletCharacter R N} (hχ:χ ≠ 1) :
    (N:R) * qf χ 1=
      ∑ a :ZMod N,χ a* (a.val:R) :=by
  rw [vU hχ,Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _=> ?_
  have hN_R: (N:R) = algebraMap ℚ R (N:ℚ) :=by push_cast;rfl
  rw [hN_R,show algebraMap ℚ R ((N:ℚ)) * (χ a *algebraMap ℚ R ((a.val:ℚ) / N)) =
        χ a * (algebraMap ℚ R (N:ℚ) * algebraMap ℚ R ((a.val:ℚ) / N)) from by ring,
    ← map_mul,mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  push_cast;rfl
noncomputable def q7 (p:ℕ) [Fact p.Prime] : DirichletCharacter ℚ_[p] p :=
  (rp p).ringHomComp PadicInt.Coe.ringHom
variable (p:ℕ) [Fact p.Prime]
lemma r6 (n:ℕ) :
    (q7 p) ^ n=
      ((rp p) ^ n).ringHomComp PadicInt.Coe.ringHom:=by
  simpa [q7] using
    (MulChar.ringHomComp_pow (χ:=rp p) (f:=PadicInt.Coe.ringHom) (n:=n))
lemma xx:
    (q7 p) ^ (p-1) = 1:=by
  rw [r6 (p:=p) (n:=p-1)]
  simp [ub (p:=p)]
lemma s6:
    orderOf (q7 p) = p-1:=by
  refine Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (xx (p:=p))) ?_
  have hpowQ':
      ((rp p) ^ orderOf (q7 p)).ringHomComp
          PadicInt.Coe.ringHom=1:=by
    rw [← r6 (p:=p) (n:=orderOf (q7 p))]
    simp only [pow_orderOf_eq_one]
  have hpowZ: (rp p) ^ orderOf (q7 p) = 1:=
    (MulChar.ringHomComp_eq_one_iff (f:=PadicInt.Coe.ringHom)
      (hf:=fun _ _ h => Subtype.coe_injective h)).mp hpowQ'
  simpa [yt (p:=p)] using orderOf_dvd_of_pow_eq_one hpowZ
lemma zw (n:ℕ) :
    (q7 p) ^ n=1 ↔ (p-1) ∣ n:=by
  refine ⟨fun hpow=> ?_,?_⟩
  · simpa [s6 (p:=p)] using orderOf_dvd_of_pow_eq_one hpow
  · rintro ⟨m,rfl⟩
    rw [← s6 (p:=p),pow_mul,pow_orderOf_eq_one,one_pow]
lemma sI {n:ℕ} (hn: ¬ (p-1) ∣ n) :
    (q7 p) ^ n ≠ 1:=
  fun hpow=> hn ((zw (p:=p) n).mp hpow)
omit [Algebra ℚ R] in
lemma uj
    {p:ℕ} [Fact p.Prime] (hp_odd:p ≠ 2) :
    ∃ z :ℤ_[p],
      qf ((q7 p) ^ (p-2)) 1 =
        ((p-1:ℚ_[p]) / p) + z:=by
  have hp:Nat.Prime p :=Fact.out
  have hp_gt2:2 < p:=lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  let ωZ:DirichletCharacter ℤ_[p] p := (rp p) ^ (p-2)
  let ωQ:DirichletCharacter ℚ_[p] p := (q7 p) ^ (p-2)
  let S :ℤ_[p] := ∑ a:ZMod p,ωZ a * (a.val:ℤ_[p])
  change ∃ z:ℤ_[p],qf ωQ 1 = ((p-1:ℚ_[p]) / p) + z
  have hp_sub_two_not_dvd: ¬ (p-1) ∣ p-2:=Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hωQ_def:ωQ=ωZ.ringHomComp PadicInt.Coe.ringHom:=
    r6 (p:=p) (n:=p-2)
  have hωQ_ne_one:ωQ ≠ 1:=
    sI (p:=p) hp_sub_two_not_dvd
  have hB:=rM (R:=ℚ_[p]) (N:=p) (χ:=ωQ) hωQ_ne_one
  have hS_coe: ((S:ℤ_[p]) : ℚ_[p]) = ∑ a :ZMod p,ωQ a * (a.val:ℚ_[p]) :=by
    rw [hωQ_def];dsimp [S];rw [PadicInt.coe_sum];rfl
  have hB': (p:ℚ_[p]) * qf ωQ 1 = (S:ℚ_[p]) :=by rw [hB,← hS_coe]
  have hpow_ne_zero:p-2 ≠ 0:=by omega
  have hterm: ∀ a:ZMod p,
      PadicInt.toZMod (ωZ a * (a.val:ℤ_[p])) = if a =0 then 0 else 1 :=by
    intro a
    rcases eq_or_ne a 0 with rfl | ha
    · dsimp [ωZ];simp
    · have hω:PadicInt.toZMod (ωZ a) = a^ (p-2) :=by
        dsimp [ωZ];rw [MulChar.pow_apply' _ hpow_ne_zero,map_pow,rI,
          zi]
      have hval:PadicInt.toZMod (a.val:ℤ_[p]) = a:=by simp
      rw [map_mul,hω,hval,if_neg ha]
      calc
        a^ (p-2) * a=a^ ((p-2) + 1) :=by rw [mul_comm,pow_succ']
        _=a^ (p-1) :=by congr;omega
        _=1:=ZMod.pow_card_sub_one_eq_one ha
  have hS_mod:PadicInt.toZMod S = (p-1:ZMod p) :=by
    have hsplit:
        (∑ a :ZMod p,if a =0 then 0 else 1) =
          (Finset.univ.erase (0:ZMod p)).sum (fun _ => (1:ZMod p)) :=by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0),if_pos rfl,add_zero]
      refine Finset.sum_congr rfl fun a ha=> ?_
      simp [(Finset.mem_erase.mp ha).1]
    calc
      PadicInt.toZMod S = ∑ a:ZMod p,if a =0 then 0 else 1 :=by
        dsimp [S];rw [map_sum];exact Finset.sum_congr rfl fun a _=> hterm a
      _= (Finset.univ.erase (0:ZMod p)).sum (fun _ => (1:ZMod p)) :=hsplit
      _= (p-1:ZMod p) :=by
        have hcard: (Finset.univ.erase (0:ZMod p)).card=p-1:=by simp [ZMod.card p]
        rw [Finset.sum_const,hcard,nsmul_eq_mul,mul_one,Nat.cast_sub hp.one_le]
        simp
  have hS_mem:S- (p-1:ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=by
    have hspec:=PadicInt.toZMod_spec (p:=p) S
    rw [hS_mod] at hspec
    have hcast: (ZMod.cast ((p:ZMod p) - 1) : ℤ_[p]) = (p-1:ℤ_[p]) :=by
      have hrepr: ((p:ZMod p) - 1) = ((p-1:ℕ) : ZMod p) :=by
        rw [Nat.cast_sub hp.one_le];simp
      have hval0: ((p:ZMod p) - 1).val=p-1:=by
        rw [hrepr];exact ZMod.val_natCast_of_lt (by omega)
      rw [ZMod.cast_eq_val,hval0,Nat.cast_sub hp.one_le,Nat.cast_one]
    rwa [hcast] at hspec
  rw [PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton] at hS_mem
  rcases hS_mem with ⟨z,hz⟩
  have hzQ_sub: (S:ℚ_[p]) - (p-1:ℚ_[p]) = (p:ℚ_[p]) * z:=by
    simpa using congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hz
  have hpQ_ne_zero: (p:ℚ_[p]) ≠ 0:=by exact_mod_cast hp.ne_zero
  refine ⟨z,(mul_right_inj' hpQ_ne_zero).mp ?_⟩
  calc
    (p:ℚ_[p]) * qf ωQ 1 = (S:ℚ_[p]) :=hB'
    _= (p-1:ℚ_[p]) + (p:ℚ_[p]) * z:=by
      simpa [add_comm] using sub_eq_iff_eq_add.mp hzQ_sub
    _= (p:ℚ_[p]) * (((p-1:ℚ_[p]) / p) + z) :=by
      rw [mul_add,mul_div_cancel₀ _ hpQ_ne_zero]
theorem u1 {p:ℕ} [hp:Fact p.Prime]
    (hp_odd:p ≠ 2) (k:ℕ) (hk:k < p-1) :
    ∃ z :ℤ_[p],(bernoulli k :ℚ_[p]) = (z:ℚ_[p]) :=by
  have hp:p.Prime:=hp.out
  have hp_gt:2 < p:=lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  revert hk
  induction k using Nat.strong_induction_on with
  | _ k ih=>
  intro hk
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · exact ⟨1,by simp [_root_.bernoulli_zero]⟩
  have hkp1_lt:k+1 < p:=by omega
  have h_sum:=_root_.sum_bernoulli (k+1)
  rw [if_neg (by omega:k+1 ≠ 1),Finset.sum_range_succ] at h_sum
  have h_choose_k: (Nat.choose (k+1) k :ℚ) = (k+1:ℚ) :=by
    rw [Nat.choose_succ_self_right];push_cast;rfl
  rw [h_choose_k] at h_sum
  have h_bern_rat: ((k+1:ℕ) : ℚ) * _root_.bernoulli k =
      -∑ j ∈ Finset.range k,(Nat.choose (k+1) j :ℚ) * _root_.bernoulli j :=by
    push_cast;linarith [h_sum]
  have hj_wit: ∀ j,j < k-> ∃ z:ℤ_[p],(bernoulli j :ℚ_[p]) = (z:ℚ_[p]) :=
    fun j hj=> ih j hj (Nat.lt_of_lt_of_le hj (Nat.le_of_lt hk))
  let z_of:ℕ-> ℤ_[p] :=fun j =>
    if h :j < k then (hj_wit j h).choose else 0
  have hz_of: ∀ j,j < k-> (bernoulli j :ℚ_[p]) = ((z_of j :ℤ_[p]) : ℚ_[p]) :=by
    intro j hj;simp only [z_of,dif_pos hj];exact (hj_wit j hj).choose_spec
  let S :ℤ_[p] := ∑ j ∈ Finset.range k,(Nat.choose (k+1) j :ℤ_[p]) * z_of j
  have hS_coe: (S:ℚ_[p]) =
      ∑ j ∈ Finset.range k,(Nat.choose (k+1) j :ℚ_[p]) * (bernoulli j :ℚ_[p]) :=by
    simp only [S,PadicInt.coe_sum]
    refine Finset.sum_congr rfl fun j hj=> ?_
    rw [PadicInt.coe_mul,PadicInt.coe_natCast,hz_of j (Finset.mem_range.mp hj)]
  have h_kp1_unit:IsUnit ((k+1:ℕ) : ℤ_[p]) :=by
    rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkp1_lt)
  refine ⟨-(h_kp1_unit.unit⁻¹: (ℤ_[p])ˣ).val*S,?_⟩
  have h_bern_Qp: ((k+1:ℕ) : ℚ_[p]) * ((_root_.bernoulli k :ℚ) : ℚ_[p]) =
      -∑ j ∈ Finset.range k,
        (Nat.choose (k+1) j :ℚ_[p]) * ((_root_.bernoulli j :ℚ) : ℚ_[p]) :=by
    have h_cast:=congrArg (fun q :ℚ=> (q:ℚ_[p])) h_bern_rat
    push_cast at h_cast ⊢
    exact h_cast
  rw [← hS_coe] at h_bern_Qp
  have h_coe_unit: ((h_kp1_unit.unit:ℤ_[p]) : ℚ_[p]) = ((k+1:ℕ) : ℚ_[p]) :=rfl
  have h_unit_mul_inv: ((h_kp1_unit.unit:ℤ_[p]) : ℚ_[p]) *
      ((h_kp1_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℚ_[p]) = 1:=by
    rw [← PadicInt.coe_mul,← Units.val_mul,mul_inv_cancel];rfl
  calc (bernoulli k :ℚ_[p])
      = (1:ℚ_[p]) * (bernoulli k :ℚ_[p]) :=by ring
    _= (((h_kp1_unit.unit:ℤ_[p]) : ℚ_[p]) *
          ((h_kp1_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℚ_[p])) * (bernoulli k :ℚ_[p]) :=by
        rw [h_unit_mul_inv]
    _= ((h_kp1_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℚ_[p]) *
          (((h_kp1_unit.unit:ℤ_[p]) : ℚ_[p]) * (bernoulli k :ℚ_[p])) :=by ring
    _= ((h_kp1_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℚ_[p]) *
          (((k+1:ℕ) : ℚ_[p]) * (bernoulli k :ℚ_[p])) :=by rw [h_coe_unit]
    _= ((h_kp1_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℚ_[p]) * (- (S:ℚ_[p])) :=by
        rw [h_bern_Qp]
    _= ((-(h_kp1_unit.unit⁻¹: (ℤ_[p])ˣ).val*S:ℤ_[p]) : ℚ_[p]) :=by
        rw [PadicInt.coe_mul,PadicInt.coe_neg];ring
theorem rE {p n :ℕ} [hp:Fact p.Prime]
    (hp_odd:p ≠ 2) (hn:n < p-1) :
    ¬ p ∣ (_root_.bernoulli n).den:=by
  obtain ⟨z,hz⟩ :=u1 hp_odd n hn
  have hnorm: ‖((_root_.bernoulli n :ℚ) : ℚ_[p])‖ ≤ 1:=by rw [hz];exact z.2
  have hunit:IsUnit (((_root_.bernoulli n).den:ℕ) : ℤ_[p]) :=
    PadicInt.isUnit_den _ hnorm
  rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff] at hunit
  exact hp.out.coprime_iff_not_dvd.mp hunit
lemma yp (n:ℕ) (hn:n ≠ 0) :
    ((-(1/2:ℚ)) * (((_root_.bernoulli n :ℚ) / n:ℚ))) *
        (2* (_root_.bernoulli n).den*n:ℚ) =
      -(_root_.bernoulli n).num:=by
  calc
    ((-(1/2:ℚ)) * (((_root_.bernoulli n :ℚ) / n:ℚ))) *
        (2* (_root_.bernoulli n).den*n:ℚ) =
        -((((_root_.bernoulli n :ℚ) / n:ℚ) * ((_root_.bernoulli n).den*n:ℚ))) :=by
          ring
    _= -((_root_.bernoulli n :ℚ) * ((_root_.bernoulli n).den:ℚ)) :=by
      have hnQ: (n:ℚ) ≠ 0:=by exact_mod_cast hn
      field_simp [hnQ]
    _= -(_root_.bernoulli n).num:=by
      simp
lemma s8 {p:ℕ} [hp:Fact p.Prime] (hp_odd:p ≠ 2)
    {n:ℕ} (hn_pos:0 < n) (hn_lt:n < p)
    (hden: ¬ p ∣ (_root_.bernoulli n).den) :
    ∃ a :ℤ_[p],
      (a:ℚ_[p]) =
        (-(1/2:ℚ_[p])) * ((((_root_.bernoulli n :ℚ) / n:ℚ) : ℚ_[p])) ∧
      (IsUnit a ↔ ¬ (p:ℤ) ∣ (_root_.bernoulli n).num) :=by
  let D :ℕ:=2* (_root_.bernoulli n).den*n
  have htwo_not_dvd: ¬ p ∣ 2:=
    Nat.not_dvd_of_pos_of_lt (by positivity) (by omega)
  have hn_not_dvd: ¬ p ∣ n:=Nat.not_dvd_of_pos_of_lt hn_pos hn_lt
  have hD_coprime:p.Coprime D :=by
    simpa [D,Nat.mul_assoc] using
      (hp.out.coprime_iff_not_dvd.mpr htwo_not_dvd).mul_right <|
        (hp.out.coprime_iff_not_dvd.mpr hden).mul_right <|
        (hp.out.coprime_iff_not_dvd.mpr hn_not_dvd)
  have hD_unit:IsUnit ((D:ℕ) : ℤ_[p]) :=by
    rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
    simpa [Nat.coprime_comm] using hD_coprime
  let a :ℤ_[p] := -((hD_unit.unit⁻¹: (ℤ_[p])ˣ).val) * (_root_.bernoulli n).num
  refine ⟨a,?_,?_⟩
  · have hD_ne: (D:ℚ_[p]) ≠ 0:=by
      exact_mod_cast (show D ≠ 0 by dsimp [D];positivity)
    apply (mul_left_inj' hD_ne).mp
    have hunit_mul: ((((hD_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℚ_[p])) * (D:ℚ_[p])) = 1:=by
      change ((((hD_unit.unit⁻¹: (ℤ_[p])ˣ) * hD_unit.unit).val:ℚ_[p])) = 1
      simp
    have hfactor_mul:
        ((-(1/2:ℚ_[p])) * ((((_root_.bernoulli n :ℚ) / n:ℚ) : ℚ_[p]))) *
            (D:ℚ_[p]) =
          -((_root_.bernoulli n).num:ℚ_[p]) :=by
      simpa [D] using
        congrArg (fun q :ℚ=> (q:ℚ_[p]))
          (yp (n:=n) hn_pos.ne')
    have ha_mul: (((a:ℤ_[p]) : ℚ_[p])) * (D:ℚ_[p]) =
        -((_root_.bernoulli n).num:ℚ_[p]) :=by
      have: (((a:ℤ_[p]) : ℚ_[p])) * (D:ℚ_[p])
          = -((_root_.bernoulli n).num:ℚ_[p]) *
            (((((hD_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℚ_[p])) * (D:ℚ_[p]))) :=by
        simp [a,mul_left_comm,mul_comm]
      rw [this,hunit_mul,mul_one]
    exact ha_mul.trans hfactor_mul.symm
  · have hcoef_unit:IsUnit (-((hD_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p])) :=
      (hD_unit.unit⁻¹).isUnit.neg
    have ha_unit:IsUnit a ↔ IsUnit (((_root_.bernoulli n).num:ℤ_[p])) :=by
      rw [show a = -((hD_unit.unit⁻¹: (ℤ_[p])ˣ).val) * ((_root_.bernoulli n).num:ℤ_[p])
        by rfl,IsUnit.mul_iff]
      simp [hcoef_unit]
    rw [ha_unit,← not_iff_not,PadicInt.not_isUnit_iff,PadicInt.norm_intCast_lt_one_iff]
    simp
end KummerCriterion
end
end Module8
-- Source: KummerCriterion.GaussSum.Basic
section Module9
noncomputable section
namespace KummerCriterion
open scoped BigOperators ComplexConjugate
section GaussSum
variable (p:ℕ) [hp:Fact p.Prime]
theorem xE
    {χ:DirichletCharacter ℂ p} (hχ:χ ≠ 1) :
    gaussSum χ (ZMod.stdAddChar (N:=p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) =
      χ (-1) * p:=by
  have h_prim: (ZMod.stdAddChar:AddChar (ZMod p) ℂ).IsPrimitive:=
    ZMod.isPrimitive_stdAddChar p
  have h_card: (Fintype.card (ZMod p) : ℂ) = p:=by
    rw [ZMod.card]
  have h1:gaussSum χ (ZMod.stdAddChar (N:=p)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))⁻¹= (p:ℂ) :=by
    rw [← h_card];exact gaussSum_mul_gaussSum_eq_card hχ h_prim
  have h2:=mul_gaussSum_inv_eq_gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))
  have h_neg_unit:IsUnit (-1:ZMod p) :=isUnit_one.neg
  have h_sq:χ (-1) * χ (-1) = 1:=by
    rw [← map_mul,show (-1:ZMod p) * -1=1 from by ring,MulChar.map_one]
  have h_ne:χ (-1) ≠ 0:=fun h => by
    rw [h,mul_zero] at h_sq;exact zero_ne_one h_sq
  have h_inv_neg_one:χ⁻¹ (-1) = χ (-1) :=by
    have h_inv_mul:χ⁻¹ (-1) * χ (-1) = 1:=by
      rw [← MulChar.mul_apply,MulChar.inv_mul,MulChar.one_apply h_neg_unit]
    exact mul_right_cancel₀ h_ne (h_inv_mul.trans h_sq.symm)
  rw [h_inv_neg_one] at h2
  have h3:χ (-1) * (gaussSum χ (ZMod.stdAddChar (N:=p)) *
      gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))⁻¹) = χ (-1) * p:=by rw [h1]
  rw [show χ (-1) * (gaussSum χ (ZMod.stdAddChar (N:=p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))⁻¹) =
      gaussSum χ (ZMod.stdAddChar (N:=p)) *
        (χ (-1) * gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p))⁻¹) from by ring,h2] at h3
  exact h3
theorem DirichletCharacter.isPrimitive_of_ne_one
    {χ:DirichletCharacter ℂ p} (hχ:χ ≠ 1) : χ.IsPrimitive:=by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp.out).mp χ.conductor_dvd_level with h | h
  · exact absurd ((DirichletCharacter.factorsThrough_one_iff χ).mp
      (h ▸ χ.factorsThrough_conductor)) hχ
  · exact h
noncomputable def q3:DirichletCharacter ℂ p:=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
theorem zx:
    (q3 p).IsQuadratic:=by
  simpa [q3] using
    (quadraticChar_isQuadratic (F:=ZMod p)).comp (Int.castRingHom ℂ)
theorem ri (hp₂:p ≠ 2) :
    q3 p ≠ 1 :=by
  simpa [q3] using
    (MulChar.ringHomComp_ne_one_iff
      (f:=Int.castRingHom ℂ) (hf:=Int.cast_injective)).2
      (quadraticChar_ne_one (F:=ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂))
theorem rK:
    (q3 p)⁻¹=q3 p :=by
  simpa using
    (zx (p:=p)).inv
theorem wQ (hp₂:p ≠ 2) :
    q3 p (-1) = ZMod.χ₄ p :=by
  rw [q3,MulChar.ringHomComp_apply,
    quadraticChar_neg_one (F:=ZMod p) ((ZMod.ringChar_zmod_n p).substr hp₂),ZMod.card]
  rfl
theorem um (hp₂:p ≠ 2) :
    q3 p (-1) = if p %4=1 then 1 else-1:=by
  have hp_odd:p%2=1:=by
    rcases hp.out.odd_of_ne_two hp₂ with ⟨k,hk⟩
    omega
  rw [wQ (p:=p) hp₂,ZMod.χ₄_nat_eq_if_mod_four]
  simp [hp_odd]
theorem vu (hp₂:p ≠ 2)
    (hp₄:p%4=1) :
    q3 p (-1) = 1:=by
  simp [um (p:=p) hp₂,hp₄]
theorem rg (hp₂:p ≠ 2)
    (hp₄:p%4=3) :
    q3 p (-1) = -1:=by
  simp [um (p:=p) hp₂,hp₄]
end GaussSum
end KummerCriterion
end
end Module9
-- Source: KummerCriterion.GaussSum.SignInvariant.Trace
section Module10
noncomputable section
namespace KummerCriterion
open scoped BigOperators ComplexConjugate
section SignInvariant
variable (p:ℕ) [hp:Fact p.Prime]
theorem zr (x k :ZMod p) :
    ZMod.dft (Pi.basisFun ℂ (ZMod p) x) k =
      ZMod.stdAddChar (N:=p) (-(x*k)) :=by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul,Pi.basisFun_apply,Pi.single_apply,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ x (fun y :ZMod p => ZMod.stdAddChar (N:=p) (-(y*k)))]
  simp
theorem yh:
    ZMod.dft (Pi.basisFun ℂ (ZMod p) (0:ZMod p)) = fun _ :ZMod p => (1:ℂ) :=by
  ext k
  rw [zr (p:=p) (x:= (0:ZMod p)) (k:=k)]
  simp
theorem yO (k:ZMod p) :
    ZMod.dft (fun _ :ZMod p => (1:ℂ)) k =if k =0 then p else 0 :=by
  by_cases hk:k=0
  · subst hk
    rw [ZMod.dft_apply_zero]
    simp
  · rw [ZMod.dft_apply,if_neg hk]
    have hne: ((ZMod.stdAddChar:AddChar (ZMod p) ℂ).mulShift (-k)) ≠ 1:=by
      intro hshift
      have heval: (ZMod.stdAddChar (N:=p)) (-k) = 1:=by
        simpa [AddChar.mulShift_apply] using
          congrArg (fun ψ :AddChar (ZMod p) ℂ => ψ 1) hshift
      have hzero: (ZMod.stdAddChar (N:=p)) (0:ZMod p) = 1:=AddChar.map_zero_eq_one _
      have hkzero: (-k:ZMod p) = 0:=ZMod.injective_stdAddChar (heval.trans hzero.symm)
      exact hk (by simpa using hkzero)
    have hsum: ∑ j:ZMod p,((ZMod.stdAddChar:AddChar (ZMod p) ℂ).mulShift (-k)) j =0:=
      AddChar.sum_eq_zero_of_ne_one hne
    simpa [AddChar.mulShift_apply,mul_comm,mul_left_comm,mul_assoc] using hsum
theorem xH:
    ZMod.dft (fun _ :ZMod p => (1:ℂ)) =
      (p:ℂ) • Pi.basisFun ℂ (ZMod p) (0:ZMod p) :=by
  ext k
  by_cases hk:k=0
  · subst hk
    simp [yO (p:=p),Pi.basisFun_apply]
  · simp [yO (p:=p),hk,Pi.basisFun_apply]
theorem zA {χ:DirichletCharacter ℂ p}
    (hχ:χ ≠ 1) :
    ZMod.dft χ =
      (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N:=p))) •
        (((χ⁻¹:DirichletCharacter ℂ p) : ZMod p → ℂ)) :=by
  have hprim:χ.IsPrimitive:=DirichletCharacter.isPrimitive_of_ne_one (p:=p) hχ
  ext k
  simp only [Pi.smul_apply,smul_eq_mul]
  calc
    ZMod.dft χ k=χ⁻¹ (-k) * gaussSum χ (ZMod.stdAddChar (N:=p)) :=
      DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ:=χ) hprim k
    _= (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N:=p))) * χ⁻¹ k :=by
      rw [show χ⁻¹ (-k) = χ⁻¹ (-1) * χ⁻¹ k by
        calc
          χ⁻¹ (-k) = χ⁻¹ ((-1:ZMod p) * k) :=by congr;ring
          _=χ⁻¹ (-1) * χ⁻¹ k :=by rw [map_mul]]
      ring
noncomputable def qu:DirichletCharacter ℂ p ≃* (ZMod p)ˣ:=by
  letI:NeZero p := ⟨hp.out.ne_zero⟩
  exact (MulChar.mulEquiv_units (ZMod p) ℂ).some
omit hp in
theorem zF {χ:DirichletCharacter ℂ p}
    (hχself:χ=χ⁻¹) : χ^2=1:=by
  simpa [pow_two] using congrArg (fun ψ :DirichletCharacter ℂ p=> ψ *χ) hχself
theorem xr {χ:DirichletCharacter ℂ p}
    (hχself:χ=χ⁻¹) :
    (((qu (p:=p) χ : (ZMod p)ˣ) : ZMod p) ^ 2) = 1:=by
  have hsq_units: (qu (p:=p) χ : (ZMod p)ˣ) ^ 2=1:=by
    rw [← map_pow]
    simp [zF (p:=p) (χ:=χ) hχself]
  simpa [Units.val_pow_eq_pow_val] using
    congrArg (fun u : (ZMod p)ˣ=> ((u:ZMod p))) hsq_units
theorem wi {χ:DirichletCharacter ℂ p}
    (hχself:χ=χ⁻¹) :
    ((qu (p:=p) χ : (ZMod p)ˣ) : ZMod p) = 1 ∨
      ((qu (p:=p) χ : (ZMod p)ˣ) : ZMod p) = -1:=
  sq_eq_one_iff.mp <|
    xr (p:=p) (χ:=χ) hχself
theorem rS {χ:DirichletCharacter ℂ p}
    (hχself:χ=χ⁻¹) :
    qu (p:=p) χ =1 ∨
      qu (p:=p) χ = (-1: (ZMod p)ˣ) :=by
  rcases wi (p:=p) (χ:=χ) hχself with hχ | hχ
  · left
    apply Units.ext
    simpa using hχ
  · right
    apply Units.ext
    simpa using hχ
theorem vM (hp₂:p ≠ 2) :
    qu (p:=p) (q3 p) = (-1: (ZMod p)ˣ) :=by
  rcases rS (p:=p)
      (χ:=q3 p) (rK (p:=p)).symm with hχ | hχ
  · exact absurd ((qu (p:=p)).injective (by simpa using hχ))
      (ri (p:=p) hp₂)
  · exact hχ
theorem sC (hp₂:p ≠ 2)
    {χ:DirichletCharacter ℂ p} (hχself:χ=χ⁻¹) :
    χ=1 ∨ χ=q3 p :=by
  rcases rS (p:=p) (χ:=χ)
      hχself with hχ | hχ
  · left
    exact (qu (p:=p)).injective (by simpa using hχ)
  · right
    exact (qu (p:=p)).injective (by
      calc
        qu (p:=p) χ = (-1: (ZMod p)ˣ) :=hχ
        _=qu (p:=p) (q3 p) :=by
              symm
              exact vM (p:=p) hp₂)
theorem sm (hp₂:p ≠ 2)
    {χ:DirichletCharacter ℂ p} (hχ:χ ≠ 1) (hχself:χ=χ⁻¹) :
    χ=q3 p :=by
  rcases sC (p:=p) hp₂ hχself with hχ1 | hχquad
  · exact (hχ hχ1).elim
  · exact hχquad
end SignInvariant
end KummerCriterion
end
end Module10
-- Source: KummerCriterion.GaussSum.SignInvariant.Operator
section Module11
noncomputable section
namespace KummerCriterion
open scoped BigOperators ComplexConjugate
section SignInvariant
variable (p:ℕ) [hp:Fact p.Prime]
noncomputable def qn: (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  ((Real.sqrt p :ℂ)⁻¹) •
    ((ZMod.dft: (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap)
theorem u5 (Φ:ZMod p → ℂ) (x:ZMod p) :
    qn p Φ x = (Real.sqrt p :ℂ)⁻¹*ZMod.dft Φ x:=by
  simp [qn,smul_eq_mul]
theorem yC (Φ:ZMod p → ℂ) (x:ZMod p) :
    qn p (qn p Φ) x =Φ (-x) :=by
  have hp_nonneg: (0:ℝ) ≤ p:=by
    exact_mod_cast Nat.zero_le p
  have hsqrt_ne_real: (Real.sqrt p :ℝ) ≠ 0:=
    Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
  have hsqrt_ne: (Real.sqrt p :ℂ) ≠ 0:=by
    exact_mod_cast hsqrt_ne_real
  have hscalar:
      (Real.sqrt p :ℂ)⁻¹* ((Real.sqrt p :ℂ)⁻¹* (p:ℂ)) = 1:=by
    field_simp [hsqrt_ne]
    have hsqrt_sq: ((Real.sqrt p :ℂ) ^ 2) = (p:ℂ) :=by
      exact_mod_cast (Real.sq_sqrt hp_nonneg)
    simpa [pow_two] using hsqrt_sq.symm
  calc
    qn p (qn p Φ) x
        = ((Real.sqrt p :ℂ)⁻¹* ((Real.sqrt p :ℂ)⁻¹* (p:ℂ))) * Φ (-x) :=by
            simp [qn,ZMod.dft_dft,mul_assoc,mul_left_comm,mul_comm]
    _=Φ (-x) :=by simp [hscalar]
noncomputable def wH:Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k=> ZMod.stdAddChar (N:=p) (-(x*k))
noncomputable def qN:Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k=> (Real.sqrt p :ℂ)⁻¹*ZMod.stdAddChar (N:=p) (-(x*k))
theorem wo:
    qN p = ((Real.sqrt p :ℂ)⁻¹) • wH p :=by
  ext x k
  simp [qN,wH,smul_eq_mul]
theorem vP:
    LinearMap.toMatrix (Pi.basisFun ℂ (ZMod p)) (Pi.basisFun ℂ (ZMod p))
        (qn p) =
      qN p :=by
  ext x k
  rw [LinearMap.toMatrix_apply,Pi.basisFun_repr]
  rw [u5]
  simpa [qN,mul_comm] using
    congrArg (fun z :ℂ=> (Real.sqrt p :ℂ)⁻¹*z)
      (zr (p:=p) (x:=k) (k:=x))
theorem vY:
    LinearMap.det (qn p) = Matrix.det (qN p) :=by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (ZMod p)) (qn p),
    vP]
noncomputable def st:ZMod p ≃ Fin p :=by
  exact (ZMod.finEquiv p).symm.toEquiv
theorem uk (i:Fin p) : (st (p:=p)).symm i = (i:ZMod p) :=by
  cases p with
  | zero=>
      exact (hp.out.ne_zero rfl).elim
  | succ n =>
      apply Fin.ext
      simpa [ZMod.finEquiv] using! (ZMod.val_natCast_of_lt i.is_lt).symm
noncomputable def rZ:Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (st (p:=p)) (st (p:=p)) (qN p)
noncomputable def u3:Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (st (p:=p)) (st (p:=p)) (wH p)
theorem vy:
    rZ p = ((Real.sqrt p :ℂ)⁻¹) • u3 p :=by
  ext i j
  simp [rZ,u3,wo]
theorem uy:
    Matrix.det (qN p) = Matrix.det (rZ p) :=by
  change Matrix.det (qN p) =
    Matrix.det (Matrix.reindex (st (p:=p)) (st (p:=p))
      (qN p))
  exact (Matrix.det_reindex_self (st (p:=p)) (qN p)).symm
end SignInvariant
end KummerCriterion
end
end Module11
-- Source: KummerCriterion.GaussSum.SignInvariant.BlockDeterminant
section Module12
noncomputable section
namespace KummerCriterion
section SignInvariant
open scoped BigOperators ComplexConjugate
variable (p:ℕ) [hp:Fact p.Prime]
def rf:ZMod p → ℂ :=
  Pi.basisFun ℂ (ZMod p) (0:ZMod p)
def rF: (ZMod p → ℂ) →ₗ[ℂ] ((ZMod p)ˣ → ℂ) where
  toFun Φ u:=Φ u
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
def qK (χ:DirichletCharacter ℂ p) : (ZMod p)ˣ →*ℂ:=
  (Units.coeHom ℂ).comp χ.toUnitHom
theorem wU:
    Function.Injective (qK (p:=p)) :=fun χ ψ hχψ=>
  (DirichletCharacter.toUnitHom_inj χ ψ).mp
    (MonoidHom.ext fun u => Units.ext (DFunLike.congr_fun hχψ u))
theorem sp:
    LinearIndependent ℂ (fun χ :DirichletCharacter ℂ p=>
      (qK (p:=p) χ : (ZMod p)ˣ → ℂ)) :=
  (linearIndependent_monoidHom ((ZMod p)ˣ) ℂ).comp
      (qK (p:=p))
      (wU (p:=p))
def zX: (ZMod p → ℂ) →ₗ[ℂ] ℂ where
  toFun Φ :=Φ 0
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
@[simp] theorem dirichletCharacter_apply_zero (χ:DirichletCharacter ℂ p) :
    χ (0:ZMod p) = 0:=
  MulChar.map_zero χ
theorem yu:
    qn p (rf (p:=p)) =
      (Real.sqrt p :ℂ)⁻¹ • (fun _ :ZMod p => (1:ℂ)) :=by
  ext x
  rw [u5,rf,yh]
  simp [smul_eq_mul]
theorem yD:
    qn p (fun _ :ZMod p => (1:ℂ)) =
      (((Real.sqrt p :ℂ)⁻¹) * p) • rf (p:=p) :=by
  ext x
  rw [u5,congrFun (xH (p:=p)) x]
  simp [rf,smul_eq_mul,mul_assoc]
end SignInvariant
end KummerCriterion
noncomputable section
namespace KummerCriterion
section SignInvariant
open scoped BigOperators ComplexConjugate
variable (p:ℕ) [hp:Fact p.Prime]
local instance:DecidableEq (DirichletCharacter ℂ p) :=Classical.decEq _
local instance:DecidableEq (Option (DirichletCharacter ℂ p)) :=Classical.decEq _
def qr (χ:DirichletCharacter ℂ p) : ZMod p → ℂ :=by
  classical
  exact if hχ:χ=1 then fun _ :ZMod p => (1:ℂ) else (χ:ZMod p → ℂ)
omit hp in
@[simp] theorem constOneDirichletCharacterFamily_one:
    qr (p:=p) (1:DirichletCharacter ℂ p) =
      (fun _ :ZMod p => (1:ℂ)) :=by
  classical
  rw [qr]
  simp
omit hp in
theorem qM {χ:DirichletCharacter ℂ p}
    (hχ:χ ≠ 1) :
    qr (p:=p) χ = (χ:ZMod p → ℂ) :=by
  classical
  rw [qr]
  simp [hχ]
@[simp] theorem restrictUnits_deltaZero:
    rF (p:=p) (rf (p:=p)) = 0:=by
  ext u
  have hu: ((u: (ZMod p)) ≠ 0) :=Units.ne_zero u
  simp [rF,rf,hu]
@[simp] theorem restrictUnits_constOneDirichletCharacterFamily
    (χ:DirichletCharacter ℂ p) :
    rF (p:=p) (qr (p:=p) χ) =
      (qK (p:=p) χ : (ZMod p)ˣ → ℂ) :=by
  classical
  by_cases hχ:χ=1
  · subst hχ
    ext u
    rw [constOneDirichletCharacterFamily_one (p:=p)]
    simp [rF,qK]
  · ext u
    rw [qM (p:=p) hχ]
    simp [rF,qK]
theorem vI:
    LinearIndependent ℂ (qr (p:=p)) :=by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha χ
  have h_units:
      ∑ ψ,a ψ • (qK (p:=p) ψ : (ZMod p)ˣ → ℂ) = 0:=by
    simpa using congrArg (rF (p:=p)) ha
  exact
    (Fintype.linearIndependent_iff.mp
      (sp (p:=p))) a h_units χ
theorem vb:
    rf (p:=p) ∉
      Submodule.span ℂ
        (Set.range fun χ :DirichletCharacter ℂ p=>
          qr (p:=p) χ) :=by
  intro hdelta
  obtain ⟨a,ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun
      (R:=ℂ)
      (v:=fun χ :DirichletCharacter ℂ p=>
        qr (p:=p) χ)).mp hdelta
  have h_units:
      ∑ χ,a χ • (qK (p:=p) χ : (ZMod p)ˣ → ℂ) = 0:=by
    simpa using congrArg (rF (p:=p)) ha
  have ha_zero: ∀ χ:DirichletCharacter ℂ p,a χ=0:=
    (Fintype.linearIndependent_iff.mp
      (sp (p:=p))) a h_units
  have hone: (1:ℂ) = 0:=by
    simpa [zX,rf,qr,
      dirichletCharacter_apply_zero,ha_zero] using
      congrArg (zX (p:=p)) ha
  exact one_ne_zero hone
def sD:
    Option (DirichletCharacter ℂ p) → (ZMod p → ℂ) :=
  fun o => Option.casesOn' o (rf (p:=p))
    (qr (p:=p))
theorem uH:
    LinearIndependent ℂ (sD (p:=p)) :=by
  simpa [sD] using!
    (vI (p:=p)).option
      (x:=rf (p:=p))
      (vb (p:=p))
def qj:
    Module.Basis (Option (DirichletCharacter ℂ p)) ℂ (ZMod p → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (uH (p:=p)) <| by
      rw [Fintype.card_option,← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R:=ℂ) (n:=p),
        Nat.totient_prime hp.out]
      rw [Module.finrank_fintype_fun_eq_card,ZMod.card]
      exact Nat.sub_add_cancel hp.out.one_le
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_none:
    qj (p:=p) none=rf (p:=p) :=by
  rw [qj,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_some
    (χ:DirichletCharacter ℂ p) :
    qj (p:=p) (some χ) =
      qr (p:=p) χ :=by
  rw [qj,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl
@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_some_one:
    qj (p:=p)
        (some (1:DirichletCharacter ℂ p)) =
      (fun _ :ZMod p => (1:ℂ)) :=by
  simp [deltaZeroConstOneDirichletCharacterBasis_apply_some,constOneDirichletCharacterFamily_one]
theorem r7
    {χ:DirichletCharacter ℂ p} (hχ:χ ≠ 1) :
    qj (p:=p) (some χ) = (χ:ZMod p → ℂ) :=by
  simp [deltaZeroConstOneDirichletCharacterBasis_apply_some,
    qM,hχ]
def qg:
    Option (DirichletCharacter ℂ p) → Option (DirichletCharacter ℂ p) :=by
  classical
  exact fun
    | none=> some 1
    | some χ => if hχ:χ=1 then none else some χ⁻¹
def qc:
    Equiv.Perm (Option (DirichletCharacter ℂ p)) where
  toFun:=qg (p:=p)
  invFun:=qg (p:=p)
  left_inv:=by
    classical
    intro i
    cases i with
    | none=>
        simp [qg]
    | some χ =>
        by_cases hχ:χ=1
        · subst hχ
          simp [qg]
        · have hχinv:χ⁻¹ ≠ (1:DirichletCharacter ℂ p) :=by
            intro hχinv
            apply hχ
            calc
              χ= (χ⁻¹)⁻¹:=by simp
              _= (1:DirichletCharacter ℂ p)⁻¹:=by rw [hχinv]
              _=1:=by simp
          simp [qg,hχ,hχinv]
  right_inv:=by
    classical
    intro i
    cases i with
    | none=>
        simp [qg]
    | some χ =>
        by_cases hχ:χ=1
        · subst hχ
          simp [qg]
        · have hχinv:χ⁻¹ ≠ (1:DirichletCharacter ℂ p) :=by
            intro hχinv
            apply hχ
            calc
              χ= (χ⁻¹)⁻¹:=by simp
              _= (1:DirichletCharacter ℂ p)⁻¹:=by rw [hχinv]
              _=1:=by simp
          simp [qg,hχ,hχinv]
def q1 (i:Option (DirichletCharacter ℂ p)) : ℂ:=by
  classical
  exact match i with
  | none=> (Real.sqrt p :ℂ)⁻¹
  | some χ =>
      if hχ:χ=1 then ((Real.sqrt p :ℂ)⁻¹) * p
      else ((Real.sqrt p :ℂ)⁻¹) *
        (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N:=p)))
theorem qT
    (i:Option (DirichletCharacter ℂ p)) :
    qn p (qj (p:=p) i) =
      q1 (p:=p) i •
        qj (p:=p)
          ((qc (p:=p)) i) :=by
  classical
  cases i with
  | none=>
      rw [deltaZeroConstOneDirichletCharacterBasis_apply_none,
        yu,q1]
      simp [qc,qg]
  | some χ =>
      by_cases hχ:χ=1
      · subst hχ
        rw [deltaZeroConstOneDirichletCharacterBasis_apply_some_one,yD,
          q1]
        simp [qc,qg]
      · have hχinv:χ⁻¹ ≠ (1:DirichletCharacter ℂ p) :=by
          intro hχinv
          apply hχ
          calc
            χ= (χ⁻¹)⁻¹:=by simp
            _= (1:DirichletCharacter ℂ p)⁻¹:=by rw [hχinv]
            _=1:=by simp
        rw [r7 (p:=p) hχ]
        ext x
        rw [u5]
        rw [congrFun (zA (p:=p) (χ:=χ) hχ) x]
        simp [q1,qc,
          qg,hχ,hχinv,
          deltaZeroConstOneDirichletCharacterBasis_apply_some,
          qM,smul_eq_mul,
          mul_left_comm,mul_comm]
theorem ul:
    LinearMap.toMatrix
        (qj (p:=p))
        (qj (p:=p))
        (qn p) =
      (((qc (p:=p))⁻¹).permMatrix ℂ) *
        Matrix.diagonal (q1 (p:=p)) :=by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply,qT]
  by_cases hij:i=qc (p:=p) j
  · subst hij
    simp [Matrix.mul_diagonal,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply]
  · have hneq: ((qc (p:=p))⁻¹) i ≠ j :=by
      intro h
      apply hij
      simpa using congrArg (qc (p:=p)) h
    have hneq': ¬ Equiv.symm (qc (p:=p)) i =j:=by
      simpa using hneq
    have hsingle:
        ((qj (p:=p)).repr
            (q1 (p:=p) j •
              (qj (p:=p))
                ((qc (p:=p)) j))) i =0:=by
      simp [Module.Basis.repr_self,hij]
    simpa only [Matrix.mul_diagonal,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
      Equiv.Perm.coe_inv,Option.mem_def,Option.some.injEq,ite_mul,one_mul,zero_mul,hneq',
      if_false] using hsingle
theorem w5:
    LinearMap.det (qn p) =
      (Equiv.Perm.sign (qc (p:=p)) : ℂ) *
        ∏ i,q1 (p:=p) i :=by
  classical
  rw [← LinearMap.det_toMatrix (qj (p:=p))
      (qn p),
    ul (p:=p),
    Matrix.det_mul,Matrix.det_permutation,Matrix.det_diagonal]
  simp
omit hp in
theorem zo:
    (qc (p:=p)) ^ 2=1:=by
  ext i
  cases i with
  | none=>
      simp [pow_two,qc,qg]
  | some χ =>
      classical
      by_cases hχ:χ=1
      · subst hχ
        simp [pow_two,qc,qg]
      · have hχinv:χ⁻¹ ≠ (1:DirichletCharacter ℂ p) :=by
          intro hχinv
          apply hχ
          calc
            χ= (χ⁻¹)⁻¹:=by simp
            _= (1:DirichletCharacter ℂ p)⁻¹:=by rw [hχinv]
            _=1:=by simp
        simp [pow_two,qc,qg,hχ,
          hχinv]
theorem rW
    (hp₂:p ≠ 2) (i:Option (DirichletCharacter ℂ p)) :
    i ∈ Function.fixedPoints (qc (p:=p)) ↔
      i=some (q3 p) :=by
  classical
  cases i with
  | none=>
      simp [Function.fixedPoints,Function.IsFixedPt,qc,
        qg]
  | some χ =>
      by_cases hχ:χ=1
      · subst hχ
        have hquad_ne:q3 p ≠ (1:DirichletCharacter ℂ p) :=
          ri (p:=p) hp₂
        constructor
        · intro hfix
          simp [Function.fixedPoints,Function.IsFixedPt,qc,
            qg] at hfix
        · intro hquad
          exact False.elim (hquad_ne (Option.some.inj hquad).symm)
      · constructor
        · intro hfix
          have hself:χ⁻¹=χ:=by
            simpa [Function.fixedPoints,Function.IsFixedPt,qc,
              qg,hχ] using hfix
          exact congrArg some
            (sm (p:=p) hp₂ hχ hself.symm)
        · intro hquad
          injection hquad with hχquad
          subst hχquad
          have hquad_ne:q3 p ≠ (1:DirichletCharacter ℂ p) :=
            ri (p:=p) hp₂
          change Function.IsFixedPt (qc (p:=p))
            (some (q3 p))
          simp [Function.IsFixedPt,qc,
            qg,hquad_ne,rK]
theorem w8 (hp₂:p ≠ 2) :
    Fintype.card (Function.fixedPoints (qc (p:=p))) = 1:=by
  classical
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨some (q3 p),?_⟩,?_⟩
  · exact (rW (p:=p) hp₂ _).2 rfl
  · intro x
    exact Subtype.ext <|
      (rW (p:=p) hp₂ x.1).1 x.2
theorem xQ (hp₂:p ≠ 2) :
    (Equiv.Perm.sign (qc (p:=p)) : ℂ) =
      (-1:ℂ) ^ ((p-1) / 2) :=by
  classical
  rw [Equiv.Perm.sign_of_pow_two_eq_one (zo (p:=p)),
    w8 (p:=p) hp₂,
    Fintype.card_option,← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R:=ℂ) (n:=p),
    Nat.totient_prime hp.out]
  rw [Nat.sub_add_cancel hp.out.one_le]
  simp
theorem uI (hp₂:p ≠ 2) :
    LinearMap.det (qn p) =
      (-1:ℂ) ^ ((p-1) / 2) * ∏ i,q1 (p:=p) i :=by
  rw [w5 (p:=p),
    xQ (p:=p) hp₂]
theorem uY
    {χ:DirichletCharacter ℂ p} (hχ:χ ≠ 1) :
    q1 (p:=p) (some χ) *
      q1 (p:=p) (some χ⁻¹) = χ (-1) :=by
  classical
  have hχinv:χ⁻¹ ≠ (1:DirichletCharacter ℂ p) :=by
    intro hχinv
    apply hχ
    calc
      χ= (χ⁻¹)⁻¹:=by simp
      _= (1:DirichletCharacter ℂ p)⁻¹:=by rw [hχinv]
      _=1:=by simp
  have hχmap:=
    qT
      (p:=p) (i:=some χ)
  have hχinvmap:=
    qT
      (p:=p) (i:=some χ⁻¹)
  rw [r7 (p:=p) hχ] at hχmap
  rw [r7 (p:=p) hχinv] at hχinvmap
  have hχmap':
      qn p (χ:ZMod p → ℂ) =
        q1 (p:=p) (some χ) •
          (((χ⁻¹:DirichletCharacter ℂ p) : ZMod p → ℂ)) :=by
    simpa [qc,qg,hχ,hχinv,
      qM (p:=p) hχinv] using hχmap
  have hχinvmap':
      qn p (((χ⁻¹:DirichletCharacter ℂ p) : ZMod p → ℂ)) =
        q1 (p:=p) (some χ⁻¹) •
          ((χ:DirichletCharacter ℂ p) : ZMod p → ℂ) :=by
    simpa [qc,qg,hχinv,hχ,
      qM (p:=p) hχ] using hχinvmap
  have htwice:
      qn p (qn p (χ:ZMod p → ℂ)) =
        (q1 (p:=p) (some χ) *
          q1 (p:=p) (some χ⁻¹)) •
            (χ:ZMod p → ℂ) :=by
    rw [hχmap',LinearMap.map_smul,hχinvmap']
    simp [smul_smul]
  have hsq:
      qn p (qn p (χ:ZMod p → ℂ)) =
        χ (-1) • (χ:ZMod p → ℂ) :=by
    ext x
    rw [yC]
    by_cases hx:x=0
    · subst hx
      simp [dirichletCharacter_apply_zero]
    · calc
        χ (-x) = χ ((-1:ZMod p) * x) :=by ring_nf
        _=χ (-1) * χ x :=by rw [map_mul]
        _= (χ (-1) • (χ:ZMod p → ℂ)) x :=by simp [smul_eq_mul]
  have hone:χ (1:ZMod p) = 1:=MulChar.map_one χ
  have hcoeff:= (congrFun htwice (1:ZMod p)).symm.trans (congrFun hsq (1:ZMod p))
  simpa [hone,smul_eq_mul] using hcoeff
def qa:Finset (DirichletCharacter ℂ p) :=
  (Finset.univ.erase (1:DirichletCharacter ℂ p)).erase (q3 p)
theorem ue (hp₂:p ≠ 2) :
    ∏ i,q1 (p:=p) i =
      q1 (p:=p) (some (q3 p)) *
        Finset.prod (qa (p:=p))
          (fun χ => q1 (p:=p) (some χ)) :=by
  rw [Fintype.prod_option]
  let q :DirichletCharacter ℂ p:=q3 p
  have hq_ne:q ≠ (1:DirichletCharacter ℂ p) :=ri (p:=p) hp₂
  have htriv:
      q1 (p:=p) none*
        q1 (p:=p) (some (1:DirichletCharacter ℂ p)) = 1:=by
    have hp_nonneg: (0:ℝ) ≤ p:=by
      exact_mod_cast Nat.zero_le p
    have hsqrt_ne: (Real.sqrt p :ℂ) ≠ 0:=by
      exact_mod_cast Real.sqrt_ne_zero'.2 (by exact_mod_cast hp.out.pos)
    have hsq: ((Real.sqrt p :ℂ) ^ 2) = (p:ℂ) :=by
      exact_mod_cast (Real.sq_sqrt hp_nonneg)
    simp [q1]
    field_simp [hsqrt_ne]
    simpa [pow_two,mul_assoc] using hsq.symm
  have hprod_chars:
      ∏ χ :DirichletCharacter ℂ p,q1 (p:=p) (some χ) =
        q1 (p:=p) (some (1:DirichletCharacter ℂ p)) *
          (q1 (p:=p) (some q) *
            Finset.prod (qa (p:=p))
              (fun χ => q1 (p:=p) (some χ))) :=by
    let f :DirichletCharacter ℂ p → ℂ:=
      fun χ => q1 (p:=p) (some χ)
    have h1:
        f 1 *Finset.prod (Finset.univ.erase (1:DirichletCharacter ℂ p)) f = ∏ χ,f χ:=by
      simpa [f] using
        (Finset.mul_prod_erase (Finset.univ:Finset (DirichletCharacter ℂ p)) f (by simp))
    have hq:
        f q *Finset.prod ((Finset.univ.erase (1:DirichletCharacter ℂ p)).erase q) f =
          Finset.prod (Finset.univ.erase (1:DirichletCharacter ℂ p)) f :=by
      simpa [f] using
        (Finset.mul_prod_erase
          ((Finset.univ:Finset (DirichletCharacter ℂ p)).erase (1:DirichletCharacter ℂ p))
          f (by simp [hq_ne]))
    calc
      ∏ χ,f χ=f 1*Finset.prod (Finset.univ.erase (1:DirichletCharacter ℂ p)) f :=by
        symm
        exact h1
      _=f 1* (f q *Finset.prod (qa (p:=p)) f) :=by
        rw [← hq]
        simp [qa,q]
      _=q1 (p:=p) (some (1:DirichletCharacter ℂ p)) *
            (q1 (p:=p) (some q) *
              Finset.prod (qa (p:=p))
                (fun χ => q1 (p:=p) (some χ))) :=by
          simp [f]
  have hstep1:
      q1 (p:=p) none*
          ∏ i,q1 (p:=p) (some i) =
        q1 (p:=p) none*
          (q1 (p:=p) (some (1:DirichletCharacter ℂ p)) *
            (q1 (p:=p) (some q) *
              Finset.prod (qa (p:=p))
                (fun χ => q1 (p:=p) (some χ)))) :=
    congrArg (fun z => q1 (p:=p) none*z) hprod_chars
  calc
    q1 (p:=p) none*
        ∏ i,q1 (p:=p) (some i)
        =q1 (p:=p) none*
            (q1 (p:=p) (some (1:DirichletCharacter ℂ p)) *
              (q1 (p:=p) (some q) *
                Finset.prod (qa (p:=p))
                  (fun χ => q1 (p:=p) (some χ)))) :=hstep1
    _= (q1 (p:=p) none*
          q1 (p:=p) (some (1:DirichletCharacter ℂ p))) *
            (q1 (p:=p) (some q) *
              Finset.prod (qa (p:=p))
                (fun χ => q1 (p:=p) (some χ))) :=by
            ring_nf
    _=q1 (p:=p) (some q) *
          Finset.prod (qa (p:=p))
            (fun χ => q1 (p:=p) (some χ)) :=by
            rw [htriv]
            simp
    _=q1 (p:=p) (some (q3 p)) *
          Finset.prod (qa (p:=p))
            (fun χ => q1 (p:=p) (some χ)) :=by
            simp [q]
theorem uh (hp₂:p ≠ 2) :
    LinearMap.det (qn p) =
      (-1:ℂ) ^ ((p-1) / 2) *
        (q1 (p:=p) (some (q3 p)) *
          Finset.prod (qa (p:=p))
            (fun χ => q1 (p:=p) (some χ))) :=by
  rw [uI (p:=p) hp₂,
    ue (p:=p) hp₂]
noncomputable def rl:
    DirichletCharacter ℂ p ≃ Fin (Fintype.card (DirichletCharacter ℂ p)) :=
  Fintype.equivFin (DirichletCharacter ℂ p)
theorem qW (χ:DirichletCharacter ℂ p) :
    χ ∈ qa (p:=p) ↔
      χ ≠ 1 ∧ χ ≠ q3 p :=by
  constructor
  · intro h
    have h':χ ≠ q3 p ∧ χ ≠ 1 :=by
      simpa [qa] using h
    exact ⟨h'.2,h'.1⟩
  · intro h
    simp [qa,h.1,h.2]
theorem rY {χ:DirichletCharacter ℂ p}
    (hχ:χ ∈ qa (p:=p)) :
    χ⁻¹ ∈ qa (p:=p) :=by
  rcases (qW (p:=p) χ).1 hχ with ⟨hχ1,hχquad⟩
  rw [qW (p:=p)]
  constructor
  · intro hχinv
    apply hχ1
    calc
      χ= (χ⁻¹)⁻¹:=by simp
      _= (1:DirichletCharacter ℂ p)⁻¹:=by rw [hχinv]
      _=1:=by simp
  · intro hχinvquad
    apply hχquad
    calc
      χ= (χ⁻¹)⁻¹:=by simp
      _= (q3 p)⁻¹:=by rw [hχinvquad]
      _=q3 p :=by simp [rK (p:=p)]
theorem x0 {hp₂:p ≠ 2} {χ:DirichletCharacter ℂ p}
    (hχ:χ ∈ qa (p:=p)) :
    χ ≠ χ⁻¹:=by
  rcases (qW (p:=p) χ).1 hχ with ⟨hχ1,hχquad⟩
  intro hχself
  rcases sC (p:=p) hp₂ hχself with h | h
  · exact hχ1 h
  · exact hχquad h
noncomputable def qh:
    Finset (DirichletCharacter ℂ p) :=
  (qa (p:=p)).filter
    fun χ => rl (p:=p) χ < rl (p:=p) χ⁻¹
theorem qD (χ:DirichletCharacter ℂ p) :
    χ ∈ qh (p:=p) ↔
      χ ∈ qa (p:=p) ∧
        rl (p:=p) χ < rl (p:=p) χ⁻¹:=by
  simp [qh]
theorem sZ {χ:DirichletCharacter ℂ p}
    (hχ:χ ∈ qh (p:=p)) :
    χ⁻¹ ∉ qh (p:=p) :=by
  intro hχinv
  rcases (qD (p:=p) χ).1 hχ with ⟨_,hlt⟩
  have hlt_inv:
      rl (p:=p) χ⁻¹ < rl (p:=p) χ :=by
    simpa using ((qD (p:=p) χ⁻¹).1 hχinv).2
  exact lt_irrefl _ (lt_trans hlt hlt_inv)
theorem wp {hp₂:p ≠ 2} {χ:DirichletCharacter ℂ p}
    (hχ:χ ∈ qa (p:=p)) :
    χ ∈ qh (p:=p) ∨ χ⁻¹ ∈ qh (p:=p) :=by
  have hne:χ ≠ χ⁻¹:=
    x0 (p:=p) (hp₂:=hp₂) hχ
  have hij:
      rl (p:=p) χ ≠ rl (p:=p) χ⁻¹:=fun hidx=>
    hne <| (rl (p:=p)).injective hidx
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · left
    exact (qD (p:=p) χ).2 ⟨hχ,hlt⟩
  · right
    exact (qD (p:=p) χ⁻¹).2
      ⟨rY (p:=p) hχ,by simpa using hgt⟩
theorem rV (hp₂:p ≠ 2) :
    qa (p:=p) =
      qh (p:=p) ∪
        (qh (p:=p)).image fun χ => χ⁻¹:=by
  ext χ
  constructor
  · intro hχ
    rcases wp (p:=p) (hp₂:=hp₂) hχ with hrep | hinvrep
    · exact Finset.mem_union.mpr (Or.inl hrep)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨χ⁻¹,hinvrep,by simp⟩))
  · intro hχ
    rcases Finset.mem_union.mp hχ with hrep | himage
    · exact (qD (p:=p) χ).1 hrep |>.1
    · rcases Finset.mem_image.mp himage with ⟨ψ,hψrep,hψ⟩
      have hψnon:ψ ∈ qa (p:=p) :=
        (qD (p:=p) ψ).1 hψrep |>.1
      simpa [← hψ] using rY (p:=p) hψnon
theorem sy:
    Disjoint (qh (p:=p))
      ((qh (p:=p)).image fun χ => χ⁻¹) :=by
  refine Finset.disjoint_left.mpr ?_
  intro χ hχrep hχimage
  rcases Finset.mem_image.mp hχimage with ⟨ψ,hψrep,hψ⟩
  have hψinv:ψ⁻¹ ∈ qh (p:=p) :=by
    simpa [hψ] using hχrep
  exact (sZ (p:=p) hψrep) hψinv
theorem vR (hp₂:p ≠ 2) :
    Finset.prod (qa (p:=p))
      (fun χ => q1 (p:=p) (some χ)) =
        Finset.prod (qh (p:=p)) (fun χ => χ (-1)) :=by
  let reps:=qh (p:=p)
  let f :DirichletCharacter ℂ p → ℂ:=
    fun χ => q1 (p:=p) (some χ)
  have hsplit:=rV (p:=p) hp₂
  have hdisj:=sy (p:=p)
  have hinj:Set.InjOn (fun χ :DirichletCharacter ℂ p=> χ⁻¹) ↑reps:=by
    intro χ hχ ψ hψ hEq
    simpa using congrArg Inv.inv hEq
  calc
    Finset.prod (qa (p:=p)) f
        =Finset.prod reps f *Finset.prod (reps.image fun χ => χ⁻¹) f :=by
            rw [hsplit,Finset.prod_union hdisj]
    _=Finset.prod reps f *Finset.prod reps (fun χ => f (χ⁻¹)) :=by
          rw [Finset.prod_image hinj]
    _=Finset.prod reps (fun χ => f χ*f (χ⁻¹)) :=by
          rw [← Finset.prod_mul_distrib]
    _=Finset.prod reps (fun χ => χ (-1)) :=by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          have hχnon:χ ∈ qa (p:=p) :=
            (qD (p:=p) χ).1 hχ |>.1
          exact uY (p:=p)
            ((qW (p:=p) χ).1 hχnon).1
theorem zZ (hp₂:p ≠ 2) :
    (qh (p:=p)).card= (p-3) / 2:=by
  let reps:=qh (p:=p)
  let q :DirichletCharacter ℂ p:=q3 p
  have hq_ne:q ≠ (1:DirichletCharacter ℂ p) :=ri (p:=p) hp₂
  have hq_mem:q ∈ (Finset.univ.erase (1:DirichletCharacter ℂ p) :
      Finset (DirichletCharacter ℂ p)) :=by
    simp [Finset.mem_erase,q,hq_ne]
  have hcard_nonself:
      (qa (p:=p)).card=p-3:=by
    rw [qa,Finset.card_erase_of_mem hq_mem,
      Finset.card_erase_of_mem (by simp),
      Finset.card_univ,← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R:=ℂ) (n:=p),
      Nat.totient_prime hp.out]
    omega
  have hsplit:
      (qa (p:=p)).card=
        reps.card+reps.card:=by
    rw [rV (p:=p) hp₂,
      Finset.card_union_of_disjoint (sy (p:=p)),
      Finset.card_image_of_injective _ (fun χ ψ hEq=> by simpa using congrArg Inv.inv hEq)]
  have hp₂le:2 ≤ p:=hp.out.two_le
  have hp₃:3 ≤ p:=by
    omega
  have htwice:p-3=reps.card*2:=by
    omega
  exact (Nat.div_eq_of_eq_mul_left (by decide:0 < 2) htwice).symm
theorem su
    (hp₂:p ≠ 2) :
    LinearMap.det (qn p) =
      (-1:ℂ) *
        (q1 (p:=p) (some (q3 p)) *
          Finset.prod (qh (p:=p)) (fun χ => -(χ (-1)))) :=by
  let reps:=qh (p:=p)
  let qScalar:ℂ:=
    q1 (p:=p) (some (q3 p))
  have hprod:
      Finset.prod (qa (p:=p))
        (fun χ => q1 (p:=p) (some χ)) =
          Finset.prod reps (fun χ => χ (-1)) :=
    vR (p:=p) hp₂
  have hexp: ((p-1) / 2:ℕ) = 1+reps.card:=by
    have hreps:reps.card= (p-3) / 2:=by
      simpa [reps] using zZ (p:=p) hp₂
    obtain ⟨k,hk⟩ :=hp.out.odd_of_ne_two hp₂
    have hreps':reps.card=k-1:=by
      rw [hreps,hk]
      omega
    have hleft: ((p-1) / 2:ℕ) = k:=by
      rw [hk]
      omega
    have hright:1+reps.card=k:=by
      rw [hreps']
      have hp₂le:2 ≤ p:=hp.out.two_le
      have hkpos:0 < k:=by
        omega
      simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hkpos
    calc
      ((p-1) / 2:ℕ) = k:=hleft
      _=1+reps.card:=hright.symm
  have hnegprod:
      Finset.prod reps (fun χ => -(χ (-1))) =
        (-1:ℂ) ^ reps.card*Finset.prod reps (fun χ => χ (-1)) :=by
    rw [show (fun χ :DirichletCharacter ℂ p=> -(χ (-1))) =
        fun χ => (-1:ℂ) * χ (-1) by
          funext χ
          ring]
    rw [Finset.prod_mul_distrib,Finset.prod_const]
  calc
    LinearMap.det (qn p)
        = (-1:ℂ) ^ ((p-1) / 2) *
            (qScalar*Finset.prod reps (fun χ => χ (-1))) :=by
            simp [reps,qScalar,hprod,
              uh (p:=p) hp₂]
    _= ((-1:ℂ) * (-1:ℂ) ^ reps.card) *
          (qScalar*Finset.prod reps (fun χ => χ (-1))) :=by
          rw [hexp,pow_add]
          simp
    _= (-1:ℂ) *
          (qScalar* ((-1:ℂ) ^ reps.card*Finset.prod reps (fun χ => χ (-1)))) :=by
            ring
    _= (-1:ℂ) * (qScalar*Finset.prod reps (fun χ => -(χ (-1)))) :=by
          rw [← hnegprod]
end SignInvariant
end KummerCriterion
end
end
end Module12
-- Source: KummerCriterion.ZetaFactorisation.Basic
section Module13
noncomputable section
open NumberField
open Polynomial
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section ZetaFactorisation
noncomputable instance instFintypeSym (α:Type*) [Finite α] (n:ℕ) :
    Fintype (Sym α n) :=
  Fintype.ofFinite (Sym α n)
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def zI:DirichletCharacter ℂ p ≃* (ZMod p)ˣ:=by
  letI:NeZero p := ⟨hp.1.ne_zero⟩
  exact (DirichletCharacter.mulEquiv_units ℂ p).some
lemma qH:Nat.card (DirichletCharacter ℂ p) = p-1:=by
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity,Nat.totient_prime hp.1]
lemma xL {s:ℂ} (hs:s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar p s=
      (1- (p:ℂ) ^ (-s)) * riemannZeta s :=by
  have hpf:Nat.primeFactors p = {p} :=by
    simpa using (Nat.primeFactors_prime_pow (p:=p) (k:=1) (by decide: (1:ℕ) ≠ 0) hp.1)
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N:=p) hs,hpf,
    Finset.prod_singleton]
noncomputable def q0 (ℓ:ℕ) : Ideal ℤ :=
  Ideal.span ({(ℓ:ℤ)} : Set ℤ)
noncomputable def qb (ℓ:ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (q0 ℓ) (𝓞 K)
noncomputable def vi:Finset (DirichletCharacter ℂ p) :=by
  classical
  exact Finset.univ.erase 1
noncomputable def qi:Finset (DirichletCharacter ℂ p) :=by
  classical
  exact Finset.univ.filter fun χ => χ.Even ∧ χ ≠ 1
noncomputable def q8:Finset (DirichletCharacter ℂ p) :=by
  classical
  exact Finset.univ.filter fun χ => χ.Odd
theorem xd (p:ℕ) {χ:DirichletCharacter ℂ p}
    (hχ:χ ∈ q8 p) : χ⁻¹ ∈ q8 p :=by
  classical
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  have hχ_odd:χ.Odd:= (Finset.mem_filter.mp hχ).2
  rw [DirichletCharacter.Odd] at hχ_odd ⊢
  rw [MulChar.inv_apply_eq_inv',hχ_odd]
  norm_num
noncomputable def rm (ℓ:ℕ) (s:ℂ) : ℂ:=
  ∏ χ :DirichletCharacter ℂ p,(1-χ (ℓ:ZMod p) * (ℓ:ℂ) ^ (-s))
noncomputable def qI (ℓ:ℕ) (s:ℂ) : ℂ:=
  Finset.prod (qi (p:=p)) fun χ =>
    (1-χ (ℓ:ZMod p) * (ℓ:ℂ) ^ (-s))
noncomputable def qm (ℓ:ℕ) (s:ℂ) : ℂ:=
  Finset.prod (qb K ℓ) fun P => (1- (Ideal.absNorm P :ℂ) ^ (-s))
noncomputable def LProduct (s:ℂ) : ℂ:=
  ∏ χ :DirichletCharacter ℂ p,DirichletCharacter.LFunction χ s
noncomputable def qR (s:ℂ) : ℂ:=
  Finset.prod (vi (p:=p)) fun χ => DirichletCharacter.LFunction χ s
noncomputable def r1 (s:ℂ) : ℂ:=
  Finset.prod (qi (p:=p)) fun χ => DirichletCharacter.LFunction χ s
noncomputable def vx (s:ℂ) : ℂ:=
  Finset.prod (q8 (p:=p)) fun χ => DirichletCharacter.LFunction χ s
noncomputable def rR:𝓞 K:=
  (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
lemma sz {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) : p.Coprime ℓ :=
  (Nat.coprime_primes hp.out (Fact.out:ℓ.Prime)).mpr (Ne.symm hℓp)
noncomputable def qx (ℓ:ℕ) [Fact ℓ.Prime] (hℓp:ℓ ≠ p) : (ZMod p)ˣ:=
  ZMod.unitOfCoprime ℓ (sz (p:=p) hℓp).symm
noncomputable def q4 (ℓ:ℕ) [Fact ℓ.Prime] (hℓp:ℓ ≠ p) : ℕ:=
  orderOf (qx (p:=p) ℓ hℓp)
noncomputable def rd (ℓ:ℕ) [Fact ℓ.Prime] (hℓp:ℓ ≠ p) : ℕ:=
  Nat.card (DirichletCharacter ℂ p) / q4 (p:=p) ℓ hℓp
lemma xl {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    q4 (p:=p) ℓ hℓp ∣ Nat.card (DirichletCharacter ℂ p) :=by
  rw [qH (p:=p)]
  simpa [q4,ZMod.card_units p] using
    (orderOf_dvd_card (x:=qx (p:=p) ℓ hℓp))
lemma xm {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    rd (p:=p) ℓ hℓp*q4 (p:=p) ℓ hℓp=
      Nat.card (DirichletCharacter ℂ p) :=
  Nat.div_mul_cancel (xl (p:=p) hℓp)
lemma zG (d:ℕ) (hd:0 < d) (T:ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset d (1:ℂ),(1-ζ*T) = 1-T^d:=by
  by_cases hT:T=0
  · subst hT
    simp [zero_pow hd.ne']
  · have hζ:IsPrimitiveRoot (Complex.exp (2*Real.pi*Complex.I/d)) d :=
      Complex.isPrimitiveRoot_exp d hd.ne'
    have hcard: (Polynomial.nthRootsFinset d (1:ℂ)).card=d:=hζ.card_nthRootsFinset
    have hpoly:Polynomial.X^d-1= ∏ ζ ∈ Polynomial.nthRootsFinset d (1:ℂ),
        (Polynomial.X-Polynomial.C ζ) :=Polynomial.X_pow_sub_one_eq_prod hd hζ
    have heval:=congrArg (Polynomial.eval T⁻¹) hpoly
    simp only [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_sub,
      Polynomial.eval_one,Polynomial.eval_prod,Polynomial.eval_C] at heval
    have key: ∀ ζ:ℂ,(1-ζ*T) = T* (T⁻¹-ζ) :=fun ζ => by field_simp
    rw [Finset.prod_congr rfl (fun ζ _=> key ζ),Finset.prod_mul_distrib,
      Finset.prod_const,hcard,← heval]
    have hTT:T^d*T⁻¹^d=1:=by rw [← mul_pow,mul_inv_cancel₀ hT,one_pow]
    linear_combination hTT
lemma _root_.IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd
    {M:Type*} [CommMonoid M] {n:ℕ} (hn:0 < n) (a:ℕ)
    {ω:M} (hω:IsPrimitiveRoot ω n) :
    IsPrimitiveRoot (ω^a) (n/n.gcd a) :=by
  set d :=n/n.gcd a with hd_def
  set c :=n.gcd a with hc_def
  have hc_dvd_n:c ∣ n:=Nat.gcd_dvd_left n a
  have hc_dvd_a:c ∣ a:=Nat.gcd_dvd_right n a
  have hc_mul_d:c*d=n:=Nat.mul_div_cancel' hc_dvd_n
  have hc_pos:0 < c:=Nat.gcd_pos_of_pos_left _ hn
  obtain ⟨a',ha'⟩ :=hc_dvd_a
  have ha'_cop:a'.Coprime d :=by
    have key:c*Nat.gcd a' d =c*1:=by
      rw [mul_one]
      calc c *Nat.gcd a' d
          = (c*a').gcd (c*d) := (Nat.gcd_mul_left c a' d).symm
        _=a.gcd n :=by rw [← ha',hc_mul_d]
        _=c:=by rw [Nat.gcd_comm]
    exact Nat.eq_of_mul_eq_mul_left hc_pos key
  have hω_c:IsPrimitiveRoot (ω^c) d :=hω.pow hn hc_mul_d.symm
  rw [ha',pow_mul]
  exact hω_c.pow_of_coprime _ ha'_cop
lemma wm {n:ℕ} (hn:0 < n) (a:ℕ)
    {ω:ℂ} (hω:IsPrimitiveRoot ω n) (T:ℂ) :
    ∏ k ∈ Finset.range n,(1-ω^ (k*a) * T) =
      (1-T^ (n/n.gcd a)) ^ n.gcd a :=by
  classical
  set d :=n/n.gcd a with hd_def
  set c :=n.gcd a with hc_def
  have hc_dvd_n:c ∣ n:=Nat.gcd_dvd_left n a
  have hc_dvd_a:c ∣ a:=Nat.gcd_dvd_right n a
  have hc_mul_d:c*d=n:=Nat.mul_div_cancel' hc_dvd_n
  have hc_pos:0 < c:=Nat.gcd_pos_of_pos_left _ hn
  have hd_pos:0 < d:=Nat.div_pos (Nat.le_of_dvd hn hc_dvd_n) hc_pos
  have hd_dvd_n:d ∣ n:= ⟨c,by rw [mul_comm];exact hc_mul_d.symm⟩
  have hω_a_prim:IsPrimitiveRoot (ω^a) d :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn a hω
  have h_period: ∀ k:ℕ,ω^ (k*a) = ω^ ((k%d) * a) :=by
    intro k
    have hkd:k=d* (k/d) + k%d:= (Nat.div_add_mod k d).symm
    have h_da:ω^ ((k/d) * (d*a)) = 1:=by
      obtain ⟨a',ha'⟩ :=hc_dvd_a
      rw [ha',show (k/d) * (d* (c*a')) = (k/d) * a'* (c*d) from by ring,hc_mul_d]
      exact (hω.pow_eq_one_iff_dvd _).mpr ⟨(k/d) * a',mul_comm _ _⟩
    conv_lhs=> rw [hkd]
    rw [show (d* (k/d) + k%d) * a= (k%d) * a+ (k/d) * (d*a) from by ring,pow_add,
      h_da,mul_one]
  rw [show (∏ k ∈ Finset.range n,(1-ω^ (k*a) * T)) =
      ∏ k ∈ Finset.range n,(1-ω^ ((k%d) * a) * T) from
    Finset.prod_congr rfl (fun k _=> by rw [← h_period k])]
  rw [← Finset.prod_fiberwise_of_maps_to
    (g:=fun k :ℕ=> k %d) (t:=Finset.range d)
    (fun k _=> Finset.mem_range.mpr (Nat.mod_lt _ hd_pos))]
  have h_inner: ∀ j ∈ Finset.range d,
      (∏ k ∈ (Finset.range n).filter (fun k => k %d=j),(1-ω^ ((k%d) * a) * T)) =
      (1-ω^ (j*a) * T) ^ c:=by
    intro j hj
    have h_rewrite: ∀ k ∈ (Finset.range n).filter (fun k => k %d=j),
        (1-ω^ ((k%d) * a) * T) = (1-ω^ (j*a) * T) :=fun k hk=> by
      rw [Finset.mem_filter] at hk;rw [hk.2]
    rw [Finset.prod_congr rfl h_rewrite,Finset.prod_const]
    congr 1
    rw [Finset.mem_range] at hj
    obtain ⟨c',hcd'⟩ :=hd_dvd_n
    have hc_eq:c=c':=by
      have hd_mul:d*c=n:=by rw [mul_comm,hc_mul_d]
      exact Nat.eq_of_mul_eq_mul_left hd_pos (by rw [hd_mul,hcd'])
    rw [hc_eq]
    have hset: (Finset.range n).filter (fun k => k %d=j) =
        (Finset.range c').image (fun m => j +m*d) :=by
      ext k
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_image]
      refine ⟨fun ⟨hk_lt,hk_mod⟩ => ?_,?_⟩
      · have hk_dec:k=j+ (k/d) * d:=by
          have h1:k=d* (k/d) + k%d:= (Nat.div_add_mod k d).symm
          rw [hk_mod,mul_comm d (k/d)] at h1
          omega
        refine ⟨k/d,?_,hk_dec.symm⟩
        have h_lt_cd: (k/d) * d < c'*d:=by
          have h_le: (k/d) * d ≤ k:=Nat.div_mul_le_self k d
          rw [mul_comm c' d,← hcd'];omega
        exact Nat.lt_of_mul_lt_mul_right h_lt_cd
      · rintro ⟨m,hm_lt,rfl⟩
        refine ⟨?_,?_⟩
        · rw [hcd',mul_comm];nlinarith
        · rw [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hj]
    rw [hset,Finset.card_image_of_injective _ (fun x y hxy=> by simp at hxy;omega),
      Finset.card_range]
  rw [Finset.prod_congr rfl h_inner,Finset.prod_pow]
  congr 1
  have h_inj:Set.InjOn (fun j :ℕ=> (ω^a) ^ j) ↑(Finset.range d) :=by
    intro x hx y hy hxy
    simp only [Finset.coe_range,Set.mem_Iio] at hx hy
    exact hω_a_prim.pow_inj hx hy hxy
  have h_image:Finset.image (fun j :ℕ=> (ω^a) ^ j) (Finset.range d) =
      Polynomial.nthRootsFinset d (1:ℂ) :=by
    apply Finset.eq_of_subset_of_card_le
    · intro ζ hζ
      simp only [Finset.mem_image,Finset.mem_range] at hζ
      obtain ⟨j,_,rfl⟩ :=hζ
      rw [Polynomial.mem_nthRootsFinset hd_pos,← pow_mul,mul_comm j d,pow_mul,
        hω_a_prim.pow_eq_one,one_pow]
    · rw [hω_a_prim.card_nthRootsFinset,Finset.card_image_of_injOn h_inj,Finset.card_range]
  calc ∏ j ∈ Finset.range d,(1-ω^ (j*a) * T)
      = ∏ j ∈ Finset.range d,(1- (ω^a) ^ j*T) :=by
        refine Finset.prod_congr rfl (fun j _=> ?_)
        rw [← pow_mul,mul_comm a j]
    _= ∏ ζ ∈ Finset.image (fun j :ℕ=> (ω^a) ^ j) (Finset.range d),(1-ζ*T) :=by
        rw [Finset.prod_image h_inj]
    _= ∏ ζ ∈ Polynomial.nthRootsFinset d (1:ℂ),(1-ζ*T) :=by rw [h_image]
    _=1-T^d:=zG d hd_pos T
lemma y7 (u: (ZMod p)ˣ) (T:ℂ) :
    (∏ χ :DirichletCharacter ℂ p,(1-χ (u:ZMod p) * T)) =
      (1-T^orderOf u) ^ (Nat.card (DirichletCharacter ℂ p) / orderOf u) :=by
  classical
  set d :=orderOf u with hd_def
  set n :=Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units:Fintype.card (ZMod p)ˣ=n:=by
    rw [hn_def,qH (p:=p),ZMod.card_units]
  have hn_units':Nat.card (ZMod p)ˣ=n:=by
    rw [Nat.card_eq_fintype_card,hn_units]
  have hn_pos:0 < n:=by rw [← hn_units];exact Fintype.card_pos
  obtain ⟨g,hg_mon⟩ : ∃ g : (ZMod p)ˣ,∀ x: (ZMod p)ˣ,x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon': ∀ x: (ZMod p)ˣ,∃ m:ℕ,g^m=x:=fun x => hg_mon x
  obtain ⟨a,ha⟩ :=hg_mon' u
  have hg_zpow: ∀ x: (ZMod p)ˣ,x ∈ Subgroup.zpowers g :=fun x => by
    obtain ⟨m,hm⟩ :=hg_mon' x
    refine ⟨(m:ℤ),?_⟩
    change g ^ (m:ℤ) = x
    rw [zpow_natCast];exact hm
  have hg_order:orderOf g =n:=by
    rw [← hn_units'];exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hd_eq:d=n/n.gcd a :=by
    have hfin:IsOfFinOrder g :=by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨n,hn_pos,by rw [← hg_order];exact pow_orderOf_eq_one g⟩
    have:d=orderOf (g^a) :=by rw [hd_def,← ha]
    rw [this,hfin.orderOf_pow,hg_order]
  have hn_div_d:n/d=n.gcd a :=by
    have hcd:n.gcd a ∣ n :=Nat.gcd_dvd_left n a
    rw [hd_eq,Nat.div_div_self hcd hn_pos.ne']
  have hω:IsPrimitiveRoot (Complex.exp (2*Real.pi*Complex.I/n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω :ℂ:=Complex.exp (2*Real.pi*Complex.I/n)
  have hω_unit:IsUnit ω :=hω.isUnit hn_pos.ne'
  set ωu:ℂˣ:=hω_unit.unit with hωu_def
  have hωu_val: (ωu:ℂ) = ω:=by simp [hωu_def]
  have hωu_roots: ∀ k:ℕ,(ωu^k:ℂˣ) ∈ rootsOfUnity n ℂ:=by
    intro k
    rw [mem_rootsOfUnity,← pow_mul,mul_comm]
    have h1: (ωu^n:ℂˣ) = 1:=by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val,Units.val_one,hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul,h1,one_pow]
  let χAt:ℕ → DirichletCharacter ℂ p:=fun k =>
    MulChar.ofRootOfUnity (M:=ZMod p) (R:=ℂ) (ζ:=ωu^k)
      (by rw [hn_units];exact hωu_roots k) hg_zpow
  have hχAt_g: ∀ k:ℕ,χAt k ((g: (ZMod p)ˣ) : ZMod p) = ω^k:=fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val,hωu_val]
  have hχAt_u: ∀ k:ℕ,χAt k (u:ZMod p) = ω^ (k*a) :=fun k => by
    have hu_eq: (u:ZMod p) = ((g: (ZMod p)ˣ) : ZMod p) ^ a:=by
      rw [← Units.val_pow_eq_pow_val,ha]
    rw [hu_eq,map_pow,hχAt_g,← pow_mul]
  have hχAt_inj:Set.InjOn χAt ↑(Finset.range n) :=by
    intro j hj k hk hjk
    simp only [Finset.coe_range,Set.mem_Iio] at hj hk
    have hval:χAt j ((g: (ZMod p)ˣ) : ZMod p) = χAt k ((g: (ZMod p)ˣ) : ZMod p) :=by
      rw [hjk]
    rw [hχAt_g,hχAt_g] at hval
    exact hω.pow_inj hj hk hval
  have hχAt_surj_onto_univ:
      Finset.image χAt (Finset.range n) = (Finset.univ:Finset (DirichletCharacter ℂ p)) :=by
    apply Finset.eq_of_subset_of_card_le
    · exact fun _ _=> Finset.mem_univ _
    · rw [Finset.card_image_of_injOn hχAt_inj,Finset.card_range,Finset.card_univ,
        ← Nat.card_eq_fintype_card]
  have h_transfer: ∏ χ:DirichletCharacter ℂ p,(1-χ (u:ZMod p) * T) =
      ∏ k ∈ Finset.range n,(1-ω^ (k*a) * T) :=by
    calc ∏ χ:DirichletCharacter ℂ p,(1-χ (u:ZMod p) * T)
        = ∏ χ ∈ (Finset.univ:Finset (DirichletCharacter ℂ p)),
            (1-χ (u:ZMod p) * T) :=rfl
      _= ∏ χ ∈ Finset.image χAt (Finset.range n),(1-χ (u:ZMod p) * T) :=by
          rw [hχAt_surj_onto_univ]
      _= ∏ k ∈ Finset.range n,(1- (χAt k) (u:ZMod p) * T) :=by
          rw [Finset.prod_image hχAt_inj]
      _= ∏ k ∈ Finset.range n,(1-ω^ (k*a) * T) :=by
          refine Finset.prod_congr rfl (fun k _=> ?_)
          rw [hχAt_u k]
  rw [h_transfer,wm hn_pos a hω T,← hd_eq,hn_div_d]
lemma wV {ℓ:ℕ} [Fact ℓ.Prime]
    (hℓp:ℓ ≠ p) {s:ℂ} :
    rm (p:=p) ℓ s=
      (1- ((ℓ:ℂ) ^ (-s)) ^ q4 (p:=p) ℓ hℓp) ^
        (Nat.card (DirichletCharacter ℂ p) / q4 (p:=p) ℓ hℓp) :=by
  have hval: ((qx p ℓ hℓp: (ZMod p)ˣ) : ZMod p) = (ℓ:ZMod p) :=by
    simp [qx]
  unfold rm
  rw [← hval]
  unfold q4
  exact y7 p (qx p ℓ hℓp) ((ℓ:ℂ) ^ (-s))
lemma wW {ℓ:ℕ} [Fact ℓ.Prime]
    (hℓp:ℓ ≠ p) {s:ℂ} :
    rm (p:=p) ℓ s=
      (1- (ℓ:ℂ) ^ (-(q4 (p:=p) ℓ hℓp:ℂ) * s)) ^
        rd (p:=p) ℓ hℓp:=by
  rw [wV (p:=p) hℓp,
    show ((ℓ:ℂ) ^ (-s)) ^ q4 (p:=p) ℓ hℓp=
        (ℓ:ℂ) ^ (-((q4 (p:=p) ℓ hℓp:ℂ)) * s) by
      rw [show-((q4 (p:=p) ℓ hℓp:ℂ)) * s=
          (-s) * ((q4 (p:=p) ℓ hℓp:ℕ) : ℂ) by ring,
        Complex.cpow_mul_nat]]
  rfl
lemma yU {s:ℂ} :
    rm (p:=p) p s=1:=
  Finset.prod_eq_one fun χ _=> by
    rw [ZMod.natCast_self,MulChar.map_nonunit _ not_isUnit_zero,zero_mul,sub_zero]
lemma qs {ℓ:ℕ} [Fact ℓ.Prime] {P:Ideal (𝓞 K)} :
    P ∈ qb K ℓ ↔ P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K) :=by
  have: (q0 ℓ).IsMaximal:=Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (q0 ℓ) ≠ ⊥ :=by
    rw [q0,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out:ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 K)
lemma zC:
    Algebra.adjoin ℤ ({rR (p:=p) (K:=K)} : Set (𝓞 K)) = ⊤ :=by
  exact IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (IsCyclotomicExtension.zeta_spec p ℚ K)
lemma y6:
    RingOfIntegers.exponent (rR (p:=p) (K:=K)) = 1:=
  RingOfIntegers.exponent_eq_one_iff.mpr (zC (p:=p) (K:=K))
lemma z4 {ℓ:ℕ} [Fact ℓ.Prime] :
    ¬ ℓ ∣ RingOfIntegers.exponent (rR (p:=p) (K:=K)) :=by
  rw [y6]
  exact Nat.Prime.not_dvd_one (Fact.out:ℓ.Prime)
noncomputable def uQ (ℓ:ℕ) [Fact ℓ.Prime] :
  Ideal.primesOver (q0 ℓ) (𝓞 K) ≃
      RingOfIntegers.monicFactorsMod (θ:=rR (p:=p) (K:=K)) (p:=ℓ) :=
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K:=K) (θ:=rR (p:=p) (K:=K))
    (p:=ℓ) (z4 (p:=p) (K:=K) (ℓ:=ℓ))
lemma xb {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    (RingOfIntegers.monicFactorsMod (θ:=rR (p:=p) (K:=K)) (p:=ℓ)).card=
      rd (p:=p) ℓ hℓp:=by
  classical
  have hmin:minpoly ℤ (rR (p:=p) (K:=K)) = cyclotomic p ℤ:=by
    rw [rR,← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  have hcop:ℓ.Coprime p := (sz (p:=p) hℓp).symm
  have hFcard:Fintype.card (ZMod ℓ) = ℓ^1:=by
    rw [pow_one];exact ZMod.card ℓ
  unfold RingOfIntegers.monicFactorsMod
  rw [hmin,Polynomial.map_cyclotomic_int,
    Polynomial.normalizedFactors_cyclotomic_card hFcard hcop]
  unfold rd q4 qx
  rw [qH (p:=p),Nat.totient_prime hp.out,
    ← orderOf_units (y:=ZMod.unitOfCoprime _ _),
    ← orderOf_units (y:=ZMod.unitOfCoprime ℓ _),ZMod.coe_unitOfCoprime,
    ZMod.coe_unitOfCoprime,pow_one]
lemma zt:
    map (Int.castRingHom (ZMod p))
        (minpoly ℤ (rR (p:=p) (K:=K))) =
      (X-1) ^ (p-1) :=by
  have hmin:minpoly ℤ (rR (p:=p) (K:=K)) = cyclotomic p ℤ:=by
    rw [rR,← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  rw [hmin,Polynomial.map_cyclotomic_int]
  have h1: (cyclotomic p (ZMod p)) * (X-1) = X^p-1:=
    cyclotomic_prime_mul_X_sub_one (ZMod p) p
  have h2: (X-1: (ZMod p)[X]) ^ p=X^p-1:=by
    rw [sub_pow_char_of_commute p (Commute.one_right X)]
    ring
  have hne: (X-1: (ZMod p)[X]) ≠ 0:=X_sub_C_ne_zero 1
  have hpow: (X-1: (ZMod p)[X]) ^ p= (X-1) ^ (p-1) * (X-1) :=by
    have hpos:0 < p:=hp.out.pos
    rw [← pow_succ]
    congr 1
    omega
  refine mul_right_cancel₀ hne ?_
  rw [← hpow,h2,← h1]
lemma zK:
    (RingOfIntegers.monicFactorsMod (θ:=rR (p:=p) (K:=K)) (p:=p)).card=1:=by
  classical
  unfold RingOfIntegers.monicFactorsMod
  rw [zt (p:=p) (K:=K)]
  have hirr:Irreducible (X-1: (ZMod p)[X]) :=
    irreducible_X_sub_C 1
  rw [hirr.normalizedFactors_pow,Multiset.toFinset_replicate]
  have hp_pos:p-1 ≠ 0:=Nat.sub_ne_zero_of_lt hp.out.one_lt
  simp [hp_pos]
lemma sE:
    (Ideal.primesOver (q0 p) (𝓞 K)).ncard=1:=by
  classical
  rw [← zK (p:=p) (K:=K),
    ← Nat.card_coe_set_eq,Nat.card_congr (uQ (p:=p) (K:=K) p),
    Nat.card_eq_finsetCard]
lemma s3 (P:Ideal (𝓞 K))
    (hP:P ∈ Ideal.primesOver (q0 p) (𝓞 K)) :
    P.inertiaDeg ℤ =1:=by
  have:P.IsPrime:=hP.1
  have:P.LiesOver (Ideal.span {(p:ℤ)}) :=by
    simpa [q0] using hP.2
  simpa [q0] using IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime p K P
lemma rv {ℓ:ℕ} [Fact ℓ.Prime]
    (hℓp:ℓ ≠ p) (P:Ideal (𝓞 K))
    (hP:P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K)) :
    P.inertiaDeg ℤ =q4 (p:=p) ℓ hℓp:=by
  have:P.IsPrime:=hP.1
  have:P.LiesOver (Ideal.span {(ℓ:ℤ)}) :=hP.2
  have hcop: ¬ ℓ ∣ p:=fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out:ℓ.Prime) hp.out).mp h)
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd ℓ K P hcop]
  unfold q4 qx
  rw [← orderOf_units]
  rfl
lemma un {ℓ:ℕ} [Fact ℓ.Prime]
    (hℓp:ℓ ≠ p) (P:Ideal (𝓞 K))
    (hP:P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K)) :
    P.ramificationIdx ℤ =1:=by
  have:P.IsPrime:=hP.1
  have:P.LiesOver (Ideal.span {(ℓ:ℤ)}) :=hP.2
  have hcop: ¬ ℓ ∣ p:=fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out:ℓ.Prime) hp.out).mp h)
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ℓ K P hcop
lemma u6 {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    (Ideal.primesOver (q0 ℓ) (𝓞 K)).ncard=
      rd (p:=p) ℓ hℓp:=by
  classical
  rw [← xb (p:=p) (K:=K) hℓp,
    ← Nat.card_coe_set_eq,Nat.card_congr (uQ (p:=p) (K:=K) ℓ),
    Nat.card_eq_finsetCard]
lemma sn {ℓ:ℕ} [Fact ℓ.Prime]
    (hℓp:ℓ ≠ p) {s:ℂ} :
    qm K ℓ s =
      (1- (ℓ:ℂ) ^ (-(q4 (p:=p) ℓ hℓp:ℂ) * s)) ^
        rd (p:=p) ℓ hℓp:=by
  classical
  have: (q0 ℓ).IsMaximal:=Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (q0 ℓ) ≠ ⊥ :=by
    rw [q0,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out:ℓ.Prime).ne_zero
  have hcoe:=IsDedekindDomain.coe_primesOverFinset (p:=q0 ℓ) hne (𝓞 K)
  have hcard_eq: (qb K ℓ).card=rd (p:=p) ℓ hℓp:=by
    have h1:=u6 p K hℓp
    rw [← hcoe,Set.ncard_coe_finset] at h1
    exact h1
  unfold qm
  have hprod_eq: ∀ P ∈ qb K ℓ,
      (1- (Ideal.absNorm P :ℂ) ^ (-s)) =
        1- (ℓ:ℂ) ^ (-(q4 (p:=p) ℓ hℓp:ℂ) * s) :=by
    intro P hP
    have hPmem:P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K) :=by
      have: (P:Ideal _) ∈
          (↑(IsDedekindDomain.primesOverFinset (q0 ℓ) (𝓞 K)) : Set _) :=
        hP
      rwa [hcoe] at this
    have:P.IsPrime:=hPmem.1
    have:P.LiesOver (Ideal.span {(ℓ:ℤ)}) :=hPmem.2
    have:P.IsMaximal:=Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(ℓ:ℤ)})
    have habsNorm:Ideal.absNorm P =ℓ^ (q4 (p:=p) ℓ hℓp) :=by
      rw [← rv p K hℓp P hPmem,
        ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(ℓ:ℤ)}) P]
      exact Ideal.absNorm_eq_pow_inertiaDeg' P (Fact.out:ℓ.Prime)
    rw [habsNorm]
    push_cast
    have:=Complex.natCast_cpow_natCast_mul ℓ (q4 (p:=p) ℓ hℓp) (-s)
    rw [show-((q4 (p:=p) ℓ hℓp:ℂ)) * s=
        ((q4 (p:=p) ℓ hℓp:ℕ) : ℂ) * (-s) by ring,
      this]
  rw [Finset.prod_congr rfl hprod_eq,Finset.prod_const,hcard_eq]
lemma wv {s:ℂ} :
    qm K p s =1- (p:ℂ) ^ (-s) :=by
  classical
  unfold qm qb q0
  have hne: (Ideal.span {(p:ℤ)} : Ideal ℤ) ≠ ⊥ :=by
    rw [Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hcoe:=
    IsDedekindDomain.coe_primesOverFinset (p:= (Ideal.span {(p:ℤ)} : Ideal ℤ)) hne (𝓞 K)
  have hcard: (IsDedekindDomain.primesOverFinset
      (Ideal.span {(p:ℤ)} : Ideal ℤ) (𝓞 K)).card=1:=by
    have hncard: ((Ideal.span {(p:ℤ)}).primesOver (𝓞 K)).ncard=1:=by
      simpa [q0] using sE (p:=p) (K:=K)
    rw [← hcoe] at hncard
    simpa using hncard
  obtain ⟨P,hP⟩ :=Finset.card_eq_one.mp hcard
  rw [hP,Finset.prod_singleton]
  have hPmem:P ∈ (Ideal.span {(p:ℤ)}).primesOver (𝓞 K) :=by
    rw [← hcoe,hP]
    exact Finset.mem_singleton_self P
  have:P.IsPrime:=hPmem.1
  have:P.LiesOver (Ideal.span {(p:ℤ)}) :=hPmem.2
  have:P.IsMaximal:=Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {(p:ℤ)})
  have habsNorm:Ideal.absNorm P =p^ (1:ℕ) :=by
    have hP':P ∈ Ideal.primesOver (q0 p) (𝓞 K) :=by
      simpa [q0] using hPmem
    rw [← s3 (p:=p) (K:=K) P hP',
      ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p:ℤ)}) P]
    exact Ideal.absNorm_eq_pow_inertiaDeg' P hp.out
  rw [habsNorm]
  push_cast
  rw [pow_one]
end ZetaFactorisation
end KummerCriterion
end
end Module13
-- Source: KummerCriterion.HMinus.ClassNumberFormula
section Module14
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
variable (p:ℕ) [hp:Fact p.Prime] (hp_odd:p ≠ 2)
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem h_formula:
    (h K :ℝ) =
      NumberField.dedekindZeta_residue K *
        (((Units.torsionOrder K :ℝ) * Real.sqrt |discr K|) /
          (2^InfinitePlace.nrRealPlaces K *
            (2*Real.pi) ^ InfinitePlace.nrComplexPlaces K *Units.regulator K)) :=by
  let A :ℝ:=
    2^InfinitePlace.nrRealPlaces K *
      (2*Real.pi) ^ InfinitePlace.nrComplexPlaces K *Units.regulator K
  let B :ℝ:= (Units.torsionOrder K :ℝ) * Real.sqrt |discr K|
  have hA_pos:0 < A:=by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos K)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA:A ≠ 0:=hA_pos.ne'
  have hB_pos:0 < B:=by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos K
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  calc
    (h K :ℝ) = ((A* (h K :ℝ)) / B) * (B/A) :=by
      field_simp [hA,hB_pos.ne']
    _=NumberField.dedekindZeta_residue K * (B/A) :=by
          dsimp [A,B]
          rw [NumberField.dedekindZeta_residue_def,KummerCriterion.h,NumberField.classNumber]
    _=NumberField.dedekindZeta_residue K *
          (((Units.torsionOrder K :ℝ) * Real.sqrt |discr K|) /
            (2^InfinitePlace.nrRealPlaces K *
              (2*Real.pi) ^ InfinitePlace.nrComplexPlaces K *Units.regulator K)) :=by
          simp [A,B]
theorem hPlus_formula:
    (hPlus K :ℝ) =
      NumberField.dedekindZeta_residue (oMR K) *
        (((Units.torsionOrder (oMR K) : ℝ) *
            Real.sqrt |discr (oMR K)|) /
          (2^InfinitePlace.nrRealPlaces (oMR K) *
            (2*Real.pi) ^ InfinitePlace.nrComplexPlaces (oMR K) *
              Units.regulator (oMR K))) :=by
  let L :=oMR K
  let A :ℝ:=
    2^InfinitePlace.nrRealPlaces L *
      (2*Real.pi) ^ InfinitePlace.nrComplexPlaces L *Units.regulator L
  let B :ℝ:= (Units.torsionOrder L :ℝ) * Real.sqrt |discr L|
  have hA_pos:0 < A:=by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA:A ≠ 0:=hA_pos.ne'
  have hB_pos:0 < B:=by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  calc
    (hPlus K :ℝ) = ((A* (hPlus K :ℝ)) / B) * (B/A) :=by
      field_simp [hA,hB_pos.ne']
    _=NumberField.dedekindZeta_residue L * (B/A) :=by
          dsimp [A,B,L]
          rw [NumberField.dedekindZeta_residue_def,KummerCriterion.hPlus,NumberField.classNumber]
    _=NumberField.dedekindZeta_residue L *
          (((Units.torsionOrder L :ℝ) * Real.sqrt |discr L|) /
            (2^InfinitePlace.nrRealPlaces L *
              (2*Real.pi) ^ InfinitePlace.nrComplexPlaces L *Units.regulator L)) :=by
          simp [A,B]
omit [IsCMField K] in
lemma wF:
    NumberField.InfinitePlace.nrComplexPlaces (oMR K) = 0:=
  NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
      (K:=oMR K)
lemma uR:
    NumberField.InfinitePlace.nrRealPlaces (oMR K) = (p-1) / 2:=by
  let L :=oMR K
  calc
    NumberField.InfinitePlace.nrRealPlaces L =Module.finrank ℚ L:=by
      rw [← NumberField.IsTotallyReal.finrank (K:=L)]
    _= (p-1) / 2:=by
      rw [uz (p:=p) (K:=K)]
lemma wz:
    2^NumberField.InfinitePlace.nrRealPlaces (oMR K) *
        (2*Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (oMR K) =
      2^ ((p-1) / 2:ℕ) :=by
  rw [wF (K:=K),pow_zero,mul_one,
    uR (p:=p) (K:=K)]
omit [IsCMField K] in
lemma wq
    (x:NumberField.Units.torsion (oMR K)) :
    (x: (𝓞 (oMR K))ˣ) = 1 ∨
      (x: (𝓞 (oMR K))ˣ) = -1:=by
  let L :=oMR K
  let φ :L →+*ℂ:=Classical.choice inferInstance
  let hφ:ComplexEmbedding.IsReal φ :=
    NumberField.IsTotallyReal.complexEmbedding_isReal φ
  let u : (𝓞 L)ˣ:=x
  let r :ℝ:=hφ.embedding (u:L)
  have hur: ((r:ℂ)) = φ (u:L) :=
    hφ.coe_embedding_apply (u:L)
  have hu_fin:IsOfFinOrder u := (CommGroup.mem_torsion u).1 x.prop
  obtain ⟨n,hn,hu_pow⟩ :=isOfFinOrder_iff_pow_eq_one.mp hu_fin
  have hnorm: ‖φ (u:L)‖ = 1:=
    Complex.norm_eq_one_of_pow_eq_one
      (by simpa [map_pow] using congrArg (fun z : (𝓞 L)ˣ=> φ (z:L)) hu_pow)
      (Nat.ne_of_gt hn)
  have hr_norm: ‖(r:ℂ)‖ = 1:=by
    rwa [← hur] at hnorm
  have hr_abs: |r| = 1:=by
    simpa [Complex.norm_real] using hr_norm
  have hr_sq:r^2=1:=by
    have hsquare:=congrArg (fun t :ℝ=> t ^2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · left
    apply NumberField.Units.coe_injective (K:=L)
    apply φ.injective
    simpa [hr] using hur.symm
  · right
    apply NumberField.Units.coe_injective (K:=L)
    apply φ.injective
    simpa [hr] using hur.symm
omit [IsCMField K] in
lemma xc:
    Units.torsionOrder (oMR K) = 2:=by
  let L :=oMR K
  classical
  let:=Fintype.ofFinite (Units.torsion L)
  rw [Units.torsionOrder,Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.2
    ⟨1,⟨-1,neg_one_mem_torsion⟩,by simp [← Subtype.coe_ne_coe],
      Finset.ext fun x ↦ ⟨fun _ ↦ ?_,fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert,Finset.mem_singleton,← Subtype.val_inj,← Subtype.val_inj]
  exact wq (K:=K) x
omit [IsCMField K] in
lemma x3 (hp_odd':p ≠ 2) :
    Units.torsionOrder K =2*p:=by
  have hneven: ¬ Even p :=fun h =>
    hp_odd' ((hp.out.even_iff).mp h)
  simpa [hneven,two_mul] using
    (IsCyclotomicExtension.Rat.torsionOrder_eq (n:=p) (K:=K))
lemma xp:
    Units.rank K = (p-3) / 2:=by
  let L :=oMR K
  rw [← NumberField.IsCMField.units_rank_eq_units_rank (K:=K),Units.rank]
  calc
    Fintype.card (NumberField.InfinitePlace L) - 1
        =NumberField.InfinitePlace.nrRealPlaces L -1:=by
            rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
              NumberField.IsTotallyReal.nrComplexPlaces_eq_zero,add_zero]
    _=Module.finrank ℚ L-1:=by
          rw [← NumberField.IsTotallyReal.finrank (K:=L)]
    _= (p-1) / 2-1:=by
          rw [uz (p:=p) (K:=K)]
    _= (p-3) / 2:=by omega
lemma vG (hp_odd':p ≠ 2) :
    Units.regulator K /Units.regulator (oMR K) =
      2^ ((p-3) / 2:ℕ) :=by
  rw [NumberField.IsCMField.regulator_div_regulator_eq_two_pow_mul_indexRealUnits_inv (K:=K),
    yK (p:=p) (K:=K) (hp_odd:=hp_odd'),
    xp (p:=p) (K:=K)]
  simp
omit [IsCMField K] in
lemma y9:
    |((NumberField.discr K :ℤ) : ℝ)| = (p:ℝ) ^ (p-2) :=by
  rw [IsCyclotomicExtension.Rat.discr_prime (p:=p) (K:=K)]
  rw [Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,abs_mul,abs_pow,abs_neg,
    abs_one,one_pow]
  simp [abs_of_nonneg (show 0 ≤ ((p:ℝ) ^ (p-2)) by positivity)]
omit [IsCMField K] in
lemma zu (hp_odd':p ≠ 2) :
    IsCyclotomicExtension.zeta p ℚ K ∉ oMR K :=by
  classical
  let ζ :K:=IsCyclotomicExtension.zeta p ℚ K
  have hζ:IsPrimitiveRoot ζ p:=IsCyclotomicExtension.zeta_spec p ℚ K
  intro hmem
  have hfix:= (NumberField.mem_maximalRealSubfield_iff (K:=K) ζ).mp hmem
  let φ :K →+*ℂ:=Classical.choice inferInstance
  have hstar:star (φ ζ) = φ ζ :=hfix φ
  have hpow: (φ ζ) ^ p=1:=by
    simpa [map_pow] using congrArg φ hζ.pow_eq_one
  have hnorm: ‖φ ζ‖ = 1:=
    Complex.norm_eq_one_of_pow_eq_one hpow hp.out.ne_zero
  have him: (φ ζ).im=0:=by
    simpa [RCLike.star_def] using (Complex.conj_eq_iff_im.mp hstar)
  let r :ℝ:= (φ ζ).re
  have hreal:φ ζ= (r:ℂ) :=by
    apply Complex.ext <;> simp [r,him]
  rw [hreal] at hnorm
  have hr_abs: |r| = 1:=by
    simpa [Complex.norm_real] using hnorm
  have hr_sq:r^2=1:=by
    have hsquare:=congrArg (fun t :ℝ=> t ^2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · have hφζ:φ ζ=1:=by
      calc
        φ ζ = (r:ℂ) :=hreal
        _= (1:ℂ) :=by simp [hr]
    have hζeq:ζ=1:=φ.injective <| by simpa using hφζ
    exact (hζ.ne_one hp.out.one_lt) hζeq
  · have hφζ:φ ζ= -1:=by
      calc
        φ ζ = (r:ℂ) :=hreal
        _= (-1:ℂ) :=by simp [hr]
    have hpo:Odd p :=hp.out.odd_of_ne_two hp_odd'
    have: ((-1:ℂ) ^ p) = 1:=by simpa [hφζ] using hpow
    have hneg: (-1:ℂ) = 1:=by simpa [Odd.neg_one_pow hpo] using this
    have hneq: (-1:ℂ) ≠ 1:=by norm_num
    exact hneq hneg
omit [IsCMField K] in
lemma uA (hp_odd':p ≠ 2) :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) : K) ∉
      Set.range (algebraMap (oMR K) K) :=by
  rintro ⟨x,hx⟩
  have hxmem: (algebraMap (oMR K) K x) ∈
      oMR K :=x.2
  have hzmem: (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) : K) ∈
      oMR K :=by
    simpa [hx] using hxmem
  exact zu (p:=p) (K:=K) hp_odd' hzmem
omit [IsCMField K] in
lemma zJ (hp_odd':p ≠ 2) :
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ∉
      Set.range (algebraMap (𝓞 (oMR K)) (𝓞 K)) :=by
  rintro ⟨x,hx⟩
  apply uA (p:=p) (K:=K) hp_odd'
  refine ⟨(x:oMR K),?_⟩
  exact congrArg (fun y :𝓞 K=> (y:K)) hx
lemma we (hp_odd':p ≠ 2) :
    Algebra.adjoin (oMR K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) : K)} : Set K) = ⊤ :=by
  let L :IntermediateField (oMR K) K :=
    IntermediateField.adjoin (oMR K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) : K)} : Set K)
  have hL:L= ⊤ :=by
    have hprime:Nat.Prime (Module.finrank (oMR K) K) :=by
      simpa [sg (K:=K)] using Nat.prime_two
    have hsimple:=
      ((IntermediateField.isSimpleOrder_of_finrank_prime (oMR K) K
          hprime).eq_bot_or_eq_top L)
    refine hsimple.resolve_left ?_
    intro hbot
    have hzeta_mem: (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) : K) ∈ L:=
      IntermediateField.subset_adjoin _ _ (by simp)
    rw [hbot,IntermediateField.mem_bot] at hzeta_mem
    exact uA (p:=p) (K:=K) hp_odd' hzeta_mem
  have hzeta_alg:IsAlgebraic (oMR K)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) : K)) :=
    Algebra.IsAlgebraic.isAlgebraic _
  exact Algebra.adjoin_eq_top_of_primitive_element hzeta_alg hL
omit [IsCMField K] in
lemma yb (hp_odd':p ≠ 2) :
    IsUnit (1+ ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K)) :=by
  have h :=
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.geom_sum_isUnit
      hp.out.two_le (Nat.coprime_two_left.mpr (hp.out.odd_of_ne_two hp_odd'))
  simpa [Finset.sum_range_succ] using h
omit [IsCMField K] in
lemma si:
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) ^ (p-1) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) = 1:=
  rQ p K
omit [IsCMField K] in
lemma uB:
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger^ (p-1) : 𝓞 K) = 1:=by
  simpa [mul_comm] using si (p:=p) (K:=K)
omit [IsCMField K] in
lemma xS (hp_odd':p ≠ 2) :
    IsUnit (1+ ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) ^ (p-1)) :=by
  let ζi:𝓞 K:= (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hzeta_unit:IsUnit (ζi^ (p-1) : 𝓞 K) :=by
    simpa using! (IsCyclotomicExtension.zeta_spec p ℚ K).unit'.isUnit.pow (p-1)
  have hmul: (ζi^ (p-1) : 𝓞 K) * (1+ζi) = 1+ζi^ (p-1) :=by
    rw [mul_add,mul_one,si (p:=p) (K:=K)]
    ring
  rw [← hmul]
  exact hzeta_unit.mul (yb (p:=p) (K:=K) hp_odd')
lemma s2:
    (algebraMap (𝓞 (oMR K)) (𝓞 K)) (piPlus p K) =
      (2:𝓞 K) - (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger-
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger^ (p-1) :=by
  let ζi:𝓞 K:= (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [ww]
  have hconj:NumberField.IsCMField.ringOfIntegersComplexConj K (ζi-1) =
      ζi^ (p-1) - 1:=by
    rw [map_sub,map_one,rT]
  calc
    (ζi-1) * NumberField.IsCMField.ringOfIntegersComplexConj K (ζi-1)
        = (ζi-1) * (ζi^ (p-1) - 1) :=by rw [hconj]
    _=ζi*ζi^ (p-1) - ζi-ζi^ (p-1) + 1:=by
          ring
    _= (2:𝓞 K) - ζi-ζi^ (p-1) :=by
          rw [uB (p:=p) (K:=K)]
          ring_nf
lemma z0:
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.X^2+Polynomial.C (piPlus p K-2) * Polynomial.X+1:
        Polynomial (𝓞 (oMR K))) = 0:=by
  let ζi:𝓞 K:= (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hcalc:
      ζi^2+ (((2:𝓞 K) - ζi-ζi^ (p-1)) - 2) * ζi+1=0:=by
    calc
      ζi^2+ (((2:𝓞 K) - ζi-ζi^ (p-1)) - 2) * ζi+1
          = -(ζi^ (p-1) * ζi) + 1:=by ring
      _=0:=by
            rw [si (p:=p) (K:=K)]
            norm_num
  simpa [Polynomial.aeval_def,s2,
    pow_two,map_sub,add_assoc,add_left_comm,add_comm,mul_assoc,mul_left_comm,mul_comm]
    using! hcalc
lemma vv (hp_odd':p ≠ 2) :
    minpoly (𝓞 (oMR K))
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) =
      (Polynomial.X^2+Polynomial.C (piPlus p K-2) * Polynomial.X+1:
        Polynomial (𝓞 (oMR K))) :=by
  let A :=𝓞 (oMR K)
  let ζi:𝓞 K:= (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hint:IsIntegral A ζi:=IsIntegralClosure.isIntegral A K ζi
  have hdeg:
      (Polynomial.X^2+Polynomial.C (piPlus p K-2) * Polynomial.X+1:
          Polynomial A).degree ≤
        (minpoly A ζi).degree:=by
    have hnatdeg:2 ≤ (minpoly A ζi).natDegree:=
      (minpoly.two_le_natDegree_iff hint).2
        (zJ (p:=p) (K:=K) hp_odd')
    have hpoly_deg:
        (Polynomial.X^2+Polynomial.C (piPlus p K-2) * Polynomial.X+1:
          Polynomial A).degree=2:=by
      simpa [one_mul,Polynomial.C_1] using
        (Polynomial.degree_quadratic
          (R:=A)
          (a:= (1:A))
          (b:=piPlus p K-2)
          (c:= (1:A))
          one_ne_zero)
    rw [hpoly_deg,Polynomial.degree_eq_natDegree (minpoly.ne_zero hint)]
    exact_mod_cast hnatdeg
  symm
  refine IsIntegrallyClosed.minpoly.unique (R:=A) (S:=𝓞 K) (s:=ζi) ?_ ?_ ?_
  · simpa [Polynomial.C_1] using
      (Polynomial.isMonicOfDegree_add_add_two (a:=piPlus p K-2) (b:= (1:A))).monic
  · exact z0 (p:=p) (K:=K)
  · intro Q hQ hQroot
    exact hdeg.trans (minpoly.min (A:=A) (x:=ζi) hQ hQroot)
lemma ud (hp_odd':p ≠ 2) :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.derivative
        (minpoly (𝓞 (oMR K))
          ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K))) =
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger^ (p-1) :=by
  let ζi:𝓞 K:= (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have htwo:
      (algebraMap (𝓞 (oMR K)) (𝓞 K)) 2 = (2:𝓞 K) :=by
    simpa using map_natCast (algebraMap (𝓞 (oMR K)) (𝓞 K)) 2
  rw [vv (p:=p) (K:=K) hp_odd']
  simpa [Polynomial.aeval_def,s2,
    map_sub,htwo,add_assoc,add_left_comm,add_comm,mul_assoc,mul_left_comm,
    mul_comm] using
    (show ((1+1:𝓞 K) * ζi) + (((2:𝓞 K) - ζi-ζi^ (p-1)) - 2) =
        ζi-ζi^ (p-1) by ring)
omit [IsCMField K] in
lemma wh (hp_odd':p ≠ 2) :
    Ideal.span
        ({((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:𝓞 K) -
            (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger^ (p-1)} :
          Set (𝓞 K)) =
      qt p K:=by
  let ζi:𝓞 K:= (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [qt]
  have hcalc:
      (ζi-1) * (1+ζi^ (p-1)) = ζi-ζi^ (p-1) :=by
    have hmul:ζi*ζi^ (p-1) = 1:=uB (p:=p) (K:=K)
    calc
      (ζi-1) * (1+ζi^ (p-1)) = ζi-1+ (ζi*ζi^ (p-1) - ζi^ (p-1)) :=by
        ring
      _=ζi-ζi^ (p-1) :=by
        rw [hmul]
        ring
  rw [← hcalc,Ideal.span_singleton_mul_right_unit]
  exact xS (p:=p) (K:=K) hp_odd'
lemma w4 (hp_odd':p ≠ 2) :
    differentIdeal (𝓞 (oMR K)) (𝓞 K) = qt p K:=by
  let A :=𝓞 (oMR K)
  let B :=𝓞 K
  let PPlus:Ideal A :=qX p K
  let P :Ideal B :=qt p K
  have hPPlus0:PPlus ≠ ⊥ :=by
    intro hbot
    have hmap:Ideal.map (algebraMap A B) PPlus=P^2:=by
      simpa [A,B,PPlus,P] using sf (p:=p) (hp_odd:=hp_odd') (K:=K)
    rw [hbot,Ideal.map_bot] at hmap
    exact (pow_ne_zero 2 (v3 p K)) hmap.symm
  have hle:differentIdeal A B ≤ P:=by
    have:PPlus.IsMaximal:=Ideal.IsPrime.isMaximal inferInstance hPPlus0
    have hdiv:P ∣ differentIdeal A B:=by
      have hpow:P^2 ∣ Ideal.map (algebraMap A B) PPlus:=by
        rw [sf (p:=p) (hp_odd:=hp_odd') (K:=K)]
      simpa [A,B,P,PPlus] using
        (pow_sub_one_dvd_differentIdeal (A:=A) (B:=B) (p:=PPlus) P 2 hPPlus0 hpow)
    exact Ideal.dvd_iff_le.mp hdiv
  have hmem:
      Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
          (Polynomial.derivative
            (minpoly A ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger:B))) ∈
        differentIdeal A B:=
    aeval_derivative_mem_differentIdeal (A:=A)
      (K:=oMR K) (L:=K) (B:=B)
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger)
      (we (p:=p) (K:=K) hp_odd')
  have hP_le:P ≤ differentIdeal A B:=by
    change qt p K ≤ differentIdeal A B
    rw [← wh (p:=p) (K:=K) hp_odd']
    rw [Ideal.span_singleton_le_iff_mem]
    convert hmem using 1
    symm
    exact ud
      (p:=p) (K:=K) hp_odd'
  exact le_antisymm hle hP_le
lemma vE (hp_odd':p ≠ 2) :
    Ideal.absNorm (differentIdeal (𝓞 (oMR K)) (𝓞 K)) = p:=by
  rw [w4 (p:=p) (K:=K) hp_odd',
    qt]
  rw [Ideal.absNorm_span_singleton,
    (IsCyclotomicExtension.zeta_spec p ℚ K).norm_toInteger_sub_one_of_prime_ne_two' hp_odd']
  simp [Int.natAbs_natCast]
lemma xa (hp_odd':p ≠ 2) :
    (NumberField.discr (oMR K)).natAbs=p^ ((p-3) / 2) :=by
  let L :=oMR K
  have hmain:=NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K:=L) (𝒪:=𝓞 L) (L:=K) (𝒪':=𝓞 K)
  have hdiscrK: (NumberField.discr K).natAbs=p^ (p-2) :=by
    rw [IsCyclotomicExtension.Rat.discr_prime (p:=p) (K:=K)]
    simp [Int.natAbs_mul]
  have hfin:Module.finrank L K=2:=by
    simpa [L] using (sg (K:=K))
  have hp3:3 ≤ p:=by
    have hp2:2 ≤ p:=hp.out.two_le
    omega
  rw [hdiscrK,vE (p:=p)
      (K:=K) hp_odd'] at hmain
  have hmain2:p^ (p-2) = p* (NumberField.discr L).natAbs^2:=by
    conv_rhs=> rw [← hfin]
    exact hmain
  have hsq: (NumberField.discr L).natAbs^2=p^ (p-3) :=by
    have hmain':p*p^ (p-3) = p* (NumberField.discr L).natAbs^2:=by
      calc
        p*p^ (p-3) = p^ (p-2) :=by
          rw [show p -2= (p-3) + 1 by omega,pow_succ',mul_comm]
        _=p* (NumberField.discr L).natAbs^2:=hmain2
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos hmain'.symm
  have hpow: (p^ ((p-3) / 2)) ^ 2=p^ (p-3) :=by
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n,hn⟩
    have hdiv: (p-3) / 2=n-1:=by
      rw [hn,show 2 *n+1-3=2* (n-1) by omega,
        Nat.mul_div_right _ (by decide:0 < 2)]
    calc
      (p^ ((p-3) / 2)) ^ 2= (p^ (n-1)) ^ 2:=by rw [hdiv]
      _=p^ ((n-1) * 2) :=by rw [← pow_mul]
      _=p^ (p-3) :=by
            congr
            rw [hn]
            omega
  have hsq': (NumberField.discr L).natAbs^2= (p^ ((p-3) / 2)) ^ 2:=by
    rw [hpow,hsq]
  have:=congrArg Nat.sqrt hsq'
  simpa [Nat.sqrt_eq'] using this
lemma xK (hp_odd':p ≠ 2) :
    |((NumberField.discr (oMR K) : ℤ) : ℝ)| =
      (p:ℝ) ^ ((p-3) / 2) :=by
  have habs: (((NumberField.discr (oMR K)).natAbs:ℕ) : ℝ) =
      |((NumberField.discr (oMR K) : ℤ) : ℝ)| :=by
    convert
      (Nat.cast_natAbs (α:=ℝ) (NumberField.discr (oMR K))) using 1
    simp
  rw [← habs,xa (p:=p) (K:=K) hp_odd',Nat.cast_pow]
theorem yR (hp_odd':p ≠ 2) :
    (h K :ℝ) =
      NumberField.dedekindZeta_residue K *
        ((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ (p-2))) /
          ((2*Real.pi) ^ ((p-1) / 2) * Units.regulator K)) :=by
  have hp_gt2:2 < p:=lt_of_le_of_ne hp.out.two_le (by simpa using hp_odd'.symm)
  have hreal:NumberField.InfinitePlace.nrRealPlaces K =0:=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n:=p) (K:=K) hp_gt2
  have hcomplex:NumberField.InfinitePlace.nrComplexPlaces K = (p-1) / 2:=by
    simpa [Nat.totient_prime hp.out] using
      (IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n:=p) (K:=K))
  rw [h_formula (K:=K),hreal,hcomplex,
    x3 (p:=p) (K:=K) hp_odd',
    y9 (p:=p) (K:=K)]
  simp [mul_assoc,mul_comm]
end KummerCriterion
end
end Module14
-- Source: KummerCriterion.HMinus.LValueReduction.Factors
section Module15
noncomputable section
open NumberField
namespace KummerCriterion
section Factors
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
def rk:ℂ:=
  (((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ (p-2))) /
    ((2*Real.pi) ^ ((p-1) / 2) * Units.regulator K) : ℝ) : ℂ)
lemma y1 (hp_odd':p ≠ 2) :
    ((h K :ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) *
        rk (p:=p) (K:=K) :=by
  simpa [rk] using congrArg (fun x :ℝ=> (x:ℂ))
    (yR (p:=p) (K:=K) hp_odd')
def ql:ℂ:=
  (((((Units.torsionOrder (oMR K) : ℝ) *
      Real.sqrt |discr (oMR K)|) /
    (2^InfinitePlace.nrRealPlaces (oMR K) *
      (2*Real.pi) ^ InfinitePlace.nrComplexPlaces (oMR K) *
        Units.regulator (oMR K)) : ℝ) : ℂ))
lemma yL:
    ((hPlus K :ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue (oMR K) : ℝ) : ℂ) *
        ql (K:=K) :=by
  simpa [ql] using congrArg (fun x :ℝ=> (x:ℂ))
    (hPlus_formula (K:=K))
theorem vX (hp_odd':p ≠ 2) :
    ql (K:=K) =
      (((((2:ℝ) * Real.sqrt ((p:ℝ) ^ ((p-3) / 2))) /
        (2^ ((p-1) / 2:ℕ) * Units.regulator (oMR K)) : ℝ) :
        ℂ)) :=by
  rw [ql]
  congr 1
  rw [xc (K:=K),
    wz (p:=p) (K:=K),
    xK (p:=p) (K:=K) hp_odd']
  norm_num
theorem zM
    {KplusResidue:ℂ}
    (hresPlus:
      ((NumberField.dedekindZeta_residue (oMR K) : ℝ) : ℂ) =
        KplusResidue) :
    ((hPlus K :ℕ) : ℂ) =
      ql (K:=K) * KplusResidue:=by
  rw [yL (K:=K),hresPlus]
  ring
omit [IsCMField K] in
lemma wA:
  ql (K:=K) ≠ 0:=by
  let L :=oMR K
  let A :ℝ:=
    2^InfinitePlace.nrRealPlaces L *
      (2*Real.pi) ^ InfinitePlace.nrComplexPlaces L *Units.regulator L
  let B :ℝ:= (Units.torsionOrder L :ℝ) * Real.sqrt |discr L|
  have hA_pos:0 < A:=by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hB_pos:0 < B:=by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  have hq_pos:0 < B/A:=div_pos hB_pos hA_pos
  change (((B/A:ℝ) : ℂ) ≠ 0)
  exact_mod_cast hq_pos.ne'
def qF:ℂ:=
  rk (p:=p) (K:=K) /
    ql (K:=K)
theorem w7
    (hp_odd':p ≠ 2) :
    qF (p:=p) (K:=K) =
      ((((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ (p-2))) /
        ((2*Real.pi) ^ ((p-1) / 2) * Real.sqrt ((p:ℝ) ^ ((p-3) / 2))) : ℝ) : ℂ)) :=by
  let L :=oMR K
  have hLreg_ne:Units.regulator L ≠ 0 :=
    (Units.regulator_pos L).ne'
  have hp_pos:0 < (p:ℝ) :=by
    exact_mod_cast hp.out.pos
  have hsqrt_pos:0 < Real.sqrt ((p:ℝ) ^ ((p-3) / 2)) :=
    Real.sqrt_pos.2 <| pow_pos hp_pos _
  have hsqrt_ne:Real.sqrt ((p:ℝ) ^ ((p-3) / 2)) ≠ 0:=hsqrt_pos.ne'
  have hpow_pi_ne: ((2*Real.pi) ^ ((p-1) / 2:ℕ) : ℝ) ≠ 0:=by
    positivity
  have hpow_two_ne: (2:ℝ) ^ ((p-3) / 2:ℕ) ≠ 0:=by
    positivity
  have hreg:
      Units.regulator K =
        (2:ℝ) ^ ((p-3) / 2:ℕ) * Units.regulator L :=
    (div_eq_iff hLreg_ne).mp <| by
      simpa [L] using
        (vG (p:=p) (K:=K) hp_odd':_)
  have hexp: ((p-1) / 2:ℕ) = ((p-3) / 2) + 1:=by
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n,hn⟩
    have hp3:3 ≤ p:=by
      have hp2:2 ≤ p:=hp.out.two_le
      omega
    have hn_pos:0 < n:=by
      rw [hn] at hp3
      omega
    have hdiv1: (p-1) / 2=n:=by
      rw [hn,show 2 *n+1-1=2*n by omega,
        Nat.mul_div_right _ (by decide:0 < 2)]
    have hdiv2: (p-3) / 2=n-1:=by
      rw [hn,show 2 *n+1-3=2* (n-1) by omega,
        Nat.mul_div_right _ (by decide:0 < 2)]
    rw [hdiv1,hdiv2]
    exact (Nat.sub_add_cancel (n:=n) (m:=1) (Nat.succ_le_of_lt hn_pos)).symm
  have hpow_two:
      (2:ℝ) ^ ((p-1) / 2:ℕ) =
        2* (2:ℝ) ^ ((p-3) / 2:ℕ) :=by
    rw [hexp,pow_succ]
    ring
  rw [qF,rk,
    vX (p:=p) (K:=K) hp_odd']
  suffices hreal:
      ((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ (p-2))) /
          ((2*Real.pi) ^ ((p-1) / 2) * Units.regulator K)) /
        (((2:ℝ) * Real.sqrt ((p:ℝ) ^ ((p-3) / 2))) /
          (2^ ((p-1) / 2:ℕ) * Units.regulator L)) =
      ((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ (p-2))) /
        ((2*Real.pi) ^ ((p-1) / 2) * Real.sqrt ((p:ℝ) ^ ((p-3) / 2))) : ℝ) by
    simpa [Complex.ofReal_div] using congrArg (fun x :ℝ=> (x:ℂ)) hreal
  rw [hreg,hpow_two]
  field_simp [hLreg_ne,hsqrt_ne,hpow_pi_ne,hpow_two_ne]
theorem ss
    (hp_odd':p ≠ 2) :
    qF (p:=p) (K:=K) =
      ((((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ ((p-1) / 2))) /
        (2*Real.pi) ^ ((p-1) / 2) : ℝ) : ℂ)) :=by
  let a :ℕ:= (p-1) / 2
  let b :ℕ:= (p-3) / 2
  have hp_pos:0 < (p:ℝ) :=by
    exact_mod_cast hp.out.pos
  have hpowA_nonneg:0 ≤ (p:ℝ) ^ a:=by
    positivity
  have hsqrtB_ne:Real.sqrt ((p:ℝ) ^ b) ≠ 0:=
    Real.sqrt_ne_zero'.2 <| pow_pos hp_pos _
  have hpow_pi_ne: ((2*Real.pi) ^ a:ℝ) ≠ 0:=by
    positivity
  have hsplit_exp:p-2=a+b:=by
    dsimp [a,b]
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n,hn⟩
    rw [hn]
    omega
  have hsqrt_split:
      Real.sqrt ((p:ℝ) ^ (p-2)) =
        Real.sqrt ((p:ℝ) ^ a) * Real.sqrt ((p:ℝ) ^ b) :=by
    rw [hsplit_exp,pow_add,Real.sqrt_mul hpowA_nonneg]
  suffices hreal:
      ((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ (p-2))) /
          ((2*Real.pi) ^ a*Real.sqrt ((p:ℝ) ^ b))) =
        ((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ a)) / (2*Real.pi) ^ a:ℝ) by
    rw [w7 (p:=p) (K:=K) hp_odd']
    simpa [a,b,Complex.ofReal_div] using congrArg (fun x :ℝ=> (x:ℂ)) hreal
  rw [hsqrt_split]
  field_simp [hsqrtB_ne,hpow_pi_ne]
abbrev rj:ℂ:=
  ql (K:=K)
omit hp [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
lemma u8:
    rk (p:=p) (K:=K) =
      qF (p:=p) (K:=K) *
        rj (K:=K) :=by
  symm
  rw [qF,rj,div_eq_mul_inv,mul_assoc,
    inv_mul_cancel₀ (wA (K:=K)),mul_one]
end Factors
end KummerCriterion
end
end Module15
-- Source: KummerCriterion.LValueAtOne.ComplexBounds
section Module16
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p:ℕ) [hp:Fact p.Prime]
lemma sP {a:ZMod p} (ha:a ≠ 0) :
    (a.val/p:ℝ) ∈ Set.Ioo 0 1:=by
  have hp_pos:0 < p:=hp.out.pos
  have hval_pos:0 < a.val:=by
    by_contra h
    have hval_zero:a.val=0:=Nat.eq_zero_of_not_pos h
    exact ha <| (ZMod.val_eq_zero a).mp hval_zero
  refine Set.mem_Ioo.mpr ⟨?_,?_⟩
  · exact div_pos (Nat.cast_pos.mpr hval_pos) (Nat.cast_pos.mpr hp_pos)
  · exact (div_lt_one (Nat.cast_pos.mpr hp_pos)).2 <| Nat.cast_lt.mpr (ZMod.val_lt a)
lemma xy (a:ZMod p) (s:ℂ) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle a) s =HurwitzZeta.sinZeta (a.val/p:ℝ) s :=by
  rw [ZMod.toAddCircle_apply]
lemma sj (t:ℝ) :
    (1:ℂ) - Complex.exp (t*Complex.I) =
      (2*Real.sin (t/2) : ℝ) *
        (Real.cos (t/2-Real.pi/2) + Real.sin (t/2-Real.pi/2) * Complex.I) :=by
  calc
    (1:ℂ) - Complex.exp (t*Complex.I)
        = ((1-Real.cos t :ℝ) : ℂ) + (-Real.sin t :ℝ) * Complex.I:=by
            rw [Complex.exp_ofReal_mul_I]
            simp [sub_eq_add_neg,add_comm,add_left_comm,add_assoc]
    _= ((2*Real.sin (t/2) ^ 2:ℝ) : ℂ) +
          (-(2*Real.sin (t/2) * Real.cos (t/2)) : ℝ) * Complex.I:=by
            rw [show t =2* (t/2) by ring,Real.cos_two_mul,Real.sin_two_mul]
            have hsq:1- (2*Real.cos (t/2) ^ 2-1) = 2*Real.sin (t/2) ^ 2:=by
              nlinarith [Real.sin_sq_add_cos_sq (t/2)]
            rw [hsq]
            ring_nf
    _= (2*Real.sin (t/2) : ℝ) *
          (Real.cos (t/2-Real.pi/2) + Real.sin (t/2-Real.pi/2) * Complex.I) :=by
            simp [Real.cos_sub_pi_div_two,Real.sin_sub_pi_div_two,sq]
            ring
lemma y5 {t:ℝ} (ht₀:0 < t) (ht₂π:t < 2*Real.pi) :
    Complex.arg ((1:ℂ) - Complex.exp (t*Complex.I)) = t/2-Real.pi/2:=by
  have hs:0 < 2*Real.sin (t/2) :=by
    have hhalf:0 < t/2 ∧ t/2 < Real.pi:=by
      constructor <;> nlinarith [ht₀,ht₂π,Real.pi_pos]
    have hsin:0 < Real.sin (t/2) :=Real.sin_pos_of_mem_Ioo hhalf
    positivity
  have hθ:t/2-Real.pi/2 ∈ Set.Ioc (-Real.pi) Real.pi:=by
    constructor
    · nlinarith [ht₀,Real.pi_pos]
    · nlinarith [ht₂π]
  rw [sj]
  simpa using (Complex.arg_mul_cos_add_sin_mul_I hs hθ)
lemma xT {t:ℝ} (ht₀:0 < t) (ht₂π:t < 2*Real.pi) :
    (-Complex.log ((1:ℂ) - Complex.exp (t*Complex.I))).im=Real.pi/2-t/2:=by
  rw [show (-Complex.log ((1:ℂ) - Complex.exp (t*Complex.I))).im=
      -(Complex.log ((1:ℂ) - Complex.exp (t*Complex.I))).im by simp]
  rw [Complex.log_im,y5 ht₀ ht₂π]
  ring
lemma yZ (x r :ℝ) (hr₀:0 ≤ r) (hr₁:r < 1) :
    HasSum (fun n :ℕ=> (r^n/n) * Real.sin (2*Real.pi*x*n))
      (-Complex.log ((1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I))).im:=by
  let z :ℂ:= (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)
  have hz: ‖z‖ < 1:=by
    have hexp: ‖Complex.exp (2*Real.pi*x*Complex.I)‖ = 1:=by
      simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2*Real.pi*x)
    have hz': ‖z‖ = r:=by
      calc
        ‖z‖ = ‖(r:ℂ)‖ * ‖Complex.exp (2*Real.pi*x*Complex.I)‖ :=by
          simp [z]
        _=r*1:=by rw [Complex.norm_real,Real.norm_of_nonneg hr₀,hexp]
        _=r:=by ring
    rw [hz']
    exact hr₁
  refine (Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hz)).congr_fun ?_
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [z]
  · rw [show z = (r:ℂ) * Complex.exp ((2*Real.pi*x:ℝ) * Complex.I) by simp [z]]
    rw [Complex.div_natCast_im,mul_pow,Complex.mul_im,← Complex.ofReal_pow,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,add_zero,← Complex.exp_nat_mul]
    rw [show (n:ℂ) * ((2*Real.pi*x:ℝ) * Complex.I) =
        ((2*Real.pi*x*n:ℝ) : ℂ) * Complex.I by
          norm_num
          ring]
    rw [Complex.exp_ofReal_mul_I_im]
    ring
lemma t0 (x r :ℝ) (hr₀:0 ≤ r) (hr₁:r < 1) :
    HasSum (fun n :ℕ=> (r^n/n) * Real.cos (2*Real.pi*x*n))
      (-Real.log ‖(1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)‖) :=by
  let z :ℂ:= (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)
  have hz: ‖z‖ < 1:=by
    have hexp: ‖Complex.exp (2*Real.pi*x*Complex.I)‖ = 1:=by
      simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2*Real.pi*x)
    have hz': ‖z‖ = r:=by
      calc
        ‖z‖ = ‖(r:ℂ)‖ * ‖Complex.exp (2*Real.pi*x*Complex.I)‖ :=by
          simp [z]
        _=r*1:=by rw [Complex.norm_real,Real.norm_of_nonneg hr₀,hexp]
        _=r:=by ring
    rw [hz']
    exact hr₁
  have hsum:
      HasSum (fun n :ℕ=> (z^n/n).re) (-Complex.log ((1:ℂ) - z)).re:=
    (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz))
  have hsum':
      HasSum (fun n :ℕ=> (r^n/n) * Real.cos (2*Real.pi*x*n))
        (-Complex.log ((1:ℂ) - z)).re:=by
    refine hsum.congr_fun ?_
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [z]
    · rw [show z = (r:ℂ) * Complex.exp ((2*Real.pi*x:ℝ) * Complex.I) by simp [z]]
      rw [Complex.div_natCast_re,mul_pow,Complex.mul_re,← Complex.ofReal_pow,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,← Complex.exp_nat_mul]
      rw [show (n:ℂ) * ((2*Real.pi*x:ℝ) * Complex.I) =
          ((2*Real.pi*x*n:ℝ) : ℂ) * Complex.I by
            norm_num
            ring]
      rw [Complex.exp_ofReal_mul_I_re]
      ring
  have hvalue: (-Complex.log ((1:ℂ) - z)).re= -Real.log ‖(1:ℂ) - z‖ :=by
    simpa using congrArg Neg.neg (Complex.log_re ((1:ℂ) - z))
  simpa [hvalue,z] using hsum'
lemma rN {t:ℝ} (ht₀:0 < t) (ht₂π:t < 2*Real.pi) :
    ‖(1:ℂ) - Complex.exp (t*Complex.I)‖ = 2*Real.sin (t/2) :=by
  have hs:0 < 2*Real.sin (t/2) :=by
    have hhalf:0 < t/2 ∧ t/2 < Real.pi:=by
      constructor <;> nlinarith [ht₀,ht₂π,Real.pi_pos]
    have hsin:0 < Real.sin (t/2) :=Real.sin_pos_of_mem_Ioo hhalf
    positivity
  calc
    ‖(1:ℂ) - Complex.exp (t*Complex.I)‖
        = ‖((2*Real.sin (t/2) : ℝ) : ℂ)‖ *
            ‖Real.cos (t/2-Real.pi/2) + Real.sin (t/2-Real.pi/2) * Complex.I‖ :=by
              rw [sj,Complex.norm_mul]
    _= |2*Real.sin (t/2)| * 1:=by
          rw [Complex.norm_real,Real.norm_eq_abs]
          have hunit:
              ‖Real.cos (t/2-Real.pi/2) +
                  Real.sin (t/2-Real.pi/2) * Complex.I‖ = 1:=by
            simpa using Complex.norm_cos_add_sin_mul_I (t/2-Real.pi/2)
          rw [hunit]
    _=2*Real.sin (t/2) :=by rw [abs_of_pos hs,mul_one]
end LValueAtOne
end KummerCriterion
end
end Module16
-- Source: KummerCriterion.LValueAtOne.DirichletBounds
section Module17
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
lemma v9
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a:ℕ → ℝ} {z:ℕ → E} {B:ℝ}
    (ha:Antitone a) (ha_nonneg: ∀ n,0 ≤ a n)
    (hbound: ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤ B) (n:ℕ) :
    ‖∑ i ∈ Finset.range n,a i • z i‖ ≤ B*a 0:=by
  have hB:0 ≤ B:=by
    simpa using hbound 0
  rcases n.eq_zero_or_pos with rfl | hn
  · have:0 ≤ B*a 0:=mul_nonneg hB (ha_nonneg 0)
    simpa using this
  · rw [Finset.sum_range_by_parts (f:=a) (g:=z) (n:=n)]
    have hsum_le:
        ‖∑ i ∈ Finset.range (n-1),
            (a (i+1) - a i) • ∑ j ∈ Finset.range (i+1),z j‖ ≤
          B* (a 0 -a (n-1)) :=by
      calc
        ‖∑ i ∈ Finset.range (n-1),
            (a (i+1) - a i) • ∑ j ∈ Finset.range (i+1),z j‖
            ≤ ∑ i ∈ Finset.range (n-1),
                ‖(a (i+1) - a i) • ∑ j ∈ Finset.range (i+1),z j‖ :=by
              simpa using norm_sum_le (Finset.range (n-1))
                (fun i => (a (i+1) - a i) • ∑ j ∈ Finset.range (i+1),z j)
        _ ≤ ∑ i ∈ Finset.range (n-1),B* (a i -a (i+1)) :=by
              refine Finset.sum_le_sum fun i hi=> ?_
              have hdiff_nonpos:a (i+1) - a i ≤ 0 :=sub_nonpos.mpr (ha (Nat.le_succ i))
              calc
                ‖(a (i+1) - a i) • ∑ j ∈ Finset.range (i+1),z j‖
                    = |a (i+1) - a i| * ‖∑ j ∈ Finset.range (i+1),z j‖ :=by
                        rw [norm_smul,Real.norm_eq_abs]
                _= (a i -a (i+1)) * ‖∑ j ∈ Finset.range (i+1),z j‖ :=by
                      rw [abs_of_nonpos hdiff_nonpos]
                      ring
                _ ≤ (a i -a (i+1)) * B:=by
                      gcongr
                      · exact sub_nonneg.mpr (ha (Nat.le_succ i))
                      · exact hbound (i+1)
                _=B* (a i -a (i+1)) :=by ring
        _=B* (a 0 -a (n-1)) :=by
              rw [← Finset.mul_sum]
              have htel':=Finset.sum_range_sub (f:=a) (n:=n-1)
              have htel: ∑ i ∈ Finset.range (n-1),(a i -a (i+1)) = a 0 -a (n-1) :=by
                calc
                  ∑ i ∈ Finset.range (n-1),(a i -a (i+1))
                      = ∑ i ∈ Finset.range (n-1),-((a (i+1) - a i)) :=by
                          refine Finset.sum_congr rfl fun i hi=> by ring
                  _= -∑ i ∈ Finset.range (n-1),(a (i+1) - a i) :=by
                        rw [Finset.sum_neg_distrib]
                  _=a 0-a (n-1) :=by linarith
              rw [htel]
    have hfirst: ‖a (n-1) • ∑ i ∈ Finset.range n,z i‖ ≤ B*a (n-1) :=by
      calc
        ‖a (n-1) • ∑ i ∈ Finset.range n,z i‖ =
            |a (n-1)| * ‖∑ i ∈ Finset.range n,z i‖ :=by
          rw [norm_smul,Real.norm_eq_abs]
        _=a (n-1) * ‖∑ i ∈ Finset.range n,z i‖ :=by
          rw [abs_of_nonneg (ha_nonneg _)]
        _ ≤ a (n-1) * B:=by
          gcongr
          · exact ha_nonneg _
          · exact hbound n
        _=B*a (n-1) :=by ring
    calc
      ‖a (n-1) • ∑ i ∈ Finset.range n,z i-
          ∑ i ∈ Finset.range (n-1),
            (a (i+1) - a i) • ∑ j ∈ Finset.range (i+1),z j‖
          ≤ ‖a (n-1) • ∑ i ∈ Finset.range n,z i‖ +
              ‖∑ i ∈ Finset.range (n-1),
                  (a (i+1) - a i) • ∑ j ∈ Finset.range (i+1),z j‖ :=by
              simpa [sub_eq_add_neg] using
                (norm_sub_le (a (n-1) • ∑ i ∈ Finset.range n,z i)
                  (∑ i ∈ Finset.range (n-1),
                    (a (i+1) - a i) • ∑ j ∈ Finset.range (i+1),z j))
      _ ≤ B*a (n-1) + B* (a 0 -a (n-1)) :=add_le_add hfirst hsum_le
      _=B*a 0:=by ring
lemma z8
    {E:Type*} [NormedAddCommGroup E]
    {z:ℕ → E} {B:ℝ}
    (hbound: ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤ B) (m n :ℕ) :
    ‖∑ i ∈ Finset.range n,z (m+i)‖ ≤ 2*B:=by
  have hshift:
      ∑ i ∈ Finset.range n,z (m+i) =
        ∑ i ∈ Finset.range (m+n),z i- ∑ i ∈ Finset.range m,z i:=by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm,add_left_comm,add_assoc] using (Finset.sum_range_add z m n).symm
  rw [hshift]
  calc
    ‖∑ i ∈ Finset.range (m+n),z i- ∑ i ∈ Finset.range m,z i‖
        ≤ ‖∑ i ∈ Finset.range (m+n),z i‖ + ‖∑ i ∈ Finset.range m,z i‖ :=by
            simpa [sub_eq_add_neg] using
              (norm_sub_le (∑ i ∈ Finset.range (m+n),z i) (∑ i ∈ Finset.range m,z i))
    _ ≤ B+B:=add_le_add (hbound _) (hbound _)
    _=2*B:=by ring
lemma rA
    {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a:ℕ → ℝ} {z:ℕ → E} {B:ℝ}
    (ha:Antitone a) (ha_nonneg: ∀ n,0 ≤ a n)
    (hbound: ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤ B) (m n :ℕ) :
    ‖∑ i ∈ Finset.range n,a (m+i) • z (m+i)‖ ≤ (2*B) * a m :=by
  simpa [two_mul,add_comm,add_left_comm,add_assoc,mul_add,add_mul,mul_comm,mul_left_comm,
    mul_assoc] using
    (v9
      (a:=fun k => a (m+k)) (z:=fun k => z (m+k)) (B:=2*B)
      (ha:=fun i j hij=> ha (Nat.add_le_add_left hij m))
      (ha_nonneg:=fun k => ha_nonneg (m+k))
      (hbound:=fun k => z8 (z:=z) (B:=B) hbound m k) n)
end KummerCriterion
end
end Module17
-- Source: KummerCriterion.LValueAtOne.Sine
section Module18
noncomputable section
open Filter
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p:ℕ) [hp:Fact p.Prime]
lemma x8 {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) (n:ℕ) :
    ‖∑ i ∈ Finset.range n,Real.sin (2*Real.pi*x*i)‖ ≤
      2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
  let z :ℂ:=Complex.exp ((2*Real.pi*x) * Complex.I)
  have hz_ne_one:z ≠ 1:=by
    intro hz
    have hexp:Complex.exp ((2*Real.pi*x) * Complex.I) = 1:=by simpa [z] using hz
    obtain ⟨m,hm⟩ :=Complex.exp_eq_one_iff.mp hexp
    have him:2*Real.pi*x= (m:ℝ) * (2*Real.pi) :=by
      simpa using congrArg Complex.im hm
    have hm_pos: (0:ℝ) < m:=by nlinarith [Real.pi_pos,hx₀,him]
    have hm_lt_one: (m:ℝ) < 1:=by nlinarith [Real.pi_pos,hx₁,him]
    have hm_pos_int:0 < m:=by exact_mod_cast hm_pos
    have hm_lt_one_int:m < 1:=by exact_mod_cast hm_lt_one
    lia
  have him:
      ((∑ i ∈ Finset.range n,z^i).im:ℝ) =
        ∑ i ∈ Finset.range n,Real.sin (2*Real.pi*x*i) :=by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun i _=> ?_
    rw [show z ^i=Complex.exp (((2*Real.pi*x*i:ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring,Complex.exp_ofReal_mul_I_im]
  have hgeom: ‖∑ i ∈ Finset.range n,z^i‖ ≤ 2/ ‖z-1‖ :=by
    calc
      ‖∑ i ∈ Finset.range n,z^i‖ = ‖(z^n-1) / (z-1)‖ :=by
        rw [geom_sum_eq hz_ne_one]
      _= ‖z^n-1‖ / ‖z-1‖ :=by rw [Complex.norm_div]
      _ ≤ 2/ ‖z-1‖ :=by
        have hden:0 < ‖z-1‖ :=norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne_one)
        have hnum: ‖z^n-1‖ ≤ 2:=by
          calc
            ‖z^n-1‖ ≤ ‖z^n‖ + ‖(1:ℂ)‖ :=norm_sub_le _ _
            _=1+1:=by
              rw [norm_pow]
              have hz_norm: ‖z‖ = 1:=by
                simpa [z] using Complex.norm_exp_ofReal_mul_I (2*Real.pi*x)
              rw [hz_norm]
              simp
            _=2:=by norm_num
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc
    ‖∑ i ∈ Finset.range n,Real.sin (2*Real.pi*x*i)‖
      = ‖((∑ i ∈ Finset.range n,z^i).im:ℝ)‖ :=by rw [him]
    _ ≤ ‖∑ i ∈ Finset.range n,z^i‖ :=by
      simpa using (RCLike.norm_im_le_norm (∑ i ∈ Finset.range n,z^i))
    _ ≤ 2/ ‖z-1‖ :=hgeom
    _=2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
      simp [z,norm_sub_rev]
lemma yi (x:ℝ) (i:ℕ) :
    Continuous fun s :ℝ=>
      Real.sin (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ)) :=by
  refine Continuous.div continuous_const ?_ ?_
  · exact Continuous.const_cpow Complex.continuous_ofReal (Or.inl (Nat.cast_add_one_ne_zero i))
  · intro s h
    exact (Nat.cast_add_one_ne_zero i) ((Complex.cpow_eq_zero_iff _ _).mp h).1
lemma yF (x s :ℝ) (hs:1 < s) :
    HasSum (fun n :ℕ=> Real.sin (2*Real.pi*x* (n+1)) / ((n+1:ℂ) ^ (s:ℂ)))
      (HurwitzZeta.sinZeta x s) :=by
  let f :ℕ → ℂ:=fun n => Real.sin (2*Real.pi*x*n) / ((n:ℂ) ^ (s:ℂ))
  have hfull:HasSum f (HurwitzZeta.sinZeta x s) :=by
    simpa [f] using HurwitzZeta.hasSum_nat_sinZeta x (show 1 < ((s:ℂ)).re by simpa)
  have hshift:HasSum (fun n :ℕ=> f (n+1)) (∑' n :ℕ,f (n+1)) :=
    ((summable_nat_add_iff 1).2 hfull.summable).hasSum
  have hfull':HasSum f (f 0 + ∑' n :ℕ,f (n+1)) :=hshift.zero_add
  have hvalue: (∑' n :ℕ,f (n+1)) = HurwitzZeta.sinZeta x s:=by
    have:=tendsto_nhds_unique hfull'.tendsto_sum_nat hfull.tendsto_sum_nat
    simpa [f,hs.ne'] using this
  exact hvalue ▸ hshift.congr_fun (fun n => by simp [f])
lemma z6 {x s :ℝ} (hx₀:0 < x) (hx₁:x < 1) (hs:1 ≤ s)
    (m n :ℕ) :
    ‖∑ i ∈ Finset.range n,
        Real.sin (2*Real.pi*x* (m+i+1)) / (((m+i+1:ℕ) : ℂ) ^ (s:ℂ))‖ ≤
      (4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖) *
        (1/ (m+1:ℝ) ^ s) :=by
  let a :ℕ → ℝ:=fun k => 1 / (k+1:ℝ) ^ s
  let z :ℕ → ℂ:=fun k => Real.sin (2*Real.pi*x* (k+1))
  have ha:Antitone a :=by
    intro i j hij
    have hij': (i+1:ℝ) ≤ j+1:=by exact_mod_cast Nat.succ_le_succ hij
    have hi_pos:0 < (i+1:ℝ) :=by positivity
    have hs_nonneg:0 ≤ s:=le_trans zero_lt_one.le hs
    have hpow: (i+1:ℝ) ^ s ≤ (j+1:ℝ) ^ s:=
      Real.rpow_le_rpow hi_pos.le hij' hs_nonneg
    simpa [a,one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hi_pos _) hpow
  have ha_nonneg: ∀ k,0 ≤ a k:=by
    intro k
    positivity
  have hzbound:
      ∀ k,‖∑ i ∈ Finset.range k,z i‖ ≤
        2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
    intro k
    have hsum:
        ∑ i ∈ Finset.range k,Real.sin (2*Real.pi*x* (i+1)) =
          ∑ i ∈ Finset.range (k+1),Real.sin (2*Real.pi*x*i) :=by
      simpa [Nat.cast_add,add_assoc,add_comm,add_left_comm] using
        (Finset.sum_range_add (fun i => Real.sin (2*Real.pi*x*i)) 1 k).symm
    rw [show (∑ i ∈ Finset.range k,z i) =
        ((∑ i ∈ Finset.range k,Real.sin (2*Real.pi*x* (i+1)) : ℝ) : ℂ) by
          simp [z,Complex.ofReal_sum]]
    rw [Complex.norm_real,hsum]
    exact x8 hx₀ hx₁ (k+1)
  calc
    ‖∑ i ∈ Finset.range n,
        Real.sin (2*Real.pi*x* (m+i+1)) / (((m+i+1:ℕ) : ℂ) ^ (s:ℂ))‖
        = ‖∑ i ∈ Finset.range n,a (m+i) • z (m+i)‖ :=by
            congr 1
            refine Finset.sum_congr rfl fun i hi=> ?_
            have hcpow:
                (((m+i+1:ℕ) : ℂ) ^ (s:ℂ)) =
                  ((((m+i+1:ℕ) : ℝ) ^ s:ℝ) : ℂ) :=by
              simpa using
                (Complex.ofReal_cpow (x:= (m+i+1:ℝ)) (by positivity) (y:=s)).symm
            rw [hcpow]
            simp [a,z,div_eq_mul_inv,mul_comm,mul_left_comm]
    _ ≤ (2* (2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖)) * a m :=
          rA ha ha_nonneg hzbound m n
    _= (4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖) *
          (1/ (m+1:ℝ) ^ s) :=by
          have hcoef:
              (2* (2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖)) =
                4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
            ring
          rw [hcoef]
lemma xF {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    ∃ l :ℝ,
      Tendsto
        (fun n ↦
          ∑ i ∈ Finset.range n,if i =0 then 0 else Real.sin (2*Real.pi*x*i) / i)
        atTop (𝓝 l) :=by
  let f :ℕ → ℝ:=fun n => if n =0 then 1 else 1 /n
  let z :ℕ → ℝ:=fun n => if n =0 then 0 else Real.sin (2*Real.pi*x*n)
  have hf:Antitone f :=by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [f]
      · simp [f,hb.ne']
        have hb1: (1:ℝ) ≤ b:=by exact_mod_cast Nat.succ_le_of_lt hb
        simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hb1
    · have hb:0 < b:=lt_of_lt_of_le ha hab
      simp [f,ha.ne',(Nat.ne_of_gt hb)]
      have ha': (0:ℝ) < a:=by exact_mod_cast ha
      have hab': (a:ℝ) ≤ b:=by exact_mod_cast hab
      simpa [one_div] using one_div_le_one_div_of_le ha' hab'
  have hf0:Tendsto f atTop (𝓝 0) :=by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa [f]
      using
        (tendsto_one_div_add_atTop_nhds_zero_nat:
          Tendsto (fun n :ℕ=> 1 / (n+1:ℝ)) atTop (𝓝 0))
  have hpartial:
      ∀ n,∑ i ∈ Finset.range n,z i=
        ∑ i ∈ Finset.range n,Real.sin (2*Real.pi*x*i) :=by
    intro n
    refine Finset.sum_congr rfl fun i _=> ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [z]
    · simp [z,hi.ne']
  have hbound:
      ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤
        2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
    intro n
    rw [hpartial]
    exact x8 hx₀ hx₁ n
  have hcauchy:=hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l,hl⟩ :=cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l,?_⟩
  have hseries:
      (fun n ↦ ∑ i ∈ Finset.range n,f i • z i) =
        fun n ↦
          ∑ i ∈ Finset.range n,if i =0 then 0 else Real.sin (2*Real.pi*x*i) / i:=by
    funext n
    refine Finset.sum_congr rfl fun i _=> ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f,z]
    · simp [f,z,hi.ne',smul_eq_mul,div_eq_mul_inv,mul_comm]
  exact hseries ▸ hl
lemma zT {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n,if i =0 then 0 else Real.sin (2*Real.pi*x*i) / i)
      atTop (𝓝 (Real.pi* (1/2-x))) :=by
  obtain ⟨l,hl⟩ :=xF hx₀ hx₁
  let coeff:ℕ → ℝ:=fun n =>
    if n =0 then 0 else Real.sin (2*Real.pi*x*n) / n
  have habel:
      Tendsto (fun r :ℝ=> ∑' n,coeff n *r^n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff:
      Set.EqOn
        (fun r :ℝ=> ∑' n,coeff n *r^n)
        (fun r :ℝ=>
          (-Complex.log ((1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I))).im)
        (Set.Ioo 0 1) :=by
    intro r hr
    have hr₀:0 ≤ r:=hr.1.le
    have hr₁:r < 1:=hr.2
    calc
      ∑' n :ℕ,coeff n *r^n
          = ∑' n :ℕ,(r^n/n) * Real.sin (2*Real.pi*x*n) :=by
              refine tsum_congr fun n :ℕ=> ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff,hn.ne',div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
      _= (-Complex.log ((1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I))).im:=
            (yZ x r hr₀ hr₁).tsum_eq
  have habel':
      Tendsto
        (fun r :ℝ=>
          (-Complex.log ((1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hslit:
      ((1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)) ∈ Complex.slitPlane:=by
    rw [Complex.mem_slitPlane_iff]
    left
    have hre:
        (((1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)).re:ℝ) =
          2*Real.sin (Real.pi*x) ^ 2:=by
      have hExp:
          (Complex.exp ((2*Real.pi*x) * Complex.I)).re=Real.cos (2*Real.pi*x) :=by
        simpa using (Complex.exp_ofReal_mul_I_re (2*Real.pi*x))
      rw [Complex.sub_re,Complex.one_re,hExp]
      have hsq:1-Real.cos (2*Real.pi*x) = 2*Real.sin (Real.pi*x) ^ 2:=by
        rw [show 2 *Real.pi*x=2* (Real.pi*x) by ring,Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi*x)]
      exact hsq
    rw [hre]
    have hxπ:Real.pi*x ∈ Set.Ioo 0 Real.pi:=by
      constructor <;> nlinarith [hx₀,hx₁,Real.pi_pos]
    have hsin:0 < Real.sin (Real.pi*x) :=Real.sin_pos_of_mem_Ioo hxπ
    positivity
  have hcont:
      Tendsto
        (fun r :ℝ=>
          (-Complex.log ((1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I))).im)
        (𝓝[<] 1) (𝓝 (Real.pi* (1/2-x))) :=by
    have hz:
        Tendsto
          (fun r :ℝ=> (1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I))
          (𝓝[<] 1)
          (𝓝 ((1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I))) :=by
      have hcont:
          Continuous fun r :ℝ=>
            (1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I) :=by
        continuity
      have hcont1:
          ContinuousAt
            (fun r :ℝ=>
              (1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)) 1 :=
        hcont.continuousAt
      convert tendsto_nhdsWithin_of_tendsto_nhds hcont1.tendsto using 1
      · simp
    have hlog:
        Tendsto
          (fun r :ℝ=>
            Complex.log ((1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)))
          (𝓝[<] 1)
          (𝓝 (Complex.log ((1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)))) :=
      hz.clog hslit
    have him0:
        Tendsto
          (fun r :ℝ=>
            (Complex.log ((1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I))).im)
          (𝓝[<] 1)
          (𝓝 ((Complex.log (((1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)))).im)) :=
      Complex.continuous_im.continuousAt.tendsto.comp hlog
    have hnegim:
        Tendsto
          (fun r :ℝ=>
            -((Complex.log
              ((1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I))).im))
          (𝓝[<] 1)
          (𝓝 (-((Complex.log
            (((1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)))).im))) :=
      him0.neg
    have ht₀:0 < 2*Real.pi*x:=by nlinarith [hx₀,Real.pi_pos]
    have ht₂π:2*Real.pi*x < 2*Real.pi:=by nlinarith [hx₁,Real.pi_pos]
    have hvalue:=xT ht₀ ht₂π
    have hvalue':
        -((Complex.log (((1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)))).im) =
          Real.pi* (1/2-x) :=by
      calc
        -((Complex.log (((1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)))).im) =
            Real.pi/2- (2*Real.pi*x) / 2:=by
              simpa using hvalue
        _=Real.pi* (1/2-x) :=by ring
    simpa [hvalue'] using hnegim
  have hl_eq:l=Real.pi* (1/2-x) :=tendsto_nhds_unique habel' hcont
  simpa [hl_eq] using hl
lemma zj {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    Tendsto
      (fun n :ℕ=> ∑ i ∈ Finset.range n,
        Real.sin (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (1:ℂ)))
      atTop (nhds (Real.pi* (1/2-x) : ℂ)) :=by
  let F :ℕ → ℂ:=fun n =>
    ((∑ i ∈ Finset.range n,
        if i =0 then 0 else Real.sin (2*Real.pi*x*i) / i:ℝ) : ℂ)
  have hbase:Tendsto F atTop (nhds (Real.pi* (1/2-x) : ℂ)) :=by
    simpa [F] using (zT hx₀ hx₁).ofReal
  have hshifted:Tendsto (fun n :ℕ=> F (n+1)) atTop (nhds (Real.pi* (1/2-x) : ℂ)) :=
    (tendsto_add_atTop_iff_nat 1).2 hbase
  refine hshifted.congr' <| Filter.Eventually.of_forall fun n => ?_
  have hsum:=
    Finset.sum_range_add
      (fun i :ℕ=> (((if i =0 then 0 else Real.sin (2*Real.pi*x*i) / i:ℝ)) : ℂ)) 1 n
  simpa [F,add_comm,add_left_comm,add_assoc] using hsum
lemma wX {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    UniformCauchySeqOn
      (fun n (s:ℝ) => ∑ i ∈ Finset.range n,
        Real.sin (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ)))
      atTop (Set.Ici 1) :=by
  rw [Metric.uniformCauchySeqOn_iff]
  let B :ℝ:=
    4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖
  have hxπ:Real.pi*x ∈ Set.Ioo 0 Real.pi:=by
    constructor <;> nlinarith [hx₀,hx₁,Real.pi_pos]
  have hsin:0 < Real.sin (Real.pi*x) :=Real.sin_pos_of_mem_Ioo hxπ
  have hdenom:0 < ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
    have htwo:0 < 2*Real.sin (Real.pi*x) :=by positivity
    have hunit_ne:
        Real.cos (Real.pi*x-Real.pi/2) +
            Real.sin (Real.pi*x-Real.pi/2) * Complex.I ≠ 0:=by
      have hunit_pos:
          0 < ‖Real.cos (Real.pi*x-Real.pi/2) +
              Real.sin (Real.pi*x-Real.pi/2) * Complex.I‖ :=by
        have hunit_pos':
            0 < ‖Complex.cos ((Real.pi*x-Real.pi/2:ℝ) : ℂ) +
                Complex.sin ((Real.pi*x-Real.pi/2:ℝ) : ℂ) * Complex.I‖ :=by
          rw [Complex.norm_cos_add_sin_mul_I]
          norm_num
        simpa [Complex.ofReal_cos,Complex.ofReal_sin] using hunit_pos'
      exact norm_pos_iff.mp hunit_pos
    have hfac_ne: ((2*Real.sin (Real.pi*x) : ℝ) : ℂ) ≠ 0:=by
      exact_mod_cast htwo.ne'
    have hzero: (1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I) ≠ 0:=by
      have hrewrite:
          (1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I) =
            (2*Real.sin ((2*Real.pi*x) / 2) : ℝ) *
              (Real.cos ((2*Real.pi*x) / 2-Real.pi/2) +
                Real.sin ((2*Real.pi*x) / 2-Real.pi/2) * Complex.I) :=by
        simpa [mul_assoc] using sj (2*Real.pi*x)
      rw [hrewrite]
      simpa [show (2*Real.pi*x) / 2=Real.pi*x by ring] using mul_ne_zero hfac_ne hunit_ne
    exact norm_pos_iff.mpr hzero
  have hB_pos:0 < B:=by
    positivity
  intro ε hε
  obtain ⟨N,hN⟩ :=exists_nat_one_div_lt (div_pos hε hB_pos)
  refine ⟨N,?_⟩
  have htail_bound:
      ∀ ⦃m n :ℕ⦄,N ≤ m → m ≤ n → ∀ s ∈ Set.Ici (1:ℝ),
        dist
            (∑ i ∈ Finset.range m,
              Real.sin (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ)))
            (∑ i ∈ Finset.range n,
              Real.sin (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ)))
          < ε :=by
    intro m n hm hmn s hs
    let term:ℕ → ℂ:=fun k =>
      Real.sin (2*Real.pi*x* (k+1)) / ((k+1:ℂ) ^ (s:ℂ))
    have hsplit:
        ∑ i ∈ Finset.range n,term i =
          ∑ i ∈ Finset.range m,term i + ∑ i ∈ Finset.range (n-m),term (m+i) :=by
      simpa [term,Nat.add_sub_of_le hmn] using Finset.sum_range_add term m (n-m)
    have hs':1 ≤ s:=hs
    rw [dist_eq_norm,norm_sub_rev]
    calc
      ‖∑ i ∈ Finset.range n,term i - ∑ i ∈ Finset.range m,term i‖
          = ‖∑ i ∈ Finset.range (n-m),term (m+i)‖ :=by
              rw [hsplit]
              ring_nf
      _ ≤ B* (1/ (m+1:ℝ) ^ s) :=by
            simpa [B,term,add_assoc,add_comm,add_left_comm] using
              z6 (x:=x) hx₀ hx₁ hs' m (n-m)
      _ ≤ B* (1/ (m+1:ℝ)) :=by
            have hm1:1 ≤ (m+1:ℝ) :=by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            have hpow: (m+1:ℝ) ^ (1:ℝ) ≤ (m+1:ℝ) ^ s:=by
              simpa using Real.rpow_le_rpow_of_exponent_le hm1 hs'
            have hpow_inv:1/ (m+1:ℝ) ^ s ≤ 1/ (m+1:ℝ) :=by
              simpa [Real.rpow_one] using
                (one_div_le_one_div_of_le (show 0 < (m+1:ℝ) ^ (1:ℝ) by positivity) hpow)
            exact mul_le_mul_of_nonneg_left hpow_inv hB_pos.le
      _ ≤ B* (1/ (N+1:ℝ)) :=by
            have hm_inv:1/ (m+1:ℝ) ≤ 1/ (N+1:ℝ) :=
              one_div_le_one_div_of_le (show 0 < (N+1:ℝ) by positivity)
                (by exact_mod_cast Nat.succ_le_succ hm)
            exact mul_le_mul_of_nonneg_left hm_inv hB_pos.le
      _ < B* (ε/B) :=
            mul_lt_mul_of_pos_left hN hB_pos
      _=ε:=by
            field_simp [hB_pos.ne']
  intro m hm n hn s hs
  rcases le_total m n with hmn | hnm
  · exact htail_bound hm hmn s hs
  · simpa [dist_comm] using htail_bound hn hnm s hs
theorem ys {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    HurwitzZeta.sinZeta x 1= (Real.pi* (1/2-x) : ℂ) :=by
  let boundary:ℂ:= (Real.pi* (1/2-x) : ℂ)
  let S :ℕ → ℝ → ℂ:=fun n s=>
    ∑ i ∈ Finset.range n,
      Real.sin (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ))
  let G :ℝ → ℂ:=fun s => if hs:s=1 then boundary else HurwitzZeta.sinZeta x s
  have hCauchy:UniformCauchySeqOn S atTop (Set.Ici 1) :=by
    simpa [S] using wX (x:=x) hx₀ hx₁
  have hpoint: ∀ s ∈ Set.Ici (1:ℝ),Tendsto (fun n => S n s) atTop (𝓝 (G s)) :=by
    intro s hs
    by_cases hs1:s=1
    · simpa [S,G,hs1,boundary] using zj (x:=x) hx₀ hx₁
    · have hslt:1 < s:=lt_of_le_of_ne hs (by simpa [eq_comm] using hs1)
      simpa [S,G,hs1] using (yF (x:=x) s hslt).tendsto_sum_nat
  have hunif:TendstoUniformlyOn S G atTop (Set.Ici 1) :=
    hCauchy.tendstoUniformlyOn_of_tendsto hpoint
  have hcont:ContinuousOn G (Set.Ici (1:ℝ)) :=by
    apply hunif.continuousOn
    refine Frequently.of_forall fun n => ?_
    classical
    dsimp [S]
    exact Continuous.continuousOn <|
      continuous_finsetSum _ fun i _=> yi x i
  have hG_right:Tendsto G (𝓝[Set.Ioi 1] 1) (𝓝 boundary) :=by
    have hG_Ici:Tendsto G (𝓝[Set.Ici 1] 1) (𝓝 boundary) :=by
      simpa [G,boundary] using (hcont 1 (by simp)).tendsto
    exact hG_Ici.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hG_eq:G=ᶠ[𝓝[Set.Ioi 1] 1] fun s :ℝ=> HurwitzZeta.sinZeta x s:=by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hslt:1 < s:=by simpa using hs
    simp [G,ne_of_gt hslt]
  have hsin_right:Tendsto (fun s :ℝ=> HurwitzZeta.sinZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 boundary) :=
    Tendsto.congr' hG_eq hG_right
  have hsin_cont:Tendsto (fun s :ℝ=> HurwitzZeta.sinZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 (HurwitzZeta.sinZeta x 1)) :=by
    have hcomplex:Tendsto (fun z :ℂ=> HurwitzZeta.sinZeta x z) (𝓝 (1:ℂ))
        (𝓝 (HurwitzZeta.sinZeta x 1)) :=
      ((HurwitzZeta.differentiableAt_sinZeta x) (1:ℂ)).continuousAt.tendsto
    have hreal:Tendsto (fun s :ℝ=> (s:ℂ)) (𝓝 (1:ℝ)) (𝓝 (1:ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have hcomp:Tendsto (fun s :ℝ=> HurwitzZeta.sinZeta x (s:ℂ)) (𝓝 (1:ℝ))
        (𝓝 (HurwitzZeta.sinZeta x 1)) :=by
      simpa [Function.comp] using! hcomplex.comp hreal
    exact hcomp.mono_left nhdsWithin_le_nhds
  simpa [boundary] using (tendsto_nhds_unique hsin_right hsin_cont).symm
theorem xP {a:ZMod p} (ha:a ≠ 0) :
    HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =
      (((Real.pi:ℝ) : ℂ) * ((1/2:ℂ) - (a.val:ℂ) / (p:ℂ))) :=by
  rw [xy]
  have hx: (a.val/p:ℝ) ∈ Set.Ioo 0 1:=sP (p:=p) ha
  calc
    HurwitzZeta.sinZeta (a.val/p:ℝ) 1 =
        (Real.pi* (1/2- (a.val/p:ℝ)) : ℂ) :=
          ys (x:= (a.val/p:ℝ)) hx.1 hx.2
    _= (((Real.pi:ℝ) : ℂ) * ((1/2:ℂ) - (a.val:ℂ) / (p:ℂ))) :=by
          have hcast: (((a.val/p:ℝ) : ℂ)) = (a.val:ℂ) / (p:ℂ) :=by
            push_cast
            rfl
          simpa using congrArg
            (fun z :ℂ=> (((Real.pi:ℝ) : ℂ) * ((1/2:ℂ) - z))) hcast
end LValueAtOne
end KummerCriterion
end
end Module18
-- Source: KummerCriterion.LValueAtOne.Odd
section Module19
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p:ℕ) [hp:Fact p.Prime]
noncomputable def u9 (χ:DirichletCharacter ℂ p) : ℂ:=
  ((((Real.pi:ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ)) *
    qf χ⁻¹ 1
noncomputable def u4 (χ:DirichletCharacter ℂ p) : ℂ:=
  ∑ a :ZMod p,χ⁻¹ a * ((Real.log ‖(1:ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ)
noncomputable def ra (χ:DirichletCharacter ℂ p) : ℂ:=
  -(gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)))⁻¹*u4 p χ
theorem v8
    {χ:DirichletCharacter ℂ p} (hχ_prim:χ.IsPrimitive) (hχ_odd:χ.Odd)
    (hχ0:DirichletCharacter.LFunction χ⁻¹ 0 = -qf χ⁻¹ 1) :
    DirichletCharacter.LFunction χ 1=u9 p χ:=by
  have hp_ne_one:p ≠ 1:=hp.out.ne_one
  have hp_ne_zero: (p:ℂ) ≠ 0:=by
    exact_mod_cast hp.out.ne_zero
  have hχinv_odd: (χ⁻¹).Odd:=by
    rw [DirichletCharacter.Odd] at hχ_odd ⊢
    rw [MulChar.inv_apply_eq_inv',hχ_odd]
    norm_num
  have hL1:DirichletCharacter.LFunction χ 1=
      ((Real.pi:ℝ) : ℂ) * DirichletCharacter.completedLFunction χ 1:=by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ:=χ) (s:=1)
        (Or.inl one_ne_zero),hχ_odd.gammaFactor_def]
    simp [Complex.Gammaℝ_def,Complex.Gamma_one,Complex.cpow_neg_one,mul_comm]
  have hL0:DirichletCharacter.completedLFunction χ⁻¹ 0 =
      DirichletCharacter.LFunction χ⁻¹ 0 :=by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor (χ:=χ⁻¹) (s:=0)
        (Or.inr hp_ne_one),hχinv_odd.gammaFactor_def]
    simp
  have hfe:=
    DirichletCharacter.IsPrimitive.completedLFunction_one_sub (χ:=χ) hχ_prim (0:ℂ)
  rw [DirichletCharacter.rootNumber,if_neg hχ_odd.not_even,pow_one,
    ← mul_comm_div,← mul_comm_div,← Complex.cpow_sub _ _ hp_ne_zero,sub_sub,add_halves,
    hL0,hχ0] at hfe
  have hfe':DirichletCharacter.completedLFunction χ 1=
      (p:ℂ) ^ (-1:ℂ) * Complex.I*gaussSum χ (ZMod.stdAddChar (N:=p)) *
        qf χ⁻¹ 1 :=by
    simpa using hfe
  calc
    DirichletCharacter.LFunction χ 1
        = ((Real.pi:ℝ) : ℂ) * DirichletCharacter.completedLFunction χ 1:=hL1
    _= ((Real.pi:ℝ) : ℂ) *
          (((p:ℂ) ^ (-1:ℂ)) * Complex.I*gaussSum χ (ZMod.stdAddChar (N:=p)) *
            qf χ⁻¹ 1) :=by rw [hfe']
    _= ((((Real.pi:ℝ) : ℂ) * Complex.I) * gaussSum χ (ZMod.stdAddChar (N:=p)) /
            (p:ℂ)) * qf χ⁻¹ 1 :=by
      simp [Complex.cpow_neg_one,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
    _=u9 p χ:=rfl
end LValueAtOne
end KummerCriterion
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p:ℕ) [hp:Fact p.Prime]
theorem vW
    {χ:DirichletCharacter ℂ p} (hχ_odd:χ.Odd) :
    DirichletCharacter.LFunction χ 0=
      (((Real.pi:ℝ) : ℂ)⁻¹) *
        ∑ a :ZMod p,χ a*HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 :=by
  have hs: ∀ n:ℕ,(1:ℂ) ≠ -n:=by
    intro n h
    have hre: (1:ℝ) = -(n:ℝ) :=by
      simpa using congrArg Complex.re h
    nlinarith
  have hχ_odd_fun:Function.Odd (fun a :ZMod p => χ a) :=
    fun a => DirichletCharacter.Odd.eval_neg (ψ:=χ) a hχ_odd
  rw [DirichletCharacter.LFunction,ZMod.LFunction_def_odd hχ_odd_fun]
  simp only [neg_zero,Complex.cpow_zero,one_mul]
  calc
    ∑ a :ZMod p,χ a*HurwitzZeta.hurwitzZetaOdd (ZMod.toAddCircle a) 0
        = ∑ a:ZMod p,
            χ a *
              ((((Real.pi:ℝ) : ℂ)⁻¹) * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) :=by
              refine Finset.sum_congr rfl fun a _=> ?_
              have hvalue:=HurwitzZeta.hurwitzZetaOdd_one_sub
                (s:= (1:ℂ)) (a:=ZMod.toAddCircle a) hs
              have hsin:Complex.sin (((Real.pi:ℝ) : ℂ) * (2⁻¹:ℂ)) = 1:=by
                simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
                  using Complex.sin_pi_div_two
              simpa [Complex.Gamma_one,Complex.cpow_neg_one,hsin,mul_assoc,mul_left_comm,
                mul_comm,div_eq_mul_inv] using congrArg (fun z :ℂ=> χ a*z) hvalue
    _= ∑ a:ZMod p,
          (((Real.pi:ℝ) : ℂ)⁻¹) * (χ a *HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) :=by
            refine Finset.sum_congr rfl fun a _=> by ring
    _= (((Real.pi:ℝ) : ℂ)⁻¹) *
          ∑ a :ZMod p,χ a*HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 :=by
            rw [Finset.mul_sum]
theorem uc
    {χ:DirichletCharacter ℂ p} (hχ_odd:χ.Odd) (hχ_ne_one:χ ≠ 1)
    (hsin: ∀ a:ZMod p,a ≠ 0 →
      HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =
        (((Real.pi:ℝ) : ℂ) * ((1/2:ℂ) - (a.val:ℂ) / (p:ℂ)))) :
    DirichletCharacter.LFunction χ 0= -qf χ 1:=by
  have hp_ne_one:p ≠ 1:=hp.out.ne_one
  have hp_ne_zero: (p:ℂ) ≠ 0:=by
    exact_mod_cast hp.out.ne_zero
  have hχ_zero:χ 0=0:=χ.map_zero' hp_ne_one
  have hsum_zero: ∑ a:ZMod p,χ a=0:=MulChar.sum_eq_zero_of_ne_one hχ_ne_one
  have hpi: (((Real.pi:ℝ) : ℂ)⁻¹) * (((Real.pi:ℝ) : ℂ)) = 1:=by
    field_simp [Real.pi_ne_zero]
  calc
    DirichletCharacter.LFunction χ 0
        = (((Real.pi:ℝ) : ℂ)⁻¹) *
            ∑ a :ZMod p,χ a*HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 :=
          vW (p:=p) hχ_odd
    _= (((Real.pi:ℝ) : ℂ)⁻¹) *
          ∑ a :ZMod p,
            χ a *
              ((((Real.pi:ℝ) : ℂ) * ((1/2:ℂ) - (a.val:ℂ) / (p:ℂ)))) :=by
            refine congrArg (fun z :ℂ=> (((Real.pi:ℝ) : ℂ)⁻¹) * z) ?_
            refine Finset.sum_congr rfl fun a _=> ?_
            rcases eq_or_ne a 0 with rfl | ha
            · simp [hχ_zero]
            · rw [hsin a ha]
    _= ∑ a:ZMod p,χ a* ((1/2:ℂ) - (a.val:ℂ) / (p:ℂ)) :=by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _=> ?_
          calc
            (((Real.pi:ℝ) : ℂ)⁻¹) *
                (χ a * (((Real.pi:ℝ) : ℂ) * ((1/2:ℂ) - (a.val:ℂ) / (p:ℂ))))
                = ((((Real.pi:ℝ) : ℂ)⁻¹) * (((Real.pi:ℝ) : ℂ))) *
                    (χ a * ((1/2:ℂ) - (a.val:ℂ) / (p:ℂ))) :=by
                      ring
            _=χ a* ((1/2:ℂ) - (a.val:ℂ) / (p:ℂ)) :=by
                  rw [hpi,one_mul]
    _= -∑ a :ZMod p,χ a* ((a.val:ℂ) / (p:ℂ)) :=by
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib]
          have hconst: ∑ a:ZMod p,χ a* (1/2:ℂ) = 0:=by
            calc
              ∑ a :ZMod p,χ a* (1/2:ℂ) = (1/2:ℂ) * ∑ a :ZMod p,χ a:=by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _=> by rw [mul_comm]
              _=0:=by rw [hsum_zero,mul_zero]
          rw [hconst,zero_sub]
    _= -qf χ 1:=by
          congr 1
          rw [vU (R:=ℂ) (N:=p) (χ:=χ) hχ_ne_one]
          refine Finset.sum_congr rfl fun a _=> ?_
          congr 1
          change (a.val:ℂ) / (p:ℂ) = ((((a.val:ℚ) / p:ℚ)) : ℂ)
          rw [Rat.cast_div]
          push_cast
          rfl
theorem wK
    {χ:DirichletCharacter ℂ p} (hχ_odd:χ.Odd) (hχ_ne_one:χ ≠ 1) :
    DirichletCharacter.LFunction χ 0= -qf χ 1:=
  uc (p:=p)
    hχ_odd hχ_ne_one
    (fun _ ha=> xP (p:=p) ha)
theorem zn
    {χ:DirichletCharacter ℂ p} (hχ_prim:χ.IsPrimitive) (hχ_odd:χ.Odd)
    (hχ_ne_one:χ ≠ 1) :
    DirichletCharacter.LFunction χ 1=u9 p χ:=by
  have hχinv_odd: (χ⁻¹).Odd:=by
    rw [DirichletCharacter.Odd] at hχ_odd ⊢
    rw [MulChar.inv_apply_eq_inv',hχ_odd]
    norm_num
  have hχinv_ne_one:χ⁻¹ ≠ 1:=by
    intro h
    apply hχ_ne_one
    calc χ =χ⁻¹⁻¹:= (inv_inv χ).symm
      _= (1:DirichletCharacter ℂ p)⁻¹:=by rw [h]
      _=1:=inv_one
  exact v8 (p:=p) hχ_prim hχ_odd
    (wK (p:=p) hχinv_odd hχinv_ne_one)
end LValueAtOne
end KummerCriterion
end
end
end Module19
-- Source: KummerCriterion.GaussSum.SignInvariant.Vandermonde
section Module20
noncomputable section
namespace KummerCriterion
open scoped BigOperators ComplexConjugate
section SignInvariant
variable (p:ℕ) [hp:Fact p.Prime]
noncomputable def q2:ℂ:=
  ZMod.stdAddChar (N:=p) (-(1:ZMod p))
noncomputable def ry:Fin p → ℂ :=
  fun i => ZMod.stdAddChar (N:=p) (-((st (p:=p)).symm i))
noncomputable def uq:Matrix (Fin p) (Fin p) ℂ :=
  Matrix.vandermonde (ry (p:=p))
noncomputable def qP:ℂ:=
  ∏ i :Fin p,∏ j ∈ Finset.Ioi i,
    (ry (p:=p) j -ry (p:=p) i)
noncomputable def qy:ℂ:=
  ∏ i :Fin p,∏ j ∈ Finset.Ioi i,
    ((q2 (p:=p)) ^ ((j:ℕ) - (i:ℕ)) - 1)
noncomputable def qp:ℂ:=
  ∏ d ∈ Finset.range (p-1),
    ((q2 (p:=p)) ^ (d+1) - 1) ^ (p-1-d)
theorem yH (i j :Fin p) :
    u3 p i j =
      ZMod.stdAddChar (N:=p) (-((i:ZMod p) * (j:ZMod p))) :=by
  rw [u3,Matrix.reindex_apply]
  simp [wH,uk]
theorem xo:
    u3 p =uq p :=by
  ext i j
  rw [yH (p:=p),uq,Matrix.vandermonde_apply]
  simp only [ry,uk]
  calc
    ZMod.stdAddChar (N:=p) (-((i:ZMod p) * (j:ZMod p))) =
        ZMod.stdAddChar (N:=p) ((j:ℕ) • (-(i:ZMod p))) :=by
          congr
          rw [nsmul_eq_mul]
          ring
    _=ZMod.stdAddChar (N:=p) (-(i:ZMod p)) ^ (j:ℕ) :=
          AddChar.map_nsmul_eq_pow _ _ _
theorem se (i:Fin p) :
    ry (p:=p) i =q2 (p:=p) ^ (i:ℕ) :=by
  rw [ry,q2]
  simp only [uk]
  calc
    ZMod.stdAddChar (N:=p) (-(i:ZMod p)) =
        ZMod.stdAddChar (N:=p) ((i:ℕ) • (-(1:ZMod p))) :=by
          congr
          rw [nsmul_eq_mul]
          ring
    _=ZMod.stdAddChar (N:=p) (-(1:ZMod p)) ^ (i:ℕ) :=
          AddChar.map_nsmul_eq_pow _ _ _
theorem wt:
    qP p =
      ∏ i :Fin p,∏ j ∈ Finset.Ioi i,
        ((q2 (p:=p)) ^ (j:ℕ) - (q2 (p:=p)) ^ (i:ℕ)) :=by
  unfold qP
  refine Finset.prod_congr rfl ?_
  intro i _
  refine Finset.prod_congr rfl ?_
  intro j _
  rw [se (p:=p),
    se (p:=p)]
theorem zP (i j :Fin p) (hij:i < j) :
    (q2 (p:=p)) ^ (j:ℕ) - (q2 (p:=p)) ^ (i:ℕ) =
      (q2 (p:=p)) ^ (i:ℕ) *
        ((q2 (p:=p)) ^ ((j:ℕ) - (i:ℕ)) - 1) :=by
  set ζ :ℂ:=q2 (p:=p)
  have hij': (i:ℕ) ≤ (j:ℕ) :=
    Nat.le_of_lt (show (i:ℕ) < (j:ℕ) by simpa using hij)
  have hnat: (j:ℕ) = (i:ℕ) + ((j:ℕ) - (i:ℕ)) :=
    (Nat.add_sub_of_le hij').symm
  calc
    ζ^ (j:ℕ) - ζ^ (i:ℕ) =
        ζ^ ((i:ℕ) + ((j:ℕ) - (i:ℕ))) - ζ^ (i:ℕ) :=by
      conv_lhs=> rw [hnat]
    _=ζ^ (i:ℕ) * ζ^ ((j:ℕ) - (i:ℕ)) - ζ^ (i:ℕ) :=by
      rw [pow_add]
    _=ζ^ (i:ℕ) * (ζ^ ((j:ℕ) - (i:ℕ)) - 1) :=by
      ring
theorem sr:
    (∏ i :Fin p,∏ j ∈ Finset.Ioi i,
      ((q2 (p:=p)) ^ (j:ℕ) - (q2 (p:=p)) ^ (i:ℕ))) =
      (∏ i :Fin p,((q2 (p:=p)) ^ (i:ℕ)) ^ (Finset.Ioi i).card) *
        qy p :=by
  unfold qy
  have hsplit:
      (∏ i :Fin p,∏ j ∈ Finset.Ioi i,
          ((q2 (p:=p)) ^ (j:ℕ) - (q2 (p:=p)) ^ (i:ℕ))) =
        ∏ i :Fin p,
          (((q2 (p:=p)) ^ (i:ℕ)) ^ (Finset.Ioi i).card*
            ∏ j ∈ Finset.Ioi i,
              ((q2 (p:=p)) ^ ((j:ℕ) - (i:ℕ)) - 1)) :=by
    refine Finset.prod_congr rfl ?_
    intro i _
    calc
      (∏ j ∈ Finset.Ioi i,
          ((q2 (p:=p)) ^ (j:ℕ) -
            (q2 (p:=p)) ^ (i:ℕ))) =
          ∏ j ∈ Finset.Ioi i,
            ((q2 (p:=p)) ^ (i:ℕ) *
              ((q2 (p:=p)) ^ ((j:ℕ) - (i:ℕ)) - 1)) :=by
              refine Finset.prod_congr rfl ?_
              intro j hj
              exact zP (p:=p) i j (by simpa using hj)
      _= (∏ _j ∈ Finset.Ioi i,(q2 (p:=p)) ^ (i:ℕ)) *
          ∏ j ∈ Finset.Ioi i,
            ((q2 (p:=p)) ^ ((j:ℕ) - (i:ℕ)) - 1) :=by
              rw [Finset.prod_mul_distrib]
      _= (((q2 (p:=p)) ^ (i:ℕ)) ^ (Finset.Ioi i).card) *
          ∏ j ∈ Finset.Ioi i,
            ((q2 (p:=p)) ^ ((j:ℕ) - (i:ℕ)) - 1) :=by
              simp
  rw [hsplit,Finset.prod_mul_distrib]
theorem vA:
    qP p =
      (∏ i :Fin p,(q2 (p:=p)) ^ ((i:ℕ) * (p-1- (i:ℕ)))) *
        qy p :=by
  calc
    qP p =
        (∏ i :Fin p,((q2 (p:=p)) ^ (i:ℕ)) ^ (Finset.Ioi i).card) *
          qy p :=by
            rw [wt (p:=p),
              sr
                (p:=p)]
    _= (∏ i :Fin p,(q2 (p:=p)) ^ ((i:ℕ) * (p-1- (i:ℕ)))) *
          qy p :=by
            congr 1
            refine Finset.prod_congr rfl ?_
            intro i _
            rw [show (Finset.Ioi i).card=p-1- (i:ℕ) by simp,
              ← pow_mul]
omit hp in
theorem sa (n:ℕ) :
    ∑ i ∈ Finset.range n,i* (n-1-i) = n.choose 3 :=by
  induction n with
  | zero=>
      simp
  | succ n ih=>
      rw [Finset.sum_range_succ]
      simp only [Nat.succ_sub_one,tsub_self,mul_zero,add_zero]
      calc
        ∑ i ∈ Finset.range n,i* (n-i) =
            ∑ i ∈ Finset.range n,(i* (n-1-i) + i) :=by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hi':i < n:=Finset.mem_range.mp hi
              have hsub:n-i= (n-1-i) + 1:=by
                omega
              rw [hsub,mul_add,mul_one]
        _= (∑ i ∈ Finset.range n,i* (n-1-i)) + ∑ i ∈ Finset.range n,i:=by
              rw [Finset.sum_add_distrib]
        _=n.choose 3 +n.choose 2 :=by
              rw [ih,Finset.sum_range_id,Nat.choose_two_right]
        _= (n+1).choose 3 :=by
              rw [Nat.choose_succ_succ' n 2,add_comm]
theorem v5:
    (∏ i :Fin p,(q2 (p:=p)) ^ ((i:ℕ) * (p-1- (i:ℕ)))) =
      (q2 (p:=p)) ^ (p.choose 3) :=by
  have hprod:
      (∏ i :Fin p,(q2 (p:=p)) ^ ((i:ℕ) * (p-1- (i:ℕ)))) =
        ∏ i ∈ Finset.range p,(q2 (p:=p)) ^ (i* (p-1-i)) :=by
          simpa using
            (Fin.prod_univ_eq_prod_range
              (f:=fun i => (q2 (p:=p)) ^ (i* (p-1-i))) (n:=p))
  rw [hprod,Finset.prod_pow_eq_pow_sum,sa]
theorem vk:
    qP p =
      (q2 (p:=p)) ^ (p.choose 3) * qy p :=by
  rw [vA (p:=p),
    v5 (p:=p)]
theorem wl (n:ℕ) (ζ:ℂ) :
    (∏ d ∈ Finset.range n,(ζ^ (d+1) - 1)) *
        (∏ d ∈ Finset.range n,(ζ^ (d+1) - 1) ^ (n-d)) =
      ∏ d ∈ Finset.range n,(ζ^ (d+1) - 1) ^ (n+1-d) :=by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro d hd
  have hd':d < n:=Finset.mem_range.mp hd
  have hshift:n+1-d= (n-d) + 1:=by
    omega
  simpa [hshift] using (pow_succ' (ζ^ (d+1) - 1) (n-d)).symm
theorem uU (n:ℕ) (ζ:ℂ) :
    (∏ i :Fin (n+1),∏ j ∈ Finset.Ioi i,(ζ^ ((j:ℕ) - (i:ℕ)) - 1)) =
      ∏ d ∈ Finset.range n,(ζ^ (d+1) - 1) ^ (n-d) :=by
  induction n with
  | zero=>
      simp
  | succ n ih=>
      rw [Fin.prod_univ_succ,Fin.prod_Ioi_zero]
      have hsucc:
          (∏ i :Fin (n+1),
              ∏ j ∈ Finset.Ioi i.succ,(ζ^ ((j:ℕ) - (i.succ:ℕ)) - 1)) =
            ∏ i :Fin (n+1),
              ∏ j ∈ Finset.Ioi i,(ζ^ ((j:ℕ) - (i:ℕ)) - 1) :=by
        refine Finset.prod_congr rfl ?_
        intro i hi
        rw [Fin.prod_Ioi_succ]
        refine Finset.prod_congr rfl ?_
        intro j hj
        simp [Fin.val_succ]
      rw [hsucc]
      have hfirst:
          (∏ j :Fin (n+1),(ζ^ ((j:ℕ) + 1) - 1)) =
            ∏ d ∈ Finset.range (n+1),(ζ^ (d+1) - 1) :=by
        simpa using
          (Fin.prod_univ_eq_prod_range (f:=fun d => (ζ^ (d+1) - 1)) (n:=n+1))
      have hfirst':
          (∏ j :Fin (n+1),
              (ζ^ (((j.succ:Fin (n+2)) : ℕ) - ((0:Fin (n+2)) : ℕ)) -
                1)) =
            ∏ d ∈ Finset.range (n+1),(ζ^ (d+1) - 1) :=by
        simpa [Fin.val_succ] using hfirst
      rw [ih,hfirst',Finset.prod_range_succ]
      let a :ℕ → ℂ:=fun d => ζ ^ (d+1) - 1
      calc
        ((∏ d ∈ Finset.range n,a d) * a n) * (∏ d ∈ Finset.range n,a d^ (n-d)) =
            ((∏ d ∈ Finset.range n,a d) *
              (∏ d ∈ Finset.range n,a d^ (n-d))) * a n :=by
              ac_rfl
        _= (∏ d ∈ Finset.range n,a d^ (n+1-d)) * a n :=by
              rw [wl (n:=n) (ζ:=ζ)]
        _= (∏ d ∈ Finset.range n,a d^ (n+1-d)) * a n ^ ((n+1) - n) :=by
              simp
        _= ∏ d ∈ Finset.range (n+1),a d^ (n+1-d) :=by
              rw [Finset.prod_range_succ]
theorem ux:
    qy p =qp p :=by
  have hbase:
      (∏ i :Fin ((p-1) + 1),∏ j ∈ Finset.Ioi i,
          (q2 (p:=p) ^ ((j:ℕ) - (i:ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p-1),
          (q2 (p:=p) ^ (d+1) - 1) ^ (p-1-d) :=
    uU
      (n:=p-1) (ζ:=q2 (p:=p))
  have hp_pred: (p-1) + 1=p:=Nat.succ_pred_eq_of_pos hp.out.pos
  have hcast:
      (∏ i :Fin p,∏ j ∈ Finset.Ioi i,
          (q2 (p:=p) ^ ((j:ℕ) - (i:ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p-1),
          (q2 (p:=p) ^ (d+1) - 1) ^ (p-1-d) :=by
    let P :ℕ → Prop:=fun m =>
      (∏ i :Fin m,∏ j ∈ Finset.Ioi i,
          (q2 (p:=p) ^ ((j:ℕ) - (i:ℕ)) - 1)) =
        ∏ d ∈ Finset.range (p-1),
          (q2 (p:=p) ^ (d+1) - 1) ^ (p-1-d)
    have hP:P ((p-1) + 1) :=by
      simpa [P] using hbase
    change P p
    exact hp_pred ▸ hP
  simpa [qy,qp] using hcast
theorem vB:
    Matrix.det (uq p) = qP p :=by
  simp [uq,qP,Matrix.det_vandermonde]
theorem u0:
    Matrix.det (rZ p) =
      ((Real.sqrt p :ℂ)⁻¹) ^ p*qP p :=by
  rw [vy (p:=p),Matrix.det_smul,
    xo (p:=p),
    vB]
  simp
theorem v0:
    LinearMap.det (qn p) =
      ((Real.sqrt p :ℂ)⁻¹) ^ p*qP p :=by
  rw [vY (p:=p),
    uy (p:=p)]
  exact u0 (p:=p)
theorem wb:
    LinearMap.det (qn p) =
      ((Real.sqrt p :ℂ)⁻¹) ^ p*
        ((q2 (p:=p)) ^ (p.choose 3) * qy p) :=by
  rw [v0 (p:=p),
    vk (p:=p)]
theorem vw:
    LinearMap.det (qn p) =
      ((Real.sqrt p :ℂ)⁻¹) ^ p*
        ((q2 (p:=p)) ^ (p.choose 3) *
          qp p) :=by
  rw [wb (p:=p),
    ux (p:=p)]
end SignInvariant
end KummerCriterion
end
end Module20
-- Source: KummerCriterion.GaussSum.SignInvariant.VandermondeScalar
section Module21
noncomputable section
namespace KummerCriterion
open scoped BigOperators ComplexConjugate
section SignInvariant
variable (p:ℕ) [hp:Fact p.Prime]
theorem zd:
    q2 (p:=p) = Complex.exp (2*Real.pi*Complex.I* ((-1:ℤ) / p)) :=by
  rw [q2]
  calc
    ZMod.stdAddChar (N:=p) (-(1:ZMod p)) = Complex.exp (-(2*Real.pi*Complex.I) / p) :=by
      simpa using (ZMod.stdAddChar_coe (N:=p) (-1))
    _=Complex.exp (2*Real.pi*Complex.I* ((-1:ℤ) / p)) :=by
          congr 1
          have hp0: (p:ℂ) ≠ 0:=by
            exact_mod_cast hp.out.ne_zero
          push_cast
          field_simp [hp0]
theorem rn:
    IsPrimitiveRoot (q2 (p:=p)) p :=by
  have hcop:IsCoprime (-1:ℤ) p :=by
    refine ⟨-1,0,by simp⟩
  rw [zd (p:=p)]
  exact Complex.isPrimitiveRoot_exp_of_isCoprime (-1) p hp.out.ne_zero hcop
theorem uT (r:ℕ) :
    q2 (p:=p) ^ r=
      Complex.exp ((-(2*Real.pi* (r:ℝ) / p)) * Complex.I) :=by
  rw [q2]
  calc
    ZMod.stdAddChar (N:=p) (-(1:ZMod p)) ^ r=
        ZMod.stdAddChar (N:=p) ((r:ℕ) • (-(1:ZMod p))) :=by
          symm
          exact AddChar.map_nsmul_eq_pow _ _ _
    _=ZMod.stdAddChar (N:=p) (-(r:ZMod p)) :=by
          congr
          rw [nsmul_eq_mul]
          ring
    _=Complex.exp (-(2*Real.pi*Complex.I*r) / p) :=by
          simpa using (ZMod.stdAddChar_coe (N:=p) (j:= -(r:ℤ)))
    _=Complex.exp ((-(2*Real.pi* (r:ℝ) / p)) * Complex.I) :=by
          congr 1
          have hp0: (p:ℂ) ≠ 0:=by
            exact_mod_cast hp.out.ne_zero
          push_cast
          field_simp [hp0]
theorem yS {k:ℕ} (hk:k ≤ p) :
    2*Real.sin (Real.pi* ((p-k:ℕ) / p:ℝ)) =
      2*Real.sin (Real.pi* (k:ℝ) / p) :=by
  have hp0: (p:ℝ) ≠ 0:=by
    exact_mod_cast hp.out.ne_zero
  rw [show Real.pi* ((p-k:ℕ) / p:ℝ) = Real.pi-Real.pi* (k:ℝ) / p by
      rw [Nat.cast_sub hk]
      field_simp [hp0]]
  rw [Real.sin_pi_sub]
theorem doubleSin_pos {k:ℕ} (hk0:0 < k) (hkp:k < p) :
    0 < 2*Real.sin (Real.pi* (k:ℝ) / p) :=by
  have hp0: (0:ℝ) < p:=by
    exact_mod_cast hp.out.pos
  have hkp': (k:ℝ) < p:=by
    exact_mod_cast hkp
  have hang:Real.pi* (k:ℝ) / p ∈ Set.Ioo 0 Real.pi:=by
    constructor
    · exact div_pos (by positivity) hp0
    · have hfrac: (k:ℝ) / p < 1:=
        (div_lt_one hp0).2 hkp'
      have hmul:Real.pi* ((k:ℝ) / p) < Real.pi:=by
        simpa [one_mul] using (mul_lt_mul_of_pos_left hfrac Real.pi_pos)
      simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hmul
  have hsin:0 < Real.sin (Real.pi* (k:ℝ) / p) :=
    Real.sin_pos_of_mem_Ioo hang
  positivity
theorem s7 {k:ℕ} (hkp:k ≤ p) :
    q2 (p:=p) ^ k=
      Complex.exp ((2*Real.pi* ((p-k:ℕ) : ℝ) / p) * Complex.I) :=by
  have hperiod:Complex.exp (((-2:ℝ) * Real.pi) * Complex.I) = 1:=by
    rw [Complex.exp_mul_I]
    simp
  calc
    q2 (p:=p) ^ k=
        Complex.exp ((-(2*Real.pi* (k:ℝ) / p)) * Complex.I) :=
          uT (p:=p) k
    _=Complex.exp
          (((2*Real.pi* ((p-k:ℕ) : ℝ) / p) * Complex.I) +
            (((-2:ℝ) * Real.pi) * Complex.I)) :=by
          congr 1
          have hp0: (p:ℂ) ≠ 0:=by
            exact_mod_cast hp.out.ne_zero
          have hcalc:
              -(((2:ℂ) * k) / p) = ((2:ℂ) * (p-k:ℕ)) / p-2:=by
            rw [Nat.cast_sub hkp]
            field_simp [hp0]
            ring
          simpa [sub_eq_add_neg,div_eq_mul_inv,mul_assoc,mul_left_comm,
            mul_comm,mul_add,add_mul] using
            congrArg (fun x :ℂ=> (Real.pi:ℂ) * x*Complex.I) hcalc
    _=Complex.exp ((2*Real.pi* ((p-k:ℕ) : ℝ) / p) * Complex.I) :=by
          rw [Complex.exp_add,hperiod,mul_one]
theorem xB {k:ℕ} (hk0:0 < k) (hkp:k < p) :
    ‖1-q2 (p:=p) ^ k‖ = 2*Real.sin (Real.pi* (k:ℝ) / p) :=by
  have ht0:0 < 2*Real.pi* ((p-k:ℕ) : ℝ) / p:=by
    have hp0: (0:ℝ) < p:=by
      exact_mod_cast hp.out.pos
    have hpk0: (0:ℝ) < (p-k:ℕ) :=by
      exact_mod_cast (Nat.sub_pos_of_lt hkp)
    positivity
  have ht2π:2*Real.pi* ((p-k:ℕ) : ℝ) / p < 2*Real.pi:=by
    have hp0: (0:ℝ) < p:=by
      exact_mod_cast hp.out.pos
    have hpk_lt: ((p-k:ℕ) : ℝ) < p:=by
      exact_mod_cast (Nat.sub_lt hp.out.pos hk0)
    have hfrac: (((p-k:ℕ) : ℝ) / p) < 1:= (div_lt_one hp0).2 hpk_lt
    have hmul: (2*Real.pi) * (((p-k:ℕ) : ℝ) / p) < (2*Real.pi) * 1:=
      mul_lt_mul_of_pos_left hfrac Real.two_pi_pos
    simpa [one_mul,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hmul
  calc
    ‖1-q2 (p:=p) ^ k‖ =
        ‖(1:ℂ) - Complex.exp ((2*Real.pi* ((p-k:ℕ) : ℝ) / p) * Complex.I)‖ :=by
          rw [s7 (p:=p) (k:=k) hkp.le]
    _=2*Real.sin ((2*Real.pi* ((p-k:ℕ) : ℝ) / p) / 2) :=by
          simpa [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
            (rN
              (t:=2*Real.pi* ((p-k:ℕ) : ℝ) / p) ht0 ht2π)
    _=2*Real.sin (Real.pi* (k:ℝ) / p) :=by
          rw [show (2*Real.pi* ((p-k:ℕ) : ℝ) / p) / 2=
            Real.pi* ((p-k:ℕ) / p:ℝ) by ring]
          exact yS (p:=p) hkp.le
theorem u2
    {k:ℕ} (hkp:k ≤ p) :
    (1-q2 (p:=p) ^ k) * (1-q2 (p:=p) ^ (p-k)) =
      (2*Complex.sin (Real.pi* (k:ℝ) / p)) ^ 2:=by
  rcases eq_or_lt_of_le hkp with h_eq | hklt
  · subst k
    have hpow:q2 (p:=p) ^ p=1:=
        (rn (p:=p)).pow_eq_one
    rw [hpow,Nat.sub_self,pow_zero]
    simp
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · have hpow:q2 (p:=p) ^ p=1:=
        (rn (p:=p)).pow_eq_one
    rw [pow_zero,Nat.sub_zero,hpow]
    simp
  have hnorm:
      ‖1-q2 (p:=p) ^ k‖ ^ 2=
        (2*Real.sin (Real.pi* (k:ℝ) / p)) ^ 2:=by
    rw [xB (p:=p) hk0 hklt]
  have hpowComp:q2 (p:=p) ^ (p-k) = conj (q2 (p:=p) ^ k) :=by
    rw [s7 (p:=p) (k:=p-k) (Nat.sub_le _ _)]
    have hsub:p- (p-k) = k:=by omega
    rw [hsub,uT (p:=p) k]
    rw [← Complex.exp_conj]
    have hconjArg:
        (starRingEnd ℂ) (-(2*Real.pi* (k:ℝ) / p) * Complex.I) =
          (2*Real.pi* (k:ℝ) / p) * Complex.I:=by
      apply Complex.ext <;> simp [Complex.conj_ofReal,Complex.conj_I]
    rw [hconjArg]
  have hconjSub:
      1-q2 (p:=p) ^ (p-k) =
        conj (1-q2 (p:=p) ^ k) :=by
    rw [hpowComp]
    rw [map_sub,map_one]
  calc
    (1-q2 (p:=p) ^ k) * (1-q2 (p:=p) ^ (p-k))
        = (1-q2 (p:=p) ^ k) * conj (1-q2 (p:=p) ^ k) :=by
          rw [hconjSub]
    _= ((‖1-q2 (p:=p) ^ k‖ ^ 2:ℝ) : ℂ) :=by
          simpa using Complex.mul_conj' (1-q2 (p:=p) ^ k)
    _= (2*Complex.sin (Real.pi* (k:ℝ) / p)) ^ 2:=by
          simpa [Complex.ofReal_sin] using congrArg (fun x :ℝ=> (x:ℂ)) hnorm
theorem wT:
    ∏ d ∈ Finset.range (p-1),(1-q2 (p:=p) ^ (d+1)) = p:=by
  have hp_eq: (p-1:ℕ) + 1=p:=by
    simpa [Nat.add_comm] using (Nat.succ_pred_eq_of_pos hp.out.pos)
  have hμ:IsPrimitiveRoot (q2 (p:=p)) ((p-1) + 1) :=by
    rw [hp_eq]
    exact rn (p:=p)
  convert
      (IsPrimitiveRoot.prod_one_sub_pow_eq_order
        (n:=p-1) (μ:=q2 (p:=p)) hμ) using 1
  simpa [Nat.cast_add] using congrArg (fun n :ℕ=> (n:ℂ)) hp_eq.symm
theorem ur
    (hp2:p ≠ 2) :
    qp p =
      ∏ d ∈ Finset.range ((p-1) / 2),
        (q2 (p:=p) ^ (d+1) - 1) ^ (p- (d+1)) *
          (q2 (p:=p) ^ (p- (d+1)) - 1) ^ (d+1) :=by
  let n :ℕ:= (p-1) / 2
  have hp_eqn:p=2*n+1:=by
    dsimp [n]
    have htwo:2* ((p-1) / 2) = p-1:=
      Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp2)
    calc
      p= (p-1) + 1:= (Nat.succ_pred_eq_of_pos hp.out.pos).symm
      _=2* ((p-1) / 2) + 1:=by rw [htwo]
  have hp_sub:p-1=n+n:=by
    have:=congrArg (fun m :ℕ=> m -1) hp_eqn
    simpa [two_mul,add_assoc,add_left_comm,add_comm] using this
  unfold qp
  rw [hp_sub,Finset.prod_range_add]
  have hfirst:
      ∏ d ∈ Finset.range n,
          (q2 (p:=p) ^ (d+1) - 1) ^ (n+n-d) =
        ∏ d ∈ Finset.range n,
          (q2 (p:=p) ^ (d+1) - 1) ^ (p- (d+1)) :=by
    refine Finset.prod_congr rfl ?_
    intro d hd
    have hd':d < n:=Finset.mem_range.mp hd
    have hp_add:p=n+n+1:=by
      simpa [two_mul,add_assoc,add_left_comm,add_comm] using hp_eqn
    have hd1:d+1 ≤ n:=Nat.succ_le_of_lt hd'
    have hexp:n+n-d=p- (d+1) :=by
      rw [hp_add]
      omega
    rw [hexp]
  have hreflect:
      (∏ d ∈ Finset.range n,
          (q2 (p:=p) ^ (n+d+1) - 1) ^ (n-d)) =
        ∏ d ∈ Finset.range n,
          (q2 (p:=p) ^ (p- (d+1)) - 1) ^ (d+1) :=by
    rw [← Finset.prod_range_reflect
      (fun d => (q2 (p:=p) ^ (n+d+1) - 1) ^ (n-d)) n]
    refine Finset.prod_congr rfl ?_
    intro d hd
    have hd':d < n:=Finset.mem_range.mp hd
    have hd1:d+1 ≤ n:=Nat.succ_le_of_lt hd'
    have hp_add:p=n+n+1:=by
      simpa [two_mul,add_assoc,add_left_comm,add_comm] using hp_eqn
    have hbase:n+ (n-1-d) + 1=p- (d+1) :=by
      rw [hp_add,Nat.sub_sub]
      omega
    have hpow:n- (n-1-d) = d+1:=by
      rw [Nat.sub_sub]
      omega
    rw [hbase,hpow]
  have hsecond:
      (∏ x ∈ Finset.range n,
          (q2 (p:=p) ^ (n+x+1) - 1) ^ (n+n- (n+x))) =
        ∏ x ∈ Finset.range n,
          (q2 (p:=p) ^ (n+x+1) - 1) ^ (n-x) :=by
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hexp:n+n- (n+x) = n-x:=Nat.add_sub_add_left n n x
    rw [hexp]
  rw [hfirst,hsecond]
  rw [hreflect,← Finset.prod_mul_distrib]
  have hhalf: (n+n) / 2=n:=by
    have htwo:2* ((n+n) / 2) = n+n:=
      Nat.two_mul_div_two_of_even ⟨n,by simp⟩
    omega
  rw [hhalf]
theorem uD
    (hp2:p ≠ 2) :
    2* (∑ d ∈ Finset.range ((p-1) / 2),(d+1) * (p- (d+1))) = (p+1).choose 3 :=by
  let n :ℕ:= (p-1) / 2
  have hp_eqn:p=2*n+1:=by
    dsimp [n]
    have htwo:2* ((p-1) / 2) = p-1:=
      Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp2)
    calc
      p= (p-1) + 1:= (Nat.succ_pred_eq_of_pos hp.out.pos).symm
      _=2* ((p-1) / 2) + 1:=by rw [htwo]
  have hp_add:p=n+n+1:=by simpa [two_mul,add_assoc,add_left_comm,add_comm] using hp_eqn
  have hsplit:
      ∑ i ∈ Finset.range (p+1),i* (p-i) =
        (∑ i ∈ Finset.range (n+1),i* (p-i)) +
          ∑ i ∈ Finset.range (n+1),(n+1+i) * (p- (n+1+i)) :=by
    have hp_split:p+1= (n+1) + (n+1) :=by
      calc
        p+1= (n+n+1) + 1:=by rw [hp_add]
        _= (n+1) + (n+1) :=by ring
    rw [hp_split,Finset.sum_range_add]
  have hreflect:
      ∑ i ∈ Finset.range (n+1),(n+1+i) * (p- (n+1+i)) =
        ∑ i ∈ Finset.range (n+1),i* (p-i) :=by
    rw [← Finset.sum_range_reflect
      (fun i => (n+1+i) * (p- (n+1+i))) (n+1)]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi':i < n+1:=Finset.mem_range.mp hi
    have hi_le:i ≤ n:=Nat.lt_succ_iff.mp hi'
    have hi1:i ≤ n+1:=Nat.le_of_lt hi'
    have hp_add:p=n+n+1:=by
      simpa [two_mul,add_assoc,add_left_comm,add_comm] using hp_eqn
    have hfirst:n+1+ (n+1-1-i) = p-i:=by
      rw [hp_add,Nat.succ_sub_one]
      omega
    have hip:i ≤ p:=
      le_trans (Nat.le_of_lt hi')
        (by rw [hp_add];omega)
    rw [hfirst,Nat.sub_sub_self hip,Nat.mul_comm]
  have hshift:
      ∑ i ∈ Finset.range (n+1),i* (p-i) =
        ∑ d ∈ Finset.range n,(d+1) * (p- (d+1)) :=by
    rw [show n +1=1+n by simp [Nat.add_comm],Finset.sum_range_add]
    simp [add_comm]
  calc
    2* (∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) =
        ∑ i ∈ Finset.range (p+1),i* (p-i) :=by
          rw [← hshift,two_mul,hsplit,hreflect]
    _= (p+1).choose 3 :=by
          simpa using (sa (n:=p+1))
theorem x1 (hp2:p ≠ 2) :
    p ∣ p.choose 3 + ∑ d ∈ Finset.range ((p-1) / 2),(d+1) * (p- (d+1)) :=by
  let n :ℕ:= (p-1) / 2
  have hsum:=uD (p:=p) hp2
  have hchoose3:3*p.choose 3 =p* (p-1).choose 2 :=by
    simpa [Nat.succ_eq_add_one,Nat.sub_add_cancel hp.out.one_le,
      Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      (Nat.add_one_mul_choose_eq (p-1) 2).symm
  have hdvd_choose2:p ∣ p.choose 2 :=by
    rw [Nat.choose_two_right]
    rw [Nat.mul_div_assoc _ (hp.out.even_sub_one hp2).two_dvd]
    exact dvd_mul_right p ((p-1) / 2)
  have hdvd2:
      p ∣ 2* (p.choose 3 + ∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) :=by
    have hsum':2* (∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) = (p+1).choose 3 :=by
      simpa [n] using hsum
    have hsum'':
        (∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) +
          (∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) = (p+1).choose 3 :=by
      simpa [two_mul] using hsum'
    have hEq:
        2* (p.choose 3 + ∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) =
          p* (p-1).choose 2 +p.choose 2 :=by
      calc
        2* (p.choose 3 + ∑ d ∈ Finset.range n,(d+1) * (p- (d+1)))
            = (p.choose 3 + ∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) +
                (p.choose 3 + ∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) :=by
                  rw [two_mul]
        _=p.choose 3 +p.choose 3 +
              ((∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) +
                (∑ d ∈ Finset.range n,(d+1) * (p- (d+1)))) :=by ring
        _=2*p.choose 3 + (p+1).choose 3 :=by rw [hsum'',two_mul]
        _=3*p.choose 3 +p.choose 2 :=by rw [Nat.choose_succ_succ' p 2];ring
        _=p* (p-1).choose 2 +p.choose 2 :=by rw [hchoose3]
    rw [hEq]
    exact dvd_add (dvd_mul_right p ((p-1).choose 2)) hdvd_choose2
  exact (hp.out.odd_of_ne_two hp2).coprime_two_right.dvd_of_dvd_mul_left hdvd2
theorem us
    (hp2:p ≠ 2) :
    q2 (p:=p) ^
        (p.choose 3 + ∑ d ∈ Finset.range ((p-1) / 2),(d+1) * (p- (d+1))) = 1:=by
  obtain ⟨m,hm⟩ :=x1 (p:=p) hp2
  rw [hm,pow_mul,(rn (p:=p)).pow_eq_one]
  simp
theorem xe (hp2:p ≠ 2) :
    ∏ d ∈ Finset.range ((p-1) / 2),
      2*Real.sin (Real.pi* ((d+1:ℕ) / p:ℝ)) = Real.sqrt p :=by
  let n :ℕ:= (p-1) / 2
  let S :ℕ → ℝ:=fun k => 2 *Real.sin (Real.pi* (k:ℝ) / p)
  have hp_eqn:p=2*n+1:=by
    dsimp [n]
    have htwo:2* ((p-1) / 2) = p-1:=
      Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp2)
    calc
      p= (p-1) + 1:= (Nat.succ_pred_eq_of_pos hp.out.pos).symm
      _=2* ((p-1) / 2) + 1:=by rw [htwo]
  have hp_sub:p-1=n+n:=by
    have:=congrArg (fun m :ℕ=> m -1) hp_eqn
    simpa [two_mul,add_assoc,add_left_comm,add_comm] using this
  have hpair:
      ∏ d ∈ Finset.range (p-1),(1-q2 (p:=p) ^ (d+1)) =
        (((∏ d ∈ Finset.range n,S (d+1)) ^ 2:ℝ) : ℂ) :=by
    rw [hp_sub,Finset.prod_range_add]
    have hreflect:
        (∏ d ∈ Finset.range n,(1-q2 (p:=p) ^ (n+d+1))) =
          ∏ d ∈ Finset.range n,(1-q2 (p:=p) ^ (p- (d+1))) :=by
      rw [← Finset.prod_range_reflect (fun d => 1 -q2 (p:=p) ^ (n+d+1)) n]
      refine Finset.prod_congr rfl ?_
      intro d hd
      have hd':d < n:=Finset.mem_range.mp hd
      congr 2
      have hp_add:p=n+n+1:=by
        simpa [two_mul,add_assoc,add_left_comm,add_comm] using hp_eqn
      omega
    rw [hreflect,← Finset.prod_mul_distrib]
    calc
      ∏ d ∈ Finset.range n,
          ((1-q2 (p:=p) ^ (d+1)) *
            (1-q2 (p:=p) ^ (p- (d+1)))) =
          ∏ d ∈ Finset.range n,((((S (d+1) : ℝ) : ℂ)) ^ 2) :=by
            refine Finset.prod_congr rfl ?_
            intro d hd
            have hd':d < n:=Finset.mem_range.mp hd
            have hle:d+1 ≤ p:=by
              have hp_add:p=n+n+1:=by
                simpa [two_mul,add_assoc,add_left_comm,add_comm] using hp_eqn
              omega
            simpa [S,Complex.ofReal_sin] using
              (u2
                (p:=p) (k:=d+1) hle)
      _= (((∏ d ∈ Finset.range n,S (d+1)) ^ 2:ℝ) : ℂ) :=by
            rw [← Finset.prod_pow]
            simp
  have hsqC: (((∏ d ∈ Finset.range n,S (d+1)) ^ 2:ℝ) : ℂ) = (p:ℂ) :=by
    rw [← hpair]
    exact wT (p:=p)
  have hsq: (∏ d ∈ Finset.range n,S (d+1)) ^ 2= (p:ℝ) :=by
    exact_mod_cast hsqC
  have hpos:0 < ∏ d ∈ Finset.range n,S (d+1) :=by
    refine Finset.prod_pos ?_
    intro d hd
    have hd':d < n:=Finset.mem_range.mp hd
    have hdk:d+1 < p:=by
      have hp_add:p=n+n+1:=by
        simpa [two_mul,add_assoc,add_left_comm,add_comm] using hp_eqn
      omega
    exact doubleSin_pos (p:=p) (Nat.succ_pos d) hdk
  have hsq': (∏ d ∈ Finset.range n,S (d+1)) ^ 2= (Real.sqrt p) ^ 2:=by
    rw [Real.sq_sqrt (show 0 ≤ (p:ℝ) by positivity)]
    exact hsq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq' with hEq | hEq
  · simpa [n,S,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hEq
  · exfalso
    have hsqrt_pos:0 < Real.sqrt p :=by
      apply Real.sqrt_pos.2
      exact_mod_cast hp.out.pos
    linarith
theorem xU (hp2:p ≠ 2) :
    (-Complex.I) ^ (p* ((p-1) / 2)) = Complex.I^ ((p-1) / 2) :=by
  let n :ℕ:= (p-1) / 2
  have hp_eqn:p=2*n+1:=by
    dsimp [n]
    have htwo:2* ((p-1) / 2) = p-1:=
      Nat.two_mul_div_two_of_even (hp.out.even_sub_one hp2)
    calc
      p= (p-1) + 1:= (Nat.succ_pred_eq_of_pos hp.out.pos).symm
      _=2* ((p-1) / 2) + 1:=by rw [htwo]
  calc
    (-Complex.I) ^ (p*n) = (-Complex.I) ^ (2* (n*n) + n) :=by
      congr
      have hp_add:p=n+n+1:=by
        simpa [two_mul,add_assoc,add_left_comm,add_comm] using hp_eqn
      rw [hp_add]
      ring
    _= ((-Complex.I) ^ 2) ^ (n*n) * (-Complex.I) ^ n:=by
          rw [pow_add,pow_mul]
    _= (-1:ℂ) ^ (n*n) * (((-1:ℂ) ^ n) * Complex.I^n) :=by
          rw [show (-Complex.I) ^ 2= (-1:ℂ) by simp,
            show (-Complex.I) ^ n= (((-1:ℂ) * Complex.I) ^ n) by ring,
            mul_pow]
    _= (-1:ℂ) ^ (n*n+n) * Complex.I^n:=by
          have hpowNegOne: (-1:ℂ) ^ (n*n) * (-1:ℂ) ^ n= (-1:ℂ) ^ (n*n+n) :=by
            rw [← pow_add]
          rw [show (-1:ℂ) ^ (n*n) * (((-1:ℂ) ^ n) * Complex.I^n) =
              ((-1:ℂ) ^ (n*n) * (-1:ℂ) ^ n) * Complex.I^n by ac_rfl,
            hpowNegOne]
    _=Complex.I^n:=by
          have hEven:Even (n*n+n) :=by
            simpa [pow_two,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using
              Nat.even_mul_succ_self n
          rcases hEven with ⟨m,hm⟩
          rw [hm,← two_mul,pow_mul]
          simp
    _=Complex.I^ ((p-1) / 2) :=by
          simp [n]
end SignInvariant
end KummerCriterion
end
end Module21
-- Source: KummerCriterion.GaussSum.SignInvariant.VandermondeEndpoint
section Module22
noncomputable section
namespace KummerCriterion
open scoped BigOperators ComplexConjugate
section SignInvariant
variable (p:ℕ) [hp:Fact p.Prime]
theorem uE
  {k:ℕ} (_hk0:0 < k) (hkp:k < p) :
    (1:ℂ) - q2 (p:=p) ^ (p-k) =
      (-Complex.I) *
        Complex.exp ((Real.pi* (k:ℝ) / p) * Complex.I) *
        ((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) :=by
  let a :ℝ:=Real.pi* (k:ℝ) / p
  let S :ℂ:= ((2*Real.sin a :ℝ) : ℂ)
  have hpow:q2 (p:=p) ^ (p-k) =
      Complex.exp ((2*Real.pi* (k:ℝ) / p) * Complex.I) :=by
    simpa [Nat.sub_sub_self (Nat.le_of_lt hkp)] using
      (KummerCriterion.s7 (p:=p) (k:=p-k)
        (Nat.sub_le _ _))
  have hhalf: (2*Real.pi* (k:ℝ) / p) / 2=a:=by
    dsimp [a]
    ring
  calc
    (1:ℂ) - q2 (p:=p) ^ (p-k)
        =1-Complex.exp ((2*Real.pi* (k:ℝ) / p) * Complex.I) :=by
            rw [hpow]
    _=S*
          (Real.cos (a-Real.pi/2) + Real.sin (a-Real.pi/2) * Complex.I) :=by
            simpa [a,S,hhalf] using
              (KummerCriterion.sj (2*Real.pi* (k:ℝ) / p))
    _= (-Complex.I) * Complex.exp (a*Complex.I) * S:=by
            rw [Complex.exp_mul_I]
            have hcos:Real.cos (a-Real.pi/2) = Real.sin a :=by
              rw [Real.cos_sub]
              simp
            have hsin:Real.sin (a-Real.pi/2) = -Real.cos a :=by
              rw [Real.sin_sub]
              simp
            rw [hcos,hsin]
            apply Complex.ext <;>
            simp [S,mul_add,add_mul,mul_assoc,mul_left_comm,mul_comm]
    _= (-Complex.I) * Complex.exp ((Real.pi* (k:ℝ) / p) * Complex.I) *
          ((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) :=by
            simp [a,S]
theorem sw
    {k:ℕ} (hk0:0 < k) (hkp:k < p) :
    ((1:ℂ) - q2 (p:=p) ^ (p-k)) ^ p=
      (-Complex.I) ^ p*
        ((-1:ℂ) ^ k) *
        (((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) ^ p) :=by
  let a :ℂ:= (Real.pi* (k:ℝ) / p) * Complex.I
  rw [uE (p:=p) hk0 hkp,mul_assoc,
    mul_pow,mul_pow]
  have hexp:Complex.exp a ^p= (-1:ℂ) ^ k:=by
    have hExpPi:Complex.exp (Real.pi*Complex.I) = (-1:ℂ) :=by
      rw [Complex.exp_mul_I]
      simp
    rw [← Complex.exp_nat_mul]
    have hp0: (p:ℝ) ≠ 0:=by
      exact_mod_cast hp.out.ne_zero
    have hmulReal: (p:ℝ) * (Real.pi* (k:ℝ) / p) = (k:ℝ) * Real.pi:=by
      field_simp [hp0]
    have hmulCast:
        (p:ℂ) * ((Real.pi* (k:ℝ) / p:ℝ) : ℂ) = (k:ℂ) * (Real.pi:ℂ) :=by
      exact_mod_cast hmulReal
    calc
      Complex.exp ((p:ℂ) * a)
          =Complex.exp (((p:ℂ) * ((Real.pi* (k:ℝ) / p:ℝ) : ℂ)) * Complex.I) :=by
              simp [a,mul_assoc]
      _=Complex.exp (((k:ℂ) * (Real.pi:ℂ)) * Complex.I) :=by
            rw [hmulCast]
      _=Complex.exp ((k:ℂ) * (Real.pi*Complex.I)) :=by
            rw [← mul_assoc]
      _=Complex.exp (Real.pi*Complex.I) ^ k:=by
            rw [Complex.exp_nat_mul]
      _= (-1:ℂ) ^ k:=by rw [hExpPi]
  have hfinal:=congrArg
      (fun x :ℂ=> (-Complex.I) ^ p*
        (x* (((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) ^ p))) hexp
  simpa [a,mul_assoc,mul_left_comm,mul_comm] using hfinal
theorem uM
    {k:ℕ} (hk0:0 < k) (hkp:k < p) :
    ((q2 (p:=p)) ^ k-1) ^ (p-k) *
      ((q2 (p:=p)) ^ (p-k) - 1) ^ k=
        (-Complex.I) ^ p*
          (q2 (p:=p)) ^ (k* (p-k)) *
          (((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) ^ p) :=by
  let z :ℂ:=q2 (p:=p) ^ (p-k)
  have hfirst:q2 (p:=p) ^ k-1=
      q2 (p:=p) ^ k* (1-z) :=by
    dsimp [z]
    calc
      q2 (p:=p) ^ k-1=
          q2 (p:=p) ^ k-q2 (p:=p) ^ p:=by
            rw [(KummerCriterion.rn (p:=p)).pow_eq_one]
      _=q2 (p:=p) ^ k-
            q2 (p:=p) ^ k*q2 (p:=p) ^ (p-k) :=by
            congr 1
            rw [← pow_add]
            congr 1
            omega
      _=q2 (p:=p) ^ k* (1-q2 (p:=p) ^ (p-k)) :=by
            ring
  have hsecond: (q2 (p:=p) ^ (p-k) - 1) ^ k=
      (-1:ℂ) ^ k* (1-z) ^ k:=by
    dsimp [z]
    rw [show q2 (p:=p) ^ (p-k) - 1=
        (-1:ℂ) * (1-q2 (p:=p) ^ (p-k)) by ring,
      mul_pow]
  have hpowcombine: (1-z) ^ (p-k) * (1-z) ^ k= (1-z) ^ p:=by
    rw [← pow_add]
    congr 1
    omega
  calc
    ((q2 (p:=p)) ^ k-1) ^ (p-k) *
        ((q2 (p:=p)) ^ (p-k) - 1) ^ k
        = (q2 (p:=p) ^ (k* (p-k))) *
            ((-1:ℂ) ^ k* (1-z) ^ p) :=by
              rw [hfirst,mul_pow,← pow_mul,hsecond]
              rw [show (q2 (p:=p) ^ (k* (p-k))) * (1-z) ^ (p-k) *
                  ((-1:ℂ) ^ k* (1-z) ^ k) =
                    (q2 (p:=p) ^ (k* (p-k))) *
                      (((-1:ℂ) ^ k) * ((1-z) ^ (p-k) * (1-z) ^ k)) by ac_rfl,
                hpowcombine]
    _= (q2 (p:=p) ^ (k* (p-k))) *
          ((-1:ℂ) ^ k*
            ((-Complex.I) ^ p* ((-1:ℂ) ^ k) *
              (((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) ^ p))) :=by
            rw [sw
              (p:=p) hk0 hkp]
    _= (-Complex.I) ^ p*
          (q2 (p:=p)) ^ (k* (p-k)) *
          (((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) ^ p) :=by
            have hsign: (-1:ℂ) ^ k* (-1:ℂ) ^ k=1:=by
              rw [← pow_add]
              rw [show k +k=2*k by ring,pow_mul]
              simp
            rw [show (q2 (p:=p) ^ (k* (p-k))) *
                ((-1:ℂ) ^ k* (((-Complex.I) ^ p* (-1:ℂ) ^ k) *
                  (((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) ^ p))) =
                  (q2 (p:=p) ^ (k* (p-k))) *
                    (((-1:ℂ) ^ k* (-1:ℂ) ^ k) *
                        ((-Complex.I) ^ p*
                          (((2*Real.sin (Real.pi* (k:ℝ) / p) : ℝ) : ℂ) ^ p))) by
                  ac_rfl,
              hsign]
            simp [mul_assoc,mul_left_comm,mul_comm]
theorem
    s5
    (hp2:p ≠ 2) :
    qp p =
      (-Complex.I) ^ (p* ((p-1) / 2)) *
        (q2 (p:=p)) ^
          (∑ d ∈ Finset.range ((p-1) / 2),(d+1) * (p- (d+1))) *
        (∏ d ∈ Finset.range ((p-1) / 2),
          (((2*Real.sin (Real.pi* ((d+1:ℕ) / p:ℝ)) : ℝ) : ℂ))) ^ p:=by
  let n :ℕ:= (p-1) / 2
  let S :ℕ → ℂ:=fun d =>
    (((2*Real.sin (Real.pi* ((d+1:ℕ) / p:ℝ)) : ℝ) : ℂ))
  have hrootprod:
      ∏ d ∈ Finset.range n,
          (q2 (p:=p)) ^ ((d+1) * (p- (d+1))) =
        (q2 (p:=p)) ^
          (∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) :=by
    simpa using
      (Finset.prod_pow_eq_pow_sum (Finset.range n)
        (fun d => (d+1) * (p- (d+1))) (q2 (p:=p)))
  have hsinprod:
      ∏ d ∈ Finset.range n,S d^p= (∏ d ∈ Finset.range n,S d) ^ p:=by
    simpa using (Finset.prod_pow (Finset.range n) p S)
  calc
    qp p
        = ∏ d ∈ Finset.range n,
            ((-Complex.I) ^ p*
              (q2 (p:=p)) ^ ((d+1) * (p- (d+1))) *
              S d ^p) :=by
                rw [KummerCriterion.ur
                  (p:=p) hp2]
                refine Finset.prod_congr rfl ?_
                intro d hd
                have hdlt:d < n:=Finset.mem_range.mp hd
                have hdp:d+1 < p:=by
                  dsimp [n] at hdlt
                  omega
                simpa [S,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
                  uM (p:=p)
                    (k:=d+1) (Nat.succ_pos d) hdp
    _= (∏ _ ∈ Finset.range n,(-Complex.I) ^ p) *
          (∏ d ∈ Finset.range n,
            (q2 (p:=p)) ^ ((d+1) * (p- (d+1)))) *
          (∏ d ∈ Finset.range n,S d^p) :=by
            rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
    _= (-Complex.I) ^ (p*n) *
          (q2 (p:=p)) ^
            (∑ d ∈ Finset.range n,(d+1) * (p- (d+1))) *
          (∏ d ∈ Finset.range n,S d) ^ p:=by
            rw [Finset.prod_const,Finset.card_range,pow_mul,hrootprod,hsinprod]
    _= (-Complex.I) ^ (p* ((p-1) / 2)) *
          (q2 (p:=p)) ^
            (∑ d ∈ Finset.range ((p-1) / 2),(d+1) * (p- (d+1))) *
          (∏ d ∈ Finset.range ((p-1) / 2),
            (((2*Real.sin (Real.pi* ((d+1:ℕ) / p:ℝ)) : ℝ) : ℂ))) ^ p:=by
            simp [n,S]
theorem xI (hp2:p ≠ 2) :
    LinearMap.det (qn p) = Complex.I^ ((p-1) / 2) :=by
  let n :ℕ:= (p-1) / 2
  let e :ℕ:= ∑ d ∈ Finset.range n,(d+1) * (p- (d+1))
  let S :ℂ:= ∏ d ∈ Finset.range n,
    (((2*Real.sin (Real.pi* ((d+1:ℕ) / p:ℝ)) : ℝ) : ℂ))
  have hsingle:qp p =
      (-Complex.I) ^ (p*n) * (q2 (p:=p)) ^ e*S^p:=by
    simpa [n,e,S] using
      s5
        (p:=p) hp2
  have hroot: (q2 (p:=p)) ^ (p.choose 3 +e) = 1:=by
    simpa [n,e] using
      KummerCriterion.us (p:=p) hp2
  have hSreal: ∏ d ∈ Finset.range n,
      2*Real.sin (Real.pi* ((d+1:ℕ) / p:ℝ)) = Real.sqrt p :=by
    simpa [n] using KummerCriterion.xe (p:=p) hp2
  have hS:S= (Real.sqrt p :ℂ) :=by
    calc
      S= (((∏ d ∈ Finset.range n,
          2*Real.sin (Real.pi* ((d+1:ℕ) / p:ℝ)) : ℝ)) : ℂ) :=by
            simp [S]
      _= (Real.sqrt p :ℂ) :=by
            exact_mod_cast hSreal
  have hsqrt_ne: (Real.sqrt p :ℂ) ≠ 0:=by
    apply Complex.ofReal_ne_zero.2
    apply Real.sqrt_ne_zero'.2
    exact_mod_cast hp.out.pos
  calc
    LinearMap.det (qn p)
        = ((Real.sqrt p :ℂ)⁻¹) ^ p*
            ((q2 (p:=p)) ^ (p.choose 3) *
              qp p) :=
                KummerCriterion.vw (p:=p)
    _= ((Real.sqrt p :ℂ)⁻¹) ^ p*
          ((q2 (p:=p)) ^ (p.choose 3) *
            (((-Complex.I) ^ (p*n) * (q2 (p:=p)) ^ e) * S^p)) :=by
              rw [hsingle]
    _= ((Real.sqrt p :ℂ)⁻¹) ^ p*
          (((-Complex.I) ^ (p*n)) *
            (((q2 (p:=p)) ^ (p.choose 3 +e)) * S^p)) :=by
              rw [show (q2 (p:=p)) ^ (p.choose 3) *
                  (((-Complex.I) ^ (p*n) * (q2 (p:=p)) ^ e) * S^p) =
                    ((-Complex.I) ^ (p*n)) *
                      (((q2 (p:=p)) ^ (p.choose 3) *
                        (q2 (p:=p)) ^ e) * S^p) by ac_rfl,
                ← pow_add]
        _= ((Real.sqrt p :ℂ)⁻¹) ^ p* (((-Complex.I) ^ (p*n)) * (1*S^p)) :=by
          rw [hroot]
        _= ((Real.sqrt p :ℂ)⁻¹) ^ p* (((-Complex.I) ^ (p*n)) * S^p) :=by
          simp
    _= ((-Complex.I) ^ (p*n)) * (((Real.sqrt p :ℂ)⁻¹) ^ p*S^p) :=by
          ac_rfl
    _= ((-Complex.I) ^ (p*n)) * (((Real.sqrt p :ℂ)⁻¹) ^ p* (Real.sqrt p :ℂ) ^ p) :=by
          rw [hS]
    _= (-Complex.I) ^ (p*n) :=by
          rw [← mul_pow]
          simp [hsqrt_ne]
    _=Complex.I^ ((p-1) / 2) :=by
          simpa [n] using KummerCriterion.xU (p:=p) hp2
theorem uV
    (hp2:p ≠ 2) (hp4:p%4=3) :
    LinearMap.det (qn p) = (-1:ℂ) ^ ((p-3) / 4) * Complex.I:=by
  have hhalf: (p-1) / 2=2* ((p-3) / 4) + 1:=by
    omega
  rw [xI (p:=p) hp2,hhalf,pow_add,pow_mul]
  simp [mul_comm]
end SignInvariant
end KummerCriterion
end
end Module22
-- Source: KummerCriterion.GaussSum.SignInvariant.BranchChoice
section Module23
noncomputable section
namespace KummerCriterion
section SignInvariant
open scoped BigOperators ComplexConjugate
variable (p:ℕ) [hp:Fact p.Prime]
local instance (α:Sort*) : DecidableEq α :=Classical.decEq α
local instance (q:Prop) : Decidable q :=Classical.propDecidable q
theorem vl (hp₂:p ≠ 2) :
    (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even).card= (p-1) / 2:=by
  classical
  let E :Finset (DirichletCharacter ℂ p) :=Finset.univ.filter fun χ => χ.Even
  let O :Finset (DirichletCharacter ℂ p) :=Finset.univ.filter fun χ => χ.Odd
  have hdisj:Disjoint E O:=by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even:χ.Even:=by simpa [E] using hχE
    have hχ_odd:χ.Odd:=by simpa [O] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion:E ∪ O= (Finset.univ:Finset (DirichletCharacter ℂ p)) :=by
    ext χ
    simp only [E,O,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hneg_ne_one: (-1:ZMod p) ≠ 1:=by
    have:Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp₂)⟩
    exact ZMod.neg_one_ne_one
  have hsum_zero:
      ∑ χ :DirichletCharacter ℂ p,χ (-1:ZMod p) = 0:=
    DirichletCharacter.sum_characters_eq_zero (R:=ℂ) (n:=p) hneg_ne_one
  have hsum_split:
      (∑ χ :DirichletCharacter ℂ p,χ (-1:ZMod p)) = (E.card:ℂ) - O.card:=by
    have hsum_union:
        (∑ χ :DirichletCharacter ℂ p,χ (-1:ZMod p)) =
          (E ∪ O).sum (fun χ => χ (-1:ZMod p)) :=by
      rw [hunion]
    have hsum_E:E.sum (fun χ => χ (-1:ZMod p)) = E.card:=by
      calc
        E.sum (fun χ => χ (-1:ZMod p)) = E.sum (fun _ => (1:ℂ)) :=by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_even:χ.Even:=by simpa [E] using hχ
          simpa [DirichletCharacter.Even] using hχ_even
        _=E.card:=by simp
    have hsum_O:O.sum (fun χ => χ (-1:ZMod p)) = -(O.card:ℂ) :=by
      calc
        O.sum (fun χ => χ (-1:ZMod p)) = O.sum (fun _ => (-1:ℂ)) :=by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_odd:χ.Odd:=by simpa [O] using hχ
          simpa [DirichletCharacter.Odd] using hχ_odd
        _= -(O.card:ℂ) :=by simp
    calc
      (∑ χ :DirichletCharacter ℂ p,χ (-1:ZMod p)) =
          E.sum (fun χ => χ (-1:ZMod p)) + O.sum (fun χ => χ (-1:ZMod p)) :=by
            rw [hsum_union,Finset.sum_union hdisj]
      _= (E.card:ℂ) - O.card:=by
            rw [hsum_E,hsum_O]
            simp [sub_eq_add_neg]
  have hbalance: (E.card:ℂ) - O.card=0:=by
    rw [← hsum_split]
    exact hsum_zero
  have hsame:E.card=O.card:=by
    have hsame_real: (E.card:ℝ) = O.card:=by
      have hdiff_real: (E.card:ℝ) - O.card=0:=by
        simpa using congrArg Complex.re hbalance
      nlinarith
    exact_mod_cast hsame_real
  have hcard_total:E.card+O.card=p-1:=by
    calc
      E.card+O.card= (E ∪ O).card:=by
        rw [← Finset.card_union_of_disjoint hdisj]
      _=Fintype.card (DirichletCharacter ℂ p) :=by
        rw [hunion,Finset.card_univ]
      _=p-1:=by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R:=ℂ) (n:=p),
          Nat.totient_prime hp.out]
  have hcardE:E.card= (p-1) / 2:=by
    omega
  simpa [E] using hcardE
theorem yY (χ:DirichletCharacter ℂ p) :
    χ⁻¹ (-1:ZMod p) = χ (-1) :=by
  rw [MulChar.inv_apply',inv_neg_one]
theorem yM {χ:DirichletCharacter ℂ p} : χ⁻¹.Even ↔ χ.Even:=by
  simp [DirichletCharacter.Even,yY (p:=p) χ]
theorem wk
    (hp₂:p ≠ 2) (hp₄:p%4=3) :
    (q3 p).Odd:=by
  simpa [DirichletCharacter.Odd] using
    rg (p:=p) hp₂ hp₄
noncomputable def qV:Finset (DirichletCharacter ℂ p) :=
  (qa (p:=p)).filter fun χ => χ.Even
noncomputable def qA:Finset (DirichletCharacter ℂ p) :=
  (qh (p:=p)).filter fun χ => χ.Even
theorem r5 (χ:DirichletCharacter ℂ p) :
    χ ∈ qV (p:=p) ↔
      χ ∈ qa (p:=p) ∧ χ.Even:=by
  simp [qV]
theorem qO (χ:DirichletCharacter ℂ p) :
    χ ∈ qA (p:=p) ↔
      χ ∈ qh (p:=p) ∧ χ.Even:=by
  simp [qA]
theorem uK (hp₂:p ≠ 2) :
    qV (p:=p) =
      qA (p:=p) ∪
        (qA (p:=p)).image fun χ => χ⁻¹:=by
  ext χ
  constructor
  · intro hχ
    rcases (r5 (p:=p) χ).1 hχ with ⟨hχnon,hχeven⟩
    rcases wp (p:=p) (hp₂:=hp₂) hχnon with hχrep | hχinvrep
    · exact Finset.mem_union.mpr <| Or.inl <|
        (qO (p:=p) χ).2 ⟨hχrep,hχeven⟩
    · have hχinv_even: (χ⁻¹:DirichletCharacter ℂ p).Even:=
        (yM (p:=p) (χ:=χ)).2 hχeven
      exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_image.mpr ⟨χ⁻¹,
          (qO (p:=p) (χ⁻¹)).2 ⟨hχinvrep,hχinv_even⟩,
          by simp⟩
  · intro hχ
    rcases Finset.mem_union.mp hχ with hχrep | hχimage
    · rcases (qO (p:=p) χ).1 hχrep with
        ⟨hχrep',hχeven⟩
      exact (r5 (p:=p) χ).2
        ⟨(qD (p:=p) χ).1 hχrep' |>.1,hχeven⟩
    · rcases Finset.mem_image.mp hχimage with ⟨ψ,hψrep,rfl⟩
      rcases (qO (p:=p) ψ).1 hψrep with ⟨hψrep',hψeven⟩
      exact (r5 (p:=p) ψ⁻¹).2
        ⟨rY (p:=p)
            ((qD (p:=p) ψ).1 hψrep' |>.1),
          (yM (p:=p) (χ:=ψ)).2 hψeven⟩
theorem w3:
    Disjoint (qA (p:=p))
      ((qA (p:=p)).image fun χ => χ⁻¹) :=by
  refine Finset.disjoint_left.mpr ?_
  intro χ hχrep hχimage
  rcases Finset.mem_image.mp hχimage with ⟨ψ,hψrep,hψ⟩
  have hψrep':ψ ∈ qh (p:=p) :=
    (qO (p:=p) ψ).1 hψrep |>.1
  have hχrep':χ ∈ qh (p:=p) :=
    (qO (p:=p) χ).1 hχrep |>.1
  have hψinv:ψ⁻¹ ∈ qh (p:=p) :=by
    simpa [hψ] using hχrep'
  exact (sZ (p:=p) hψrep') hψinv
theorem v2
    (hp₂:p ≠ 2) (hp₄:p%4=3) :
    (qV (p:=p)).card= (p-3) / 2:=by
  classical
  let E :Finset (DirichletCharacter ℂ p) :=Finset.univ.filter fun χ => χ.Even
  have htriv_even: (1:DirichletCharacter ℂ p).Even:=by
    change (1:DirichletCharacter ℂ p) (-1:ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1:ZMod p) from isUnit_one.neg)]
  have hquad_odd: (q3 p).Odd:=
    wk (p:=p) hp₂ hp₄
  have hq_not_even: ¬ (q3 p).Even:=
    DirichletCharacter.Odd.not_even (q3 p) hquad_odd
  have hrewrite:
      qV (p:=p) = E.erase (1:DirichletCharacter ℂ p) :=by
    ext χ
    constructor
    · intro hχ
      rcases (r5 (p:=p) χ).1 hχ with ⟨hχnon,hχeven⟩
      rcases (qW (p:=p) χ).1 hχnon with ⟨hχ1,_⟩
      simp [E,hχ1,hχeven]
    · intro hχ
      have hχ1:χ ≠ (1:DirichletCharacter ℂ p) :=by
        simpa [E] using (Finset.mem_erase.mp hχ).1
      have hχeven:χ.Even:=by
        simpa [E] using (Finset.mem_erase.mp hχ).2
      have hχquad:χ ≠ q3 p :=fun hχquad=>
        hq_not_even (hχquad ▸ hχeven)
      exact (r5 (p:=p) χ).2
        ⟨(qW (p:=p) χ).2 ⟨hχ1,hχquad⟩,hχeven⟩
  rw [hrewrite,Finset.card_erase_of_mem]
  · rw [vl (p:=p) hp₂]
    omega
  · simpa [E] using htriv_even
theorem vm
    (hp₂:p ≠ 2) (hp₄:p%4=3) :
    (qA (p:=p)).card= (p-3) / 4:=by
  let reps:=qA (p:=p)
  have hsplit:
      (qV (p:=p)).card=reps.card+reps.card:=by
    rw [uK (p:=p) hp₂,
      Finset.card_union_of_disjoint (w3 (p:=p)),
      Finset.card_image_of_injective _ (fun χ ψ hEq=> by simpa using congrArg Inv.inv hEq)]
  have hcard: (qV (p:=p)).card= (p-3) / 2:=
    v2 (p:=p) hp₂ hp₄
  have htwice: (p-3) / 2=reps.card*2:=by
    omega
  have hdiv: ((p-3) / 2) / 2=reps.card:=
    Nat.div_eq_of_eq_mul_left (by decide:0 < 2) htwice
  have hquarter: ((p-3) / 2) / 2= (p-3) / 4:=by
    omega
  calc
    reps.card= ((p-3) / 2) / 2:=hdiv.symm
    _= (p-3) / 4:=hquarter
theorem vp:
    Finset.prod (qh (p:=p)) (fun χ => -(χ (-1))) =
      (-1:ℂ) ^ (qA (p:=p)).card:=by
  classical
  let reps:=qh (p:=p)
  let g :DirichletCharacter ℂ p → ℂ:=fun χ => if χ.Even then (-1:ℂ) else 1
  have hrewrite:
      Finset.prod reps (fun χ => -(χ (-1))) = Finset.prod reps g :=by
    refine Finset.prod_congr rfl ?_
    intro χ hχ
    rcases DirichletCharacter.even_or_odd χ with hχeven | hχodd
    · have hχeval:χ (-1:ZMod p) = 1:=by
        simpa [DirichletCharacter.Even] using hχeven
      simp [g,hχeven,hχeval]
    · have hχeval:χ (-1:ZMod p) = -1:=by
        simpa [DirichletCharacter.Odd] using hχodd
      have hχnot_even: ¬ χ.Even:=DirichletCharacter.Odd.not_even χ hχodd
      simp [g,hχnot_even,hχeval]
  have hfilter:
      reps.filter (fun χ => g χ ≠ 1) = reps.filter fun χ => χ.Even:=by
    ext χ
    by_cases hχeven:χ.Even
    · have hneq: (-1:ℂ) ≠ 1:=by norm_num
      simp [g,hχeven,hneq]
    · simp [g,hχeven]
  calc
    Finset.prod reps (fun χ => -(χ (-1))) = Finset.prod reps g :=hrewrite
    _=Finset.prod (reps.filter fun χ => χ.Even) g :=by
          rw [← hfilter,Finset.prod_filter_ne_one]
    _=Finset.prod (reps.filter fun χ => χ.Even) (fun _ => (-1:ℂ)) :=by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          simp [g,(Finset.mem_filter.mp hχ).2]
    _= (-1:ℂ) ^ (qA (p:=p)).card:=by
          simp [qA,reps]
theorem w0
    (hp₂:p ≠ 2) (hp₄:p%4=3) :
    Finset.prod (qh (p:=p)) (fun χ => -(χ (-1))) =
      (-1:ℂ) ^ ((p-3) / 4) :=by
  rw [vp (p:=p),
    vm (p:=p) hp₂ hp₄]
theorem sT
    (hp₂:p ≠ 2) (hp₄:p%4=3) :
    q1 (p:=p) (some (q3 p)) =
      -((Real.sqrt p :ℂ)⁻¹*
        gaussSum (q3 p) (ZMod.stdAddChar (N:=p))) :=by
  have hq_ne:q3 p ≠ (1:DirichletCharacter ℂ p) :=
    ri (p:=p) hp₂
  simp [q1,hq_ne,rK (p:=p),
    rg (p:=p) hp₂ hp₄]
theorem uG
    (hp₂:p ≠ 2) (hp₄:p%4=3) :
    q1 (p:=p) (some (q3 p)) = -Complex.I:=by
  let qScalar:ℂ:=q1 (p:=p) (some (q3 p))
  have hdet_block:=
    su
      (p:=p) hp₂
  have hdet_vand:=uV (p:=p) hp₂ hp₄
  have hpair:=w0 (p:=p) hp₂ hp₄
  have hdet_q:
      LinearMap.det (qn p) = (qScalar* (-1:ℂ)) * (-1:ℂ) ^ ((p-3) / 4) :=by
    calc
      LinearMap.det (qn p)
          = (-1:ℂ) * (qScalar* (-1:ℂ) ^ ((p-3) / 4)) :=by
              simpa [qScalar,hpair] using hdet_block
      _= (qScalar* (-1:ℂ)) * (-1:ℂ) ^ ((p-3) / 4) :=by
            ring
  have hpow_ne: ((-1:ℂ) ^ ((p-3) / 4)) ≠ 0:=by simp
  have heq: (qScalar* (-1:ℂ)) * (-1:ℂ) ^ ((p-3) / 4) =
      Complex.I* (-1:ℂ) ^ ((p-3) / 4) :=by
    calc
      (qScalar* (-1:ℂ)) * (-1:ℂ) ^ ((p-3) / 4) = LinearMap.det (qn p) :=
        hdet_q.symm
      _= (-1:ℂ) ^ ((p-3) / 4) * Complex.I:=hdet_vand
      _=Complex.I* (-1:ℂ) ^ ((p-3) / 4) :=by ring
  have hneg:qScalar* (-1:ℂ) = Complex.I:=
    mul_right_cancel₀ hpow_ne heq
  calc
    qScalar=qScalar* (1:ℂ) :=by ring
    _=qScalar* ((-1:ℂ) * (-1:ℂ)) :=by ring
    _= (qScalar* (-1:ℂ)) * (-1:ℂ) :=by ring
    _=Complex.I* (-1:ℂ) :=by rw [hneg]
    _= -Complex.I:=by ring
theorem ug
    (hp₂:p ≠ 2) (hp₄:p%4=3) :
    gaussSum (q3 p) (ZMod.stdAddChar (N:=p)) =
      Complex.I* (Real.sqrt p :ℂ) :=by
  have hp_pos_real: (0:ℝ) < p:=by exact_mod_cast hp.out.pos
  have hsqrt_ne: (Real.sqrt p :ℂ) ≠ 0:=by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hp_pos_real)
  have hscaled_neg:
      -((Real.sqrt p :ℂ)⁻¹*gaussSum (q3 p) (ZMod.stdAddChar (N:=p))) =
        -Complex.I:=by
    rw [← sT
      (p:=p) hp₂ hp₄]
    exact uG (p:=p) hp₂ hp₄
  have hscaled:=congrArg (fun z :ℂ=> (-1:ℂ) * z) hscaled_neg
  have hscaled':
      (Real.sqrt p :ℂ)⁻¹*gaussSum (q3 p) (ZMod.stdAddChar (N:=p)) =
        Complex.I:=by
    simpa [mul_assoc] using hscaled
  have hmul:=congrArg (fun z :ℂ=> (Real.sqrt p :ℂ) * z) hscaled'
  simpa [hsqrt_ne,mul_assoc,mul_left_comm,mul_comm] using hmul
end SignInvariant
end KummerCriterion
end
end Module23
-- Source: KummerCriterion.HMinus.KplusLocalCharacters
section Module24
noncomputable section
open NumberField
open scoped BigOperators Pointwise
namespace KummerCriterion
variable (p:ℕ) [hp:Fact p.Prime]
noncomputable def q5 (ℓ:ℕ) [Fact ℓ.Prime] (hℓp:ℓ ≠ p) : ℕ:=
  let d :=q4 (p:=p) ℓ hℓp
  if Even d then d /2 else d
noncomputable def qo (ℓ:ℕ) [Fact ℓ.Prime] (hℓp:ℓ ≠ p) : ℕ:=
  let d :=q4 (p:=p) ℓ hℓp
  let c :=rd (p:=p) ℓ hℓp
  if Even d then c else c /2
lemma r9 {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p)
    (hd_even:Even (q4 (p:=p) ℓ hℓp)) :
    q5 (p:=p) ℓ hℓp=q4 (p:=p) ℓ hℓp/2:=by
  simp [q5,hd_even]
lemma r8 {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p)
    (hd_odd: ¬ Even (q4 (p:=p) ℓ hℓp)) :
    q5 (p:=p) ℓ hℓp=q4 (p:=p) ℓ hℓp:=by
  simp [q5,hd_odd]
lemma uJ
    {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    (((qx (p:=p) ℓ hℓp: (ZMod p)ˣ) : ZMod p) ^
        q5 (p:=p) ℓ hℓp=1) ∨
      (((qx (p:=p) ℓ hℓp: (ZMod p)ˣ) : ZMod p) ^
        q5 (p:=p) ℓ hℓp= -1) :=by
  let u : (ZMod p)ˣ:=qx (p:=p) ℓ hℓp
  let d :ℕ:=q4 (p:=p) ℓ hℓp
  by_cases hd_even:Even d
  · rcases hd_even with ⟨k,hk⟩
    have hsq: (((u:ZMod p) ^ (d/2)) ^ 2) = 1:=by
      rw [← pow_mul]
      have: (d/2) * 2=d:=by omega
      rw [this]
      dsimp [d,q4]
      change (((u^orderOf u : (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x : (ZMod p)ˣ=> ((x:ZMod p))) (pow_orderOf_eq_one u)
    have hcases: ((u:ZMod p) ^ (d/2)) = 1 ∨ ((u:ZMod p) ^ (d/2)) = -1:=
      sq_eq_one_iff.mp hsq
    have hnot_one: ((u:ZMod p) ^ (d/2)) ≠ 1:=by
      intro hpow
      have hpow_units:u^ (d/2) = 1:=by
        apply Units.ext
        simpa using hpow
      have hdvd:d ∣ d/2:=by
        simpa [d,q4,u] using
          (orderOf_dvd_iff_pow_eq_one (x:=u)).2 hpow_units
      have hk_pos:0 < k:=by
        have hd_pos:0 < d:=by
          dsimp [d,q4]
          exact orderOf_pos u
        omega
      have hle:2*k ≤ k:=by
        have hdvd':2*k ∣ k:=by
          rw [hk] at hdvd
          rw [show k +k=2*k by omega] at hdvd
          simpa using hdvd
        exact Nat.le_of_dvd hk_pos hdvd'
      omega
    rcases hcases with hpow | hpow
    · exact False.elim (hnot_one hpow)
    · right
      simpa [q5,d,hk] using hpow
  · left
    have hpow: (u:ZMod p) ^ d=1:=by
      dsimp [d,q4]
      change (((u^orderOf u : (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x : (ZMod p)ˣ=> ((x:ZMod p))) (pow_orderOf_eq_one u)
    simpa [q5,d,hd_even] using hpow
lemma rU
    {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    orderOf ((qx (p:=p) ℓ hℓp) ^ 2) =
      q5 (p:=p) ℓ hℓp:=by
  let u : (ZMod p)ˣ:=qx (p:=p) ℓ hℓp
  let d :ℕ:=q4 (p:=p) ℓ hℓp
  have hfin:IsOfFinOrder u :=isOfFinOrder_iff_pow_eq_one.mpr
    ⟨d,by
      dsimp [d,q4]
      exact orderOf_pos u,
      by
        dsimp [d,q4]
        exact pow_orderOf_eq_one u⟩
  by_cases hd_even:Even d
  · rcases hd_even with ⟨k,hk⟩
    have hd_even':Even (q4 (p:=p) ℓ hℓp) :=
      ⟨k,by simpa [d] using hk⟩
    have hgcd:d.gcd 2 =2:=by
      apply Nat.dvd_antisymm
      · exact Nat.gcd_dvd_right d 2
      · exact Nat.dvd_gcd ⟨k,by omega⟩ dvd_rfl
    rw [show orderOf (u^2) = d/d.gcd 2 by
        dsimp [d,q4]
        rw [hfin.orderOf_pow],hgcd,
      r9 (p:=p) hℓp hd_even']
  · have hd_odd:Odd d :=Nat.not_even_iff_odd.mp hd_even
    have hgcd:d.gcd 2 =1:=
      Nat.coprime_iff_gcd_eq_one.mp hd_odd.coprime_two_right
    rw [show orderOf (u^2) = d/d.gcd 2 by
        dsimp [d,q4]
        rw [hfin.orderOf_pow],hgcd,
      r8 (p:=p) hℓp (by simpa [d] using hd_even)]
    simp [d]
local instance (α:Sort*) : DecidableEq α :=Classical.decEq α
local instance (q:Prop) : Decidable q :=Classical.propDecidable q
lemma s1 (hp_odd':p ≠ 2) :
    (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even).card= (p-1) / 2:=
  vl p hp_odd'
lemma card_evenNontrivialCharacters (hp_odd':p ≠ 2) :
    (qi (p:=p)).card= (p-3) / 2:=by
  classical
  have htriv_even: (1:DirichletCharacter ℂ p).Even:=by
    change (1:DirichletCharacter ℂ p) (-1:ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1:ZMod p) from isUnit_one.neg)]
  have hrewrite:
      qi (p:=p) =
        (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even).erase 1 :=by
    ext χ
    simp [qi,and_comm]
  rw [hrewrite,Finset.card_erase_of_mem]
  · have hcard_even:
        (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even).card= (p-1) / 2:=
      s1 (p:=p) hp_odd'
    omega
  · simp [htriv_even]
lemma sd
    (hp_odd':p ≠ 2) {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    qo (p:=p) ℓ hℓp*q5 (p:=p) ℓ hℓp=
      (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even).card:=by
  classical
  set d :=q4 (p:=p) ℓ hℓp with hd
  set c :=rd (p:=p) ℓ hℓp with hc
  have hprod_card:c*d=Nat.card (DirichletCharacter ℂ p) :=by
    simpa [c,d] using (xm (p:=p) hℓp)
  have hprod:c*d=p-1:=by
    rw [hprod_card,qH (p:=p)]
  have hp_odd_nat:Odd p :=hp.out.odd_of_ne_two hp_odd'
  rw [s1 (p:=p) hp_odd']
  rcases hp_odd_nat with ⟨m,hm⟩
  have hhalf: (p-1) / 2=m:=by
    omega
  by_cases hd_even:Even d
  · rcases hd_even with ⟨k,hk⟩
    have hkdiv: (k+k) / 2=k:=by
      omega
    have hlhs:
        qo (p:=p) ℓ hℓp*
            q5 (p:=p) ℓ hℓp=
          c*k:=by
      simp [qo,q5,d,hk,hkdiv,← hc]
    have hck:c*k=m:=by
      have hdouble:c*k+c*k=m+m:=by
        calc
          c*k+c*k=c* (k+k) :=by rw [Nat.mul_add]
          _=p-1:=by simpa [hk] using hprod
          _=m+m:=by rw [hm];omega
      have hdouble':2* (c*k) = 2*m:=by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide:0 < 2) hdouble'
    rw [hlhs,hhalf,hck]
  · have hd_odd:Odd d :=Nat.not_even_iff_odd.mp hd_even
    rcases hd_odd with ⟨k,hk⟩
    have hc_even:Even c :=by
      have hprod':c* (2*k+1) = p-1:=by
        simpa [hk] using hprod
      have h_rhs_even:Even (p-1) :=by
        refine ⟨m,?_⟩
        rw [hm]
        omega
      by_contra hc_not_even
      have hc_odd:Odd c :=Nat.not_even_iff_odd.mp hc_not_even
      have hlhs_odd:Odd (c* (2*k+1)) :=
        hc_odd.mul ⟨k,rfl⟩
      have h_lhs_even:Even (c* (2*k+1)) :=by
        simpa [hprod'] using h_rhs_even
      exact (Nat.not_even_iff_odd.mpr hlhs_odd) h_lhs_even
    rcases hc_even with ⟨j,hj⟩
    have hc_half:rd (p:=p) ℓ hℓp/2=j:=by
      rw [← hc,hj]
      simpa [two_mul,Nat.mul_comm] using (Nat.mul_div_right j (by decide:0 < 2))
    have hlhs:
        qo (p:=p) ℓ hℓp*q5 (p:=p) ℓ hℓp=
          j* (2*k+1) :=by
      simp [qo,q5,d,hk,hc_half]
    have hjk:j* (2*k+1) = m:=by
      have hdouble:j* (2*k+1) + j* (2*k+1) = m+m:=by
        calc
          j* (2*k+1) + j* (2*k+1) = (j+j) * (2*k+1) :=by
            rw [Nat.add_mul]
          _=p-1:=by simpa [hj,hk] using hprod
          _=m+m:=by rw [hm];omega
      have hdouble':2* (j* (2*k+1)) = 2*m:=by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide:0 < 2) hdouble'
    rw [hlhs,hhalf,hjk]
lemma v7
    (hp_odd':p ≠ 2) {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) (T:ℂ) :
    Finset.prod (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even)
      (fun χ => (1-χ (ℓ:ZMod p) * T)) =
      (1-T^q5 (p:=p) ℓ hℓp) ^
        qo (p:=p) ℓ hℓp:=by
  classical
  let E :Finset (DirichletCharacter ℂ p) :=
    Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even
  set n :=Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units:Fintype.card (ZMod p)ˣ=n:=by
    rw [hn_def,qH (p:=p),ZMod.card_units]
  have hn_units':Nat.card (ZMod p)ˣ=n:=by
    rw [Nat.card_eq_fintype_card,hn_units]
  have hn_pos:0 < n:=by
    rw [← hn_units]
    exact Fintype.card_pos
  have hp_odd_nat:Odd p :=hp.out.odd_of_ne_two hp_odd'
  have hn_even:Even n :=by
    rcases hp_odd_nat with ⟨m,hm⟩
    refine ⟨m,?_⟩
    rw [hn_def,qH (p:=p),hm]
    omega
  rcases hn_even with ⟨n2,hn2⟩
  have hn2':n=2*n2:=by
    omega
  have hn2_pos:0 < n2:=by
    omega
  have hnp1:n=p-1:=by
    rw [hn_def,qH (p:=p)]
  obtain ⟨g,hg_mon⟩ : ∃ g : (ZMod p)ˣ,∀ x: (ZMod p)ˣ,x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon': ∀ x: (ZMod p)ˣ,∃ m:ℕ,g^m=x:=fun x => hg_mon x
  obtain ⟨a,ha⟩ :=hg_mon' (qx (p:=p) ℓ hℓp)
  have hg_zpow: ∀ x: (ZMod p)ˣ,x ∈ Subgroup.zpowers g :=fun x => by
    obtain ⟨m,hm⟩ :=hg_mon' x
    refine ⟨(m:ℤ),?_⟩
    change g ^ (m:ℤ) = x
    rw [zpow_natCast]
    exact hm
  have hg_order:orderOf g =n:=by
    rw [← hn_units']
    exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hfin_g:IsOfFinOrder g :=isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n,hn_pos,by rw [← hg_order];exact pow_orderOf_eq_one g⟩
  have hgcd2:n.gcd 2 =2:=
    Nat.dvd_antisymm (Nat.gcd_dvd_right n 2) (Nat.dvd_gcd ⟨n2,hn2'⟩ dvd_rfl)
  have hω:IsPrimitiveRoot (Complex.exp (2*Real.pi*Complex.I/n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω :ℂ:=Complex.exp (2*Real.pi*Complex.I/n)
  have hω_unit:IsUnit ω :=hω.isUnit hn_pos.ne'
  set ωu:ℂˣ:=hω_unit.unit with hωu_def
  have hωu_val: (ωu:ℂ) = ω:=by simp [hωu_def]
  have hωu_roots: ∀ k:ℕ,(ωu^k:ℂˣ) ∈ rootsOfUnity n ℂ:=by
    intro k
    rw [mem_rootsOfUnity,← pow_mul,mul_comm]
    have h1: (ωu^n:ℂˣ) = 1:=by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val,Units.val_one,hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul,h1,one_pow]
  let χAt:ℕ → DirichletCharacter ℂ p:=fun k =>
    MulChar.ofRootOfUnity (M:=ZMod p) (R:=ℂ) (ζ:=ωu^k)
      (by rw [hn_units];exact hωu_roots k) hg_zpow
  have hχAt_g: ∀ k:ℕ,χAt k ((g: (ZMod p)ˣ) : ZMod p) = ω^k:=fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val,hωu_val]
  have hℓ_eq: (ℓ:ZMod p) = (((g: (ZMod p)ˣ) : ZMod p)) ^ a:=by
    have h1: (((qx (p:=p) ℓ hℓp: (ZMod p)ˣ) : ZMod p)) = (ℓ:ZMod p) :=by
      simp [qx]
    rw [← h1,← ha,Units.val_pow_eq_pow_val]
  have hχAt_ℓ: ∀ k:ℕ,χAt k (ℓ:ZMod p) = ω^ (k*a) :=fun k => by
    rw [hℓ_eq,map_pow,hχAt_g,← pow_mul]
  have hg_half_sq: ((((g: (ZMod p)ˣ) : ZMod p) ^ n2) ^ 2) = 1:=by
    rw [← pow_mul]
    have:n2*2=n:=by
      omega
    rw [this]
    simpa [Units.val_pow_eq_pow_val,hg_order] using
      congrArg (fun x : (ZMod p)ˣ=> ((x:ZMod p))) (pow_orderOf_eq_one g)
  have hg_half_ne_one: (((g: (ZMod p)ˣ) : ZMod p) ^ n2) ≠ 1:=by
    intro hpow
    have hpow_units:g^n2=1:=by
      apply Units.ext
      simpa using hpow
    have hdvd:n ∣ n2:=by
      rw [← hg_order]
      exact (orderOf_dvd_iff_pow_eq_one (x:=g)).2 hpow_units
    have hle:n ≤ n2:=Nat.le_of_dvd hn2_pos hdvd
    rw [hn2] at hle
    omega
  have hg_half_eq_neg_one: (((g: (ZMod p)ˣ) : ZMod p) ^ n2) = -1:=by
    rcases sq_eq_one_iff.mp hg_half_sq with h1 | h1
    · exact False.elim (hg_half_ne_one h1)
    · exact h1
  let χEvenAt:ℕ → DirichletCharacter ℂ p:=fun k => χAt (2*k)
  have hχEven_mem: ∀ k ∈ Finset.range n2,χEvenAt k ∈ E :=by
    intro k hk
    have h_even:χAt (2*k) (-1:ZMod p) = 1:=by
      rw [← hg_half_eq_neg_one,map_pow,hχAt_g,← pow_mul]
      have: (2*k) * n2=k*n:=by
        rw [hn2']
        simp [Nat.mul_left_comm,Nat.mul_comm]
      rw [this,mul_comm,pow_mul,hω.pow_eq_one,one_pow]
    change χAt (2*k) ∈ E
    rw [show E =Finset.univ.filter (fun χ :DirichletCharacter ℂ p=> χ.Even) from rfl,
      Finset.mem_filter]
    simp [DirichletCharacter.Even,h_even]
  have hχEven_inj:Set.InjOn χEvenAt ↑(Finset.range n2) :=by
    intro j hj k hk hjk
    simp only [Finset.coe_range,Set.mem_Iio] at hj hk
    have hval:χEvenAt j ((g: (ZMod p)ˣ) : ZMod p) = χEvenAt k ((g: (ZMod p)ˣ) : ZMod p) :=
      congrArg (fun χ :DirichletCharacter ℂ p=> χ ((g: (ZMod p)ˣ) : ZMod p)) hjk
    rw [hχAt_g,hχAt_g] at hval
    have hj2:2*j < n:=by
      omega
    have hk2:2*k < n:=by
      omega
    have h_eq:2*j=2*k:=by
      simpa [χEvenAt] using hω.pow_inj hj2 hk2 hval
    omega
  have hE_card:E.card=n2:=by
    rw [s1 (p:=p) hp_odd']
    omega
  have himage_eq:Finset.image χEvenAt (Finset.range n2) = E:=by
    apply Finset.eq_of_subset_of_card_le
    · intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨k,hk,rfl⟩
      exact hχEven_mem k hk
    · rw [hE_card,Finset.card_image_of_injOn hχEven_inj,Finset.card_range]
  have hprod_transfer:
      ∏ χ ∈ E,(1-χ (ℓ:ZMod p) * T) =
        ∏ k ∈ Finset.range n2,(1-ω^ ((2*k) * a) * T) :=by
    calc
      ∏ χ ∈ E,(1-χ (ℓ:ZMod p) * T)
          = ∏ χ ∈ Finset.image χEvenAt (Finset.range n2),(1-χ (ℓ:ZMod p) * T) :=by
              rw [← himage_eq]
      _= ∏ k ∈ Finset.range n2,(1-χEvenAt k (ℓ:ZMod p) * T) :=by
            rw [Finset.prod_image hχEven_inj]
      _= ∏ k ∈ Finset.range n2,(1-ω^ ((2*k) * a) * T) :=by
            refine Finset.prod_congr rfl (fun k _=> ?_)
            simpa [χEvenAt] using congrArg (fun z :ℂ=> 1 -z*T) (hχAt_ℓ (2*k))
  have hω_sq_prim':IsPrimitiveRoot (ω^2) (n/n.gcd 2) :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn_pos 2 hω
  have hω_sq_prim:IsPrimitiveRoot (ω^2) n2:=by
    simpa [hgcd2,hn2'] using hω_sq_prim'
  have hcollapse:
      ∏ k ∈ Finset.range n2,(1-ω^ ((2*k) * a) * T) =
        (1-T^ (n2/n2.gcd a)) ^ n2.gcd a :=by
    calc
      ∏ k ∈ Finset.range n2,(1-ω^ ((2*k) * a) * T)
          = ∏ k ∈ Finset.range n2,(1- (ω^2) ^ (k*a) * T) :=by
              refine Finset.prod_congr rfl (fun k _=> ?_)
              congr 1
              have hexp: (2*k) * a=2* (k*a) :=by
                simp [Nat.mul_assoc,Nat.mul_comm]
              rw [hexp,pow_mul]
      _= (1-T^ (n2/n2.gcd a)) ^ n2.gcd a :=
            wm hn2_pos a hω_sq_prim T
  have hfin_g2:IsOfFinOrder (g^2) :=isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n2,hn2_pos,by
      rw [← pow_mul]
      have:2*n2=n:=by
        omega
      rw [this,← hg_order]
      exact pow_orderOf_eq_one g⟩
  have hg_sq_order:orderOf (g^2) = n2:=by
    rw [hfin_g.orderOf_pow,hg_order,hgcd2,hn2']
    simp
  have hu_sq: (qx (p:=p) ℓ hℓp) ^ 2= (g^2) ^ a:=by
    rw [← ha,← pow_mul]
    have:a*2=2*a:=by
      omega
    rw [this,pow_mul]
  have horder_u_sq:orderOf ((qx (p:=p) ℓ hℓp) ^ 2) = n2/n2.gcd a :=by
    rw [hu_sq,hfin_g2.orderOf_pow,hg_sq_order]
  have hlocalResidue:
      q5 (p:=p) ℓ hℓp=n2/n2.gcd a :=by
    rw [← rU (p:=p) hℓp,horder_u_sq]
  have hlocalResiduePlus_pos:0 < q5 (p:=p) ℓ hℓp:=by
    rw [← rU (p:=p) hℓp]
    exact orderOf_pos _
  have hlocalResidue_pos:0 < n2/n2.gcd a :=by
    simpa [hlocalResidue] using hlocalResiduePlus_pos
  have hcount_mul:qo (p:=p) ℓ hℓp* (n2/n2.gcd a) = n2:=by
    have hbase:=sd (p:=p) hp_odd' hℓp
    rw [hlocalResidue] at hbase
    simpa [E,hE_card] using hbase
  have hgcd_mul:n2.gcd a * (n2/n2.gcd a) = n2:=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left n2 a)
  have hlocalPrimeCount:
      qo (p:=p) ℓ hℓp=n2.gcd a :=by
    have hmul:
        (n2/n2.gcd a) * qo (p:=p) ℓ hℓp=
          (n2/n2.gcd a) * (n2.gcd a) :=by
      rw [Nat.mul_comm (n2/n2.gcd a) (qo (p:=p) ℓ hℓp),
        Nat.mul_comm (n2/n2.gcd a) (n2.gcd a),hcount_mul,hgcd_mul]
    exact Nat.eq_of_mul_eq_mul_left hlocalResidue_pos hmul
  simpa [E] using
    (Eq.trans hprod_transfer (Eq.trans hcollapse (by rw [← hlocalResidue,← hlocalPrimeCount])))
lemma uv
    (hp_odd':p ≠ 2) {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) {s:ℂ} :
    (1- (ℓ:ℂ) ^ (-s)) * qI p ℓ s =
      (1- (ℓ:ℂ) ^ (-((q5 (p:=p) ℓ hℓp:ℂ) * s))) ^
        qo (p:=p) ℓ hℓp:=by
  classical
  have htriv_even: (1:DirichletCharacter ℂ p).Even:=by
    change (1:DirichletCharacter ℂ p) (-1:ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1:ZMod p) from isUnit_one.neg)]
  have hrewrite:
      qi (p:=p) =
        (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even).erase 1 :=by
    ext χ
    simp [qi,and_comm]
  have htrivial_mul:
      (1- (ℓ:ℂ) ^ (-s)) * qI p ℓ s =
        Finset.prod (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even)
          (fun χ => (1-χ (ℓ:ZMod p) * (ℓ:ℂ) ^ (-s))) :=by
    unfold qI
    rw [hrewrite,← Finset.mul_prod_erase
      (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even)
      (fun χ :DirichletCharacter ℂ p=> (1-χ (ℓ:ZMod p) * (ℓ:ℂ) ^ (-s)))]
    · have hℓ_unit:IsUnit ((ℓ:ZMod p)) :=by
        rw [ZMod.isUnit_iff_coprime]
        exact (sz (p:=p) hℓp).symm
      rw [MulChar.one_apply hℓ_unit,one_mul]
    · simp [htriv_even]
  calc
    (1- (ℓ:ℂ) ^ (-s)) * qI p ℓ s
        =Finset.prod (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even)
            (fun χ => (1-χ (ℓ:ZMod p) * (ℓ:ℂ) ^ (-s))) :=htrivial_mul
    _=
        (1- (((ℓ:ℂ) ^ (-s)) ^ q5 (p:=p) ℓ hℓp)) ^
          qo (p:=p) ℓ hℓp:=by
            simpa using
              v7 (p:=p) hp_odd' hℓp
                ((ℓ:ℂ) ^ (-s))
    _=
        (1- (ℓ:ℂ) ^ (-((q5 (p:=p) ℓ hℓp:ℂ) * s))) ^
          qo (p:=p) ℓ hℓp:=by
            congr 1
            congr 1
            rw [show ((ℓ:ℂ) ^ (-s)) ^ q5 (p:=p) ℓ hℓp=
                (ℓ:ℂ) ^ ((-s) * ((q5 (p:=p) ℓ hℓp:ℕ) : ℂ)) by
                  rw [Complex.cpow_mul_nat]]
            congr 1
            ring
end KummerCriterion
end
end Module24
-- Source: KummerCriterion.HMinus.KplusPrimeArithmetic
section Module25
noncomputable section
open NumberField
open NumberField.IsCMField
open scoped BigOperators Pointwise
namespace KummerCriterion
variable (p:ℕ) [hp:Fact p.Prime]
variable {K:Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def q9 (ℓ:ℕ) : Finset (Ideal (𝓞 ((oMR K)))) :=
  IsDedekindDomain.primesOverFinset (q0 ℓ) (𝓞 ((oMR K)))
lemma rt (ℓ:ℕ) [Fact ℓ.Prime] :
    (q9 (K:=K) ℓ).card=
      (Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K)))).ncard:=by
  classical
  have: (q0 ℓ).IsMaximal:=Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (q0 ℓ) ≠ ⊥ :=by
    rw [q0,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out:ℓ.Prime).ne_zero
  unfold q9
  rw [← Set.ncard_coe_finset,IsDedekindDomain.coe_primesOverFinset hne]
lemma qz {ℓ:ℕ} [Fact ℓ.Prime] {P:Ideal (𝓞 ((oMR K)))} :
    P ∈ q9 (K:=K) ℓ ↔
      P ∈ Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K))) :=by
  have: (q0 ℓ).IsMaximal:=Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (q0 ℓ) ≠ ⊥ :=by
    rw [q0,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out:ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 ((oMR K)))
lemma uO {ℓ:ℕ} [Fact ℓ.Prime] {P:Ideal (𝓞 K)}
    (hP:P ∈ qb K ℓ) :
    P.under (𝓞 ((oMR K))) ∈ q9 (K:=K) ℓ :=by
  have hP_over:P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K) :=
    (qs (K:=K) (ℓ:=ℓ)).1 hP
  have:P.IsPrime:=hP_over.1
  rw [qz]
  refine ⟨Ideal.IsPrime.under (𝓞 ((oMR K))) P,?_⟩
  rw [Ideal.liesOver_iff,Ideal.under_under]
  exact (Ideal.liesOver_iff _ _).1 hP_over.2
variable [IsCMField K]
lemma zQ (σ:K ≃ₐ[(oMR K)] K) :
    σ=1 ∨ σ=complexConj K :=by
  by_cases hσ:σ=1
  · exact Or.inl hσ
  · right
    have hcard:Nat.card (K ≃ₐ[(oMR K)] K) = 2:=
      (IsGalois.card_aut_eq_finrank (oMR K) K).trans (sg (K:=K))
    rw [Nat.card_eq_two_iff' (1:K ≃ₐ[(oMR K)] K)] at hcard
    exact ExistsUnique.unique hcard hσ (complexConj_ne_one K)
lemma vF:
    MulSemiringAction.toRingHom (K ≃ₐ[(oMR K)] K) (𝓞 K) (complexConj K) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:=by
  ext x
  change (((complexConj K) • x:𝓞 K) : K) = ((ringOfIntegersComplexConj K x:𝓞 K) : K)
  rfl
lemma zm (P:Ideal (𝓞 K)) :
    complexConj K • P =P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:=by
  rw [Ideal.pointwise_smul_def,vF (K:=K)]
lemma vH {ℓ:ℕ} [Fact ℓ.Prime]
    {P:Ideal (𝓞 K)} (hP:P ∈ qb K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ∈ qb K ℓ:=by
  let PPlus:Ideal (𝓞 ((oMR K))) :=P.under (𝓞 ((oMR K)))
  have hP_over:P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K) :=
    (qs (K:=K) (ℓ:=ℓ)).1 hP
  have hPPlus_mem:PPlus ∈ q9 (K:=K) ℓ :=by
    simpa [PPlus] using uO (K:=K) hP
  have hPPlus_over:PPlus ∈ Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K))) :=
    (qz (K:=K) (ℓ:=ℓ)).1 hPPlus_mem
  have:P.IsPrime:=hP_over.1
  have hmap_liesOver_PPlus:
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus:=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  have:PPlus.LiesOver (q0 ℓ) :=hPPlus_over.2
  have hmap_liesOver:
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver
        (q0 ℓ) :=
    Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((oMR K))) (C:=𝓞 K)
      (𝔓:=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (P:=PPlus) (p:=q0 ℓ)
  have: (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).IsPrime:=
    Ideal.map_isPrime_of_equiv (ringOfIntegersComplexConj K).toRingEquiv
  rw [qs (K:=K) (ℓ:=ℓ)]
  exact ⟨inferInstance,hmap_liesOver⟩
lemma wx (P:Ideal (𝓞 K)) :
    (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).under (𝓞 ((oMR K))) =
      P.under (𝓞 ((oMR K))) :=by
  let PPlus:Ideal (𝓞 ((oMR K))) :=P.under (𝓞 ((oMR K)))
  have hmap_liesOver_PPlus:
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus:=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  simpa [PPlus] using
    (Ideal.over_def
      (P:=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (A:=𝓞 ((oMR K))) (p:=PPlus)).symm
lemma vL {ℓ:ℕ} [Fact ℓ.Prime]
    {P Q :Ideal (𝓞 K)} (hP:P ∈ qb K ℓ) (hQ:Q ∈ qb K ℓ)
    (hunder:P.under (𝓞 ((oMR K))) = Q.under (𝓞 ((oMR K)))) :
    Q=P ∨ Q=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:=by
  let PPlus:Ideal (𝓞 ((oMR K))) :=P.under (𝓞 ((oMR K)))
  have hP_over:P ∈ Ideal.primesOver PPlus (𝓞 K) :=by
    refine ⟨((qs (K:=K) (ℓ:=ℓ)).1 hP).1,
      by simp [Ideal.liesOver_iff,PPlus]⟩
  have hQ_over:Q ∈ Ideal.primesOver PPlus (𝓞 K) :=by
    refine ⟨((qs (K:=K) (ℓ:=ℓ)).1 hQ).1,
      by simpa [Ideal.liesOver_iff,PPlus] using hunder⟩
  have:P.IsPrime:=hP_over.1
  have:Q.IsPrime:=hQ_over.1
  have:Q.LiesOver PPlus:=hQ_over.2
  let _ :MulSemiringAction Gal(K/(oMR K)) (𝓞 K) :=inferInstance
  have _ :IsGaloisGroup Gal(K/(oMR K)) (𝓞 ((oMR K))) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/(oMR K))) (𝓞 ((oMR K))) (𝓞 K) ((oMR K)) K
  obtain ⟨σ,hσ⟩ :=Ideal.exists_smul_eq_of_isGaloisGroup
    (A:=𝓞 ((oMR K))) (B:=𝓞 K) (p:=PPlus) (P:=P) (Q:=Q) (G:=Gal(K/(oMR K)))
  rcases zQ (K:=K) σ with rfl | rfl
  · left
    simpa using hσ.symm
  · right
    rw [zm (K:=K) P] at hσ
    exact hσ.symm
lemma rD {ℓ:ℕ} [Fact ℓ.Prime]
    {P:Ideal (𝓞 K)} (hP:P ∈ qb K ℓ) :
    let Pconj:=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
    let fiber:= (qb K ℓ).filter
      (fun Q => Q.under (𝓞 ((oMR K))) = P.under (𝓞 ((oMR K))))
    (Pconj=P ∧ fiber= ({P} : Finset (Ideal (𝓞 K)))) ∨
      (Pconj ≠ P ∧ fiber= {P,Pconj}) :=by
  classical
  let Pconj:Ideal (𝓞 K) :=P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
  let fiber:Finset (Ideal (𝓞 K)) := (qb K ℓ).filter
    (fun Q => Q.under (𝓞 ((oMR K))) = P.under (𝓞 ((oMR K))))
  have hPconj:Pconj ∈ qb K ℓ:=by
    simpa [Pconj] using vH (K:=K) hP
  have hunder_conj:Pconj.under (𝓞 ((oMR K))) = P.under (𝓞 ((oMR K))) :=by
    simpa [Pconj] using wx (K:=K) P
  have hP_fiber:P ∈ fiber:=by
    simp [fiber,hP]
  have hPconj_fiber:Pconj ∈ fiber:=by
    simp [fiber,hPconj,hunder_conj]
  have hfiber_subset {Q:Ideal (𝓞 K)} (hQ:Q ∈ fiber) : Q=P ∨ Q=Pconj:=by
    have hQ_mem:Q ∈ qb K ℓ:= (Finset.mem_filter.1 hQ).1
    have hQ_under:Q.under (𝓞 ((oMR K))) = P.under (𝓞 ((oMR K))) := (Finset.mem_filter.1 hQ).2
    rcases vL (K:=K) hP hQ_mem hQ_under.symm with
      hQP | hQconj
    · exact Or.inl hQP
    · exact Or.inr (by simpa [Pconj] using hQconj)
  by_cases hfix:Pconj=P
  · left
    refine ⟨hfix,Finset.ext fun Q => ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj,hfix]
        simp
    · intro hQ
      have hQP:Q=P:=by simpa using hQ
      subst hQP
      exact hP_fiber
  · right
    refine ⟨hfix,Finset.ext fun Q => ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj]
        simp [Pconj]
    · intro hQ
      have hQ':Q=P ∨ Q=Pconj:=by
        simpa [hfix] using! hQ
      rcases hQ' with hQP | hQconj
      · rw [hQP]
        exact hP_fiber
      · rw [hQconj]
        exact hPconj_fiber
noncomputable def rP (hp_odd:p ≠ 2) : Gal(K/ℚ) :=by
  letI:IsCMField K :=r0 (p:=p) (K:=K) hp_odd
  exact
    { (complexConj K).toRingEquiv with
      commutes':=fun q => by
        exact map_ratCast ((complexConj K).toRingEquiv.toRingHom) q }
@[simp] private lemma complexConjRat_apply (hp_odd:p ≠ 2) (x:K) :
    rP (p:=p) (K:=K) hp_odd x =complexConj K x:=by
  rfl
lemma vn (hp_odd:p ≠ 2) :
    MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K)
        (rP (p:=p) (K:=K) hp_odd) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:=by
  ext x
  change rP (p:=p) (K:=K) hp_odd x =
      ((ringOfIntegersComplexConj K x:𝓞 K) : K)
  simp [complexConjRat_apply,coe_ringOfIntegersComplexConj]
lemma sY (hp_odd:p ≠ 2) (P:Ideal (𝓞 K)) :
    (rP (p:=p) (K:=K) hp_odd • P) =
      P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom:=by
  rw [Ideal.pointwise_smul_def,vn
    (p:=p) (K:=K) hp_odd]
omit [IsCMField K] in
lemma u7 (hp_odd:p ≠ 2) :
    IsCyclotomicExtension.Rat.galEquivZMod p K
        (rP (p:=p) (K:=K) hp_odd) = -1:=by
  have:IsCMField K :=r0 (p:=p) (K:=K) hp_odd
  let c :Gal(K/ℚ) :=rP (p:=p) (K:=K) hp_odd
  have hζ:=IsCyclotomicExtension.zeta_spec p ℚ K
  have hc:
      c (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p-1) :=by
    have hc':=congrArg (fun x :𝓞 K=> (x:K)) (rT (p:=p) (K:=K))
    rw [coe_ringOfIntegersComplexConj] at hc'
    change (complexConj K) hζ.toInteger.1=
      hζ.toInteger.1^ (p-1) at hc'
    simpa [c,complexConjRat_apply,hζ.coe_toInteger] using hc'
  have hpow:
      (IsCyclotomicExtension.zeta p ℚ K) ^
          (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val=
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p-1) :=by
    calc
      (IsCyclotomicExtension.zeta p ℚ K) ^ (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val
          =c (IsCyclotomicExtension.zeta p ℚ K) :=by
              symm
              exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                (n:=p) (K:=K) c hζ.pow_eq_one
      _= (IsCyclotomicExtension.zeta p ℚ K) ^ (p-1) :=hc
  apply Units.ext
  have hpow':=hpow
  rw [(hζ.isOfFinOrder (NeZero.ne p)).pow_inj_mod,← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff',ZMod.natCast_val,Nat.cast_sub hp.out.one_le,
    ZMod.natCast_self,zero_sub,Nat.cast_one] at hpow'
  simpa [c] using hpow'
lemma uC
    {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p)
    (hd_even:Even (q4 (p:=p) ℓ hℓp)) :
    qx (p:=p) ℓ hℓp^q5 (p:=p) ℓ hℓp=
      (-1: (ZMod p)ˣ) :=by
  let u : (ZMod p)ˣ:=qx (p:=p) ℓ hℓp
  let d :ℕ:=q4 (p:=p) ℓ hℓp
  rcases uJ (p:=p) hℓp with hpow | hpow
  · have hpow_units:u^q5 (p:=p) ℓ hℓp=1:=by
      apply Units.ext
      simpa [u,Units.val_pow_eq_pow_val] using hpow
    have hdvd:d ∣ q5 (p:=p) ℓ hℓp:=by
      simpa [d,q4,u] using (orderOf_dvd_iff_pow_eq_one (x:=u)).2 hpow_units
    have hd_pos:0 < d:=by
      dsimp [d,q4,u]
      exact orderOf_pos u
    have hhalf:q5 (p:=p) ℓ hℓp=d/2:=by
      simpa [d] using r9 (p:=p) hℓp hd_even
    have hhalf_pos:0 < d/2:=by
      rcases hd_even with ⟨k,hk⟩
      rw [show d =2*k by omega]
      omega
    have hle:d ≤ d/2:=by
      rw [hhalf] at hdvd
      exact Nat.le_of_dvd hhalf_pos hdvd
    omega
  · apply Units.ext
    simpa [u,Units.val_pow_eq_pow_val] using hpow
lemma rB
    (hp_odd:p ≠ 2) {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    (-1: (ZMod p)ˣ) ∈ Subgroup.zpowers (qx (p:=p) ℓ hℓp) ↔
      Even (q4 (p:=p) ℓ hℓp) :=by
  let u : (ZMod p)ˣ:=qx (p:=p) ℓ hℓp
  constructor
  · intro hneg
    have htwo:2 ∣ orderOf u :=by
      have horder_neg:orderOf (-1: (ZMod p)ˣ) = 2:=by
        rw [← orderOf_units,Units.coe_neg_one,orderOf_neg_one,ringChar.eq (ZMod p) p,
          if_neg hp_odd]
      exact horder_neg ▸ orderOf_dvd_of_mem_zpowers hneg
    simpa [u,q4,even_iff_two_dvd] using htwo
  · intro hd_even
    refine Subgroup.mem_zpowers_iff.mpr ⟨q5 (p:=p) ℓ hℓp,?_⟩
    rw [zpow_natCast]
    exact uC (p:=p) hℓp hd_even
omit [IsCMField K] in
lemma rJ
    (hp_odd:p ≠ 2) {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p)
    {P:Ideal (𝓞 K)} (hP:P ∈ qb K ℓ) :
    (rP (p:=p) (K:=K) hp_odd ∈ MulAction.stabilizer Gal(K/ℚ) P) ↔
      Even (q4 (p:=p) ℓ hℓp) :=by
  let c :Gal(K/ℚ) :=rP (p:=p) (K:=K) hp_odd
  have hP_over:P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K) :=
    (qs (K:=K) (ℓ:=ℓ)).1 hP
  have:P.LiesOver (Ideal.span {(ℓ:ℤ)}) :=by
    simpa [q0] using hP_over.2
  have: (q0 ℓ).IsMaximal:=by
    simpa [q0] using Int.ideal_span_isMaximal_of_prime ℓ
  have:P.IsMaximal:=Ideal.isMaximal_of_mem_primesOver hP_over
  constructor
  · intro hc
    have hmem_map:IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := ⟨c,hc,rfl⟩
    rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n:=p) (K:=K) (p:=ℓ) (P:=P)
      ((sz (p:=p) hℓp).symm),u7
      (p:=p) (K:=K) hp_odd] at hmem_map
    simpa [qx] using
      (rB
        (p:=p) hp_odd hℓp).1 hmem_map
  · intro h_even
    have hneg_mem: (-1: (ZMod p)ˣ) ∈ Subgroup.zpowers (qx (p:=p) ℓ hℓp) :=
      (rB (p:=p) hp_odd hℓp).2 h_even
    have hmem_map:IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) :=by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n:=p) (K:=K) (p:=ℓ) (P:=P)
        ((sz (p:=p) hℓp).symm),u7
        (p:=p) (K:=K) hp_odd]
      simpa [qx] using hneg_mem
    rcases hmem_map with ⟨σ,hσ,hσeq⟩
    have hc_eq:σ=c:= (IsCyclotomicExtension.Rat.galEquivZMod p K).injective hσeq
    subst hc_eq
    exact hσ
lemma ru
    (hp_odd:p ≠ 2) {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p)
    {P:Ideal (𝓞 K)} (hP:P ∈ qb K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom=P ↔
      Even (q4 (p:=p) ℓ hℓp) :=by
  let c :Gal(K/ℚ) :=rP (p:=p) (K:=K) hp_odd
  constructor
  · intro hmap
    have hsmul:c • P=P:=by
      rw [sY (p:=p) (K:=K) hp_odd]
      exact hmap
    have hc:c ∈ MulAction.stabilizer Gal(K/ℚ) P :=by simpa [c] using hsmul
    exact (rJ
      (p:=p) (K:=K) hp_odd hℓp hP).1 hc
  · intro h_even
    have hc:c ∈ MulAction.stabilizer Gal(K/ℚ) P :=
      (rJ
        (p:=p) (K:=K) hp_odd hℓp hP).2 h_even
    have hsmul:c • P=P:=by simpa [c] using hc
    rw [sY (p:=p) (K:=K) hp_odd] at hsmul
    exact hsmul
lemma sU
    (hp_odd:p ≠ 2) {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p)
    {P:Ideal (𝓞 K)} (hP:P ∈ qb K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom=P ↔
      q5 (p:=p) ℓ hℓp=q4 (p:=p) ℓ hℓp/2:=by
  rw [ru
    (p:=p) (K:=K) hp_odd hℓp hP]
  constructor
  · exact r9 (p:=p) hℓp
  · intro hhalf
    by_contra hodd
    have hself:=r8 (p:=p) hℓp hodd
    have hpos:0 < q4 (p:=p) ℓ hℓp:=by
      unfold q4 qx
      exact orderOf_pos _
    rw [hself] at hhalf
    omega
omit [IsCMField K] in
lemma uf {ℓ:ℕ} [Fact ℓ.Prime]
    {P:Ideal (𝓞 K)} (hP:P ∈ qb K ℓ)
    {PPlus:Ideal (𝓞 ((oMR K)))} (hPPlus:P.under (𝓞 ((oMR K))) = PPlus) :
    let fiber:= (qb K ℓ).filter
      (fun Q => Q.under (𝓞 ((oMR K))) = PPlus)
    fiber.card= (Ideal.primesOver PPlus (𝓞 K)).ncard:=by
  classical
  let fiber:Finset (Ideal (𝓞 K)) := (qb K ℓ).filter
    (fun Q => Q.under (𝓞 ((oMR K))) = PPlus)
  have hPPlus_mem:PPlus ∈ q9 (K:=K) ℓ :=by
    simpa [hPPlus] using uO (K:=K) hP
  have hPPlus_over:PPlus ∈ Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K))) :=
    (qz (K:=K) (ℓ:=ℓ)).1 hPPlus_mem
  have:PPlus.LiesOver (q0 ℓ) :=hPPlus_over.2
  have hfiber: (↑fiber:Set (Ideal (𝓞 K))) = Ideal.primesOver PPlus (𝓞 K) :=by
    ext Q
    constructor
    · intro hQ
      rw [Finset.mem_coe,Finset.mem_filter] at hQ
      rcases hQ with ⟨hQ_fin,hQ_under⟩
      have hQ_over:Q ∈ Ideal.primesOver (q0 ℓ) (𝓞 K) :=
        (qs (K:=K) (ℓ:=ℓ)).1 hQ_fin
      have:Q.IsPrime:=hQ_over.1
      exact ⟨inferInstance,(Ideal.liesOver_iff _ _).2 hQ_under.symm⟩
    · intro hQ
      have:Q.IsPrime:=hQ.1
      have:Q.LiesOver PPlus:=hQ.2
      have hQ_over:Q.LiesOver (q0 ℓ) :=
        Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((oMR K))) (C:=𝓞 K)
          (𝔓:=Q) (P:=PPlus) (p:=q0 ℓ)
      have hQ_fin:Q ∈ qb K ℓ:=by
        rw [qs (K:=K) (ℓ:=ℓ)]
        exact ⟨inferInstance,hQ_over⟩
      have hQ_under:Q.under (𝓞 ((oMR K))) = PPlus:=
        ((Ideal.liesOver_iff _ _).1 (show Q.LiesOver PPlus from inferInstance)).symm
      rw [Finset.mem_coe,Finset.mem_filter]
      exact ⟨hQ_fin,hQ_under⟩
  simpa [fiber] using (show fiber.card= (Ideal.primesOver PPlus (𝓞 K)).ncard from by
    rw [← Set.ncard_coe_finset,hfiber])
omit [IsCMField K] in
lemma rq
    (hp_odd:p ≠ 2) {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p)
    (PPlus:Ideal (𝓞 ((oMR K))))
    (hPPlus:PPlus ∈ Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K)))) :
    PPlus.inertiaDeg ℤ =q5 (p:=p) ℓ hℓp:=by
  classical
  have:IsCMField K :=r0 (p:=p) (K:=K) hp_odd
  have:PPlus.IsPrime:=hPPlus.1
  have:PPlus.LiesOver (q0 ℓ) :=hPPlus.2
  obtain ⟨⟨P,hP_prime,hP_over_PPlus⟩⟩ :=PPlus.nonempty_primesOver (S:=𝓞 K)
  have hP_over:P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K) :=by
    refine ⟨hP_prime,?_⟩
    exact Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((oMR K))) (C:=𝓞 K)
      (𝔓:=P) (P:=PPlus) (p:=q0 ℓ)
  have hP_fin:P ∈ qb K ℓ:=
    (qs (K:=K) (ℓ:=ℓ)).2 hP_over
  have hℓ_ne:q0 ℓ ≠ ⊥ :=by
    rw [q0,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out:ℓ.Prime).ne_zero
  have hPPlus_eq:P.under (𝓞 ((oMR K))) = PPlus:=
    ((Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)).symm
  let fiber:Finset (Ideal (𝓞 K)) := (qb K ℓ).filter
    (fun Q => Q.under (𝓞 ((oMR K))) = PPlus)
  have hfiber_ncard:fiber.card= (Ideal.primesOver PPlus (𝓞 K)).ncard:=by
    simpa [fiber] using uf
      (K:=K) hP_fin hPPlus_eq
  have hram_tower:
      P.ramificationIdx ℤ =
        PPlus.ramificationIdx ℤ *P.ramificationIdx (𝓞 ((oMR K))) :=by
    simpa using Ideal.ramificationIdx_tower
      (R:=ℤ) (S:=𝓞 ((oMR K))) (T:=𝓞 K) (q:=PPlus) (r:=P)
  have hram_rel:P.ramificationIdx (𝓞 ((oMR K))) = 1:=by
    apply Nat.eq_one_of_dvd_one
    refine ⟨PPlus.ramificationIdx ℤ,?_⟩
    rw [mul_comm,← hram_tower,
      un (p:=p) (K:=K) hℓp P hP_over]
  have hPPlus_ne_bot:PPlus ≠ ⊥ :=by
    intro hbot
    have hlie:PPlus.LiesOver (q0 ℓ) :=inferInstance
    have hover:= (Ideal.liesOver_iff _ _).1 hlie
    have hcomap_bot:
        Ideal.comap (algebraMap ℤ (𝓞 ((oMR K)))) (⊥ : Ideal (𝓞 ((oMR K)))) = ⊥ :=by
      ext x
      simp
    have hneq:q0 ℓ ≠ ⊥ :=by
      rw [q0,Ne,Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out:ℓ.Prime).ne_zero
    exact hneq (by simpa [Ideal.under_def,hbot,hcomap_bot] using hover)
  have _ :IsGaloisGroup Gal(K/(oMR K)) (𝓞 ((oMR K))) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/(oMR K))) (𝓞 ((oMR K))) (𝓞 K) ((oMR K)) K
  have hquad: (Ideal.primesOver PPlus (𝓞 K)).ncard*P.inertiaDeg (𝓞 ((oMR K))) = 2:=by
    have hfund:=Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p:=PPlus)
      (B:=𝓞 K) (G:=Gal(K/(oMR K)))
    have hcard_gal:Nat.card Gal(K/(oMR K)) = 2:=
      (IsGalois.card_aut_eq_finrank (oMR K) K).trans (sg (K:=K))
    rw [hcard_gal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (p:=PPlus) (P:=P) (G:=Gal(K/(oMR K))),
      Ideal.inertiaDegIn_eq_inertiaDeg (p:=PPlus) (P:=P) (G:=Gal(K/(oMR K))),
      hram_rel] at hfund
    simpa using hfund
  have hinertia_tower:
      P.inertiaDeg ℤ =
        PPlus.inertiaDeg ℤ *P.inertiaDeg (𝓞 ((oMR K))) :=by
    simpa using Ideal.inertiaDeg_tower
      (R:=ℤ) (S:=𝓞 ((oMR K))) (T:=𝓞 K) (q:=PPlus) (r:=P)
  have hP_inertia:
      P.inertiaDeg ℤ =q4 (p:=p) ℓ hℓp:=by
    exact rv (p:=p) (K:=K) hℓp P hP_over
  by_cases hfix:P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom=P
  · have hfiber_card:fiber.card=1:=by
      rcases rD (K:=K) hP_fin with
        hsingle | hpair
      · have hsingle_fiber:fiber= ({P} : Finset (Ideal (𝓞 K))) :=by
          simpa [fiber,hPPlus_eq] using hsingle.2
        rw [hsingle_fiber]
        simp
      · exact (hpair.1 hfix).elim
    have hcard_primes: (Ideal.primesOver PPlus (𝓞 K)).ncard=1:=by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia:P.inertiaDeg (𝓞 ((oMR K))) = 2:=by
      rw [hcard_primes] at hquad
      simpa using hquad
    have hhalf:q5 (p:=p) ℓ hℓp=
        q4 (p:=p) ℓ hℓp/2:=
      (sU
        (p:=p) (K:=K) hp_odd hℓp hP_fin).1 hfix
    rw [hhalf]
    rw [hP_inertia,hrel_inertia] at hinertia_tower
    omega
  · have hfiber_card:fiber.card=2:=by
      rcases rD (K:=K) hP_fin with
        hsingle | hpair
      · exact (hfix hsingle.1).elim
      · have hpair_fiber:
            fiber=
              ({P,P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom} :
                Finset (Ideal (𝓞 K))) :=by
          simpa [fiber,hPPlus_eq] using hpair.2
        rw [hpair_fiber]
        rw [Finset.card_eq_two]
        exact ⟨P,P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          by simpa [eq_comm] using hpair.1,rfl⟩
    have hcard_primes: (Ideal.primesOver PPlus (𝓞 K)).ncard=2:=by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia:P.inertiaDeg (𝓞 ((oMR K))) = 1:=by
      rw [hcard_primes] at hquad
      omega
    have hnot_even: ¬ Even (q4 (p:=p) ℓ hℓp) :=fun h_even=>
      hfix
        ((ru
          (p:=p) (K:=K) hp_odd hℓp hP_fin).2 h_even)
    have hself:q5 (p:=p) ℓ hℓp=
        q4 (p:=p) ℓ hℓp:=
      r8 (p:=p) hℓp hnot_even
    rw [hself]
    rw [hP_inertia,hrel_inertia] at hinertia_tower
    omega
omit [IsCMField K] in
lemma xs {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p)
    (PPlus:Ideal (𝓞 ((oMR K))))
    (hPPlus:PPlus ∈ Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K)))) :
    PPlus.ramificationIdx ℤ =1:=by
  have:PPlus.IsPrime:=hPPlus.1
  have:PPlus.LiesOver (q0 ℓ) :=hPPlus.2
  obtain ⟨⟨P,hP_prime,hP_over_PPlus⟩⟩ :=PPlus.nonempty_primesOver (S:=𝓞 K)
  have hP_over:P ∈ Ideal.primesOver (q0 ℓ) (𝓞 K) :=by
    refine ⟨hP_prime,?_⟩
    exact Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((oMR K))) (C:=𝓞 K)
      (𝔓:=P) (P:=PPlus) (p:=q0 ℓ)
  have hram_tower:
      P.ramificationIdx ℤ =
        PPlus.ramificationIdx ℤ *P.ramificationIdx (𝓞 ((oMR K))) :=by
    simpa using Ideal.ramificationIdx_tower
      (R:=ℤ) (S:=𝓞 ((oMR K))) (T:=𝓞 K) (q:=PPlus) (r:=P)
  have hℓ_ne:q0 ℓ ≠ ⊥ :=by
    rw [q0,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out:ℓ.Prime).ne_zero
  have hram_abs:P.ramificationIdx ℤ =1:=by
    exact KummerCriterion.un (p:=p) (K:=K) hℓp P hP_over
  apply Nat.eq_one_of_dvd_one
  refine ⟨P.ramificationIdx (𝓞 ((oMR K))),?_⟩
  rw [← hram_tower,hram_abs]
lemma sx (hp_odd:p ≠ 2)
    {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) :
    (Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K)))).ncard=
      qo (p:=p) ℓ hℓp:=by
  have: (q0 ℓ).IsMaximal:=by
    simpa [q0] using Int.ideal_span_isMaximal_of_prime ℓ
  have hne: (q0 ℓ) ≠ ⊥ :=by
    rw [q0,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out:ℓ.Prime).ne_zero
  have hcoe: ((q9 (K:=K) ℓ :Finset (Ideal (𝓞 ((oMR K))))) :
      Set (Ideal (𝓞 ((oMR K))))) = Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K))) :=
    IsDedekindDomain.coe_primesOverFinset hne (𝓞 ((oMR K)))
  have hsum:
      ∑ PPlus ∈ q9 (K:=K) ℓ,
          PPlus.ramificationIdx ℤ *PPlus.inertiaDeg ℤ =Module.finrank ℚ ((oMR K)) :=by
    rw [← NumberField.RingOfIntegers.rank ((oMR K)),
      ← Ideal.sum_ramification_inertia_eq_finrank (q0 ℓ) (𝓞 ((oMR K))),
      ← Finset.sum_coe_sort]
    exact Fintype.sum_equiv (Equiv.setCongr hcoe) _ _ fun _ => rfl
  have hsum_const:
      (q9 (K:=K) ℓ).card*q5 (p:=p) ℓ hℓp=
        Module.finrank ℚ ((oMR K)) :=by
    calc
      (q9 (K:=K) ℓ).card*q5 (p:=p) ℓ hℓp
          = ∑ PPlus ∈ q9 (K:=K) ℓ,
              q5 (p:=p) ℓ hℓp:=by
              simp
      _= ∑ PPlus ∈ q9 (K:=K) ℓ,
              PPlus.ramificationIdx ℤ *PPlus.inertiaDeg ℤ :=by
              refine Finset.sum_congr rfl ?_
              intro PPlus hPPlus_fin
              have hPPlus:PPlus ∈ Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K))) :=
                (qz (K:=K) (ℓ:=ℓ)).1 hPPlus_fin
              rw [xs (p:=p) (K:=K) hℓp PPlus hPPlus,
                rq (p:=p) (K:=K)
                  hp_odd hℓp PPlus hPPlus]
              simp
      _=Module.finrank ℚ ((oMR K)) :=hsum
  rw [rt (K:=K) (ℓ:=ℓ),
    uz (p:=p) (K:=K)] at hsum_const
  have hlocal:=sd (p:=p) hp_odd hℓp
  rw [s1 (p:=p) hp_odd] at hlocal
  have hd_pos:0 < q4 (p:=p) ℓ hℓp:=by
    dsimp [q4]
    exact orderOf_pos (qx (p:=p) ℓ hℓp)
  have hfd_pos:0 < q5 (p:=p) ℓ hℓp:=by
    by_cases hde:Even (q4 (p:=p) ℓ hℓp)
    · rcases hde with ⟨k,hk⟩
      rw [r9 (p:=p) hℓp ⟨k,hk⟩]
      omega
    · rw [r8 (p:=p) hℓp hde]
      exact hd_pos
  have hmul:
      (Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K)))).ncard*
        q5 (p:=p) ℓ hℓp=
          qo (p:=p) ℓ hℓp*q5 (p:=p) ℓ hℓp:=by
    omega
  exact Nat.eq_of_mul_eq_mul_right hfd_pos (by simpa [Nat.mul_comm] using hmul)
lemma s0 (hp_odd:p ≠ 2)
    {ℓ:ℕ} [Fact ℓ.Prime] (hℓp:ℓ ≠ p) {s:ℂ} :
    qm (oMR K) ℓ s=
      (1- (ℓ:ℂ) ^ (-(q5 (p:=p) ℓ hℓp:ℂ) * s)) ^
        qo (p:=p) ℓ hℓp:=by
  classical
  have hcard_eq:
      (q9 (K:=K) ℓ).card=
        qo (p:=p) ℓ hℓp:=by
    rw [rt (K:=K) (ℓ:=ℓ)]
    exact sx (p:=p) (K:=K) hp_odd hℓp
  unfold qm
  change Finset.prod (q9 (K:=K) ℓ) (fun PPlus=>
      (1- (Ideal.absNorm PPlus:ℂ) ^ (-s))) =
        (1- (ℓ:ℂ) ^ (-(q5 (p:=p) ℓ hℓp:ℂ) * s)) ^
          qo (p:=p) ℓ hℓp
  have hprod_eq: ∀ PPlus ∈ q9 (K:=K) ℓ,
      (1- (Ideal.absNorm PPlus:ℂ) ^ (-s)) =
        1- (ℓ:ℂ) ^ (-(q5 (p:=p) ℓ hℓp:ℂ) * s) :=by
    intro PPlus hP
    have hPmem:PPlus ∈ Ideal.primesOver (q0 ℓ) (𝓞 ((oMR K))) :=
      (qz (K:=K) (ℓ:=ℓ)).1 hP
    have:PPlus.LiesOver (q0 ℓ) :=hPmem.2
    have:PPlus.LiesOver (Ideal.span {(ℓ:ℤ)}) :=hPmem.2
    have: (q0 ℓ).IsMaximal:=by
      simpa [q0] using Int.ideal_span_isMaximal_of_prime ℓ
    have:PPlus.IsMaximal:=Ideal.isMaximal_of_mem_primesOver hPmem
    have habsNorm:Ideal.absNorm PPlus=ℓ^ (q5 (p:=p) ℓ hℓp) :=by
      rw [← rq (p:=p) (K:=K)
        hp_odd hℓp PPlus hPmem,
        ← Ideal.inertiaDeg'_eq_inertiaDeg (p:=q0 ℓ) (q:=PPlus)]
      simpa [q0] using Ideal.absNorm_eq_pow_inertiaDeg' PPlus (Fact.out:ℓ.Prime)
    rw [habsNorm]
    push_cast
    have:=Complex.natCast_cpow_natCast_mul ℓ (q5 (p:=p) ℓ hℓp) (-s)
    rw [show-((q5 (p:=p) ℓ hℓp:ℂ)) * s=
        ((q5 (p:=p) ℓ hℓp:ℕ) : ℂ) * (-s) by ring,
      this]
  rw [Finset.prod_congr rfl hprod_eq,Finset.prod_const,hcard_eq]
omit [IsCMField K] in
lemma v4:
    qt p K ∈ Ideal.primesOver (q0 p) (𝓞 K) :=by
  refine ⟨zetaPrime_isPrime p K,?_⟩
  have:IsCyclotomicExtension {p^ (0+1)} ℚ K:=by
    simpa using (inferInstance:IsCyclotomicExtension {p} ℚ K)
  simpa [qt,q0] using
    (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p:=p) (k:=0)
      (K:=K) (hζ:=IsCyclotomicExtension.zeta_spec (p^ (0+1)) ℚ K))
omit [IsCMField K] in
lemma xj:
    Ideal.primesOver (q0 p) (𝓞 K) = {qt p K} :=by
  classical
  obtain ⟨P,hP⟩ :=
    Set.ncard_eq_one.mp (sE (p:=p) (K:=K))
  have hzeta:qt p K=P:=by
    have hzeta_mem:=v4 (p:=p) (K:=K)
    rw [hP] at hzeta_mem
    simpa using hzeta_mem
  simpa [hzeta] using hP
lemma zg:
    qX p K ∈ Ideal.primesOver (q0 p) (𝓞 ((oMR K))) :=by
  refine ⟨inferInstance,?_⟩
  have:IsCyclotomicExtension {p^ (0+1)} ℚ K:=by
    simpa using (inferInstance:IsCyclotomicExtension {p} ℚ K)
  have hzeta_over: (qt p K).LiesOver (q0 p) :=by
    simpa [qt,q0] using
      (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p:=p) (k:=0)
        (K:=K) (hζ:=IsCyclotomicExtension.zeta_spec (p^ (0+1)) ℚ K))
  rw [Ideal.liesOver_iff,qX,Ideal.under_under]
  exact Ideal.over_def (P:=qt p K) (A:=ℤ) (p:=q0 p)
lemma sb:
    Ideal.primesOver (q0 p) (𝓞 ((oMR K))) = {qX p K} :=by
  classical
  ext PPlus
  constructor
  · intro hPPlus
    have:PPlus.IsPrime:=hPPlus.1
    have:PPlus.LiesOver (q0 p) :=hPPlus.2
    obtain ⟨⟨P,hP_prime,hP_over_PPlus⟩⟩ :=PPlus.nonempty_primesOver (S:=𝓞 K)
    have hP:P ∈ Ideal.primesOver (q0 p) (𝓞 K) :=by
      refine ⟨hP_prime,?_⟩
      exact Ideal.LiesOver.trans (A:=ℤ) (B:=𝓞 ((oMR K))) (C:=𝓞 K)
        (𝔓:=P) (P:=PPlus) (p:=q0 p)
    have hP_eq:P=qt p K:=by
      rw [xj (p:=p) (K:=K)] at hP
      simpa using hP
    have hPPlus_eq:PPlus=qX p K:=by
      simpa [qX,hP_eq] using
        (Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)
    simp [hPPlus_eq]
  · intro hPPlus
    rw [Set.mem_singleton_iff] at hPPlus
    simpa [hPPlus] using zg (p:=p) (K:=K)
lemma uw:
    (Ideal.primesOver (q0 p) (𝓞 ((oMR K)))).ncard=1:=by
  rw [sb (p:=p) (K:=K)]
  simp
lemma xw:
    (qX p K).inertiaDeg ℤ =1:=by
  have hinertia_tower:
      (qt p K).inertiaDeg ℤ =
        (qX p K).inertiaDeg ℤ *
          (qt p K).inertiaDeg (𝓞 ((oMR K))) :=by
    simpa using Ideal.inertiaDeg_tower
      (R:=ℤ) (S:=𝓞 ((oMR K))) (T:=𝓞 K) (q:=qX p K) (r:=qt p K)
  have hzeta_inertia:
      (qt p K).inertiaDeg ℤ =1:=by
    exact s3 (p:=p) (K:=K) (qt p K)
      (v4 (p:=p) (K:=K))
  rw [hzeta_inertia] at hinertia_tower
  exact Nat.eq_one_of_dvd_one <|
    ⟨(qt p K).inertiaDeg (𝓞 ((oMR K))),hinertia_tower⟩
lemma sW (PPlus:Ideal (𝓞 ((oMR K))))
    (hPPlus:PPlus ∈ Ideal.primesOver (q0 p) (𝓞 ((oMR K)))) :
    PPlus.inertiaDeg ℤ =1:=by
  have hPPlus_eq:PPlus=qX p K:=by
    rw [sb (p:=p) (K:=K)] at hPPlus
    simpa using hPPlus
  simpa [hPPlus_eq] using xw (p:=p) (K:=K)
lemma vs {s:ℂ} :
    qm (oMR K) p s=1- (p:ℂ) ^ (-s) :=by
  classical
  unfold qm qb q0
  have hne: (Ideal.span {(p:ℤ)} : Ideal ℤ) ≠ ⊥ :=by
    rw [Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hcoe:=
    IsDedekindDomain.coe_primesOverFinset (p:= (Ideal.span {(p:ℤ)} : Ideal ℤ)) hne
      (𝓞 ((oMR K)))
  have hcard: (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)} : Ideal ℤ)
      (𝓞 ((oMR K)))).card=1:=by
    have hncard: ((Ideal.span {(p:ℤ)}).primesOver (𝓞 ((oMR K)))).ncard=1:=by
      simpa [q0] using uw (p:=p) (K:=K)
    rw [← hcoe] at hncard
    simpa using hncard
  obtain ⟨PPlus,hPPlus⟩ :=Finset.card_eq_one.mp hcard
  rw [hPPlus,Finset.prod_singleton]
  have hPPlus_mem:PPlus ∈ (Ideal.span {(p:ℤ)}).primesOver (𝓞 ((oMR K))) :=by
    rw [← hcoe]
    rw [hPPlus]
    exact Finset.mem_singleton_self PPlus
  have:PPlus.LiesOver (Ideal.span {(p:ℤ)}) :=by
    simpa [q0] using hPPlus_mem.2
  have:PPlus.IsMaximal:=Ideal.isMaximal_of_mem_primesOver (by
    simpa [q0] using hPPlus_mem)
  have habsNorm:Ideal.absNorm PPlus=p^ (1:ℕ) :=by
    rw [← sW (p:=p) (K:=K) PPlus]
    · rw [← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p:ℤ)}) PPlus]
      exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus hp.out
    · simpa [q0] using hPPlus_mem
  rw [habsNorm]
  push_cast
  rw [pow_one]
end KummerCriterion
end
end Module25
-- Source: KummerCriterion.ZetaFactorisation.NumberFieldEulerProduct
section Module26
noncomputable section
open NumberField
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section NumberFieldEulerProduct
variable (L:Type*) [Field L] [NumberField L]
abbrev qQ:Type _ := {I:Ideal (𝓞 L) //I ≠ ⊥}
noncomputable def qe (n:ℕ) : ℕ:=
  Nat.card {I:qQ L //Ideal.absNorm I.1=n}
lemma rC:qe L 0=0:=by
  unfold qe
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I,hI⟩,hnorm⟩
  exact hI (Ideal.absNorm_eq_zero_iff.mp hnorm)
lemma rr:qe L 1=1:=by
  have:Unique {I:qQ L //Ideal.absNorm I.1=1} :=
    { default:= ⟨⟨⊤,by simp⟩,Ideal.absNorm_top⟩
      uniq:=by
        rintro ⟨⟨I,hI⟩,hnorm⟩
        exact Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm))}
  exact Nat.card_unique
lemma yg {m n :ℕ} (hcop:Nat.Coprime m n) :
    qe L (m*n) =
      qe L m*qe L n:=by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.Coprime,Nat.gcd_zero_left] at hcop
    subst hcop
    simp [rC,rr]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.Coprime,Nat.gcd_zero_right] at hcop
    subst hcop
    simp [rC,rr]
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  all_goals rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · classical
    have h_cop_spans: (Ideal.span {(m:𝓞 L)}) ⊔ (Ideal.span {(n:𝓞 L)}) = ⊤ :=by
      rw [← Ideal.isCoprime_iff_sup_eq,Ideal.isCoprime_span_singleton_iff]
      have hZ:IsCoprime (m:ℤ) (n:ℤ) :=Nat.Coprime.isCoprime hcop
      simpa using hZ.map (algebraMap ℤ (𝓞 L))
    have h_mul_sup: ∀ (I:Ideal (𝓞 L)),
        (I ⊔ Ideal.span {(m:𝓞 L)}) * (I ⊔ Ideal.span {(n:𝓞 L)}) =
          I ⊔ Ideal.span {(m:𝓞 L) * (n:𝓞 L)} :=fun I => by
      rw [Ideal.sup_mul,Ideal.mul_sup,Ideal.mul_sup,
        mul_comm (Ideal.span {(m:𝓞 L)}) I,
        Ideal.span_singleton_mul_span_singleton,
        show I *I ⊔ I*Ideal.span {(n:𝓞 L)} ⊔
            (I*Ideal.span {(m:𝓞 L)} ⊔ Ideal.span {(m:𝓞 L) * (n:𝓞 L)}) =
            (I*I ⊔ I*Ideal.span {(n:𝓞 L)} ⊔ I*Ideal.span {(m:𝓞 L)}) ⊔
              Ideal.span {(m:𝓞 L) * (n:𝓞 L)} from by ac_rfl,
        ← Ideal.mul_sup,← Ideal.mul_sup,
        show I ⊔ Ideal.span {(n:𝓞 L)} ⊔ Ideal.span {(m:𝓞 L)} = ⊤ from by
          rw [sup_assoc,sup_comm (Ideal.span {(n:𝓞 L)}) _,h_cop_spans,sup_top_eq],
        Ideal.mul_top]
    have h_sup_absNorm: ∀ (I:Ideal (𝓞 L)),Ideal.absNorm I =m*n →
        I ⊔ Ideal.span {(m:𝓞 L) * (n:𝓞 L)} = I:=fun I hI=> by
      refine le_antisymm (sup_le le_rfl ?_) le_sup_left
      rw [Ideal.span_le,Set.singleton_subset_iff]
      have: ((m*n:ℕ) : 𝓞 L) ∈ I:=by
        rw [← hI]
        exact Ideal.absNorm_mem I
      push_cast at this
      exact this
    have h_cop_lift: ∀ (I:Ideal (𝓞 L)),
        IsCoprime (I ⊔ Ideal.span {(m:𝓞 L)}) (I ⊔ Ideal.span {(n:𝓞 L)}) :=fun I => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = (Ideal.span {(m:𝓞 L)}) ⊔ (Ideal.span {(n:𝓞 L)}) :=h_cop_spans.symm
        _ ≤ (I ⊔ Ideal.span {(m:𝓞 L)}) ⊔ (I ⊔ Ideal.span {(n:𝓞 L)}) :=
            sup_le_sup le_sup_right le_sup_right
    have h_abs_span_nat: ∀ (r:ℕ),Ideal.absNorm (Ideal.span {(r:𝓞 L)}) =
        r^Module.finrank ℤ (𝓞 L) :=fun r => by
      rw [Ideal.absNorm_span_singleton,
        show ((r:𝓞 L)) = algebraMap ℤ (𝓞 L) (r:ℤ) from by push_cast;rfl,
        Algebra.norm_algebraMap_of_basis (Module.finBasis ℤ (𝓞 L))]
      simp
    have h_fwd_norms: ∀ (I:Ideal (𝓞 L)),Ideal.absNorm I =m*n →
        Ideal.absNorm (I ⊔ Ideal.span {(m:𝓞 L)}) = m ∧
          Ideal.absNorm (I ⊔ Ideal.span {(n:𝓞 L)}) = n:=fun I hI=> by
      set a :=Ideal.absNorm (I ⊔ Ideal.span {(m:𝓞 L)}) with ha_def
      set b :=Ideal.absNorm (I ⊔ Ideal.span {(n:𝓞 L)}) with hb_def
      have h_prod: (I ⊔ Ideal.span {(m:𝓞 L)}) * (I ⊔ Ideal.span {(n:𝓞 L)}) = I:=by
        rw [h_mul_sup I,h_sup_absNorm I hI]
      have h_ab:a*b=m*n:=by
        rw [ha_def,hb_def,← map_mul,h_prod,hI]
      have h_a_dvd_md:a ∣ m^Module.finrank ℤ (𝓞 L) :=by
        rw [← h_abs_span_nat m]
        exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
      have h_b_dvd_nd:b ∣ n^Module.finrank ℤ (𝓞 L) :=by
        rw [← h_abs_span_nat n]
        exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
      have h_cop_an:Nat.Coprime a n:=
        (hcop.pow_left _).coprime_dvd_left h_a_dvd_md
      have h_cop_bm:Nat.Coprime b m:=
        (hcop.symm.pow_left _).coprime_dvd_left h_b_dvd_nd
      have h_a_dvd_m:a ∣ m:=
        h_cop_an.dvd_of_dvd_mul_right ⟨b,h_ab.symm⟩
      have h_b_dvd_n:b ∣ n:=
        h_cop_bm.dvd_of_dvd_mul_right ⟨a,by linarith [h_ab,mul_comm a b,mul_comm m n]⟩
      have ha_le:a ≤ m:=Nat.le_of_dvd hm h_a_dvd_m
      have hb_le:b ≤ n:=Nat.le_of_dvd hn h_b_dvd_n
      have ha_ge:m ≤ a:=by
        have h1:m*n ≤ a*n:=by
          calc
            m*n=a*b:=h_ab.symm
            _ ≤ a*n:=Nat.mul_le_mul_left a hb_le
        exact Nat.le_of_mul_le_mul_right h1 hn
      have hb_ge:n ≤ b:=by
        have h1:m*n ≤ m*b:=by
          calc
            m*n=a*b:=h_ab.symm
            _ ≤ m*b:=Nat.mul_le_mul_right b ha_le
        exact Nat.le_of_mul_le_mul_left h1 hm
      exact ⟨Nat.le_antisymm ha_le ha_ge,Nat.le_antisymm hb_le hb_ge⟩
    have h_cop_m_L: ∀ (L':Ideal (𝓞 L)),Ideal.absNorm L'=n →
        IsCoprime (Ideal.span {(m:𝓞 L)}) L':=fun L' hL=> by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = Ideal.span {(m:𝓞 L)} ⊔ Ideal.span {(n:𝓞 L)} :=h_cop_spans.symm
        _ ≤ Ideal.span {(m:𝓞 L)} ⊔ L':=sup_le_sup_left (by
            rw [Ideal.span_le,Set.singleton_subset_iff]
            have: ((n:ℕ) : 𝓞 L) ∈ L':=by
              rw [← hL]
              exact Ideal.absNorm_mem L'
            exact_mod_cast this) _
    have h_cop_n_J: ∀ (J:Ideal (𝓞 L)),Ideal.absNorm J =m →
        IsCoprime (Ideal.span {(n:𝓞 L)}) J :=fun J hJ=> by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = Ideal.span {(n:𝓞 L)} ⊔ Ideal.span {(m:𝓞 L)} :=by
              rw [sup_comm]
              exact h_cop_spans.symm
        _ ≤ Ideal.span {(n:𝓞 L)} ⊔ J:=sup_le_sup_left (by
            rw [Ideal.span_le,Set.singleton_subset_iff]
            have: ((m:ℕ) : 𝓞 L) ∈ J:=by
              rw [← hJ]
              exact Ideal.absNorm_mem J
            exact_mod_cast this) _
    have h_inv_m: ∀ (J L':Ideal (𝓞 L)),Ideal.absNorm J =m → Ideal.absNorm L'=n →
        J*L' ⊔ Ideal.span {(m:𝓞 L)} = J:=fun J L' hJ hL=> by
      have h_cop_mL_sup:Ideal.span {(m:𝓞 L)} ⊔ L'= ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp (h_cop_m_L L' hL)
      refine le_antisymm (sup_le Ideal.mul_le_left ?_) ?_
      · rw [Ideal.span_le,Set.singleton_subset_iff]
        have: ((m:ℕ) : 𝓞 L) ∈ J:=by
          rw [← hJ]
          exact Ideal.absNorm_mem J
        exact_mod_cast this
      · calc
          J=J* ⊤ := (Ideal.mul_top J).symm
          _=J* (Ideal.span {(m:𝓞 L)} ⊔ L') :=by rw [h_cop_mL_sup]
          _=J*Ideal.span {(m:𝓞 L)} ⊔ J*L':=Ideal.mul_sup _ _ _
          _ ≤ Ideal.span {(m:𝓞 L)} ⊔ J*L':=sup_le_sup_right Ideal.mul_le_right _
          _=J*L' ⊔ Ideal.span {(m:𝓞 L)} :=sup_comm _ _
    have h_inv_n: ∀ (J L':Ideal (𝓞 L)),Ideal.absNorm J =m → Ideal.absNorm L'=n →
        J*L' ⊔ Ideal.span {(n:𝓞 L)} = L':=fun J L' hJ hL=> by
      have h_cop_nJ_sup:Ideal.span {(n:𝓞 L)} ⊔ J= ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp (h_cop_n_J J hJ)
      refine le_antisymm (sup_le Ideal.mul_le_right ?_) ?_
      · rw [Ideal.span_le,Set.singleton_subset_iff]
        have: ((n:ℕ) : 𝓞 L) ∈ L':=by
          rw [← hL]
          exact Ideal.absNorm_mem L'
        exact_mod_cast this
      · calc
          L'= ⊤ *L':= (Ideal.top_mul L').symm
          _= (Ideal.span {(n:𝓞 L)} ⊔ J) * L':=by rw [h_cop_nJ_sup]
          _=Ideal.span {(n:𝓞 L)} * L' ⊔ J*L':=Ideal.sup_mul _ _ _
          _ ≤ Ideal.span {(n:𝓞 L)} ⊔ J*L':=sup_le_sup_right Ideal.mul_le_left _
          _=J*L' ⊔ Ideal.span {(n:𝓞 L)} :=sup_comm _ _
    let fwd: {I:qQ L //Ideal.absNorm I.1=m*n} →
        {J:qQ L //Ideal.absNorm J.1=m} ×
          {L':qQ L //Ideal.absNorm L'.1=n} :=
      fun ⟨⟨I,hI_ne⟩,hI_norm⟩ =>
        ⟨⟨⟨I ⊔ Ideal.span {(m:𝓞 L)},fun h => hI_ne (by
            have:I ≤ I ⊔ Ideal.span {(m:𝓞 L)} :=le_sup_left
            rw [h,le_bot_iff] at this
            exact this)⟩,
          (h_fwd_norms I hI_norm).1⟩,
         ⟨⟨I ⊔ Ideal.span {(n:𝓞 L)},fun h => hI_ne (by
            have:I ≤ I ⊔ Ideal.span {(n:𝓞 L)} :=le_sup_left
            rw [h,le_bot_iff] at this
            exact this)⟩,
          (h_fwd_norms I hI_norm).2⟩⟩
    let bwd: {J:qQ L //Ideal.absNorm J.1=m} ×
        {L':qQ L //Ideal.absNorm L'.1=n} →
        {I:qQ L //Ideal.absNorm I.1=m*n} :=
      fun ⟨⟨⟨J,hJ_ne⟩,hJ_norm⟩,⟨⟨L',hL_ne⟩,hL_norm⟩⟩ =>
        ⟨⟨J*L',fun h => by
            rcases Ideal.mul_eq_bot.mp h with h1 | h1
            · exact hJ_ne h1
            · exact hL_ne h1⟩,
         by rw [map_mul,hJ_norm,hL_norm]⟩
    have h_equiv:
        {I:qQ L //Ideal.absNorm I.1=m*n} ≃
          {J:qQ L //Ideal.absNorm J.1=m} ×
            {L':qQ L //Ideal.absNorm L'.1=n} :=
      { toFun:=fwd
        invFun:=bwd
        left_inv:=fun ⟨⟨I,hI_ne⟩,hI_norm⟩ => by
          simp only [fwd,bwd]
          refine Subtype.ext (Subtype.ext ?_)
          simp only
          rw [h_mul_sup,h_sup_absNorm I hI_norm]
        right_inv:=fun ⟨⟨⟨J,hJ_ne⟩,hJ_norm⟩,⟨⟨L',hL_ne⟩,hL_norm⟩⟩ => by
          simp only [fwd,bwd]
          refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
          · exact h_inv_m J L' hJ_norm hL_norm
          · exact h_inv_n J L' hJ_norm hL_norm}
    unfold qe
    rw [Nat.card_congr h_equiv,Nat.card_prod]
  · interval_cases n
    simp [rr]
  · interval_cases m
    simp [rr]
  · interval_cases m
    interval_cases n
    simp [rr]
lemma wO {s:ℂ} (hs:1 < s.re) :
    NumberField.dedekindZeta L s=
      ∑' n :ℕ,(qe L n:ℂ) * (n:ℂ) ^ (-s) :=by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n => ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [↓reduceIte]
    rw [rC]
    push_cast
    rw [Complex.zero_cpow (by
      intro h
      have hs_ne:s ≠ 0:=by
        intro hs_zero
        rw [hs_zero,Complex.zero_re] at hs
        exact absurd hs (by norm_num)
      exact hs_ne (neg_eq_zero.mp h)),mul_zero]
  · simp only [hn.ne',↓reduceIte]
    have hn_ne: (n:ℂ) ≠ 0:=by exact_mod_cast hn.ne'
    rw [Complex.cpow_neg,div_eq_mul_inv]
    congr 1
    unfold qe
    have hequiv: {I:Ideal (𝓞 L) //Ideal.absNorm I =n} ≃
        {I:qQ L //Ideal.absNorm I.1=n} :=by
      refine {
        toFun:=fun ⟨I,hI⟩ => ⟨⟨I,?_⟩,hI⟩
        invFun:=fun ⟨⟨I,_⟩,hI⟩ => ⟨I,hI⟩
        left_inv:=fun _ => rfl
        right_inv:=fun _ => rfl}
      intro h
      rw [h] at hI
      rw [Ideal.absNorm_bot] at hI
      omega
    exact (Nat.card_congr hequiv).symm ▸ rfl
lemma sR (α:Type*) [Fintype α] [Finite α] {z:ℂ}
    (hz: ‖z‖ < 1) :
    Summable (fun n :ℕ=> (Fintype.card (Sym α n) : ℂ) * z^n) ∧
      (∑' n :ℕ,(Fintype.card (Sym α n) : ℂ) * z^n) =
        ((1-z)⁻¹) ^ Fintype.card α :=by
  by_cases hα:Fintype.card α =0
  · have:IsEmpty α :=Fintype.card_eq_zero_iff.mp hα
    let term:ℕ → ℂ:=fun n => (Fintype.card (Sym α n) : ℂ) * z^n
    have hzero: ∀ n ≠ 0,term n =0:=by
      intro n hn
      cases n with
      | zero=> contradiction
      | succ n => simp [term,Sym.card_sym_eq_multichoose,Nat.multichoose_zero_succ]
    have hsupport: {n:ℕ | term n ≠ 0}.Finite:=by
      refine Set.Finite.subset ({0} : Set ℕ).toFinite ?_
      intro n hn
      by_contra hne
      exact hn (hzero n hne)
    constructor
    · exact summable_of_hasFiniteSupport hsupport
    · have hcard0:Fintype.card (Sym α 0) = 1:=by
        rw [Sym.card_sym_eq_multichoose,Nat.multichoose_zero_right]
      simpa [term,hcard0,hα] using tsum_eq_single 0 hzero
  · obtain ⟨k,hk⟩ :=Nat.exists_eq_succ_of_ne_zero hα
    constructor
    · refine (summable_choose_mul_geometric_of_norm_lt_one k hz).congr ?_
      intro n
      rw [Sym.card_sym_eq_choose,hk,Nat.succ_add_sub_one,Nat.add_comm k n,
        Nat.choose_symm_add]
    · calc
        ∑' n :ℕ,(Fintype.card (Sym α n) : ℂ) * z^n
            = ∑' n :ℕ,((n+k).choose k :ℂ) * z^n:=by
                apply tsum_congr
                intro n
                rw [Sym.card_sym_eq_choose,hk,Nat.succ_add_sub_one,Nat.add_comm k n,
                  Nat.choose_symm_add]
        _=1/ (1-z) ^ (k+1) :=tsum_choose_mul_geometric_of_norm_lt_one k hz
        _= ((1-z)⁻¹) ^ (k+1) :=by simp [one_div]
        _= ((1-z)⁻¹) ^ Fintype.card α :=by simp [hk]
lemma zD (α:Type*) [Fintype α] [Finite α] {z:ℂ} (hz: ‖z‖ < 1) :
    (∑' n :ℕ,(Fintype.card (Sym α n) : ℂ) * z^n) = ((1-z)⁻¹) ^ Fintype.card α :=
  (sR α hz).2
lemma wC {s:ℂ} (hs:1 < s.re) :
    Summable fun n :ℕ=> ‖(qe L n:ℂ) * (n:ℂ) ^ (-s)‖ :=by
  classical
  have h_finite: ∀ (b:ℕ),{I:qQ L | Ideal.absNorm I.1=b}.Finite:=fun b => by
    refine Set.Finite.preimage (f:=fun I :qQ L => I.1) ?_
      (Ideal.finite_setOfPred_absNorm_eq b)
    intro _ _ _ _;exact Subtype.ext
  have h_sum_card: ∀ n:ℕ,∑ k ∈ Finset.Icc 1 n,qe L k=
      Nat.card {I:qQ L //Ideal.absNorm I.1 ≤ n} :=fun n => by
    have key:=Finset.card_preimage_eq_sum_card_image_eq (f:=fun I :qQ L =>
      Ideal.absNorm I.1) (s:=Finset.Icc 1 n) (fun b _=> h_finite b)
    rw [show ((fun I :qQ L => Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I:qQ L | Ideal.absNorm I.1 ≤ n} from by
      ext ⟨I,hI⟩
      simp only [Set.mem_preimage,Finset.coe_Icc,Set.mem_Icc,Set.mem_ofPred_eq]
      exact ⟨fun h => h.2,fun h =>
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI),h⟩⟩] at key
    exact key.symm
  have h_bigO: (fun n :ℕ=> ∑ k ∈ Finset.Icc 1 n,(qe L k:ℝ))
      =O[Filter.atTop] (fun n :ℕ=> (n:ℝ) ^ (1:ℝ)) :=by
    have h_card_bridge: ∀ n:ℕ,
        Nat.card {I:qQ L //Ideal.absNorm I.1 ≤ n} =
        Nat.card {I: (Ideal (𝓞 L))⁰// ((Ideal.absNorm I.1:ℕ) : ℝ) ≤ (n:ℝ)} :=
      fun n =>
      Nat.card_congr
        { toFun:=fun ⟨⟨I,hI⟩,hn⟩ =>
            ⟨⟨I,mem_nonZeroDivisors_of_ne_zero hI⟩,by exact_mod_cast hn⟩
          invFun:=fun ⟨⟨I,hI⟩,hn⟩ =>
            ⟨⟨I,mem_nonZeroDivisors_iff_ne_zero.mp hI⟩,by exact_mod_cast hn⟩
          left_inv:=fun _ => rfl
          right_inv:=fun _ => rfl}
    refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
      (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
        tendsto_natCast_atTop_atTop).congr' ?_)
    filter_upwards with n
    simp only [Function.comp_apply,Real.rpow_one]
    rw [show (∑ k ∈ Finset.Icc 1 n,(qe L k:ℝ)) =
        ((∑ k ∈ Finset.Icc 1 n,qe L k:ℕ) : ℝ) from by push_cast;rfl,
      h_sum_card n,h_card_bridge n]
    push_cast
    rfl
  have h_lss:LSeriesSummable (fun n :ℕ=> ((qe L n:ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f:=fun n => (qe L n:ℝ))
      h_bigO (fun _ => Nat.cast_nonneg _) zero_le_one (by exact_mod_cast hs)
  have h_term_eq:LSeries.term (fun n :ℕ=> ((qe L n:ℝ) : ℂ)) s =
      fun n => (qe L n:ℂ) * (n:ℂ) ^ (-s) :=by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [rC]
    · show ((qe L n:ℝ) : ℂ) / (n:ℂ) ^ s=_
      rw [Complex.cpow_neg,← div_eq_mul_inv]
      push_cast
      rfl
  exact (h_term_eq ▸ h_lss:
    Summable fun n => (qe L n:ℂ) * (n:ℂ) ^ (-s)).norm
lemma sO {s:ℂ} (hs:1 < s.re) :
    NumberField.dedekindZeta L s=
      ∏' q :Nat.Primes,
        (∑' k :ℕ,(qe L ((q:ℕ) ^ k) : ℂ) *
          ((((q:ℕ) ^ k:ℕ) : ℂ) ^ (-s))) :=by
  let f :ℕ → ℂ:=fun n => (qe L n:ℂ) * (n:ℂ) ^ (-s)
  have hf_zero:f 0=0:=by simp [f,rC L]
  have hf_one:f 1=1:=by simp [f,rr L]
  have hf_mul: ∀ {m n :ℕ},m.Coprime n → f (m*n) = f m *f n:=fun {m n} hcop=> by
    simp only [f]
    rw [yg L hcop,Nat.cast_mul,Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  have hf_sum:Summable fun n => ‖f n‖ :=wC L hs
  rw [wO L hs,
    ← EulerProduct.eulerProduct_tprod hf_one hf_mul hf_sum hf_zero]
end NumberFieldEulerProduct
end KummerCriterion
end
end Module26
-- Source: KummerCriterion.ZetaFactorisation.EulerProduct
section Module27
noncomputable section
open NumberField
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section ZetaFactorisation
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
lemma zc (k:ℕ) :
    qe K (p^k) = 1:=by
  classical
  have hne: (q0 p) ≠ ⊥ :=by
    rw [q0,Ne,Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have: (q0 p).IsMaximal:=Int.ideal_span_isMaximal_of_prime p
  have hcoe:=IsDedekindDomain.coe_primesOverFinset (p:=q0 p) hne (𝓞 K)
  have hcard: (qb K p).card=1:=by
    have hncard: (Ideal.primesOver (q0 p) (𝓞 K)).ncard=1:=
      sE (p:=p) (K:=K)
    rw [← hcoe,Set.ncard_coe_finset] at hncard
    simpa [qb] using hncard
  obtain ⟨P,hP⟩ :=Finset.card_eq_one.mp hcard
  have hPmem:P ∈ Ideal.primesOver (q0 p) (𝓞 K) :=by
    have hPfin:P ∈ qb K p:=by
      rw [hP]
      exact Finset.mem_singleton_self P
    exact (qs (K:=K) (ℓ:=p)).1 hPfin
  have hP_ne:P ≠ ⊥ :=by
    intro hP_bot
    have hunder:=hPmem.2
    rw [Ideal.liesOver_iff,Ideal.under_def,hP_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 K))
      (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))] at hunder
    exact hne hunder
  have:P.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hP_ne hPmem.1
  have:P.LiesOver (Ideal.span {(p:ℤ)}) :=by
    simpa [q0] using hPmem.2
  have habsNormP:Ideal.absNorm P =p:=by
    calc
      Ideal.absNorm P =p^ (1:ℕ) :=by
        rw [← s3 (p:=p) (K:=K) P hPmem,
          ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p:ℤ)}) P]
        exact Ideal.absNorm_eq_pow_inertiaDeg' P hp.out
      _=p:=by simp
  have:Unique {I:qQ K //Ideal.absNorm I.1=p^k} :=
    { default:= ⟨⟨P^k,pow_ne_zero k hP_ne⟩,by
          rw [map_pow,habsNormP]⟩
      uniq:=by
        rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
        let m :ℕ:=Multiset.count P (UniqueFactorizationMonoid.normalizedFactors I)
        obtain ⟨Q,hPQ,hIeq⟩ :=Ideal.eq_prime_pow_mul_coprime hI_ne P
        have hQ_top:Q= ⊤ :=by
          by_contra hQ_ne_top
          have hQ_ne:Q ≠ ⊥ :=by
            intro hQ_bot
            apply hI_ne
            rw [hIeq,hQ_bot,Ideal.mul_bot]
          have hnf_ne:UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 :=by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne,hnf]
            simp
          obtain ⟨R,hRmem⟩ :=Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac:= (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime:R.IsPrime:=hRfac.1
          have hQ_le_R:Q ≤ R:=hRfac.2
          have hR_ne:R ≠ ⊥ :=fun hR_bot=>
            hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          have:NeZero R := ⟨hR_ne⟩
          have hI_le_Q:I ≤ Q:=by
            rw [hIeq]
            exact Ideal.mul_le_right
          have hR_dvd_I:Ideal.absNorm R ∣ p ^k:=by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd:Ideal.absNorm (Ideal.under ℤ R) ∣ p^k:=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime: (Ideal.absNorm (Ideal.under ℤ R)).Prime:=Nat.absNorm_under_prime R
          have hunder_dvd_p:Ideal.absNorm (Ideal.under ℤ R) ∣ p:=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_p:Ideal.absNorm (Ideal.under ℤ R) = p:=
            (Nat.prime_dvd_prime_iff_eq hunder_prime hp.out).1 hunder_dvd_p
          have hunder_eq_span_p:Ideal.under ℤ R=Ideal.span {(p:ℤ)} :=by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]
            simp [hunder_eq_p]
          have hR_lies:R.LiesOver (Ideal.span {(p:ℤ)}) :=by
            rw [Ideal.liesOver_iff,hunder_eq_span_p]
          have hRmem_p:R ∈ Ideal.primesOver (q0 p) (𝓞 K) :=by
            refine ⟨hRprime,?_⟩
            simpa [q0] using hR_lies
          have hRmem_fin:R ∈ qb K p:=
            (qs (K:=K) (ℓ:=p)).2 hRmem_p
          have hR_eq_P:R=P:=by
            rw [hP] at hRmem_fin
            exact Finset.mem_singleton.mp hRmem_fin
          have hQ_le_P:Q ≤ P:=by
            simpa [hR_eq_P] using hQ_le_R
          have htop_le_P: (⊤ : Ideal (𝓞 K)) ≤ P:=by
            calc
              ⊤ = P ⊔ Q:=hPQ.symm
              _ ≤ P:=sup_le le_rfl hQ_le_P
          exact hPmem.1.ne_top (top_le_iff.mp htop_le_P)
        have hI_pow:I=P^m:=by
          simpa [m,hQ_top] using hIeq
        have hm:m=k:=by
          apply Nat.pow_right_injective hp.out.one_lt
          calc
            p^m=Ideal.absNorm I :=by
              rw [hI_pow,map_pow,habsNormP]
            _=p^k:=hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m,hm] using hI_pow}
  exact Nat.card_unique
lemma r3
    {q:Nat.Primes} {I:Ideal (𝓞 K)} (hI_ne:I ≠ ⊥)
    {k:ℕ} (hI_norm:Ideal.absNorm I = (q:ℕ) ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆ qb K (q:ℕ) :=by
  classical
  have:Fact (q:ℕ).Prime:= ⟨q.2⟩
  intro P hP
  have hP_mem:P ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.mem_toFinset.1 hP
  have hP_fac:= (Ideal.mem_normalizedFactors_iff hI_ne).1 hP_mem
  have hP_prime:P.IsPrime:=hP_fac.1
  have hI_le_P:I ≤ P:=hP_fac.2
  have hP_ne:P ≠ ⊥ :=fun hP_bot=>
    hI_ne (le_bot_iff.mp (hP_bot ▸ hI_le_P))
  have:NeZero P := ⟨hP_ne⟩
  have hP_dvd:Ideal.absNorm P ∣ (q:ℕ) ^ k:=by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_P
  have hunder_dvd:Ideal.absNorm (Ideal.under ℤ P) ∣ (q:ℕ) ^ k:=
    dvd_trans (Int.absNorm_under_dvd_absNorm P) hP_dvd
  have hunder_prime: (Ideal.absNorm (Ideal.under ℤ P)).Prime:=Nat.absNorm_under_prime P
  have hunder_dvd_q:Ideal.absNorm (Ideal.under ℤ P) ∣ (q:ℕ) :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q:Ideal.absNorm (Ideal.under ℤ P) = (q:ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime q.2).1 hunder_dvd_q
  have hunder_eq_span_q:Ideal.under ℤ P=Ideal.span {((q:ℕ) : ℤ)} :=by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ P)]
    simp [hunder_eq_q]
  have hP_lies:P.LiesOver (Ideal.span {((q:ℕ) : ℤ)}) :=by
    rw [Ideal.liesOver_iff,hunder_eq_span_q]
  have hP_over:P ∈ Ideal.primesOver (q0 (q:ℕ)) (𝓞 K) :=by
    refine ⟨hP_prime,?_⟩
    simpa [q0] using hP_lies
  exact (qs (K:=K) (ℓ:= (q:ℕ))).2 hP_over
lemma qL
    {q:Nat.Primes} [Fact (q:ℕ).Prime] (hq: (q:ℕ) ≠ p) {P:Ideal (𝓞 K)}
    (hP:P ∈ qb K (q:ℕ)) :
    Ideal.absNorm P = (q:ℕ) ^ q4 (p:=p) (q:ℕ) hq:=by
  classical
  have hP_over:P ∈ Ideal.primesOver (q0 (q:ℕ)) (𝓞 K) :=
    (qs (K:=K) (ℓ:= (q:ℕ))).1 hP
  have:P.IsPrime:=hP_over.1
  have:P.LiesOver (Ideal.span {((q:ℕ) : ℤ)}) :=by
    simpa [q0] using hP_over.2
  have:P.IsMaximal:=Ideal.IsMaximal.of_liesOver_isMaximal P (Ideal.span {((q:ℕ) : ℤ)})
  rw [← rv p K hq P hP_over,
    ← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {((q:ℕ) : ℤ)}) P]
  exact Ideal.absNorm_eq_pow_inertiaDeg' P q.2
lemma rs
    {q:Nat.Primes} [Fact (q:ℕ).Prime] (hq: (q:ℕ) ≠ p)
    {I:Ideal (𝓞 K)} (hI_ne:I ≠ ⊥)
    {k:ℕ} (hI_norm:Ideal.absNorm I = (q:ℕ) ^ k) :
    q4 (p:=p) (q:ℕ) hq*
        (UniqueFactorizationMonoid.normalizedFactors I).card=k:=by
  classical
  set d :=q4 (p:=p) (q:ℕ) hq with hd
  set m :=UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset:m.toFinset ⊆ qb K (q:ℕ) :=by
    simpa [hm] using
      r3 (K:=K) hI_ne
        hI_norm
  have hsum_count: ∑ P ∈ qb K (q:ℕ),m.count P =m.card:=
    Multiset.sum_count_eq_card fun P hP=> hsubset (Multiset.mem_toFinset.2 hP)
  have hnorm_factors:Ideal.absNorm m.prod= (q:ℕ) ^ (d*m.card) :=by
    rw [Finset.prod_multiset_count_of_subset m (qb K (q:ℕ)) hsubset,
      map_prod]
    calc
      ∏ P ∈ qb K (q:ℕ),Ideal.absNorm (P^m.count P)
          = ∏ P ∈ qb K (q:ℕ),((q:ℕ) ^ d) ^ m.count P :=by
              apply Finset.prod_congr rfl
              intro P hP
              rw [map_pow]
              rw [qL
                (p:=p) (K:=K) hq hP,hd]
      _= (q:ℕ) ^ (d* ∑ P ∈ qb K (q:ℕ),m.count P) :=by
              rw [Finset.prod_pow_eq_pow_sum]
              simp [Nat.pow_mul]
      _= (q:ℕ) ^ (d*m.card) :=by rw [hsum_count]
  have hpow: (q:ℕ) ^ (d*m.card) = (q:ℕ) ^ k:=by
    calc
      (q:ℕ) ^ (d*m.card) = Ideal.absNorm m.prod:=hnorm_factors.symm
      _=Ideal.absNorm I :=by rw [hm,Ideal.prod_normalizedFactors_eq_self hI_ne]
      _= (q:ℕ) ^ k:=hI_norm
  exact Nat.pow_right_injective q.2.one_lt hpow
lemma vJ
    {q:Nat.Primes} [Fact (q:ℕ).Prime] (hq: (q:ℕ) ≠ p) {k:ℕ}
    (hk: ¬ q4 (p:=p) (q:ℕ) hq ∣ k) :
    qe K ((q:ℕ) ^ k) = 0:=by
  unfold qe
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
  apply hk
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card,?_⟩
  simpa [mul_comm] using
    rs
      (p:=p) (K:=K) hq hI_ne hI_norm |>.symm
lemma ua
    {q:Nat.Primes} [Fact (q:ℕ).Prime] (hq: (q:ℕ) ≠ p) (n:ℕ) :
    qe K
        ((q:ℕ) ^ (q4 (p:=p) (q:ℕ) hq*n)) =
      Fintype.card (Sym {P:Ideal (𝓞 K) //P ∈ qb K (q:ℕ)} n) :=by
  classical
  set d :=q4 (p:=p) (q:ℕ) hq with hd
  let α :Type _ := {P:Ideal (𝓞 K) //P ∈ qb K (q:ℕ)}
  let β :Type _ := {I:qQ K //Ideal.absNorm I.1= (q:ℕ) ^ (d*n)}
  have hd_pos:0 < d:=by
    rw [hd]
    exact orderOf_pos _
  have hpmap_val:
      ∀ {m:Multiset (Ideal (𝓞 K))}
        (H: ∀ P,P ∈ m → P ∈ qb K (q:ℕ)),
        (Multiset.pmap (fun P hP=> (⟨P,hP⟩ : α)) m H).map Subtype.val=m:=by
    intro m H
    rw [Multiset.map_pmap,Multiset.pmap_eq_map,Multiset.map_id']
  let toSym:β → Sym α n:=fun ⟨⟨I,hI_ne⟩,hI_norm⟩ =>
    let m :=UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ P,P ∈ m → P ∈ qb K (q:ℕ) :=by
      intro P hP
      have hsubset:m.toFinset ⊆ qb K (q:ℕ) :=by
        simpa [m] using
          r3 (K:=K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hP)
    have hm_card:m.card=n:=by
      have hmul:d*m.card=d*n:=by
        simpa [m,hd] using
          rs
            (p:=p) (K:=K) hq hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hd_pos hmul
    ⟨Multiset.pmap (fun P hP=> (⟨P,hP⟩ : α)) m H,by
      simp [hm_card]⟩
  let ofSym:Sym α n → β:=fun s =>
    let m :Multiset (Ideal (𝓞 K)) :=s.1.map Subtype.val
    have hm_card:m.card=n:=by
      simp [m]
    have hm_subset:m.toFinset ⊆ qb K (q:ℕ) :=by
      intro P hP
      rcases Multiset.mem_toFinset.1 hP with hP
      rcases Multiset.mem_map.1 hP with ⟨Q,hQ,rfl⟩
      exact Q.2
    have hm_prime: ∀ P ∈ m,Prime P :=by
      intro P hP
      rcases Multiset.mem_map.1 hP with ⟨Q,hQ,rfl⟩
      have hQ_ne: (Q:Ideal (𝓞 K)) ≠ ⊥ :=by
        intro hQ_bot
        have hQ_norm:=
          qL
            (p:=p) (K:=K) hq Q.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQ_bot,← hd] at hQ_norm
        exact pow_ne_zero d q.2.ne_zero hQ_norm.symm
      exact (Ideal.prime_iff_isPrime hQ_ne).2
        ((qs (K:=K) (ℓ:= (q:ℕ))).1 Q.2).1
    have hm_prod_ne:m.prod ≠ ⊥ :=Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm:Ideal.absNorm m.prod= (q:ℕ) ^ (d*n) :=by
      have hsum_count: ∑ P ∈ qb K (q:ℕ),m.count P =m.card:=
        Multiset.sum_count_eq_card fun P hP=> hm_subset (Multiset.mem_toFinset.2 hP)
      rw [Finset.prod_multiset_count_of_subset m (qb K (q:ℕ)) hm_subset,
        map_prod]
      calc
        ∏ P ∈ qb K (q:ℕ),Ideal.absNorm (P^m.count P)
            = ∏ P ∈ qb K (q:ℕ),((q:ℕ) ^ d) ^ m.count P :=by
                apply Finset.prod_congr rfl
                intro P hP
                rw [map_pow]
                rw [qL
                  (p:=p) (K:=K) hq hP,hd]
        _= (q:ℕ) ^ (d* ∑ P ∈ qb K (q:ℕ),m.count P) :=by
                rw [Finset.prod_pow_eq_pow_sum]
                simp [Nat.pow_mul]
        _= (q:ℕ) ^ (d*m.card) :=by rw [hsum_count]
        _= (q:ℕ) ^ (d*n) :=by rw [hm_card]
    ⟨⟨m.prod,hm_prod_ne⟩,hm_norm⟩
  have htoSym_map_val: ∀ b:β,
      (toSym b).1.map Subtype.val=UniqueFactorizationMonoid.normalizedFactors b.1.1:=by
    rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
    dsimp [toSym]
    let m :=UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ P,P ∈ m → P ∈ qb K (q:ℕ) :=by
      intro P hP
      have hsubset:m.toFinset ⊆ qb K (q:ℕ) :=by
        simpa [m] using
          r3 (K:=K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hP)
    change (Multiset.pmap (fun P hP=> (⟨P,hP⟩ : α)) m H).map Subtype.val=m
    rw [hpmap_val H]
  have hofSym_nfactors:
      ∀ s :Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1=s.1.map Subtype.val:=by
    intro s
    dsimp [ofSym]
    let m :Multiset (Ideal (𝓞 K)) :=s.1.map Subtype.val
    have hm_prime: ∀ P ∈ m,Prime P :=by
      intro P hP
      rcases Multiset.mem_map.1 hP with ⟨Q,hQ,rfl⟩
      have hQ_ne: (Q:Ideal (𝓞 K)) ≠ ⊥ :=by
        intro hQ_bot
        have hQ_norm:=
          qL
            (p:=p) (K:=K) hq Q.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQ_bot,← hd] at hQ_norm
        exact pow_ne_zero d q.2.ne_zero hQ_norm.symm
      exact (Ideal.prime_iff_isPrime hQ_ne).2
        ((qs (K:=K) (ℓ:= (q:ℕ))).1 Q.2).1
    change UniqueFactorizationMonoid.normalizedFactors m.prod=m
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hm_prime
  have hleft:Function.LeftInverse ofSym toSym:=by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod=b.1.1
    rw [htoSym_map_val,Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright:Function.RightInverse ofSym toSym:=by
    intro s
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  unfold qe
  simpa [β,α,hd,Nat.card_eq_fintype_card] using
    Nat.card_congr (⟨toSym,ofSym,hleft,hright⟩ : β ≃ Sym α n)
lemma w6 {s:ℂ} (hs:1 < s.re) :
    (∑' k :ℕ,(qe K (p^k) : ℂ) *
      (((p^k:ℕ) : ℂ) ^ (-s))) =
      (qm K p s)⁻¹:=by
  have hnorm: ‖(p:ℂ) ^ (-s)‖ < 1:=by
    have hle: ‖(p:ℂ) ^ (-s)‖ ≤ 1/2:=
      Complex.norm_prime_cpow_le_one_half ⟨p,hp.out⟩ hs
    exact hle.trans_lt (by norm_num)
  rw [wv]
  trans ∑' k :ℕ,((p:ℂ) ^ (-s)) ^ k
  · refine tsum_congr fun k => ?_
    rw [zc (p:=p) (K:=K) k]
    simp only [Nat.cast_one,one_mul]
    rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul p k (-s),mul_comm,
      Complex.cpow_mul_nat]
  · simpa using tsum_geometric_of_norm_lt_one hnorm
lemma wN
    (p:ℕ) [Fact p.Prime] (K:Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] {q:Nat.Primes} {s:ℂ} (hs:1 < s.re) :
    (∑' k :ℕ,(qe K ((q:ℕ) ^ k) : ℂ) *
      (((q:ℕ) ^ k:ℕ) : ℂ) ^ (-s)) =
      (qm K (q:ℕ) s)⁻¹:=by
  have:Fact (q:ℕ).Prime:= ⟨q.2⟩
  by_cases hq: (q:ℕ) = p
  · have hq':q= ⟨p,Fact.out⟩ :=by
      apply Subtype.ext
      simpa using hq
    subst hq'
    simpa using w6 (p:=p) (K:=K) hs
  · classical
    set d :=q4 (p:=p) (q:ℕ) hq with hd
    let α :Type _ := {P:Ideal (𝓞 K) //P ∈ qb K (q:ℕ)}
    let f :ℕ → ℂ:=fun k =>
      (qe K ((q:ℕ) ^ k) : ℂ) * ((((q:ℕ) ^ k:ℕ) : ℂ) ^ (-s))
    let g :ℕ → ℂ:=fun n =>
      (qe K ((q:ℕ) ^ (d*n)) : ℂ) *
        ((((q:ℕ) ^ (d*n) : ℕ) : ℂ) ^ (-s))
    let z :ℂ:= (q:ℂ) ^ (-((d:ℂ) * s))
    have hd_pos:0 < d:=by
      rw [hd]
      exact orderOf_pos _
    have hs_d:1 < (((d:ℂ) * s).re) :=by
      rw [Complex.mul_re]
      simp
      have hd_ge: (1:ℝ) ≤ d:=by
        exact_mod_cast Nat.succ_le_of_lt hd_pos
      nlinarith [hs,hd_ge]
    have hz: ‖z‖ < 1:=by
      have hle: ‖z‖ ≤ 1/2:=by
        dsimp [z]
        exact Complex.norm_prime_cpow_le_one_half ⟨q,q.2⟩ hs_d
      exact hle.trans_lt (by norm_num)
    have hg_term: ∀ n:ℕ,g n= (Fintype.card (Sym α n) : ℂ) * z^n:=by
      intro n
      dsimp [g,z]
      rw [show qe K ((q:ℕ) ^ (d*n)) = Fintype.card (Sym α n) by
        simpa [α,hd] using
          ua
            (p:=p) (K:=K) hq n]
      rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul (q:ℕ) (d*n) (-s)]
      have hexp: (((d*n:ℕ) : ℂ) * (-s)) = (-((d:ℂ) * s)) * n:=by
        push_cast
        ring
      rw [hexp,Complex.cpow_mul_nat]
    have hg_eq:g=fun n :ℕ=> (Fintype.card (Sym α n) : ℂ) * z^n:=funext hg_term
    have hg_hasSum0:HasSum (fun n :ℕ=> (Fintype.card (Sym α n) : ℂ) * z^n)
        (((1-z)⁻¹) ^ Fintype.card α) :=by
      rw [← zD α hz]
      exact (sR α hz).1.hasSum
    have hg_hasSum:HasSum g (((1-z)⁻¹) ^ Fintype.card α) :=by
      simpa [hg_eq] using hg_hasSum0
    have hf_hasSum:HasSum f (((1-z)⁻¹) ^ Fintype.card α) :=by
      refine (hasSum_iff_hasSum_of_ne_zero_bij
        (f:=f) (g:=g) (i:=fun x :Function.support g => d *x.1) ?_ ?_ ?_).2 hg_hasSum
      · intro x y hxy
        exact Subtype.ext <| Nat.eq_of_mul_eq_mul_left hd_pos hxy
      · intro k hk
        have hk_mult:qe K ((q:ℕ) ^ k) ≠ 0:=fun hk_zero=>
          hk (by simp [f,hk_zero])
        have hk_dvd:d ∣ k:=by
          by_contra hk_ndvd
          exact hk_mult <|
            vJ (p:=p) (K:=K) hq hk_ndvd
        obtain ⟨n,rfl⟩ :=hk_dvd
        refine ⟨⟨n,?_⟩,rfl⟩
        simpa [f,g,mul_comm] using hk
      · intro x
        simp [f,g,mul_comm]
    have hcard_finset:
        (qb K (q:ℕ)).card=rd (p:=p) (q:ℕ) hq:=by
      have: (q0 (q:ℕ)).IsMaximal:=
        Int.ideal_span_isMaximal_of_prime (q:ℕ)
      have hne: (q0 (q:ℕ)) ≠ ⊥ :=by
        simp [q0,q.2.ne_zero]
      have hcoe:=
        IsDedekindDomain.coe_primesOverFinset (p:=q0 (q:ℕ)) hne (𝓞 K)
      have h1:=u6 (p:=p) (K:=K) hq
      rw [← hcoe,Set.ncard_coe_finset] at h1
      exact h1
    have hα_card:Fintype.card α =rd (p:=p) (q:ℕ) hq:=by
      calc
        Fintype.card α = (qb K (q:ℕ)).card:=
          Fintype.card_of_finset' (qb K (q:ℕ)) fun P => by simp
        _=rd (p:=p) (q:ℕ) hq:=hcard_finset
    have hf_hasSum':HasSum f ((qm K (q:ℕ) s)⁻¹) :=by
      rw [sn (p:=p) (K:=K) hq,← inv_pow]
      simpa [z,hd,hα_card] using hf_hasSum
    simpa [f] using hf_hasSum'.tsum_eq
lemma sH (χ:DirichletCharacter ℂ p) {s:ℂ}
    (hs:1 < s.re) :
    DirichletCharacter.LFunction χ s=
      ∏' q :Nat.Primes,(1-χ ((q:ℕ) : ZMod p) * ((q:ℕ) : ℂ) ^ (-s))⁻¹:=by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.LSeries_eulerProduct_tprod χ hs]
omit hp in
lemma xV (f:DirichletCharacter ℂ p → Nat.Primes → ℂ)
    (hmul: ∀ χ:DirichletCharacter ℂ p,Multipliable (f χ)) :
    (∏ χ :DirichletCharacter ℂ p,∏' q :Nat.Primes,f χ q) =
      ∏' q :Nat.Primes,∏ χ:DirichletCharacter ℂ p,f χ q:=
  (Multipliable.tprod_finsetProd (fun χ _=> hmul χ)).symm
lemma zR {s:ℂ} (hs:1 < s.re) :
    LProduct (p:=p) s =
      ∏' q :Nat.Primes,∏ χ:DirichletCharacter ℂ p,
        (1-χ ((q:ℕ) : ZMod p) * ((q:ℕ) : ℂ) ^ (-s))⁻¹:=by
  unfold LProduct
  rw [Finset.prod_congr rfl (fun χ _=> sH p χ hs)]
  exact xV (p:=p)
    (fun χ q=> (1-χ ((q:ℕ) : ZMod p) * ((q:ℕ) : ℂ) ^ (-s))⁻¹)
    (fun χ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable)
lemma zV {q:Nat.Primes} (hq: (q:ℕ) ≠ p) {s:ℂ} :
    qm K (q:ℕ) s =rm (p:=p) (q:ℕ) s :=by
  have:Fact (q:ℕ).Prime:= ⟨q.2⟩
  rw [sn (p:=p) (K:=K) hq,
    wW (p:=p) hq]
lemma yq {s:ℂ} (hs:1 < s.re) :
    LProduct (p:=p) s =
      ∏' q :Nat.Primes,(rm (p:=p) (q:ℕ) s)⁻¹:=by
  rw [zR p hs]
  refine tprod_congr fun q => ?_
  unfold rm
  rw [Finset.prod_inv_distrib]
lemma y4
  (p:ℕ) [Fact p.Prime] (K:Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] {s:ℂ} (hs:1 < s.re) :
    NumberField.dedekindZeta K s=
      ∏' q :Nat.Primes,(qm K (q:ℕ) s)⁻¹:=by
  rw [sO K hs]
  exact tprod_congr fun _ => wN (p:=p) (K:=K) hs
theorem uX {s:ℂ} (hs:1 < s.re) :
    LProduct (p:=p) s = (1- (p:ℂ) ^ (-s)) * NumberField.dedekindZeta K s:=by
  classical
  have hp_prime:Nat.Prime p :=hp.out
  set p₀:Nat.Primes:= ⟨p,hp_prime⟩
  have h_mul_cf:
      Multipliable (fun q :Nat.Primes=> (rm (p:=p) (q:ℕ) s)⁻¹) :=by
    have h1: (fun q :Nat.Primes=> (rm (p:=p) (q:ℕ) s)⁻¹) =
        (fun q :Nat.Primes=> ∏ χ:DirichletCharacter ℂ p,
          (1-χ ((q:ℕ) : ZMod p) * ((q:ℕ) : ℂ) ^ (-s))⁻¹) :=by
      funext q
      unfold rm
      rw [Finset.prod_inv_distrib]
    rw [h1]
    exact multipliable_prod (s:=Finset.univ) fun χ _=>
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  let h :Nat.Primes → ℂ:=Pi.mulSingle p₀ ((1- (p:ℂ) ^ (-s))⁻¹)
  have h_mul_h:Multipliable h :=multipliable_of_hasFiniteMulSupport <|
    Set.Finite.subset (Set.finite_singleton p₀) Pi.mulSupport_mulSingle_subset
  have h_pointwise: ∀ q:Nat.Primes,
      (rm (p:=p) (q:ℕ) s)⁻¹*h q=
        (qm K (q:ℕ) s)⁻¹:=fun q => by
    by_cases hq:q=p₀
    · subst hq
      simp only [h,Pi.mulSingle_eq_same]
      rw [yU,inv_one,one_mul,wv]
    · simp only [h,Pi.mulSingle_eq_of_ne hq,mul_one]
      have hq': (q:ℕ) ≠ p:=fun heq=> hq (Subtype.ext heq)
      exact (zV (p:=p) (K:=K) hq').symm ▸ rfl
  rw [yq p hs,y4 (p:=p) (K:=K) hs]
  have h_combine: ∏' q :Nat.Primes,(qm K (q:ℕ) s)⁻¹=
      (∏' q :Nat.Primes,(rm (p:=p) (q:ℕ) s)⁻¹) *
        (1- (p:ℂ) ^ (-s))⁻¹:=by
    rw [← tprod_pi_single p₀ ((1- (p:ℂ) ^ (-s))⁻¹),
      ← Multipliable.tprod_mul h_mul_cf h_mul_h]
    exact tprod_congr fun q => (h_pointwise q).symm
  rw [h_combine]
  have h_ne: (1- (p:ℂ) ^ (-s)) ≠ 0:=by
    rw [sub_ne_zero]
    intro heq
    have hpp: (0:ℝ) < (p:ℝ) :=by exact_mod_cast hp_prime.pos
    have hpnorm: ‖(p:ℂ) ^ (-s)‖ < 1:=by
      rw [show ((p:ℂ) ^ (-s)) = ((p:ℝ) : ℂ) ^ (-s) from by push_cast;rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hpp]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp_prime.one_lt)
        (by simp only [Complex.neg_re];linarith)
    rw [← heq,norm_one] at hpnorm
    exact lt_irrefl 1 hpnorm
  field_simp
lemma zf {s:ℂ} :
    LProduct (p:=p) s =
      DirichletCharacter.LFunctionTrivChar p s*qR p s:=by
  classical
  unfold LProduct qR
  rw [show vi (p:=p) = Finset.univ.erase 1 from rfl,
    ← Finset.mul_prod_erase Finset.univ (fun χ => DirichletCharacter.LFunction χ s)
      (Finset.mem_univ 1)]
lemma z9 {s:ℂ} :
    qR p s=r1 p s*vx p s:=by
  classical
  unfold qR r1 vx
    vi qi q8
  have hdisj:Disjoint
      (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Even ∧ χ ≠ 1)
      (Finset.univ.filter fun χ :DirichletCharacter ℂ p=> χ.Odd) :=by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχe hχo
    rw [Finset.mem_filter] at hχe hχo
    exact DirichletCharacter.Odd.not_even χ hχo.2 hχe.2.1
  have hunion:Finset.univ.erase (1:DirichletCharacter ℂ p) =
      Finset.univ.filter (fun χ :DirichletCharacter ℂ p=> χ.Even ∧ χ ≠ 1) ∪
        Finset.univ.filter (fun χ :DirichletCharacter ℂ p=> χ.Odd) :=by
    ext χ
    simp only [Finset.mem_erase,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
      and_true,true_and]
    refine ⟨fun hne=> ?_,?_⟩
    · rcases DirichletCharacter.even_or_odd χ with he | ho
      · exact Or.inl ⟨he,hne⟩
      · exact Or.inr ho
    · rintro (⟨_,hne⟩ | ho)
      · exact hne
      · rintro rfl
        exact DirichletCharacter.Odd.not_even _ ho (by
          change (1:DirichletCharacter ℂ p) (-1) = 1
          rw [MulChar.one_apply (isUnit_one.neg)])
  rw [hunion,Finset.prod_union hdisj]
theorem ut {s:ℂ}
    (hs:1 < s.re) :
    NumberField.dedekindZeta K s=riemannZeta s *qR p s:=by
  have hs_ne:s ≠ 1:=fun h => by
    rw [h] at hs
    simp at hs
  have h1:LProduct (p:=p) s = (1- (p:ℂ) ^ (-s)) * NumberField.dedekindZeta K s:=
    uX p K hs
  have h2:LProduct (p:=p) s =
      (1- (p:ℂ) ^ (-s)) * (riemannZeta s *qR p s) :=by
    rw [zf p,xL p hs_ne,
      mul_assoc]
  have hne: (1- (p:ℂ) ^ (-s)) ≠ 0:=by
    rw [sub_ne_zero]
    intro heq
    have hpp: (0:ℝ) < (p:ℝ) :=by exact_mod_cast hp.out.pos
    have hpnorm: ‖(p:ℂ) ^ (-s)‖ < 1:=by
      rw [show ((p:ℂ) ^ (-s)) = ((p:ℝ) : ℂ) ^ (-s) from by push_cast;rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hpp]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.out.one_lt)
        (by simp;linarith)
    rw [← heq,norm_one] at hpnorm
    exact lt_irrefl 1 hpnorm
  exact mul_left_cancel₀ hne (h1.symm.trans h2)
end ZetaFactorisation
end KummerCriterion
end
end Module27
-- Source: KummerCriterion.HMinus.KplusEulerProduct
section Module28
noncomputable section
open NumberField
open scoped BigOperators Topology nonZeroDivisors
namespace KummerCriterion
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
abbrev ym (L:Type*) [Field L] [NumberField L] : Type _ :=qQ L
abbrev qE (L:Type*) [Field L] [NumberField L] (n:ℕ) : ℕ:=
  qe L n
lemma x2
    (L:Type*) [Field L] [NumberField L] {s:ℂ} (hs:1 < s.re) :
    NumberField.dedekindZeta L s=
      ∏' q :Nat.Primes,
        (∑' k :ℕ,(qE L ((q:ℕ) ^ k) : ℂ) *
          ((((q:ℕ) ^ k:ℕ) : ℂ) ^ (-s))) :=by
  simpa [qE] using
    (sO (L:=L) hs)
lemma wS (hp_odd:p ≠ 2) (k:ℕ) :
    qE (oMR K) (p^k) = 1:=by
  classical
  have:IsCMField K :=r0 (p:=p) (K:=K) hp_odd
  have hcard: (q9 (K:=K) p).card=1:=by
    rw [rt (K:=K) (ℓ:=p)]
    exact uw (p:=p) (K:=K)
  obtain ⟨PPlus,hPPlus⟩ :=Finset.card_eq_one.mp hcard
  have hPPlusmem:PPlus ∈ Ideal.primesOver (q0 p) (𝓞 (oMR K)) :=by
    have hPPlus_fin:PPlus ∈ q9 (K:=K) p :=by
      rw [hPPlus]
      exact Finset.mem_singleton_self PPlus
    exact (qz (K:=K) (ℓ:=p)).1 hPPlus_fin
  have hPPlus_ne:PPlus ≠ ⊥ :=by
    intro hPPlus_bot
    have hunder:=hPPlusmem.2
    rw [Ideal.liesOver_iff,Ideal.under_def,hPPlus_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 (oMR K)))
        (FaithfulSMul.algebraMap_injective ℤ (𝓞 (oMR K)))] at hunder
    have hne: (q0 p) ≠ ⊥ :=by
      rw [q0,Ne,Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    exact hne hunder
  have:PPlus.IsMaximal:=Ring.DimensionLEOne.maximalOfPrime hPPlus_ne hPPlusmem.1
  have:PPlus.LiesOver (Ideal.span {(p:ℤ)}) :=by
    simpa [q0] using hPPlusmem.2
  have habsNormPPlus:Ideal.absNorm PPlus=p:=by
    calc
      Ideal.absNorm PPlus=p^ (1:ℕ) :=by
        rw [← sW (p:=p) (K:=K) PPlus hPPlusmem]
        rw [← Ideal.inertiaDeg'_eq_inertiaDeg (p:=Ideal.span {(p:ℤ)}) (q:=PPlus)]
        exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus hp.out
      _=p:=by simp
  have:Unique {I:ym (oMR K) //Ideal.absNorm I.1=p^k} :=
    { default:= ⟨⟨PPlus^k,pow_ne_zero k hPPlus_ne⟩,by
          rw [map_pow,habsNormPPlus]⟩
      uniq:=by
        rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
        let m :ℕ:=Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I)
        obtain ⟨Q,hPQ,hIeq⟩ :=Ideal.eq_prime_pow_mul_coprime hI_ne PPlus
        have hQ_top:Q= ⊤ :=by
          by_contra hQ_ne_top
          have hQ_ne:Q ≠ ⊥ :=by
            intro hQ_bot
            apply hI_ne
            rw [hIeq,hQ_bot,Ideal.mul_bot]
          have hnf_ne:UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 :=by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne,hnf]
            simp
          obtain ⟨R,hRmem⟩ :=Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac:= (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime:R.IsPrime:=hRfac.1
          have hQ_le_R:Q ≤ R:=hRfac.2
          have hR_ne:R ≠ ⊥ :=fun hR_bot=>
            hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          have:NeZero R := ⟨hR_ne⟩
          have hI_le_Q:I ≤ Q:=by
            rw [hIeq]
            exact Ideal.mul_le_right
          have hR_dvd_I:Ideal.absNorm R ∣ p ^k:=by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd:Ideal.absNorm (Ideal.under ℤ R) ∣ p^k:=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime: (Ideal.absNorm (Ideal.under ℤ R)).Prime:=Nat.absNorm_under_prime R
          have hunder_dvd_p:Ideal.absNorm (Ideal.under ℤ R) ∣ p:=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_p:Ideal.absNorm (Ideal.under ℤ R) = p:=
            (Nat.prime_dvd_prime_iff_eq hunder_prime hp.out).1 hunder_dvd_p
          have hunder_eq_span_p:Ideal.under ℤ R=Ideal.span {(p:ℤ)} :=by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]
            simp [hunder_eq_p]
          have hR_lies:R.LiesOver (Ideal.span {(p:ℤ)}) :=by
            rw [Ideal.liesOver_iff,hunder_eq_span_p]
          have hRmem_p:R ∈ Ideal.primesOver (q0 p) (𝓞 (oMR K)) :=by
            refine ⟨hRprime,?_⟩
            simpa [q0] using hR_lies
          have hRmem_fin:R ∈ q9 (K:=K) p :=
            (qz (K:=K) (ℓ:=p)).2 hRmem_p
          have hR_eq_PPlus:R=PPlus:=by
            rw [hPPlus] at hRmem_fin
            exact Finset.mem_singleton.mp hRmem_fin
          have hQ_le_PPlus:Q ≤ PPlus:=by
            simpa [hR_eq_PPlus] using hQ_le_R
          have htop_le_PPlus: (⊤ : Ideal (𝓞 (oMR K))) ≤ PPlus:=by
            calc
              ⊤ = PPlus ⊔ Q:=hPQ.symm
              _ ≤ PPlus:=sup_le le_rfl hQ_le_PPlus
          exact hPPlusmem.1.ne_top (top_le_iff.mp htop_le_PPlus)
        have hI_pow:I=PPlus^m:=by
          simpa [m,hQ_top] using hIeq
        have hm:m=k:=by
          apply Nat.pow_right_injective hp.out.one_lt
          calc
            p^m=Ideal.absNorm I :=by
              rw [hI_pow,map_pow,habsNormPPlus]
            _=p^k:=hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m,hm] using hI_pow}
  exact Nat.card_unique
lemma qU
    {q:Nat.Primes} {I:Ideal (𝓞 (oMR K))} (hI_ne:I ≠ ⊥)
    {k:ℕ} (hI_norm:Ideal.absNorm I = (q:ℕ) ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆
      q9 (K:=K) (q:ℕ) :=by
  have:Fact (q:ℕ).Prime:= ⟨q.2⟩
  intro PPlus hPPlus
  have hPPlus_mem:PPlus ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.mem_toFinset.1 hPPlus
  have hPPlus_fac:= (Ideal.mem_normalizedFactors_iff hI_ne).1 hPPlus_mem
  have hPPlus_prime:PPlus.IsPrime:=hPPlus_fac.1
  have hI_le_PPlus:I ≤ PPlus:=hPPlus_fac.2
  have hPPlus_ne:PPlus ≠ ⊥ :=fun hPPlus_bot=>
    hI_ne (le_bot_iff.mp (hPPlus_bot ▸ hI_le_PPlus))
  have:NeZero PPlus:= ⟨hPPlus_ne⟩
  have hPPlus_dvd:Ideal.absNorm PPlus ∣ (q:ℕ) ^ k:=by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_PPlus
  have hunder_dvd:Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q:ℕ) ^ k:=
    dvd_trans (Int.absNorm_under_dvd_absNorm PPlus) hPPlus_dvd
  have hunder_prime: (Ideal.absNorm (Ideal.under ℤ PPlus)).Prime:=Nat.absNorm_under_prime PPlus
  have hunder_dvd_q:Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q:ℕ) :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q:Ideal.absNorm (Ideal.under ℤ PPlus) = (q:ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime q.2).1 hunder_dvd_q
  have hunder_eq_span_q:Ideal.under ℤ PPlus=Ideal.span {((q:ℕ) : ℤ)} :=by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ PPlus)]
    simp [hunder_eq_q]
  have hPPlus_lies:PPlus.LiesOver (Ideal.span {((q:ℕ) : ℤ)}) :=by
    rw [Ideal.liesOver_iff,hunder_eq_span_q]
  have hPPlus_over:PPlus ∈ Ideal.primesOver (q0 (q:ℕ)) (𝓞 (oMR K)) :=by
    refine ⟨hPPlus_prime,?_⟩
    simpa [q0] using hPPlus_lies
  exact (qz (K:=K) (ℓ:= (q:ℕ))).2 hPPlus_over
lemma qG
    (hp_odd:p ≠ 2) {q:Nat.Primes} [Fact (q:ℕ).Prime] (hq: (q:ℕ) ≠ p)
    {PPlus:Ideal (𝓞 (oMR K))}
    (hPPlus:PPlus ∈ q9 (K:=K) (q:ℕ)) :
    Ideal.absNorm PPlus= (q:ℕ) ^ q5 (p:=p) (q:ℕ) hq:=by
  have hPPlus_over:PPlus ∈ Ideal.primesOver (q0 (q:ℕ)) (𝓞 (oMR K)) :=
    (qz (K:=K) (ℓ:= (q:ℕ))).1 hPPlus
  have:PPlus.LiesOver (Ideal.span {((q:ℕ) : ℤ)}) :=by
    simpa [q0] using hPPlus_over.2
  have: (q0 (q:ℕ)).IsMaximal:=by
    simpa [q0] using Int.ideal_span_isMaximal_of_prime (q:ℕ)
  have:PPlus.IsMaximal:=Ideal.isMaximal_of_mem_primesOver hPPlus_over
  rw [← rq
    (p:=p) (K:=K) hp_odd hq PPlus hPPlus_over]
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    (p:=Ideal.span {((q:ℕ) : ℤ)}) (q:=PPlus)]
  exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus q.2
lemma ro
    (hp_odd:p ≠ 2) {q:Nat.Primes} [Fact (q:ℕ).Prime] (hq: (q:ℕ) ≠ p)
    {I:Ideal (𝓞 (oMR K))} (hI_ne:I ≠ ⊥) {k:ℕ}
    (hI_norm:Ideal.absNorm I = (q:ℕ) ^ k) :
    q5 (p:=p) (q:ℕ) hq*
        (UniqueFactorizationMonoid.normalizedFactors I).card=k:=by
  classical
  set d :=q5 (p:=p) (q:ℕ) hq with hd
  set m :=UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset:m.toFinset ⊆ q9 (K:=K) (q:ℕ) :=by
    simpa [hm] using
      qU (K:=K) hI_ne hI_norm
  have hsum_count: ∑ PPlus ∈ q9 (K:=K) (q:ℕ),m.count PPlus=m.card:=
    Multiset.sum_count_eq_card fun PPlus hPPlus=> hsubset (Multiset.mem_toFinset.2 hPPlus)
  have hnorm_factors:Ideal.absNorm m.prod= (q:ℕ) ^ (d*m.card) :=by
    rw [Finset.prod_multiset_count_of_subset m (q9 (K:=K) (q:ℕ)) hsubset,
      map_prod]
    calc
      ∏ PPlus ∈ q9 (K:=K) (q:ℕ),Ideal.absNorm (PPlus^m.count PPlus)
          = ∏ PPlus ∈ q9 (K:=K) (q:ℕ),
              ((q:ℕ) ^ d) ^ m.count PPlus:=by
              apply Finset.prod_congr rfl
              intro PPlus hPPlus
              rw [map_pow]
              rw [qG
                (p:=p) (K:=K) hp_odd hq hPPlus,hd]
      _= (q:ℕ) ^
          (d* ∑ PPlus ∈ q9 (K:=K) (q:ℕ),m.count PPlus) :=by
              rw [Finset.prod_pow_eq_pow_sum]
              simp [Nat.pow_mul]
      _= (q:ℕ) ^ (d*m.card) :=by rw [hsum_count]
  have hpow: (q:ℕ) ^ (d*m.card) = (q:ℕ) ^ k:=by
    calc
      (q:ℕ) ^ (d*m.card) = Ideal.absNorm m.prod:=hnorm_factors.symm
      _=Ideal.absNorm I :=by rw [hm,Ideal.prod_normalizedFactors_eq_self hI_ne]
      _= (q:ℕ) ^ k:=hI_norm
  exact Nat.pow_right_injective q.2.one_lt hpow
lemma uS
    (hp_odd:p ≠ 2) {q:Nat.Primes} [Fact (q:ℕ).Prime] (hq: (q:ℕ) ≠ p)
    {k:ℕ} (hk: ¬ q5 (p:=p) (q:ℕ) hq ∣ k) :
    qE (oMR K) ((q:ℕ) ^ k) = 0:=by
  unfold qE qe
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
  apply hk
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card,?_⟩
  simpa [mul_comm] using
    (ro
      (p:=p) (K:=K) hp_odd hq hI_ne hI_norm).symm
lemma sV
    (hp_odd:p ≠ 2) {q:Nat.Primes} [Fact (q:ℕ).Prime] (hq: (q:ℕ) ≠ p) (n:ℕ) :
    qE (oMR K)
        ((q:ℕ) ^ (q5 (p:=p) (q:ℕ) hq*n)) =
      Fintype.card (Sym {PPlus:Ideal (𝓞 (oMR K)) //
        PPlus ∈ q9 (K:=K) (q:ℕ)} n) :=by
  classical
  set d :=q5 (p:=p) (q:ℕ) hq with hd
  let α :Type _ :=
    {PPlus:Ideal (𝓞 (oMR K)) //PPlus ∈ q9 (K:=K) (q:ℕ)}
  let β :Type _ := {I:ym (oMR K) //Ideal.absNorm I.1= (q:ℕ) ^ (d*n)}
  have hd_raw_pos:0 < q4 (p:=p) (q:ℕ) hq:=by
    dsimp [q4]
    exact orderOf_pos (qx (p:=p) (q:ℕ) hq)
  have hd_pos:0 < d:=by
    rw [hd]
    by_cases hde:Even (q4 (p:=p) (q:ℕ) hq)
    · rcases hde with ⟨k,hk⟩
      rw [r9 (p:=p) hq ⟨k,hk⟩,hk]
      omega
    · rw [r8 (p:=p) hq hde]
      exact hd_raw_pos
  have hpmap_val:
      ∀ {m:Multiset (Ideal (𝓞 (oMR K)))}
        (H: ∀ PPlus,PPlus ∈ m → PPlus ∈ q9 (K:=K) (q:ℕ)),
        Multiset.map Subtype.val
          (Multiset.pmap (fun PPlus hPPlus=> (⟨PPlus,hPPlus⟩ : α)) m H) = m:=by
    intro m H
    rw [Multiset.map_pmap,Multiset.pmap_eq_map,Multiset.map_id']
  let toSym:β → Sym α n:=fun ⟨⟨I,hI_ne⟩,hI_norm⟩ =>
    let m :=UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ PPlus,PPlus ∈ m → PPlus ∈ q9 (K:=K) (q:ℕ) :=by
      intro PPlus hPPlus
      have hsubset:m.toFinset ⊆ q9 (K:=K) (q:ℕ) :=by
        simpa [m] using
          qU (K:=K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    have hm_card:m.card=n:=by
      have hmul:d*m.card=d*n:=by
        simpa [m,hd] using
          ro
            (p:=p) (K:=K) hp_odd hq hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hd_pos hmul
    ⟨Multiset.pmap (fun PPlus hPPlus=> (⟨PPlus,hPPlus⟩ : α)) m H,by
      simp [hm_card]⟩
  let ofSym:Sym α n → β:=fun s =>
    let m :Multiset (Ideal (𝓞 (oMR K))) :=s.1.map Subtype.val
    have hm_card:m.card=n:=by
      simp [m]
    have hm_subset:m.toFinset ⊆ q9 (K:=K) (q:ℕ) :=by
      intro PPlus hPPlus
      rcases Multiset.mem_toFinset.1 hPPlus with hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus,hQPlus,rfl⟩
      exact QPlus.2
    have hm_prime: ∀ PPlus ∈ m,Prime PPlus:=by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus,hQPlus,rfl⟩
      have hQPlus_ne: (QPlus:Ideal (𝓞 (oMR K))) ≠ ⊥ :=by
        intro hQPlus_bot
        have hQPlus_norm:=
          qG
            (p:=p) (K:=K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot,← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((qz (K:=K) (ℓ:= (q:ℕ))).1 QPlus.2).1
    have hm_prod_ne:m.prod ≠ ⊥ :=Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm:Ideal.absNorm m.prod= (q:ℕ) ^ (d*n) :=by
      have hsum_count:
          ∑ PPlus ∈ q9 (K:=K) (q:ℕ),m.count PPlus=m.card:=
        Multiset.sum_count_eq_card fun PPlus hPPlus=>
          hm_subset (Multiset.mem_toFinset.2 hPPlus)
      rw [Finset.prod_multiset_count_of_subset m
        (q9 (K:=K) (q:ℕ)) hm_subset,map_prod]
      calc
        ∏ PPlus ∈ q9 (K:=K) (q:ℕ),Ideal.absNorm (PPlus^m.count PPlus)
            = ∏ PPlus ∈ q9 (K:=K) (q:ℕ),
                ((q:ℕ) ^ d) ^ m.count PPlus:=by
                apply Finset.prod_congr rfl
                intro PPlus hPPlus
                rw [map_pow]
                rw [qG
                  (p:=p) (K:=K) hp_odd hq hPPlus,hd]
        _= (q:ℕ) ^
            (d* ∑ PPlus ∈ q9 (K:=K) (q:ℕ),m.count PPlus) :=by
                rw [Finset.prod_pow_eq_pow_sum]
                simp [Nat.pow_mul]
        _= (q:ℕ) ^ (d*m.card) :=by rw [hsum_count]
        _= (q:ℕ) ^ (d*n) :=by rw [hm_card]
    ⟨⟨m.prod,hm_prod_ne⟩,hm_norm⟩
  have htoSym_map_val:
      ∀ b :β,
        (toSym b).1.map Subtype.val=UniqueFactorizationMonoid.normalizedFactors b.1.1:=by
    rintro ⟨⟨I,hI_ne⟩,hI_norm⟩
    dsimp [toSym]
    let m :=UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ PPlus,PPlus ∈ m → PPlus ∈ q9 (K:=K) (q:ℕ) :=by
      intro PPlus hPPlus
      have hsubset:m.toFinset ⊆ q9 (K:=K) (q:ℕ) :=by
        simpa [m] using
          qU (K:=K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    change (Multiset.pmap (fun PPlus hPPlus=> (⟨PPlus,hPPlus⟩ : α)) m H).map Subtype.val=m
    rw [hpmap_val H]
  have hofSym_nfactors:
      ∀ s :Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1=s.1.map Subtype.val:=by
    intro s
    dsimp [ofSym]
    let m :Multiset (Ideal (𝓞 (oMR K))) :=s.1.map Subtype.val
    have hm_prime: ∀ PPlus ∈ m,Prime PPlus:=by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus,hQPlus,rfl⟩
      have hQPlus_ne: (QPlus:Ideal (𝓞 (oMR K))) ≠ ⊥ :=by
        intro hQPlus_bot
        have hQPlus_norm:=
          qG
            (p:=p) (K:=K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot,← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((qz (K:=K) (ℓ:= (q:ℕ))).1 QPlus.2).1
    change UniqueFactorizationMonoid.normalizedFactors m.prod=m
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hm_prime
  have hleft:Function.LeftInverse ofSym toSym:=by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod=b.1.1
    rw [htoSym_map_val,Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright:Function.RightInverse ofSym toSym:=by
    intro s
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  unfold qE qe
  simpa [β,α,hd,Nat.card_eq_fintype_card] using
    Nat.card_congr (⟨toSym,ofSym,hleft,hright⟩ : β ≃ Sym α n)
lemma vC
    (hp_odd:p ≠ 2) {s:ℂ} (hs:1 < s.re) :
    (∑' k :ℕ,(qE (oMR K) (p^k) : ℂ) *
      (((p^k:ℕ) : ℂ) ^ (-s))) =
      (qm (oMR K) p s)⁻¹:=by
  have:IsCMField K :=r0 (p:=p) (K:=K) hp_odd
  have hnorm: ‖(p:ℂ) ^ (-s)‖ < 1:=by
    have hle: ‖(p:ℂ) ^ (-s)‖ ≤ 1/2:=
      Complex.norm_prime_cpow_le_one_half ⟨p,hp.out⟩ hs
    exact hle.trans_lt (by norm_num)
  rw [vs (p:=p) (K:=K)]
  trans ∑' k :ℕ,((p:ℂ) ^ (-s)) ^ k
  · refine tsum_congr fun k => ?_
    rw [wS (p:=p) (K:=K) hp_odd k]
    simp only [Nat.cast_one,one_mul]
    rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul p k (-s),mul_comm,
      Complex.cpow_mul_nat]
  · simpa using tsum_geometric_of_norm_lt_one hnorm
lemma wc
    (hp_odd:p ≠ 2) {q:Nat.Primes} {s:ℂ} (hs:1 < s.re) :
    (∑' k :ℕ,(qE (oMR K) ((q:ℕ) ^ k) : ℂ) *
      ((((q:ℕ) ^ k:ℕ) : ℂ) ^ (-s))) =
      (qm (oMR K) (q:ℕ) s)⁻¹:=by
  have:Fact (q:ℕ).Prime:= ⟨q.2⟩
  by_cases hq: (q:ℕ) = p
  · have hq':q= ⟨p,Fact.out⟩ :=by
      apply Subtype.ext
      simpa using hq
    subst hq'
    simpa using vC
      (p:=p) (K:=K) hp_odd hs
  · classical
    have:IsCMField K :=r0 (p:=p) (K:=K) hp_odd
    set d :=q5 (p:=p) (q:ℕ) hq with hd
    let α :Type _ := {PPlus:Ideal (𝓞 (oMR K)) //
      PPlus ∈ q9 (K:=K) (q:ℕ)}
    let f :ℕ → ℂ:=fun k =>
      (qE (oMR K) ((q:ℕ) ^ k) : ℂ) * ((((q:ℕ) ^ k:ℕ) : ℂ) ^ (-s))
    let g :ℕ → ℂ:=fun n =>
      (qE (oMR K) ((q:ℕ) ^ (d*n)) : ℂ) *
        ((((q:ℕ) ^ (d*n) : ℕ) : ℂ) ^ (-s))
    let z :ℂ:= (q:ℂ) ^ (-((d:ℂ) * s))
    have hd_raw_pos:0 < q4 (p:=p) (q:ℕ) hq:=by
      dsimp [q4]
      exact orderOf_pos (qx (p:=p) (q:ℕ) hq)
    have hd_pos:0 < d:=by
      rw [hd]
      by_cases hde:Even (q4 (p:=p) (q:ℕ) hq)
      · rcases hde with ⟨k,hk⟩
        rw [r9 (p:=p) hq ⟨k,hk⟩,hk]
        omega
      · rw [r8 (p:=p) hq hde]
        exact hd_raw_pos
    have hs_d:1 < (((d:ℂ) * s).re) :=by
      rw [Complex.mul_re]
      simp
      have hd_ge: (1:ℝ) ≤ d:=by
        exact_mod_cast Nat.succ_le_of_lt hd_pos
      nlinarith [hs,hd_ge]
    have hz: ‖z‖ < 1:=by
      have hle: ‖z‖ ≤ 1/2:=by
        dsimp [z]
        exact Complex.norm_prime_cpow_le_one_half ⟨q,q.2⟩ hs_d
      exact hle.trans_lt (by norm_num)
    have hg_term: ∀ n:ℕ,g n= (Fintype.card (Sym α n) : ℂ) * z^n:=by
      intro n
      dsimp [g,z]
      rw [show qE (oMR K) ((q:ℕ) ^ (d*n)) = Fintype.card (Sym α n) by
        simpa [α,hd] using
          sV
            (p:=p) (K:=K) hp_odd hq n]
      rw [Nat.cast_pow,← Complex.natCast_cpow_natCast_mul (q:ℕ) (d*n) (-s)]
      have hexp: (((d*n:ℕ) : ℂ) * (-s)) = (-((d:ℂ) * s)) * n:=by
        push_cast
        ring
      rw [hexp,Complex.cpow_mul_nat]
    have hg_eq:g=fun n :ℕ=> (Fintype.card (Sym α n) : ℂ) * z^n:=funext hg_term
    have hg_hasSum0:HasSum (fun n :ℕ=> (Fintype.card (Sym α n) : ℂ) * z^n)
        (((1-z)⁻¹) ^ Fintype.card α) :=by
      rw [← zD α hz]
      exact (sR α hz).1.hasSum
    have hg_hasSum:HasSum g (((1-z)⁻¹) ^ Fintype.card α) :=by
      simpa [hg_eq] using hg_hasSum0
    have hf_hasSum:HasSum f (((1-z)⁻¹) ^ Fintype.card α) :=by
      refine (hasSum_iff_hasSum_of_ne_zero_bij
        (f:=f) (g:=g) (i:=fun x :Function.support g => d *x.1) ?_ ?_ ?_).2 hg_hasSum
      · intro x y hxy
        exact Subtype.ext <| Nat.eq_of_mul_eq_mul_left hd_pos hxy
      · intro k hk
        have hk_mult:qE (oMR K) ((q:ℕ) ^ k) ≠ 0:=fun hk_zero=>
          hk (by simp [f,hk_zero])
        have hk_dvd:d ∣ k:=by
          by_contra hk_ndvd
          exact hk_mult <|
            uS
              (p:=p) (K:=K) hp_odd hq hk_ndvd
        obtain ⟨n,rfl⟩ :=hk_dvd
        refine ⟨⟨n,?_⟩,rfl⟩
        simpa [f,g,mul_comm] using hk
      · intro x
        simp [f,g,mul_comm]
    have hcard_finset:
        (q9 (K:=K) (q:ℕ)).card=
          qo (p:=p) (q:ℕ) hq:=by
      rw [rt (K:=K) (ℓ:= (q:ℕ))]
      exact sx (p:=p) (K:=K) hp_odd hq
    have hα_card:Fintype.card α =qo (p:=p) (q:ℕ) hq:=by
      calc
        Fintype.card α = (q9 (K:=K) (q:ℕ)).card:=
          Fintype.card_of_finset' (q9 (K:=K) (q:ℕ)) fun PPlus=> by simp
        _=qo (p:=p) (q:ℕ) hq:=hcard_finset
    have hf_hasSum':HasSum f ((qm (oMR K) (q:ℕ) s)⁻¹) :=by
      rw [s0
        (p:=p) (K:=K) hp_odd hq,← inv_pow]
      simpa [z,hd,hα_card] using hf_hasSum
    simpa [f] using hf_hasSum'.tsum_eq
lemma zB (hp_odd:p ≠ 2) {s:ℂ} (hs:1 < s.re) :
    NumberField.dedekindZeta (oMR K) s =
      ∏' q :Nat.Primes,(qm (oMR K) (q:ℕ) s)⁻¹:=by
  rw [x2 (L:= (oMR K)) hs]
  exact tprod_congr fun q =>
    wc (p:=p) (K:=K) hp_odd hs
lemma ze {s:ℂ} (hs:1 < s.re) :
    r1 p s=
      ∏' q :Nat.Primes,
        ∏ χ ∈ qi (p:=p),
          (1-χ ((q:ℕ) : ZMod p) * ((q:ℕ) : ℂ) ^ (-s))⁻¹:=by
  classical
  unfold r1
  rw [Finset.prod_congr rfl (fun χ _=> sH p χ hs)]
  exact (Multipliable.tprod_finsetProd
    (s:=qi (p:=p))
    (fun χ _=> (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable)).symm
lemma y3 {s:ℂ} (hs:1 < s.re) :
    r1 p s=
      ∏' q :Nat.Primes,(qI (p:=p) (q:ℕ) s)⁻¹:=by
  classical
  rw [ze (p:=p) hs]
  refine tprod_congr fun q => ?_
  unfold qI
  rw [Finset.prod_inv_distrib]
lemma yo {s:ℂ} :
    qI (p:=p) p s=1:=by
  classical
  exact Finset.prod_eq_one fun χ _=> by
    rw [ZMod.natCast_self,MulChar.map_nonunit _ not_isUnit_zero,zero_mul,sub_zero]
lemma zp (hp_odd:p ≠ 2)
    {q:Nat.Primes} (hq: (q:ℕ) ≠ p) {s:ℂ} :
    qm (oMR K) (q:ℕ) s =
      (1- ((q:ℕ) : ℂ) ^ (-s)) * qI (p:=p) (q:ℕ) s :=by
  have:IsCMField K :=r0 (p:=p) (K:=K) hp_odd
  have:Fact (q:ℕ).Prime:= ⟨q.2⟩
  rw [s0 (p:=p) (K:=K) hp_odd hq]
  symm
  simpa [neg_mul] using
    (uv
      (p:=p) hp_odd hq (s:=s))
lemma y8 (hp_odd:p ≠ 2) {s:ℂ} :
    qm (oMR K) p s=
      (1- (p:ℂ) ^ (-s)) * qI (p:=p) p s:=by
  have:IsCMField K :=r0 (p:=p) (K:=K) hp_odd
  rw [yo (p:=p),mul_one,vs (p:=p) (K:=K)]
lemma yE (hp_odd:p ≠ 2) {q:Nat.Primes} {s:ℂ} :
    qm (oMR K) (q:ℕ) s =
      (1- ((q:ℕ) : ℂ) ^ (-s)) * qI (p:=p) (q:ℕ) s :=by
  by_cases hq: (q:ℕ) = p
  · have hq':q= ⟨p,Fact.out⟩ :=by
      apply Subtype.ext
      simpa using hq
    subst hq'
    exact y8 (p:=p) (K:=K) hp_odd
  · exact zp (p:=p) (K:=K) hp_odd hq
theorem uW
    (hp_odd:p ≠ 2) {s:ℂ} (hs:1 < s.re) :
    NumberField.dedekindZeta (oMR K) s =riemannZeta s *r1 p s:=by
  have hmul_riem:
      Multipliable (fun q :Nat.Primes=> (1- ((q:ℕ) : ℂ) ^ (-s))⁻¹) :=
    (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hmul_even:
      Multipliable (fun q :Nat.Primes=> (qI (p:=p) (q:ℕ) s)⁻¹) :=by
    classical
    have h1:
        (fun q :Nat.Primes=> (qI (p:=p) (q:ℕ) s)⁻¹) =
          (fun q :Nat.Primes=>
            ∏ χ ∈ qi (p:=p),
              (1-χ ((q:ℕ) : ZMod p) * ((q:ℕ) : ℂ) ^ (-s))⁻¹) :=by
      funext q
      unfold qI
      rw [Finset.prod_inv_distrib]
    rw [h1]
    exact multipliable_prod (s:=qi (p:=p)) fun χ _=>
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  calc
    NumberField.dedekindZeta (oMR K) s
        = ∏' q :Nat.Primes,(qm (oMR K) (q:ℕ) s)⁻¹:=
            zB (p:=p) (K:=K) hp_odd hs
    _= ∏' q :Nat.Primes,
          ((1- ((q:ℕ) : ℂ) ^ (-s))⁻¹*
            (qI (p:=p) (q:ℕ) s)⁻¹) :=by
            refine tprod_congr fun q => ?_
            rw [yE (p:=p) (K:=K) hp_odd,mul_inv_rev,mul_comm]
    _= (∏' q :Nat.Primes,(1- ((q:ℕ) : ℂ) ^ (-s))⁻¹) *
          (∏' q :Nat.Primes,(qI (p:=p) (q:ℕ) s)⁻¹) :=by
            rw [Multipliable.tprod_mul hmul_riem hmul_even]
    _=riemannZeta s *r1 p s:=by
            rw [riemannZeta_eulerProduct_tprod hs,y3 (p:=p) hs]
theorem vV:
    Filter.Tendsto
      (fun s :ℝ ↦ (s-1) * (riemannZeta (s:ℂ) * r1 p (s:ℂ)))
      (𝓝[>] 1)
      (𝓝 (r1 p (1:ℂ))) :=by
  classical
  have h_cont:Continuous (r1 p) :=
    continuous_finsetProd _ fun χ hχ=>
      (DirichletCharacter.differentiable_LFunction (Finset.mem_filter.mp hχ).2.2).continuous
  have h_embed:
      Filter.Tendsto (fun s :ℝ=> (s:ℂ)) (𝓝[>] (1:ℝ)) (𝓝[≠] (1:ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin] with s hs h
          exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta:Filter.Tendsto (fun s :ℝ=> ((s:ℂ) - 1) * riemannZeta (s:ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod:Filter.Tendsto (fun s :ℝ=> r1 p (s:ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 (r1 p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod:=h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring
theorem vg (hp_odd:p ≠ 2) :
    Filter.Tendsto
      (fun s :ℝ ↦ (s-1) * NumberField.dedekindZeta (oMR K) (s:ℂ))
      (𝓝[>] 1)
      (𝓝 (r1 p (1:ℂ))) :=by
  refine (Filter.tendsto_congr' ?_).mp
    (vV (p:=p))
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [uW
    (p:=p) (K:=K) hp_odd (by exact_mod_cast hs)]
theorem vc (hp_odd:p ≠ 2) :
    ((NumberField.dedekindZeta_residue (oMR K) : ℝ) : ℂ) = r1 p (1:ℂ) :=
  tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT (oMR K))
    (vg (p:=p) (K:=K) hp_odd)
end KummerCriterion
end
end Module28
-- Source: KummerCriterion.LValueAtOne.Cosine
section Module29
noncomputable section
open Filter
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p:ℕ) [hp:Fact p.Prime]
lemma x9 {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) (n:ℕ) :
    ‖∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i)‖ ≤
      2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
  let z :ℂ:=Complex.exp ((2*Real.pi*x) * Complex.I)
  have hz_ne_one:z ≠ 1:=by
    intro hz
    have hexp:Complex.exp ((2*Real.pi*x) * Complex.I) = 1:=by simpa [z] using hz
    obtain ⟨m,hm⟩ :=Complex.exp_eq_one_iff.mp hexp
    have him:2*Real.pi*x= (m:ℝ) * (2*Real.pi) :=by
      simpa using congrArg Complex.im hm
    have hm_pos: (0:ℝ) < m:=by nlinarith [Real.pi_pos,hx₀,him]
    have hm_lt_one: (m:ℝ) < 1:=by nlinarith [Real.pi_pos,hx₁,him]
    have hm_pos_int:0 < m:=by exact_mod_cast hm_pos
    have hm_lt_one_int:m < 1:=by exact_mod_cast hm_lt_one
    lia
  have hre:
      ((∑ i ∈ Finset.range n,z^i).re:ℝ) =
        ∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i) :=by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _=> ?_
    rw [show z ^i=Complex.exp (((2*Real.pi*x*i:ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring,Complex.exp_ofReal_mul_I_re]
  have hgeom: ‖∑ i ∈ Finset.range n,z^i‖ ≤ 2/ ‖z-1‖ :=by
    calc
      ‖∑ i ∈ Finset.range n,z^i‖ = ‖(z^n-1) / (z-1)‖ :=by
        rw [geom_sum_eq hz_ne_one]
      _= ‖z^n-1‖ / ‖z-1‖ :=by rw [Complex.norm_div]
      _ ≤ 2/ ‖z-1‖ :=by
        have hden:0 < ‖z-1‖ :=norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne_one)
        have hnum: ‖z^n-1‖ ≤ 2:=by
          calc
            ‖z^n-1‖ ≤ ‖z^n‖ + ‖(1:ℂ)‖ :=norm_sub_le _ _
            _=1+1:=by
              rw [norm_pow]
              have hz_norm: ‖z‖ = 1:=by
                simpa [z] using Complex.norm_exp_ofReal_mul_I (2*Real.pi*x)
              rw [hz_norm]
              simp
            _=2:=by norm_num
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc
    ‖∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i)‖
      = ‖((∑ i ∈ Finset.range n,z^i).re:ℝ)‖ :=by rw [hre]
    _ ≤ ‖∑ i ∈ Finset.range n,z^i‖ :=by
      simpa using (RCLike.norm_re_le_norm (∑ i ∈ Finset.range n,z^i))
    _ ≤ 2/ ‖z-1‖ :=hgeom
    _=2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
      simp [z,norm_sub_rev]
lemma yj (x:ℝ) (i:ℕ) :
    Continuous fun s :ℝ=>
      Real.cos (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ)) :=by
  refine Continuous.div continuous_const ?_ ?_
  · exact Continuous.const_cpow Complex.continuous_ofReal (Or.inl (Nat.cast_add_one_ne_zero i))
  · intro s h
    exact (Nat.cast_add_one_ne_zero i) ((Complex.cpow_eq_zero_iff _ _).mp h).1
lemma yG (x s :ℝ) (hs:1 < s) :
    HasSum (fun n :ℕ=> Real.cos (2*Real.pi*x* (n+1)) / ((n+1:ℂ) ^ (s:ℂ)))
      (HurwitzZeta.cosZeta x s) :=by
  let f :ℕ → ℂ:=fun n => Real.cos (2*Real.pi*x*n) / ((n:ℂ) ^ (s:ℂ))
  have hfull:HasSum f (HurwitzZeta.cosZeta x s) :=by
    simpa [f] using HurwitzZeta.hasSum_nat_cosZeta x (show 1 < ((s:ℂ)).re by simpa)
  have hshift:HasSum (fun n :ℕ=> f (n+1)) (∑' n :ℕ,f (n+1)) :=
    ((summable_nat_add_iff 1).2 hfull.summable).hasSum
  have hfull':HasSum f (f 0 + ∑' n :ℕ,f (n+1)) :=hshift.zero_add
  have hvalue: (∑' n :ℕ,f (n+1)) = HurwitzZeta.cosZeta x s:=by
    have hs0: ((s:ℂ)) ≠ 0:=by
      exact_mod_cast (show s ≠ 0 by linarith)
    have hf0:f 0=0:=by
      simp [f,hs0]
    have:=tendsto_nhds_unique hfull'.tendsto_sum_nat hfull.tendsto_sum_nat
    simpa [hf0] using this
  exact hvalue ▸ hshift.congr_fun (fun n => by simp [f])
lemma z7 {x s :ℝ} (hx₀:0 < x) (hx₁:x < 1) (hs:1 ≤ s)
    (m n :ℕ) :
    ‖∑ i ∈ Finset.range n,
        Real.cos (2*Real.pi*x* (m+i+1)) / (((m+i+1:ℕ) : ℂ) ^ (s:ℂ))‖ ≤
      (8/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖) *
        (1/ (m+1:ℝ) ^ s) :=by
  let a :ℕ → ℝ:=fun k => 1 / (k+1:ℝ) ^ s
  let z :ℕ → ℂ:=fun k => Real.cos (2*Real.pi*x* (k+1))
  have ha:Antitone a :=by
    intro i j hij
    have hij': (i+1:ℝ) ≤ j+1:=by exact_mod_cast Nat.succ_le_succ hij
    have hi_pos:0 < (i+1:ℝ) :=by positivity
    have hs_nonneg:0 ≤ s:=le_trans zero_lt_one.le hs
    have hpow: (i+1:ℝ) ^ s ≤ (j+1:ℝ) ^ s:=
      Real.rpow_le_rpow hi_pos.le hij' hs_nonneg
    simpa [a,one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hi_pos _) hpow
  have ha_nonneg: ∀ k,0 ≤ a k:=by
    intro k
    positivity
  have hzbound:
      ∀ k,‖∑ i ∈ Finset.range k,z i‖ ≤
        4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
    intro k
    let f :ℕ → ℝ:=fun i => Real.cos (2*Real.pi*x*i)
    have hsum0:=Finset.sum_range_add f 1 k
    have hsum:
        ∑ i ∈ Finset.range k,Real.cos (2*Real.pi*x* (i+1)) =
          ∑ i ∈ Finset.range (k+1),Real.cos (2*Real.pi*x*i) - 1:=by
      rw [Finset.sum_range_one] at hsum0
      calc
        ∑ i ∈ Finset.range k,Real.cos (2*Real.pi*x* (i+1))
            = ∑ i ∈ Finset.range k,f (1+i) :=by simp [f,add_comm]
        _= ∑ i ∈ Finset.range (k+1),f i-f 0:=
              eq_sub_iff_add_eq.mpr (by
                simpa [add_comm,add_left_comm,add_assoc,Nat.add_comm] using hsum0.symm)
        _= ∑ i ∈ Finset.range (k+1),Real.cos (2*Real.pi*x*i) - 1:=by simp [f]
    rw [show (∑ i ∈ Finset.range k,z i) =
        ((∑ i ∈ Finset.range k,Real.cos (2*Real.pi*x* (i+1)) : ℝ) : ℂ) by
          simp [z,Complex.ofReal_sum]]
    rw [Complex.norm_real,hsum]
    calc
      |∑ i ∈ Finset.range (k+1),Real.cos (2*Real.pi*x*i) - 1|
          ≤ |∑ i ∈ Finset.range (k+1),Real.cos (2*Real.pi*x*i) - 0| +
              |0- (1:ℝ)| :=by
              simpa using
                abs_sub_le
                  (∑ i ∈ Finset.range (k+1),Real.cos (2*Real.pi*x*i)) 0 1
      _ ≤ |∑ i ∈ Finset.range (k+1),Real.cos (2*Real.pi*x*i)| + 1:=by simp
      _ ≤ (2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖) + 1:=by
            have hcos:
                |∑ i ∈ Finset.range (k+1),Real.cos (2*Real.pi*x*i)| ≤
                  2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
              simpa using x9 hx₀ hx₁ (k+1)
            exact add_le_add hcos le_rfl
      _ ≤ 2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ +
            2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
            have hdenom:
                1 ≤ 2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
              have hnorm: ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ ≤ 2:=by
                calc
                  ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖
                      ≤ ‖(1:ℂ)‖ + ‖Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=
                        norm_sub_le _ _
                  _=1+1:=by
                        rw [norm_one]
                        simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2*Real.pi*x)
                  _=2:=by norm_num
              have hzero: (1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I) ≠ 0:=by
                intro hzero
                have hexp:Complex.exp ((2*Real.pi*x) * Complex.I) = 1:=by
                  simpa [eq_comm] using sub_eq_zero.mp hzero
                obtain ⟨m,hm⟩ :=Complex.exp_eq_one_iff.mp hexp
                have him:2*Real.pi*x= (m:ℝ) * (2*Real.pi) :=by
                  simpa using congrArg Complex.im hm
                have hm_pos: (0:ℝ) < m:=by nlinarith [Real.pi_pos,hx₀,him]
                have hm_lt_one: (m:ℝ) < 1:=by nlinarith [Real.pi_pos,hx₁,him]
                have hm_pos_int:0 < m:=by exact_mod_cast hm_pos
                have hm_lt_one_int:m < 1:=by exact_mod_cast hm_lt_one
                lia
              have hden_pos:0 < ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=
                norm_pos_iff.mpr hzero
              simpa using (one_le_div hden_pos).2 hnorm
            linarith
      _=4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by ring
  calc
    ‖∑ i ∈ Finset.range n,
        Real.cos (2*Real.pi*x* (m+i+1)) / (((m+i+1:ℕ) : ℂ) ^ (s:ℂ))‖
        = ‖∑ i ∈ Finset.range n,a (m+i) • z (m+i)‖ :=by
            congr 1
            refine Finset.sum_congr rfl fun i hi=> ?_
            have hcpow:
                (((m+i+1:ℕ) : ℂ) ^ (s:ℂ)) =
                  ((((m+i+1:ℕ) : ℝ) ^ s:ℝ) : ℂ) :=by
              simpa using
                (Complex.ofReal_cpow (x:= (m+i+1:ℝ)) (by positivity) (y:=s)).symm
            rw [hcpow]
            simp [a,z,div_eq_mul_inv,mul_comm,mul_left_comm]
    _ ≤ (2* (4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖)) * a m :=
          rA ha ha_nonneg hzbound m n
    _= (8/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖) *
          (1/ (m+1:ℝ) ^ s) :=by
          have hcoef:
              (2* (4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖)) =
                8/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
            ring
          rw [hcoef]
lemma xG {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    ∃ l :ℝ,
      Tendsto
        (fun n ↦
          ∑ i ∈ Finset.range n,if i =0 then 0 else Real.cos (2*Real.pi*x*i) / i)
        atTop (𝓝 l) :=by
  let f :ℕ → ℝ:=fun n => if n =0 then 1 else 1 /n
  let z :ℕ → ℝ:=fun n => if n =0 then 0 else Real.cos (2*Real.pi*x*n)
  have hf:Antitone f :=by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [f]
      · simp [f,hb.ne']
        have hb1: (1:ℝ) ≤ b:=by exact_mod_cast Nat.succ_le_of_lt hb
        simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hb1
    · have hb:0 < b:=lt_of_lt_of_le ha hab
      simp [f,ha.ne',(Nat.ne_of_gt hb)]
      have ha': (0:ℝ) < a:=by exact_mod_cast ha
      have hab': (a:ℝ) ≤ b:=by exact_mod_cast hab
      simpa [one_div] using one_div_le_one_div_of_le ha' hab'
  have hf0:Tendsto f atTop (𝓝 0) :=by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa [f]
      using
        (tendsto_one_div_add_atTop_nhds_zero_nat:
          Tendsto (fun n :ℕ=> 1 / (n+1:ℝ)) atTop (𝓝 0))
  have hbound:
      ∀ n,‖∑ i ∈ Finset.range n,z i‖ ≤
        4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · have:0 ≤ 4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
        positivity
      simpa [z] using this
    · let g :ℕ → ℝ:=fun i => Real.cos (2*Real.pi*x*i)
      have hz0:=Finset.sum_range_add z 1 (n-1)
      have hg0:=Finset.sum_range_add g 1 (n-1)
      have hsum:
          ∑ i ∈ Finset.range n,z i=
            ∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i) - 1:=by
        have hn':1+ (n-1) = n:=by
          simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hn
        have hz0':
            ∑ x ∈ Finset.range n,z x=
              ∑ x ∈ Finset.range 1,z x+ ∑ x ∈ Finset.range (n-1),z (1+x) :=by
          simpa [hn',add_comm] using hz0
        have hg0':
            ∑ x ∈ Finset.range n,g x=
              ∑ x ∈ Finset.range 1,g x+ ∑ x ∈ Finset.range (n-1),g (1+x) :=by
          simpa [hn',add_comm] using hg0
        rw [Finset.sum_range_one] at hz0' hg0'
        calc
          ∑ i ∈ Finset.range n,z i=z 0+ ∑ i ∈ Finset.range (n-1),z (1+i) :=by
            simpa [add_comm,add_left_comm,add_assoc,Nat.add_comm] using hz0'
          _= ∑ i ∈ Finset.range (n-1),g (1+i) :=by simp [z,g]
          _= ∑ i ∈ Finset.range n,g i-g 0:=
                eq_sub_iff_add_eq.mpr (by
                  simpa [add_comm,add_left_comm,add_assoc,Nat.add_comm] using hg0'.symm)
          _= ∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i) - 1:=by simp [g]
      rw [hsum]
      calc
        |∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i) - 1|
            ≤ |∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i) - 0| +
                |0- (1:ℝ)| :=by
                simpa using
                  abs_sub_le
                    (∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i)) 0 1
        _ ≤ |∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i)| + 1:=by simp
        _ ≤ (2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖) + 1:=by
              have hcos:
                  |∑ i ∈ Finset.range n,Real.cos (2*Real.pi*x*i)| ≤
                    2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
                simpa using x9 hx₀ hx₁ n
              exact add_le_add hcos le_rfl
        _ ≤ 2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ +
              2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
              have hnorm: ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ ≤ 2:=by
                calc
                  ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖
                      ≤ ‖(1:ℂ)‖ + ‖Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=
                        norm_sub_le _ _
                  _=1+1:=by
                        rw [norm_one]
                        simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2*Real.pi*x)
                  _=2:=by norm_num
              have hzero: (1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I) ≠ 0:=by
                intro hzero
                have hexp:Complex.exp ((2*Real.pi*x) * Complex.I) = 1:=by
                  simpa [eq_comm] using sub_eq_zero.mp hzero
                obtain ⟨m,hm⟩ :=Complex.exp_eq_one_iff.mp hexp
                have him:2*Real.pi*x= (m:ℝ) * (2*Real.pi) :=by
                  simpa using congrArg Complex.im hm
                have hm_pos: (0:ℝ) < m:=by nlinarith [Real.pi_pos,hx₀,him]
                have hm_lt_one: (m:ℝ) < 1:=by nlinarith [Real.pi_pos,hx₁,him]
                have hm_pos_int:0 < m:=by exact_mod_cast hm_pos
                have hm_lt_one_int:m < 1:=by exact_mod_cast hm_lt_one
                lia
              have hden_pos:0 < ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=
                norm_pos_iff.mpr hzero
              have hdenom:
                  1 ≤ 2/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
                simpa using (one_le_div hden_pos).2 hnorm
              linarith
        _=4/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by ring
  have hcauchy:=hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l,hl⟩ :=cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l,?_⟩
  have hseries:
      (fun n ↦ ∑ i ∈ Finset.range n,f i • z i) =
        fun n ↦
          ∑ i ∈ Finset.range n,if i =0 then 0 else Real.cos (2*Real.pi*x*i) / i:=by
    funext n
    refine Finset.sum_congr rfl fun i _=> ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f,z]
    · simp [f,z,hi.ne',smul_eq_mul,div_eq_mul_inv,mul_comm]
  exact hseries ▸ hl
lemma zU {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n,if i =0 then 0 else Real.cos (2*Real.pi*x*i) / i)
      atTop (𝓝 (-Real.log (2*Real.sin (Real.pi*x)))) :=by
  obtain ⟨l,hl⟩ :=xG hx₀ hx₁
  let coeff:ℕ → ℝ:=fun n =>
    if n =0 then 0 else Real.cos (2*Real.pi*x*n) / n
  have habel:
      Tendsto (fun r :ℝ=> ∑' n,coeff n *r^n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff:
      Set.EqOn
        (fun r :ℝ=> ∑' n,coeff n *r^n)
        (fun r :ℝ=>
          -Real.log ‖(1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)‖)
        (Set.Ioo 0 1) :=by
    intro r hr
    have hr₀:0 ≤ r:=hr.1.le
    have hr₁:r < 1:=hr.2
    calc
      ∑' n :ℕ,coeff n *r^n
          = ∑' n :ℕ,(r^n/n) * Real.cos (2*Real.pi*x*n) :=by
              refine tsum_congr fun n :ℕ=> ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff,hn.ne',div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
      _= -Real.log ‖(1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=
            (t0 x r hr₀ hr₁).tsum_eq
  have habel':
      Tendsto
        (fun r :ℝ=>
          -Real.log ‖(1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)‖)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hzero:
      (1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I) ≠ 0:=by
    intro hzero
    have hexp:Complex.exp ((2*Real.pi*x) * Complex.I) = 1:=by
      simpa [eq_comm] using sub_eq_zero.mp hzero
    obtain ⟨m,hm⟩ :=Complex.exp_eq_one_iff.mp hexp
    have him:2*Real.pi*x= (m:ℝ) * (2*Real.pi) :=by
      simpa using congrArg Complex.im hm
    have hm_pos: (0:ℝ) < m:=by nlinarith [Real.pi_pos,hx₀,him]
    have hm_lt_one: (m:ℝ) < 1:=by nlinarith [Real.pi_pos,hx₁,him]
    have hm_pos_int:0 < m:=by exact_mod_cast hm_pos
    have hm_lt_one_int:m < 1:=by exact_mod_cast hm_lt_one
    lia
  have hcont:
      Tendsto
        (fun r :ℝ=>
          -Real.log ‖(1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)‖)
        (𝓝[<] 1)
        (𝓝 (-Real.log ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖)) :=by
    have hinner:
        ContinuousAt
          (fun r :ℝ=> (1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)) 1 :=
      continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have hnorm:
        ContinuousAt
          (fun r :ℝ=>
            ‖(1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)‖) 1 :=
      continuous_norm.continuousAt.comp hinner
    have hnorm_ne:
        ‖(1:ℂ) - ((1:ℝ) : ℂ) *
            Complex.exp ((2*Real.pi*x) * Complex.I)‖ ≠ 0:=by
      simpa using (norm_ne_zero_iff.mpr hzero)
    have hlog:
        ContinuousAt
          (fun r :ℝ=>
            Real.log ‖(1:ℂ) - (r:ℂ) * Complex.exp ((2*Real.pi*x) * Complex.I)‖) 1 :=
      hnorm.log hnorm_ne
    convert! tendsto_nhdsWithin_of_tendsto_nhds hlog.neg.tendsto using 2
    simp
  have ht₀:0 < 2*Real.pi*x:=by nlinarith [hx₀,Real.pi_pos]
  have ht₂π:2*Real.pi*x < 2*Real.pi:=by nlinarith [hx₁,Real.pi_pos]
  have hnorm_value:
      ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ =
        2*Real.sin (Real.pi*x) :=by
    simpa [show (2*Real.pi*x) / 2=Real.pi*x by ring] using
      rN ht₀ ht₂π
  have hl_eq:l= -Real.log (2*Real.sin (Real.pi*x)) :=
    tendsto_nhds_unique habel' (by simpa [hnorm_value] using hcont)
  simpa [hl_eq] using hl
lemma zk {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    Tendsto
      (fun n :ℕ=> ∑ i ∈ Finset.range n,
        Real.cos (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (1:ℂ)))
      atTop (nhds ((-Real.log (2*Real.sin (Real.pi*x)) : ℝ) : ℂ)) :=by
  let F :ℕ → ℂ:=fun n =>
    ((∑ i ∈ Finset.range n,
        if i =0 then 0 else Real.cos (2*Real.pi*x*i) / i:ℝ) : ℂ)
  have hbase:Tendsto F atTop (nhds (((-Real.log (2*Real.sin (Real.pi*x)) : ℝ) : ℂ))) :=by
    simpa [F] using (zU hx₀ hx₁).ofReal
  have hshifted:Tendsto (fun n :ℕ=> F (n+1)) atTop
      (nhds (((-Real.log (2*Real.sin (Real.pi*x)) : ℝ) : ℂ))) :=
    (tendsto_add_atTop_iff_nat 1).2 hbase
  refine hshifted.congr' <| Filter.Eventually.of_forall fun n => ?_
  have hsum:=
    Finset.sum_range_add
      (fun i :ℕ=> (((if i =0 then 0 else Real.cos (2*Real.pi*x*i) / i:ℝ)) : ℂ)) 1 n
  simpa [F,add_comm,add_left_comm,add_assoc] using hsum
lemma wY {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    UniformCauchySeqOn
      (fun n (s:ℝ) => ∑ i ∈ Finset.range n,
        Real.cos (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ)))
      atTop (Set.Ici 1) :=by
  rw [Metric.uniformCauchySeqOn_iff]
  let B :ℝ:=
    8/ ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖
  have hdenom:0 < ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ :=by
    have ht₀:0 < 2*Real.pi*x:=by nlinarith [hx₀,Real.pi_pos]
    have ht₂π:2*Real.pi*x < 2*Real.pi:=by nlinarith [hx₁,Real.pi_pos]
    have hnorm_eq:
        ‖(1:ℂ) - Complex.exp ((2*Real.pi*x) * Complex.I)‖ =
          2*Real.sin (Real.pi*x) :=by
      simpa [show (2*Real.pi*x) / 2=Real.pi*x by ring] using
        rN ht₀ ht₂π
    rw [hnorm_eq]
    have hxπ:Real.pi*x ∈ Set.Ioo 0 Real.pi:=by
      constructor <;> nlinarith [hx₀,hx₁,Real.pi_pos]
    have hsin:0 < Real.sin (Real.pi*x) :=Real.sin_pos_of_mem_Ioo hxπ
    positivity
  have hB_pos:0 < B:=by
    positivity
  intro ε hε
  obtain ⟨N,hN⟩ :=exists_nat_one_div_lt (div_pos hε hB_pos)
  refine ⟨N,?_⟩
  have htail_bound:
      ∀ ⦃m n :ℕ⦄,N ≤ m → m ≤ n → ∀ s ∈ Set.Ici (1:ℝ),
        dist
            (∑ i ∈ Finset.range m,
              Real.cos (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ)))
            (∑ i ∈ Finset.range n,
              Real.cos (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ)))
          < ε :=by
    intro m n hm hmn s hs
    let term:ℕ → ℂ:=fun k =>
      Real.cos (2*Real.pi*x* (k+1)) / ((k+1:ℂ) ^ (s:ℂ))
    have hsplit:
        ∑ i ∈ Finset.range n,term i =
          ∑ i ∈ Finset.range m,term i + ∑ i ∈ Finset.range (n-m),term (m+i) :=by
      simpa [term,Nat.add_sub_of_le hmn] using Finset.sum_range_add term m (n-m)
    have hs':1 ≤ s:=hs
    rw [dist_eq_norm,norm_sub_rev]
    calc
      ‖∑ i ∈ Finset.range n,term i - ∑ i ∈ Finset.range m,term i‖
          = ‖∑ i ∈ Finset.range (n-m),term (m+i)‖ :=by
              rw [hsplit]
              ring_nf
      _ ≤ B* (1/ (m+1:ℝ) ^ s) :=by
            simpa [B,term,add_assoc,add_comm,add_left_comm] using
              z7 (x:=x) hx₀ hx₁ hs' m (n-m)
      _ ≤ B* (1/ (m+1:ℝ)) :=by
            have hm1:1 ≤ (m+1:ℝ) :=by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            have hpow: (m+1:ℝ) ^ (1:ℝ) ≤ (m+1:ℝ) ^ s:=by
              simpa using Real.rpow_le_rpow_of_exponent_le hm1 hs'
            have hpow_inv:1/ (m+1:ℝ) ^ s ≤ 1/ (m+1:ℝ) :=by
              simpa [Real.rpow_one] using
                (one_div_le_one_div_of_le (show 0 < (m+1:ℝ) ^ (1:ℝ) by positivity) hpow)
            exact mul_le_mul_of_nonneg_left hpow_inv hB_pos.le
      _ ≤ B* (1/ (N+1:ℝ)) :=by
            have hm_inv:1/ (m+1:ℝ) ≤ 1/ (N+1:ℝ) :=
              one_div_le_one_div_of_le (show 0 < (N+1:ℝ) by positivity)
                (by exact_mod_cast Nat.succ_le_succ hm)
            exact mul_le_mul_of_nonneg_left hm_inv hB_pos.le
      _ < B* (ε/B) :=
            mul_lt_mul_of_pos_left hN hB_pos
      _=ε:=by
            field_simp [hB_pos.ne']
  intro m hm n hn s hs
  rcases le_total m n with hmn | hnm
  · exact htail_bound hm hmn s hs
  · simpa [dist_comm] using htail_bound hn hnm s hs
theorem yx {x:ℝ} (hx₀:0 < x) (hx₁:x < 1) :
    HurwitzZeta.cosZeta x 1= (((-Real.log (2*Real.sin (Real.pi*x)) : ℝ) : ℂ)) :=by
  let boundary:ℂ:= (((-Real.log (2*Real.sin (Real.pi*x)) : ℝ) : ℂ))
  let S :ℕ → ℝ → ℂ:=fun n s=>
    ∑ i ∈ Finset.range n,
      Real.cos (2*Real.pi*x* (i+1)) / ((i+1:ℂ) ^ (s:ℂ))
  let G :ℝ → ℂ:=fun s => if hs:s=1 then boundary else HurwitzZeta.cosZeta x s
  have hCauchy:UniformCauchySeqOn S atTop (Set.Ici 1) :=by
    simpa [S] using wY (x:=x) hx₀ hx₁
  have hpoint: ∀ s ∈ Set.Ici (1:ℝ),Tendsto (fun n => S n s) atTop (𝓝 (G s)) :=by
    intro s hs
    by_cases hs1:s=1
    · simpa [S,G,hs1,boundary] using zk (x:=x) hx₀ hx₁
    · have hslt:1 < s:=lt_of_le_of_ne hs (by simpa [eq_comm] using hs1)
      simpa [S,G,hs1] using (yG (x:=x) s hslt).tendsto_sum_nat
  have hunif:TendstoUniformlyOn S G atTop (Set.Ici 1) :=
    hCauchy.tendstoUniformlyOn_of_tendsto hpoint
  have hcont:ContinuousOn G (Set.Ici (1:ℝ)) :=by
    apply hunif.continuousOn
    refine Frequently.of_forall fun n => ?_
    classical
    dsimp [S]
    exact Continuous.continuousOn <|
      continuous_finsetSum _ fun i _=> yj x i
  have hG_right:Tendsto G (𝓝[Set.Ioi 1] 1) (𝓝 boundary) :=by
    have hG_Ici:Tendsto G (𝓝[Set.Ici 1] 1) (𝓝 boundary) :=by
      simpa [G,boundary] using (hcont 1 (by simp)).tendsto
    exact hG_Ici.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hG_eq:G=ᶠ[𝓝[Set.Ioi 1] 1] fun s :ℝ=> HurwitzZeta.cosZeta x s:=by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hslt:1 < s:=by simpa using hs
    simp [G,ne_of_gt hslt]
  have hcos_right:Tendsto (fun s :ℝ=> HurwitzZeta.cosZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 boundary) :=
    Tendsto.congr' hG_eq hG_right
  have hcos_cont:Tendsto (fun s :ℝ=> HurwitzZeta.cosZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 (HurwitzZeta.cosZeta x 1)) :=by
    have hxadd: (x:UnitAddCircle) ≠ 0:=by
      intro hxzero
      rw [AddCircle.coe_eq_zero_iff] at hxzero
      rcases hxzero with ⟨n,hn⟩
      have hn': (n:ℝ) = x:=by simpa using hn
      have hn_pos: (0:ℝ) < n:=by nlinarith [hx₀,hn']
      have hn_lt_one: (n:ℝ) < 1:=by nlinarith [hx₁,hn']
      have hn_pos_int:0 < n:=by exact_mod_cast hn_pos
      have hn_lt_one_int:n < 1:=by exact_mod_cast hn_lt_one
      lia
    have hcomplex:Tendsto (fun z :ℂ=> HurwitzZeta.cosZeta x z) (𝓝 (1:ℂ))
        (𝓝 (HurwitzZeta.cosZeta x 1)) :=
      (HurwitzZeta.differentiableAt_cosZeta (a:= (x:UnitAddCircle)) (s:= (1:ℂ))
        (Or.inr hxadd)).continuousAt.tendsto
    have hreal:Tendsto (fun s :ℝ=> (s:ℂ)) (𝓝 (1:ℝ)) (𝓝 (1:ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have hcomp:Tendsto (fun s :ℝ=> HurwitzZeta.cosZeta x (s:ℂ)) (𝓝 (1:ℝ))
        (𝓝 (HurwitzZeta.cosZeta x 1)) :=by
      simpa [Function.comp] using! hcomplex.comp hreal
    exact hcomp.mono_left nhdsWithin_le_nhds
  simpa [boundary] using (tendsto_nhds_unique hcos_right hcos_cont).symm
theorem xY {a:ZMod p} (ha:a ≠ 0) :
    HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
      (((-Real.log (2*Real.sin (Real.pi* (a.val/p:ℝ))) : ℝ) : ℂ)) :=by
  have hx:=sP (p:=p) ha
  rw [ZMod.toAddCircle_apply]
  exact yx (x:= (a.val/p:ℝ)) hx.1 hx.2
lemma yv {a:ZMod p} (ha:a ≠ 0) :
    ‖(1:ℂ) - ZMod.stdAddChar (N:=p) a‖ =
      2*Real.sin (Real.pi* (a.val/p:ℝ)) :=by
  have hx:=sP (p:=p) ha
  have ht₀:0 < 2*Real.pi* (a.val/p:ℝ) :=by
    nlinarith [hx.1,Real.pi_pos]
  have ht₂π:2*Real.pi* (a.val/p:ℝ) < 2*Real.pi:=by
    nlinarith [hx.2,Real.pi_pos]
  rw [ZMod.stdAddChar_apply,ZMod.toCircle_apply]
  have hexp:
      Complex.exp (2* (Real.pi:ℂ) * Complex.I* (a.val:ℂ) / (p:ℂ)) =
        Complex.exp ((((2*Real.pi* (a.val/p:ℝ)) : ℝ) : ℂ) * Complex.I) :=by
    congr 1
    push_cast
    ring
  rw [hexp]
  convert rN ht₀ ht₂π using 1
  ring_nf
end LValueAtOne
end KummerCriterion
end
end Module29
-- Source: KummerCriterion.LValueAtOne.Even
section Module30
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p:ℕ) [hp:Fact p.Prime]
theorem xX
    {χ:DirichletCharacter ℂ p} (hχ_prim:χ.IsPrimitive) (hχ_even:χ.Even)
    (hχ_ne_one:χ ≠ 1) :
    DirichletCharacter.LFunction χ 1=ra p χ:=by
  let _ :=hχ_prim
  change ZMod.LFunction (fun a :ZMod p => χ a) 1 =ra p χ
  have hp_ne_one:p ≠ 1:=hp.out.ne_one
  have hχinv_ne_one:χ⁻¹ ≠ 1:=by
    intro h
    apply hχ_ne_one
    calc
      χ=χ⁻¹⁻¹:= (inv_inv χ).symm
      _=1:=by simp [h]
  have hχinv_even: (χ⁻¹).Even:=by
    rw [DirichletCharacter.Even] at hχ_even ⊢
    rw [MulChar.inv_apply_eq_inv',hχ_even]
    simp
  have hχinv_prim: (χ⁻¹).IsPrimitive:=by
    rw [DirichletCharacter.isPrimitive_def]
    have hdiv: (χ⁻¹).conductor ∣ p:=DirichletCharacter.conductor_dvd_level (χ⁻¹)
    rcases (Nat.dvd_prime hp.out).mp hdiv with hcond | hcond
    · exact (hχinv_ne_one <| (DirichletCharacter.eq_one_iff_conductor_eq_one).2 hcond).elim
    · exact hcond
  have hχinv_zero:χ⁻¹ 0 =0:= (χ⁻¹).map_zero' hp_ne_one
  let χinv:ZMod p → ℂ :=fun a => χ⁻¹ a
  have hdft:
      ZMod.LFunction (ZMod.dft χinv) 1 =
        ∑ a :ZMod p,χ⁻¹ a *HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 :=by
    simpa using
      (ZMod.LFunction_dft (Φ:=χinv) (s:= (1:ℂ))
        (hs:=Or.inl hχinv_zero))
  have hft:
      ZMod.dft χinv=fun a :ZMod p =>
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * χ a :=by
    funext a
    simpa [χinv,hχ_even.to_fun a,mul_comm] using
      (DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ:=χ⁻¹) hχinv_prim a)
  have hleft:
      ZMod.LFunction (ZMod.dft χinv) 1 =
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * ZMod.LFunction χ 1:=by
    rw [hft,ZMod.LFunction,ZMod.LFunction]
    calc
      (p:ℂ) ^ (-1:ℂ) *
          ∑ a :ZMod p,
            (gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * χ a) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1
          = (p:ℂ) ^ (-1:ℂ) *
              (gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) *
                ∑ a :ZMod p,χ a*HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1) :=by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _=> by ring
      _=gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * ZMod.LFunction χ 1:=by
            rw [ZMod.LFunction]
            ring
  have hsum_sin_zero:
      ∑ a :ZMod p,χ⁻¹ a *HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 =0:=by
    refine (hχinv_even.to_fun.mul_odd fun a => ?_).sum_eq_zero
    simpa using HurwitzZeta.sinZeta_neg (ZMod.toAddCircle a) (1:ℂ)
  have hsum_isin_zero:
      ∑ a :ZMod p,χ⁻¹ a *
          (Complex.I*HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) = 0:=by
    calc
      ∑ a :ZMod p,χ⁻¹ a * (Complex.I*HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)
          =Complex.I*
              ∑ a :ZMod p,χ⁻¹ a *HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 :=by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _=> by ring
      _=0:=by rw [hsum_sin_zero,mul_zero]
  have hsum_exp:
      ∑ a :ZMod p,χ⁻¹ a *HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 =
        ∑ a :ZMod p,χ⁻¹ a *HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 :=by
    calc
      ∑ a :ZMod p,χ⁻¹ a *HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1
          = ∑ a:ZMod p,
              (χ⁻¹ a *HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
                χ⁻¹ a * (Complex.I*HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)) :=by
                  refine Finset.sum_congr rfl fun a _=> ?_
                  have hneg:ZMod.toAddCircle (-a) = -ZMod.toAddCircle a :=
                    map_neg ZMod.toAddCircle a
                  rw [hneg,HurwitzZeta.expZeta,HurwitzZeta.cosZeta_neg,
                    HurwitzZeta.sinZeta_neg]
                  ring
      _= ∑ a:ZMod p,χ⁻¹ a *HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
            ∑ a :ZMod p,
              χ⁻¹ a * (Complex.I*HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) :=by
            rw [Finset.sum_sub_distrib]
      _= ∑ a:ZMod p,χ⁻¹ a *HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 :=by
            rw [hsum_isin_zero,sub_zero]
  have hboundary:
      ∑ a :ZMod p,χ⁻¹ a *HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
        -u4 p χ:=by
    unfold u4
    calc
      ∑ a :ZMod p,χ⁻¹ a *HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1
          = ∑ a:ZMod p,
              -(χ⁻¹ a *
                ((Real.log ‖(1:ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ)) :=by
                  refine Finset.sum_congr rfl fun a _=> ?_
                  rcases eq_or_ne a 0 with rfl | ha
                  · simp [hχinv_zero]
                  · rw [xY (p:=p) ha]
                    have hlog:
                        ((Real.log ‖(1:ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ) =
                          ((Real.log
                            (2*Real.sin (Real.pi* (a.val/p:ℝ))) : ℝ) : ℂ) :=by
                      congr 1
                      rw [yv (p:=p) ha]
                    rw [hlog]
                    rw [show
                      (((-Real.log (2*Real.sin (Real.pi* (a.val/p:ℝ))) : ℝ) : ℂ)) =
                        -(((Real.log
                          (2*Real.sin (Real.pi* (a.val/p:ℝ))) : ℝ) : ℂ)) by simp]
                    exact mul_neg (χ⁻¹ a)
                      (((Real.log (2*Real.sin (Real.pi* (a.val/p:ℝ))) : ℝ) : ℂ))
      _= -∑ a :ZMod p,
            χ⁻¹ a * ((Real.log ‖(1:ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ) :=
              Finset.sum_neg_distrib
                (s:=Finset.univ)
                (f:=fun a :ZMod p =>
                  χ⁻¹ a * ((Real.log ‖(1:ℂ) - ZMod.stdAddChar (N:=p) a‖ : ℝ) : ℂ))
      _= -u4 p χ:=rfl
  have hcard_ne: (Fintype.card (ZMod p) : ℂ) ≠ 0:=by
    simpa [ZMod.card] using (show (p:ℂ) ≠ 0 by exact_mod_cast hp.out.ne_zero)
  have hgauss_ne:gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) ≠ 0:=
    gaussSum_ne_zero_of_nontrivial hcard_ne hχinv_ne_one (ZMod.isPrimitive_stdAddChar p)
  apply (mul_left_cancel₀ hgauss_ne)
  calc
    gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * ZMod.LFunction χ 1
        =ZMod.LFunction (ZMod.dft χinv) 1 :=hleft.symm
    _= ∑ a:ZMod p,χ⁻¹ a *HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 :=hdft
    _= ∑ a:ZMod p,χ⁻¹ a *HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 :=hsum_exp
    _= -u4 p χ:=hboundary
    _=gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) * ra p χ:=by
          simp [ra,hgauss_ne,mul_left_comm,mul_comm]
end LValueAtOne
end KummerCriterion
end
end Module30
-- Source: KummerCriterion.HMinus.LValueReduction.LValues
section Module31
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section LValues
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem xC:
    vx p (1:ℂ) =
      Finset.prod (q8 (p:=p)) fun χ => u9 p χ:=by
  classical
  unfold vx
  refine Finset.prod_congr rfl fun χ hχ=> ?_
  have hχ_odd:χ.Odd:= (Finset.mem_filter.mp hχ).2
  have hχ_ne_one:χ ≠ 1:=by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ_odd (by
      change (1:DirichletCharacter ℂ p) (-1) = 1
      rw [MulChar.one_apply (isUnit_one.neg)])
  simpa using zn (p:=p)
    (hχ_prim:=DirichletCharacter.isPrimitive_of_ne_one (p:=p) hχ_ne_one)
    (hχ_odd:=hχ_odd) (hχ_ne_one:=hχ_ne_one)
theorem sN:
    r1 p (1:ℂ) =
      Finset.prod (qi (p:=p)) fun χ => ra p χ:=by
  classical
  unfold r1
  refine Finset.prod_congr rfl fun χ hχ=> ?_
  have hχ_mem:=Finset.mem_filter.mp hχ
  have hχ_even:χ.Even:=hχ_mem.2.1
  have hχ_ne_one:χ ≠ 1:=hχ_mem.2.2
  simpa using xX (p:=p)
    (hχ_prim:=DirichletCharacter.isPrimitive_of_ne_one (p:=p) hχ_ne_one)
    (hχ_even:=hχ_even) (hχ_ne_one:=hχ_ne_one)
lemma s4 (hp_odd':p ≠ 2) :
    (q8 (p:=p)).card= (p-1) / 2:=by
  classical
  let E :Finset (DirichletCharacter ℂ p) :=Finset.univ.filter fun χ => χ.Even
  let O :Finset (DirichletCharacter ℂ p) :=q8 (p:=p)
  have hdisj:Disjoint E O:=by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even:χ.Even:=by simpa [E] using hχE
    have hχ_odd:χ.Odd:=by simpa [O,q8] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion:E ∪ O= (Finset.univ:Finset (DirichletCharacter ℂ p)) :=by
    ext χ
    simp only [E,O,q8,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,
      true_and,iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hcard_total:E.card+O.card=p-1:=by
    calc
      E.card+O.card= (E ∪ O).card:=by
        rw [← Finset.card_union_of_disjoint hdisj]
      _=Nat.card (DirichletCharacter ℂ p) :=by
        rw [hunion,Finset.card_univ,Nat.card_eq_fintype_card]
      _=p-1:=qH (p:=p)
  have hcard_even:E.card= (p-1) / 2:=vl (p:=p) hp_odd'
  rcases hp.out.odd_of_ne_two hp_odd' with ⟨m,hm⟩
  have hhalf: (p-1) / 2=m:=by omega
  rw [hhalf] at hcard_even
  have hcard_odd:O.card=m:=by omega
  rw [hhalf]
  simpa [O,q8] using hcard_odd
theorem sG
    {χ:DirichletCharacter ℂ p} (hχ_odd:χ.Odd) :
    gaussSum χ (ZMod.stdAddChar (N:=p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N:=p)) =
      -(p:ℂ) :=by
  have hχ_ne_one:χ ≠ 1:=by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ_odd (by
      change (1:DirichletCharacter ℂ p) (-1) = 1
      rw [MulChar.one_apply (isUnit_one.neg)])
  rw [xE (p:=p) (χ:=χ) hχ_ne_one]
  rw [DirichletCharacter.Odd] at hχ_odd
  rw [hχ_odd]
  simp
theorem rL
    (hp_odd':p ≠ 2) {χ:DirichletCharacter ℂ p}
    (hχ_odd:χ.Odd) (hχself:χ=χ⁻¹) :
    χ=q3 p :=by
  have hχ_ne_one:χ ≠ 1:=by
    rintro rfl
    exact DirichletCharacter.Odd.not_even _ hχ_odd (by
      change (1:DirichletCharacter ℂ p) (-1) = 1
      rw [MulChar.one_apply (isUnit_one.neg)])
  exact sm (p:=p) hp_odd' hχ_ne_one hχself
theorem vt
    (hp_odd':p ≠ 2) (hp₄:p%4=3) :
    (q3 p).Odd:=by
  simpa [DirichletCharacter.Odd] using
    rg (p:=p) hp_odd' hp₄
theorem wE
    (hp_odd':p ≠ 2) {χ:DirichletCharacter ℂ p}
    (hχ_odd:χ.Odd) (hχself:χ=χ⁻¹) :
    p%4=3:=by
  have hquad:χ=q3 p :=
    rL (p:=p) hp_odd' hχ_odd hχself
  have hquad_odd: (q3 p).Odd:=by simpa [hquad] using hχ_odd
  have hneg:q3 p (-1:ZMod p) = -1:=by
    simpa [DirichletCharacter.Odd] using hquad_odd
  have hmod1_ne:p%4 ≠ 1:=by
    intro hp₄
    rw [vu (p:=p) hp_odd' hp₄] at hneg
    norm_num at hneg
  rcases hp.out.odd_of_ne_two hp_odd' with ⟨k,hk⟩
  have hp_mod2:p%2=1:=by
    omega
  have hp_mod4_lt:p%4 < 4:=Nat.mod_lt _ (by decide)
  omega
theorem sK
    (hp_odd':p ≠ 2) (hp₄:p%4=1) {χ:DirichletCharacter ℂ p}
    (hχ_odd:χ.Odd) :
    χ ≠ χ⁻¹:=by
  intro hχself
  have hp₄':=wE (p:=p) hp_odd' hχ_odd hχself
  omega
theorem sB (hp_odd':p ≠ 2) :
    Finset.prod (q8 (p:=p)) (fun χ =>
      ((((Real.pi:ℝ) : ℂ) * Complex.I) *
        gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ))) =
      (((((Real.pi:ℝ) : ℂ) * Complex.I) / (p:ℂ)) ^ ((p-1) / 2)) *
        Finset.prod (q8 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) :=by
  let C :ℂ:= ((((Real.pi:ℝ) : ℂ) * Complex.I) / (p:ℂ))
  have hp_ne: (p:ℂ) ≠ 0:=Nat.cast_ne_zero.mpr hp.out.ne_zero
  calc
    Finset.prod (q8 (p:=p)) (fun χ =>
        ((((Real.pi:ℝ) : ℂ) * Complex.I) *
          gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ))) =
      Finset.prod (q8 (p:=p)) (fun χ =>
        C*gaussSum χ (ZMod.stdAddChar (N:=p))) :=by
          refine Finset.prod_congr rfl ?_
          intro χ hχ
          dsimp [C]
          field_simp [hp_ne]
    _=
      (Finset.prod (q8 (p:=p)) (fun _ :DirichletCharacter ℂ p=> C)) *
        Finset.prod (q8 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) :=by
            rw [Finset.prod_mul_distrib]
    _=
      (C^ (q8 (p:=p)).card) *
        Finset.prod (q8 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) :=by
            rw [Finset.prod_const]
    _=
      (C^ ((p-1) / 2)) *
        Finset.prod (q8 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) :=by
            rw [s4 (p:=p) hp_odd']
    _=
      (((((Real.pi:ℝ) : ℂ) * Complex.I) / (p:ℂ)) ^ ((p-1) / 2)) *
        Finset.prod (q8 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) :=by
            rfl
theorem zW (hp_odd':p ≠ 2) :
    ((hPlus K :ℕ) : ℂ) =
      ql (K:=K) * r1 p (1:ℂ) :=
  zM (K:=K)
    (KplusResidue:=r1 p (1:ℂ))
    (vc (p:=p) (K:=K) hp_odd')
theorem zL (hp_odd':p ≠ 2) :
    ((hPlus K :ℕ) : ℂ) =
      ql (K:=K) *
        Finset.prod (qi (p:=p)) (fun χ => ra p χ) :=by
  calc
    ((hPlus K :ℕ) : ℂ) =
        ql (K:=K) * r1 p (1:ℂ) :=
          zW (p:=p) (K:=K) hp_odd'
    _=
        ql (K:=K) *
          Finset.prod (qi (p:=p)) (fun χ => ra p χ) :=by
            rw [sN (p:=p)]
theorem wr (hp_odd':p ≠ 2) :
    ((hPlus K :ℕ) : ℂ) =
      rj (K:=K) *
        Finset.prod (qi (p:=p)) (fun χ => ra p χ) :=by
  simpa [rj] using
    (zL (p:=p) (K:=K) hp_odd')
theorem y2 (hp_odd':p ≠ 2) :
    ((hPlus K :ℕ) : ℂ) =
      rj (K:=K) *
        Finset.prod (qi (p:=p)) (fun χ => ra p χ) :=
  wr (p:=p) (K:=K) hp_odd'
theorem uF:
    Finset.prod (q8 (p:=p)) (fun χ => u9 p χ) =
      Finset.prod (q8 (p:=p)) (fun χ =>
        ((((Real.pi:ℝ) : ℂ) * Complex.I) *
          gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ))) *
        Finset.prod (q8 (p:=p)) (fun χ => qf χ⁻¹ 1) :=by
  classical
  unfold u9
  rw [Finset.prod_mul_distrib]
end LValues
end KummerCriterion
end
end Module31
-- Source: KummerCriterion.HMinus.LValueReduction.GaussGoal
section Module32
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section GaussGoal
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
def sh:Prop:=
  qF (p:=p) (K:=K) *
      Finset.prod (q8 (p:=p)) (fun χ =>
        ((((Real.pi:ℝ) : ℂ) * Complex.I) *
          gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ))) =
    (2*p:ℂ) *
      Finset.prod (q8 (p:=p))
        (fun _ :DirichletCharacter ℂ p=> (-(1/2:ℂ)))
theorem x4
    (hp_odd':p ≠ 2) :
    sh (p:=p) K ↔
      Finset.prod (q8 (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) =
        (Complex.I^ ((p-1) / 2)) *
          ((((Real.sqrt ((p:ℝ) ^ ((p-1) / 2)) : ℝ) : ℂ))) :=by
  let n :ℕ:= (p-1) / 2
  let S :ℂ:= (((Real.sqrt ((p:ℝ) ^ n) : ℝ) : ℂ))
  let G :ℂ:=
    Finset.prod (q8 (p:=p))
      (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p)))
  have hp_pos:0 < (p:ℝ) :=by
    exact_mod_cast hp.out.pos
  have hp_ne: (p:ℂ) ≠ 0:=by
    exact_mod_cast hp.out.ne_zero
  have hI_ne:Complex.I^n ≠ 0:=
    pow_ne_zero _ Complex.I_ne_zero
  have hS_ne:S ≠ 0:=by
    dsimp [S]
    exact Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 <| pow_pos hp_pos _)
  have h2p_ne: (2*p:ℂ) ≠ 0:=by
    exact_mod_cast Nat.mul_ne_zero two_ne_zero hp.out.ne_zero
  have hpi_ne: (((Real.pi:ℝ) : ℂ)) ≠ 0:=by
    exact_mod_cast Real.pi_ne_zero
  have htwo_pow_ne: ((2:ℂ) ^ n) ≠ 0:=
    pow_ne_zero _ (by norm_num)
  have hpow_pi_ne: ((((2*Real.pi) ^ n:ℝ) : ℂ)) ≠ 0:=by
    exact_mod_cast pow_ne_zero n (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hpow_nonneg:0 ≤ (p:ℝ) ^ n:=by
    positivity
  have hS_sq:S^2= (p:ℂ) ^ n:=by
    dsimp [S]
    calc
      ((((Real.sqrt ((p:ℝ) ^ n) : ℝ) : ℂ)) ^ 2)
          = ((((p:ℝ) ^ n:ℝ) : ℂ)) :=by
              rw [pow_two,← Complex.ofReal_mul]
              simp [hpow_nonneg]
      _= (p:ℂ) ^ n:=by
              norm_num
  have hneg_half_pow: (-(1/2:ℂ)) ^ n= ((-1:ℂ) ^ n) / (2:ℂ) ^ n:=by
    rw [show (-(1/2:ℂ)) = (-1:ℂ) / 2 by norm_num,div_pow]
  have hscalar:
      ((((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ n)) /
            (2*Real.pi) ^ n:ℝ) : ℂ) *
          (((((Real.pi:ℝ) : ℂ) * Complex.I) / (p:ℂ)) ^ n)) =
        (((2*p:ℂ) * (Complex.I^n)) / (((2:ℂ) ^ n) * S)) :=by
    have hpi_pow_ne: (((Real.pi:ℝ) : ℂ) ^ n) ≠ 0:=
      pow_ne_zero _ hpi_ne
    have hp_pow_ne: (p:ℂ) ^ n ≠ 0:=
      pow_ne_zero _ hp_ne
    rw [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,div_pow,mul_pow]
    rw [show (((2*Real.pi:ℝ) : ℂ)) =
        (2:ℂ) * (((Real.pi:ℝ) : ℂ)) by norm_num,mul_pow]
    rw [← hS_sq]
    field_simp [hS_ne,hp_pow_ne,hpi_pow_ne,htwo_pow_ne]
    simp [S,mul_assoc,mul_comm]
  have hI_twice:
      (Complex.I^n) * ((Complex.I^n) * S) = ((-1:ℂ) ^ n) * S:=by
    calc
      (Complex.I^n) * ((Complex.I^n) * S) = (Complex.I^ (n+n)) * S:=by
        rw [← mul_assoc,← pow_add]
      _= (Complex.I^ (2*n)) * S:=by
        congr 1
        rw [two_mul]
      _= ((Complex.I^2) ^ n) * S:=by rw [pow_mul]
      _= ((-1:ℂ) ^ n) * S:=by rw [Complex.I_sq]
  have hI_sq_pow: (Complex.I^n) ^ 2= (-1:ℂ) ^ n:=by
    calc
      (Complex.I^n) ^ 2=Complex.I^ (n*2) :=by rw [pow_mul]
      _=Complex.I^ (2*n) :=by
            congr 1
            ring
      _= (Complex.I^2) ^ n:=by rw [pow_mul]
      _= (-1:ℂ) ^ n:=by rw [Complex.I_sq]
  constructor
  · intro h
    rw [sh,sB (p:=p) hp_odd',
      ss (p:=p) (K:=K) hp_odd',
      Finset.prod_const] at h
    rw [s4 (p:=p) hp_odd'] at h
    have h0:
      ((((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ n)) /
          (2*Real.pi) ^ n:ℝ) : ℂ) *
        ((((Real.pi:ℝ) : ℂ) * Complex.I) / (p:ℂ)) ^ n*G=
        (2*p:ℂ) * (-(1/2:ℂ)) ^ n) :=by
          simpa [n,G,mul_assoc] using h
    have hmid: (Complex.I^n) * G= ((-1:ℂ) ^ n) * S:=by
      rw [hscalar,hneg_half_pow] at h0
      have h':=h0
      field_simp [h2p_ne,hS_ne,htwo_pow_ne] at h'
      simpa [mul_assoc,mul_left_comm,mul_comm] using h'
    apply mul_left_cancel₀ hI_ne
    calc
      (Complex.I^n) * G= ((-1:ℂ) ^ n) * S:=hmid
      _= (Complex.I^n) * ((Complex.I^n) * S) :=hI_twice.symm
  · intro hraw
    have hraw':G= (Complex.I^n) * S:=by
      simpa [n,G,S] using hraw
    have hgoal:
      ((((((2*p:ℕ) : ℝ) * Real.sqrt ((p:ℝ) ^ n)) /
          (2*Real.pi) ^ n:ℝ) : ℂ) *
        ((((Real.pi:ℝ) : ℂ) * Complex.I) / (p:ℂ)) ^ n*G=
        (2*p:ℂ) * (-(1/2:ℂ)) ^ n) :=by
          rw [hscalar,hneg_half_pow,hraw']
          have h':
              ((2*p:ℂ) * (Complex.I^n) / (((2:ℂ) ^ n) * S)) * (Complex.I^n*S) =
                (2*p:ℂ) * (((-1:ℂ) ^ n) / (2:ℂ) ^ n) :=by
              field_simp [h2p_ne,hS_ne,htwo_pow_ne]
              simpa [pow_two,mul_assoc,mul_left_comm,mul_comm] using hI_sq_pow
          exact h'
    rw [sh,sB (p:=p) hp_odd',
      ss (p:=p) (K:=K) hp_odd',
      Finset.prod_const]
    rw [s4 (p:=p) hp_odd']
    simpa [n,G,mul_assoc] using hgoal
end GaussGoal
end KummerCriterion
end
end Module32
-- Source: KummerCriterion.HMinus.LValueReduction.Assembly
section Module33
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section Assembly
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
omit [IsCyclotomicExtension {p} ℚ K] in
theorem vK
    {coefficient:ℂ}
    (hLValues:
      ((hMinus K :ℕ) : ℂ) =
        coefficient*
          Finset.prod (q8 (p:=p))
            (fun χ => DirichletCharacter.LFunction χ 1))
    (hgauss:
      coefficient*
          Finset.prod (q8 (p:=p)) (fun χ =>
            ((((Real.pi:ℝ) : ℂ) * Complex.I) *
              gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ))) =
        (2*p:ℂ) *
          Finset.prod (q8 (p:=p))
            (fun _ :DirichletCharacter ℂ p=> (-(1/2:ℂ)))) :
    ((hMinus K :ℕ) : ℂ) =
      (2*p:ℂ) *
        Finset.prod (q8 (p:=p)) (fun χ =>
          (-(1/2:ℂ)) * qf χ⁻¹ 1) :=by
  have hodd:
      Finset.prod (q8 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1) =
        Finset.prod (q8 (p:=p)) (fun χ => u9 p χ) :=by
    simpa [vx] using xC (p:=p)
  rw [hLValues,hodd,uF (p:=p)]
  calc
    coefficient*
        (Finset.prod (q8 (p:=p)) (fun χ =>
            ((((Real.pi:ℝ) : ℂ) * Complex.I) *
              gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ))) *
          Finset.prod (q8 (p:=p)) (fun χ => qf χ⁻¹ 1)) =
      (coefficient*
          Finset.prod (q8 (p:=p)) (fun χ =>
            ((((Real.pi:ℝ) : ℂ) * Complex.I) *
              gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ)))) *
        Finset.prod (q8 (p:=p)) (fun χ => qf χ⁻¹ 1) :=by
          ring
    _=
      ((2*p:ℂ) *
          Finset.prod (q8 (p:=p))
            (fun _ :DirichletCharacter ℂ p=> (-(1/2:ℂ)))) *
        Finset.prod (q8 (p:=p)) (fun χ => qf χ⁻¹ 1) :=by
          rw [hgauss]
    _=
      (2*p:ℂ) *
        (Finset.prod (q8 (p:=p))
            (fun _ :DirichletCharacter ℂ p=> (-(1/2:ℂ))) *
          Finset.prod (q8 (p:=p)) (fun χ => qf χ⁻¹ 1)) :=by
            ring
    _=
      (2*p:ℂ) *
        Finset.prod (q8 (p:=p)) (fun χ =>
          (-(1/2:ℂ)) * qf χ⁻¹ 1) :=by
            rw [← Finset.prod_mul_distrib]
theorem wM
    (hp_odd':p ≠ 2)
    {coefficient plusFactor:ℂ}
    (hh_formula:
      ((h K :ℕ) : ℂ) =
        ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) * (coefficient*plusFactor))
    (hres:
      ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) =
        Finset.prod (qi (p:=p)) (fun χ => ra p χ) *
          Finset.prod (q8 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1))
    (hplus:
      ((hPlus K :ℕ) : ℂ) =
        plusFactor*
          Finset.prod (qi (p:=p)) (fun χ => ra p χ)) :
    ((hMinus K :ℕ) : ℂ) =
      coefficient*
        Finset.prod (q8 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1) :=by
  let O :ℂ:=
    Finset.prod (q8 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1)
  have hh: ((h K :ℕ) : ℂ) = ((hPlus K :ℕ) : ℂ) * ((hMinus K :ℕ) : ℂ) :=by
    exact_mod_cast (xf (p:=p) (hp_odd:=hp_odd') (K:=K))
  have hhplus_ne: ((hPlus K :ℕ) : ℂ) ≠ 0:=by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos:0 < Fintype.card
      (ClassGroup (𝓞 (oMR K)))))
  have hmain: ((hPlus K :ℕ) : ℂ) * ((hMinus K :ℕ) : ℂ) =
      ((hPlus K :ℕ) : ℂ) * (coefficient*O) :=by
    rw [← hh,hh_formula,hres,hplus]
    simp [O]
    ring
  exact mul_left_cancel₀ hhplus_ne hmain
theorem ws
    (hp_odd':p ≠ 2)
    {coefficient plusFactor:ℂ}
    (hh_formula:
      ((h K :ℕ) : ℂ) =
        ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) * (coefficient*plusFactor))
    (hres:
      ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) =
        Finset.prod (qi (p:=p)) (fun χ => ra p χ) *
          Finset.prod (q8 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1))
    (hplus:
      ((hPlus K :ℕ) : ℂ) =
        plusFactor*Finset.prod (qi (p:=p)) (fun χ => ra p χ))
    (hgauss:
      coefficient*
          Finset.prod (q8 (p:=p)) (fun χ =>
            ((((Real.pi:ℝ) : ℂ) * Complex.I) *
              gaussSum χ (ZMod.stdAddChar (N:=p)) / (p:ℂ))) =
        (2*p:ℂ) *
          Finset.prod (q8 (p:=p))
            (fun _ :DirichletCharacter ℂ p=> (-(1/2:ℂ)))) :
    ((hMinus K :ℕ) : ℂ) =
      (2*p:ℂ) *
        Finset.prod (q8 (p:=p)) (fun χ =>
          (-(1/2:ℂ)) * qf χ⁻¹ 1) :=
  vK (p:=p) (K:=K)
    (coefficient:=coefficient)
    (wM
      (p:=p) (K:=K) hp_odd' (coefficient:=coefficient) hh_formula hres hplus)
    hgauss
end Assembly
end KummerCriterion
end
end Module33
-- Source: KummerCriterion.HMinus.LValueReduction.GaussPairing
section Module34
noncomputable section
namespace KummerCriterion
section GaussSum
variable (p:ℕ) [hp:Fact p.Prime]
theorem vj
    (hp₂:p ≠ 2) (hp₄:p%4=3) :
    gaussSum ((quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ))
      (ZMod.stdAddChar (N:=p)) = Complex.I* (Real.sqrt p :ℂ) :=by
  simpa [q3] using
    ug (p:=p) hp₂ hp₄
end GaussSum
end KummerCriterion
noncomputable section
open scoped BigOperators
namespace KummerCriterion
section PairingDefs
variable (p:ℕ)
def qq:Setoid (DirichletCharacter ℂ p) where
  r χ ψ:=χ=ψ ∨ χ=ψ⁻¹
  iseqv:=by
    constructor
    · intro χ
      exact Or.inl rfl
    · intro χ ψ h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        simp [h]
    · intro χ ψ ϕ hχψ hψϕ
      rcases hχψ with hχψ | hχψ <;> rcases hψϕ with hψϕ | hψϕ
      · exact Or.inl (hχψ.trans hψϕ)
      · exact Or.inr (hχψ.trans hψϕ)
      · exact Or.inr <| by simpa [hψϕ] using hχψ
      · left
        simpa [hψϕ] using hχψ
noncomputable def rz (χ:DirichletCharacter ℂ p) :
    Finset (DirichletCharacter ℂ p) :=by
  classical
  exact Finset.filter (fun ψ =>
    Quotient.mk (qq (p:=p)) ψ =
      Quotient.mk (qq (p:=p)) χ) (q8 (p:=p))
noncomputable def qS (χ:DirichletCharacter ℂ p) :
    Finset (DirichletCharacter ℂ p) :=by
  classical
  exact {χ,χ⁻¹}
theorem vq
    {χ:DirichletCharacter ℂ p} (hχ:χ ∈ q8 (p:=p)) :
    rz (p:=p) χ =qS (p:=p) χ :=by
  classical
  apply Finset.ext
  intro ψ
  constructor
  · intro hψ
    have hψ':
        ψ ∈ Finset.filter (fun ψ =>
          Quotient.mk (qq (p:=p)) ψ =
            Quotient.mk (qq (p:=p)) χ) (q8 (p:=p)) :=by
      simpa [rz] using hψ
    have hrel:ψ=χ ∨ ψ=χ⁻¹:=by
      change (qq (p:=p)).r ψ χ
      exact Quotient.exact (Finset.mem_filter.mp hψ').2
    simpa [qS,Finset.mem_insert,Finset.mem_singleton] using hrel
  · intro hψ
    have hψ':
        ψ ∈ ({χ,χ⁻¹} : Finset (DirichletCharacter ℂ p)) :=by
      simpa [qS] using hψ
    rcases Finset.mem_insert.mp hψ' with rfl | hψ
    · simpa [rz] using Finset.mem_filter.mpr ⟨hχ,rfl⟩
    · have hψeq:ψ=χ⁻¹:=by
        simpa [Finset.mem_singleton] using hψ
      subst ψ
      have hχinv:χ⁻¹ ∈ q8 (p:=p) :=xd (p:=p) hχ
      have:
          χ⁻¹ ∈ Finset.filter (fun ψ =>
            Quotient.mk (qq (p:=p)) ψ =
              Quotient.mk (qq (p:=p)) χ) (q8 (p:=p)) :=by
        refine Finset.mem_filter.mpr ⟨hχinv,?_⟩
        exact Quotient.sound (show (qq (p:=p)).r χ⁻¹ χ by
          right
          rfl)
      simpa [rz] using this
end PairingDefs
section GaussPairing
variable (p:ℕ) [hp:Fact p.Prime]
theorem yf
    (hp_odd':p ≠ 2) (hp₄:p%4=1) {χ:DirichletCharacter ℂ p}
    (hχ:χ ∈ q8 (p:=p)) :
    (rz (p:=p) χ).card=2:=by
  classical
  have hχ_odd:χ.Odd:= (Finset.mem_filter.mp hχ).2
  have hχ_ne:χ ≠ χ⁻¹:=
    sK (p:=p) hp_odd' hp₄ hχ_odd
  rw [vq (p:=p) hχ]
  simp [qS,hχ_ne]
theorem z3
    (hp_odd':p ≠ 2) (hp₄:p%4=1) :
    Finset.prod (q8 (p:=p))
        (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) =
      (-(p:ℂ)) ^ ((p-1) / 4) :=by
  classical
  let R :=qq (p:=p)
  let q :Finset (Quotient R) := (q8 (p:=p)).image (Quotient.mk R)
  have hpartition:
      Finset.prod (q8 (p:=p)) (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) =
        ∏ xbar ∈ q,∏ ψ ∈ q8 (p:=p) with Quotient.mk R ψ=xbar,
          gaussSum ψ (ZMod.stdAddChar (N:=p)) :=by
    simpa [q,R] using
      (Finset.prod_partition (s:=q8 (p:=p)) (R:=R)
        (f:=fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))))
  have hqcard:
      q.card= (p-1) / 4:=by
    have hcard:
        (q8 (p:=p)).card=
          ∑ xbar ∈ q,(Finset.filter (fun ψ => Quotient.mk R ψ=xbar)
            (q8 (p:=p))).card:=by
      simpa [q,R] using
        (Finset.card_eq_sum_card_image (f:=Quotient.mk R) (s:=q8 (p:=p)))
    have hcard':
        (q8 (p:=p)).card=q.card*2:=by
      calc
        (q8 (p:=p)).card=
            ∑ xbar ∈ q,(Finset.filter (fun ψ => Quotient.mk R ψ=xbar)
              (q8 (p:=p))).card:=hcard
        _= ∑ xbar ∈ q,(2:ℕ) :=by
              refine Finset.sum_congr rfl ?_
              intro xbar hxbar
              rcases Finset.mem_image.mp hxbar with ⟨χ,hχ,rfl⟩
              simpa [R,rz] using
                (yf (p:=p) hp_odd' hp₄ hχ)
        _=q.card*2:=
              Finset.sum_const_nat (s:=q) (m:=2) (f:=fun _ => 2)
                (by intro _ _;rfl)
    rw [s4 (p:=p) hp_odd'] at hcard'
    omega
  rw [hpartition]
  calc
    ∏ xbar ∈ q,∏ ψ ∈ q8 (p:=p) with Quotient.mk R ψ=xbar,
        gaussSum ψ (ZMod.stdAddChar (N:=p)) =
      ∏ xbar ∈ q,(-(p:ℂ)) :=by
        refine Finset.prod_congr rfl ?_
        intro xbar hxbar
        rcases Finset.mem_image.mp hxbar with ⟨χ,hχ,rfl⟩
        have hχ_odd:χ.Odd:= (Finset.mem_filter.mp hχ).2
        have hχ_ne:χ ≠ χ⁻¹:=
          sK (p:=p) hp_odd' hp₄ hχ_odd
        rw [show Finset.filter (fun ψ => Quotient.mk R ψ=Quotient.mk R χ)
            (q8 (p:=p)) = rz (p:=p) χ by
              rfl]
        rw [vq (p:=p) hχ]
        simp only [qS]
        let:DecidableEq (DirichletCharacter ℂ p) :=Classical.decEq _
        rw [Finset.prod_insert]
        · simp [sG (p:=p) hχ_odd]
        · simpa [qS,Finset.mem_singleton] using hχ_ne
    _= (-(p:ℂ)) ^ q.card:=by
          rw [Finset.prod_const]
    _= (-(p:ℂ)) ^ ((p-1) / 4) :=by
          rw [hqcard]
noncomputable def qd:
    Finset (DirichletCharacter ℂ p) :=by
  classical
  exact (q8 (p:=p)).erase (q3 p)
theorem rG
    (hp_odd':p ≠ 2) (hp₄:p%4=3) :
    q3 p ∈ q8 (p:=p) :=by
  classical
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,
      vt (p:=p) hp_odd' hp₄⟩
theorem ve
    (hp_odd':p ≠ 2) (hp₄:p%4=3) :
    (qd (p:=p)).card= (p-3) / 2:=by
  classical
  rw [qd]
  rw [Finset.card_erase_of_mem
    (rG (p:=p) hp_odd' hp₄)]
  rw [s4 (p:=p) hp_odd']
  rcases hp.out.odd_of_ne_two hp_odd' with ⟨k,hk⟩
  omega
theorem xv {χ:DirichletCharacter ℂ p}
    (hχ:χ ∈ qd (p:=p)) :
    χ⁻¹ ∈ qd (p:=p) :=by
  classical
  rcases Finset.mem_erase.mp hχ with ⟨hχ_ne_quad,hχ_mem⟩
  refine Finset.mem_erase.mpr ⟨?_,xd (p:=p) hχ_mem⟩
  intro hχinv_quad
  apply hχ_ne_quad
  calc
    χ= (χ⁻¹)⁻¹:=by simp
    _= (q3 p)⁻¹:=by simp [hχinv_quad]
    _=q3 p :=by simp [rK (p:=p)]
noncomputable def qJ
    (χ:DirichletCharacter ℂ p) : Finset (DirichletCharacter ℂ p) :=by
  classical
  exact Finset.filter (fun ψ =>
    Quotient.mk (qq (p:=p)) ψ =
      Quotient.mk (qq (p:=p)) χ) (qd (p:=p))
theorem so
    {χ:DirichletCharacter ℂ p} (hχ:χ ∈ qd (p:=p)) :
    qJ (p:=p) χ =qS (p:=p) χ :=by
  classical
  apply Finset.ext
  intro ψ
  constructor
  · intro hψ
    have hψ':
        ψ ∈ Finset.filter (fun ψ =>
          Quotient.mk (qq (p:=p)) ψ =
            Quotient.mk (qq (p:=p)) χ)
          (qd (p:=p)) :=by
      simpa [qJ] using hψ
    have hrel:ψ=χ ∨ ψ=χ⁻¹:=by
      change (qq (p:=p)).r ψ χ
      exact Quotient.exact (Finset.mem_filter.mp hψ').2
    simpa [qS,Finset.mem_insert,Finset.mem_singleton] using hrel
  · intro hψ
    have hψ':
        ψ ∈ ({χ,χ⁻¹} : Finset (DirichletCharacter ℂ p)) :=by
      simpa [qS] using hψ
    rcases Finset.mem_insert.mp hψ' with rfl | hψ
    · simpa [qJ] using Finset.mem_filter.mpr ⟨hχ,rfl⟩
    · have hψeq:ψ=χ⁻¹:=by
        simpa [Finset.mem_singleton] using hψ
      subst ψ
      have hχinv:χ⁻¹ ∈ qd (p:=p) :=
        xv (p:=p) hχ
      have:
          χ⁻¹ ∈ Finset.filter (fun ψ =>
            Quotient.mk (qq (p:=p)) ψ =
              Quotient.mk (qq (p:=p)) χ)
            (qd (p:=p)) :=by
        refine Finset.mem_filter.mpr ⟨hχinv,?_⟩
        exact Quotient.sound (show (qq (p:=p)).r χ⁻¹ χ by
          right
          rfl)
      simpa [qJ] using this
theorem wR
    (hp_odd':p ≠ 2) {χ:DirichletCharacter ℂ p}
    (hχ:χ ∈ qd (p:=p)) :
    (qJ (p:=p) χ).card=2:=by
  classical
  rcases Finset.mem_erase.mp hχ with ⟨hχ_ne_quad,hχ_mem⟩
  have hχ_odd:χ.Odd:= (Finset.mem_filter.mp hχ_mem).2
  have hχ_ne:χ ≠ χ⁻¹:=by
    intro hχself
    have hquad:
        χ=q3 p :=
      rL (p:=p) hp_odd' hχ_odd hχself
    exact hχ_ne_quad hquad
  rw [so (p:=p) hχ]
  simp [qS,hχ_ne]
theorem vo
    (hp_odd':p ≠ 2) (hp₄:p%4=3) :
    Finset.prod (qd (p:=p))
        (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) =
      (-(p:ℂ)) ^ ((p-3) / 4) :=by
  classical
  let R :=qq (p:=p)
  let q :Finset (Quotient R) :=
    (qd (p:=p)).image (Quotient.mk R)
  have hpartition:
      Finset.prod (qd (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) =
        ∏ xbar ∈ q,
          ∏ ψ ∈ qd (p:=p) with Quotient.mk R ψ=xbar,
            gaussSum ψ (ZMod.stdAddChar (N:=p)) :=by
    simpa [q,R] using
      (Finset.prod_partition (s:=qd (p:=p)) (R:=R)
        (f:=fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))))
  have hqcard:
      q.card= (p-3) / 4:=by
    have hcard:
        (qd (p:=p)).card=
          ∑ xbar ∈ q,(Finset.filter (fun ψ => Quotient.mk R ψ=xbar)
            (qd (p:=p))).card:=by
      simpa [q,R] using
        (Finset.card_eq_sum_card_image
          (f:=Quotient.mk R) (s:=qd (p:=p)))
    have hcard':
        (qd (p:=p)).card=q.card*2:=by
      calc
        (qd (p:=p)).card=
            ∑ xbar ∈ q,(Finset.filter (fun ψ => Quotient.mk R ψ=xbar)
              (qd (p:=p))).card:=hcard
        _= ∑ xbar ∈ q,(2:ℕ) :=by
              refine Finset.sum_congr rfl ?_
              intro xbar hxbar
              rcases Finset.mem_image.mp hxbar with ⟨χ,hχ,rfl⟩
              simpa [R,qJ] using
                (wR (p:=p) hp_odd' hχ)
        _=q.card*2:=
              Finset.sum_const_nat (s:=q) (m:=2) (f:=fun _ => 2)
                (by intro _ _;rfl)
    rw [ve (p:=p) hp_odd' hp₄] at hcard'
    omega
  rw [hpartition]
  calc
    ∏ xbar ∈ q,
        ∏ ψ ∈ qd (p:=p) with Quotient.mk R ψ=xbar,
          gaussSum ψ (ZMod.stdAddChar (N:=p)) =
      ∏ xbar ∈ q,(-(p:ℂ)) :=by
        refine Finset.prod_congr rfl ?_
        intro xbar hxbar
        rcases Finset.mem_image.mp hxbar with ⟨χ,hχ,rfl⟩
        have hχ_odd:χ.Odd:= (Finset.mem_filter.mp (Finset.mem_erase.mp hχ).2).2
        have hχ_ne:χ ≠ χ⁻¹:=by
          intro hχself
          rcases Finset.mem_erase.mp hχ with ⟨hχ_ne_quad,hχ_mem⟩
          have hquad:
              χ=q3 p :=
            rL (p:=p) hp_odd'
              (Finset.mem_filter.mp hχ_mem).2 hχself
          exact hχ_ne_quad hquad
        rw [show Finset.filter (fun ψ => Quotient.mk R ψ=Quotient.mk R χ)
            (qd (p:=p)) =
              qJ (p:=p) χ by rfl]
        rw [so (p:=p) hχ]
        simp only [qS]
        let:DecidableEq (DirichletCharacter ℂ p) :=Classical.decEq _
        rw [Finset.prod_insert]
        · simp [sG (p:=p) hχ_odd]
        · simpa [qS,Finset.mem_singleton] using hχ_ne
    _= (-(p:ℂ)) ^ q.card:=by
          rw [Finset.prod_const]
    _= (-(p:ℂ)) ^ ((p-3) / 4) :=by
          rw [hqcard]
theorem xz
    (hp_odd':p ≠ 2) (hp₄:p%4=3) :
    Finset.prod (q8 (p:=p))
        (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) =
      (Complex.I* (Real.sqrt p :ℂ)) * (-(p:ℂ)) ^ ((p-3) / 4) :=by
  classical
  have hquad_mem:
      q3 p ∈ q8 (p:=p) :=
    rG (p:=p) hp_odd' hp₄
  calc
    Finset.prod (q8 (p:=p))
        (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) =
      gaussSum (q3 p) (ZMod.stdAddChar (N:=p)) *
        Finset.prod (qd (p:=p))
          (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) :=by
            symm
            simpa [qd] using
              (Finset.mul_prod_erase (s:=q8 (p:=p))
                (f:=fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) hquad_mem)
    _=
      gaussSum (q3 p) (ZMod.stdAddChar (N:=p)) *
        (-(p:ℂ)) ^ ((p-3) / 4) :=by
          rw [vo (p:=p) hp_odd' hp₄]
    _= (Complex.I* (Real.sqrt p :ℂ)) * (-(p:ℂ)) ^ ((p-3) / 4) :=by
          rw [show gaussSum (q3 p) (ZMod.stdAddChar (N:=p)) =
            Complex.I* (Real.sqrt p :ℂ) by
              simpa [q3] using
                vj (p:=p) hp_odd' hp₄]
end GaussPairing
end KummerCriterion
end
end
end Module34
-- Source: KummerCriterion.HMinus.LValueReduction.GaussProduct
section Module35
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section GaussProduct
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem xi
    (hp_odd':p ≠ 2) (hp₄:p%4=1) :
    (-(p:ℂ)) ^ ((p-1) / 4) =
      (Complex.I^ ((p-1) / 2)) *
        (((Real.sqrt ((p:ℝ) ^ ((p-1) / 2)) : ℝ) : ℂ)) :=by
  let m :ℕ:= (p-1) / 4
  let n :ℕ:= (p-1) / 2
  have hnm:n=2*m:=by
    dsimp [m,n]
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨k,hk⟩
    rw [hk]
    omega
  have hI:
      Complex.I^n= (-1:ℂ) ^ m:=by
    calc
      Complex.I^n=Complex.I^ (2*m) :=by rw [hnm]
      _= (Complex.I^2) ^ m:=by rw [pow_mul]
      _= (-1:ℂ) ^ m:=by rw [Complex.I_sq]
  have hsqrt:
      (((Real.sqrt ((p:ℝ) ^ n) : ℝ) : ℂ)) = (p:ℂ) ^ m:=by
    have hsqrt_real:Real.sqrt ((p:ℝ) ^ n) = (p:ℝ) ^ m:=by
      calc
        Real.sqrt ((p:ℝ) ^ n) = Real.sqrt ((p:ℝ) ^ (2*m)) :=by rw [hnm]
        _=Real.sqrt ((p:ℝ) ^ (m*2)) :=by
              congr 1
              ring
        _=Real.sqrt (((p:ℝ) ^ m) ^ 2) :=by rw [pow_mul]
        _= (p:ℝ) ^ m:=by
              rw [Real.sqrt_sq_eq_abs]
              simp
    simpa [Complex.ofReal_pow] using congrArg (fun x :ℝ=> (x:ℂ)) hsqrt_real
  calc
    (-(p:ℂ)) ^ m= ((-1:ℂ) ^ m) * (p:ℂ) ^ m:=by
      rw [show (-(p:ℂ)) = (-1:ℂ) * (p:ℂ) by ring,mul_pow]
    _= (Complex.I^n) * (((Real.sqrt ((p:ℝ) ^ n) : ℝ) : ℂ)) :=by
          rw [hI,hsqrt]
theorem wZ
    (hp_odd':p ≠ 2) (hp₄:p%4=3) :
    (Complex.I* (Real.sqrt p :ℂ)) * (-(p:ℂ)) ^ ((p-3) / 4) =
      (Complex.I^ ((p-1) / 2)) *
        (((Real.sqrt ((p:ℝ) ^ ((p-1) / 2)) : ℝ) : ℂ)) :=by
  let m :ℕ:= (p-3) / 4
  let n :ℕ:= (p-1) / 2
  have hnm:n=2*m+1:=by
    dsimp [m,n]
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨k,hk⟩
    rw [hk]
    omega
  have hI:
      Complex.I^n= ((-1:ℂ) ^ m) * Complex.I:=by
    calc
      Complex.I^n=Complex.I^ (1+2*m) :=by
        rw [hnm]
        congr 1
        ring
      _=Complex.I^1*Complex.I^ (2*m) :=by rw [pow_add]
      _=Complex.I* ((Complex.I^2) ^ m) :=by simp [pow_mul]
      _= ((-1:ℂ) ^ m) * Complex.I:=by rw [Complex.I_sq];ring
  have hsqrt:
      (((Real.sqrt ((p:ℝ) ^ n) : ℝ) : ℂ)) =
        (Real.sqrt p :ℂ) * (p:ℂ) ^ m:=by
    have hsqrt_real:
        Real.sqrt ((p:ℝ) ^ n) = Real.sqrt p * (p:ℝ) ^ m:=by
      calc
        Real.sqrt ((p:ℝ) ^ n) = Real.sqrt ((p:ℝ) ^ (1+2*m)) :=by
              rw [hnm]
              congr 1
              ring
        _=Real.sqrt (p* (p:ℝ) ^ (2*m)) :=by rw [pow_add,pow_one]
        _=Real.sqrt ((p:ℝ) ^ (2*m) * p) :=by rw [mul_comm]
        _=Real.sqrt ((p:ℝ) ^ (2*m)) * Real.sqrt p :=by
              rw [Real.sqrt_mul (by positivity)]
        _=Real.sqrt ((p:ℝ) ^ (m*2)) * Real.sqrt p :=by
              congr 1
              congr 1
              ring
        _=Real.sqrt (((p:ℝ) ^ m) ^ 2) * Real.sqrt p :=by rw [pow_mul]
        _= (p:ℝ) ^ m*Real.sqrt p :=by rw [Real.sqrt_sq_eq_abs];simp
        _=Real.sqrt p * (p:ℝ) ^ m:=by ring
    simpa [Complex.ofReal_mul,Complex.ofReal_pow] using
      congrArg (fun x :ℝ=> (x:ℂ)) hsqrt_real
  calc
    (Complex.I* (Real.sqrt p :ℂ)) * (-(p:ℂ)) ^ m=
        (Complex.I* (Real.sqrt p :ℂ)) * (((-1:ℂ) ^ m) * (p:ℂ) ^ m) :=by
          rw [show (-(p:ℂ)) = (-1:ℂ) * (p:ℂ) by ring,mul_pow]
    _= (((-1:ℂ) ^ m) * Complex.I) * ((Real.sqrt p :ℂ) * (p:ℂ) ^ m) :=by ring
    _= (Complex.I^n) * (((Real.sqrt ((p:ℝ) ^ n) : ℝ) : ℂ)) :=by
          rw [hI,hsqrt]
theorem rawGaussProduct
    (hp_odd':p ≠ 2) :
    Finset.prod (q8 (p:=p))
        (fun χ => gaussSum χ (ZMod.stdAddChar (N:=p))) =
      (Complex.I^ ((p-1) / 2)) *
        (((Real.sqrt ((p:ℝ) ^ ((p-1) / 2)) : ℝ) : ℂ)) :=by
  by_cases hp₄:p%4=1
  · rw [z3 (p:=p) hp_odd' hp₄]
    exact xi (p:=p) hp_odd' hp₄
  · have hpodd:p%2=1:=by
      rcases hp.out.odd_of_ne_two hp_odd' with ⟨k,hk⟩
      rw [hk]
      omega
    have hp₄':p%4=3:=by
      omega
    rw [xz (p:=p) hp_odd' hp₄']
    exact wZ (p:=p) hp_odd' hp₄'
theorem ye
    (hp_odd':p ≠ 2) :
    sh (p:=p) K :=
  (x4 (p:=p) (K:=K) hp_odd').2
    (rawGaussProduct (p:=p) hp_odd')
end GaussProduct
end KummerCriterion
end
end Module35
-- Source: KummerCriterion.HMinus.LValueReduction.Teichmuller
section Module36
noncomputable section
open NumberField
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section ZetaFactorisation
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem vf:
    Filter.Tendsto
      (fun s :ℝ ↦ (s-1) * (riemannZeta (s:ℂ) * qR p (s:ℂ)))
      (𝓝[>] 1)
      (𝓝 (qR p (1:ℂ))) :=by
  classical
  have h_cont:Continuous (qR p) :=
    continuous_finsetProd _ fun χ hχ=>
      (DirichletCharacter.differentiable_LFunction (Finset.mem_erase.mp hχ).1).continuous
  have h_embed:
      Filter.Tendsto (fun s :ℝ ↦ (s:ℂ)) (𝓝[>] (1:ℝ)) (𝓝[≠] (1:ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin] with s hs h
          exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta:Filter.Tendsto (fun s :ℝ=> ((s:ℂ) - 1) * riemannZeta (s:ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod:Filter.Tendsto (fun s :ℝ=> qR p (s:ℂ))
      (𝓝[>] (1:ℝ)) (𝓝 (qR p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod:=h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring
theorem w9:
    Filter.Tendsto
      (fun s :ℝ ↦ (s-1) * NumberField.dedekindZeta K (s:ℂ))
      (𝓝[>] 1)
      (𝓝 (qR p (1:ℂ))) :=by
  refine (Filter.tendsto_congr' ?_).mp (vf p)
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [ut p K (by exact_mod_cast hs)]
end ZetaFactorisation
end KummerCriterion
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section Final
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem uZ
    (hp_odd':p ≠ 2)
    (hres:
      ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) =
        Finset.prod (qi (p:=p)) (fun χ => ra p χ) *
          Finset.prod (q8 (p:=p)) (fun χ => DirichletCharacter.LFunction χ 1))
    (hplus:
      ((hPlus K :ℕ) : ℂ) =
        rj (K:=K) *
          Finset.prod (qi (p:=p)) (fun χ => ra p χ))
    (hgauss:sh (p:=p) K) :
    ((hMinus K :ℕ) : ℂ) =
      (2*p:ℂ) *
        Finset.prod (q8 (p:=p)) (fun χ =>
          (-(1/2:ℂ)) * qf χ⁻¹ 1) :=by
  apply ws (p:=p) (K:=K) hp_odd'
    (coefficient:=qF (p:=p) (K:=K))
    (plusFactor:=rj (K:=K))
  · calc
      ((h K :ℕ) : ℂ) =
          ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) *
            rk (p:=p) (K:=K) :=
            y1 (p:=p) (K:=K) hp_odd'
      _= ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) *
            (qF (p:=p) (K:=K) *
              rj (K:=K)) :=by
            rw [u8
              (p:=p) (K:=K)]
  · exact hres
  · exact hplus
  · exact hgauss
theorem hMinus_formula (hp_odd':p ≠ 2) :
    ((hMinus K :ℕ) : ℂ) =
      (2*p:ℂ) *
        Finset.prod (q8 (p:=p)) fun χ =>
          (-(1/2:ℂ)) * qf χ⁻¹ 1 :=by
  apply uZ
    (p:=p) (K:=K) hp_odd'
  · calc
      ((NumberField.dedekindZeta_residue K :ℝ) : ℂ) =
          qR p (1:ℂ) :=
            tendsto_nhds_unique
              (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
              (w9 p K)
      _=r1 p (1:ℂ) * vx p (1:ℂ) :=by
            rw [z9]
      _=
          Finset.prod (qi (p:=p)) (fun χ => ra p χ) *
            Finset.prod (q8 (p:=p))
              (fun χ => DirichletCharacter.LFunction χ 1) :=by
            rw [sN (p:=p)]
            rfl
  · exact y2 (p:=p) (K:=K) hp_odd'
  · exact ye (p:=p) (K:=K) hp_odd'
end Final
end KummerCriterion
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
section Teichmuller
variable (p:ℕ) [hp:Fact p.Prime]
lemma sM:0 < p-1:=
  Nat.sub_pos_of_lt hp.out.one_lt
lemma yJ:p-1 ≠ 0:=
  (sM (p:=p)).ne'
abbrev qC:= {j:Fin (p-1) //Odd (j:ℕ)}
omit hp in
theorem wn (j:qC p) : p ≠ 2:=by
  intro hp_two
  rcases j.2 with ⟨k,hk⟩
  have hj_lt: (j.1:ℕ) < p-1:=j.1.is_lt
  omega
noncomputable def qk: (ZMod p)ˣ:=
  (IsCyclic.exists_generator (α:= (ZMod p)ˣ)).choose
theorem vO:
    ∀ x : (ZMod p)ˣ,x ∈ Subgroup.zpowers (qk p) :=by
  simpa [qk] using
    (IsCyclic.exists_generator (α:= (ZMod p)ˣ)).choose_spec
theorem vS:
    orderOf (qk p) = p-1:=by
  rw [orderOf_eq_card_of_forall_mem_zpowers (vO (p:=p)),
    Nat.card_eq_fintype_card,ZMod.card_units]
theorem xM {m n :ℕ}
    (hm:m < p-1) (hn:n < p-1) :
    qk p ^m=qk p ^n ↔ m=n:=by
  constructor
  · intro hmn
    have hmod:
        m ≡ n [MOD orderOf (qk p)] :=by
      simpa using (pow_eq_pow_iff_modEq (x:=qk p) (n:=m) (m:=n)).mp hmn
    have hmod':m ≡ n [MOD p -1] :=by
      simpa [vS (p:=p)] using hmod
    have hEq:m% (p-1) = n:=Nat.mod_eq_of_modEq hmod' hn
    simpa [Nat.mod_eq_of_lt hm] using hEq
  · rintro rfl
    rfl
def r2 (j:Fin (p-1)) : ℕ:= (p-1) - (j:ℕ)
noncomputable def qZ (m:Fin (p-1)) : ℚ:=
  ((((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p).val:ℚ)
noncomputable def qw (j:Fin (p-1)) : Polynomial ℚ :=
  ∑ m :Fin (p-1),
    Polynomial.monomial ((m:ℕ) * r2 (p:=p) j)
      (qZ (p:=p) m)
theorem zv:
    Function.Bijective fun m :Fin (p-1) => qk p ^ (m:ℕ) :=by
  let f :Fin (p-1) → (ZMod p)ˣ:=fun m => qk p ^ (m:ℕ)
  refine (Fintype.bijective_iff_injective_and_card f).mpr ?_
  refine ⟨?_,?_⟩
  · intro m n hmn
    exact Fin.ext <| (xM (p:=p) m.is_lt n.is_lt).mp hmn
  · rw [Fintype.card_fin,ZMod.card_units]
noncomputable def sQ:Fin (p-1) ≃ (ZMod p)ˣ:=
  Equiv.ofBijective (fun m :Fin (p-1) => qk p ^ (m:ℕ))
    (zv (p:=p))
theorem sF
    {R:Type*} [AddCommMonoid R] (F:ZMod p → R) (hF0:F 0=0) :
    ∑ a :ZMod p,F a=
      ∑ m :Fin (p-1),F (((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p) :=by
  have hsplit:
      ∑ a :ZMod p,F a=F 0+ ∑ a: {a:ZMod p //a ≠ 0},F a.1:=by
    simpa using Fintype.sum_eq_add_sum_subtype_ne F (0:ZMod p)
  have hnonzero:
      ∑ a : {a:ZMod p //a ≠ 0},F a.1=
        ∑ u : (ZMod p)ˣ,F (u:ZMod p) :=by
    simpa using
      (Fintype.sum_equiv unitsEquivNeZero
        (fun u : (ZMod p)ˣ=> F (u:ZMod p))
        (fun a : {a:ZMod p //a ≠ 0} => F a.1)
        (fun u => rfl)).symm
  have hpowers:
      ∑ u : (ZMod p)ˣ,F (u:ZMod p) =
        ∑ m :Fin (p-1),F (((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p) :=by
    simpa using
      (Fintype.sum_equiv (sQ (p:=p))
        (fun m :Fin (p-1) => F (((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p))
        (fun u : (ZMod p)ˣ=> F (u:ZMod p))
        (fun m => rfl)).symm
  calc
    ∑ a :ZMod p,F a=F 0+ ∑ a: {a:ZMod p //a ≠ 0},F a.1:=hsplit
    _= ∑ a: {a:ZMod p //a ≠ 0},F a.1:=by rw [hF0,zero_add]
    _= ∑ u: (ZMod p)ˣ,F (u:ZMod p) :=hnonzero
    _= ∑ m:Fin (p-1),
        F (((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p) :=hpowers
theorem yX {R:Type*} [Field R] [CharZero R] [Algebra ℚ R]
    {χ:DirichletCharacter R p} (hχ_odd:χ.Odd) :
    χ ≠ 1:=by
  rintro rfl
  exact DirichletCharacter.Odd.not_even _ hχ_odd (by
    change (1:DirichletCharacter R p) (-1:ZMod p) = 1
    rw [MulChar.one_apply (isUnit_one.neg)])
theorem w1 {R:Type*} [Field R] [CharZero R] [Algebra ℚ R]
    {χ:DirichletCharacter R p} (hχ_odd:χ.Odd) :
    (-(1/2:R)) * qf (χ⁻¹) 1 =
      ((p:R)⁻¹* (-(1/2:R))) *
        ∑ a :ZMod p,(χ⁻¹) a * (a.val:R) :=by
  have hpR_ne_zero: (p:R) ≠ 0:=Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hχinv_ne_one:χ⁻¹ ≠ 1:=by
    intro hχinv
    apply yX (p:=p) hχ_odd
    simpa using congrArg Inv.inv hχinv
  calc
    (-(1/2:R)) * qf (χ⁻¹) 1 =
        ((p:R)⁻¹* (p:R)) * ((-(1/2:R)) * qf (χ⁻¹) 1) :=by
          rw [inv_mul_cancel₀ hpR_ne_zero,one_mul]
    _= (p:R)⁻¹* ((-(1/2:R)) * ((p:R) * qf (χ⁻¹) 1)) :=by
          ac_rfl
    _= (p:R)⁻¹* ((-(1/2:R)) * ∑ a :ZMod p,(χ⁻¹) a * (a.val:R)) :=by
          rw [rM
            (R:=R) (N:=p) (χ:=χ⁻¹) hχinv_ne_one]
    _= ((p:R)⁻¹* (-(1/2:R))) * ∑ a :ZMod p,(χ⁻¹) a * (a.val:R) :=by
          ac_rfl
theorem vT:IsCyclic (DirichletCharacter ℂ p) :=
  ((zI (p:=p)).isCyclic).2 inferInstance
noncomputable def q6:DirichletCharacter ℂ p:=by
  letI:IsCyclic (DirichletCharacter ℂ p) :=vT (p:=p)
  exact (IsCyclic.exists_monoid_generator (α:=DirichletCharacter ℂ p)).choose
noncomputable def qv:ℂ:=
  q6 p (((qk p : (ZMod p)ˣ) : ZMod p))
theorem s9:
    ∀ χ :DirichletCharacter ℂ p,χ ∈ Submonoid.powers (q6 p) :=by
  have:IsCyclic (DirichletCharacter ℂ p) :=vT (p:=p)
  simpa [q6] using
    (IsCyclic.exists_monoid_generator (α:=DirichletCharacter ℂ p)).choose_spec
theorem rx:
    orderOf (q6 p) = p-1:=by
  calc
    orderOf (q6 p) = Nat.card (DirichletCharacter ℂ p) :=
      orderOf_eq_card_of_forall_mem_powers (s9 (p:=p))
    _=p-1:=qH (p:=p)
theorem rh (m:ℕ) :
    q6 p (((qk p) ^ m: (ZMod p)ˣ) : ZMod p) =
      qv p ^m:=by
  change q6 p ((((qk p : (ZMod p)ˣ) : ZMod p) ^ m)) =
    qv p ^m
  rw [map_pow]
  rfl
theorem ui {l:ℕ}
    (hl:qv p ^l=1) :
    (q6 p) ^ l=1:=by
  apply (MulChar.eq_one_iff).2
  intro a
  let m :Fin (p-1) := (sQ (p:=p)).symm a
  have hm: ((qk p) ^ (m:ℕ) : (ZMod p)ˣ) = a:=
    (sQ (p:=p)).apply_symm_apply a
  rw [← hm,MulChar.pow_apply_coe,rh]
  rw [← pow_mul,Nat.mul_comm,pow_mul,hl,one_pow]
theorem xJ:
    IsPrimitiveRoot (qv p) (p-1) :=by
  refine ⟨?_,fun l hl=> ?_⟩
  · calc
      qv p ^ (p-1) =
          q6 p
            ((((qk p) ^ (p-1) : (ZMod p)ˣ) : ZMod p)) :=by
            symm
            exact rh (p:=p) (p-1)
      _=q6 p (1:ZMod p) :=by
            rw [show (qk p) ^ (p-1) = (1: (ZMod p)ˣ) by
              rw [← vS (p:=p),pow_orderOf_eq_one]]
            simp
      _=1:=by
            simp
  · have hpow: (q6 p) ^ l=1:=
      ui (p:=p) hl
    have hdiv:orderOf (q6 p) ∣ l:=
      (orderOf_dvd_iff_pow_eq_one (x:=q6 p)).2 hpow
    simpa [rx (p:=p)] using hdiv
theorem vD (j:Fin (p-1)) :
    (((q6 p) ^ (j:ℕ))⁻¹:DirichletCharacter ℂ p) =
      (q6 p) ^ r2 (p:=p) j :=by
  apply inv_eq_of_mul_eq_one_right
  have hj: (j:ℕ) + r2 (p:=p) j =p-1:=by
    dsimp [r2]
    exact Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)
  rw [← pow_add,hj,← rx (p:=p),pow_orderOf_eq_one]
theorem wP {i j :ℕ}
    (hi:i < p-1) (hj:j < p-1) :
    (q6 p) ^ i= (q6 p) ^ j ↔ i=j:=by
  constructor
  · intro hij
    have hmod:
        i ≡ j [MOD orderOf (q6 p)] :=by
      simpa using (pow_eq_pow_iff_modEq (x:=q6 p) (n:=i) (m:=j)).mp hij
    have hmod':i ≡ j [MOD p -1] :=by
      simpa [rx (p:=p)] using hmod
    have hEq:i% (p-1) = j:=Nat.mod_eq_of_modEq hmod' hj
    simpa [Nat.mod_eq_of_lt hi] using hEq
  · rintro rfl
    rfl
theorem t1 (hp_odd':p ≠ 2) :
    ∃ χ :DirichletCharacter ℂ p,χ.Odd:=by
  classical
  have hcard_pos:0 < (q8 (p:=p)).card:=by
    rw [s4 (p:=p) hp_odd']
    have hp_gt_two:2 < p:=lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd')
    omega
  obtain ⟨χ,hχ⟩ :=Finset.card_pos.mp hcard_pos
  exact ⟨χ,(Finset.mem_filter.mp hχ).2⟩
theorem zY (hp_odd':p ≠ 2) :
    (q6 p).Odd:=by
  rcases DirichletCharacter.even_or_odd (q6 p) with h_even | h_odd
  · exfalso
    obtain ⟨χ,hχ_odd⟩ :=t1 (p:=p) hp_odd'
    rcases (Submonoid.mem_powers_iff χ (q6 p)).mp
      (s9 (p:=p) χ) with ⟨n,rfl⟩
    have hpow_even: ((q6 p) ^ n).Even:=by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · change (1:DirichletCharacter ℂ p) (-1:ZMod p) = 1
        simpa using (MulChar.one_apply (R:=ZMod p) (R':=ℂ) isUnit_one.neg)
      · change ((q6 p) ^ n) (-1:ZMod p) = 1
        rw [MulChar.pow_apply' _ hn.ne',h_even,one_pow]
    exact DirichletCharacter.Odd.not_even _ hχ_odd hpow_even
  · exact h_odd
theorem wI (hp_odd':p ≠ 2) (i:ℕ) :
    ((q6 p) ^ i) (-1:ZMod p) = (-1:ℂ) ^ i:=by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using (MulChar.one_apply (R:=ZMod p) (R':=ℂ) isUnit_one.neg)
  · rw [MulChar.pow_apply' _ hi.ne',zY (p:=p) hp_odd']
theorem rO (hp_odd':p ≠ 2) (i:ℕ) :
    ((q6 p) ^ i).Odd ↔ Odd i :=by
  change ((q6 p) ^ i) (-1:ZMod p) = (-1:ℂ) ↔ Odd i
  rw [wI (p:=p) hp_odd' i]
  exact neg_one_pow_eq_neg_one_iff_odd (by norm_num: (-1:ℂ) ≠ 1)
noncomputable def vh:Finset (DirichletCharacter ℂ p) :=by
  classical
  exact (Finset.univ:Finset (qC p)).image
    (fun j => (q6 p) ^ (j.1:ℕ))
theorem x7 (hp_odd':p ≠ 2) :
    q8 (p:=p) = vh (p:=p) :=by
  classical
  ext χ
  constructor
  · intro hχ
    have hχ_odd:χ.Odd:= (Finset.mem_filter.mp hχ).2
    rcases (Submonoid.mem_powers_iff χ (q6 p)).mp
      (s9 (p:=p) χ) with ⟨j,hj⟩
    let k :Fin (p-1) := ⟨j% (p-1),Nat.mod_lt j (sM (p:=p))⟩
    have hk_eq: (q6 p) ^ (k:ℕ) = χ:=by
      dsimp [k]
      calc
        (q6 p) ^ (j% (p-1)) =
            (q6 p) ^ (j%orderOf (q6 p)) :=by
              rw [rx (p:=p)]
        _= (q6 p) ^ j:=by rw [pow_mod_orderOf]
        _=χ:=hj
    have hk_odd:Odd (k:ℕ) :=by
      have hk_odd': ((q6 p) ^ (k:ℕ)).Odd:=by
        simpa [hk_eq] using hχ_odd
      exact (rO (p:=p) hp_odd' (k:ℕ)).1 hk_odd'
    refine Finset.mem_image.mpr ⟨⟨k,hk_odd⟩,Finset.mem_univ _,?_⟩
    simpa using hk_eq
  · intro hχ
    unfold vh at hχ
    rcases Finset.mem_image.mp hχ with ⟨j,-,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      exact (rO (p:=p) hp_odd' (j.1:ℕ)).2 j.2⟩
theorem wy (hp_odd':p ≠ 2)
    {α:Type*} [CommMonoid α] (F:DirichletCharacter ℂ p → α) :
    Finset.prod (q8 (p:=p)) F =
      Finset.prod (Finset.univ:Finset (qC p))
        (fun j => F ((q6 p) ^ (j.1:ℕ))) :=by
  classical
  rw [x7 (p:=p) hp_odd']
  unfold vh
  exact Finset.prod_image fun a _ b _ hab=>
    Subtype.ext <| Fin.ext <|
      (wP (p:=p) a.1.is_lt b.1.is_lt).mp hab
theorem vN (j:Fin (p-1)) :
    ∑ a :ZMod p,((((q6 p) ^ (j:ℕ))⁻¹) a) * (a.val:ℂ) =
      Polynomial.eval₂ (algebraMap ℚ ℂ) (qv p)
        (qw (p:=p) j) :=by
  have hEval:
      Polynomial.eval₂ (algebraMap ℚ ℂ) (qv p)
        (qw (p:=p) j) =
          ∑ m :Fin (p-1),
            Polynomial.eval₂ (algebraMap ℚ ℂ) (qv p)
              (Polynomial.monomial ((m:ℕ) * r2 (p:=p) j)
                (qZ (p:=p) m)) :=by
    simpa [qw] using
      (Polynomial.eval₂_finsetSum (f:=algebraMap ℚ ℂ) (s:=Finset.univ)
        (g:=fun m :Fin (p-1) =>
          Polynomial.monomial ((m:ℕ) * r2 (p:=p) j)
            (qZ (p:=p) m))
        (x:=qv p))
  rw [sF (p:=p)
    (F:=fun a => ((((q6 p) ^ (j:ℕ))⁻¹) a) * (a.val:ℂ))
    (hF0:=by simp),hEval]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hcoeff:
      algebraMap ℚ ℂ (qZ (p:=p) m) =
        (((((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p).val:ℂ)) :=by
    rw [qZ]
    exact map_ratCast (algebraMap ℚ ℂ)
      (((((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p).val:ℚ))
  rw [Polynomial.eval₂_monomial,vD (p:=p) j,
    MulChar.pow_apply_coe,rh]
  rw [hcoeff,pow_mul]
  ac_rfl
theorem v1 (j:qC p) :
    (-(1/2:ℂ)) * qf (((q6 p) ^ (j.1:ℕ))⁻¹) 1 =
      ((p:ℂ)⁻¹* (-(1/2:ℂ))) *
        Polynomial.eval₂ (algebraMap ℚ ℂ) (qv p)
          (qw (p:=p) j.1) :=by
  rw [w1 (p:=p)
    (χ:= (q6 p) ^ (j.1:ℕ))
    ((rO (p:=p) (wn (p:=p) j)
      (j.1:ℕ)).2 j.2)]
  rw [vN (p:=p) j.1]
lemma xW:
    Monoid.exponent (ZMod p)ˣ=p-1:=by
  rw [IsCyclic.exponent_eq_card,Nat.card_eq_fintype_card,ZMod.card_units]
theorem wJ:
    HasEnoughRootsOfUnity ℚ_[p] (p-1) :=by
  have:NeZero (p-1) := ⟨yJ (p:=p)⟩
  apply HasEnoughRootsOfUnity.of_card_le (R:=ℚ_[p])
  refine le_of_eq ?_
  rw [eq_comm,card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot]
  obtain ⟨g,hg_gen⟩ :=IsCyclic.exists_generator (α:= (ZMod p)ˣ)
  refine ⟨((r4 p (g:ZMod p) : ℤ_[p]) : ℚ_[p]),?_⟩
  exact (rH (p:=p) hg_gen).map_of_injective
    (f:=PadicInt.Coe.ringHom) (hf:=fun _ _ h => Subtype.coe_injective h)
theorem yl:
    Nat.card (DirichletCharacter ℚ_[p] p) = p-1:=by
  have:HasEnoughRootsOfUnity ℚ_[p] (Monoid.exponent (ZMod p)ˣ) :=by
    simpa [xW (p:=p)] using
      wJ (p:=p)
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity,Nat.totient_prime hp.out]
noncomputable def qB:ℚ_[p] :=
  (((r4 p (((qk p : (ZMod p)ˣ) : ZMod p)) : ℤ_[p])) : ℚ_[p])
theorem xR:
    IsPrimitiveRoot (qB p) (p-1) :=
  (rH (p:=p) (g:=qk p)
    (vO (p:=p))).map_of_injective
    (f:=PadicInt.Coe.ringHom) (hf:=fun _ _ h => Subtype.coe_injective h)
theorem wg (m:ℕ) :
    q7 p (((qk p) ^ m: (ZMod p)ˣ) : ZMod p) =
      qB p ^m:=by
  change q7 p ((((qk p : (ZMod p)ˣ) : ZMod p) ^ m)) =
    qB p ^m
  rw [q7,MulChar.ringHomComp_apply,rI,map_pow]
  rfl
theorem sv (j:Fin (p-1)) :
    (((q7 p) ^ (j:ℕ))⁻¹:DirichletCharacter ℚ_[p] p) =
      (q7 p) ^ r2 (p:=p) j :=by
  apply inv_eq_of_mul_eq_one_right
  have hj: (j:ℕ) + r2 (p:=p) j =p-1:=by
    dsimp [r2]
    exact Nat.add_sub_of_le (Nat.le_of_lt j.is_lt)
  rw [← pow_add,hj,← s6 (p:=p),pow_orderOf_eq_one]
theorem rX {i j :ℕ}
    (hi:i < p-1) (hj:j < p-1) :
    (q7 p) ^ i= (q7 p) ^ j ↔ i=j:=by
  constructor
  · intro hij
    have hmod:
        i ≡ j [MOD orderOf (q7 p)] :=by
      simpa using (pow_eq_pow_iff_modEq (x:=q7 p) (n:=i) (m:=j)).mp hij
    have hmod':i ≡ j [MOD p -1] :=by
      simpa [s6 (p:=p)] using hmod
    have hEq:i% (p-1) = j:=Nat.mod_eq_of_modEq hmod' hj
    simpa [Nat.mod_eq_of_lt hi] using hEq
  · rintro rfl
    rfl
theorem zE:
    Function.Bijective fun j :Fin (p-1) => (q7 p) ^ (j:ℕ) :=by
  let f :Fin (p-1) → DirichletCharacter ℚ_[p] p :=fun j => (q7 p) ^ (j:ℕ)
  refine (Fintype.bijective_iff_injective_and_card f).mpr ?_
  refine ⟨?_,?_⟩
  · intro i j hij
    exact Fin.ext <| (rX (p:=p) i.is_lt j.is_lt).mp hij
  · rw [Fintype.card_fin,← Nat.card_eq_fintype_card,yl (p:=p)]
theorem xO (hp_odd':p ≠ 2) (i:ℕ) :
    ((q7 p) ^ i) (-1:ZMod p) = (-1:ℚ_[p]) ^ i:=by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using (MulChar.one_apply (R:=ZMod p) (R':=ℚ_[p]) isUnit_one.neg)
  · rw [r6 (p:=p) (n:=i),MulChar.ringHomComp_apply,
      zl (p:=p) hp_odd' i,map_pow]
    rfl
theorem sA (hp_odd':p ≠ 2) (i:ℕ) :
    ((q7 p) ^ i).Odd ↔ Odd i :=by
  change ((q7 p) ^ i) (-1:ZMod p) = (-1:ℚ_[p]) ↔ Odd i
  rw [xO (p:=p) hp_odd' i]
  exact neg_one_pow_eq_neg_one_iff_odd (by norm_num: (-1:ℚ_[p]) ≠ 1)
noncomputable def uo:Finset ℕ :=
  (Finset.range (p-1)).filter fun j => Odd j
noncomputable def up:Finset (DirichletCharacter ℚ_[p] p) :=by
  classical
  exact Finset.univ.filter fun χ => χ.Odd
noncomputable def sS:Finset (DirichletCharacter ℚ_[p] p) :=by
  classical
  exact (uo (p:=p)).image fun j => (q7 p) ^ j
theorem sk (hp_odd':p ≠ 2) :
    up (p:=p) =
      sS (p:=p) :=by
  classical
  ext χ
  constructor
  · intro hχ
    have hχ_odd:χ.Odd:=by
      simpa [up] using hχ
    rcases (zE (p:=p)).surjective χ with ⟨j,hj⟩
    have hj_odd:Odd (j:ℕ) :=by
      have hj': ((q7 p) ^ (j:ℕ)).Odd:=by simpa [hj] using hχ_odd
      exact (sA (p:=p) hp_odd' (j:ℕ)).1 hj'
    refine Finset.mem_image.mpr ⟨(j:ℕ),?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.is_lt,hj_odd⟩
    · simpa using hj
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j,hj,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
      exact (sA (p:=p) hp_odd' j).2
        ((Finset.mem_filter.mp hj).2)⟩
noncomputable def x6:Finset (DirichletCharacter ℚ_[p] p) :=by
  classical
  exact (Finset.univ:Finset (qC p)).image
    (fun j => (q7 p) ^ (j.1:ℕ))
theorem z5 (hp_odd':p ≠ 2) :
    up (p:=p) = x6 (p:=p) :=by
  classical
  rw [sk (p:=p) hp_odd']
  unfold sS x6
  ext χ
  constructor
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j,hj,rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨⟨⟨j,Finset.mem_range.mp (Finset.mem_filter.mp hj).1⟩,
      (Finset.mem_filter.mp hj).2⟩,Finset.mem_univ _,?_⟩
    rfl
  · intro hχ
    rcases Finset.mem_image.mp hχ with ⟨j,-,rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(j.1:ℕ),Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr j.1.is_lt,j.2⟩,?_⟩
    rfl
theorem wa (hp_odd':p ≠ 2)
    {α:Type*} [CommMonoid α] (F:DirichletCharacter ℚ_[p] p → α) :
    Finset.prod (up (p:=p)) F =
      Finset.prod (Finset.univ:Finset (qC p))
        (fun j => F ((q7 p) ^ (j.1:ℕ))) :=by
  classical
  rw [z5 (p:=p) hp_odd']
  unfold x6
  exact Finset.prod_image fun a _ b _ hab=>
    Subtype.ext <| Fin.ext <|
      (rX (p:=p) a.1.is_lt b.1.is_lt).mp hab
theorem vQ (j:Fin (p-1)) :
    ∑ a :ZMod p,((((q7 p) ^ (j:ℕ))⁻¹) a) * (a.val:ℚ_[p]) =
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
        (qw (p:=p) j) :=by
  have hEval:
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
        (qw (p:=p) j) =
          ∑ m :Fin (p-1),
            Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
              (Polynomial.monomial ((m:ℕ) * r2 (p:=p) j)
                (qZ (p:=p) m)) :=by
    simpa [qw] using
      (Polynomial.eval₂_finsetSum (f:=algebraMap ℚ ℚ_[p]) (s:=Finset.univ)
        (g:=fun m :Fin (p-1) =>
          Polynomial.monomial ((m:ℕ) * r2 (p:=p) j)
            (qZ (p:=p) m))
        (x:=qB p))
  rw [sF (p:=p)
    (F:=fun a => ((((q7 p) ^ (j:ℕ))⁻¹) a) * (a.val:ℚ_[p]))
    (hF0:=by simp),hEval]
  refine Finset.sum_congr rfl ?_
  intro m hm
  have hcoeff:
      algebraMap ℚ ℚ_[p] (qZ (p:=p) m) =
        (((((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p).val:ℚ_[p])) :=by
    rw [qZ]
    exact map_ratCast (algebraMap ℚ ℚ_[p])
      (((((qk p) ^ (m:ℕ) : (ZMod p)ˣ) : ZMod p).val:ℚ))
  rw [Polynomial.eval₂_monomial,sv (p:=p) j,
    MulChar.pow_apply_coe,wg]
  rw [hcoeff,pow_mul]
  ac_rfl
theorem v6 (j:qC p) :
    (-(1/2:ℚ_[p])) * qf (((q7 p) ^ (j.1:ℕ))⁻¹) 1 =
      ((p:ℚ_[p])⁻¹* (-(1/2:ℚ_[p]))) *
        Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
          (qw (p:=p) j.1) :=by
  rw [w1 (p:=p)
    (χ:= (q7 p) ^ (j.1:ℕ))
    ((sA (p:=p) (wn (p:=p) j)
      (j.1:ℕ)).2 j.2)]
  rw [vQ (p:=p) j.1]
theorem sl (j:qC p) :
    ((-(1/2:ℂ)) * qf (((q6 p) ^ (j.1:ℕ))⁻¹) 1 =
        ((p:ℂ)⁻¹* (-(1/2:ℂ))) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (qv p)
            (qw (p:=p) j.1))
      ∧
    ((-(1/2:ℚ_[p])) * qf (((q7 p) ^ (j.1:ℕ))⁻¹) 1 =
        ((p:ℚ_[p])⁻¹* (-(1/2:ℚ_[p]))) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
            (qw (p:=p) j.1)) :=
  ⟨v1 (p:=p) j,
    v6 (p:=p) j⟩
theorem sc:
    ((Finset.prod (Finset.univ:Finset (qC p)) fun j =>
        (-(1/2:ℂ)) * qf (((q6 p) ^ (j.1:ℕ))⁻¹) 1) =
      Finset.prod (Finset.univ:Finset (qC p)) fun j =>
        ((p:ℂ)⁻¹* (-(1/2:ℂ))) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (qv p)
            (qw (p:=p) j.1))
      ∧
    ((Finset.prod (Finset.univ:Finset (qC p)) fun j =>
        (-(1/2:ℚ_[p])) * qf (((q7 p) ^ (j.1:ℕ))⁻¹) 1) =
      Finset.prod (Finset.univ:Finset (qC p)) fun j =>
        ((p:ℚ_[p])⁻¹* (-(1/2:ℚ_[p]))) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
            (qw (p:=p) j.1)) :=by
  constructor
  · refine Finset.prod_congr rfl ?_
    intro j hj
    exact (sl (p:=p) j).1
  · refine Finset.prod_congr rfl ?_
    intro j hj
    exact (sl (p:=p) j).2
noncomputable def qY:Polynomial ℚ :=
  Finset.prod (Finset.univ:Finset (qC p)) fun j =>
    Polynomial.C (((p:ℚ)⁻¹) * (-(1/2:ℚ))) *
      qw (p:=p) j.1
theorem vr
    {R:Type*} [Field R] [CharZero R] [Algebra ℚ R] (x:R) :
    Polynomial.eval₂ (algebraMap ℚ R) x (qY (p:=p)) =
      Finset.prod (Finset.univ:Finset (qC p)) fun j =>
        ((p:R)⁻¹* (-(1/2:R))) *
          Polynomial.eval₂ (algebraMap ℚ R) x (qw (p:=p) j.1) :=by
  change (Polynomial.eval₂RingHom (algebraMap ℚ R) x) (qY (p:=p)) = _
  rw [qY,map_prod]
  refine Finset.prod_congr rfl ?_
  intro j hj
  change Polynomial.eval₂ (algebraMap ℚ R) x
      (Polynomial.C (((p:ℚ)⁻¹) * (-(1/2:ℚ))) *
        qw (p:=p) j.1) = _
  rw [Polynomial.eval₂_mul,Polynomial.eval₂_C]
  congr 1
  simp
theorem uL:
    Finset.prod (Finset.univ:Finset (qC p)) (fun j =>
      (-(1/2:ℂ)) * qf (((q6 p) ^ (j.1:ℕ))⁻¹) 1) =
        Polynomial.eval₂ (algebraMap ℚ ℂ) (qv p)
          (qY (p:=p)) :=by
  rw [(sc (p:=p)).1,
    vr (p:=p) (R:=ℂ) (x:=qv p)]
theorem uP:
    Finset.prod (Finset.univ:Finset (qC p)) (fun j =>
      (-(1/2:ℚ_[p])) * qf (((q7 p) ^ (j.1:ℕ))⁻¹) 1) =
        Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
          (qY (p:=p)) :=by
  rw [(sc (p:=p)).2,
    vr (p:=p) (R:=ℚ_[p]) (x:=qB p)]
end Teichmuller
section FinalTeichmuller
variable (p:ℕ) [hp:Fact p.Prime]
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem zz (hp_odd':p ≠ 2) :
    ((hMinus K :ℕ) : ℂ) =
      (2*p:ℂ) *
        Finset.prod (Finset.univ:Finset (qC p)) fun j =>
          (-(1/2:ℂ)) *
            qf (((q6 p) ^ (j.1:ℕ))⁻¹) 1 :=by
  rw [hMinus_formula (p:=p) (K:=K) hp_odd']
  rw [wy (p:=p) hp_odd'
    (fun χ => (-(1/2:ℂ)) * qf (χ⁻¹) 1)]
theorem xg (hp_odd':p ≠ 2) :
    ((hMinus K :ℕ) : ℚ_[p]) =
      (2*p:ℚ_[p]) *
        Finset.prod (Finset.univ:Finset (qC p)) fun j =>
          (-(1/2:ℚ_[p])) * qf (((q7 p) ^ (j.1:ℕ))⁻¹) 1 :=by
  let Q :Polynomial ℚ :=
    Polynomial.C (2*p:ℚ) * qY (p:=p) -
      Polynomial.C ((hMinus K :ℕ) : ℚ)
  have hcomplex:
      ((hMinus K :ℕ) : ℂ) =
        (2*p:ℂ) *
          Polynomial.eval₂ (algebraMap ℚ ℂ) (qv p)
            (qY (p:=p)) :=by
    rw [zz (p:=p) (K:=K) hp_odd',
      uL (p:=p)]
  have hQ_complex:Polynomial.aeval (qv p) Q =0:=by
    rw [Polynomial.aeval_def,Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_C]
    simpa only [eq_ratCast,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,map_natCast,
      Polynomial.eval₂_natCast] using sub_eq_zero.mpr hcomplex.symm
  have hdvd:Polynomial.cyclotomic (p-1) ℚ ∣ Q :=by
    rw [Polynomial.cyclotomic_eq_minpoly_rat
      (xJ (p:=p)) (sM (p:=p))]
    exact minpoly.dvd ℚ (qv p) hQ_complex
  have hcycl_qpadic:
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
        (Polynomial.cyclotomic (p-1) ℚ) = 0:=by
    simpa [Polynomial.eval₂_eq_eval_map,Polynomial.map_cyclotomic,Polynomial.IsRoot.def] using
      (xR (p:=p)).isRoot_cyclotomic
      (sM (p:=p))
  have hQ_qpadic:
      Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p) Q =0:=
    Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
      (f:=algebraMap ℚ ℚ_[p]) (x:=qB p) hdvd hcycl_qpadic
  have hq:
      (2*p:ℚ_[p]) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
            (qY (p:=p)) -
        ((hMinus K :ℕ) : ℚ_[p]) = 0:=by
    simpa [Q,Polynomial.eval₂_sub,Polynomial.eval₂_mul,Polynomial.eval₂_C] using hQ_qpadic
  calc
    ((hMinus K :ℕ) : ℚ_[p]) =
        (2*p:ℚ_[p]) *
          Polynomial.eval₂ (algebraMap ℚ ℚ_[p]) (qB p)
            (qY (p:=p)) :=
          (sub_eq_zero.mp hq).symm
    _= (2*p:ℚ_[p]) *
        Finset.prod (Finset.univ:Finset (qC p)) (fun j =>
          (-(1/2:ℚ_[p])) * qf (((q7 p) ^ (j.1:ℕ))⁻¹) 1) :=by
          rw [← uP (p:=p)]
theorem zN (hp_odd':p ≠ 2) :
    ((hMinus K :ℕ) : ℚ_[p]) =
      (2*p:ℚ_[p]) *
        Finset.prod (up (p:=p)) fun χ =>
          (-(1/2:ℚ_[p])) * qf χ⁻¹ 1 :=by
  rw [xg (p:=p) (K:=K) hp_odd']
  rw [← wa (p:=p) hp_odd'
    (fun χ => (-(1/2:ℚ_[p])) * qf χ⁻¹ 1)]
theorem xn (hp_odd':p ≠ 2) :
    ((hMinus K :ℕ) : ℚ_[p]) =
      (2*p:ℚ_[p]) *
        Finset.prod (uo (p:=p)) fun j =>
          (-(1/2:ℚ_[p])) * qf (((q7 p) ^ j)⁻¹) 1 :=by
  classical
  rw [zN (p:=p) (K:=K) hp_odd']
  rw [sk (p:=p) hp_odd']
  unfold sS
  rw [Finset.prod_image]
  · intro a ha b hb hab
    exact (rX (p:=p)
      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)).mp hab
theorem yc (hp_odd':p ≠ 2) :
    ((hMinus K :ℕ) : ℚ_[p]) =
      (2*p:ℚ_[p]) *
        Finset.prod ((Finset.range (p-1)).filter fun j => Odd j) fun j =>
          (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1 :=by
  rw [xn (p:=p) (K:=K) hp_odd']
  have hp_even:Even (p-1) :=hp.out.even_sub_one hp_odd'
  have hmem_complement:
      ∀ {j:ℕ},j ∈ (Finset.range (p-1)).filter (fun j => Odd j) →
        (p-1) - j ∈ (Finset.range (p-1)).filter (fun j => Odd j) :=by
    intro j hj
    rw [Finset.mem_filter,Finset.mem_range] at hj ⊢
    have hj_pos:0 < j:=by
      rcases hj.2 with ⟨k,hk⟩
      omega
    have hcomp_odd:Odd ((p-1) - j) :=
      Nat.Even.sub_odd (Nat.le_of_lt hj.1) hp_even hj.2
    exact ⟨Nat.sub_lt (sM (p:=p)) hj_pos,hcomp_odd⟩
  congr 1
  unfold uo
  refine Finset.prod_bij (fun j _=> (p-1) - j) ?_ ?_ ?_ ?_
  · intro j hj
    exact hmem_complement hj
  · intro a ha b hb hab
    rw [Finset.mem_filter,Finset.mem_range] at ha hb
    simpa [Nat.sub_sub_self (Nat.le_of_lt ha.1),Nat.sub_sub_self (Nat.le_of_lt hb.1)] using
      congrArg (fun t => (p-1) - t) hab
  · intro j hj
    have hj_mem:j ∈ (Finset.range (p-1)).filter (fun j => Odd j) :=hj
    rw [Finset.mem_filter,Finset.mem_range] at hj
    refine ⟨(p-1) - j,hmem_complement hj_mem,?_⟩
    · exact Nat.sub_sub_self (Nat.le_of_lt hj.1)
  · intro j hj
    rw [Finset.mem_filter,Finset.mem_range] at hj
    let j':Fin (p-1) := ⟨j,hj.1⟩
    simpa [j',r2] using
      congrArg (fun χ :DirichletCharacter ℚ_[p] p =>
        (-(1/2:ℚ_[p])) * qf χ 1)
        (sv (p:=p) j')
end FinalTeichmuller
end KummerCriterion
end
end
end
end Module36
-- Source: KummerCriterion.KummerCongruence.VonStaudtClausen
section Module37
noncomputable section
namespace KummerCriterion
lemma yw
    {p:ℕ} [hp:Fact p.Prime] (hp_odd:p ≠ 2)
    {t:ℕ} (ht_two:2 ≤ t) (ht_even:Even t)
    (ih_pB: ∀ j,j < t-> 2 ≤ j -> Even j ->
      ∃ z :ℤ_[p],(p:ℚ_[p]) * ((bernoulli j :ℚ) : ℚ_[p]) = (z:ℚ_[p]))
    {i:ℕ} (hi:i < t) :
    ∃ z :ℤ_[p],
      ((bernoulli i :ℚ) : ℚ_[p]) * ((Nat.choose (t+1) i :ℕ) : ℚ_[p]) *
          ((p:ℚ_[p]) ^ (t+1-i)) =
        ((p:ℚ_[p]) ^ 2) * (z:ℚ_[p]) :=by
  have hp:Nat.Prime p :=hp.out
  have hp_gt:2 < p:=lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  rcases Nat.eq_zero_or_pos i with rfl | hi_pos
  · refine ⟨(p:ℤ_[p]) ^ (t-1),?_⟩
    simp only [_root_.bernoulli_zero,Rat.cast_one,one_mul,
      Nat.choose_zero_right,Nat.cast_one]
    rw [show (t+1-0:ℕ) = 2+ (t-1) by omega,pow_add];push_cast;ring
  rcases eq_or_ne i 1 with rfl | hi_ne_one
  · have h2_unit:IsUnit ((2:ℕ) : ℤ_[p]) :=by
      rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.mpr fun h =>
        absurd (Nat.le_of_dvd (by omega) h) (by omega)
    set w :ℤ_[p] := (h2_unit.unit⁻¹: (ℤ_[p])ˣ).val with hw_def
    have hw_mul: ((2:ℕ) : ℤ_[p]) * w=1:=by
      change ((h2_unit.unit*h2_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) = 1;simp
    have hw_mul_Qp: (2:ℚ_[p]) * ((w:ℤ_[p]) : ℚ_[p]) = 1:=by
      simpa using! congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hw_mul
    refine ⟨-((Nat.choose (t+1) 1 :ℤ_[p]) * w* (p:ℤ_[p]) ^ (t-2)),?_⟩
    rw [_root_.bernoulli_one,
      show (t+1-1:ℕ) = 2+ (t-2) by omega,pow_add]
    have h2Q_ne: (2:ℚ_[p]) ≠ 0:=by norm_num
    have h_half: ((-1/2:ℚ) : ℚ_[p]) = -((w:ℤ_[p]) : ℚ_[p]) :=
      mul_left_cancel₀ h2Q_ne (by push_cast;linear_combination hw_mul_Qp)
    rw [h_half];push_cast;ring
  have hi_ge:2 ≤ i:=by omega
  rcases Nat.even_or_odd i with hi_even | hi_odd
  · have hi_le:i ≤ t-2:=by
      rcases hi_even with ⟨k,hk⟩;rcases ht_even with ⟨m,hm⟩;omega
    obtain ⟨c,hc⟩ :=ih_pB i hi hi_ge hi_even
    refine ⟨c* (Nat.choose (t+1) i :ℤ_[p]) * (p:ℤ_[p]) ^ (t-i-2),?_⟩
    rw [show t +1-i=1+ (t-i-2) + 2 from by omega,
      show (p:ℚ_[p]) ^ (1+ (t-i-2) + 2) =
        (p:ℚ_[p]) * (p:ℚ_[p]) ^ (t-i-2) * (p:ℚ_[p]) ^ 2 from by
        rw [pow_add,pow_add];ring]
    have hbc: ((bernoulli i :ℚ) : ℚ_[p]) * ((p:ℚ_[p])) = ((c:ℤ_[p]) : ℚ_[p]) :=by
      rw [← hc];ring
    push_cast
    linear_combination
      (((Nat.choose (t+1) i :ℕ) : ℚ_[p]) * ((p:ℚ_[p]) ^ (t-i-2)) *
        ((p:ℚ_[p]) ^ 2)) * hbc
  · refine ⟨0,?_⟩
    have hi_gt:1 < i:=by omega
    rw [bernoulli_eq_zero_of_odd hi_odd hi_gt];push_cast;ring
theorem rb
    {p:ℕ} [hp:Fact p.Prime] (hp_odd:p ≠ 2)
    {t:ℕ} (ht_two:2 ≤ t) (ht_even:Even t)
    (ih_pB: ∀ j,j < t-> 2 ≤ j -> Even j ->
      ∃ z :ℤ_[p],(p:ℚ_[p]) * ((bernoulli j :ℚ) : ℚ_[p]) = (z:ℚ_[p])) :
    ∃ W :ℤ_[p],
      ((t+1:ℕ) : ℚ_[p]) *
          ((∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t) -
            (p:ℚ_[p]) * ((bernoulli t :ℚ) : ℚ_[p])) =
        ((p:ℚ_[p]) ^ 2) * ((W:ℤ_[p]) : ℚ_[p]) :=by
  have hp:Nat.Prime p :=hp.out
  have hp_gt:2 < p:=lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  choose w hw using (fun (i:ℕ) (hi:i < t) =>
    yw hp_odd ht_two ht_even ih_pB hi)
  set W :ℤ_[p] :=
    ∑ i ∈ Finset.attach (Finset.range t),w i.1 (Finset.mem_range.mp i.2) with hW_def
  refine ⟨W,?_⟩
  have h_faulhaber_Q: ((t+1:ℚ)) * (∑ k ∈ Finset.range p,(k:ℚ) ^ t) =
      ∑ i ∈ Finset.range (t+1),
        bernoulli i * (Nat.choose (t+1) i :ℚ) * (p:ℚ) ^ (t+1-i) :=by
    rw [sum_range_pow p t,Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _=> ?_
    have htp1Q_ne: (((t+1:ℕ)) : ℚ) ≠ 0:=Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have h_faulhaber_Qp: ((t+1:ℕ) : ℚ_[p]) * (∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t) =
      ∑ i ∈ Finset.range (t+1),
        ((bernoulli i :ℚ) : ℚ_[p]) * ((Nat.choose (t+1) i :ℕ) : ℚ_[p]) *
          ((p:ℚ_[p])) ^ (t+1-i) :=by
    have:=congrArg (fun q :ℚ=> (q:ℚ_[p])) h_faulhaber_Q
    push_cast at this;push_cast;exact this
  have h_split_sum: ((t+1:ℕ) : ℚ_[p]) * (∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t) -
        ((t+1:ℕ) : ℚ_[p]) * ((p:ℚ_[p])) * ((bernoulli t :ℚ) : ℚ_[p]) =
      ∑ i ∈ Finset.range t,
        ((bernoulli i :ℚ) : ℚ_[p]) * ((Nat.choose (t+1) i :ℕ) : ℚ_[p]) *
          ((p:ℚ_[p])) ^ (t+1-i) :=by
    rw [h_faulhaber_Qp,Finset.sum_range_succ,Nat.choose_succ_self_right t,
      show (t+1-t:ℕ) = 1 from by omega]
    push_cast;ring
  have h_rhs_eq: (∑ i ∈ Finset.range t,
        ((bernoulli i :ℚ) : ℚ_[p]) * ((Nat.choose (t+1) i :ℕ) : ℚ_[p]) *
          ((p:ℚ_[p])) ^ (t+1-i)) =
      ((p:ℚ_[p])) ^ 2* ((W:ℤ_[p]) : ℚ_[p]) :=by
    rw [← Finset.sum_attach]
    rw [show (((p:ℚ_[p])) ^ 2* ((W:ℤ_[p]) : ℚ_[p])) =
        ∑ i ∈ Finset.attach (Finset.range t),
          ((p:ℚ_[p])) ^ 2* ((w i.1 (Finset.mem_range.mp i.2) : ℤ_[p]) : ℚ_[p]) from ?_]
    · refine Finset.sum_congr rfl fun i _=> ?_
      exact hw i.1 (Finset.mem_range.mp i.2)
    · rw [hW_def]
      simp [PadicInt.coe_sum,Finset.mul_sum]
  rw [mul_sub,← h_rhs_eq,← h_split_sum];push_cast;ring
theorem sX
    {p:ℕ} [hp:Fact p.Prime] (hp_odd:p ≠ 2)
    {t:ℕ} (ht_two:2 ≤ t) (ht_even:Even t)
    (h_p_not_dvd_t_plus_one: ¬ (p:ℕ) ∣ (t+1))
    (ih_pB: ∀ j,j < t-> 2 ≤ j -> Even j ->
      ∃ z :ℤ_[p],(p:ℚ_[p]) * ((bernoulli j :ℚ) : ℚ_[p]) = (z:ℚ_[p])) :
    ∃ z :ℤ_[p],
      ((∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t)) -
          (p:ℚ_[p]) * ((bernoulli t :ℚ) : ℚ_[p]) =
        ((p:ℚ_[p]) ^ 2) * (z:ℚ_[p]) :=by
  have hp:Nat.Prime p :=hp.out
  have htp1_unit:IsUnit ((t+1:ℕ) : ℤ_[p]) :=by
    rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr h_p_not_dvd_t_plus_one
  set u :ℤ_[p] := (htp1_unit.unit⁻¹: (ℤ_[p])ˣ).val with hu_def
  have hu_mul: ((t+1:ℕ) : ℤ_[p]) * u=1:=by
    change ((htp1_unit.unit*htp1_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) = 1;simp
  have hu_mul_Qp: ((t+1:ℕ) : ℚ_[p]) * ((u:ℤ_[p]) : ℚ_[p]) = 1:=by
    simpa using congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hu_mul
  obtain ⟨W,hW⟩ :=rb hp_odd ht_two ht_even ih_pB
  refine ⟨u*W,?_⟩
  have: ((u:ℤ_[p]) : ℚ_[p]) *
      (((t+1:ℕ) : ℚ_[p]) *
        ((∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t) -
          (p:ℚ_[p]) * ((bernoulli t :ℚ) : ℚ_[p]))) =
      ((u:ℤ_[p]) : ℚ_[p]) * ((p:ℚ_[p]) ^ 2* ((W:ℤ_[p]) : ℚ_[p])) :=by
    rw [hW]
  push_cast
  linear_combination this- ((∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t) -
    (p:ℚ_[p]) * ((bernoulli t :ℚ) : ℚ_[p])) * hu_mul_Qp
theorem sJ
    {p:ℕ} [hp:Fact p.Prime] (hp_odd:p ≠ 2)
    {k:ℕ} (hk_two:2 ≤ k) (hk_even:Even k)
    (h_below: ∀ j,j ≤ k-> ¬ (p:ℕ) ^ 3 ∣ (j+1)) :
    ∃ z :ℤ_[p],(p:ℚ_[p]) * (((bernoulli k :ℚ)) : ℚ_[p]) = (z:ℚ_[p]) :=by
  have hp:Nat.Prime p :=hp.out
  have hp_gt:2 < p:=lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hpQ_ne: (p:ℚ_[p]) ≠ 0:=by exact_mod_cast hp.ne_zero
  revert hk_two hk_even h_below
  induction k using Nat.strong_induction_on with
  | _ k ih=>
    intro hk_two hk_even h_below
    have ih_pB: ∀ j,j < k-> 2 ≤ j -> Even j ->
        ∃ z :ℤ_[p],(p:ℚ_[p]) * ((bernoulli j :ℚ) : ℚ_[p]) = (z:ℚ_[p]) :=by
      intro j hj hj_two hj_even
      exact ih j hj hj_two hj_even (fun j' hj'=> h_below j' (Nat.le_trans hj' hj.le))
    have h_not_pCube: ¬ (p:ℕ) ^ 3 ∣ (k+1) :=h_below k (le_refl k)
    set S_nat:ℕ:= ∑ j ∈ Finset.range p,j^k with hS_def
    have hS_cast: (∑ j ∈ Finset.range p,(j:ℚ_[p]) ^ k) = ((S_nat:ℕ) : ℚ_[p]) :=by
      simp only [hS_def];push_cast;rfl
    by_cases h_p_dvd: (p:ℕ) ∣ (k+1)
    · by_cases h_p_sq: (p:ℕ) ^ 2 ∣ (k+1)
      · obtain ⟨q,hq⟩ :=h_p_sq
        have hq_coprime: ¬ (p:ℕ) ∣ q:=by
          intro hdvd
          apply h_not_pCube
          rw [hq,pow_succ]
          exact mul_dvd_mul_left (p^2) hdvd
        have hq_unit:IsUnit ((q:ℕ) : ℤ_[p]) :=by
          rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
          exact hp.coprime_iff_not_dvd.mpr hq_coprime
        set qInv:ℤ_[p] := (hq_unit.unit⁻¹: (ℤ_[p])ˣ).val
        have hqInv_mul: ((q:ℕ) : ℤ_[p]) * qInv=1:=by
          change ((hq_unit.unit*hq_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) = 1;simp
        have hqInv_mul_Qp: ((q:ℕ) : ℚ_[p]) * ((qInv:ℤ_[p]) : ℚ_[p]) = 1:=by
          simpa using congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hqInv_mul
        obtain ⟨W,hW⟩ :=rb hp_odd hk_two hk_even ih_pB
        have h_kp1_eq: ((k+1:ℕ) : ℚ_[p]) = (p:ℚ_[p])^2* ((q:ℕ) : ℚ_[p]) :=by
          have: (k+1:ℕ) = p^2*q:=hq
          push_cast [this];ring
        rw [h_kp1_eq] at hW
        have hp_sq_ne: (p:ℚ_[p])^2 ≠ 0:=pow_ne_zero 2 hpQ_ne
        have hW'': ((q:ℕ) : ℚ_[p]) *
            ((∑ k' ∈ Finset.range p,(k':ℚ_[p]) ^ k) -
              (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p])) =
            ((W:ℤ_[p]) : ℚ_[p]) :=
          mul_left_cancel₀ hp_sq_ne (by linear_combination hW)
        have h_sub: ((∑ k' ∈ Finset.range p,(k':ℚ_[p]) ^ k) -
              (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p])) =
            ((qInv:ℤ_[p]) : ℚ_[p]) * ((W:ℤ_[p]) : ℚ_[p]) :=by
          linear_combination ((qInv:ℤ_[p]) : ℚ_[p]) * hW''-
            (((∑ k' ∈ Finset.range p,(k':ℚ_[p]) ^ k) -
              (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p]))) * hqInv_mul_Qp
        rw [hS_cast] at h_sub
        refine ⟨(S_nat:ℤ_[p]) - qInv*W,?_⟩
        have h_rearr: (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p]) =
            ((S_nat:ℕ) : ℚ_[p]) -
              ((qInv:ℤ_[p]) : ℚ_[p]) * ((W:ℤ_[p]) : ℚ_[p]) :=by
          linear_combination-h_sub
        rw [h_rearr];push_cast;ring
      · obtain ⟨m',hm'⟩ :=h_p_dvd
        have hm'_coprime: ¬ (p:ℕ) ∣ m':=by
          intro hdvd
          apply h_p_sq
          rw [hm',pow_two]
          exact mul_dvd_mul_left p hdvd
        have hm'_unit:IsUnit ((m':ℕ) : ℤ_[p]) :=by
          rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
          exact hp.coprime_iff_not_dvd.mpr hm'_coprime
        set mInv:ℤ_[p] := (hm'_unit.unit⁻¹: (ℤ_[p])ˣ).val
        have hmInv_mul: ((m':ℕ) : ℤ_[p]) * mInv=1:=by
          change ((hm'_unit.unit*hm'_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) = 1;simp
        have hmInv_mul_Qp: ((m':ℕ) : ℚ_[p]) * ((mInv:ℤ_[p]) : ℚ_[p]) = 1:=by
          simpa using congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hmInv_mul
        obtain ⟨W,hW⟩ :=rb hp_odd hk_two hk_even ih_pB
        have h_kp1_eq: ((k+1:ℕ) : ℚ_[p]) = (p:ℚ_[p]) * ((m':ℕ) : ℚ_[p]) :=by
          have: (k+1:ℕ) = p*m':=hm'
          push_cast [this];ring
        rw [h_kp1_eq] at hW
        have hW'': ((m':ℕ) : ℚ_[p]) *
            ((∑ k' ∈ Finset.range p,(k':ℚ_[p]) ^ k) -
              (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p])) =
            (p:ℚ_[p]) * ((W:ℤ_[p]) : ℚ_[p]) :=
          mul_left_cancel₀ hpQ_ne (by linear_combination hW)
        have h_sub: ((∑ k' ∈ Finset.range p,(k':ℚ_[p]) ^ k) -
              (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p])) =
            ((mInv:ℤ_[p]) : ℚ_[p]) * ((p:ℚ_[p]) * ((W:ℤ_[p]) : ℚ_[p])) :=by
          linear_combination ((mInv:ℤ_[p]) : ℚ_[p]) * hW''-
            (((∑ k' ∈ Finset.range p,(k':ℚ_[p]) ^ k) -
              (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p]))) * hmInv_mul_Qp
        rw [hS_cast] at h_sub
        refine ⟨(S_nat:ℤ_[p]) - mInv* (p:ℤ_[p]) * W,?_⟩
        have h_rearr: (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p]) =
            ((S_nat:ℕ) : ℚ_[p]) - ((mInv:ℤ_[p]) : ℚ_[p]) * (p:ℚ_[p]) *
              ((W:ℤ_[p]) : ℚ_[p]) :=by
          linear_combination-h_sub
        rw [h_rearr];push_cast;ring
    · obtain ⟨w,hw⟩ :=
        sX hp_odd hk_two hk_even h_p_dvd ih_pB
      rw [hS_cast] at hw
      refine ⟨(S_nat:ℤ_[p]) - (p:ℤ_[p]) ^ 2*w,?_⟩
      have h_rearr: (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p]) =
          ((S_nat:ℕ) : ℚ_[p]) - (p:ℚ_[p]) ^ 2* ((w:ℤ_[p]) : ℚ_[p]) :=by
        linear_combination-hw
      rw [h_rearr];push_cast;ring
end KummerCriterion
end
end Module37
-- Source: KummerCriterion.KummerCongruence.Voronoi
section Module38
noncomputable section
namespace KummerCriterion
lemma zS {R:Type*} [CommRing R]
    (p:R) {k:ℕ} (hk:1 ≤ k) (x y :R) :
    ∃ z :R,
      (x-p*y) ^ k=x^k- (k:R) * x^ (k-1) * p*y+p^2*z:=by
  induction k with
  | zero=> omega
  | succ n ih=>
    by_cases hn:n=0
    · subst hn;refine ⟨0,?_⟩;push_cast;ring
    · have hn_pos:1 ≤ n:=Nat.one_le_iff_ne_zero.mpr hn
      obtain ⟨z,hz⟩ :=ih hn_pos
      refine ⟨z*x+ (n:R) * x^ (n-1) * y*y-p*y*z,?_⟩
      have h_pow_shift:x^ (n-1) * x=x^n:=by
        rw [← pow_succ];congr 1;omega
      have h_lhs: (x-p*y) ^ (n+1) =
          (x^n- (n:R) * x^ (n-1) * p*y+p^2*z) * (x-p*y) :=by
        rw [pow_succ,hz]
      rw [h_lhs,show (n+1-1:ℕ) = n from by omega,pow_succ x n,
        show ((n+1:ℕ) : R) = (n:R) + 1 from by push_cast;ring]
      linear_combination-((n:R) * p*y) * h_pow_shift
lemma yV
    {p:ℕ} [hp:Fact p.Prime] {a:ℕ} (ha_coprime: ¬ (p:ℕ) ∣ a)
    {R:Type*} [AddCommMonoid R] (f:ℕ → R) :
    ∑ j ∈ Finset.range p,f ((j*a) % p) = ∑ j ∈ Finset.range p,f j:=by
  have hp:Nat.Prime p :=hp.out
  have ha_coprime_p:Nat.Coprime a p:=
    Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr ha_coprime)
  set b :ℕ:= ((a:ZMod p)⁻¹).val with hb_def
  have ha_unit:IsUnit ((a:ℕ) : ZMod p) :=by
    rw [ZMod.isUnit_iff_coprime]
    exact ha_coprime_p
  have hab: ((a:ZMod p) * (a:ZMod p)⁻¹) = 1:=
    ZMod.mul_inv_of_unit _ ha_unit
  have hb_zmod: ((b:ℕ) : ZMod p) = (a:ZMod p)⁻¹:=by
    rw [hb_def,ZMod.natCast_val,ZMod.cast_id]
  refine Finset.sum_nbij' (fun i => (i*a) % p) (fun j => (j*b) % p) ?_ ?_ ?_ ?_ ?_
  · intros i _;simp only [Finset.mem_range];exact Nat.mod_lt _ hp.pos
  · intros j _;simp only [Finset.mem_range];exact Nat.mod_lt _ hp.pos
  · intros i hi
    simp only [Finset.mem_range] at hi
    rw [show ((i*a) % p*b) % p= (i*a*b) % p by
      rw [Nat.mul_mod,Nat.mod_mod,← Nat.mul_mod]]
    have h_zmod: ((i*a*b:ℕ) : ZMod p) = (i:ZMod p) :=by
      push_cast;rw [hb_zmod]
      rw [show ((i:ZMod p) * (a:ZMod p) * (a:ZMod p)⁻¹) =
        (i:ZMod p) * ((a:ZMod p) * (a:ZMod p)⁻¹) from by ring,hab,mul_one]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod,Nat.mod_eq_of_lt hi]
  · intros j hj
    simp only [Finset.mem_range] at hj
    rw [show ((j*b) % p*a) % p= (j*b*a) % p by
      rw [Nat.mul_mod,Nat.mod_mod,← Nat.mul_mod]]
    have h_zmod: ((j*b*a:ℕ) : ZMod p) = (j:ZMod p) :=by
      push_cast;rw [hb_zmod]
      rw [show ((j:ZMod p) * (a:ZMod p)⁻¹* (a:ZMod p)) =
        (j:ZMod p) * ((a:ZMod p) * (a:ZMod p)⁻¹) from by ring,hab,mul_one]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod,Nat.mod_eq_of_lt hj]
  · intros i _;dsimp only
lemma yP
    {p:ℕ} [hp:Fact p.Prime]
    {a:ℕ} (ha_coprime: ¬ (p:ℕ) ∣ a)
    {k:ℕ} (hk_pos:0 < k) :
    ∃ W :ℤ_[p],
      (((a:ℤ_[p]) ^ k-1) * ((∑ j ∈ Finset.range p,j^k:ℕ) : ℤ_[p]) -
          (k:ℤ_[p]) * ((a:ℤ_[p]) ^ (k-1)) * (p:ℤ_[p]) *
            ((∑ j ∈ Finset.range p,j^ (k-1) * (j*a/p) : ℕ) : ℤ_[p])) =
        (p:ℤ_[p]) ^ 2*W:=by
  have hp_prime:Nat.Prime p :=hp.out
  have h_div_mod: ∀ j:ℕ,
      ((j*a:ℕ) : ℤ_[p]) = ((j*a/p:ℕ) : ℤ_[p]) * (p:ℤ_[p]) +
        ((((j*a) % p:ℕ)) : ℤ_[p]) :=fun j => by
    rw [show ((j*a:ℕ) : ℤ_[p]) = (((j*a/p) * p+ (j*a) % p:ℕ) : ℤ_[p]) from by
      rw [← (Nat.div_add_mod' _ _).symm]]
    push_cast;ring
  choose wj hwj using (fun (j:ℕ) (_hj:j ∈ Finset.range p) =>
    zS (R:=ℤ_[p])
      (p:= (p:ℤ_[p])) (k:=k) hk_pos ((j*a:ℕ) : ℤ_[p])
      (((j*a/p:ℕ)) : ℤ_[p]))
  have h_rj_eq: ∀ j:ℕ,(((((j*a) % p:ℕ)) : ℤ_[p])) =
      ((j*a:ℕ) : ℤ_[p]) - (p:ℤ_[p]) * (((j*a/p:ℕ)) : ℤ_[p]) :=fun j => by
    linear_combination-h_div_mod j
  have h_per_j: ∀ (j:ℕ) (hj:j ∈ Finset.range p),
      (((((j*a) % p:ℕ)) : ℤ_[p])) ^ k=
        ((j*a:ℕ) : ℤ_[p]) ^ k-
          (k:ℤ_[p]) * ((j*a:ℕ) : ℤ_[p]) ^ (k-1) * (p:ℤ_[p]) *
            (((j*a/p:ℕ)) : ℤ_[p]) +
        (p:ℤ_[p]) ^ 2*wj j hj:=fun j hj=> by rw [h_rj_eq j];exact hwj j hj
  have h_perm: ((∑ j ∈ Finset.range p,((j*a) % p) ^ k:ℕ) : ℤ_[p]) =
      ((∑ j ∈ Finset.range p,j^k:ℕ) : ℤ_[p]) :=by
    congr 1;exact yV ha_coprime (fun n :ℕ=> n ^k)
  set w :ℕ → ℤ_[p] :=fun j => if h :j ∈ Finset.range p then wj j h else 0 with hw_def
  have hw_eq: ∀ (j:ℕ) (hj:j ∈ Finset.range p),w j=wj j hj:=fun j hj=> by
    change (if h :j ∈ Finset.range p then wj j h else 0) = wj j hj;simp [hj]
  set W_sum:ℤ_[p] := ∑ j ∈ Finset.range p,w j with hW_sum
  refine ⟨-W_sum,?_⟩
  have h_sum_binom: (((∑ j ∈ Finset.range p,((j*a) % p) ^ k:ℕ)) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j*a:ℕ) : ℤ_[p]) ^ k-
          (k:ℤ_[p]) * ((j*a:ℕ) : ℤ_[p]) ^ (k-1) * (p:ℤ_[p]) *
            (((j*a/p:ℕ)) : ℤ_[p]) +
        (p:ℤ_[p]) ^ 2*w j) :=by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j hj=> ?_
    rw [hw_eq j hj,Nat.cast_pow]
    exact h_per_j j hj
  have h_sum_ℤp: ((∑ j ∈ Finset.range p,j^k:ℕ) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j*a:ℕ) : ℤ_[p]) ^ k-
          (k:ℤ_[p]) * ((j*a:ℕ) : ℤ_[p]) ^ (k-1) * (p:ℤ_[p]) *
            (((j*a/p:ℕ)) : ℤ_[p]) +
        (p:ℤ_[p]) ^ 2*w j) :=by
    rw [← h_perm,h_sum_binom]
  have h_ja_pow: ∀ j:ℕ,((j*a:ℕ) : ℤ_[p]) ^ k=
      ((a:ℤ_[p])) ^ k* ((j:ℕ) : ℤ_[p]) ^ k:=fun j => by push_cast;ring
  have h_ja_pow_sub1: ∀ j:ℕ,((j*a:ℕ) : ℤ_[p]) ^ (k-1) =
      ((a:ℤ_[p])) ^ (k-1) * ((j:ℕ) : ℤ_[p]) ^ (k-1) :=fun j => by push_cast;ring
  have h_sum_rewrite:
      ∑ j ∈ Finset.range p,
        (((j*a:ℕ) : ℤ_[p]) ^ k-
          (k:ℤ_[p]) * ((j*a:ℕ) : ℤ_[p]) ^ (k-1) * (p:ℤ_[p]) *
            (((j*a/p:ℕ)) : ℤ_[p]) +
        (p:ℤ_[p]) ^ 2*w j) =
      ∑ j ∈ Finset.range p,
        ((a:ℤ_[p]) ^ k* ((j:ℕ) : ℤ_[p]) ^ k-
          (k:ℤ_[p]) * (a:ℤ_[p]) ^ (k-1) * (p:ℤ_[p]) *
            (((j:ℕ) : ℤ_[p]) ^ (k-1) * (((j*a/p:ℕ)) : ℤ_[p])) +
        (p:ℤ_[p]) ^ 2*w j) :=by
    refine Finset.sum_congr rfl fun j _=> ?_
    rw [h_ja_pow j,h_ja_pow_sub1 j];ring
  rw [h_sum_rewrite] at h_sum_ℤp
  have h_three:
      ∑ j ∈ Finset.range p,
        ((a:ℤ_[p]) ^ k* ((j:ℕ) : ℤ_[p]) ^ k-
          (k:ℤ_[p]) * (a:ℤ_[p]) ^ (k-1) * (p:ℤ_[p]) *
            (((j:ℕ) : ℤ_[p]) ^ (k-1) * (((j*a/p:ℕ)) : ℤ_[p])) +
        (p:ℤ_[p]) ^ 2*w j) =
      (a:ℤ_[p]) ^ k* (∑ j ∈ Finset.range p,((j:ℕ) : ℤ_[p]) ^ k) -
      (k:ℤ_[p]) * (a:ℤ_[p]) ^ (k-1) * (p:ℤ_[p]) *
        (∑ j ∈ Finset.range p,
          ((j:ℕ) : ℤ_[p]) ^ (k-1) * ((j*a/p:ℕ) : ℤ_[p])) +
      (p:ℤ_[p]) ^ 2*W_sum:=by
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,
        ← Finset.mul_sum,← Finset.mul_sum]
    congr 1;rw [hW_sum,Finset.mul_sum]
  have h_cast1: (∑ j ∈ Finset.range p,((j:ℕ) : ℤ_[p]) ^ k) =
      ((∑ j ∈ Finset.range p,j^k:ℕ) : ℤ_[p]) :=by push_cast;rfl
  have h_cast2: (∑ j ∈ Finset.range p,
        ((j:ℕ) : ℤ_[p]) ^ (k-1) * ((j*a/p:ℕ) : ℤ_[p])) =
      ((∑ j ∈ Finset.range p,j^ (k-1) * (j*a/p) : ℕ) : ℤ_[p]) :=by push_cast;rfl
  rw [h_three,h_cast1,h_cast2] at h_sum_ℤp
  linear_combination-h_sum_ℤp
theorem wf
    {p:ℕ} [hp:Fact p.Prime] (hp_odd:p ≠ 2)
    {a:ℕ} (ha_coprime: ¬ (p:ℕ) ∣ a)
    {k:ℕ} (hk_two:2 ≤ k) (hk_even:Even k) (_hk_coprime: ¬ (p-1) ∣ k)
    (h_p_not_dvd_kPlus: ¬ (p:ℕ) ∣ (k+1))
    (h_below_k: ∀ j,j ≤ k → ¬ (p:ℕ) ^ 3 ∣ (j+1)) :
    ∃ z :ℤ_[p],
      ((a:ℚ_[p]) ^ k-1) * ((bernoulli k :ℚ) : ℚ_[p]) -
          (k:ℚ_[p]) * ((a:ℚ_[p]) ^ (k-1)) *
            ((∑ j ∈ Finset.range p,j^ (k-1) * (j*a/p) : ℕ) : ℚ_[p]) =
        (p:ℚ_[p]) * (z:ℚ_[p]) :=by
  have hp:Nat.Prime p :=hp.out
  have hp_gt:2 < p:=lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hk_pos:0 < k:=by omega
  have hpQ_ne: (p:ℚ_[p]) ≠ 0:=by exact_mod_cast hp.ne_zero
  obtain ⟨W,hW⟩ :=yP ha_coprime hk_pos
  obtain ⟨W',hW'⟩ :=rb hp_odd hk_two hk_even
    (fun j hj hj_two hj_even=>
      sJ hp_odd hj_two hj_even
        (fun j' hj'=> h_below_k j' (Nat.le_trans hj' hj.le)))
  have hkp1_unit:IsUnit ((k+1:ℕ) : ℤ_[p]) :=by
    rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr h_p_not_dvd_kPlus
  set u :ℤ_[p] := (hkp1_unit.unit⁻¹: (ℤ_[p])ˣ).val with hu_def
  have hu_mul: ((k+1:ℕ) : ℤ_[p]) * u=1:=by
    change ((hkp1_unit.unit*hkp1_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) = 1;simp
  have hu_mul_Qp: ((k+1:ℕ) : ℚ_[p]) * ((u:ℤ_[p]) : ℚ_[p]) = 1:=by
    simpa using congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hu_mul
  refine ⟨W- ((a:ℤ_[p]) ^ k-1) * u*W',?_⟩
  set S1:ℚ_[p] := ∑ j ∈ Finset.range p,(j:ℚ_[p]) ^ k with hS1_def
  set S2:ℚ_[p] :=
    ∑ j ∈ Finset.range p,(j:ℚ_[p]) ^ (k-1) * ((j*a/p:ℕ) : ℚ_[p]) with hS2_def
  have hW_Q: ((a:ℚ_[p]) ^ k-1) * S1-
      (k:ℚ_[p]) * (a:ℚ_[p]) ^ (k-1) * (p:ℚ_[p]) * S2=
      (p:ℚ_[p]) ^ 2* ((W:ℤ_[p]) : ℚ_[p]) :=by
    have:=congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hW
    simp only [PadicInt.coe_sub,PadicInt.coe_mul,PadicInt.coe_pow,
      PadicInt.coe_natCast,PadicInt.coe_one] at this
    rw [hS1_def,hS2_def]
    push_cast at this
    exact this
  have hkp1Q_ne: ((k+1:ℕ) : ℚ_[p]) ≠ 0:=Nat.cast_ne_zero.mpr (by omega)
  have h_S1_sub:S1- (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p]) =
      ((u:ℤ_[p]) : ℚ_[p]) * (p:ℚ_[p]) ^ 2* ((W':ℤ_[p]) : ℚ_[p]) :=by
    have h_mul: ((k+1:ℕ) : ℚ_[p]) *
        (S1- (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p])) =
        ((k+1:ℕ) : ℚ_[p]) *
        (((u:ℤ_[p]) : ℚ_[p]) * (p:ℚ_[p]) ^ 2* ((W':ℤ_[p]) : ℚ_[p])) :=by
      rw [hS1_def,hW']
      linear_combination-((p:ℚ_[p]) ^ 2* ((W':ℤ_[p]) : ℚ_[p])) * hu_mul_Qp
    exact mul_left_cancel₀ hkp1Q_ne h_mul
  have hS1_eq:S1= (p:ℚ_[p]) * ((bernoulli k :ℚ) : ℚ_[p]) +
      ((u:ℤ_[p]) : ℚ_[p]) * (p:ℚ_[p]) ^ 2* ((W':ℤ_[p]) : ℚ_[p]) :=by
    linear_combination h_S1_sub
  rw [hS1_eq] at hW_Q
  have hS2_cast: ((∑ j ∈ Finset.range p,j^ (k-1) * (j*a/p) : ℕ) : ℚ_[p]) = S2:=by
    rw [hS2_def];push_cast;rfl
  have hX: ((a:ℚ_[p]) ^ k-1) * ((bernoulli k :ℚ) : ℚ_[p]) -
      (k:ℚ_[p]) * (a:ℚ_[p]) ^ (k-1) * S2=
      (p:ℚ_[p]) * (((W:ℤ_[p]) : ℚ_[p]) -
        ((a:ℚ_[p]) ^ k-1) * ((u:ℤ_[p]) : ℚ_[p]) * ((W':ℤ_[p]) : ℚ_[p])) :=
    mul_left_cancel₀ hpQ_ne (by linear_combination hW_Q)
  rw [hS2_cast];push_cast;linear_combination hX
end KummerCriterion
end
end Module38
-- Source: KummerCriterion.KummerCongruence.Kummer
section Module39
noncomputable section
namespace KummerCriterion
theorem y0
    {p:ℕ} [hp:Fact p.Prime] (hp_odd:p ≠ 2)
    {m n :ℕ} (hm_pos:0 < m) (hn_pos:0 < n)
    (hm_even:Even m) (hn_even:Even n)
    (h_pSubOne_not_dvd_n: ¬ (p-1) ∣ n)
    (h_mn_modEq:m ≡ n [MOD (p-1)])
    (hm_coprime_p: ¬ (p:ℕ) ∣ m) (hn_coprime_p: ¬ (p:ℕ) ∣ n)
    (hm_p_plus: ¬ (p:ℕ) ∣ (m+1)) (hn_p_plus: ¬ (p:ℕ) ∣ (n+1))
    (h_below_m: ∀ j,j ≤ m → ¬ (p:ℕ) ^ 3 ∣ (j+1))
    (h_below_n: ∀ j,j ≤ n → ¬ (p:ℕ) ^ 3 ∣ (j+1)) :
    ∃ z :ℤ_[p],
      (((bernoulli m :ℚ) / m:ℚ) : ℚ_[p]) -
          (((bernoulli n :ℚ) / n:ℚ) : ℚ_[p]) =
        (p:ℚ_[p]) * (z:ℚ_[p]) :=by
  have hp:Nat.Prime p :=hp.out
  have hp_gt:2 < p:=lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hpQ_ne: (p:ℚ_[p]) ≠ 0:=by exact_mod_cast hp.ne_zero
  have hm_two:2 ≤ m:=by
    obtain ⟨r,hr⟩ :=hm_even;omega
  have hn_two:2 ≤ n:=by
    obtain ⟨r,hr⟩ :=hn_even;omega
  have h_pSubOne_not_dvd_m: ¬ (p-1) ∣ m:=by
    intro hdvd
    have h_n_mod:n ≡ 0 [MOD (p-1)] :=h_mn_modEq.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd)
    exact h_pSubOne_not_dvd_n (Nat.modEq_zero_iff_dvd.mp h_n_mod)
  obtain ⟨g,hg_gen⟩ :=IsCyclic.exists_generator (α:= (ZMod p)ˣ)
  set a :ℕ:= (g:ZMod p).val with ha_def
  have ha_lt:a < p:=ZMod.val_lt _
  have ha_coprimeZ:Nat.Coprime a p:=ZMod.val_coe_unit_coprime g
  have ha_coprime: ¬ (p:ℕ) ∣ a:=by
    rw [Nat.coprime_comm] at ha_coprimeZ
    exact (hp.coprime_iff_not_dvd.mp ha_coprimeZ)
  have ha_cast: ((a:ℕ) : ZMod p) = (g:ZMod p) :=by
    rw [ha_def];exact ZMod.natCast_zmod_val _
  have hg_order:orderOf g =p-1:=by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg_gen,Nat.card_eq_fintype_card,ZMod.card_units]
  have hk_coprime_m: ¬ (p-1) ∣ m:=h_pSubOne_not_dvd_m
  have hk_coprime_n: ¬ (p-1) ∣ n:=h_pSubOne_not_dvd_n
  obtain ⟨z_m,hz_m⟩ :=wf hp_odd ha_coprime hm_two hm_even
    hk_coprime_m hm_p_plus h_below_m
  obtain ⟨z_n,hz_n⟩ :=wf hp_odd ha_coprime hn_two hn_even
    hk_coprime_n hn_p_plus h_below_n
  set Am:ℤ_[p] := (a:ℤ_[p]) ^ m with hAm_def
  set An:ℤ_[p] := (a:ℤ_[p]) ^ n with hAn_def
  set Am1:ℤ_[p] := (a:ℤ_[p]) ^ (m-1) with hAm1_def
  set An1:ℤ_[p] := (a:ℤ_[p]) ^ (n-1) with hAn1_def
  set Sm:ℕ:= ∑ j ∈ Finset.range p,j^ (m-1) * (j*a/p) with hSm_def
  set Sn:ℕ:= ∑ j ∈ Finset.range p,j^ (n-1) * (j*a/p) with hSn_def
  have h_gmn_eq:g^m=g^n:=by
    rw [pow_eq_pow_iff_modEq,hg_order];exact h_mn_modEq
  have h_mn1_modEq: (m-1) ≡ (n-1) [MOD (p-1)] :=by
    have h1: (m-1) + 1=m:=Nat.succ_pred_eq_of_pos hm_pos
    have h2: (n-1) + 1=n:=Nat.succ_pred_eq_of_pos hn_pos
    have h_mod_add1: (m-1) + 1 ≡ (n-1) + 1 [MOD (p-1)] :=by
      rw [h1,h2];exact h_mn_modEq
    exact Nat.ModEq.add_right_cancel' 1 h_mod_add1
  have h_gmn1_eq:g^ (m-1) = g^ (n-1) :=by
    rw [pow_eq_pow_iff_modEq,hg_order];exact h_mn1_modEq
  have h_mn_ZMod: ((a:ℕ) : ZMod p) ^ m= ((a:ℕ) : ZMod p) ^ n:=by
    rw [ha_cast]
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun u : (ZMod p)ˣ=> (u:ZMod p)) h_gmn_eq
  have h_mn1_ZMod: ((a:ℕ) : ZMod p) ^ (m-1) = ((a:ℕ) : ZMod p) ^ (n-1) :=by
    rw [ha_cast]
    simpa [Units.val_pow_eq_pow_val] using
      congrArg (fun u : (ZMod p)ˣ=> (u:ZMod p)) h_gmn1_eq
  have h_mk_eq_zmod: ∀ {x y :ℤ_[p]},PadicInt.toZMod x =PadicInt.toZMod y →
      x-y ∈ Ideal.span ({(p:ℤ_[p])} : Set ℤ_[p]) :=fun {x y} h => by
    have h_sub:PadicInt.toZMod (x-y) = 0:=by rw [map_sub,h,sub_self]
    have h_ker:x-y ∈ IsLocalRing.maximalIdeal ℤ_[p] :=by
      rw [← PadicInt.ker_toZMod];exact h_sub
    rwa [PadicInt.maximalIdeal_eq_span_p] at h_ker
  have hpℤ_ne: (p:ℤ_[p]) ≠ 0:=Nat.cast_ne_zero.mpr hp.ne_zero
  have h_toZMod_a:PadicInt.toZMod (a:ℤ_[p]) = ((a:ℕ) : ZMod p) :=by rw [map_natCast]
  have h_Am_An_toZMod:PadicInt.toZMod Am=PadicInt.toZMod An:=by
    rw [hAm_def,hAn_def,map_pow,map_pow,h_toZMod_a];exact h_mn_ZMod
  obtain ⟨d_A,hd_A⟩ :=Ideal.mem_span_singleton.mp (h_mk_eq_zmod h_Am_An_toZMod)
  have h_Am1_An1_toZMod:PadicInt.toZMod Am1=PadicInt.toZMod An1:=by
    rw [hAm1_def,hAn1_def,map_pow,map_pow,h_toZMod_a];exact h_mn1_ZMod
  obtain ⟨d_A1,hd_A1⟩ :=Ideal.mem_span_singleton.mp (h_mk_eq_zmod h_Am1_An1_toZMod)
  have h_pow_pred_ZMod: ∀ j:ℕ,j < p → j ≠ 0 →
      ((j:ℕ) : ZMod p) ^ (m-1) = ((j:ℕ) : ZMod p) ^ (n-1) :=by
    intro j hjp hj_ne
    have hj_coprime:Nat.Coprime j p:=
      (hp.coprime_iff_not_dvd.mpr
        (fun hdvd=> hj_ne (Nat.eq_zero_of_dvd_of_lt hdvd hjp))).symm
    lift (((j:ℕ) : ZMod p)) to (ZMod p)ˣ using
      (ZMod.isUnit_iff_coprime j p).mpr hj_coprime
      with u hu
    rw [← Units.val_pow_eq_pow_val,← Units.val_pow_eq_pow_val]
    congr 1
    rw [pow_eq_pow_iff_modEq]
    have h_ord_dvd:orderOf u ∣ (p-1) :=by
      rw [← ZMod.card_units,← Nat.card_eq_fintype_card];exact orderOf_dvd_natCard u
    exact h_mn1_modEq.of_dvd h_ord_dvd
  have h_Sm_Sn_toZMod: ((Sm:ℕ) : ZMod p) = ((Sn:ℕ) : ZMod p) :=by
    rw [hSm_def,hSn_def];push_cast
    refine Finset.sum_congr rfl fun j hj=> ?_
    rw [Finset.mem_range] at hj
    congr 1
    by_cases hj_ne:j=0
    · rw [hj_ne]
      simp [zero_pow (by omega:m-1 ≠ 0),zero_pow (by omega:n-1 ≠ 0)]
    · exact h_pow_pred_ZMod j hj hj_ne
  have h_Sm_Sn_toZMod':PadicInt.toZMod ((Sm:ℤ_[p])) = PadicInt.toZMod ((Sn:ℤ_[p])) :=by
    rw [map_natCast,map_natCast];exact h_Sm_Sn_toZMod
  obtain ⟨d_S,hd_S⟩ :=Ideal.mem_span_singleton.mp (h_mk_eq_zmod h_Sm_Sn_toZMod')
  have h_ax_sub_one_unit: ∀ {k:ℕ},¬ (p-1) ∣ k →
      IsUnit ((a:ℤ_[p]) ^ k-1) :=fun {k} hk=> by
    rw [PadicInt.isUnit_iff]
    by_contra h_norm
    have h_mem: ((a:ℤ_[p]) ^ k-1:ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] :=
      PadicInt.mem_nonunits.mpr (lt_of_le_of_ne (PadicInt.norm_le_one _) h_norm)
    rw [← PadicInt.ker_toZMod,RingHom.mem_ker] at h_mem
    rw [map_sub,map_one,map_pow,map_natCast,ha_cast,sub_eq_zero] at h_mem
    have h_gk:g^k=1:=
      Units.ext (by rw [Units.val_pow_eq_pow_val,Units.val_one];exact h_mem)
    exact hk (hg_order ▸ orderOf_dvd_of_pow_eq_one h_gk)
  have h_Am_sub_one_unit:IsUnit (Am-1) :=by
    rw [hAm_def];exact h_ax_sub_one_unit h_pSubOne_not_dvd_m
  have h_An_sub_one_unit:IsUnit (An-1) :=by
    rw [hAn_def];exact h_ax_sub_one_unit h_pSubOne_not_dvd_n
  have h_m_unit:IsUnit ((m:ℕ) : ℤ_[p]) :=by
    rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hm_coprime_p
  have h_n_unit:IsUnit ((n:ℕ) : ℤ_[p]) :=by
    rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr hn_coprime_p
  have hunit_inv: ∀ {x:ℤ_[p]} (hx:IsUnit x),x* (hx.unit⁻¹: (ℤ_[p])ˣ).val=1:=by
    intro x hx
    change ((hx.unit*hx.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) = 1;simp
  set mInv:ℤ_[p] := (h_m_unit.unit⁻¹: (ℤ_[p])ˣ).val
  have hmInv_mul: ((m:ℕ) : ℤ_[p]) * mInv=1:=hunit_inv h_m_unit
  set nInv:ℤ_[p] := (h_n_unit.unit⁻¹: (ℤ_[p])ˣ).val
  have hnInv_mul: ((n:ℕ) : ℤ_[p]) * nInv=1:=hunit_inv h_n_unit
  set AmInv:ℤ_[p] := (h_Am_sub_one_unit.unit⁻¹: (ℤ_[p])ˣ).val
  have hAmInv_mul: (Am-1) * AmInv=1:=hunit_inv h_Am_sub_one_unit
  set AnInv:ℤ_[p] := (h_An_sub_one_unit.unit⁻¹: (ℤ_[p])ˣ).val
  have hAnInv_mul: (An-1) * AnInv=1:=hunit_inv h_An_sub_one_unit
  set SmZ:ℤ_[p] := ((Sm:ℕ) : ℤ_[p]) with hSmZ_def
  set SnZ:ℤ_[p] := ((Sn:ℕ) : ℤ_[p]) with hSnZ_def
  set E :ℤ_[p] := (Am-1) * (d_A1*SmZ+An1*d_S) - d_A*Am1*SmZ with hE_def
  have hE_eq: (An-1) * Am1*SmZ- (Am-1) * An1*SnZ= (p:ℤ_[p]) * E:=by
    have h_An_eq:An=Am- (p:ℤ_[p]) * d_A:=by linear_combination-hd_A
    have h_An1_eq:An1=Am1- (p:ℤ_[p]) * d_A1:=by linear_combination-hd_A1
    have h_SnZ_eq:SnZ=SmZ- (p:ℤ_[p]) * d_S:=by linear_combination-hd_S
    rw [hE_def,h_An_eq,h_An1_eq,h_SnZ_eq]
    ring
  refine ⟨AmInv*AnInv*E+AmInv*mInv*z_m-AnInv*nInv*z_n,?_⟩
  set Am_Q:ℚ_[p] := (Am:ℚ_[p]) with hAm_Q_def
  set An_Q:ℚ_[p] := (An:ℚ_[p]) with hAn_Q_def
  set Am1_Q:ℚ_[p] := (Am1:ℚ_[p]) with hAm1_Q_def
  set An1_Q:ℚ_[p] := (An1:ℚ_[p]) with hAn1_Q_def
  set Sm_Q:ℚ_[p] := (SmZ:ℚ_[p]) with hSm_Q_def
  set Sn_Q:ℚ_[p] := (SnZ:ℚ_[p]) with hSn_Q_def
  set mQ:ℚ_[p] := ((m:ℕ) : ℚ_[p]) with hmQ_def
  set nQ:ℚ_[p] := ((n:ℕ) : ℚ_[p]) with hnQ_def
  set Bm_Q:ℚ_[p] := ((bernoulli m :ℚ) : ℚ_[p]) with hBm_Q_def
  set Bn_Q:ℚ_[p] := ((bernoulli n :ℚ) : ℚ_[p]) with hBn_Q_def
  have hmQ_ne:mQ ≠ 0:=Nat.cast_ne_zero.mpr hm_pos.ne'
  have hnQ_ne:nQ ≠ 0:=Nat.cast_ne_zero.mpr hn_pos.ne'
  set Bm_div:ℚ_[p] := (((bernoulli m :ℚ) / m:ℚ) : ℚ_[p]) with hBm_div_def
  set Bn_div:ℚ_[p] := (((bernoulli n :ℚ) / n:ℚ) : ℚ_[p]) with hBn_div_def
  have h_mBm:mQ*Bm_div=Bm_Q:=by
    rw [hBm_div_def,hmQ_def,hBm_Q_def];push_cast
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hm_pos.ne': ((m:ℕ) : ℚ_[p]) ≠ 0)]
  have h_nBn:nQ*Bn_div=Bn_Q:=by
    rw [hBn_div_def,hnQ_def,hBn_Q_def];push_cast
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn_pos.ne': ((n:ℕ) : ℚ_[p]) ≠ 0)]
  have h_Sm_cast:
      ((∑ j ∈ Finset.range p,j^ (m-1) * (j*a/p) : ℕ) : ℚ_[p]) = Sm_Q:=by
    rw [hSm_Q_def,hSmZ_def,hSm_def,PadicInt.coe_natCast]
  have h_Sn_cast:
      ((∑ j ∈ Finset.range p,j^ (n-1) * (j*a/p) : ℕ) : ℚ_[p]) = Sn_Q:=by
    rw [hSn_Q_def,hSnZ_def,hSn_def,PadicInt.coe_natCast]
  have hz_m_Q: (Am_Q-1) * Bm_Q-mQ*Am1_Q*Sm_Q= (p:ℚ_[p]) * (z_m:ℚ_[p]) :=by
    have:=hz_m
    rw [hAm_Q_def,hAm1_Q_def,hAm_def,hAm1_def,hBm_Q_def,hmQ_def]
    rw [h_Sm_cast] at this;convert! this using 2
  have hz_n_Q: (An_Q-1) * Bn_Q-nQ*An1_Q*Sn_Q= (p:ℚ_[p]) * (z_n:ℚ_[p]) :=by
    have:=hz_n
    rw [hAn_Q_def,hAn1_Q_def,hAn_def,hAn1_def,hBn_Q_def,hnQ_def]
    rw [h_Sn_cast] at this;convert! this using 2
  have hE_eq_Q: (An_Q-1) * Am1_Q*Sm_Q- (Am_Q-1) * An1_Q*Sn_Q=
      (p:ℚ_[p]) * ((E:ℤ_[p]) : ℚ_[p]) :=by
    have:=congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hE_eq
    rw [hAm_Q_def,hAn_Q_def,hAm1_Q_def,hAn1_Q_def,hSm_Q_def,hSn_Q_def]
    push_cast at this ⊢
    linear_combination this
  have h_mQ_mInv:mQ* ((mInv:ℤ_[p]) : ℚ_[p]) = 1:=by
    rw [hmQ_def];simpa using congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hmInv_mul
  have h_nQ_nInv:nQ* ((nInv:ℤ_[p]) : ℚ_[p]) = 1:=by
    rw [hnQ_def];simpa using congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hnInv_mul
  have h_Am_AmInv: (Am_Q-1) * ((AmInv:ℤ_[p]) : ℚ_[p]) = 1:=by
    have:=congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hAmInv_mul
    rw [hAm_Q_def];push_cast at this;exact this
  have h_An_AnInv: (An_Q-1) * ((AnInv:ℤ_[p]) : ℚ_[p]) = 1:=by
    have:=congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hAnInv_mul
    rw [hAn_Q_def];push_cast at this;exact this
  set AmInv_Q:ℚ_[p] := ((AmInv:ℤ_[p]) : ℚ_[p]) with hAmInv_Q_def
  set AnInv_Q:ℚ_[p] := ((AnInv:ℤ_[p]) : ℚ_[p]) with hAnInv_Q_def
  set mInv_Q:ℚ_[p] := ((mInv:ℤ_[p]) : ℚ_[p]) with hmInv_Q_def
  set nInv_Q:ℚ_[p] := ((nInv:ℤ_[p]) : ℚ_[p]) with hnInv_Q_def
  set z_m_Q:ℚ_[p] := ((z_m:ℤ_[p]) : ℚ_[p]) with hz_m_Q_def
  set z_n_Q:ℚ_[p] := ((z_n:ℤ_[p]) : ℚ_[p]) with hz_n_Q_def
  set E_Q:ℚ_[p] := ((E:ℤ_[p]) : ℚ_[p]) with hE_Q_def
  have h_witness_eq: ((((AmInv*AnInv*E+AmInv*mInv*z_m-
      AnInv*nInv*z_n:ℤ_[p]) : ℚ_[p]))) =
      AmInv_Q*AnInv_Q*E_Q+AmInv_Q*mInv_Q*z_m_Q-AnInv_Q*nInv_Q*z_n_Q:=by
    rw [hAmInv_Q_def,hAnInv_Q_def,hmInv_Q_def,hnInv_Q_def,hz_m_Q_def,hz_n_Q_def,hE_Q_def]
    push_cast;ring
  rw [h_witness_eq]
  have h_Am_sub_one_ne:Am_Q-1 ≠ 0:=fun h0=> one_ne_zero <| by
    rw [← h_Am_AmInv,h0,zero_mul]
  have h_An_sub_one_ne:An_Q-1 ≠ 0:=fun h0=> one_ne_zero <| by
    rw [← h_An_AnInv,h0,zero_mul]
  have h_key: (Am_Q-1) * (An_Q-1) * mQ*nQ* (Bm_div-Bn_div) =
      (Am_Q-1) * (An_Q-1) * mQ*nQ* ((p:ℚ_[p]) *
        (AmInv_Q*AnInv_Q*E_Q+AmInv_Q*mInv_Q*z_m_Q-AnInv_Q*nInv_Q*z_n_Q)) :=by
    have h_lhs:
        (Am_Q-1) * (An_Q-1) * mQ*nQ* (Bm_div-Bn_div) =
        (An_Q-1) * nQ* ((Am_Q-1) * (mQ*Bm_div)) -
          (Am_Q-1) * mQ* ((An_Q-1) * (nQ*Bn_div)) :=by ring
    rw [h_lhs,h_mBm,h_nBn]
    have h_Bm_expand: (Am_Q-1) * Bm_Q=mQ*Am1_Q*Sm_Q+ (p:ℚ_[p]) * z_m_Q:=by
      rw [hz_m_Q_def];linear_combination hz_m_Q
    have h_Bn_expand: (An_Q-1) * Bn_Q=nQ*An1_Q*Sn_Q+ (p:ℚ_[p]) * z_n_Q:=by
      rw [hz_n_Q_def];linear_combination hz_n_Q
    rw [h_Bm_expand,h_Bn_expand]
    have h_E_expand: (An_Q-1) * nQ* (mQ*Am1_Q*Sm_Q) -
        (Am_Q-1) * mQ* (nQ*An1_Q*Sn_Q) =
        mQ*nQ* ((An_Q-1) * Am1_Q*Sm_Q- (Am_Q-1) * An1_Q*Sn_Q) :=by ring
    rw [show (An_Q-1) * nQ* (mQ*Am1_Q*Sm_Q+ (p:ℚ_[p]) * z_m_Q) -
        (Am_Q-1) * mQ* (nQ*An1_Q*Sn_Q+ (p:ℚ_[p]) * z_n_Q) =
        ((An_Q-1) * nQ* (mQ*Am1_Q*Sm_Q) -
          (Am_Q-1) * mQ* (nQ*An1_Q*Sn_Q)) +
        ((p:ℚ_[p]) * ((An_Q-1) * nQ*z_m_Q- (Am_Q-1) * mQ*z_n_Q)) from
      by ring,h_E_expand,hE_eq_Q]
    have h_rhs_goal:
        (Am_Q-1) * (An_Q-1) * mQ*nQ* ((p:ℚ_[p]) *
          (AmInv_Q*AnInv_Q*E_Q+AmInv_Q*mInv_Q*z_m_Q-
            AnInv_Q*nInv_Q*z_n_Q)) =
        (p:ℚ_[p]) * (((Am_Q-1) * AmInv_Q) * ((An_Q-1) * AnInv_Q) * mQ*nQ*E_Q) +
        (p:ℚ_[p]) * ((An_Q-1) * ((Am_Q-1) * AmInv_Q) *
          (mQ*mInv_Q) * nQ*z_m_Q) -
        (p:ℚ_[p]) * ((Am_Q-1) * ((An_Q-1) * AnInv_Q) *
          (nQ*nInv_Q) * mQ*z_n_Q) :=by
      rw [hAmInv_Q_def,hAnInv_Q_def,hmInv_Q_def,hnInv_Q_def];ring
    rw [h_rhs_goal,h_Am_AmInv,h_An_AnInv,h_mQ_mInv,h_nQ_nInv]
    ring
  have h_cancel_ne: (Am_Q-1) * (An_Q-1) * mQ*nQ ≠ 0:=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h_Am_sub_one_ne h_An_sub_one_ne) hmQ_ne) hnQ_ne
  exact mul_left_cancel₀ h_cancel_ne h_key
end KummerCriterion
end
end Module39
-- Source: KummerCriterion.KummerCongruence.Bridge
section Module40
noncomputable section
namespace KummerCriterion
theorem sL
    {p:ℕ} [hp:Fact p.Prime] (hp_odd:p ≠ 2)
    {n:ℕ} (hn_odd:Odd n) (hn_pos:0 < n)
    (h_pSubOne_not_dvd_nPlus: ¬ (p-1) ∣ (n+1))
    (hn_p_plus: ¬ (p:ℕ) ∣ (n+1))
    (hn_p_plus_two: ¬ (p:ℕ) ∣ (n+2))
    (hn_small:n+1 < p-1) :
    ∃ z :ℤ_[p],
      qf ((q7 p) ^ n) 1 -
          (((bernoulli (n+1) : ℚ) / (n+1) : ℚ) : ℚ_[p]) =
        (p:ℚ_[p]) * (z:ℚ_[p]) :=by
  have hp:Nat.Prime p :=hp.out
  have hp_gt:2 < p:=lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  set t :ℕ:=p*n+1 with ht_def
  have hpQ_ne: (p:ℚ_[p]) ≠ 0:=by exact_mod_cast hp.ne_zero
  have hn_le_pm3:n ≤ p-3:=by omega
  have h_t_lt_p_sq:t+1 < p^2:=by
    have ht_eq:t+1=p*n+2:=by simp [ht_def]
    obtain ⟨r,hr⟩ : ∃ r,p=r+3:= ⟨p-3,by omega⟩
    rw [ht_eq,hr,pow_two]
    have hn_le_r:n ≤ r:=by omega
    nlinarith [hn_le_r,Nat.zero_le r]
  have h_p_sq_lt_p_cube:p^2 < p^3:=by
    have h_p2_pos:0 < p^2:=by positivity
    simpa [pow_succ] using (Nat.mul_lt_mul_left h_p2_pos).mpr hp.one_lt
  have h_below_t: ∀ j,j ≤ t → ¬ (p:ℕ) ^ 3 ∣ (j+1) :=fun j hj hdvd=> by
    have h_j1_lt:j+1 < p^3:=
      calc j +1 ≤ t+1:=by omega
        _ < p^2:=h_t_lt_p_sq
        _ < p^3:=h_p_sq_lt_p_cube
    exact absurd (Nat.le_of_dvd (Nat.succ_pos j) hdvd) (by omega)
  have h_below_n1: ∀ j,j ≤ n+1 → ¬ (p:ℕ) ^ 3 ∣ (j+1) :=fun j hj hdvd=> by
    have h_j1_lt:j+1 < p^3:=
      calc j +1 ≤ n+2:=by omega
        _ ≤ p:=by omega
        _ < p^2:=by nlinarith [hp.one_lt]
        _ < p^3:=h_p_sq_lt_p_cube
    exact absurd (Nat.le_of_dvd (Nat.succ_pos j) hdvd) (by omega)
  have h_ingr1: ∃ z:ℤ_[p],
      (p:ℚ_[p]) * qf ((q7 p) ^ n) 1 -
          (∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t) =
        (p:ℚ_[p]) ^ 2* (z:ℚ_[p]) :=by
    have hn_ne_zero:n ≠ 0:=hn_pos.ne'
    have hn_not_dvd: ¬ (p-1) ∣ n:=by
      intro hdvd
      have hp_minus_one_even:2 ∣ (p-1) :=by
        obtain ⟨k,_⟩ :=hp.odd_of_ne_two hp_odd
        exact ⟨k,by omega⟩
      have h2n:2 ∣ n:=dvd_trans hp_minus_one_even hdvd
      obtain ⟨k,hk⟩ :=hn_odd
      rw [hk] at h2n
      omega
    have hωQ_ne_one: (q7 p) ^ n ≠ 1:=
      sI (p:=p) hn_not_dvd
    have hT006:=rM
      (R:=ℚ_[p]) (N:=p) (χ:= (q7 p) ^ n) hωQ_ne_one
    have hterm_mem: ∀ a:ZMod p,
        (r4 p a) ^ n* (a.val:ℤ_[p]) - (a.val:ℤ_[p]) ^ t ∈
        (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2:=by
      intro a
      have h_mod:r4 p a ≡ (a.val:ℤ_[p]) ^ p
          [SMOD (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2] :=
        SModEq.sub_mem.mpr (xN (p:=p) a)
      have h_pow:=h_mod.pow n
      have h_mul:=h_pow.mul (SModEq.refl (a.val:ℤ_[p]))
      rw [SModEq.sub_mem] at h_mul
      have h_simp: ((a.val:ℤ_[p]) ^ p) ^ n* (a.val:ℤ_[p]) =
          (a.val:ℤ_[p]) ^ t:=by
        rw [← pow_mul,ht_def,← pow_succ]
      rw [h_simp] at h_mul
      exact h_mul
    let S :ℤ_[p] := ∑ a:ZMod p,(r4 p a) ^ n* (a.val:ℤ_[p])
    let T :ℤ_[p] := ∑ a:ZMod p,(a.val:ℤ_[p]) ^ t
    have hST_mem:S-T ∈ (IsLocalRing.maximalIdeal ℤ_[p]) ^ 2:=by
      change (∑ a :ZMod p,(r4 p a) ^ n* (a.val:ℤ_[p])) -
          (∑ a :ZMod p,(a.val:ℤ_[p]) ^ t) ∈ _
      rw [← Finset.sum_sub_distrib]
      exact Ideal.sum_mem _ fun a _=> hterm_mem a
    rw [PadicInt.maximalIdeal_eq_span_p,Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hST_mem
    obtain ⟨w,hw⟩ :=hST_mem
    refine ⟨w,?_⟩
    have hS_coe: ((S:ℤ_[p]) : ℚ_[p]) =
        ∑ a :ZMod p,((q7 p) ^ n) a * (a.val:ℚ_[p]) :=by
      change ((∑ a :ZMod p,(r4 p a) ^ n* (a.val:ℤ_[p]) : ℤ_[p]) : ℚ_[p]) = _
      rw [PadicInt.coe_sum]
      refine Finset.sum_congr rfl fun a _=> ?_
      rw [PadicInt.coe_mul,PadicInt.coe_pow,PadicInt.coe_natCast]
      congr 1
      rw [r6 (p:=p) (n:=n),
        MulChar.ringHomComp_apply,MulChar.pow_apply' _ hn_ne_zero,
        map_pow,rI]
      rfl
    have hT_coe: ((T:ℤ_[p]) : ℚ_[p]) =
        ∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t:=by
      change ((∑ a :ZMod p,(a.val:ℤ_[p]) ^ t:ℤ_[p]) : ℚ_[p]) = _
      rw [PadicInt.coe_sum]
      simp_rw [show ∀ a:ZMod p,
          (((a.val:ℤ_[p]) ^ t:ℤ_[p]) : ℚ_[p]) = ((a.val:ℚ_[p]) ^ t) from
        fun a => by rw [PadicInt.coe_pow,PadicInt.coe_natCast]]
      refine Finset.sum_nbij (fun a => a.val) ?_ ?_ ?_ ?_
      · intro a _;simp only [Finset.mem_range];exact ZMod.val_lt a
      · intros a _ b _ hab;exact ZMod.val_injective _ hab
      · intros k hk
        simp only [Finset.coe_univ,Set.image_univ,Set.mem_range]
        simp only [Finset.mem_coe,Finset.mem_range] at hk
        exact ⟨(k:ZMod p),ZMod.val_natCast_of_lt hk⟩
      · intros a _;rfl
    calc (p:ℚ_[p]) * qf ((q7 p) ^ n) 1 -
          (∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t)
        = (((S:ℤ_[p]) : ℚ_[p])) - ((T:ℤ_[p]) : ℚ_[p]) :=by
          rw [hS_coe,hT_coe,hT006]
      _= (((S-T:ℤ_[p]) : ℚ_[p])) :=by rw [PadicInt.coe_sub]
      _= (((p:ℤ_[p]) ^ 2*w:ℤ_[p]) : ℚ_[p]) :=by rw [hw]
      _= (p:ℚ_[p]) ^ 2* (w:ℚ_[p]) :=by push_cast;ring
  obtain ⟨z₁,hz₁⟩ :=h_ingr1
  have h_ingr2: ∃ z:ℤ_[p],
      (∑ k ∈ Finset.range p,(k:ℚ_[p]) ^ t) -
          (p:ℚ_[p]) * ((bernoulli t :ℚ) : ℚ_[p]) =
        (p:ℚ_[p]) ^ 2* (z:ℚ_[p]) :=by
    refine sX hp_odd ?_ ?_ ?_ ?_
    · have hpn:1 ≤ p*n:=Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    · exact ((hp.odd_of_ne_two hp_odd).mul hn_odd).add_one
    · intro hdvd
      have h_pn:p ∣ p*n:= ⟨n,rfl⟩
      have h_eq:t+1=p*n+2:=by simp [ht_def]
      rw [h_eq] at hdvd
      have hp2:p ∣ 2:=by simpa using Nat.dvd_sub hdvd h_pn
      exact absurd (Nat.le_of_dvd (by omega) hp2) (by omega)
    · intro j hj hj_two hj_even
      exact sJ hp_odd hj_two hj_even
        (fun j' hj'=> h_below_t j' (Nat.le_trans hj' hj.le))
  obtain ⟨z₂,hz₂⟩ :=h_ingr2
  have h_ingr3: ∃ z:ℤ_[p],
      (((bernoulli t :ℚ) : ℚ_[p])) -
          (((bernoulli (n+1) : ℚ) / (n+1) : ℚ) : ℚ_[p]) =
        (p:ℚ_[p]) * (z:ℚ_[p]) :=by
    have ht_pos:0 < t:=by simp [ht_def]
    have hn1_pos:0 < n+1:=Nat.succ_pos n
    have hn1_even:Even (n+1) :=hn_odd.add_one
    have hp_odd_pred:Odd p :=hp.odd_of_ne_two hp_odd
    have ht_even:Even t := (hp_odd_pred.mul hn_odd).add_one
    have h_mn_modEq:t ≡ (n+1) [MOD (p-1)] :=by
      have h_eq:t= (n+1) + (p-1) * n:=by
        simp only [ht_def]
        have hn_le:n ≤ p*n:=Nat.le_mul_of_pos_left n (by omega)
        have hpn: (p-1) * n=p*n-n:=by rw [Nat.sub_mul,Nat.one_mul]
        omega
      unfold Nat.ModEq;rw [h_eq,Nat.add_mul_mod_self_left]
    have ht_coprime: ¬ (p:ℕ) ∣ t:=fun h => by
      have h_pn:p ∣ p*n:= ⟨n,rfl⟩
      rw [(ht_def:t=p*n+1)] at h
      exact absurd (Nat.le_of_dvd (by omega) ((Nat.dvd_add_right h_pn).mp h)) (by omega)
    have ht_p_plus: ¬ (p:ℕ) ∣ (t+1) :=fun h => by
      have h_pn:p ∣ p*n:= ⟨n,rfl⟩
      have h_eq_t1:t+1=p*n+2:=by simp [ht_def]
      rw [h_eq_t1] at h
      have hp2:p ∣ 2:=by simpa using Nat.dvd_sub h h_pn
      exact absurd (Nat.le_of_dvd (by omega) hp2) (by omega)
    obtain ⟨z',hz'⟩ :=y0 hp_odd
      ht_pos hn1_pos ht_even hn1_even h_pSubOne_not_dvd_nPlus h_mn_modEq
      ht_coprime hn_p_plus ht_p_plus hn_p_plus_two h_below_t h_below_n1
    obtain ⟨bn1,hbn1⟩ :=u1 hp_odd (n+1) hn_small
    have hn1_unit:IsUnit ((n+1:ℕ) : ℤ_[p]) :=by
      rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
      exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hn1_pos (by omega))
    set n1Inv:ℤ_[p] := (hn1_unit.unit⁻¹: (ℤ_[p])ˣ).val
    have hn1Inv_mul: ((n+1:ℕ) : ℤ_[p]) * n1Inv=1:=by
      change ((hn1_unit.unit*hn1_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) = 1;simp
    have hn1Inv_mul_Qp: ((n+1:ℕ) : ℚ_[p]) * ((n1Inv:ℤ_[p]) : ℚ_[p]) = 1:=by
      simpa using congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) hn1Inv_mul
    set b :ℤ_[p] :=bn1*n1Inv with hb_def
    have hb:
        (((bernoulli (n+1) : ℚ) / (n+1:ℕ) : ℚ) : ℚ_[p]) =
          ((b:ℤ_[p]) : ℚ_[p]) :=by
      have h_div: (((bernoulli (n+1) : ℚ) / (n+1:ℕ) : ℚ) : ℚ_[p]) =
          ((bernoulli (n+1) : ℚ) : ℚ_[p]) / ((n+1:ℕ) : ℚ_[p]) :=by push_cast;rfl
      rw [h_div,hbn1,div_eq_mul_inv,
        inv_eq_of_mul_eq_one_right hn1Inv_mul_Qp]
      simp only [hb_def,PadicInt.coe_mul]
    refine ⟨(n:ℤ_[p]) * b+ (t:ℤ_[p]) * z',?_⟩
    have htQ_ne: (t:ℚ_[p]) ≠ 0:=by exact_mod_cast ht_pos.ne'
    rw [hb] at hz'
    have h_BtOverT: (((bernoulli t :ℚ) / t:ℚ) : ℚ_[p]) =
        (b:ℚ_[p]) + (p:ℚ_[p]) * (z':ℚ_[p]) :=by
      linear_combination hz'
    have h_Bt: ((bernoulli t :ℚ) : ℚ_[p]) = (t:ℚ_[p]) *
        (((bernoulli t :ℚ) / t:ℚ) : ℚ_[p]) :=by
      push_cast;field_simp
    rw [h_Bt,h_BtOverT]
    have hb': (((bernoulli (n+1) : ℚ) / (↑n+1) : ℚ) : ℚ_[p]) = (b:ℚ_[p]) :=by
      rw [show ((((bernoulli (n+1) : ℚ) / (↑n+1) : ℚ)) : ℚ_[p]) =
          (((bernoulli (n+1) : ℚ) / ↑(n+1) : ℚ) : ℚ_[p]) from by push_cast;ring_nf,hb]
    rw [hb']
    have ht_sub: (t:ℚ_[p]) = (p:ℚ_[p]) * (n:ℚ_[p]) + 1:=by
      simp only [ht_def];push_cast;ring
    push_cast;rw [ht_sub];ring
  obtain ⟨z₃,hz₃⟩ :=h_ingr3
  refine ⟨z₁+z₂+z₃,?_⟩
  have h_bridge:qf ((q7 p) ^ n) 1 -
      ((bernoulli t :ℚ) : ℚ_[p]) = (p:ℚ_[p]) * ((z₁:ℚ_[p]) + (z₂:ℚ_[p])) :=
    (mul_right_inj' hpQ_ne).mp <| by linear_combination hz₁+hz₂
  calc qf ((q7 p) ^ n) 1 -
        (((bernoulli (n+1) : ℚ) / (n+1) : ℚ) : ℚ_[p])
      = (qf ((q7 p) ^ n) 1 -
           ((bernoulli t :ℚ) : ℚ_[p])) +
        (((bernoulli t :ℚ) : ℚ_[p]) -
           (((bernoulli (n+1) : ℚ) / (n+1) : ℚ) : ℚ_[p])) :=by ring
    _= (p:ℚ_[p]) * ((z₁:ℚ_[p]) + (z₂:ℚ_[p])) +
        (p:ℚ_[p]) * (z₃:ℚ_[p]) :=by
          rw [h_bridge,hz₃]
    _= (p:ℚ_[p]) * ((z₁+z₂+z₃:ℤ_[p]) : ℚ_[p]) :=by push_cast;ring
theorem wB
    {p:ℕ} [Fact p.Prime] (hp_odd:p ≠ 2) :
    ∃ z :ℤ_[p],
      (2*p:ℚ_[p]) * (-(1/2:ℚ_[p])) *
          qf ((q7 p) ^ (p-2)) 1 =
        1+ (p:ℚ_[p]) * (z:ℚ_[p]) :=by
  obtain ⟨z₀,hz₀⟩ :=
    uj hp_odd
  have hpQ_ne: (p:ℚ_[p]) ≠ 0:=by exact_mod_cast (Fact.out:Nat.Prime p).ne_zero
  have htwo_ne: (2:ℚ_[p]) ≠ 0:=by norm_num
  refine ⟨-1-z₀,?_⟩
  rw [hz₀]
  push_cast;field_simp [hpQ_ne,htwo_ne];ring
end KummerCriterion
end
end Module40
-- Source: KummerCriterion.HMinus.PadicCorollaries
section Module41
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
variable (p:ℕ) [hp:Fact p.Prime] (hp_odd:p ≠ 2)
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
lemma w2 (hp_odd':p ≠ 2) :
    ∃ c :ℤ_[p],(c:ℚ_[p]) = -(1/2:ℚ_[p]) :=by
  have hp':Nat.Prime p :=hp.out
  have h2_not_dvd: ¬ p ∣ 2:=by
    intro h
    have hle:p ≤ 2:=Nat.le_of_dvd (by positivity) h
    exact hp_odd' (le_antisymm hle hp'.two_le)
  have h2_unit:IsUnit ((2:ℕ) : ℤ_[p]) :=by
    rw [PadicInt.isUnit_iff,PadicInt.norm_natCast_eq_one_iff]
    simpa [Nat.coprime_comm] using hp'.coprime_iff_not_dvd.mpr h2_not_dvd
  let c :ℤ_[p] := -((h2_unit.unit⁻¹: (ℤ_[p])ˣ).val)
  have hunit_mul:
      ((((h2_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) : ℚ_[p])) *
        (2:ℚ_[p]) = 1:=by
    have h2_spec: ((h2_unit.unit: (ℤ_[p])ˣ) : ℤ_[p]) = 2:=h2_unit.unit_spec
    have h2_specQ:
        ((((h2_unit.unit: (ℤ_[p])ˣ).val:ℤ_[p]) : ℚ_[p])) = (2:ℚ_[p]) :=
      congrArg (fun x :ℤ_[p] => (x:ℚ_[p])) h2_spec
    rw [← h2_specQ]
    change (((((h2_unit.unit⁻¹: (ℤ_[p])ˣ) * h2_unit.unit).val:ℤ_[p]) : ℚ_[p])) = 1
    simp
  have hhalf:
      ((((h2_unit.unit⁻¹: (ℤ_[p])ˣ).val:ℤ_[p]) : ℚ_[p])) = (1/2:ℚ_[p]) :=
    eq_one_div_of_mul_eq_one_left hunit_mul
  refine ⟨c,?_⟩
  simp [c,hhalf]
lemma yB
    {α:Type*} (s:Finset α) (f:α → ℚ_[p]) (g:α → ℤ_[p])
    (hfg: ∀ a ∈ s,∃ z:ℤ_[p],
      f a = (g a :ℚ_[p]) + (p:ℚ_[p]) * (z:ℚ_[p])) :
    ∃ z :ℤ_[p],
      (∏ a ∈ s,f a) =
        ((∏ a ∈ s,g a:ℤ_[p]) : ℚ_[p]) + (p:ℚ_[p]) * (z:ℚ_[p]) :=by
  classical
  induction s using Finset.induction_on with
  | empty=>
      refine ⟨0,by simp⟩
  | @insert a s ha ih=>
      obtain ⟨za,hza⟩ :=hfg a (by simp)
      have hs: ∀ b ∈ s,∃ z:ℤ_[p],
          f b = (g b :ℚ_[p]) + (p:ℚ_[p]) * (z:ℚ_[p]) :=
        fun b hb=> hfg b (by simp [hb])
      obtain ⟨zs,hzs⟩ :=ih hs
      let w :ℤ_[p] :=g a*zs+za* (∏ b ∈ s,g b) + (p:ℤ_[p]) * za*zs
      refine ⟨w,?_⟩
      calc
        (∏ b ∈ insert a s,f b) = f a * ∏ b ∈ s,f b:=by simp [ha]
        _= (((g a :ℤ_[p]) : ℚ_[p]) + (p:ℚ_[p]) * (za:ℚ_[p])) *
              ((((∏ b ∈ s,g b:ℤ_[p]) : ℚ_[p])) + (p:ℚ_[p]) * (zs:ℚ_[p])) :=by
                rw [hza,hzs]
        _= (((g a * ∏ b ∈ s,g b:ℤ_[p]) : ℚ_[p])) +
              (p:ℚ_[p]) * (w:ℚ_[p]) :=by
                simp [w]
                ring
        _= (((∏ b ∈ insert a s,g b:ℤ_[p]) : ℚ_[p])) +
              (p:ℚ_[p]) * (w:ℚ_[p]) :=by
                simp [ha]
theorem zy (hp_odd':p ≠ 2) :
    ∃ z :ℤ_[p],
      ((hMinus K :ℕ) : ℚ_[p]) =
        Finset.prod ((Finset.range (p-2)).filter fun j => Odd j) (fun j =>
          (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1) +
        (p:ℚ_[p]) * (z:ℚ_[p]) :=by
  have hp_gt:2 < p:=lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd')
  obtain ⟨c,hc⟩ :=w2 (p:=p) hp_odd'
  let S := (Finset.range (p-2)).filter fun j => Odd j
  have hfactor:
      ∀ j ∈ S,
        ∃ a :ℤ_[p],
          (a:ℚ_[p]) = (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1 :=by
    intro j hj
    have hj_lt:j < p-2:=Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj_odd:Odd j := (Finset.mem_filter.mp hj).2
    have hj_pos:0 < j:=by
      obtain ⟨k,hk⟩ :=hj_odd
      omega
    have hj_not_dvd: ¬ (p-1) ∣ (j+1) :=by
      refine Nat.not_dvd_of_pos_of_lt (by omega) ?_
      omega
    have hj_p_plus: ¬ (p:ℕ) ∣ (j+1) :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hj_p_plus_two: ¬ (p:ℕ) ∣ (j+2) :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨a₀,ha₀,_⟩ :=s8
      (p:=p) (hp:=hp) (n:=j+1) hp_odd' (by omega) (by omega)
      (KummerCriterion.rE
        (p:=p) (n:=j+1) (hp:=hp) hp_odd' (by omega))
    obtain ⟨z,hz⟩ :=sL
      (p:=p) hp_odd' hj_odd hj_pos hj_not_dvd hj_p_plus hj_p_plus_two
      (by omega:j+1 < p-1)
    have hz':qf ((q7 p) ^ j) 1 =
        ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p])) +
          (p:ℚ_[p]) * (z:ℚ_[p]) :=by
      rw [sub_eq_iff_eq_add] at hz
      simpa [add_comm] using hz
    refine ⟨a₀+ (p:ℤ_[p]) * (c*z),?_⟩
    rw [PadicInt.coe_add,PadicInt.coe_mul,PadicInt.coe_mul,ha₀,hc,hz']
    simp [mul_add,mul_comm,mul_left_comm,mul_assoc,add_comm]
  classical
  let a :ℕ → ℤ_[p] :=fun j => if hj:j ∈ S then Classical.choose (hfactor j hj) else 1
  let A :ℤ_[p] := ∏ j ∈ S,a j
  have hA_cast:
      (A:ℚ_[p]) =
        Finset.prod S (fun j =>
          (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1) :=by
    calc
      (A:ℚ_[p]) = ∏ j ∈ S,((a j :ℤ_[p]) : ℚ_[p]) :=by
        dsimp [A]
        change (algebraMap ℤ_[p] ℚ_[p]) (∏ j ∈ S,a j) =
          ∏ j ∈ S,(algebraMap ℤ_[p] ℚ_[p]) (a j)
        rw [map_prod]
      _=Finset.prod S (fun j =>
            (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1) :=by
          refine Finset.prod_congr rfl fun j hj=> ?_
          simpa [a,hj] using (Classical.choose_spec (hfactor j hj))
  have hp_sub_two_odd:Odd (p-2) :=by
    obtain ⟨k,hk⟩ :=hp.out.odd_of_ne_two hp_odd'
    refine ⟨k-1,?_⟩
    rw [hk]
    omega
  have hsplit: ((Finset.range (p-1)).filter fun j => Odd j) = insert (p-2) S :=by
    ext j
    rw [Finset.mem_filter,Finset.mem_range,Finset.mem_insert,
      show j ∈ S ↔ j < p -2 ∧ Odd j by
        dsimp [S]
        rw [Finset.mem_filter,Finset.mem_range]]
    constructor
    · intro h
      by_cases hj:j=p-2
      · exact Or.inl hj
      · exact Or.inr ⟨by omega,h.2⟩
    · intro h
      rcases h with rfl | h
      · exact ⟨by omega,hp_sub_two_odd⟩
      · exact ⟨by omega,h.2⟩
  obtain ⟨z₀,hz₀⟩ :=wB (p:=p) hp_odd'
  refine ⟨A*z₀,?_⟩
  calc
    ((hMinus K :ℕ) : ℚ_[p])
        = (2*p:ℚ_[p]) *
            Finset.prod ((Finset.range (p-1)).filter fun j => Odd j)
              (fun j => (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1) :=
          yc (p:=p) (K:=K) hp_odd'
    _= (Finset.prod S (fun j =>
            (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1)) *
          ((2*p:ℚ_[p]) * (-(1/2:ℚ_[p])) *
            qf ((q7 p) ^ (p-2)) 1) :=by
          rw [hsplit,Finset.prod_insert]
          · ring
          · simp [S]
    _= (A:ℚ_[p]) * (1+ (p:ℚ_[p]) * (z₀:ℚ_[p])) :=by rw [hA_cast,hz₀]
    _= (A:ℚ_[p]) + (p:ℚ_[p]) * ((A*z₀:ℤ_[p]) : ℚ_[p]) :=by
          push_cast
          ring
    _=Finset.prod S (fun j =>
          (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1) +
          (p:ℚ_[p]) * ((A*z₀:ℤ_[p]) : ℚ_[p]) :=by rw [hA_cast]
theorem zO (hp_odd':p ≠ 2) :
    ∃ z :ℤ_[p],
      ((hMinus K :ℕ) : ℚ_[p]) =
        Finset.prod ((Finset.range (p-2)).filter fun j => Odd j) (fun j =>
          (-(1/2:ℚ_[p])) *
            ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p]))) +
        (p:ℚ_[p]) * (z:ℚ_[p]) :=by
  obtain ⟨z₀,hz₀⟩ :=zy (p:=p) (K:=K) hp_odd'
  obtain ⟨c,hc⟩ :=w2 (p:=p) hp_odd'
  let S := (Finset.range (p-2)).filter fun j => Odd j
  have hfactor:
      ∀ j ∈ S,
        ∃ a :ℤ_[p],
          (a:ℚ_[p]) =
            (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p])) :=by
    intro j hj
    have hj_lt:j < p-2:=Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    obtain ⟨a,ha,_⟩ :=s8
      (p:=p) (hp:=hp) (n:=j+1) hp_odd' (by omega) (by omega)
      (KummerCriterion.rE
        (p:=p) (n:=j+1) (hp:=hp) hp_odd' (by omega))
    exact ⟨a,by simpa [Nat.cast_add,Nat.cast_one] using ha⟩
  classical
  let a :ℕ → ℤ_[p] :=fun j =>
    if hj:j ∈ S then Classical.choose (hfactor j hj) else 1
  have ha_cast:
      ∀ j ∈ S,
        ((a j :ℤ_[p]) : ℚ_[p]) =
          (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p])) :=by
    intro j hj
    simpa [a,hj] using (Classical.choose_spec (hfactor j hj))
  have hbridge:
      ∀ j ∈ S,
        ∃ z :ℤ_[p],
          (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1 =
            (a j :ℚ_[p]) + (p:ℚ_[p]) * (z:ℚ_[p]) :=by
    intro j hj
    have hp_gt:2 < p:=lt_of_le_of_ne hp.out.two_le (Ne.symm hp_odd')
    have hj_lt:j < p-2:=Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj_odd:Odd j := (Finset.mem_filter.mp hj).2
    have hj_pos:0 < j:=by
      obtain ⟨k,hk⟩ :=hj_odd
      omega
    have hj_not_dvd: ¬ (p-1) ∣ (j+1) :=by
      refine Nat.not_dvd_of_pos_of_lt (by omega) ?_
      omega
    have hj_p_plus: ¬ (p:ℕ) ∣ (j+1) :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have hj_p_plus_two: ¬ (p:ℕ) ∣ (j+2) :=
      Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    obtain ⟨z,hz⟩ :=sL
      (p:=p) hp_odd' hj_odd hj_pos hj_not_dvd hj_p_plus hj_p_plus_two
      (by omega:j+1 < p-1)
    have hz':qf ((q7 p) ^ j) 1 =
        ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p])) +
          (p:ℚ_[p]) * (z:ℚ_[p]) :=by
      rw [sub_eq_iff_eq_add] at hz
      simpa [add_comm] using hz
    refine ⟨c*z,?_⟩
    calc
      (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1
          = (c:ℚ_[p]) *
              (((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p])) +
                (p:ℚ_[p]) * (z:ℚ_[p])) :=by
                  rw [← hc,hz']
      _= (a j :ℚ_[p]) + (p:ℚ_[p]) * ((c*z:ℤ_[p]) : ℚ_[p]) :=by
            rw [ha_cast j hj,PadicInt.coe_mul,hc]
            ring
  obtain ⟨z₁,hz₁⟩ :=yB (p:=p) S
    (fun j => (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1) a hbridge
  have hA_cast:
      (((∏ j ∈ S,a j:ℤ_[p]) : ℤ_[p]) : ℚ_[p]) =
        Finset.prod S (fun j =>
          (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p]))) :=by
    change (algebraMap ℤ_[p] ℚ_[p]) (∏ j ∈ S,a j) = _
    rw [map_prod]
    exact Finset.prod_congr rfl ha_cast
  refine ⟨z₁+z₀,?_⟩
  calc
    ((hMinus K :ℕ) : ℚ_[p]) =
        Finset.prod S (fun j => (-(1/2:ℚ_[p])) * qf ((q7 p) ^ j) 1) +
          (p:ℚ_[p]) * (z₀:ℚ_[p]) :=hz₀
    _= (((∏ j ∈ S,a j:ℤ_[p]) : ℤ_[p]) : ℚ_[p]) +
          (p:ℚ_[p]) * (z₁:ℚ_[p]) + (p:ℚ_[p]) * (z₀:ℚ_[p]) :=by
            rw [hz₁]
    _=Finset.prod S (fun j =>
          (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p]))) +
          (p:ℚ_[p]) * ((z₁+z₀:ℤ_[p]) : ℚ_[p]) :=by
            rw [hA_cast]
            push_cast
            ring
end KummerCriterion
end
end Module41
-- Source: KummerCriterion.HMinus.HMinusCriterion
section Module42
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
variable (p:ℕ) [hp:Fact p.Prime] (hp_odd:p ≠ 2)
  (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
lemma va (hp_odd:p ≠ 2) (Q:ℕ → Prop) :
    (∃ j,j ∈ (Finset.range (p-2)).filter (fun j => Odd j) ∧ Q (j+1)) ↔
      ∃ k,1 ≤ k ∧ 2*k ≤ p-3 ∧ Q (2*k) :=by
  constructor
  · rintro ⟨j,hj,hQ⟩
    have hj_lt:j < p-2:=Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hj_odd:Odd j := (Finset.mem_filter.mp hj).2
    have hp_mod:p%2=1:=Nat.odd_iff.mp (hp.out.odd_of_ne_two hp_odd)
    let k :=j/2+1
    have hj_mod:j%2=1:=Nat.odd_iff.mp hj_odd
    have hk_even:2*k=j+1:=by
      dsimp [k]
      have htwo:=Nat.two_mul_odd_div_two hj_mod
      omega
    refine ⟨k,by omega,by
      rw [hk_even]
      omega,?_⟩
    simpa [hk_even] using hQ
  · rintro ⟨k,hk_one,hk_range,hQ⟩
    refine ⟨2*k-1,?_,?_⟩
    · refine Finset.mem_filter.mpr ⟨?_,?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · rw [Nat.odd_iff]
        omega
    · have hsucc: (2*k-1) + 1=2*k:=by omega
      simpa [hsucc] using hQ
theorem xt (hp_odd':p ≠ 2) :
    (p:ℕ) ∣ hMinus K ↔
      ∃ k,1 ≤ k ∧ 2*k ≤ p-3 ∧ (p:ℤ) ∣ (bernoulli (2*k)).num:=by
  obtain ⟨z,hz⟩ :=KummerCriterion.zO
    (p:=p) (K:=K) hp_odd'
  let S := (Finset.range (p-2)).filter (fun j => Odd j)
  have hfactor:
      ∀ j ∈ S,
        ∃ a :ℤ_[p],
          (a:ℚ_[p]) =
            (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p])) ∧
          (IsUnit a ↔ ¬ (p:ℤ) ∣ (bernoulli (j+1)).num) :=by
    intro j hj
    have hj_lt:j < p-2:=Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    simpa [Nat.cast_add,Nat.cast_one] using
      (s8 (p:=p) (hp:=hp) (n:=j+1) hp_odd'
        (by omega) (by omega)
        (KummerCriterion.rE
          (p:=p) (n:=j+1) (hp:=hp) hp_odd' (by omega)))
  classical
  let a :ℕ → ℤ_[p] :=fun j =>
    if hj:j ∈ S then Classical.choose (hfactor j hj) else 1
  let A :ℤ_[p] := ∏ j ∈ S,a j
  have ha_cast:
      ∀ j ∈ S,
        ((a j :ℤ_[p]) : ℚ_[p]) =
          (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p])) :=by
    intro j hj
    simpa [a,hj,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using
      (Classical.choose_spec (hfactor j hj)).1
  have ha_unit:
      ∀ j ∈ S,IsUnit (a j) ↔ ¬ (p:ℤ) ∣ (bernoulli (j+1)).num:=by
    intro j hj
    simpa [a,hj] using (Classical.choose_spec (hfactor j hj)).2
  have hA_cast:
      ((A:ℤ_[p]) : ℚ_[p]) =
        Finset.prod S (fun j =>
          (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p]))) :=by
    calc
      ((A:ℤ_[p]) : ℚ_[p]) = ∏ j ∈ S,(((a j :ℤ_[p]) : ℚ_[p])) :=by
        dsimp [A]
        change (algebraMap ℤ_[p] ℚ_[p]) (∏ j ∈ S,a j) =
          ∏ j ∈ S,(algebraMap ℤ_[p] ℚ_[p]) (a j)
        rw [map_prod]
      _=Finset.prod S (fun j =>
            (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p]))) :=
          Finset.prod_congr rfl ha_cast
  have hzA:
      (((hMinus K :ℕ) : ℚ_[p])) =
        ((A:ℤ_[p]) : ℚ_[p]) + (p:ℚ_[p]) * (z:ℚ_[p]) :=by
    calc
      (((hMinus K :ℕ) : ℚ_[p])) =
          Finset.prod S (fun j =>
            (-(1/2:ℚ_[p])) * ((((bernoulli (j+1) : ℚ) / (j+1) : ℚ) : ℚ_[p]))) +
            (p:ℚ_[p]) * (z:ℚ_[p]) :=hz
      _= ((A:ℤ_[p]) : ℚ_[p]) + (p:ℚ_[p]) * (z:ℚ_[p]) :=by rw [hA_cast]
  have hpz_lt: ‖(p:ℚ_[p]) * (z:ℚ_[p])‖ < 1:=by
    have hp_lt: ‖(p:ℚ_[p])‖ < 1:=by
      simpa using (Padic.norm_natCast_lt_one_iff (p:=p) (n:=p)).2 (dvd_rfl)
    calc
      ‖(p:ℚ_[p]) * (z:ℚ_[p])‖ = ‖(z:ℚ_[p])‖ * ‖(p:ℚ_[p])‖ :=by
        rw [norm_mul,mul_comm]
      _ < 1:=mul_lt_one_of_nonneg_of_lt_one_right z.2 (norm_nonneg _) hp_lt
  have hA_lt_iff:
      ‖A‖ < 1 ↔
        ∃ j,j ∈ S ∧ (p:ℤ) ∣ (bernoulli (j+1)).num:=by
    have hA_units:IsUnit A ↔ ∀ j ∈ S,IsUnit (a j) :=IsUnit.prod_iff (s:=S) (f:=a)
    constructor
    · intro hA_lt
      have hA_nonunit: ¬ IsUnit A := (PadicInt.not_isUnit_iff (z:=A)).2 hA_lt
      rw [hA_units] at hA_nonunit
      rcases not_forall.mp hA_nonunit with ⟨j,hj_bad_imp⟩
      obtain ⟨hjS,hj_bad⟩ :=Classical.not_imp.mp hj_bad_imp
      exact ⟨j,hjS,Classical.not_not.mp ((not_congr (ha_unit j hjS)).mp hj_bad)⟩
    · rintro ⟨j,hjS,hj_bad⟩
      refine (PadicInt.not_isUnit_iff (z:=A)).1 ?_
      rw [hA_units]
      exact fun hUnits=> (ha_unit j hjS).mp (hUnits j hjS) hj_bad
  constructor
  · intro hhMinus
    have hhMinus_lt: ‖(((hMinus K :ℕ) : ℚ_[p]))‖ < 1:=by
      simpa using (Padic.norm_natCast_lt_one_iff (p:=p) (n:=hMinus K)).2 hhMinus
    have hA_lt: ‖((A:ℤ_[p]) : ℚ_[p])‖ < 1:=by
      by_cases hA_lt: ‖((A:ℤ_[p]) : ℚ_[p])‖ < 1
      · exact hA_lt
      have hA_eq: ‖((A:ℤ_[p]) : ℚ_[p])‖ = 1:=le_antisymm A.2 (le_of_not_gt hA_lt)
      have hpz_eq: ‖(p:ℚ_[p]) * (z:ℚ_[p])‖ = ‖((A:ℤ_[p]) : ℚ_[p])‖ :=
        Padic.norm_eq_of_norm_add_lt_right
          (z1:= (p:ℚ_[p]) * (z:ℚ_[p]))
          (z2:= ((A:ℤ_[p]) : ℚ_[p])) <| by
            simpa [hzA,add_comm,hA_eq] using hhMinus_lt
      have hpz_one: ‖(p:ℚ_[p]) * (z:ℚ_[p])‖ = 1:=hpz_eq.trans hA_eq
      exact absurd (hpz_one ▸ hpz_lt) (lt_irrefl _)
    exact (va (p:=p) hp_odd'
      (Q:=fun n => (p:ℤ) ∣ (bernoulli n).num)).1 ((hA_lt_iff).1 <| by
        simpa [PadicInt.padic_norm_e_of_padicInt] using hA_lt)
  · rintro hbad
    have hA_lt: ‖((A:ℤ_[p]) : ℚ_[p])‖ < 1:=by
      simpa [PadicInt.padic_norm_e_of_padicInt] using
        (hA_lt_iff).2 <| (va (p:=p)
          hp_odd'
          (Q:=fun n => (p:ℤ) ∣ (bernoulli n).num)).2 hbad
    have hhMinus_lt: ‖(((hMinus K :ℕ) : ℚ_[p]))‖ < 1:=by
      have hle:
          ‖(((hMinus K :ℕ) : ℚ_[p]))‖ ≤
            max ‖((A:ℤ_[p]) : ℚ_[p])‖ ‖(p:ℚ_[p]) * (z:ℚ_[p])‖ :=by
        simpa [hzA] using
          (Padic.nonarchimedean (((A:ℤ_[p]) : ℚ_[p])) ((p:ℚ_[p]) * (z:ℚ_[p])))
      exact lt_of_le_of_lt hle (max_lt hA_lt hpz_lt)
    simpa using (Padic.norm_natCast_lt_one_iff (p:=p) (n:=hMinus K)).1 hhMinus_lt
end KummerCriterion
end
end Module42
open NumberField
open scoped NumberField

namespace OMAKummerR2H3

lemma classNumber_one_of_finrank_one (F : Type*) [Field F] [NumberField F]
    (h : Module.finrank ℚ F = 1) : classNumber F = 1 := by
  let e : ℚ ≃+* F := RingEquiv.ofBijective (algebraMap ℚ F)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h)
  let e' : (𝓞 ℚ) ≃+* (𝓞 F) := RingOfIntegers.mapRingEquiv e
  exact classNumber_eq_one_iff.mpr <| IsPrincipalIdealRing.of_surjective
    (e'.toRingHom.comp Rat.ringOfIntegersEquiv.symm.toRingHom)
    (e'.surjective.comp Rat.ringOfIntegersEquiv.symm.surjective)

lemma classNumbers_two : classNumber (CyclotomicField 2 ℚ) = 1 ∧
    classNumber (maximalRealSubfield (CyclotomicField 2 ℚ)) = 1 := by
  let K := CyclotomicField 2 ℚ
  let : IsCyclotomicExtension {2} ℚ K := CyclotomicField.isCyclotomicExtension 2 ℚ
  have hK : Module.finrank ℚ K = 1 := by
    rw [IsCyclotomicExtension.finrank (n := 2) K
      (Polynomial.cyclotomic.irreducible_rat two_pos)]
    rfl
  have hL : Module.finrank ℚ (maximalRealSubfield K) = 1 := by
    have hle : Module.finrank ℚ (maximalRealSubfield K) ≤ Module.finrank ℚ K :=
      LinearMap.finrank_le_finrank_of_injective
        (f := (maximalRealSubfield K).subtype.toRatAlgHom.toLinearMap)
        Subtype.val_injective
    have hpos : 0 < Module.finrank ℚ (maximalRealSubfield K) := Module.finrank_pos
    omega
  exact ⟨classNumber_one_of_finrank_one K hK, classNumber_one_of_finrank_one _ hL⟩

end OMAKummerR2H3

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R2.H3 := by
  intro p hp
  by_cases hp2 : p = 2
  · subst p
    obtain ⟨hK, hL⟩ := OMAKummerR2H3.classNumbers_two
    change 2 ∣ classNumber (CyclotomicField 2 ℚ) /
      classNumber (maximalRealSubfield (CyclotomicField 2 ℚ)) ↔ _
    norm_num [hK, hL]
  · let K := CyclotomicField p ℚ
    have : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
    have : IsCMField K := KummerCriterion.r0 p hp2 K
    change p ∣ KummerCriterion.hMinus K ↔ _
    rw [KummerCriterion.xt (p := p) (K := K) hp2]
    constructor
    · rintro ⟨j, hj, hbound, hdiv⟩
      refine ⟨2 * j, Finset.mem_Icc.mpr ⟨by omega, hbound⟩, even_two_mul j, ?_⟩
      simpa only [bernoulli_eq_bernoulli'_of_ne_one (n := 2 * j) (by omega)] using hdiv
    · rintro ⟨k, hk, heven, hdiv⟩
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
      obtain ⟨j, hj⟩ := heven
      have hkj : k = 2 * j := by omega
      refine ⟨j, by omega, by omega, ?_⟩
      simpa only [← hkj, bernoulli_eq_bernoulli'_of_ne_one (n := k) (by omega)] using hdiv

