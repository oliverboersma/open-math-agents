/-
Copyright (c) 2026 Hanan Beer and the contributors credited below.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanan Beer, Riccardo Brasca, and the credited KummerCriterion contributors
-/
import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1
import Mathlib
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Real and relative class-number factorization

Exact-target integration: Hanan Beer (@hananzlt).
The mathematical formalization is reused from Riccardo Brasca (@riccardobrasca)
and the KummerCriterion contributors, and from the flt-regular contributors.
The reused source history includes Ruben Van de Velde, Chris Birkbeck,
Andrew Yang, and Kim Morrison. Original work remains under Apache 2.0.

KummerCriterion: https://github.com/riccardobrasca/KummerCriterion/tree/470de714f3de5a1ec8c0f6209502c1c5272c2c43
flt-regular: https://github.com/leanprover-community/flt-regular/tree/bd81b78ba6e9f1c57215ff096e9e8f45d5d4b54b
The six dependency modules below are reused from the checked integration in
Hanan Beer campaign PR6541; their original helper names are retained.
Reduction: Hanan Beer, PR7356, following @Noctluxis's R3.
This establishes only the class-number factorization input H3.
-/

-- Source: KummerCriterion.PrimitiveRootUnits
section Module0
noncomputable section
open NumberField
open scoped NumberField
namespace IsPrimitiveRoot
noncomputable def unit' {K : Type*} [Field K] [CharZero K] {ζ : K} {k : ℕ}
    [NeZero k] (hζ : IsPrimitiveRoot ζ k) : (𝓞 K)ˣ :=
  (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne k)).unit
lemma unit'_coe {K : Type*} [Field K] [CharZero K] {ζ : K} {k : ℕ}
    [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot (hζ.unit' : 𝓞 K) k :=
  hζ.toInteger_isPrimitiveRoot
lemma unit'_pow {K : Type*} [Field K] [CharZero K] {ζ : K} {k : ℕ}
    [NeZero k] (hζ : IsPrimitiveRoot ζ k) : hζ.unit' ^ k = 1 :=
  Units.ext hζ.toInteger_isPrimitiveRoot.pow_eq_one
lemma eq_one_mod_sub_of_pow {A : Type*} [CommRing A] [IsDomain A] {ζ μ : A} {k : ℕ}
    [NeZero k] (hζ : IsPrimitiveRoot ζ k) (hμ : μ ^ k = 1) :
    algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A)) μ = 1 := by
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [← hi, map_pow]
  have hζ_mod : algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A)) ζ = 1 := by
    rw [← map_one (algebraMap A (A ⧸ Ideal.span ({ζ - 1} : Set A))), ← sub_eq_zero,
      ← map_sub, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [hζ_mod, one_pow]
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
variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem zeta_toInteger_pow_eq_one :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
  (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
theorem zeta_toInteger_pow_pred_mul :
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) *
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) = 1 := by
  rw [← pow_succ, Nat.sub_one_add_one hp.1.ne_zero]
  exact zeta_toInteger_pow_eq_one p K
noncomputable def zetaPrime : Ideal (𝓞 K) :=
  Ideal.span {((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)}
instance zetaPrime_isPrime : (zetaPrime p K).IsPrime :=
  (Ideal.span_singleton_prime
    (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero).mpr
    (zeta_spec p ℚ K).zeta_sub_one_prime'
theorem zetaPrime_ne_bot : zetaPrime p K ≠ ⊥ := by
  rw [zetaPrime, Ne, Ideal.span_singleton_eq_bot]
  exact (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero
noncomputable def zetaPrimePlus [IsCMField K] : Ideal (𝓞 ((NumberField.maximalRealSubfield K))) :=
  (zetaPrime p K).under (𝓞 ((NumberField.maximalRealSubfield K)))
instance [IsCMField K] : (zetaPrimePlus p K).IsPrime :=
  Ideal.IsPrime.under _ _
instance [IsCMField K] : (zetaPrime p K).LiesOver (zetaPrimePlus p K) :=
  Ideal.over_under _
lemma complexConj_apply_zeta [IsCMField K] :
    (ringOfIntegersComplexConj K (zeta_spec p ℚ K).toInteger : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hzeta_torsion : hζ.unit' ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).2
      (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.1.pos, hζ.unit'_pow⟩)
  have hconj := unitsComplexConj_torsion (K := K) ⟨hζ.unit', hzeta_torsion⟩
  have h1 : (unitsComplexConj K hζ.unit' : 𝓞 K) = (hζ.unit'⁻¹ : (𝓞 K)ˣ) :=
    congrArg ((↑·) : (𝓞 K)ˣ → 𝓞 K) hconj
  have h2 : (hζ.unit'⁻¹ : (𝓞 K)ˣ) = hζ.unit' ^ (p - 1) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_one_add_one hp.1.ne_zero]
    ext; push_cast; exact hζ.pow_eq_one
  rw [show (ringOfIntegersComplexConj K hζ.toInteger : 𝓞 K) =
    (unitsComplexConj K hζ.unit' : 𝓞 K) from rfl, h1, h2, Units.val_pow_eq_pow_val]
  rfl
theorem complexConj_sub_mem_zetaPrime [IsCMField K] (x : 𝓞 K) :
    (ringOfIntegersComplexConj K x : 𝓞 K) - x ∈ zetaPrime p K := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have htop : Algebra.adjoin ℤ {hζ.toInteger} = ⊤ :=
    IsCyclotomicExtension.Rat.adjoin_singleton_eq_top hζ
  have hx : x ∈ Algebra.adjoin ℤ ({hζ.toInteger} : Set (𝓞 K)) := htop ▸ trivial
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    simp only [Set.mem_singleton_iff] at hy
    subst hy
    have hp_pow : hζ.toInteger ^ p = 1 := zeta_toInteger_pow_eq_one p K
    have hc_pow : (ringOfIntegersComplexConj K hζ.toInteger) ^ p = 1 := by
      rw [← map_pow, hp_pow, map_one]
    have hmem_of_pow : ∀ μ : 𝓞 K, μ ^ p = 1 → μ - 1 ∈ zetaPrime p K := by
      intro μ hμ
      have h1 := hζ.unit'_coe.eq_one_mod_sub_of_pow hμ
      have h2 : (algebraMap (𝓞 K)
          (𝓞 K ⧸ Ideal.span ({(hζ.unit' : 𝓞 K) - 1} : Set (𝓞 K)))) (μ - 1) = 0 := by
        rw [map_sub, h1, map_one, sub_self]
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    have h1 : (hζ.toInteger : 𝓞 K) - 1 ∈ zetaPrime p K := hmem_of_pow _ hp_pow
    have h2 : (ringOfIntegersComplexConj K hζ.toInteger : 𝓞 K) - 1 ∈ zetaPrime p K :=
      hmem_of_pow _ hc_pow
    have : (ringOfIntegersComplexConj K hζ.toInteger : 𝓞 K) - hζ.toInteger =
        ((ringOfIntegersComplexConj K hζ.toInteger : 𝓞 K) - 1) -
          (hζ.toInteger - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ h2 h1
  | algebraMap r =>
    have : ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) r) =
        (algebraMap ℤ (𝓞 K)) r := by
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K), AlgEquiv.commutes]
    rw [this, sub_self]
    exact Ideal.zero_mem _
  | add x y _ _ hpx hpy =>
    have : (ringOfIntegersComplexConj K (x + y) : 𝓞 K) - (x + y) =
        ((ringOfIntegersComplexConj K x : 𝓞 K) - x) +
          ((ringOfIntegersComplexConj K y : 𝓞 K) - y) := by
      push_cast [map_add]; ring
    rw [this]
    exact Ideal.add_mem _ hpx hpy
  | mul x y _ _ hpx hpy =>
    have : (ringOfIntegersComplexConj K (x * y) : 𝓞 K) - (x * y) =
        ((ringOfIntegersComplexConj K x : 𝓞 K) - x) *
            (ringOfIntegersComplexConj K y : 𝓞 K) +
          x * ((ringOfIntegersComplexConj K y : 𝓞 K) - y) := by
      push_cast [map_mul]; ring
    rw [this]
    exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ hpx)
      (Ideal.mul_mem_left _ _ hpy)
lemma pi_mul_complexConj_pi_eq [IsCMField K] :
    ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K) *
      ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1) =
      -((zeta_spec p ℚ K).toInteger ^ (p - 1)) *
        ((zeta_spec p ℚ K).toInteger - 1) ^ 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hc_pi : (ringOfIntegersComplexConj K (hζ.toInteger - 1) : 𝓞 K) =
      hζ.toInteger ^ (p - 1) - 1 := by
    rw [map_sub, map_one, complexConj_apply_zeta]
  have hpow_succ : hζ.toInteger ^ (p - 1) * hζ.toInteger = 1 :=
    zeta_toInteger_pow_pred_mul p K
  rw [hc_pi]
  linear_combination (hζ.toInteger - 1) * hpow_succ
lemma complexConj_pi_mul_complexConj_pi [IsCMField K] :
    ringOfIntegersComplexConj K
        (((zeta_spec p ℚ K).toInteger - 1) *
          ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1)) =
      ((zeta_spec p ℚ K).toInteger - 1) *
        ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1) := by
  rw [map_mul, mul_comm]
  congr 1
  ext
  exact complexConj_apply_apply K _
noncomputable def piPlus [IsCMField K] : 𝓞 ((NumberField.maximalRealSubfield K)) := by
  have hfix := complexConj_pi_mul_complexConj_pi p K
  rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj,
    RingOfIntegers.complexConj_eq_self_iff] at hfix
  exact hfix.choose
lemma algebraMap_piPlus [IsCMField K] :
    (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) (piPlus p K) =
      ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K) *
        ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1) := by
  have hfix := complexConj_pi_mul_complexConj_pi p K
  rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj,
    RingOfIntegers.complexConj_eq_self_iff] at hfix
  ext
  rw [← hfix.choose_spec]; rfl
theorem map_span_piPlus_eq_zetaPrime_sq [IsCMField K] :
    (Ideal.span {piPlus p K}).map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) =
      zetaPrime p K ^ 2 := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hζ_unit : IsUnit ((hζ.unit' : 𝓞 K) ^ (p - 1)) := (hζ.unit'.isUnit.pow _)
  have hneg_unit : IsUnit (-(hζ.toInteger : 𝓞 K) ^ (p - 1)) := by
    rw [show (hζ.toInteger : 𝓞 K) = (hζ.unit' : 𝓞 K) from rfl]
    exact hζ_unit.neg
  rw [Ideal.map_span, Set.image_singleton, algebraMap_piPlus,
    pi_mul_complexConj_pi_eq, zetaPrime, Ideal.span_singleton_pow,
    show -(hζ.toInteger : 𝓞 K) ^ (p - 1) * ((hζ.toInteger - 1) ^ 2) =
        ((hζ.toInteger - 1) ^ 2) * -(hζ.toInteger) ^ (p - 1) from by ring,
    Ideal.span_singleton_mul_right_unit hneg_unit]
include hp_odd in
theorem multiplicity_zetaPrime_algebraMap_even [IsCMField K]
    (x : 𝓞 ((NumberField.maximalRealSubfield K))) (hx : x ≠ 0) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)
                      (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) x)) := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  set α := algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) x with hα_def
  have hα : α ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hx
  have hπ_prime : Prime (hζ.toInteger - 1 : 𝓞 K) := hζ.zeta_sub_one_prime'
  have hfin : FiniteMultiplicity (hζ.toInteger - 1 : 𝓞 K) α :=
    FiniteMultiplicity.of_prime_left hπ_prime hα
  obtain ⟨u, hαu, hπ_nd_u⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  set e := multiplicity (hζ.toInteger - 1 : 𝓞 K) α with he_def
  have hcα : ringOfIntegersComplexConj K α = α :=
    (ringOfIntegersComplexConj K).commutes x
  have hc_pi : ringOfIntegersComplexConj K (hζ.toInteger - 1) =
      -hζ.toInteger ^ (p - 1) * (hζ.toInteger - 1) := by
    rw [map_sub, map_one, complexConj_apply_zeta]
    linear_combination zeta_toInteger_pow_pred_mul p K
  have hcα_expand : (-hζ.toInteger ^ (p - 1) * (hζ.toInteger - 1) : 𝓞 K) ^ e *
      ringOfIntegersComplexConj K u = (hζ.toInteger - 1) ^ e * u := by
    have := hcα
    rw [hαu, map_mul, map_pow, hc_pi] at this
    exact this
  have hπ_ne : (hζ.toInteger - 1 : 𝓞 K) ≠ 0 := hπ_prime.ne_zero
  have hcu_eq : ((-hζ.toInteger ^ (p - 1)) ^ e : 𝓞 K) * ringOfIntegersComplexConj K u = u := by
    have hreord : ((hζ.toInteger - 1) ^ e : 𝓞 K) *
        (((-hζ.toInteger ^ (p - 1)) ^ e) * ringOfIntegersComplexConj K u) =
        ((hζ.toInteger - 1) ^ e : 𝓞 K) * u := by
      have hsplit : ((-hζ.toInteger ^ (p - 1) * (hζ.toInteger - 1)) ^ e : 𝓞 K) =
          ((hζ.toInteger - 1) ^ e) * (((-hζ.toInteger ^ (p - 1)) ^ e)) := by
        rw [mul_pow]; ring
      rw [← hcα_expand, hsplit, mul_assoc]
    exact mul_left_cancel₀ (pow_ne_zero _ hπ_ne) hreord
  have hres : (ringOfIntegersComplexConj K u : 𝓞 K) - u ∈ zetaPrime p K :=
    complexConj_sub_mem_zetaPrime p K u
  have hpow_sub : ∀ n : ℕ, (hζ.toInteger ^ n - 1 : 𝓞 K) ∈ zetaPrime p K := by
    intro n
    rw [zetaPrime, Ideal.mem_span_singleton]
    have := sub_dvd_pow_sub_pow hζ.toInteger (1 : 𝓞 K) n
    rwa [one_pow] at this
  have hneg_pow_sub : ((-hζ.toInteger ^ (p - 1)) ^ e - (-1) ^ e : 𝓞 K) ∈ zetaPrime p K := by
    have key : ((-hζ.toInteger ^ (p - 1)) ^ e - (-1) ^ e : 𝓞 K) =
        (-1) ^ e * (hζ.toInteger ^ ((p - 1) * e) - 1) := by
      rw [neg_pow, ← pow_mul]; ring
    rw [key]
    exact Ideal.mul_mem_left _ _ (hpow_sub _)
  have hkey : ((1 - (-1) ^ e) * u : 𝓞 K) ∈ zetaPrime p K := by
    have h1 : ((-hζ.toInteger ^ (p - 1)) ^ e : 𝓞 K) * ringOfIntegersComplexConj K u -
        (-1) ^ e * u ∈ zetaPrime p K := by
      have h1a : ((-hζ.toInteger ^ (p - 1)) ^ e : 𝓞 K) * ringOfIntegersComplexConj K u -
          (-1) ^ e * u =
          (((-hζ.toInteger ^ (p - 1)) ^ e - (-1) ^ e) * ringOfIntegersComplexConj K u) +
          ((-1) ^ e) * (ringOfIntegersComplexConj K u - u) := by ring
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
    have hp2 : 2 < p := lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
    have h_two_u : (2 * u : 𝓞 K) ∈ zetaPrime p K := by
      convert hkey using 2
      rw [Odd.neg_one_pow he]; ring
    have h_prime := zetaPrime_isPrime p K
    rcases h_prime.mem_or_mem h_two_u with h | h
    · exact IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' p (zeta_spec p ℚ K) hp2 h
    · rw [zetaPrime, Ideal.mem_span_singleton] at h
      exact hπ_nd_u h
include hp_odd in
theorem zetaPrimePlus_map_eq [IsCMField K] :
    (zetaPrimePlus p K).map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) = (zetaPrime p K) ^ 2 := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [zetaPrimePlus] at hy
    rw [Ideal.mem_comap, zetaPrime, Ideal.mem_span_singleton] at hy
    by_cases hy0 : y = 0
    · simp [hy0]
    have heven := multiplicity_zetaPrime_algebraMap_even p hp_odd K y hy0
    have hfin : FiniteMultiplicity
        ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)
        (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) y) :=
      FiniteMultiplicity.of_prime_left (zeta_spec p ℚ K).zeta_sub_one_prime'
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hy0)
    have hge : 1 ≤ multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)
        (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) y) :=
      hfin.pow_dvd_iff_le_multiplicity.mp (by rwa [pow_one])
    have h2le : 2 ≤ multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)
        (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) y) := by
      rcases heven with ⟨k, hk⟩
      omega
    rw [Ideal.mem_comap, show (zetaPrime p K) ^ 2 =
        Ideal.span {((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K) ^ 2} from
      by rw [zetaPrime, Ideal.span_singleton_pow], Ideal.mem_span_singleton]
    exact hfin.pow_dvd_iff_le_multiplicity.mpr h2le
  · rw [← map_span_piPlus_eq_zetaPrime_sq p K]
    refine Ideal.map_mono ?_
    rw [Ideal.span_singleton_le_iff_mem]
    rw [zetaPrimePlus, Ideal.mem_comap, zetaPrime, algebraMap_piPlus,
      Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
end CyclotomicSetup
end KummerCriterion
end
end Module2

-- Source: FltRegular.NumberTheory.Cyclotomic.UnitLemmas
section Module3
variable {p : ℕ} [NeZero p] {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)
open scoped nonZeroDivisors NumberField
open IsCyclotomicExtension NumberField Polynomial IsCMField
noncomputable section
theorem eq_one_mod_one_sub {A : Type*} [CommRing A] {t : A} :
    algebraMap A (A ⧸ Ideal.span ({t - 1} : Set A)) t = 1 := by
  rw [← map_one <| algebraMap A <| A ⧸ Ideal.span ({t - 1} : Set A), ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)
theorem aux {t} {l : 𝓞 K} {f : Fin t → ℤ} {μ : K} (hμ : IsPrimitiveRoot μ p)
    (h : ∑ x : Fin t, f x • hμ.toInteger ^ (x : ℕ) = l) :
    algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) l = ∑ x : Fin t, (f x : 𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) := by
  rw [← h, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_zsmul]
  have : hμ.toInteger ^ p = 1 := by
    ext
    push_cast
    exact hμ.pow_eq_one
  obtain ⟨k, -, hk⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one this
  have : algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) hμ.toInteger = 1 := by
    rw [← hk, map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K)) ^ k = 1
    rw [eq_one_mod_one_sub, one_pow]
  simp only [map_pow (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))))), this, one_pow, zsmul_one]
variable [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem roots_of_unity_in_cyclo (hpo : Odd p) (x : K)
    (h : ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1) :
    ∃ (m k : ℕ), x = (-1) ^ k * (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit).1 : K) ^ m := by
  obtain ⟨n, hn, hxn⟩ := h
  have hη : (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit).1 : K) = ζ := by rw [IsUnit.unit_spec]; rfl
  simp only [hη]
  obtain ⟨r, -, hr | hr⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder hpo
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hxn⟩)
  · exact ⟨r, 2, by simp [hr]⟩
  · exact ⟨r, 1, by simp [hr]⟩
lemma unit_inv_conj_not_neg_zeta_runity_aux (u : (𝓞 K)ˣ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (unitsMulComplexConjInv K u).1 = 1 := by
  have := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have := Units.coe_map_inv (N := 𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))))) (unitsComplexConj K u)
  rw [unitsMulComplexConjInv_apply, Units.val_mul, map_mul, ← MonoidHom.coe_coe, ← this,
    Units.mul_inv_eq_one, Units.coe_map, MonoidHom.coe_coe]
  have := Fact.mk hp
  have hu := hζ.integralPowerBasis.basis.sum_repr u
  let a := hζ.integralPowerBasis.basis.repr
  let φn := hζ.integralPowerBasis.dim
  simp_rw [PowerBasis.basis_eq_pow, IsPrimitiveRoot.integralPowerBasis_gen] at hu
  have hu' := congr_arg (ringOfIntegersComplexConj K) hu
  replace hu' : ∑ x : Fin φn, (a u) x • (ringOfIntegersComplexConj K)
      (hζ.toInteger ^ (x : ℕ)) = unitsComplexConj K u := by
    refine Eq.trans ?_ hu'
    rw [map_sum]
    congr 1
    ext x
    congr 1
    rw [map_zsmul]
  have : ∀ x : Fin φn, ringOfIntegersComplexConj K (hζ.toInteger ^ (x : ℕ)) =
      hζ.inv.toInteger ^ (x : ℕ) := by
    intro x
    ext
    simp only [map_pow, coe_ringOfIntegersComplexConj]
    suffices ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ∈ Units.torsion K by
      have H := RingOfIntegers.ext_iff.1 <|
        Units.ext_iff.1 <| unitsComplexConj_torsion K ⟨((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit), ‹_›⟩
      have : ↑↑((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) = ζ := rfl
      simp only [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingOfIntegers.mapRingEquiv_apply,
        this, AlgEquiv.coe_ringEquiv, InvMemClass.coe_inv, map_units_inv] at H
      change (complexConj K) ζ ^ (x : ℕ) = ζ⁻¹ ^ (x : ℕ)
      rw [H]
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, by lia, ?_⟩)
    ext
    exact hζ.pow_eq_one
  conv_lhs at hu' =>
    congr
    congr
    ext a
    rw [this a]
  exact (aux hζ hζ hu).trans (aux hζ hζ.inv hu').symm
theorem unit_inv_conj_not_neg_zeta_runity (u : (𝓞 K)ˣ) (n : ℕ) [Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    u * (unitsComplexConj K u)⁻¹ ≠ -((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ^ n := by
  by_contra H
  have hμ : algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) = 1 := by
    have hpow : ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) ^ p = 1 := by
      change (hζ.toInteger ^ n) ^ p = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    obtain ⟨k, -, hk⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hpow
    rw [← hk, map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K)) ^ k = 1
    rw [eq_one_mod_one_sub, one_pow]
  have hμ' : algebraMap (𝓞 K) (𝓞 K ⧸ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K)))) ((((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) : 𝓞 K) ^ n) = -1 := by
    rw [← neg_eq_iff_eq_neg, ← map_neg, ← Units.val_pow_eq_pow_val, ← Units.val_neg, ← H]
    apply unit_inv_conj_not_neg_zeta_runity_aux hζ u hp
  have := Fact.mk hp
  apply (IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' _ hζ hp : (2 : 𝓞 K) ∉ ((Ideal.span ({(((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat, ← one_add_one_eq_two, ← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ
theorem unit_inv_conj_is_root_of_unity (u : (𝓞 K)ˣ) [H : Fact (p.Prime)] (hp : 2 < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ = (((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit) ^ m) ^ 2 := by
  have := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp⟩
  have hpo : Odd p := H.out.odd_of_ne_two hp.ne'
  let : NormedAlgebra ℚ ℂ := normedAlgebraRat
  have := Embeddings.pow_eq_one_of_norm_eq_one K ℂ (x := u * (unitsComplexConj K u)⁻¹) ?_ ?_
  · have H := roots_of_unity_in_cyclo hζ hpo (u * (unitsComplexConj K u)⁻¹ : K) this
    obtain ⟨n, k, hz⟩ := H
    simp_rw [← pow_mul]
    have hk := Nat.even_or_odd k
    rcases hk with hk | hk
    · simp only [hk.neg_one_pow, one_mul] at hz
      rw [← map_mul, ← Units.val_mul, ← map_pow, ← Units.val_pow_eq_pow_val] at hz
      norm_cast at hz
      rw [hz]
      refine (exists_congr fun a => ?_).mp
        ((hζ.toInteger_isPrimitiveRoot.isUnit_unit (NeZero.ne p)).exists_pow_eq_pow_two_mul hpo n)
      · rw [mul_comm]
    · by_contra
      simp only [hk.neg_one_pow, neg_mul, one_mul] at hz
      rw [← map_mul, ← Units.val_mul, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_neg] at hz
      norm_cast at hz
      simpa [hz] using unit_inv_conj_not_neg_zeta_runity hζ u n hp
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
variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem conj_map_span_singleton [IsCMField K] (a : 𝓞 K) :
    (Ideal.span {a}).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span {ringOfIntegersComplexConj K a} := by
  simpa using
    (Ideal.map_span ((ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ({a} : Set (𝓞 K)))
theorem ideal_map_conj_eq [IsCMField K]
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K))) :
    (I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) := by
  rw [Ideal.map_map]
  congr
  ext x
  simp [RingHom.comp_apply, AlgEquiv.commutes]
theorem conj_generator_associated [IsCMField K]
    (a : 𝓞 K) (_ha : a ≠ 0) (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (hIa : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hIca : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a}) :
    ∃ u : (𝓞 K)ˣ, ringOfIntegersComplexConj K a = u * a := by
  let hspan : Ideal.span {a} = Ideal.span {ringOfIntegersComplexConj K a} := hIa.symm.trans hIca
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm
theorem conj_unit_mul_eq_one [IsCMField K]
    (a : 𝓞 K) (ha : a ≠ 0) (u : (𝓞 K)ˣ)
    (hu : ringOfIntegersComplexConj K a = u * a) :
    unitsComplexConj K u * u = 1 := by
  have hcc : ringOfIntegersComplexConj K (ringOfIntegersComplexConj K a) = a := by
    apply RingOfIntegers.ext
    simp [coe_ringOfIntegersComplexConj, complexConj_apply_apply]
  have hu1 : a = (unitsComplexConj K u : (𝓞 K)ˣ) * ringOfIntegersComplexConj K a := by
    simpa [hcc, unitsComplexConj, map_mul] using! congrArg (ringOfIntegersComplexConj K) hu
  rw [hu] at hu1
  have hu2 : a = (((unitsComplexConj K u * u : (𝓞 K)ˣ) : 𝓞 K) * a) := by
    simpa [mul_assoc] using hu1
  apply Units.ext
  apply mul_right_cancel₀ ha
  simpa [one_mul] using hu2.symm
include hp_odd in
theorem antisymmetric_unit_is_root_of_unity [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (u : (𝓞 K)ˣ) (_hu : unitsComplexConj K u * u = 1) :
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ = (hζ.unit' ^ m) ^ 2 :=
  unit_inv_conj_is_root_of_unity (hζ := hζ) u
    (lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd))
include hp_odd in
theorem antisymmetric_unit_eq_neg_one_pow_mul_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (u : (𝓞 K)ˣ)
    (hu : unitsComplexConj K u * u = 1) :
    ∃ n k : ℕ, u = (-1 : (𝓞 K)ˣ) ^ k * hζ.unit' ^ n := by
  obtain ⟨m, hm⟩ :=
    antisymmetric_unit_is_root_of_unity (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ) u hu
  have hcu : (unitsComplexConj K u)⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hu_sq : u ^ 2 = (hζ.unit' ^ m) ^ 2 := by
    simpa [pow_two, hcu] using hm
  have hu_fin : ∃ n : ℕ, ∃ _ : 0 < n, (u : K) ^ n = 1 := by
    refine ⟨2 * p, Nat.mul_pos (by decide) hp.1.pos, ?_⟩
    have hu_sqK :
        (u : K) ^ 2 = (((((hζ.unit' ^ m) ^ 2 : (𝓞 K)ˣ) : (𝓞 K)) : K)) :=
      congrArg (fun x : (𝓞 K)ˣ => (((x : (𝓞 K)) : K))) hu_sq
    calc
      (u : K) ^ (2 * p) = ((u : K) ^ 2) ^ p := by rw [pow_mul]
      _ = (((((hζ.unit' ^ m) ^ 2 : (𝓞 K)ˣ) : (𝓞 K)) : K)) ^ p := by rw [hu_sqK]
      _ = 1 := by
        let ν : (𝓞 K)ˣ := hζ.unit' ^ m
        have hνp : ν ^ p = 1 := by
          dsimp [ν]
          rw [← pow_mul, mul_comm, pow_mul, hζ.unit'_pow, one_pow]
        have hν2p : (ν ^ 2) ^ p = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hνp, one_pow]
        exact congrArg (fun x : (𝓞 K)ˣ => (((x : (𝓞 K)) : K))) hν2p
  have hpo : Odd p := hp.1.odd_of_ne_two hp_odd
  obtain ⟨n, k, hk⟩ := roots_of_unity_in_cyclo (K := K) (hζ := hζ) hpo (u : K) hu_fin
  refine ⟨n, k, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  have hunit_coe : ((((hζ.unit' : (𝓞 K)ˣ) : 𝓞 K) : K)) =
      IsCyclotomicExtension.zeta p ℚ K := by
    change (hζ.toInteger : K) = IsCyclotomicExtension.zeta p ℚ K
    exact hζ.coe_toInteger
  change (u : K) =
    (-1 : K) ^ k * IsCyclotomicExtension.zeta p ℚ K ^ n
  change (u : K) = (-1 : K) ^ k * hζ.toInteger.1 ^ n at hk
  rw [hζ.coe_toInteger] at hk
  exact hk
theorem conj_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (m : ℕ) :
    complexConj K (hζ.unit' ^ m : (𝓞 K)ˣ) = ((hζ.unit' ^ m)⁻¹ : (𝓞 K)ˣ) := by
  have hzeta_torsion : hζ.unit' ∈ NumberField.Units.torsion K := by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.1.pos, ?_⟩)
    exact hζ.unit'_pow
  have hbase : unitsComplexConj K hζ.unit' = (hζ.unit'⁻¹ : (𝓞 K)ˣ) := by
    simpa using unitsComplexConj_torsion K ⟨hζ.unit', hzeta_torsion⟩
  have hunits :
      unitsComplexConj K (hζ.unit' ^ m : (𝓞 K)ˣ) =
        ((hζ.unit' ^ m)⁻¹ : (𝓞 K)ˣ) := by
    calc
      unitsComplexConj K (hζ.unit' ^ m : (𝓞 K)ˣ) =
          (unitsComplexConj K hζ.unit') ^ m := by simp
      _ = ((hζ.unit')⁻¹ : (𝓞 K)ˣ) ^ m := by rw [hbase]
      _ = ((hζ.unit' ^ m)⁻¹ : (𝓞 K)ˣ) := by simp
  have hro :
      ringOfIntegersComplexConj K (((hζ.unit' ^ m : (𝓞 K)ˣ) : 𝓞 K)) =
        (((hζ.unit' ^ m)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := Units.ext_iff.1 hunits
  exact RingOfIntegers.ext_iff.mp hro
include hp_odd in
theorem ramificationIdx_zetaPrimePlus_eq_two [IsCMField K] :
    (zetaPrime p K).ramificationIdx (𝓞 (NumberField.maximalRealSubfield K)) = 2 := by
  have hmap0 : Ideal.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))
      (zetaPrimePlus p K) ≠ ⊥ := by
    rw [zetaPrimePlus_map_eq p hp_odd K]
    exact pow_ne_zero 2 (zetaPrime_ne_bot p K)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (zetaPrimePlus p K) (zetaPrime p K)
    hmap0, zetaPrimePlus_map_eq p hp_odd K, multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (zetaPrime_ne_bot p K) (zetaPrime_isPrime p K))]
include hp_odd in
theorem multiplicity_zetaPrime_even_of_map_eq_span [IsCMField K]
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a : 𝓞 K) (ha : a ≠ 0)
    (hIa :
      I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a}) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K) a) := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  let f : 𝓞 (NumberField.maximalRealSubfield K) →+* 𝓞 K :=
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
  let P : Ideal (𝓞 K) := zetaPrime p K
  let PPlus : Ideal (𝓞 (NumberField.maximalRealSubfield K)) := zetaPrimePlus p K
  let π : 𝓞 K := (zeta_spec p ℚ K).toInteger - 1
  have hI0 : I ≠ ⊥ := by
    intro hbot
    rw [hbot, Ideal.map_bot] at hIa
    exact ha (by simpa [Ideal.span_singleton_eq_bot] using hIa.symm)
  have hmap0 : I.map f ≠ ⊥ := by
    rw [hIa]
    simp [ha]
  have hP0 : P ≠ ⊥ := zetaPrime_ne_bot p K
  have hPprime : P.IsPrime := by
    dsimp [P]
    exact zetaPrime_isPrime p K
  have hPPlus0 : PPlus ≠ ⊥ := by
    intro hbot
    have hmap : Ideal.map f PPlus = P ^ 2 := by
      simpa [f, P, PPlus] using zetaPrimePlus_map_eq p hp_odd K
    rw [hbot, Ideal.map_bot] at hmap
    exact (pow_ne_zero 2 hP0) hmap.symm
  have hPIrr : Irreducible P := (Ideal.prime_of_isPrime hP0 hPprime).irreducible
  have hPPlusIrr : Irreducible PPlus :=
    (Ideal.prime_of_isPrime hPPlus0 inferInstance).irreducible
  have hemul : emultiplicity P (I.map f) = PPlus.ramificationIdx' P * emultiplicity PPlus I := by
    simpa [P, PPlus, f] using
      Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
        (R := 𝓞 (NumberField.maximalRealSubfield K)) (S := 𝓞 K)
        (v := PPlus) (w := P) (I := I) hI0 hPPlusIrr hPIrr hP0
  have hcount_even :
      Even (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I.map f))) := by
    rw [Even]
    refine ⟨Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    have hemul' := hemul
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := PPlus) (q := P) hPPlus0,
      ramificationIdx_zetaPrimePlus_eq_two (p := p) (hp_odd := hp_odd) (K := K),
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPIrr hmap0,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPPlusIrr hI0,
      normalize_eq P, normalize_eq PPlus] at hemul'
    have hemul_nat :
        Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (I.map f)) =
          2 * Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I) := by
      exact_mod_cast hemul'
    simpa [two_mul] using hemul_nat
  have hπPrime : Prime π := by simpa [π] using hζ.zeta_sub_one_prime'
  let e := multiplicity π a
  have hπFin : FiniteMultiplicity π a := FiniteMultiplicity.of_prime_left hπPrime ha
  have hπe_dvd : π ^ e ∣ a := (hπFin.pow_dvd_iff_le_multiplicity).2 le_rfl
  have hπe_not_dvd : ¬π ^ (e + 1) ∣ a := by
    rw [hπFin.pow_dvd_iff_le_multiplicity]
    exact Nat.not_succ_le_self e
  have hcount_span :
      Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) = e := by
    apply Ideal.count_normalizedFactors_eq (p := P) (x := Ideal.span {a})
    · dsimp [P]
      rw [zetaPrime, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
        Ideal.mem_span_singleton]
      exact hπe_dvd
    · intro hle
      exact hπe_not_dvd <| by
        dsimp [P] at hle
        rw [zetaPrime, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem,
          Ideal.mem_span_singleton] at hle
        exact hle
  have :
      Even (Multiset.count P (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}))) := by
    rw [← hIa]
    simpa [f] using hcount_even
  simpa [e, hcount_span] using this
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
variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
include hp_odd in
theorem generator_unit_eq_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (ha : a ≠ 0)
    (hIa : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hu : ringOfIntegersComplexConj K a = u * a)
    (hclass : ∃ n k : ℕ, u = (-1 : (𝓞 K)ˣ) ^ k * hζ.unit' ^ n) :
    ∃ n : ℕ, u = hζ.unit' ^ n := by
  obtain ⟨n, k, huk⟩ := hclass
  by_cases hk_even : Even k
  · rcases hk_even with ⟨m, rfl⟩
    have hneg_even : (-1 : (𝓞 K)ˣ) ^ (m + m) = 1 :=
      Even.neg_one_pow (show Even (m + m) from ⟨m, rfl⟩)
    refine ⟨n, ?_⟩
    calc
      u = (-1 : (𝓞 K)ˣ) ^ (m + m) * hζ.unit' ^ n := huk
      _ = hζ.unit' ^ n := by rw [hneg_even]; simp
  · have hk_odd : Odd k := Nat.not_even_iff_odd.mp hk_even
    let π : 𝓞 K := hζ.toInteger - 1
    let P : Ideal (𝓞 K) := zetaPrime p K
    let e := multiplicity π a
    have heven : Even e :=
      multiplicity_zetaPrime_even_of_map_eq_span (p := p) (hp_odd := hp_odd) (K := K) I a ha hIa
    have hπPrime : Prime π := by simpa [π] using hζ.zeta_sub_one_prime'
    have hπFin : FiniteMultiplicity π a := FiniteMultiplicity.of_prime_left hπPrime ha
    obtain ⟨b, hpow, hnotdvd⟩ := hπFin.exists_eq_pow_mul_and_not_dvd
    have hb_not_mem : b ∉ P := by
      simpa [P, π, zetaPrime, Ideal.mem_span_singleton] using hnotdvd
    have hu_odd : u = (-1 : (𝓞 K)ˣ) * hζ.unit' ^ n := by
      calc
        u = (-1 : (𝓞 K)ˣ) ^ k * hζ.unit' ^ n := huk
        _ = (-1 : (𝓞 K)ˣ) * hζ.unit' ^ n := by rw [Odd.neg_one_pow hk_odd]
    let γ : (𝓞 K)ˣ := (-1 : (𝓞 K)ˣ) * hζ.unit' ^ (p - 1)
    have hc_pi : ringOfIntegersComplexConj K π = (γ : (𝓞 K)ˣ) * π := by
      have hc_pi' : ringOfIntegersComplexConj K π = -hζ.toInteger ^ (p - 1) * π := by
        rw [show π = hζ.toInteger - 1 by rfl, map_sub, map_one, complexConj_apply_zeta]
        linear_combination zeta_toInteger_pow_pred_mul p K
      simpa [γ, π, mul_assoc, mul_left_comm, mul_comm] using! hc_pi'
    have hγ_mul : γ ^ e * hζ.unit' ^ e = 1 := by
      have hγhu : γ * hζ.unit' = (-1 : (𝓞 K)ˣ) := by
        dsimp [γ]
        rw [mul_assoc, ← pow_succ, Nat.sub_one_add_one hp.1.ne_zero, hζ.unit'_pow, mul_one]
      have hmulpow : γ ^ e * hζ.unit' ^ e = (γ * hζ.unit') ^ e := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using (mul_pow γ (hζ.unit') e).symm
      calc
        γ ^ e * hζ.unit' ^ e = (γ * hζ.unit') ^ e := hmulpow
        _ = (-1 : (𝓞 K)ˣ) ^ e := by rw [hγhu]
        _ = 1 := by simpa using (Even.neg_one_pow heven : (-1 : (𝓞 K)ˣ) ^ e = 1)
    let u' : (𝓞 K)ˣ := hζ.unit' ^ e * u
    have hcb : ringOfIntegersComplexConj K b = u' * b := by
      have hcalc : ringOfIntegersComplexConj K (π ^ e * b) = u * (π ^ e * b) := by
        calc
          ringOfIntegersComplexConj K (π ^ e * b) = ringOfIntegersComplexConj K a := by rw [hpow]
          _ = u * a := hu
          _ = u * (π ^ e * b) := by rw [hpow]
      rw [map_mul, map_pow, hc_pi, mul_pow] at hcalc
      have hcancel : (((γ ^ e : (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K b) =
          ((u : (𝓞 K)ˣ) : 𝓞 K) * b := by
        have htmp : π ^ e * ((((γ ^ e : (𝓞 K)ˣ) : 𝓞 K) * ringOfIntegersComplexConj K b)) =
            π ^ e * ((((u : (𝓞 K)ˣ) : 𝓞 K) * b)) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hcalc
        exact mul_left_cancel₀ (pow_ne_zero _ hπPrime.ne_zero) htmp
      have hγ_mul' : hζ.unit' ^ e * γ ^ e = 1 := by simpa [mul_comm] using hγ_mul
      have hmult :=
        congrArg (fun x : 𝓞 K => (((hζ.unit' ^ e : (𝓞 K)ˣ) : 𝓞 K) * x)) hcancel
      have hγ_mul_coe : ((((hζ.unit' ^ e : (𝓞 K)ˣ) * γ ^ e : (𝓞 K)ˣ) : 𝓞 K)) = 1 :=
        congrArg (fun x : (𝓞 K)ˣ => (x : 𝓞 K)) hγ_mul'
      have hmult'' : ((((hζ.unit' ^ e : (𝓞 K)ˣ) * γ ^ e : (𝓞 K)ˣ) : 𝓞 K) *
          ringOfIntegersComplexConj K b) =
          ((((hζ.unit' ^ e : (𝓞 K)ˣ) * u : (𝓞 K)ˣ) : 𝓞 K) * b) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmult
      have hmult' : ringOfIntegersComplexConj K b =
          ((((hζ.unit' ^ e : (𝓞 K)ˣ) * u : (𝓞 K)ˣ) : 𝓞 K) * b) := by
        calc
          ringOfIntegersComplexConj K b =
              ((((hζ.unit' ^ e : (𝓞 K)ˣ) * γ ^ e : (𝓞 K)ˣ) : 𝓞 K) *
                ringOfIntegersComplexConj K b) := by rw [hγ_mul_coe]; simp
          _ =
              ((((hζ.unit' ^ e : (𝓞 K)ˣ) * u : (𝓞 K)ˣ) : 𝓞 K) * b) := hmult''
      simpa [u', mul_assoc, mul_left_comm, mul_comm] using hmult'
    have hpow_sub : ∀ m : ℕ, (hζ.toInteger ^ m - 1 : 𝓞 K) ∈ P := by
      intro m
      dsimp [P]
      rw [zetaPrime, Ideal.mem_span_singleton]
      have hdiv := sub_dvd_pow_sub_pow hζ.toInteger (1 : 𝓞 K) m
      rwa [one_pow] at hdiv
    have hu'_class : u' = (-1 : (𝓞 K)ˣ) * hζ.unit' ^ (e + n) := by
      dsimp [u']
      calc
        hζ.unit' ^ e * u =
            hζ.unit' ^ e * ((-1 : (𝓞 K)ˣ) * hζ.unit' ^ n) := by rw [hu_odd]
        _ = (-1 : (𝓞 K)ˣ) * (hζ.unit' ^ e * hζ.unit' ^ n) := by
          simp [mul_left_comm, mul_comm]
        _ = (-1 : (𝓞 K)ˣ) * hζ.unit' ^ (e + n) := by rw [← pow_add]
    have hu'_plus_mem : ((((u' : (𝓞 K)ˣ) : 𝓞 K) + 1) : 𝓞 K) ∈ P := by
      have hu'_plus_eq : (((u' : (𝓞 K)ˣ) : 𝓞 K) + 1 : 𝓞 K) =
          (1 - hζ.toInteger ^ e * hζ.toInteger ^ n : 𝓞 K) := by
        rw [hu'_class]
        simp only [Units.val_mul, Units.val_neg]
        rw [show (((hζ.unit' ^ (e + n) : (𝓞 K)ˣ) : 𝓞 K)) =
          hζ.toInteger ^ (e + n) by rfl]
        rw [pow_add]
        simp [sub_eq_add_neg, add_comm]
      have hpow_sub' : (1 - hζ.toInteger ^ e * hζ.toInteger ^ n : 𝓞 K) ∈ P := by
        have :
            (1 - hζ.toInteger ^ e * hζ.toInteger ^ n : 𝓞 K) =
              -(hζ.toInteger ^ (e + n) - 1) := by
          rw [pow_add]
          ring
        rw [this]
        exact P.neg_mem (hpow_sub (e + n))
      rw [hu'_plus_eq]
      exact hpow_sub'
    have hu'_minus_not_mem : ((((u' : (𝓞 K)ˣ) : 𝓞 K) - 1) : 𝓞 K) ∉ P := by
      intro hminus
      have hp2 : 2 < p := lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
      have htwo : (2 : 𝓞 K) ∈ P := by
        have hsub := Ideal.sub_mem _ hu'_plus_mem hminus
        convert hsub using 1
        ring
      exact IsCyclotomicExtension.Rat.two_not_mem_span_zeta_sub_one' p (zeta_spec p ℚ K) hp2 htwo
    have hprod_mem : ((((u' : (𝓞 K)ˣ) : 𝓞 K) - 1) * b : 𝓞 K) ∈ P := by
      have hres : (ringOfIntegersComplexConj K b : 𝓞 K) - b ∈ P :=
        complexConj_sub_mem_zetaPrime p K b
      convert hres using 1
      rw [hcb]
      ring
    exfalso
    rcases (zetaPrime_isPrime p K).mem_or_mem hprod_mem with hunit_mem | hb_mem
    · exact hu'_minus_not_mem hunit_mem
    · exact hb_not_mem hb_mem
include hp_odd in
theorem exists_conj_fixed_associate_of_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (hu : ringOfIntegersComplexConj K a = u * a)
    (hclass : ∃ n : ℕ, u = hζ.unit' ^ n) :
    ∃ b : 𝓞 K, ringOfIntegersComplexConj K b = b ∧ Ideal.span {b} = Ideal.span {a} := by
  have hpo : Odd p := hp.1.odd_of_ne_two hp_odd
  obtain ⟨n, rfl⟩ := hclass
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul hζ.unit'_pow hpo n
  let μ : (𝓞 K)ˣ := hζ.unit' ^ m
  have hμsq : (hζ.unit' ^ n : (𝓞 K)ˣ) = μ ^ 2 := by
    dsimp [μ]
    calc
      (hζ.unit' ^ n : (𝓞 K)ˣ) = hζ.unit' ^ (2 * m) := hm
      _ = (hζ.unit' ^ m) ^ 2 := by simp [pow_mul, mul_comm]
  let b : 𝓞 K := a * (μ : (𝓞 K)ˣ)
  refine ⟨b, ?_, ?_⟩
  · have hμconj : complexConj K μ = (μ⁻¹ : (𝓞 K)ˣ) := by
      dsimp [μ]
      simpa using conj_zeta_pow (p := p) (K := K) (hζ := hζ) m
    have hμcoe :
        ringOfIntegersComplexConj K ((μ : (𝓞 K)ˣ) : 𝓞 K) =
          ((μ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
      apply RingOfIntegers.ext
      simpa [coe_ringOfIntegersComplexConj] using hμconj
    have huμinv : (hζ.unit' ^ n : (𝓞 K)ˣ) * μ⁻¹ = μ := by
      rw [hμsq]
      simp [pow_two, mul_assoc]
    calc
      ringOfIntegersComplexConj K b =
          ringOfIntegersComplexConj K a *
            ringOfIntegersComplexConj K ((μ : (𝓞 K)ˣ) : 𝓞 K) := by
            dsimp [b]
            simp
      _ = ((hζ.unit' ^ n : (𝓞 K)ˣ) : 𝓞 K) * a * (((μ⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) := by
            dsimp [b]
            simpa [mul_assoc, hμcoe] using congrArg
              (fun x : 𝓞 K =>
                x * ringOfIntegersComplexConj K (((μ : (𝓞 K)ˣ) : 𝓞 K))) hu
      _ =
          ((((hζ.unit' ^ n : (𝓞 K)ˣ) * μ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * a) := by
            simp [mul_assoc, mul_comm]
      _ = (μ : (𝓞 K)ˣ) * a := by rw [huμinv]
      _ = b := by dsimp [b]; simp [mul_comm]
  · rw [Ideal.span_singleton_eq_span_singleton]
    dsimp [b]
    exact (associated_mul_unit_right a (μ : (𝓞 K)ˣ) μ.isUnit).symm
include hp_odd in
theorem exists_conj_fixed_associate_of_classification [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (hIa : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hu : ringOfIntegersComplexConj K a = u * a)
    (hclass : ∃ n k : ℕ, u = (-1 : (𝓞 K)ˣ) ^ k * hζ.unit' ^ n) :
    ∃ b : 𝓞 K, ringOfIntegersComplexConj K b = b ∧ Ideal.span {b} = Ideal.span {a} := by
  by_cases ha : a = 0
  · refine ⟨0, ?_, ?_⟩ <;> simp [ha]
  · obtain ⟨n, hn⟩ :=
      generator_unit_eq_zeta_pow (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ)
        I a u ha hIa hu hclass
    exact exists_conj_fixed_associate_of_zeta_pow
      (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ) a u hu ⟨n, hn⟩
theorem mem_ringOfIntegers_of_conj_eq_self [IsCMField K]
    (b : 𝓞 K) (hb : ringOfIntegersComplexConj K b = b) :
    b ∈ Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
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
variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
include hp_odd in
theorem isCMField_of_cyclotomic : IsCMField K :=
  Rat.isCMField (S := {p}) _ ⟨p, by grind [hp.1.two_le]⟩
theorem finrank_K_over_Kplus [IsCMField K] :
    Module.finrank ((NumberField.maximalRealSubfield K)) K = 2 :=
  IsQuadraticExtension.finrank_eq_two _ _
theorem finrank_Kplus_over_rat [IsCMField K] :
    Module.finrank ℚ ((NumberField.maximalRealSubfield K)) = (p - 1) / 2 := by
  have h1 : Module.finrank ((NumberField.maximalRealSubfield K)) K = 2 := finrank_K_over_Kplus K
  have h2 : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.1.pos),
        Nat.totient_prime hp.1]
  have htow := Module.finrank_mul_finrank ℚ ((NumberField.maximalRealSubfield K)) K
  rw [h1, h2] at htow
  exact (Nat.div_eq_of_eq_mul_left (by omega) htow.symm).symm
include hp_odd in
theorem indexRealUnits_eq_one [IsCMField K] :
    IsCMField.indexRealUnits K = 1 := by
  have hp2 : 2 < p := lt_of_le_of_ne hp.1.two_le (Ne.symm hp_odd)
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hzeta_torsion : hζ.unit' ∈ NumberField.Units.torsion K := by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, by omega, ?_⟩)
    exact hζ.unit'_pow
  have hrange :
      (IsCMField.unitsMulComplexConjInv K).range =
        (powMonoidHom 2 : NumberField.Units.torsion K →* NumberField.Units.torsion K).range := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨u, rfl⟩
      obtain ⟨m, hm⟩ := unit_inv_conj_is_root_of_unity hζ u hp2
      refine ⟨⟨hζ.unit' ^ m, (NumberField.Units.torsion K).pow_mem hzeta_torsion m⟩, ?_⟩
      apply Subtype.ext
      simpa [pow_two] using! hm.symm
    · rintro x ⟨u, rfl⟩
      exact ⟨u, by simp [pow_two]⟩
  have hrange_idx : (IsCMField.unitsMulComplexConjInv K).range.index = 2 := by
    rw [hrange, IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right]
    exact even_iff_two_dvd.mp (NumberField.Units.even_torsionOrder K)
  have hmul : IsCMField.indexRealUnits K * 2 = 2 := by
    simpa [hrange_idx] using IsCMField.indexRealUnits_mul_eq K
  omega
noncomputable def h : ℕ := Fintype.card (ClassGroup (𝓞 K))
noncomputable def hPlus [IsCMField K] : ℕ := Fintype.card (ClassGroup (𝓞 ((NumberField.maximalRealSubfield K))))
end CyclotomicSetup
end KummerCriterion
end
noncomputable section
open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
section CyclotomicSetup
variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem map_comap_eq_ringOfIntegers
    (L : Type*) [Field L] [NumberField L]
    (J : Ideal (𝓞 (NumberField.maximalRealSubfield L))) :
    (J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L))).comap
        (algebraMap (𝓞 (NumberField.maximalRealSubfield L)) (𝓞 L)) = J := by
  simpa using Ideal.comap_map_eq_self_of_faithfullyFlat J
theorem isPrincipal_of_map_eq_span_singleton_of_mem
    (I : Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (b₀ : 𝓞 ((NumberField.maximalRealSubfield K)))
    (hb : I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) =
      Ideal.span {algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K) b₀}) :
    I.IsPrincipal := by
  refine ⟨b₀, ?_⟩
  let f : 𝓞 ((NumberField.maximalRealSubfield K)) →+* 𝓞 K := algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)
  have hbc := congrArg (Ideal.comap f) hb
  have hspan : Ideal.comap f (Ideal.span {f b₀}) = Ideal.span {b₀} := by
    calc
      Ideal.comap f (Ideal.span {f b₀}) = Ideal.comap f ((Ideal.span {b₀}).map f) := by
        rw [Ideal.map_span, Set.image_singleton]
      _ = Ideal.span {b₀} := map_comap_eq_ringOfIntegers K (Ideal.span {b₀})
  calc
    I = Ideal.comap f (I.map f) := (map_comap_eq_ringOfIntegers K I).symm
    _ = Ideal.comap f (Ideal.span {f b₀}) := hbc
    _ = Ideal.span {b₀} := hspan
include hp_odd in
theorem isPrincipal_of_isPrincipal_map_Kplus' [IsCMField K]
    (I : Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (hI : (I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal := by
  obtain ⟨a, ha⟩ := hI
  by_cases hzero : a = 0
  · have : I = ⊥ := by
      rw [← Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)), ha, hzero]
      simp
    exact this ▸ bot_isPrincipal
  have hIa : I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) = Ideal.span {a} := ha
  have hIcon := ideal_map_conj_eq (K := K) I
  have hIca : I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a} := by
    rw [← hIcon, hIa, conj_map_span_singleton]
  obtain ⟨u, hu⟩ := conj_generator_associated (K := K) a hzero I hIa hIca
  have hanti := conj_unit_mul_eq_one (K := K) a hzero u hu
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  obtain ⟨n, k, hclass⟩ :=
    antisymmetric_unit_eq_neg_one_pow_mul_zeta_pow
      (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ) u hanti
  obtain ⟨b, hb_conj, hb_span⟩ :=
    exists_conj_fixed_associate_of_classification
      (p := p) (hp_odd := hp_odd) (K := K) (hζ := hζ) I a u hIa hu ⟨n, k, hclass⟩
  obtain ⟨b₀, hb₀⟩ := mem_ringOfIntegers_of_conj_eq_self (K := K) b hb_conj
  have hspan : I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) = Ideal.span {b} := by
    rw [hIa, ← hb_span]
  rw [← hb₀] at hspan
  exact isPrincipal_of_map_eq_span_singleton_of_mem K I b₀ hspan
include hp_odd in
theorem isPrincipal_of_isPrincipal_map_Kplus [IsCMField K]
    (I : Ideal (𝓞 ((NumberField.maximalRealSubfield K))))
    (hI : (I.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal :=
  isPrincipal_of_isPrincipal_map_Kplus' (p := p) (hp_odd := hp_odd) (K := K) I hI
abbrev classGroupMap [IsCMField K] :
    ClassGroup (𝓞 ((NumberField.maximalRealSubfield K))) →* ClassGroup (𝓞 K) :=
  ClassGroup.extendedHom (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)
include hp_odd in
theorem classGroupMap_injective [IsCMField K] :
    Function.Injective (classGroupMap K) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [ClassGroup.mk0_eq_one_iff I.2]
  refine isPrincipal_of_isPrincipal_map_Kplus (p := p) (hp_odd := hp_odd) (K := K) I.1 ?_
  have hne : I.1.map (algebraMap (𝓞 ((NumberField.maximalRealSubfield K))) (𝓞 K)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective _ _)).not.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hne),
    ← ClassGroup.extendedHom_mk0]
  exact hc
include hp_odd in
theorem hPlus_dvd_h [IsCMField K] : (KummerCriterion.hPlus K) ∣ (KummerCriterion.h K) := by
  rw [KummerCriterion.hPlus, KummerCriterion.h,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_dvd_of_injective (classGroupMap K)
    (classGroupMap_injective p hp_odd K)
noncomputable def hMinus [IsCMField K] : ℕ := (KummerCriterion.h K) / (KummerCriterion.hPlus K)
include hp_odd in
theorem h_eq_hPlus_mul_hMinus [IsCMField K] : (KummerCriterion.h K) = (KummerCriterion.hPlus K) * (KummerCriterion.hMinus K) := by
  rw [hMinus, Nat.mul_div_cancel' (hPlus_dvd_h p hp_odd K)]
end CyclotomicSetup
end KummerCriterion
end
end Module6

open NumberField

theorem OMA.solution : OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1.H3 := by
  intro p hp hp2
  let K := CyclotomicField p ℚ
  let : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let : IsCMField K := KummerCriterion.isCMField_of_cyclotomic p hp2 K
  exact KummerCriterion.h_eq_hPlus_mul_hMinus p hp2 K
