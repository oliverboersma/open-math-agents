import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1
import Mathlib
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Vector
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

/-!
# Index of the real cyclotomic-unit subgroup

Integration and exact-target bridge: Hanan Beer (@hananzlt).
The mathematical formalization is reused from Riccardo Brasca (@riccardobrasca)
and the KummerCriterion contributors, and from the flt-regular contributors.
Contributors to the reused source history include Ruben Van de Velde,
Chris Birkbeck, Andrew Yang, and Kim Morrison. Original work is retained
under the Apache License, Version 2.0.

KummerCriterion source: https://github.com/riccardobrasca/KummerCriterion/tree/470de714f3de5a1ec8c0f6209502c1c5272c2c43
flt-regular source: https://github.com/leanprover-community/flt-regular/tree/bd81b78ba6e9f1c57215ff096e9e8f45d5d4b54b
Reduction: Hanan Beer (@hananzlt), PR7356, following @Noctluxis's R3.
This proves only the real cyclotomic-unit subgroup index input.
Common dependency integration reuses Hanan Beer campaign PR6541.
-/

/-- Transparent short name for the repeatedly used maximal real subfield. -/
noncomputable abbrev oMR (K : Type*) [Field K] : Subfield K := NumberField.maximalRealSubfield K

-- Source: FltRegular.NumberTheory.Cyclotomic.UnitLemmas
section Module0
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
end Module0

-- Source: KummerCriterion.CyclotomicUnits.DeletedFourier
section Module1
noncomputable section
open scoped BigOperators
namespace KummerCriterion
namespace CyclotomicUnits
abbrev Nonidentity (G : Type*) [One G] := {g : G // g ≠ 1}
abbrev NontrivChar (G : Type*) [CommMonoid G] :=
  {χ : MulChar G ℂ // χ ≠ 1}
theorem sum_subtype_ne_eq_sum_erase {α : Type*} [Fintype α] [DecidableEq α]
    (a₀ : α) (f : α → ℂ) [Fintype {x : α // x ≠ a₀}] :
    ∑ x : {x : α // x ≠ a₀}, f x.val =
      ∑ x ∈ (Finset.univ : Finset α).erase a₀, f x :=
  (Finset.sum_subtype _ (fun x => by simp) f).symm
section FiniteGroup
variable {G : Type*} [CommGroup G] [Fintype G]
theorem card_nonidentity_add_one [DecidableEq G] :
    Fintype.card (Nonidentity G) + 1 = Fintype.card G := by
  have hnon :
      Fintype.card (Nonidentity G) = Fintype.card G - 1 := by
    simp [Nonidentity]
  rw [hnon]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩))
theorem card_group_ne_zero_complex :
    ((Fintype.card G : ℕ) : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : G)⟩).ne'
theorem sum_nonidentity_mulChar_eq_neg_one
    [DecidableEq G]
    (χ : MulChar G ℂ) (hχ : χ ≠ 1) :
    ∑ h : Nonidentity G, χ h.val = -1 := by
  classical
  have hfull : ∑ g : G, χ g = 0 := MulChar.sum_eq_zero_of_ne_one hχ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))] at hfull
  rw [← sum_subtype_ne_eq_sum_erase (α := G) (a₀ := 1) (f := fun g => χ g)] at hfull
  have hsplit : (1 : ℂ) + ∑ h : Nonidentity G, χ h.val = 0 := by
    simpa using hfull
  linear_combination hsplit
theorem sum_nonidentity_inv_mulChar_mul
    [DecidableEq G]
    [DecidableEq (MulChar G ℂ)]
    (χ ψ : MulChar G ℂ) :
    ∑ h : Nonidentity G, (χ h.val)⁻¹ * ψ h.val =
      if χ = ψ then (Fintype.card (Nonidentity G) : ℂ) else -1 := by
  classical
  by_cases hχψ : χ = ψ
  · subst hχψ
    rw [if_pos rfl]
    rw [show (∑ h : Nonidentity G, (χ h.val)⁻¹ * χ h.val) =
        ∑ _h : Nonidentity G, (1 : ℂ) from by
      refine Finset.sum_congr rfl ?_
      intro h _
      have h_unit : IsUnit (χ h.val) := IsUnit.map χ.toMonoidHom (Group.isUnit h.val)
      exact inv_mul_cancel₀ h_unit.ne_zero]
    simp
  · rw [if_neg hχψ]
    have hchar : χ⁻¹ * ψ ≠ 1 := by
      intro h
      apply hχψ
      calc
        χ = χ * 1 := by rw [mul_one]
        _ = χ * (χ⁻¹ * ψ) := by rw [h]
        _ = (χ * χ⁻¹) * ψ := by rw [mul_assoc]
        _ = 1 * ψ := by rw [mul_inv_cancel]
        _ = ψ := by rw [one_mul]
    rw [← sum_nonidentity_mulChar_eq_neg_one (G := G) (χ⁻¹ * ψ) hchar]
    refine Finset.sum_congr rfl ?_
    intro h _
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv']
def deletedFourierCoeff (q : G → ℂ) (χ : MulChar G ℂ) : ℂ :=
  ∑ h : G, q h * (χ h)⁻¹
def deletedCharacterMatrix
    (ρ : NontrivChar G ≃ Nonidentity G) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun h χ => χ.val (ρ h).val
def deletedCharacterMatrixLeftInverse
    (ρ : NontrivChar G ≃ Nonidentity G) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun χ h =>
    ((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val (ρ h).val)⁻¹ - 1)
theorem deletedCharacterMatrix_leftInverse
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) :
    deletedCharacterMatrixLeftInverse (G := G) ρ *
        deletedCharacterMatrix (G := G) ρ = 1 := by
  classical
  ext χ ψ
  simp only [deletedCharacterMatrixLeftInverse, deletedCharacterMatrix, Matrix.mul_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [Equiv.sum_comp ρ (fun h : Nonidentity G =>
    (((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val h.val)⁻¹ - 1)) * ψ.val h.val)]
  rw [show (∑ h : Nonidentity G,
      ((Fintype.card G : ℕ) : ℂ)⁻¹ * ((χ.val h.val)⁻¹ - 1) * ψ.val h.val) =
      ∑ h : Nonidentity G,
        ((Fintype.card G : ℕ) : ℂ)⁻¹ *
          (((χ.val h.val)⁻¹ - 1) * ψ.val h.val) from by
    refine Finset.sum_congr rfl ?_
    intro h _
    ring]
  rw [← Finset.mul_sum]
  have hsplit :
      (∑ h : Nonidentity G, ((χ.val h.val)⁻¹ - 1) * ψ.val h.val) =
        (∑ h : Nonidentity G, (χ.val h.val)⁻¹ * ψ.val h.val) -
          ∑ h : Nonidentity G, ψ.val h.val := by
    simp_rw [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  rw [sum_nonidentity_inv_mulChar_mul (G := G) χ.val ψ.val]
  rw [sum_nonidentity_mulChar_eq_neg_one (G := G) ψ.val ψ.property]
  by_cases hχψ : χ = ψ
  · subst hχψ
    simp only [ite_true]
    have hcard : ((Fintype.card (Nonidentity G) : ℕ) : ℂ) + 1 =
        ((Fintype.card G : ℕ) : ℂ) := by
      exact_mod_cast card_nonidentity_add_one (G := G)
    have hnz : ((Fintype.card G : ℕ) : ℂ) ≠ 0 :=
      card_group_ne_zero_complex (G := G)
    field_simp [hnz]
    linear_combination hcard
  · have hval : χ.val ≠ ψ.val := fun h =>
      hχψ (Subtype.ext h)
    simp only [hval, ite_false]
    rw [if_neg hχψ]
    ring
theorem sum_translate_inv_mulChar
    (q : G → ℂ) (χ : MulChar G ℂ) (h : G) :
    ∑ k : G, q (h * k⁻¹) * χ k =
      χ h * deletedFourierCoeff (G := G) q χ := by
  classical
  let e : G ≃ G := (Equiv.inv G).trans (Equiv.mulLeft h)
  have he_apply : ∀ k : G, e k = h * k⁻¹ := by
    intro k
    rfl
  have hsum := Equiv.sum_comp e (fun t : G => q t * χ (t⁻¹ * h))
  have hleft :
      (∑ k : G, q (e k) * χ ((e k)⁻¹ * h)) =
        ∑ k : G, q (h * k⁻¹) * χ k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [he_apply]
    have hk : (h * k⁻¹)⁻¹ * h = k := by group
    rw [hk]
  rw [hleft] at hsum
  rw [hsum]
  unfold deletedFourierCoeff
  have hterm : ∀ t : G, q t * χ (t⁻¹ * h) =
      χ h * (q t * (χ t)⁻¹) := by
    intro t
    rw [map_mul, map_inv]
    ring
  rw [Finset.sum_congr rfl (fun t _ => hterm t)]
  rw [← Finset.mul_sum]
theorem sum_nonidentity_translate_inv_mulChar
    [DecidableEq G]
    (q : G → ℂ) (χ : MulChar G ℂ) (h : G) :
    ∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val =
      χ h * deletedFourierCoeff (G := G) q χ - q h := by
  classical
  have hfull := sum_translate_inv_mulChar (G := G) q χ h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G))] at hfull
  rw [← sum_subtype_ne_eq_sum_erase (α := G) (a₀ := 1)
    (f := fun k : G => q (h * k⁻¹) * χ k)] at hfull
  have hsplit :
      q h + ∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val =
        χ h * deletedFourierCoeff (G := G) q χ := by
    simpa using hfull
  linear_combination hsplit
theorem sum_nonidentity_deletedConvolution_mulChar
    [DecidableEq G]
    (q : G → ℂ) (χ : MulChar G ℂ) (hχ : χ ≠ 1) (h : G) :
    ∑ k : Nonidentity G, (q (h * k.val⁻¹) - q h) * χ k.val =
      χ h * deletedFourierCoeff (G := G) q χ := by
  classical
  have hfirst := sum_nonidentity_translate_inv_mulChar (G := G) q χ h
  have hchar := sum_nonidentity_mulChar_eq_neg_one (G := G) χ hχ
  have hsplit :
      (∑ k : Nonidentity G, (q (h * k.val⁻¹) - q h) * χ k.val) =
        (∑ k : Nonidentity G, q (h * k.val⁻¹) * χ k.val) -
          q h * ∑ k : Nonidentity G, χ k.val := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit, hfirst, hchar]
  ring
def deletedConvolutionMatrix
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    Matrix (NontrivChar G) (NontrivChar G) ℂ :=
  Matrix.of fun h k => q ((ρ h).val * (ρ k).val⁻¹) - q (ρ h).val
def deletedConvolutionMatrixOnNonidentity (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k => q (h.val * k.val⁻¹) - q h.val
omit [Fintype G] in
theorem deletedConvolutionMatrix_eq_submatrix
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    deletedConvolutionMatrix (G := G) ρ q =
      (deletedConvolutionMatrixOnNonidentity (G := G) q).submatrix ρ ρ := by
  ext h k
  rfl
theorem deletedConvolution_mul_deletedCharacter
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    deletedConvolutionMatrix (G := G) ρ q *
        deletedCharacterMatrix (G := G) ρ =
      deletedCharacterMatrix (G := G) ρ *
        Matrix.diagonal (fun χ : NontrivChar G =>
          deletedFourierCoeff (G := G) q χ.val) := by
  classical
  ext h χ
  simp only [deletedConvolutionMatrix, deletedCharacterMatrix, Matrix.mul_apply,
    Matrix.of_apply, Matrix.diagonal_apply]
  rw [Equiv.sum_comp ρ (fun k : Nonidentity G =>
    (q ((ρ h).val * k.val⁻¹) - q (ρ h).val) * χ.val k.val)]
  rw [sum_nonidentity_deletedConvolution_mulChar
    (G := G) q χ.val χ.property (ρ h).val]
  rw [Finset.sum_eq_single χ]
  · simp
  · intro ψ _ hψ
    rw [if_neg hψ, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ χ) hmem
theorem det_deletedConvolutionMatrix_eq_prod_deletedFourierCoeff
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMatrix (G := G) ρ q).det =
      ∏ χ : NontrivChar G, deletedFourierCoeff (G := G) q χ.val := by
  classical
  have hmul := deletedConvolution_mul_deletedCharacter (G := G) ρ q
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have hP : (deletedCharacterMatrix (G := G) ρ).det ≠ 0 :=
    Matrix.det_ne_zero_of_left_inverse
      (deletedCharacterMatrix_leftInverse (G := G) ρ)
  exact mul_right_cancel₀ hP (by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hdet)
theorem det_deletedConvolutionMatrixOnNonidentity_eq_prod_deletedFourierCoeff
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMatrixOnNonidentity (G := G) q).det =
      ∏ χ : NontrivChar G, deletedFourierCoeff (G := G) q χ.val := by
  have h := det_deletedConvolutionMatrix_eq_prod_deletedFourierCoeff
    (G := G) ρ q
  rw [deletedConvolutionMatrix_eq_submatrix] at h
  rwa [Matrix.det_submatrix_equiv_self] at h
def nonidentityInvEquiv : Nonidentity G ≃ Nonidentity G where
  toFun h := ⟨h.val⁻¹, by
    intro hinv
    exact h.property <| inv_eq_one.mp hinv⟩
  invFun h := ⟨h.val⁻¹, by
    intro hinv
    exact h.property <| inv_eq_one.mp hinv⟩
  left_inv h := by
    ext
    simp
  right_inv h := by
    ext
    simp
def deletedConvolutionMulMatrixOnNonidentity (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k => q (h.val * k.val) - q h.val
def deletedConvolutionMulMatrixAtReindexed (h₀ : G) (q : G → ℂ) :
    Matrix (Nonidentity G) (Nonidentity G) ℂ :=
  Matrix.of fun h k => q (h₀ * h.val * k.val) - q (h₀ * h.val)
omit [Fintype G] in
theorem deletedConvolutionMulMatrixAtReindexed_eq_translated
    (h₀ : G) (q : G → ℂ) :
    deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q =
      deletedConvolutionMulMatrixOnNonidentity (G := G) (fun h => q (h₀ * h)) := by
  ext h k
  simp [deletedConvolutionMulMatrixAtReindexed, deletedConvolutionMulMatrixOnNonidentity,
    mul_assoc]
omit [Fintype G] in
theorem deletedConvolutionMulMatrix_eq_invRow_submatrix (q : G → ℂ) :
    deletedConvolutionMulMatrixOnNonidentity (G := G) q =
      (deletedConvolutionMatrixOnNonidentity (G := G) (fun x => q x⁻¹)).submatrix
        (nonidentityInvEquiv (G := G)) id := by
  ext h k
  simp [deletedConvolutionMulMatrixOnNonidentity, deletedConvolutionMatrixOnNonidentity,
    nonidentityInvEquiv, mul_comm]
def deletedFourierCoeffMul (q : G → ℂ) (χ : MulChar G ℂ) : ℂ :=
  ∑ h : G, χ h * q h
omit [Fintype G] in
theorem prod_mulChar_apply_sq_eq_one
    [Fintype (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : MulChar G ℂ, χ h₀) ^ 2 = 1 := by
  classical
  set P : ℂ := ∏ χ : MulChar G ℂ, χ h₀
  have hP_inv : P = P⁻¹ := by
    calc
      P = ∏ χ : MulChar G ℂ, χ h₀ := rfl
      _ = ∏ χ : MulChar G ℂ, (χ⁻¹) h₀ := by
        rw [← Equiv.prod_comp (Equiv.inv (MulChar G ℂ)) (fun χ => χ h₀)]
        rfl
      _ = ∏ χ : MulChar G ℂ, (χ h₀)⁻¹ := by
        refine Finset.prod_congr rfl ?_
        intro χ _
        rw [MulChar.inv_apply_eq_inv']
      _ = P⁻¹ := by
        rw [Finset.prod_inv_distrib]
  have hP_ne : P ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro χ _
    exact (IsUnit.map χ.toMonoidHom (Group.isUnit h₀)).ne_zero
  calc
    P ^ 2 = P * P := by ring
    _ = P * P⁻¹ := congrArg (fun z => P * z) hP_inv
    _ = 1 := mul_inv_cancel₀ hP_ne
omit [Fintype G] in
theorem prod_nontriv_mulChar_apply_sq_eq_one
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : NontrivChar G, χ.val h₀) ^ 2 = 1 := by
  classical
  have herase :
      (∏ χ : NontrivChar G, χ.val h₀) =
        ∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1, χ h₀ := by
    rw [Finset.prod_subtype
      (p := fun χ : MulChar G ℂ => χ ≠ 1)
      (s := (Finset.univ : Finset (MulChar G ℂ)).erase 1)
      (f := fun χ => χ h₀)]
    intro χ
    simp [Finset.mem_erase]
  rw [herase]
  have hfull := prod_mulChar_apply_sq_eq_one (G := G) h₀
  have htriv : (1 : MulChar G ℂ) h₀ = 1 :=
    MulChar.one_apply (Group.isUnit h₀)
  have herase_full :
      (∏ χ ∈ (Finset.univ : Finset (MulChar G ℂ)).erase 1, χ h₀) =
        ∏ χ : MulChar G ℂ, χ h₀ :=
    Finset.prod_erase (s := (Finset.univ : Finset (MulChar G ℂ)))
      (f := fun χ => χ h₀) (a := 1) htriv
  rw [herase_full]
  exact hfull
omit [Fintype G] in
theorem prod_nontriv_mulChar_apply_inv_sq_eq_one
    [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)] (h₀ : G) :
    (∏ χ : NontrivChar G, (χ.val h₀)⁻¹) ^ 2 = 1 := by
  classical
  rw [show (∏ χ : NontrivChar G, (χ.val h₀)⁻¹) =
      (∏ χ : NontrivChar G, χ.val h₀)⁻¹ from by
    rw [Finset.prod_inv_distrib]]
  rw [inv_pow, prod_nontriv_mulChar_apply_sq_eq_one (G := G) h₀, inv_one]
theorem deletedFourierCoeffMul_mulLeft
    (q : G → ℂ) (χ : MulChar G ℂ) (h₀ : G) :
    deletedFourierCoeffMul (G := G) (fun h => q (h₀ * h)) χ =
      (χ h₀)⁻¹ * deletedFourierCoeffMul (G := G) q χ := by
  classical
  unfold deletedFourierCoeffMul
  have hsum := Equiv.sum_comp (Equiv.mulLeft h₀)
    (fun h : G => χ (h₀⁻¹ * h) * q h)
  have hleft :
      (∑ x : G, χ (h₀⁻¹ * (Equiv.mulLeft h₀) x) *
          q ((Equiv.mulLeft h₀) x)) =
        ∑ x : G, χ x * q (h₀ * x) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp
  rw [hleft] at hsum
  rw [hsum]
  have hterm : ∀ h : G, χ (h₀⁻¹ * h) * q h =
      (χ h₀)⁻¹ * (χ h * q h) := by
    intro h
    rw [map_mul, map_inv]
    ring
  rw [Finset.sum_congr rfl (fun h _ => hterm h)]
  rw [← Finset.mul_sum]
theorem deletedFourierCoeff_invArg_eq_mul
    (q : G → ℂ) (χ : MulChar G ℂ) :
    deletedFourierCoeff (G := G) (fun x => q x⁻¹) χ =
      deletedFourierCoeffMul (G := G) q χ := by
  classical
  unfold deletedFourierCoeff deletedFourierCoeffMul
  have hsum := Equiv.sum_comp (Equiv.inv G)
    (fun h : G => q h * (χ h⁻¹)⁻¹)
  have hleft :
      (∑ x : G, q ((Equiv.inv G) x) * (χ ((Equiv.inv G) x)⁻¹)⁻¹) =
        ∑ x : G, q x⁻¹ * (χ x)⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro x _
    simp
  rw [hleft] at hsum
  rw [hsum]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [map_inv]
  rw [inv_inv]
  ring
theorem det_deletedConvolutionMulMatrixOnNonidentity_sq_eq_prod_deletedFourierCoeffMul_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixOnNonidentity (G := G) q).det ^ 2 =
      (∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [deletedConvolutionMulMatrix_eq_invRow_submatrix]
  rw [Matrix.det_permute]
  rw [mul_pow]
  rw [show ((↑↑(Equiv.Perm.sign (nonidentityInvEquiv (G := G))) : ℂ)) ^ 2 = 1 from ?_]
  · rw [one_mul]
    rw [det_deletedConvolutionMatrixOnNonidentity_eq_prod_deletedFourierCoeff
      (G := G) ρ (fun x => q x⁻¹)]
    congr 1
    refine Finset.prod_congr rfl ?_
    intro χ _
    exact deletedFourierCoeff_invArg_eq_mul (G := G) q χ.val
  · have h_sign : (Equiv.Perm.sign (nonidentityInvEquiv (G := G))) ^ 2 = 1 :=
      Int.units_pow_two _
    have h_cast : (((Equiv.Perm.sign (nonidentityInvEquiv (G := G))) ^ 2 : ℤˣ) : ℂ) =
        ((1 : ℤˣ) : ℂ) := by
      rw [h_sign]
    push_cast at h_cast ⊢
    exact_mod_cast h_cast
theorem det_deletedConvolutionMulMatrixAtReindexed_sq_eq_charFactor_mul_prod_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (h₀ : G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q).det ^ 2 =
      ((∏ χ : NontrivChar G, (χ.val h₀)⁻¹) *
        ∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [deletedConvolutionMulMatrixAtReindexed_eq_translated]
  rw [det_deletedConvolutionMulMatrixOnNonidentity_sq_eq_prod_deletedFourierCoeffMul_sq
    (G := G) ρ (fun h => q (h₀ * h))]
  congr 1
  simp_rw [deletedFourierCoeffMul_mulLeft (G := G) q]
  rw [Finset.prod_mul_distrib]
theorem det_deletedConvolutionMulMatrixAtReindexed_sq_eq_prod_deletedFourierCoeffMul_sq
    [DecidableEq G] [Fintype (MulChar G ℂ)] [DecidableEq (MulChar G ℂ)]
    (ρ : NontrivChar G ≃ Nonidentity G) (h₀ : G) (q : G → ℂ) :
    (deletedConvolutionMulMatrixAtReindexed (G := G) h₀ q).det ^ 2 =
      (∏ χ : NontrivChar G, deletedFourierCoeffMul (G := G) q χ.val) ^ 2 := by
  classical
  rw [det_deletedConvolutionMulMatrixAtReindexed_sq_eq_charFactor_mul_prod_sq
    (G := G) ρ h₀ q]
  rw [mul_pow, prod_nontriv_mulChar_apply_inv_sq_eq_one (G := G) h₀, one_mul]
end FiniteGroup
end CyclotomicUnits
end KummerCriterion
end
end Module1

-- Source: KummerCriterion.PrimitiveRootUnits
section Module2
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
end Module2

-- Source: KummerCriterion.UnitQuotient.DeltaAction
section Module3
noncomputable section
namespace KummerCriterion
variable (p N : ℕ) [Fact p.Prime]
abbrev CyclotomicUnitDelta : Type :=
  (ZMod p)ˣ
end KummerCriterion
noncomputable section
open NumberField IsCyclotomicExtension
open scoped NumberField
namespace KummerCriterion
variable (p N : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable abbrev cyclotomicZetaInteger : 𝓞 K :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
theorem cyclotomicZetaInteger_isPrimitiveRoot :
    IsPrimitiveRoot (cyclotomicZetaInteger (p := p) K) p := by
  simpa [cyclotomicZetaInteger] using
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot
end KummerCriterion
end
end
end Module3

-- Source: KummerCriterion.UnitQuotient.PermutationCharacters
section Module4
noncomputable section
namespace KummerCriterion
open Finset MonoidAlgebra
local instance (α : Type*) [Finite α] : Fintype α := Fintype.ofFinite α
variable (p : ℕ) [Fact p.Prime]
abbrev CyclotomicEvenDeltaSubgroup : Subgroup (CyclotomicUnitDelta p) :=
  Subgroup.zpowers (-1 : CyclotomicUnitDelta p)
abbrev CyclotomicEvenDelta : Type :=
  CyclotomicUnitDelta p ⧸ CyclotomicEvenDeltaSubgroup p
def cyclotomicEvenDeltaQuotient : CyclotomicUnitDelta p →* CyclotomicEvenDelta p :=
  QuotientGroup.mk' (CyclotomicEvenDeltaSubgroup p)
@[simp]
theorem cyclotomicEvenDeltaQuotient_apply (a : CyclotomicUnitDelta p) :
    cyclotomicEvenDeltaQuotient p a = QuotientGroup.mk a :=
  rfl
@[simp]
theorem cyclotomicEvenDeltaQuotient_neg_one :
    cyclotomicEvenDeltaQuotient p (-1 : CyclotomicUnitDelta p) = 1 :=
  (QuotientGroup.eq_one_iff (-1 : CyclotomicUnitDelta p)).2 (Subgroup.mem_zpowers _)
@[simp]
theorem cyclotomicEvenDeltaQuotient_neg (a : CyclotomicUnitDelta p) :
    cyclotomicEvenDeltaQuotient p (-a) = cyclotomicEvenDeltaQuotient p a := by
  have h : -a = (-1 : CyclotomicUnitDelta p) * a := (neg_one_mul a).symm
  rw [h, map_mul, cyclotomicEvenDeltaQuotient_neg_one, one_mul]
def evenFunctionDescend {R : Type*} (f : CyclotomicUnitDelta p → R)
    (hf_even : ∀ a : CyclotomicUnitDelta p, f (-a) = f a) :
    CyclotomicEvenDelta p → R :=
  fun q => q.liftOn f (fun a b hab => by
    have hab' : a⁻¹ * b ∈ CyclotomicEvenDeltaSubgroup p :=
      QuotientGroup.leftRel_apply.mp hab
    rw [CyclotomicEvenDeltaSubgroup, Subgroup.mem_zpowers_iff] at hab'
    obtain ⟨k, hk⟩ := hab'
    have h_b : b = a * ((-1 : CyclotomicUnitDelta p) ^ k) := by
      rw [hk]; group
    have h_sq : ((-1 : CyclotomicUnitDelta p) ^ (2 : ℕ)) = 1 := by
      rw [sq, neg_one_mul, neg_neg]
    rw [zpow_eq_zpow_emod' k h_sq] at h_b
    have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
    rcases h_mod with h0 | h1
    · rw [h0, zpow_zero, mul_one] at h_b
      rw [h_b]
    · rw [h1, zpow_one] at h_b
      rw [h_b, mul_neg_one, hf_even])
@[simp]
theorem evenFunctionDescend_apply_mk {R : Type*} (f : CyclotomicUnitDelta p → R)
    (hf_even : ∀ a : CyclotomicUnitDelta p, f (-a) = f a)
    (a : CyclotomicUnitDelta p) :
    evenFunctionDescend (p := p) f hf_even
        ((QuotientGroup.mk a) : CyclotomicEvenDelta p) = f a := by
  rfl
def evenDeltaCharacterPullback {R : Type*} [CommMonoidWithZero R]
    (χ : MulChar (CyclotomicEvenDelta p) R) :
    MulChar (CyclotomicUnitDelta p) R where
  toFun a := χ (cyclotomicEvenDeltaQuotient p a)
  map_one' := by simp [cyclotomicEvenDeltaQuotient]
  map_mul' a b := by simp [cyclotomicEvenDeltaQuotient, map_mul]
  map_nonunit' a ha := (ha (Group.isUnit a)).elim
end KummerCriterion
end
end Module4

-- Source: KummerCriterion.GaussSum.Basic
section Module5
noncomputable section
namespace KummerCriterion
open scoped BigOperators ComplexConjugate
section GaussSum
variable (p : ℕ) [hp : Fact p.Prime]
theorem DirichletCharacter.isPrimitive_of_ne_one
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) : χ.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  rcases (Nat.dvd_prime hp.out).mp χ.conductor_dvd_level with h | h
  · exact absurd ((DirichletCharacter.factorsThrough_one_iff χ).mp
      (h ▸ χ.factorsThrough_conductor)) hχ
  · exact h
end GaussSum
end KummerCriterion
end
end Module5

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part1
section Module6
noncomputable section
namespace KummerCriterion
open Finset
local instance (α : Type*) [Finite α] : Fintype α := Fintype.ofFinite α
variable (p : ℕ) [Fact p.Prime]
theorem cyclotomicEvenDeltaSubgroup_card (hp_gt_two : 2 < p) :
    Fintype.card (CyclotomicEvenDeltaSubgroup p) = 2 := by
  change Fintype.card (Subgroup.zpowers (-1 : CyclotomicUnitDelta p)) = 2
  rw [Fintype.card_zpowers]
  have hp_ne_two : p ≠ 2 := by omega
  rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod p) p,
    if_neg hp_ne_two]
theorem cyclotomicEvenDelta_card (hp_gt_two : 2 < p) :
    Fintype.card (CyclotomicEvenDelta p) = (p - 1) / 2 := by
  have hcard :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CyclotomicEvenDeltaSubgroup p)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    show Fintype.card (CyclotomicUnitDelta p) = p - 1 by rw [ZMod.card_units],
    cyclotomicEvenDeltaSubgroup_card (p := p) hp_gt_two] at hcard
  exact Nat.eq_div_of_mul_eq_right (by decide)
    (by linarith : 2 * Fintype.card (CyclotomicEvenDelta p) = p - 1)
end KummerCriterion
end
noncomputable section
open Real Complex
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
def DirichletLogSum (χ : DirichletCharacter ℂ p) : ℂ :=
  -∑ a ∈ Finset.Ico 1 p,
    χ a * Real.log (2 * |Real.sin (Real.pi * a / p)|)
theorem norm_one_sub_stdAddChar_neg (a : ZMod p) :
    ‖(1 : ℂ) - ZMod.stdAddChar (N := p) (-a)‖ = ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ := by
  rw [AddChar.map_neg_eq_conj]
  rw [show (1 : ℂ) - (starRingEnd ℂ) (ZMod.stdAddChar (N := p) a) =
        (starRingEnd ℂ) (1 - ZMod.stdAddChar (N := p) a) from by
    rw [map_sub]; simp]
  exact Complex.norm_conj _
theorem log_norm_one_sub_stdAddChar_unit_neg (a : (ZMod p)ˣ) :
    Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((↑(-a) : ZMod p))‖ =
      Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((↑a : ZMod p))‖ := by
  have h_cast : ((-a : (ZMod p)ˣ) : ZMod p) = -((a : (ZMod p)ˣ) : ZMod p) := by
    push_cast; rfl
  rw [h_cast, norm_one_sub_stdAddChar_neg]
noncomputable def convolutionLogNormDescended :
    KummerCriterion.CyclotomicEvenDelta p → ℂ :=
  KummerCriterion.evenFunctionDescend (p := p)
    (fun a : KummerCriterion.CyclotomicUnitDelta p =>
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ))
    (fun a => by
      have h := log_norm_one_sub_stdAddChar_unit_neg (p := p) a
      exact_mod_cast h)
noncomputable def convolutionMatrixLogNormEven :
    Matrix (KummerCriterion.CyclotomicEvenDelta p)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun a b => convolutionLogNormDescended p (a * b)
noncomputable def convolutionMatrixOnEven
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ) :
    Matrix (KummerCriterion.CyclotomicEvenDelta p)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun a b => f (a * b)
theorem convolutionMatrixLogNormEven_eq_convolutionMatrixOnEven :
    convolutionMatrixLogNormEven p =
      convolutionMatrixOnEven p (convolutionLogNormDescended p) := by
  rfl
noncomputable def characterMatrixOnEven :
    Matrix (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun ξ a => ξ a
theorem nat_card_mulChar_cyclotomicEvenDelta_eq :
    Nat.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      Nat.card (KummerCriterion.CyclotomicEvenDelta p) := by
  rw [MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity]
  exact Nat.card_congr toUnits.symm.toEquiv
noncomputable def quotCharEquivQuot :
    MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ ≃
      KummerCriterion.CyclotomicEvenDelta p := by
  classical
  haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  refine Fintype.equivOfCardEq ?_
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
  exact nat_card_mulChar_cyclotomicEvenDelta_eq p
theorem characterMatrixOnEven_mul_convolutionMatrixOnEven_apply
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ)
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)
    (b : KummerCriterion.CyclotomicEvenDelta p) :
    (characterMatrixOnEven p * convolutionMatrixOnEven p f) ξ b =
      ξ (b⁻¹) * ∑ a : KummerCriterion.CyclotomicEvenDelta p, ξ a * f a := by
  classical
  simp only [Matrix.mul_apply, characterMatrixOnEven, convolutionMatrixOnEven,
    Matrix.of_apply]
  have h_reindex : ∑ a : KummerCriterion.CyclotomicEvenDelta p, ξ a * f (a * b) =
      ∑ a : KummerCriterion.CyclotomicEvenDelta p, ξ (a * b⁻¹) * f a := by
    apply (Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ _).symm
    intro a
    rw [Equiv.coe_mulRight]
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [h_reindex]
  have h_factor : ∀ a : KummerCriterion.CyclotomicEvenDelta p,
      ξ (a * b⁻¹) * f a = ξ b⁻¹ * (ξ a * f a) := by
    intro a
    rw [map_mul]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h_factor a)]
  rw [← Finset.mul_sum]
noncomputable def characterMatrixSquareOnEven :
    Matrix (KummerCriterion.CyclotomicEvenDelta p)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun k a => ((quotCharEquivQuot p).symm k) a
noncomputable def inverseCharacterMatrixSquareOnEven :
    Matrix (KummerCriterion.CyclotomicEvenDelta p)
           (KummerCriterion.CyclotomicEvenDelta p) ℂ :=
  Matrix.of fun k b => ((quotCharEquivQuot p).symm k) b⁻¹
theorem characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_apply
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ)
    (k b : KummerCriterion.CyclotomicEvenDelta p) :
    (characterMatrixSquareOnEven p * convolutionMatrixOnEven p f) k b =
      ((quotCharEquivQuot p).symm k) b⁻¹ *
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a := by
  simp only [characterMatrixSquareOnEven]
  exact characterMatrixOnEven_mul_convolutionMatrixOnEven_apply
    (p := p) f ((quotCharEquivQuot p).symm k) b
theorem characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_eq_diag_mul_inv
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ) :
    characterMatrixSquareOnEven p * convolutionMatrixOnEven p f =
      Matrix.diagonal (fun k : KummerCriterion.CyclotomicEvenDelta p =>
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      inverseCharacterMatrixSquareOnEven p := by
  classical
  ext k b
  rw [characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_apply]
  rw [Matrix.mul_apply]
  have h_rhs : ∑ j : KummerCriterion.CyclotomicEvenDelta p,
      Matrix.diagonal (fun k' : KummerCriterion.CyclotomicEvenDelta p =>
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k') a * f a) k j *
        inverseCharacterMatrixSquareOnEven p j b =
      (∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
        ((quotCharEquivQuot p).symm k) b⁻¹ := by
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq]; rfl
    · intro j _ hj
      rw [Matrix.diagonal_apply_ne _ hj.symm, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [h_rhs]; ring
theorem det_characterMatrixSquareOnEven_mul_convolutionMatrixOnEven
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ) :
    (characterMatrixSquareOnEven p).det * (convolutionMatrixOnEven p f).det =
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      (inverseCharacterMatrixSquareOnEven p).det := by
  classical
  rw [← Matrix.det_mul,
    characterMatrixSquareOnEven_mul_convolutionMatrixOnEven_eq_diag_mul_inv,
    Matrix.det_mul, Matrix.det_diagonal]
theorem inverseCharacterMatrixSquareOnEven_eq_submatrix :
    inverseCharacterMatrixSquareOnEven p =
      (characterMatrixSquareOnEven p).submatrix id
        (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p)) := by
  ext k b
  simp only [inverseCharacterMatrixSquareOnEven, characterMatrixSquareOnEven,
    Matrix.submatrix_apply, Matrix.of_apply, id_def, Equiv.inv_apply]
theorem det_inverseCharacterMatrixSquareOnEven_sq_eq_det_characterMatrixSquareOnEven_sq :
    (inverseCharacterMatrixSquareOnEven p).det ^ 2 =
      (characterMatrixSquareOnEven p).det ^ 2 := by
  rw [inverseCharacterMatrixSquareOnEven_eq_submatrix]
  rw [Matrix.det_permute' (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p))
      (characterMatrixSquareOnEven p)]
  rw [mul_pow]
  rw [show ((↑↑(Equiv.Perm.sign
      (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p))) : ℂ)) ^ 2 = 1 from ?_]
  · ring
  · have h_sign : (Equiv.Perm.sign
        (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p))) ^ 2 = 1 :=
      Int.units_pow_two _
    have h_cast : (((Equiv.Perm.sign
        (Equiv.inv (KummerCriterion.CyclotomicEvenDelta p))) ^ 2 : ℤˣ) : ℂ) =
        ((1 : ℤˣ) : ℂ) := by
      rw [h_sign]
    push_cast at h_cast ⊢
    exact_mod_cast h_cast
theorem det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ)
    (h_det_F_ne : (characterMatrixSquareOnEven p).det ≠ 0) :
    (convolutionMatrixOnEven p f).det ^ 2 =
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) ^ 2 := by
  have h_det := det_characterMatrixSquareOnEven_mul_convolutionMatrixOnEven (p := p) f
  have h_det_sq : ((characterMatrixSquareOnEven p).det *
      (convolutionMatrixOnEven p f).det) ^ 2 =
      ((∏ k : KummerCriterion.CyclotomicEvenDelta p,
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) *
      (inverseCharacterMatrixSquareOnEven p).det) ^ 2 := by
    rw [h_det]
  rw [mul_pow, mul_pow] at h_det_sq
  rw [det_inverseCharacterMatrixSquareOnEven_sq_eq_det_characterMatrixSquareOnEven_sq]
    at h_det_sq
  have h_det_F_sq_ne : (characterMatrixSquareOnEven p).det ^ 2 ≠ 0 :=
    pow_ne_zero _ h_det_F_ne
  have h_mul_cancel : (characterMatrixSquareOnEven p).det ^ 2 *
      (convolutionMatrixOnEven p f).det ^ 2 =
      (characterMatrixSquareOnEven p).det ^ 2 *
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
          ∑ a : KummerCriterion.CyclotomicEvenDelta p,
            ((quotCharEquivQuot p).symm k) a * f a) ^ 2 := by
    linear_combination h_det_sq
  exact (mul_left_cancel₀ h_det_F_sq_ne h_mul_cancel)
theorem characterMatrixSquareOnEven_mul_inverseCharacterMatrixSquareOnEven_transpose :
    characterMatrixSquareOnEven p *
        Matrix.transpose (inverseCharacterMatrixSquareOnEven p) =
      ((Fintype.card (KummerCriterion.CyclotomicEvenDelta p) : ℕ) : ℂ) •
        (1 : Matrix (KummerCriterion.CyclotomicEvenDelta p)
                    (KummerCriterion.CyclotomicEvenDelta p) ℂ) := by
  classical
  ext k k'
  simp only [characterMatrixSquareOnEven, inverseCharacterMatrixSquareOnEven,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have h_inv : ∀ a : KummerCriterion.CyclotomicEvenDelta p,
      ((quotCharEquivQuot p).symm k) a *
          ((quotCharEquivQuot p).symm k') a⁻¹ =
        (((quotCharEquivQuot p).symm k) *
          ((quotCharEquivQuot p).symm k')⁻¹) a := by
    intro a
    rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv']
    rw [map_inv]
  rw [Finset.sum_congr rfl (fun a _ => h_inv a)]
  by_cases hkk : k = k'
  · subst hkk
    rw [if_pos rfl, mul_one]
    rw [show ((quotCharEquivQuot p).symm k) *
        ((quotCharEquivQuot p).symm k)⁻¹ =
        (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) from mul_inv_cancel _]
    have h_one := MulChar.sum_one_eq_card_units
      (R := KummerCriterion.CyclotomicEvenDelta p) (R' := ℂ)
    rw [h_one]
    have h_card : Fintype.card (KummerCriterion.CyclotomicEvenDelta p)ˣ =
        Fintype.card (KummerCriterion.CyclotomicEvenDelta p) :=
      Fintype.card_congr toUnits.symm.toEquiv
    rw [h_card]
  · rw [if_neg hkk, mul_zero]
    have h_ne : ((quotCharEquivQuot p).symm k) *
        ((quotCharEquivQuot p).symm k')⁻¹ ≠
        (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := by
      intro h_eq
      apply hkk
      have h_inv_cancel : ((quotCharEquivQuot p).symm k) =
          ((quotCharEquivQuot p).symm k') := by
        have := congrArg (· * ((quotCharEquivQuot p).symm k')) h_eq
        rw [mul_assoc, inv_mul_cancel, mul_one, one_mul] at this
        exact this
      exact (quotCharEquivQuot p).symm.injective h_inv_cancel
    exact MulChar.sum_eq_zero_of_ne_one h_ne
theorem det_characterMatrixSquareOnEven_ne_zero (hp_two : 2 < p) :
    (characterMatrixSquareOnEven p).det ≠ 0 := by
  classical
  intro h_det_zero
  have h_orth :=
    characterMatrixSquareOnEven_mul_inverseCharacterMatrixSquareOnEven_transpose
      (p := p)
  have h_det_orth := congrArg Matrix.det h_orth
  rw [Matrix.det_mul, h_det_zero, zero_mul] at h_det_orth
  rw [Matrix.det_smul, Matrix.det_one, mul_one] at h_det_orth
  have h_card_pos : 0 < Fintype.card (KummerCriterion.CyclotomicEvenDelta p) := by
    rw [KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two]
    omega
  have h_card_ne : ((Fintype.card (KummerCriterion.CyclotomicEvenDelta p) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr h_card_pos.ne'
  have h_pow_ne : ((Fintype.card (KummerCriterion.CyclotomicEvenDelta p) : ℕ) : ℂ) ^
      Fintype.card (KummerCriterion.CyclotomicEvenDelta p) ≠ 0 := pow_ne_zero _ h_card_ne
  exact h_pow_ne h_det_orth.symm
theorem det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq_unconditional
    (f : KummerCriterion.CyclotomicEvenDelta p → ℂ) (hp_two : 2 < p) :
    (convolutionMatrixOnEven p f).det ^ 2 =
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
        ∑ a : KummerCriterion.CyclotomicEvenDelta p,
          ((quotCharEquivQuot p).symm k) a * f a) ^ 2 :=
  det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq (p := p) f
    (det_characterMatrixSquareOnEven_ne_zero (p := p) hp_two)
noncomputable def quotientEigenvalue
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) : ℂ :=
  ∑ ā : KummerCriterion.CyclotomicEvenDelta p,
    ξ ā * convolutionLogNormDescended p ā
theorem prod_lambda_eq_prod_quotientEigenvalue :
    (∏ k : KummerCriterion.CyclotomicEvenDelta p,
      ∑ a : KummerCriterion.CyclotomicEvenDelta p,
        ((quotCharEquivQuot p).symm k) a * convolutionLogNormDescended p a) =
    ∏ k : KummerCriterion.CyclotomicEvenDelta p,
      quotientEigenvalue p ((quotCharEquivQuot p).symm k) := by
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rfl
theorem det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq
    (hp_two : 2 < p) :
    (convolutionMatrixLogNormEven p).det ^ 2 =
      (∏ k : KummerCriterion.CyclotomicEvenDelta p,
        quotientEigenvalue p ((quotCharEquivQuot p).symm k)) ^ 2 := by
  rw [convolutionMatrixLogNormEven_eq_convolutionMatrixOnEven]
  rw [det_convolutionMatrixOnEven_sq_eq_prod_lambda_sq_unconditional p _ hp_two]
  rw [prod_lambda_eq_prod_quotientEigenvalue]
theorem prod_quot_eq_prod_mulChar
    (f : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ → ℂ) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    ∏ k : KummerCriterion.CyclotomicEvenDelta p,
        f ((quotCharEquivQuot p).symm k) =
      ∏ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ, f ξ := by
  classical
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  let : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  exact (Fintype.prod_equiv (quotCharEquivQuot p)
    (fun ξ => f ξ)
    (fun k => f ((quotCharEquivQuot p).symm k))
    (fun ξ => by simp only [Equiv.symm_apply_apply])).symm
theorem sum_full_eq_two_mul_sum_descended (f : KummerCriterion.CyclotomicUnitDelta p → ℂ)
    (hf_even : ∀ a, f (-a) = f a) (hp_two : 2 < p) :
    ∑ a : KummerCriterion.CyclotomicUnitDelta p, f a =
      2 * ∑ b : KummerCriterion.CyclotomicEvenDelta p,
            KummerCriterion.evenFunctionDescend (p := p) f hf_even b := by
  classical
  have h_step1 : ∀ a, f a =
      KummerCriterion.evenFunctionDescend (p := p) f hf_even
        (KummerCriterion.cyclotomicEvenDeltaQuotient p a) := by
    intro a
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply,
        KummerCriterion.evenFunctionDescend_apply_mk]
  simp_rw [h_step1]
  rw [Finset.sum_comp _ (KummerCriterion.cyclotomicEvenDeltaQuotient p)]
  have h_image : Finset.image (KummerCriterion.cyclotomicEvenDeltaQuotient p)
        (Finset.univ : Finset (KummerCriterion.CyclotomicUnitDelta p)) =
      Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro b
    rw [Finset.mem_image]
    refine ⟨Quotient.out b, Finset.mem_univ _, ?_⟩
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply]
    exact Quotient.out_eq b
  rw [h_image]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have h_card : ({a ∈ (Finset.univ : Finset (KummerCriterion.CyclotomicUnitDelta p)) |
      KummerCriterion.cyclotomicEvenDeltaQuotient p a = b}).card = 2 := by
    have h_equiv := QuotientGroup.preimageMkEquivSubgroupProdSet
      (KummerCriterion.CyclotomicEvenDeltaSubgroup p) ({b} : Set _)
    have h_card_eq :
        Fintype.card (QuotientGroup.mk ⁻¹' ({b} : Set _) :
            Set (KummerCriterion.CyclotomicUnitDelta p)) =
        Fintype.card (KummerCriterion.CyclotomicEvenDeltaSubgroup p) * 1 := by
      rw [Fintype.card_congr h_equiv, Fintype.card_prod]
      simp
    rw [KummerCriterion.cyclotomicEvenDeltaSubgroup_card (p := p) hp_two] at h_card_eq
    rw [show ({a ∈ Finset.univ | KummerCriterion.cyclotomicEvenDeltaQuotient p a = b} :
        Finset _).card =
        Fintype.card (QuotientGroup.mk ⁻¹' ({b} : Set _) :
            Set (KummerCriterion.CyclotomicUnitDelta p)) from ?_]
    · omega
    · rw [Fintype.card_ofFinset]
      congr 1
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_preimage,
        Set.mem_singleton_iff]
      rfl
  rw [h_card]
  ring
theorem two_mul_quotientEigenvalue_eq_sum_full
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) (hp_two : 2 < p) :
    2 * quotientEigenvalue p ξ =
      ∑ a : KummerCriterion.CyclotomicUnitDelta p,
        KummerCriterion.evenDeltaCharacterPullback (p := p) ξ a *
          ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  set f : KummerCriterion.CyclotomicUnitDelta p → ℂ := fun a =>
    KummerCriterion.evenDeltaCharacterPullback (p := p) ξ a *
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) with hf_def
  have hf_even : ∀ a : KummerCriterion.CyclotomicUnitDelta p, f (-a) = f a := by
    intro a
    simp only [hf_def]
    rw [log_norm_one_sub_stdAddChar_unit_neg (p := p) a]
    congr 1
    change ξ (KummerCriterion.cyclotomicEvenDeltaQuotient p (-a)) =
        ξ (KummerCriterion.cyclotomicEvenDeltaQuotient p a)
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_neg]
  have h_half := sum_full_eq_two_mul_sum_descended (p := p) f hf_even hp_two
  have h_quot_eq : quotientEigenvalue p ξ =
      ∑ b : KummerCriterion.CyclotomicEvenDelta p,
        KummerCriterion.evenFunctionDescend (p := p) f hf_even b := by
    unfold quotientEigenvalue
    refine Finset.sum_congr rfl (fun b _ => ?_)
    obtain ⟨a, rfl⟩ : ∃ a : KummerCriterion.CyclotomicUnitDelta p,
        KummerCriterion.cyclotomicEvenDeltaQuotient p a = b :=
      ⟨Quotient.out b,
        by rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply]; exact Quotient.out_eq b⟩
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply]
    rw [KummerCriterion.evenFunctionDescend_apply_mk]
    simp only [hf_def]
    unfold convolutionLogNormDescended
    rw [KummerCriterion.evenFunctionDescend_apply_mk]
    rfl
  rw [h_quot_eq, ← h_half]
theorem sum_units_val_eq_sum_Ico (F : ℕ → ℂ) :
    ∑ a : (ZMod p)ˣ, F ((a : ZMod p).val) = ∑ n ∈ Finset.Ico 1 p, F n := by
  have hp_pos : 0 < p := hp.out.pos
  refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => (a : ZMod p).val)
    (fun a _ => ?_) (fun a _ b _ heq => ?_) (fun n hn => ?_) (fun _ _ => rfl)
  · rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt _⟩
    have h_ne : (a : ZMod p).val ≠ 0 := by
      intro h
      rw [ZMod.val_eq_zero] at h
      exact a.ne_zero h
    exact Nat.one_le_iff_ne_zero.mpr h_ne
  · apply Units.ext
    apply ZMod.val_injective _ heq
  · rw [Finset.mem_Ico] at hn
    refine ⟨ZMod.unitOfCoprime n
      (Nat.coprime_comm.mp (Nat.coprime_of_lt_prime (by omega) hn.2 hp.out)),
      Finset.mem_univ _, ?_⟩
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt hn.2
theorem two_mul_quotientEigenvalue_trivial_eq_sum_logNorm (hp_two : 2 < p) :
    2 * quotientEigenvalue p (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      ∑ a : KummerCriterion.CyclotomicUnitDelta p,
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  rw [two_mul_quotientEigenvalue_eq_sum_full p 1 hp_two]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h_unit : IsUnit
      (KummerCriterion.cyclotomicEvenDeltaQuotient p a) := Group.isUnit _
  change (1 : MulChar _ _) (KummerCriterion.cyclotomicEvenDeltaQuotient p a) *
      _ = _
  rw [MulChar.one_apply h_unit, one_mul]
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module6

-- Source: KummerCriterion.TotallyRealSubfield.ZetaPrime
section Module7
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
noncomputable def zetaPrimePlus [IsCMField K] : Ideal (𝓞 ((oMR K))) :=
  (zetaPrime p K).under (𝓞 ((oMR K)))
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
      rw [IsScalarTower.algebraMap_apply ℤ (𝓞 ((oMR K))) (𝓞 K), AlgEquiv.commutes]
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
noncomputable def piPlus [IsCMField K] : 𝓞 ((oMR K)) := by
  have hfix := complexConj_pi_mul_complexConj_pi p K
  rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj,
    RingOfIntegers.complexConj_eq_self_iff] at hfix
  exact hfix.choose
lemma algebraMap_piPlus [IsCMField K] :
    (algebraMap (𝓞 ((oMR K))) (𝓞 K)) (piPlus p K) =
      ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K) *
        ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1) := by
  have hfix := complexConj_pi_mul_complexConj_pi p K
  rw [RingOfIntegers.ext_iff, coe_ringOfIntegersComplexConj,
    RingOfIntegers.complexConj_eq_self_iff] at hfix
  ext
  rw [← hfix.choose_spec]; rfl
theorem map_span_piPlus_eq_zetaPrime_sq [IsCMField K] :
    (Ideal.span {piPlus p K}).map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) =
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
    (x : 𝓞 ((oMR K))) (hx : x ≠ 0) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)
                      (algebraMap (𝓞 ((oMR K))) (𝓞 K) x)) := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  set α := algebraMap (𝓞 ((oMR K))) (𝓞 K) x with hα_def
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
    (zetaPrimePlus p K).map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) = (zetaPrime p K) ^ 2 := by
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
        (algebraMap (𝓞 ((oMR K))) (𝓞 K) y) :=
      FiniteMultiplicity.of_prime_left (zeta_spec p ℚ K).zeta_sub_one_prime'
        ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hy0)
    have hge : 1 ≤ multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)
        (algebraMap (𝓞 ((oMR K))) (𝓞 K) y) :=
      hfin.pow_dvd_iff_le_multiplicity.mp (by rwa [pow_one])
    have h2le : 2 ≤ multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K)
        (algebraMap (𝓞 ((oMR K))) (𝓞 K) y) := by
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
end Module7

-- Source: KummerCriterion.TotallyRealSubfield.Conjugation
section Module8
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
    (I : Ideal (𝓞 (oMR K))) :
    (I.map (algebraMap (𝓞 (oMR K)) (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) := by
  rw [Ideal.map_map]
  congr
  ext x
  simp [RingHom.comp_apply, AlgEquiv.commutes]
theorem conj_generator_associated [IsCMField K]
    (a : 𝓞 K) (_ha : a ≠ 0) (I : Ideal (𝓞 (oMR K)))
    (hIa : I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) = Ideal.span {a})
    (hIca : I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) =
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
    (zetaPrime p K).ramificationIdx (𝓞 (oMR K)) = 2 := by
  have hmap0 : Ideal.map (algebraMap (𝓞 (oMR K)) (𝓞 K))
      (zetaPrimePlus p K) ≠ ⊥ := by
    rw [zetaPrimePlus_map_eq p hp_odd K]
    exact pow_ne_zero 2 (zetaPrime_ne_bot p K)
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (zetaPrimePlus p K) (zetaPrime p K)
    hmap0, zetaPrimePlus_map_eq p hp_odd K, multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (zetaPrime_ne_bot p K) (zetaPrime_isPrime p K))]
include hp_odd in
theorem multiplicity_zetaPrime_even_of_map_eq_span [IsCMField K]
    (I : Ideal (𝓞 (oMR K)))
    (a : 𝓞 K) (ha : a ≠ 0)
    (hIa :
      I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) = Ideal.span {a}) :
    Even (multiplicity ((zeta_spec p ℚ K).toInteger - 1 : 𝓞 K) a) := by
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  let f : 𝓞 (oMR K) →+* 𝓞 K :=
    algebraMap (𝓞 (oMR K)) (𝓞 K)
  let P : Ideal (𝓞 K) := zetaPrime p K
  let PPlus : Ideal (𝓞 (oMR K)) := zetaPrimePlus p K
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
        (R := 𝓞 (oMR K)) (S := 𝓞 K)
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
end Module8

-- Source: KummerCriterion.TotallyRealSubfield.FixedAssociate
section Module9
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
    (I : Ideal (𝓞 (oMR K)))
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (ha : a ≠ 0)
    (hIa : I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) = Ideal.span {a})
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
    (I : Ideal (𝓞 (oMR K)))
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (hIa : I.map (algebraMap (𝓞 (oMR K)) (𝓞 K)) = Ideal.span {a})
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
    b ∈ Set.range (algebraMap (𝓞 (oMR K)) (𝓞 K)) :=
  (ringOfIntegersComplexConj_eq_self_iff K b).mp hb
end CyclotomicSetup
end KummerCriterion
end
end Module9

-- Source: KummerCriterion.TotallyRealSubfield.ClassGroup
section Module10
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
    Module.finrank ((oMR K)) K = 2 :=
  IsQuadraticExtension.finrank_eq_two _ _
theorem finrank_Kplus_over_rat [IsCMField K] :
    Module.finrank ℚ ((oMR K)) = (p - 1) / 2 := by
  have h1 : Module.finrank ((oMR K)) K = 2 := finrank_K_over_Kplus K
  have h2 : Module.finrank ℚ K = p - 1 := by
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.1.pos),
        Nat.totient_prime hp.1]
  have htow := Module.finrank_mul_finrank ℚ ((oMR K)) K
  rw [h1, h2] at htow
  exact (Nat.div_eq_of_eq_mul_left (by omega) htow.symm).symm
noncomputable def h : ℕ := Fintype.card (ClassGroup (𝓞 K))
noncomputable def hPlus [IsCMField K] : ℕ := Fintype.card (ClassGroup (𝓞 ((oMR K))))
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
    (J : Ideal (𝓞 (oMR L))) :
    (J.map (algebraMap (𝓞 (oMR L)) (𝓞 L))).comap
        (algebraMap (𝓞 (oMR L)) (𝓞 L)) = J := by
  simpa using Ideal.comap_map_eq_self_of_faithfullyFlat J
theorem isPrincipal_of_map_eq_span_singleton_of_mem
    (I : Ideal (𝓞 ((oMR K))))
    (b₀ : 𝓞 ((oMR K)))
    (hb : I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) =
      Ideal.span {algebraMap (𝓞 ((oMR K))) (𝓞 K) b₀}) :
    I.IsPrincipal := by
  refine ⟨b₀, ?_⟩
  let f : 𝓞 ((oMR K)) →+* 𝓞 K := algebraMap (𝓞 ((oMR K))) (𝓞 K)
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
    (I : Ideal (𝓞 ((oMR K))))
    (hI : (I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal := by
  obtain ⟨a, ha⟩ := hI
  by_cases hzero : a = 0
  · have : I = ⊥ := by
      rw [← Ideal.map_eq_bot_iff_of_injective
        (FaithfulSMul.algebraMap_injective (𝓞 ((oMR K))) (𝓞 K)), ha, hzero]
      simp
    exact this ▸ bot_isPrincipal
  have hIa : I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) = Ideal.span {a} := ha
  have hIcon := ideal_map_conj_eq (K := K) I
  have hIca : I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) =
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
  have hspan : I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) = Ideal.span {b} := by
    rw [hIa, ← hb_span]
  rw [← hb₀] at hspan
  exact isPrincipal_of_map_eq_span_singleton_of_mem K I b₀ hspan
include hp_odd in
theorem isPrincipal_of_isPrincipal_map_Kplus [IsCMField K]
    (I : Ideal (𝓞 ((oMR K))))
    (hI : (I.map (algebraMap (𝓞 ((oMR K))) (𝓞 K))).IsPrincipal) :
    I.IsPrincipal :=
  isPrincipal_of_isPrincipal_map_Kplus' (p := p) (hp_odd := hp_odd) (K := K) I hI
abbrev classGroupMap [IsCMField K] :
    ClassGroup (𝓞 ((oMR K))) →* ClassGroup (𝓞 K) :=
  ClassGroup.extendedHom (𝓞 ((oMR K))) (𝓞 K)
include hp_odd in
theorem classGroupMap_injective [IsCMField K] :
    Function.Injective (classGroupMap K) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
  rw [ClassGroup.mk0_eq_one_iff I.2]
  refine isPrincipal_of_isPrincipal_map_Kplus (p := p) (hp_odd := hp_odd) (K := K) I.1 ?_
  have hne : I.1.map (algebraMap (𝓞 ((oMR K))) (𝓞 K)) ≠ ⊥ :=
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
end CyclotomicSetup
end KummerCriterion
end
end Module10

-- Source: KummerCriterion.ZetaFactorisation.Basic
section Module11
noncomputable section
open NumberField
open Polynomial
open scoped Topology nonZeroDivisors
namespace KummerCriterion
section ZetaFactorisation
noncomputable instance instFintypeSym (α : Type*) [Finite α] (n : ℕ) :
    Fintype (Sym α n) :=
  Fintype.ofFinite (Sym α n)
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
lemma card_dirichletCharacter_complex : Nat.card (DirichletCharacter ℂ p) = p - 1 := by
  rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp.1]
noncomputable def rationalPrimeIdeal (ℓ : ℕ) : Ideal ℤ :=
  Ideal.span ({(ℓ : ℤ)} : Set ℤ)
noncomputable def primesOverFinset (ℓ : ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (rationalPrimeIdeal ℓ) (𝓞 K)
noncomputable def evenNontrivialCharacters : Finset (DirichletCharacter ℂ p) := by
  classical
  exact Finset.univ.filter fun χ => χ.Even ∧ χ ≠ 1
noncomputable def evenCharLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  Finset.prod (evenNontrivialCharacters (p := p)) fun χ =>
    (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))
noncomputable def dedekindLocalFactor (ℓ : ℕ) (s : ℂ) : ℂ :=
  Finset.prod (primesOverFinset K ℓ) fun P => (1 - (Ideal.absNorm P : ℂ) ^ (-s))
noncomputable def evenLProduct (s : ℂ) : ℂ :=
  Finset.prod (evenNontrivialCharacters (p := p)) fun χ => DirichletCharacter.LFunction χ s
noncomputable def zetaInteger : 𝓞 K :=
  (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
lemma coprime_of_prime_ne {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : p.Coprime ℓ :=
  (Nat.coprime_primes hp.out (Fact.out : ℓ.Prime)).mpr (Ne.symm hℓp)
noncomputable def unitOfPrimeNe (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : (ZMod p)ˣ :=
  ZMod.unitOfCoprime ℓ (coprime_of_prime_ne (p := p) hℓp).symm
noncomputable def localResidueDegree (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  orderOf (unitOfPrimeNe (p := p) ℓ hℓp)
noncomputable def localPrimeCount (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  Nat.card (DirichletCharacter ℂ p) / localResidueDegree (p := p) ℓ hℓp
lemma localResidueDegree_dvd_card_characters {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localResidueDegree (p := p) ℓ hℓp ∣ Nat.card (DirichletCharacter ℂ p) := by
  rw [card_dirichletCharacter_complex (p := p)]
  simpa [localResidueDegree, ZMod.card_units p] using
    (orderOf_dvd_card (x := unitOfPrimeNe (p := p) ℓ hℓp))
lemma localPrimeCount_mul_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localPrimeCount (p := p) ℓ hℓp * localResidueDegree (p := p) ℓ hℓp =
      Nat.card (DirichletCharacter ℂ p) :=
  Nat.div_mul_cancel (localResidueDegree_dvd_card_characters (p := p) hℓp)
lemma prod_nthRootsFinset_one_sub_mul (d : ℕ) (hd : 0 < d) (T : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ζ * T) = 1 - T ^ d := by
  by_cases hT : T = 0
  · subst hT
    simp [zero_pow hd.ne']
  · have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / d)) d :=
      Complex.isPrimitiveRoot_exp d hd.ne'
    have hcard : (Polynomial.nthRootsFinset d (1 : ℂ)).card = d := hζ.card_nthRootsFinset
    have hpoly : Polynomial.X ^ d - 1 = ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ),
        (Polynomial.X - Polynomial.C ζ) := Polynomial.X_pow_sub_one_eq_prod hd hζ
    have heval := congrArg (Polynomial.eval T⁻¹) hpoly
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_prod, Polynomial.eval_C] at heval
    have key : ∀ ζ : ℂ, (1 - ζ * T) = T * (T⁻¹ - ζ) := fun ζ => by field_simp
    rw [Finset.prod_congr rfl (fun ζ _ => key ζ), Finset.prod_mul_distrib,
      Finset.prod_const, hcard, ← heval]
    have hTT : T ^ d * T⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hT, one_pow]
    linear_combination hTT
lemma _root_.IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd
    {M : Type*} [CommMonoid M] {n : ℕ} (hn : 0 < n) (a : ℕ)
    {ω : M} (hω : IsPrimitiveRoot ω n) :
    IsPrimitiveRoot (ω ^ a) (n / n.gcd a) := by
  set d := n / n.gcd a with hd_def
  set c := n.gcd a with hc_def
  have hc_dvd_n : c ∣ n := Nat.gcd_dvd_left n a
  have hc_dvd_a : c ∣ a := Nat.gcd_dvd_right n a
  have hc_mul_d : c * d = n := Nat.mul_div_cancel' hc_dvd_n
  have hc_pos : 0 < c := Nat.gcd_pos_of_pos_left _ hn
  obtain ⟨a', ha'⟩ := hc_dvd_a
  have ha'_cop : a'.Coprime d := by
    have key : c * Nat.gcd a' d = c * 1 := by
      rw [mul_one]
      calc c * Nat.gcd a' d
          = (c * a').gcd (c * d) := (Nat.gcd_mul_left c a' d).symm
        _ = a.gcd n := by rw [← ha', hc_mul_d]
        _ = c := by rw [Nat.gcd_comm]
    exact Nat.eq_of_mul_eq_mul_left hc_pos key
  have hω_c : IsPrimitiveRoot (ω ^ c) d := hω.pow hn hc_mul_d.symm
  rw [ha', pow_mul]
  exact hω_c.pow_of_coprime _ ha'_cop
lemma prod_pow_primRoot_eq_pow {n : ℕ} (hn : 0 < n) (a : ℕ)
    {ω : ℂ} (hω : IsPrimitiveRoot ω n) (T : ℂ) :
    ∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T) =
      (1 - T ^ (n / n.gcd a)) ^ n.gcd a := by
  classical
  set d := n / n.gcd a with hd_def
  set c := n.gcd a with hc_def
  have hc_dvd_n : c ∣ n := Nat.gcd_dvd_left n a
  have hc_dvd_a : c ∣ a := Nat.gcd_dvd_right n a
  have hc_mul_d : c * d = n := Nat.mul_div_cancel' hc_dvd_n
  have hc_pos : 0 < c := Nat.gcd_pos_of_pos_left _ hn
  have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd hn hc_dvd_n) hc_pos
  have hd_dvd_n : d ∣ n := ⟨c, by rw [mul_comm]; exact hc_mul_d.symm⟩
  have hω_a_prim : IsPrimitiveRoot (ω ^ a) d :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn a hω
  have h_period : ∀ k : ℕ, ω ^ (k * a) = ω ^ ((k % d) * a) := by
    intro k
    have hkd : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
    have h_da : ω ^ ((k / d) * (d * a)) = 1 := by
      obtain ⟨a', ha'⟩ := hc_dvd_a
      rw [ha', show (k / d) * (d * (c * a')) = (k / d) * a' * (c * d) from by ring, hc_mul_d]
      exact (hω.pow_eq_one_iff_dvd _).mpr ⟨(k / d) * a', mul_comm _ _⟩
    conv_lhs => rw [hkd]
    rw [show (d * (k / d) + k % d) * a = (k % d) * a + (k / d) * (d * a) from by ring, pow_add,
      h_da, mul_one]
  rw [show (∏ k ∈ Finset.range n, (1 - ω ^ (k * a) * T)) =
      ∏ k ∈ Finset.range n, (1 - ω ^ ((k % d) * a) * T) from
    Finset.prod_congr rfl (fun k _ => by rw [← h_period k])]
  rw [← Finset.prod_fiberwise_of_maps_to
    (g := fun k : ℕ => k % d) (t := Finset.range d)
    (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hd_pos))]
  have h_inner : ∀ j ∈ Finset.range d,
      (∏ k ∈ (Finset.range n).filter (fun k => k % d = j), (1 - ω ^ ((k % d) * a) * T)) =
      (1 - ω ^ (j * a) * T) ^ c := by
    intro j hj
    have h_rewrite : ∀ k ∈ (Finset.range n).filter (fun k => k % d = j),
        (1 - ω ^ ((k % d) * a) * T) = (1 - ω ^ (j * a) * T) := fun k hk => by
      rw [Finset.mem_filter] at hk; rw [hk.2]
    rw [Finset.prod_congr rfl h_rewrite, Finset.prod_const]
    congr 1
    rw [Finset.mem_range] at hj
    obtain ⟨c', hcd'⟩ := hd_dvd_n
    have hc_eq : c = c' := by
      have hd_mul : d * c = n := by rw [mul_comm, hc_mul_d]
      exact Nat.eq_of_mul_eq_mul_left hd_pos (by rw [hd_mul, hcd'])
    rw [hc_eq]
    have hset : (Finset.range n).filter (fun k => k % d = j) =
        (Finset.range c').image (fun m => j + m * d) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      refine ⟨fun ⟨hk_lt, hk_mod⟩ => ?_, ?_⟩
      · have hk_dec : k = j + (k / d) * d := by
          have h1 : k = d * (k / d) + k % d := (Nat.div_add_mod k d).symm
          rw [hk_mod, mul_comm d (k / d)] at h1
          omega
        refine ⟨k / d, ?_, hk_dec.symm⟩
        have h_lt_cd : (k / d) * d < c' * d := by
          have h_le : (k / d) * d ≤ k := Nat.div_mul_le_self k d
          rw [mul_comm c' d, ← hcd']; omega
        exact Nat.lt_of_mul_lt_mul_right h_lt_cd
      · rintro ⟨m, hm_lt, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [hcd', mul_comm]; nlinarith
        · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    rw [hset, Finset.card_image_of_injective _ (fun x y hxy => by simp at hxy; omega),
      Finset.card_range]
  rw [Finset.prod_congr rfl h_inner, Finset.prod_pow]
  congr 1
  have h_inj : Set.InjOn (fun j : ℕ => (ω ^ a) ^ j) ↑(Finset.range d) := by
    intro x hx y hy hxy
    simp only [Finset.coe_range, Set.mem_Iio] at hx hy
    exact hω_a_prim.pow_inj hx hy hxy
  have h_image : Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d) =
      Polynomial.nthRootsFinset d (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro ζ hζ
      simp only [Finset.mem_image, Finset.mem_range] at hζ
      obtain ⟨j, _, rfl⟩ := hζ
      rw [Polynomial.mem_nthRootsFinset hd_pos, ← pow_mul, mul_comm j d, pow_mul,
        hω_a_prim.pow_eq_one, one_pow]
    · rw [hω_a_prim.card_nthRootsFinset, Finset.card_image_of_injOn h_inj, Finset.card_range]
  calc ∏ j ∈ Finset.range d, (1 - ω ^ (j * a) * T)
      = ∏ j ∈ Finset.range d, (1 - (ω ^ a) ^ j * T) := by
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← pow_mul, mul_comm a j]
    _ = ∏ ζ ∈ Finset.image (fun j : ℕ => (ω ^ a) ^ j) (Finset.range d), (1 - ζ * T) := by
        rw [Finset.prod_image h_inj]
    _ = ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ζ * T) := by rw [h_image]
    _ = 1 - T ^ d := prod_nthRootsFinset_one_sub_mul d hd_pos T
lemma mem_primesOverFinset_iff {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 K)} :
    P ∈ primesOverFinset K ℓ ↔ P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
  have : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 K)
lemma zetaInteger_isIntegralGenerator :
    Algebra.adjoin ℤ ({zetaInteger (p := p) (K := K)} : Set (𝓞 K)) = ⊤ := by
  exact IsCyclotomicExtension.Rat.adjoin_singleton_eq_top (IsCyclotomicExtension.zeta_spec p ℚ K)
lemma zetaInteger_exponent_eq_one :
    RingOfIntegers.exponent (zetaInteger (p := p) (K := K)) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr (zetaInteger_isIntegralGenerator (p := p) (K := K))
lemma prime_not_dvd_zetaInteger_exponent {ℓ : ℕ} [Fact ℓ.Prime] :
    ¬ ℓ ∣ RingOfIntegers.exponent (zetaInteger (p := p) (K := K)) := by
  rw [zetaInteger_exponent_eq_one]
  exact Nat.Prime.not_dvd_one (Fact.out : ℓ.Prime)
noncomputable def primesOverEquivMonicFactorsMod (ℓ : ℕ) [Fact ℓ.Prime] :
  Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) ≃
      RingOfIntegers.monicFactorsMod (θ := zetaInteger (p := p) (K := K)) (p := ℓ) :=
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := K) (θ := zetaInteger (p := p) (K := K))
    (p := ℓ) (prime_not_dvd_zetaInteger_exponent (p := p) (K := K) (ℓ := ℓ))
lemma cyclotomic_mod_p_eq_X_sub_one_pow :
    map (Int.castRingHom (ZMod p))
        (minpoly ℤ (zetaInteger (p := p) (K := K))) =
      (X - 1) ^ (p - 1) := by
  have hmin : minpoly ℤ (zetaInteger (p := p) (K := K)) = cyclotomic p ℤ := by
    rw [zetaInteger, ← NumberField.RingOfIntegers.minpoly_coe]
    exact (Polynomial.cyclotomic_eq_minpoly (IsCyclotomicExtension.zeta_spec p ℚ K)
      hp.out.pos).symm
  rw [hmin, Polynomial.map_cyclotomic_int]
  have h1 : (cyclotomic p (ZMod p)) * (X - 1) = X ^ p - 1 :=
    cyclotomic_prime_mul_X_sub_one (ZMod p) p
  have h2 : (X - 1 : (ZMod p)[X]) ^ p = X ^ p - 1 := by
    rw [sub_pow_char_of_commute p (Commute.one_right X)]
    ring
  have hne : (X - 1 : (ZMod p)[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hpow : (X - 1 : (ZMod p)[X]) ^ p = (X - 1) ^ (p - 1) * (X - 1) := by
    have hpos : 0 < p := hp.out.pos
    rw [← pow_succ]
    congr 1
    omega
  refine mul_right_cancel₀ hne ?_
  rw [← hpow, h2, ← h1]
lemma monicFactorsMod_at_p_singleton :
    (RingOfIntegers.monicFactorsMod (θ := zetaInteger (p := p) (K := K)) (p := p)).card = 1 := by
  classical
  unfold RingOfIntegers.monicFactorsMod
  rw [cyclotomic_mod_p_eq_X_sub_one_pow (p := p) (K := K)]
  have hirr : Irreducible (X - 1 : (ZMod p)[X]) :=
    irreducible_X_sub_C 1
  rw [hirr.normalizedFactors_pow, Multiset.toFinset_replicate]
  have hp_pos : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  simp [hp_pos]
lemma ncard_primesOver_at_p_eq_one :
    (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)).ncard = 1 := by
  classical
  rw [← monicFactorsMod_at_p_singleton (p := p) (K := K),
    ← Nat.card_coe_set_eq, Nat.card_congr (primesOverEquivMonicFactorsMod (p := p) (K := K) p),
    Nat.card_eq_finsetCard]
lemma primesOver_inertiaDeg_eq_one_at_p (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K)) :
    P.inertiaDeg ℤ = 1 := by
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hP.2
  simpa [rationalPrimeIdeal] using IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime p K P
lemma primesOver_inertiaDeg_eq_localResidueDegree {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)) :
    P.inertiaDeg ℤ = localResidueDegree (p := p) ℓ hℓp := by
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := hP.2
  have hcop : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out : ℓ.Prime) hp.out).mp h)
  rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd ℓ K P hcop]
  unfold localResidueDegree unitOfPrimeNe
  rw [← orderOf_units]
  rfl
lemma primesOver_ramificationIdx_eq_one {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓp : ℓ ≠ p) (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K)) :
    P.ramificationIdx ℤ = 1 := by
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := hP.2
  have hcop : ¬ ℓ ∣ p := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq
    (Fact.out : ℓ.Prime) hp.out).mp h)
  exact IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd ℓ K P hcop
end ZetaFactorisation
end KummerCriterion
end
end Module11

-- Source: KummerCriterion.HMinus.ClassNumberFormula
section Module12
noncomputable section
open NumberField
open scoped BigOperators
namespace KummerCriterion
variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem hPlus_formula :
    (hPlus K : ℝ) =
      NumberField.dedekindZeta_residue (oMR K) *
        (((Units.torsionOrder (oMR K) : ℝ) *
            Real.sqrt |discr (oMR K)|) /
          (2 ^ InfinitePlace.nrRealPlaces (oMR K) *
            (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (oMR K) *
              Units.regulator (oMR K))) := by
  let L := oMR K
  let A : ℝ :=
    2 ^ InfinitePlace.nrRealPlaces L *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L
  let B : ℝ := (Units.torsionOrder L : ℝ) * Real.sqrt |discr L|
  have hA_pos : 0 < A := by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA : A ≠ 0 := hA_pos.ne'
  have hB_pos : 0 < B := by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  calc
    (hPlus K : ℝ) = ((A * (hPlus K : ℝ)) / B) * (B / A) := by
      field_simp [hA, hB_pos.ne']
    _ = NumberField.dedekindZeta_residue L * (B / A) := by
          dsimp [A, B, L]
          rw [NumberField.dedekindZeta_residue_def, KummerCriterion.hPlus, NumberField.classNumber]
    _ = NumberField.dedekindZeta_residue L *
          (((Units.torsionOrder L : ℝ) * Real.sqrt |discr L|) /
            (2 ^ InfinitePlace.nrRealPlaces L *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L)) := by
          simp [A, B]
omit [IsCMField K] in
lemma nrComplexPlaces_maximalRealSubfield_eq_zero :
    NumberField.InfinitePlace.nrComplexPlaces (oMR K) = 0 :=
  NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
      (K := oMR K)
lemma nrRealPlaces_maximalRealSubfield_eq_prime_sub_one_div_two :
    NumberField.InfinitePlace.nrRealPlaces (oMR K) = (p - 1) / 2 := by
  let L := oMR K
  calc
    NumberField.InfinitePlace.nrRealPlaces L = Module.finrank ℚ L := by
      rw [← NumberField.IsTotallyReal.finrank (K := L)]
    _ = (p - 1) / 2 := by
      rw [finrank_Kplus_over_rat (p := p) (K := K)]
lemma maximalRealSubfield_archimedeanFactor_eq_pow :
    2 ^ NumberField.InfinitePlace.nrRealPlaces (oMR K) *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (oMR K) =
      2 ^ ((p - 1) / 2 : ℕ) := by
  rw [nrComplexPlaces_maximalRealSubfield_eq_zero (K := K), pow_zero, mul_one,
    nrRealPlaces_maximalRealSubfield_eq_prime_sub_one_div_two (p := p) (K := K)]
omit [IsCMField K] in
lemma maximalRealSubfield_torsion_eq_one_or_neg_one
    (x : NumberField.Units.torsion (oMR K)) :
    (x : (𝓞 (oMR K))ˣ) = 1 ∨
      (x : (𝓞 (oMR K))ˣ) = -1 := by
  let L := oMR K
  let φ : L →+* ℂ := Classical.choice inferInstance
  let hφ : ComplexEmbedding.IsReal φ :=
    NumberField.IsTotallyReal.complexEmbedding_isReal φ
  let u : (𝓞 L)ˣ := x
  let r : ℝ := hφ.embedding (u : L)
  have hur : ((r : ℂ)) = φ (u : L) :=
    hφ.coe_embedding_apply (u : L)
  have hu_fin : IsOfFinOrder u := (CommGroup.mem_torsion u).1 x.prop
  obtain ⟨n, hn, hu_pow⟩ := isOfFinOrder_iff_pow_eq_one.mp hu_fin
  have hnorm : ‖φ (u : L)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one
      (by simpa [map_pow] using congrArg (fun z : (𝓞 L)ˣ => φ (z : L)) hu_pow)
      (Nat.ne_of_gt hn)
  have hr_norm : ‖(r : ℂ)‖ = 1 := by
    rwa [← hur] at hnorm
  have hr_abs : |r| = 1 := by
    simpa [Complex.norm_real] using hr_norm
  have hr_sq : r ^ 2 = 1 := by
    have hsquare := congrArg (fun t : ℝ => t ^ 2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · left
    apply NumberField.Units.coe_injective (K := L)
    apply φ.injective
    simpa [hr] using hur.symm
  · right
    apply NumberField.Units.coe_injective (K := L)
    apply φ.injective
    simpa [hr] using hur.symm
omit [IsCMField K] in
lemma maximalRealSubfield_torsionOrder_eq_two :
    Units.torsionOrder (oMR K) = 2 := by
  let L := oMR K
  classical
  let := Fintype.ofFinite (Units.torsion L)
  rw [Units.torsionOrder, Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.2
    ⟨1, ⟨-1, neg_one_mem_torsion⟩, by simp [← Subtype.coe_ne_coe],
      Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact maximalRealSubfield_torsion_eq_one_or_neg_one (K := K) x
lemma units_rank_eq_prime_sub_three_div_two :
    Units.rank K = (p - 3) / 2 := by
  let L := oMR K
  rw [← NumberField.IsCMField.units_rank_eq_units_rank (K := K), Units.rank]
  calc
    Fintype.card (NumberField.InfinitePlace L) - 1
        = NumberField.InfinitePlace.nrRealPlaces L - 1 := by
            rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
              NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    _ = Module.finrank ℚ L - 1 := by
          rw [← NumberField.IsTotallyReal.finrank (K := L)]
    _ = (p - 1) / 2 - 1 := by
          rw [finrank_Kplus_over_rat (p := p) (K := K)]
    _ = (p - 3) / 2 := by omega
omit [IsCMField K] in
lemma zeta_not_mem_maximalRealSubfield (hp_odd' : p ≠ 2) :
    IsCyclotomicExtension.zeta p ℚ K ∉ oMR K := by
  classical
  let ζ : K := IsCyclotomicExtension.zeta p ℚ K
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ K
  intro hmem
  have hfix := (NumberField.mem_maximalRealSubfield_iff (K := K) ζ).mp hmem
  let φ : K →+* ℂ := Classical.choice inferInstance
  have hstar : star (φ ζ) = φ ζ := hfix φ
  have hpow : (φ ζ) ^ p = 1 := by
    simpa [map_pow] using congrArg φ hζ.pow_eq_one
  have hnorm : ‖φ ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow hp.out.ne_zero
  have him : (φ ζ).im = 0 := by
    simpa [RCLike.star_def] using (Complex.conj_eq_iff_im.mp hstar)
  let r : ℝ := (φ ζ).re
  have hreal : φ ζ = (r : ℂ) := by
    apply Complex.ext <;> simp [r, him]
  rw [hreal] at hnorm
  have hr_abs : |r| = 1 := by
    simpa [Complex.norm_real] using hnorm
  have hr_sq : r ^ 2 = 1 := by
    have hsquare := congrArg (fun t : ℝ => t ^ 2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · have hφζ : φ ζ = 1 := by
      calc
        φ ζ = (r : ℂ) := hreal
        _ = (1 : ℂ) := by simp [hr]
    have hζeq : ζ = 1 := φ.injective <| by simpa using hφζ
    exact (hζ.ne_one hp.out.one_lt) hζeq
  · have hφζ : φ ζ = -1 := by
      calc
        φ ζ = (r : ℂ) := hreal
        _ = (-1 : ℂ) := by simp [hr]
    have hpo : Odd p := hp.out.odd_of_ne_two hp_odd'
    have : ((-1 : ℂ) ^ p) = 1 := by simpa [hφζ] using hpow
    have hneg : (-1 : ℂ) = 1 := by simpa [Odd.neg_one_pow hpo] using this
    have hneq : (-1 : ℂ) ≠ 1 := by norm_num
    exact hneq hneg
omit [IsCMField K] in
lemma zetaInteger_not_mem_field_range (hp_odd' : p ≠ 2) :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∉
      Set.range (algebraMap (oMR K) K) := by
  rintro ⟨x, hx⟩
  have hxmem : (algebraMap (oMR K) K x) ∈
      oMR K := x.2
  have hzmem : (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∈
      oMR K := by
    simpa [hx] using hxmem
  exact zeta_not_mem_maximalRealSubfield (p := p) (K := K) hp_odd' hzmem
omit [IsCMField K] in
lemma zetaInteger_not_mem_ring_range (hp_odd' : p ≠ 2) :
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ∉
      Set.range (algebraMap (𝓞 (oMR K)) (𝓞 K)) := by
  rintro ⟨x, hx⟩
  apply zetaInteger_not_mem_field_range (p := p) (K := K) hp_odd'
  refine ⟨(x : oMR K), ?_⟩
  exact congrArg (fun y : 𝓞 K => (y : K)) hx
lemma zetaInteger_adjoin_eq_top_maximalRealSubfield (hp_odd' : p ≠ 2) :
    Algebra.adjoin (oMR K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)} : Set K) = ⊤ := by
  let L : IntermediateField (oMR K) K :=
    IntermediateField.adjoin (oMR K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)} : Set K)
  have hL : L = ⊤ := by
    have hprime : Nat.Prime (Module.finrank (oMR K) K) := by
      simpa [finrank_K_over_Kplus (K := K)] using Nat.prime_two
    have hsimple :=
      ((IntermediateField.isSimpleOrder_of_finrank_prime (oMR K) K
          hprime).eq_bot_or_eq_top L)
    refine hsimple.resolve_left ?_
    intro hbot
    have hzeta_mem : (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∈ L :=
      IntermediateField.subset_adjoin _ _ (by simp)
    rw [hbot, IntermediateField.mem_bot] at hzeta_mem
    exact zetaInteger_not_mem_field_range (p := p) (K := K) hp_odd' hzeta_mem
  have hzeta_alg : IsAlgebraic (oMR K)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)) :=
    Algebra.IsAlgebraic.isAlgebraic _
  exact Algebra.adjoin_eq_top_of_primitive_element hzeta_alg hL
omit [IsCMField K] in
lemma one_add_zetaInteger_isUnit (hp_odd' : p ≠ 2) :
    IsUnit (1 + ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K)) := by
  have h :=
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.geom_sum_isUnit
      hp.out.two_le (Nat.coprime_two_left.mpr (hp.out.odd_of_ne_two hp_odd'))
  simpa [Finset.sum_range_succ] using h
omit [IsCMField K] in
lemma zetaInteger_pow_pred_mul_eq_one :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) = 1 :=
  zeta_toInteger_pow_pred_mul p K
omit [IsCMField K] in
lemma zetaInteger_mul_pow_pred_eq_one :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) : 𝓞 K) = 1 := by
  simpa [mul_comm] using zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)
omit [IsCMField K] in
lemma one_add_zetaInteger_pow_pred_isUnit (hp_odd' : p ≠ 2) :
    IsUnit (1 + ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hzeta_unit : IsUnit (ζi ^ (p - 1) : 𝓞 K) := by
    simpa using! (IsCyclotomicExtension.zeta_spec p ℚ K).unit'.isUnit.pow (p - 1)
  have hmul : (ζi ^ (p - 1) : 𝓞 K) * (1 + ζi) = 1 + ζi ^ (p - 1) := by
    rw [mul_add, mul_one, zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)]
    ring
  rw [← hmul]
  exact hzeta_unit.mul (one_add_zetaInteger_isUnit (p := p) (K := K) hp_odd')
lemma algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred :
    (algebraMap (𝓞 (oMR K)) (𝓞 K)) (piPlus p K) =
      (2 : 𝓞 K) - (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [algebraMap_piPlus]
  have hconj : NumberField.IsCMField.ringOfIntegersComplexConj K (ζi - 1) =
      ζi ^ (p - 1) - 1 := by
    rw [map_sub, map_one, complexConj_apply_zeta]
  calc
    (ζi - 1) * NumberField.IsCMField.ringOfIntegersComplexConj K (ζi - 1)
        = (ζi - 1) * (ζi ^ (p - 1) - 1) := by rw [hconj]
    _ = ζi * ζi ^ (p - 1) - ζi - ζi ^ (p - 1) + 1 := by
          ring
    _ = (2 : 𝓞 K) - ζi - ζi ^ (p - 1) := by
          rw [zetaInteger_mul_pow_pred_eq_one (p := p) (K := K)]
          ring_nf
lemma aeval_zetaInteger_quadratic_eq_zero :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
        Polynomial (𝓞 (oMR K))) = 0 := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hcalc :
      ζi ^ 2 + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) * ζi + 1 = 0 := by
    calc
      ζi ^ 2 + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) * ζi + 1
          = -(ζi ^ (p - 1) * ζi) + 1 := by ring
      _ = 0 := by
            rw [zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)]
            norm_num
  simpa [Polynomial.aeval_def, algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred,
    pow_two, map_sub, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    using! hcalc
lemma minpoly_maximalRealSubfield_zetaInteger_eq_quadratic (hp_odd' : p ≠ 2) :
    minpoly (𝓞 (oMR K))
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) =
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
        Polynomial (𝓞 (oMR K))) := by
  let A := 𝓞 (oMR K)
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hint : IsIntegral A ζi := IsIntegralClosure.isIntegral A K ζi
  have hdeg :
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
          Polynomial A).degree ≤
        (minpoly A ζi).degree := by
    have hnatdeg : 2 ≤ (minpoly A ζi).natDegree :=
      (minpoly.two_le_natDegree_iff hint).2
        (zetaInteger_not_mem_ring_range (p := p) (K := K) hp_odd')
    have hpoly_deg :
        (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
          Polynomial A).degree = 2 := by
      simpa [one_mul, Polynomial.C_1] using
        (Polynomial.degree_quadratic
          (R := A)
          (a := (1 : A))
          (b := piPlus p K - 2)
          (c := (1 : A))
          one_ne_zero)
    rw [hpoly_deg, Polynomial.degree_eq_natDegree (minpoly.ne_zero hint)]
    exact_mod_cast hnatdeg
  symm
  refine IsIntegrallyClosed.minpoly.unique (R := A) (S := 𝓞 K) (s := ζi) ?_ ?_ ?_
  · simpa [Polynomial.C_1] using
      (Polynomial.isMonicOfDegree_add_add_two (a := piPlus p K - 2) (b := (1 : A))).monic
  · exact aeval_zetaInteger_quadratic_eq_zero (p := p) (K := K)
  · intro Q hQ hQroot
    exact hdeg.trans (minpoly.min (A := A) (x := ζi) hQ hQroot)
lemma aeval_derivative_minpoly_zetaInteger_eq_zeta_sub_complexConj_zeta (hp_odd' : p ≠ 2) :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.derivative
        (minpoly (𝓞 (oMR K))
          ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K))) =
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have htwo :
      (algebraMap (𝓞 (oMR K)) (𝓞 K)) 2 = (2 : 𝓞 K) := by
    simpa using map_natCast (algebraMap (𝓞 (oMR K)) (𝓞 K)) 2
  rw [minpoly_maximalRealSubfield_zetaInteger_eq_quadratic (p := p) (K := K) hp_odd']
  simpa [Polynomial.aeval_def, algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred,
    map_sub, htwo, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
    mul_comm] using
    (show ((1 + 1 : 𝓞 K) * ζi) + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) =
        ζi - ζi ^ (p - 1) by ring)
omit [IsCMField K] in
lemma span_zetaInteger_sub_zetaPowPred_eq_zetaPrime (hp_odd' : p ≠ 2) :
    Ideal.span
        ({((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) -
            (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1)} :
          Set (𝓞 K)) =
      zetaPrime p K := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [zetaPrime]
  have hcalc :
      (ζi - 1) * (1 + ζi ^ (p - 1)) = ζi - ζi ^ (p - 1) := by
    have hmul : ζi * ζi ^ (p - 1) = 1 := zetaInteger_mul_pow_pred_eq_one (p := p) (K := K)
    calc
      (ζi - 1) * (1 + ζi ^ (p - 1)) = ζi - 1 + (ζi * ζi ^ (p - 1) - ζi ^ (p - 1)) := by
        ring
      _ = ζi - ζi ^ (p - 1) := by
        rw [hmul]
        ring
  rw [← hcalc, Ideal.span_singleton_mul_right_unit]
  exact one_add_zetaInteger_pow_pred_isUnit (p := p) (K := K) hp_odd'
lemma differentIdeal_maximalRealSubfield_eq_zetaPrime (hp_odd' : p ≠ 2) :
    differentIdeal (𝓞 (oMR K)) (𝓞 K) = zetaPrime p K := by
  let A := 𝓞 (oMR K)
  let B := 𝓞 K
  let PPlus : Ideal A := zetaPrimePlus p K
  let P : Ideal B := zetaPrime p K
  have hPPlus0 : PPlus ≠ ⊥ := by
    intro hbot
    have hmap : Ideal.map (algebraMap A B) PPlus = P ^ 2 := by
      simpa [A, B, PPlus, P] using zetaPrimePlus_map_eq (p := p) (hp_odd := hp_odd') (K := K)
    rw [hbot, Ideal.map_bot] at hmap
    exact (pow_ne_zero 2 (zetaPrime_ne_bot p K)) hmap.symm
  have hle : differentIdeal A B ≤ P := by
    have : PPlus.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPPlus0
    have hdiv : P ∣ differentIdeal A B := by
      have hpow : P ^ 2 ∣ Ideal.map (algebraMap A B) PPlus := by
        rw [zetaPrimePlus_map_eq (p := p) (hp_odd := hp_odd') (K := K)]
      simpa [A, B, P, PPlus] using
        (pow_sub_one_dvd_differentIdeal (A := A) (B := B) (p := PPlus) P 2 hPPlus0 hpow)
    exact Ideal.dvd_iff_le.mp hdiv
  have hmem :
      Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
          (Polynomial.derivative
            (minpoly A ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : B))) ∈
        differentIdeal A B :=
    aeval_derivative_mem_differentIdeal (A := A)
      (K := oMR K) (L := K) (B := B)
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger)
      (zetaInteger_adjoin_eq_top_maximalRealSubfield (p := p) (K := K) hp_odd')
  have hP_le : P ≤ differentIdeal A B := by
    change zetaPrime p K ≤ differentIdeal A B
    rw [← span_zetaInteger_sub_zetaPowPred_eq_zetaPrime (p := p) (K := K) hp_odd']
    rw [Ideal.span_singleton_le_iff_mem]
    convert hmem using 1
    symm
    exact aeval_derivative_minpoly_zetaInteger_eq_zeta_sub_complexConj_zeta
      (p := p) (K := K) hp_odd'
  exact le_antisymm hle hP_le
lemma absNorm_differentIdeal_maximalRealSubfield_eq_prime (hp_odd' : p ≠ 2) :
    Ideal.absNorm (differentIdeal (𝓞 (oMR K)) (𝓞 K)) = p := by
  rw [differentIdeal_maximalRealSubfield_eq_zetaPrime (p := p) (K := K) hp_odd',
    zetaPrime]
  rw [Ideal.absNorm_span_singleton,
    (IsCyclotomicExtension.zeta_spec p ℚ K).norm_toInteger_sub_one_of_prime_ne_two' hp_odd']
  simp [Int.natAbs_natCast]
lemma natAbs_discr_maximalRealSubfield_eq_pow (hp_odd' : p ≠ 2) :
    (NumberField.discr (oMR K)).natAbs = p ^ ((p - 3) / 2) := by
  let L := oMR K
  have hmain := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (K := L) (𝒪 := 𝓞 L) (L := K) (𝒪' := 𝓞 K)
  have hdiscrK : (NumberField.discr K).natAbs = p ^ (p - 2) := by
    rw [IsCyclotomicExtension.Rat.discr_prime (p := p) (K := K)]
    simp [Int.natAbs_mul]
  have hfin : Module.finrank L K = 2 := by
    simpa [L] using (finrank_K_over_Kplus (K := K))
  have hp3 : 3 ≤ p := by
    have hp2 : 2 ≤ p := hp.out.two_le
    omega
  rw [hdiscrK, absNorm_differentIdeal_maximalRealSubfield_eq_prime (p := p)
      (K := K) hp_odd'] at hmain
  have hmain2 : p ^ (p - 2) = p * (NumberField.discr L).natAbs ^ 2 := by
    conv_rhs => rw [← hfin]
    exact hmain
  have hsq : (NumberField.discr L).natAbs ^ 2 = p ^ (p - 3) := by
    have hmain' : p * p ^ (p - 3) = p * (NumberField.discr L).natAbs ^ 2 := by
      calc
        p * p ^ (p - 3) = p ^ (p - 2) := by
          rw [show p - 2 = (p - 3) + 1 by omega, pow_succ', mul_comm]
        _ = p * (NumberField.discr L).natAbs ^ 2 := hmain2
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos hmain'.symm
  have hpow : (p ^ ((p - 3) / 2)) ^ 2 = p ^ (p - 3) := by
    rcases hp.out.odd_of_ne_two hp_odd' with ⟨n, hn⟩
    have hdiv : (p - 3) / 2 = n - 1 := by
      rw [hn, show 2 * n + 1 - 3 = 2 * (n - 1) by omega,
        Nat.mul_div_right _ (by decide : 0 < 2)]
    calc
      (p ^ ((p - 3) / 2)) ^ 2 = (p ^ (n - 1)) ^ 2 := by rw [hdiv]
      _ = p ^ ((n - 1) * 2) := by rw [← pow_mul]
      _ = p ^ (p - 3) := by
            congr
            rw [hn]
            omega
  have hsq' : (NumberField.discr L).natAbs ^ 2 = (p ^ ((p - 3) / 2)) ^ 2 := by
    rw [hpow, hsq]
  have := congrArg Nat.sqrt hsq'
  simpa [Nat.sqrt_eq'] using this
lemma abs_discr_maximalRealSubfield_eq_pow (hp_odd' : p ≠ 2) :
    |((NumberField.discr (oMR K) : ℤ) : ℝ)| =
      (p : ℝ) ^ ((p - 3) / 2) := by
  have habs : (((NumberField.discr (oMR K)).natAbs : ℕ) : ℝ) =
      |((NumberField.discr (oMR K) : ℤ) : ℝ)| := by
    convert
      (Nat.cast_natAbs (α := ℝ) (NumberField.discr (oMR K))) using 1
    simp
  rw [← habs, natAbs_discr_maximalRealSubfield_eq_pow (p := p) (K := K) hp_odd', Nat.cast_pow]
end KummerCriterion
end
end Module12

-- Source: KummerCriterion.LehmerVandiver.PrimaryUnits.Part1
section Module13
noncomputable section
open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
namespace LehmerVandiver
section CyclotomicSetup
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
end CyclotomicSetup
end LehmerVandiver
end KummerCriterion
end
noncomputable section
open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors
namespace KummerCriterion
namespace LehmerVandiver
section ConjSetup
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
end ConjSetup
end LehmerVandiver
end KummerCriterion
end
noncomputable section
open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
section PrimaryPlus
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
section CyclotomicUnits
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def cyclotomicUnit (k : ℕ) : 𝓞 K :=
  ∑ j ∈ Finset.range k, (zeta_spec p ℚ K).unit' ^ j
theorem one_sub_zeta_mul_cyclotomicUnit (k : ℕ) :
    (1 - (zeta_spec p ℚ K).unit') * cyclotomicUnit p K k =
      1 - ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k := by
  unfold cyclotomicUnit
  rw [Finset.mul_sum]
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
theorem zeta_sub_one_mul_cyclotomicUnit (k : ℕ) :
    (((zeta_spec p ℚ K).unit' : 𝓞 K) - 1) * cyclotomicUnit p K k =
      ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ k - 1 := by
  linear_combination -(one_sub_zeta_mul_cyclotomicUnit p K k)
theorem isUnit_cyclotomicUnit (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (cyclotomicUnit p K k) := by
  unfold cyclotomicUnit
  exact (zeta_spec p ℚ K).unit'_coe.geom_sum_isUnit hp_two hk
noncomputable def cyclotomicUnitUnit (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (𝓞 K)ˣ :=
  (isUnit_cyclotomicUnit p K k hk hp_two).unit
@[simp]
theorem cyclotomicUnitUnit_val (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (cyclotomicUnitUnit p K k hk hp_two : 𝓞 K) = cyclotomicUnit p K k :=
  IsUnit.unit_spec _
end CyclotomicUnits
end PrimaryPlus
end LehmerVandiver
end KummerCriterion
end
end Module13

-- Source: KummerCriterion.LehmerVandiver.PrimaryUnits.Part2
section Module14
noncomputable section
open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
section PrimaryPlus
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
section CyclotomicUnits
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
end CyclotomicUnits
section RealCyclotomicUnits
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def realCyclotomicUnit [IsCMField K] (k : ℕ) : 𝓞 K :=
  cyclotomicUnit p K k * ringOfIntegersComplexConj K (cyclotomicUnit p K k)
theorem realCyclotomicUnit_complexConj [IsCMField K] (k : ℕ) :
    ringOfIntegersComplexConj K (realCyclotomicUnit p K k) =
      realCyclotomicUnit p K k := by
  unfold realCyclotomicUnit
  rw [map_mul]
  rw [show ringOfIntegersComplexConj K
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
      cyclotomicUnit p K k from by
    apply RingOfIntegers.ext
    simp]
  ring
theorem isUnit_realCyclotomicUnit [IsCMField K] (k : ℕ) (hk : k.Coprime p)
    (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnit p K k) := by
  unfold realCyclotomicUnit
  exact (isUnit_cyclotomicUnit p K k hk hp_two).mul
    ((isUnit_cyclotomicUnit p K k hk hp_two).map
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
end RealCyclotomicUnits
end PrimaryPlus
end LehmerVandiver
end KummerCriterion
end
end Module14

-- Source: KummerCriterion.LehmerVandiver.PrimaryUnits.Part3
section Module15
noncomputable section
open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
section PrimaryPlus
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
section RealCyclotomicUnits
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
theorem exists_realCyclotomicUnit_descent [IsCMField K] (k : ℕ) :
    ∃ y : 𝓞 (oMR K),
      algebraMap (𝓞 (oMR K)) (𝓞 K) y =
      realCyclotomicUnit p K k :=
  (ringOfIntegersComplexConj_eq_self_iff K (realCyclotomicUnit p K k)).mp
    (realCyclotomicUnit_complexConj p K k)
noncomputable def realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    𝓞 (oMR K) :=
  (exists_realCyclotomicUnit_descent p K k).choose
theorem algebraMap_realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    algebraMap (𝓞 (oMR K)) (𝓞 K)
        (realCyclotomicUnitPlus p K k) =
      realCyclotomicUnit p K k :=
  (exists_realCyclotomicUnit_descent p K k).choose_spec
theorem isUnit_realCyclotomicUnitPlus [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnitPlus p K k) := by
  have h_unit : IsUnit (realCyclotomicUnit p K k) :=
    isUnit_realCyclotomicUnit p K k hk hp_two
  rw [← algebraMap_realCyclotomicUnitPlus p K k] at h_unit
  have h_norm_unit : IsUnit (RingOfIntegers.norm (oMR K)
      (algebraMap (𝓞 (oMR K)) (𝓞 K)
        (realCyclotomicUnitPlus p K k))) :=
    h_unit.map _
  rw [RingOfIntegers.norm_algebraMap] at h_norm_unit
  have hfin_ne : Module.finrank (oMR K) K ≠ 0 := by
    rw [finrank_K_over_Kplus]
    decide
  exact (isUnit_pow_iff hfin_ne).mp h_norm_unit
noncomputable def realCyclotomicUnitPlusUnit [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (𝓞 (oMR K))ˣ :=
  (isUnit_realCyclotomicUnitPlus p K k hk hp_two).unit
@[simp]
theorem realCyclotomicUnitPlusUnit_val [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (realCyclotomicUnitPlusUnit p K k hk hp_two : 𝓞 (oMR K)) =
      realCyclotomicUnitPlus p K k :=
  IsUnit.unit_spec _
end RealCyclotomicUnits
end PrimaryPlus
end LehmerVandiver
end KummerCriterion
end
end Module15

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitFamily
section Module16
noncomputable section
open NumberField NumberField.IsCMField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]
def cyclotomicRealUnit {a : ℕ} (ha : a.Coprime p) (hp_two : 2 ≤ p) : (𝓞 K)ˣ :=
  cyclotomicUnitUnit p K a ha hp_two *
    unitsComplexConj K (cyclotomicUnitUnit p K a ha hp_two)
theorem unitsComplexConj_unitsComplexConj (u : (𝓞 K)ˣ) :
    unitsComplexConj K (unitsComplexConj K u) = u := by
  apply Units.ext
  change ringOfIntegersComplexConj K
      (ringOfIntegersComplexConj K (u : 𝓞 K)) = (u : 𝓞 K)
  apply RingOfIntegers.ext
  rw [coe_ringOfIntegersComplexConj, coe_ringOfIntegersComplexConj]
  exact complexConj_apply_apply K _
theorem unitsComplexConj_cyclotomicRealUnit {a : ℕ} (ha : a.Coprime p) (hp_two : 2 ≤ p) :
    unitsComplexConj K (cyclotomicRealUnit p K ha hp_two) =
      cyclotomicRealUnit p K ha hp_two := by
  unfold cyclotomicRealUnit
  rw [map_mul, unitsComplexConj_unitsComplexConj, mul_comm]
theorem isUnit_realCyclotomicUnitPlus
    {a : ℕ} (ha : a.Coprime p) (_ha_lt : a < p) (hp_two : 2 ≤ p) :
    IsUnit (LehmerVandiver.realCyclotomicUnitPlus p K a) := by
  have h_real_unit : ∃ inv_u : (𝓞 K)ˣ,
      unitsComplexConj K inv_u = inv_u ∧
      ((cyclotomicRealUnit p K ha hp_two : (𝓞 K)ˣ) *
        inv_u : (𝓞 K)ˣ) = 1 := by
    refine ⟨(cyclotomicRealUnit p K ha hp_two)⁻¹, ?_, mul_inv_cancel _⟩
    rw [map_inv]
    exact congrArg (·⁻¹)
      (unitsComplexConj_cyclotomicRealUnit (p := p) (K := K) ha hp_two)
  obtain ⟨inv_u, h_inv_real, h_mul⟩ := h_real_unit
  have h_inv_mem : inv_u ∈ realUnits K := by
    rw [← unitsComplexConj_eq_self_iff (K := K)]
    exact h_inv_real
  rw [mem_realUnits_iff (K := K)] at h_inv_mem
  obtain ⟨v_inv, hv_inv⟩ := h_inv_mem
  rw [isUnit_iff_exists]
  refine ⟨(v_inv : 𝓞 (oMR K)), ?_, ?_⟩
  · apply FaithfulSMul.algebraMap_injective
      (𝓞 (oMR K)) (𝓞 K)
    rw [map_mul, map_one, LehmerVandiver.algebraMap_realCyclotomicUnitPlus, hv_inv]
    have h_u_eq : LehmerVandiver.realCyclotomicUnit p K a =
        ((cyclotomicRealUnit p K ha hp_two : (𝓞 K)ˣ) : 𝓞 K) := by
      unfold cyclotomicRealUnit LehmerVandiver.realCyclotomicUnit
      rw [Units.val_mul, cyclotomicUnitUnit_val]
      rfl
    rw [h_u_eq, ← Units.val_mul, h_mul, Units.val_one]
  · apply FaithfulSMul.algebraMap_injective
      (𝓞 (oMR K)) (𝓞 K)
    rw [map_mul, map_one, LehmerVandiver.algebraMap_realCyclotomicUnitPlus, hv_inv]
    have h_u_eq : LehmerVandiver.realCyclotomicUnit p K a =
        ((cyclotomicRealUnit p K ha hp_two : (𝓞 K)ˣ) : 𝓞 K) := by
      unfold cyclotomicRealUnit LehmerVandiver.realCyclotomicUnit
      rw [Units.val_mul, cyclotomicUnitUnit_val]
      rfl
    rw [h_u_eq, ← Units.val_mul]
    have h_comm : inv_u * cyclotomicRealUnit p K ha hp_two = 1 := by
      rw [mul_comm]; exact h_mul
    rw [h_comm, Units.val_one]
noncomputable def realCyclotomicUnitPlusUnit
    {a : ℕ} (ha : a.Coprime p) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    (𝓞 (oMR K))ˣ :=
  (isUnit_realCyclotomicUnitPlus p K ha ha_lt hp_two).unit
@[simp]
theorem realCyclotomicUnitPlusUnit_val
    {a : ℕ} (ha : a.Coprime p) (ha_lt : a < p) (hp_two : 2 ≤ p) :
    (realCyclotomicUnitPlusUnit p K ha ha_lt hp_two :
      𝓞 (oMR K)) =
    LehmerVandiver.realCyclotomicUnitPlus p K a :=
  IsUnit.unit_spec _
theorem cyclotomicUnitFamily_index_coprime (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) : ((i : ℕ) + 2).Coprime p := by
  have hp_prime : Nat.Prime p := Fact.out
  have h_lt : (i : ℕ) + 2 < p := by
    have hi_lt : (i : ℕ) < (p - 3) / 2 := i.isLt
    have h_half : (p - 3) / 2 ≤ p - 3 := Nat.div_le_self _ _
    omega
  have h_pos : 1 ≤ (i : ℕ) + 2 := by omega
  have h_not_dvd : ¬ p ∣ ((i : ℕ) + 2) := fun h => by
    have := Nat.le_of_dvd h_pos h
    omega
  exact (hp_prime.coprime_iff_not_dvd.mpr h_not_dvd).symm
omit hp in
theorem cyclotomicUnitFamily_index_lt
    (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    (i : ℕ) + 2 < p := by
  have hi_lt : (i : ℕ) < (p - 3) / 2 := i.isLt
  have h_half : (p - 3) / 2 ≤ p - 3 := Nat.div_le_self _ _
  omega
noncomputable def cyclotomicUnitFamilyKplus (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) : (𝓞 (oMR K))ˣ :=
  realCyclotomicUnitPlusUnit p K
    (cyclotomicUnitFamily_index_coprime p hp_three i)
    (cyclotomicUnitFamily_index_lt p hp_three i)
    (Nat.Prime.two_le Fact.out)
noncomputable def cyclotomicUnitFamilyKplusFinRank (_hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    Fin (NumberField.Units.rank (oMR K)) →
      (𝓞 (oMR K))ˣ :=
  fun i =>
    cyclotomicUnitFamilyKplus p K hp_three
      (i.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
        (KummerCriterion.units_rank_eq_prime_sub_three_div_two (p := p) (K := K))))
theorem regOfFamily_cyclotomicUnitFamilyKplus_div_regulator (hp_odd : p ≠ 2)
    (hp_three : 3 ≤ p) :
    NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) /
      NumberField.Units.regulator (oMR K) =
    ((Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (oMR K)).index
      : ℝ) :=
  NumberField.Units.regOfFamily_div_regulator
    (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module16

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.IndexFormula
section Module17
noncomputable section
open NumberField NumberField.IsCMField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]
def SinnottIndexFormula (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (Subgroup.closure
      (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
    NumberField.Units.torsion (oMR K)).index =
  2 ^ ((p - 3) / 2) * hPlus K
def SinnottRegulatorIdentity (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
    (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) *
      NumberField.Units.regulator (oMR K)
theorem sinnottIndexFormula_of_regulatorIdentity
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottRegulatorIdentity p K hp_odd hp_three) :
    SinnottIndexFormula p K hp_odd hp_three := by
  unfold SinnottIndexFormula SinnottRegulatorIdentity at *
  have h_div := regOfFamily_cyclotomicUnitFamilyKplus_div_regulator
    p K hp_odd hp_three
  have h_reg_pos : 0 < NumberField.Units.regulator
      (oMR K) :=
    NumberField.Units.regulator_pos _
  rw [h] at h_div
  rw [show (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) *
        NumberField.Units.regulator (oMR K) /
        NumberField.Units.regulator (oMR K) =
      2 ^ ((p - 3) / 2) * (hPlus K : ℝ) from by
    field_simp] at h_div
  exact_mod_cast h_div.symm
theorem index_eq_twoPow_mul_hPlus_of_sinnottIndexFormula
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h : SinnottIndexFormula p K hp_odd hp_three) :
    (Subgroup.closure
        (Set.range (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
      NumberField.Units.torsion (oMR K)).index =
    2 ^ ((p - 3) / 2) * hPlus K := h
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module17

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LogEmbedding
section Module18
noncomputable section
open NumberField NumberField.IsCMField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]
theorem algebraMap_cyclotomicUnitFamilyKplus
    (j : Fin (NumberField.Units.rank
        (oMR K)))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    algebraMap (𝓞 (oMR K)) (𝓞 K)
        ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
          (𝓞 (oMR K))ˣ) :
          𝓞 (oMR K)) =
      LehmerVandiver.realCyclotomicUnit p K
        ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
          (KummerCriterion.units_rank_eq_prime_sub_three_div_two
            (p := p) (K := K)))) + 2) := by
  unfold cyclotomicUnitFamilyKplusFinRank cyclotomicUnitFamilyKplus
  rw [realCyclotomicUnitPlusUnit_val]
  exact LehmerVandiver.algebraMap_realCyclotomicUnitPlus p K _
end Sinnott
end LehmerVandiver
end KummerCriterion
end
noncomputable section
open NumberField NumberField.IsCMField NumberField.InfinitePlace
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]
omit [IsCMField K] in
theorem mult_eq_one_of_maximalRealSubfield (w : InfinitePlace (oMR K)) :
    mult w = 1 := by
  rw [mult]
  simp [IsTotallyReal.isReal w]
omit [IsCMField K] in
theorem logEmbedding_apply_maximalRealSubfield
    (u : (𝓞 (oMR K))ˣ)
    (w : {w : InfinitePlace (oMR K) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    NumberField.Units.logEmbedding (oMR K)
        (Additive.ofMul u) w =
      Real.log (w.val (u : oMR K)) := by
  rw [NumberField.Units.dirichletUnitTheorem.logEmbedding_component]
  rw [mult_eq_one_of_maximalRealSubfield (K := K)]
  ring
theorem infinitePlace_cyclotomicUnitFamilyKplus_eq
    (j : Fin (NumberField.Units.rank
        (oMR K)))
    (w : InfinitePlace (oMR K))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    w ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
        (𝓞 (oMR K))ˣ) :
        oMR K) =
      ((NumberField.IsCMField.equivInfinitePlace K).symm w)
        (algebraMap (oMR K) K
          ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
            (𝓞 (oMR K))ˣ) :
            oMR K)) := by
  rw [NumberField.IsCMField.equivInfinitePlace_symm_apply]
theorem infinitePlace_cyclotomicUnitFamilyKplus_eq_realCyclotomicUnit
    (j : Fin (NumberField.Units.rank
        (oMR K)))
    (w : InfinitePlace (oMR K))
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    w ((cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j :
        (𝓞 (oMR K))ˣ) :
        oMR K) =
      ((NumberField.IsCMField.equivInfinitePlace K).symm w)
        ((LehmerVandiver.realCyclotomicUnit p K
          ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank
              (K := K)).trans
            (KummerCriterion.units_rank_eq_prime_sub_three_div_two
              (p := p) (K := K)))) + 2) : 𝓞 K) : K) := by
  rw [infinitePlace_cyclotomicUnitFamilyKplus_eq]
  congr 1
  have h := algebraMap_cyclotomicUnitFamilyKplus p K j hp_odd hp_three
  rw [← IsScalarTower.algebraMap_apply
    (𝓞 (oMR K)) (oMR K) K]
  rw [IsScalarTower.algebraMap_apply
    (𝓞 (oMR K)) (𝓞 K) K]
  rw [h]
theorem logEmbedding_cyclotomicUnitFamilyKplus_apply
    (j : Fin (NumberField.Units.rank
        (oMR K)))
    (w : {w : InfinitePlace (oMR K) //
      w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    NumberField.Units.logEmbedding (oMR K)
        (Additive.ofMul (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three j)) w =
      Real.log
        (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
          ((LehmerVandiver.realCyclotomicUnit p K
            ((j.cast ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2) : 𝓞 K) : K)) := by
  rw [logEmbedding_apply_maximalRealSubfield (K := K)]
  congr 1
  exact infinitePlace_cyclotomicUnitFamilyKplus_eq_realCyclotomicUnit p K j w.val hp_odd hp_three
open Classical in
theorem regOfFamily_cyclotomicUnitFamilyKplus_eq_det
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      |(Matrix.of fun (i : {w : InfinitePlace (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : InfinitePlace (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((LehmerVandiver.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (oMR K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))).det| := by
  rw [NumberField.Units.regOfFamily_eq_det']
  congr 1
  congr 1
  funext i
  funext w
  simp only [Matrix.of_apply]
  exact logEmbedding_cyclotomicUnitFamilyKplus_apply p K
    ((NumberField.Units.equivFinRank (oMR K)).symm i)
    w hp_odd hp_three
omit [IsCMField K] in
theorem norm_cyclotomicUnit_mul_zeta_sub_one (k : ℕ) (w : InfinitePlace K) :
    w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) *
        w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1) =
      w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1) := by
  rw [mul_comm, ← map_mul]
  congr 1
  exact_mod_cast LehmerVandiver.zeta_sub_one_mul_cyclotomicUnit p K k
omit [IsCMField K] in
theorem zeta_sub_one_ne_zero_K (hp_two : 2 ≤ p) :
    ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1) ≠ 0 := by
  intro h
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  have h_OK_zero : ((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) - 1 = 0 :=
    h_inj (by simpa [map_sub, map_one] using h)
  exact (IsCyclotomicExtension.zeta_spec p ℚ K).unit'_coe.sub_one_ne_zero (by omega) h_OK_zero
omit [IsCMField K] in
theorem cyclotomicUnit_ne_zero_K
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) ≠ 0 := by
  have hU := LehmerVandiver.isUnit_cyclotomicUnit p K k hk hp_two
  intro h
  apply hU.ne_zero
  have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
    FaithfulSMul.algebraMap_injective (𝓞 K) K
  exact h_inj (by simpa using h)
omit [IsCMField K] in
theorem log_norm_cyclotomicUnit_eq_sub
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) (w : InfinitePlace K) :
    Real.log (w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K)) =
      Real.log
        (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1)) -
        Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1)) := by
  have h_w_cycU : w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) ≠ 0 := by
    refine (InfinitePlace.pos_iff.mpr ?_).ne'
    exact cyclotomicUnit_ne_zero_K p K k hk hp_two
  have h_w_zsub :
      w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1) ≠ 0 := by
    refine (InfinitePlace.pos_iff.mpr ?_).ne'
    exact zeta_sub_one_ne_zero_K p K hp_two
  have h_prod := norm_cyclotomicUnit_mul_zeta_sub_one p K k w
  have h_log_prod : Real.log (w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K)) +
      Real.log
        (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1)) =
        Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1)) := by
    rw [← Real.log_mul h_w_cycU h_w_zsub, h_prod]
  linarith
theorem log_infinitePlace_realCyclotomicUnit
    (k : ℕ) (w : InfinitePlace K) :
    Real.log (w ((LehmerVandiver.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log (w ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K)) := by
  have h_eq : ((LehmerVandiver.realCyclotomicUnit p K k : 𝓞 K) : K) =
      ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) *
        complexConj K ((LehmerVandiver.cyclotomicUnit p K k : 𝓞 K) : K) := by
    unfold LehmerVandiver.realCyclotomicUnit
    push_cast
    rw [← coe_ringOfIntegersComplexConj]
  rw [h_eq, map_mul, infinitePlace_complexConj, ← sq, Real.log_pow]
  ring
theorem log_realCyclotomicUnit_eq_sub_decomp
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p) (w : InfinitePlace K) :
    Real.log (w ((LehmerVandiver.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1)) -
        2 * Real.log
          (w ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1)) := by
  rw [log_infinitePlace_realCyclotomicUnit, log_norm_cyclotomicUnit_eq_sub p K k hk hp_two w]
  ring
theorem log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp
    (k : ℕ) (hk : k.Coprime p) (hp_two : 2 ≤ p)
    (w : InfinitePlace (oMR K)) :
    Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
        ((LehmerVandiver.realCyclotomicUnit p K k : 𝓞 K) : K)) =
      2 * Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
          ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) ^ k - 1)) -
        2 * Real.log (((NumberField.IsCMField.equivInfinitePlace K).symm w)
          ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : 𝓞 K) : K) - 1)) :=
  log_realCyclotomicUnit_eq_sub_decomp p K k hk hp_two
    ((NumberField.IsCMField.equivInfinitePlace K).symm w)
def KummerDirichletDeterminant (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
    (2 : ℝ) ^ ((p - 3) / 2) * (hPlus K : ℝ) * NumberField.Units.regulator
      (oMR K)
theorem sinnottRegulatorIdentity_iff_kummerDirichletDeterminant
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    KummerDirichletDeterminant p K hp_odd hp_three ↔
      SinnottRegulatorIdentity p K hp_odd hp_three :=
  Iff.rfl
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module18

-- Source: KummerCriterion.HMinus.LValueReduction.Factors
section Module19
noncomputable section
open NumberField
namespace KummerCriterion
section Factors
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
def maximalRealSubfieldClassNumberFactor : ℂ :=
  (((((Units.torsionOrder (oMR K) : ℝ) *
      Real.sqrt |discr (oMR K)|) /
    (2 ^ InfinitePlace.nrRealPlaces (oMR K) *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (oMR K) *
        Units.regulator (oMR K)) : ℝ) : ℂ))
lemma hPlus_formula_complex :
    ((hPlus K : ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue (oMR K) : ℝ) : ℂ) *
        maximalRealSubfieldClassNumberFactor (K := K) := by
  simpa [maximalRealSubfieldClassNumberFactor] using congrArg (fun x : ℝ => (x : ℂ))
    (hPlus_formula (K := K))
theorem maximalRealSubfieldClassNumberFactor_eq_explicit (hp_odd' : p ≠ 2) :
    maximalRealSubfieldClassNumberFactor (K := K) =
      (((((2 : ℝ) * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2))) /
        (2 ^ ((p - 1) / 2 : ℕ) * Units.regulator (oMR K)) : ℝ) :
        ℂ)) := by
  rw [maximalRealSubfieldClassNumberFactor]
  congr 1
  rw [maximalRealSubfield_torsionOrder_eq_two (K := K),
    maximalRealSubfield_archimedeanFactor_eq_pow (p := p) (K := K),
    abs_discr_maximalRealSubfield_eq_pow (p := p) (K := K) hp_odd']
  norm_num
theorem hPlus_formula_of_Kplus_residue
    {KplusResidue : ℂ}
    (hresPlus :
      ((NumberField.dedekindZeta_residue (oMR K) : ℝ) : ℂ) =
        KplusResidue) :
    ((hPlus K : ℕ) : ℂ) =
      maximalRealSubfieldClassNumberFactor (K := K) * KplusResidue := by
  rw [hPlus_formula_complex (K := K), hresPlus]
  ring
abbrev cyclotomicHPlusFactor : ℂ :=
  maximalRealSubfieldClassNumberFactor (K := K)
end Factors
end KummerCriterion
end
end Module19

-- Source: KummerCriterion.LValueAtOne.ComplexBounds
section Module20
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p : ℕ) [hp : Fact p.Prime]
lemma zmod_val_div_prime_mem_Ioo {a : ZMod p} (ha : a ≠ 0) :
    (a.val / p : ℝ) ∈ Set.Ioo 0 1 := by
  have hp_pos : 0 < p := hp.out.pos
  have hval_pos : 0 < a.val := by
    by_contra h
    have hval_zero : a.val = 0 := Nat.eq_zero_of_not_pos h
    exact ha <| (ZMod.val_eq_zero a).mp hval_zero
  refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
  · exact div_pos (Nat.cast_pos.mpr hval_pos) (Nat.cast_pos.mpr hp_pos)
  · exact (div_lt_one (Nat.cast_pos.mpr hp_pos)).2 <| Nat.cast_lt.mpr (ZMod.val_lt a)
lemma one_sub_exp_ofReal_mul_I (t : ℝ) :
    (1 : ℂ) - Complex.exp (t * Complex.I) =
      (2 * Real.sin (t / 2) : ℝ) *
        (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I) := by
  calc
    (1 : ℂ) - Complex.exp (t * Complex.I)
        = ((1 - Real.cos t : ℝ) : ℂ) + (-Real.sin t : ℝ) * Complex.I := by
            rw [Complex.exp_ofReal_mul_I]
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ = ((2 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) +
          (-(2 * Real.sin (t / 2) * Real.cos (t / 2)) : ℝ) * Complex.I := by
            rw [show t = 2 * (t / 2) by ring, Real.cos_two_mul, Real.sin_two_mul]
            have hsq : 1 - (2 * Real.cos (t / 2) ^ 2 - 1) = 2 * Real.sin (t / 2) ^ 2 := by
              nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
            rw [hsq]
            ring_nf
    _ = (2 * Real.sin (t / 2) : ℝ) *
          (Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I) := by
            simp [Real.cos_sub_pi_div_two, Real.sin_sub_pi_div_two, sq]
            ring
lemma hasSum_mul_rpow_cos (x r : ℝ) (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    HasSum (fun n : ℕ => (r ^ n / n) * Real.cos (2 * Real.pi * x * n))
      (-Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) := by
  let z : ℂ := (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz : ‖z‖ < 1 := by
    have hexp : ‖Complex.exp (2 * Real.pi * x * Complex.I)‖ = 1 := by
      simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
    have hz' : ‖z‖ = r := by
      calc
        ‖z‖ = ‖(r : ℂ)‖ * ‖Complex.exp (2 * Real.pi * x * Complex.I)‖ := by
          simp [z]
        _ = r * 1 := by rw [Complex.norm_real, Real.norm_of_nonneg hr₀, hexp]
        _ = r := by ring
    rw [hz']
    exact hr₁
  have hsum :
      HasSum (fun n : ℕ => (z ^ n / n).re) (-Complex.log ((1 : ℂ) - z)).re :=
    (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz))
  have hsum' :
      HasSum (fun n : ℕ => (r ^ n / n) * Real.cos (2 * Real.pi * x * n))
        (-Complex.log ((1 : ℂ) - z)).re := by
    refine hsum.congr_fun ?_
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp [z]
    · rw [show z = (r : ℂ) * Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) by simp [z]]
      rw [Complex.div_natCast_re, mul_pow, Complex.mul_re, ← Complex.ofReal_pow,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, ← Complex.exp_nat_mul]
      rw [show (n : ℂ) * ((2 * Real.pi * x : ℝ) * Complex.I) =
          ((2 * Real.pi * x * n : ℝ) : ℂ) * Complex.I by
            norm_num
            ring]
      rw [Complex.exp_ofReal_mul_I_re]
      ring
  have hvalue : (-Complex.log ((1 : ℂ) - z)).re = -Real.log ‖(1 : ℂ) - z‖ := by
    simpa using congrArg Neg.neg (Complex.log_re ((1 : ℂ) - z))
  simpa [hvalue, z] using hsum'
lemma norm_one_sub_exp_ofReal_mul_I {t : ℝ} (ht₀ : 0 < t) (ht₂π : t < 2 * Real.pi) :
    ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖ = 2 * Real.sin (t / 2) := by
  have hs : 0 < 2 * Real.sin (t / 2) := by
    have hhalf : 0 < t / 2 ∧ t / 2 < Real.pi := by
      constructor <;> nlinarith [ht₀, ht₂π, Real.pi_pos]
    have hsin : 0 < Real.sin (t / 2) := Real.sin_pos_of_mem_Ioo hhalf
    positivity
  calc
    ‖(1 : ℂ) - Complex.exp (t * Complex.I)‖
        = ‖((2 * Real.sin (t / 2) : ℝ) : ℂ)‖ *
            ‖Real.cos (t / 2 - Real.pi / 2) + Real.sin (t / 2 - Real.pi / 2) * Complex.I‖ := by
              rw [one_sub_exp_ofReal_mul_I, Complex.norm_mul]
    _ = |2 * Real.sin (t / 2)| * 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          have hunit :
              ‖Real.cos (t / 2 - Real.pi / 2) +
                  Real.sin (t / 2 - Real.pi / 2) * Complex.I‖ = 1 := by
            simpa using Complex.norm_cos_add_sin_mul_I (t / 2 - Real.pi / 2)
          rw [hunit]
    _ = 2 * Real.sin (t / 2) := by rw [abs_of_pos hs, mul_one]
end LValueAtOne
end KummerCriterion
end
end Module20

-- Source: KummerCriterion.LValueAtOne.DirichletBounds
section Module21
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
lemma norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, a i • z i‖ ≤ B * a 0 := by
  have hB : 0 ≤ B := by
    simpa using hbound 0
  rcases n.eq_zero_or_pos with rfl | hn
  · have : 0 ≤ B * a 0 := mul_nonneg hB (ha_nonneg 0)
    simpa using this
  · rw [Finset.sum_range_by_parts (f := a) (g := z) (n := n)]
    have hsum_le :
        ‖∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ ≤
          B * (a 0 - a (n - 1)) := by
      calc
        ‖∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
            ≤ ∑ i ∈ Finset.range (n - 1),
                ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ := by
              simpa using norm_sum_le (Finset.range (n - 1))
                (fun i => (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j)
        _ ≤ ∑ i ∈ Finset.range (n - 1), B * (a i - a (i + 1)) := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hdiff_nonpos : a (i + 1) - a i ≤ 0 := sub_nonpos.mpr (ha (Nat.le_succ i))
              calc
                ‖(a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
                    = |a (i + 1) - a i| * ‖∑ j ∈ Finset.range (i + 1), z j‖ := by
                        rw [norm_smul, Real.norm_eq_abs]
                _ = (a i - a (i + 1)) * ‖∑ j ∈ Finset.range (i + 1), z j‖ := by
                      rw [abs_of_nonpos hdiff_nonpos]
                      ring
                _ ≤ (a i - a (i + 1)) * B := by
                      gcongr
                      · exact sub_nonneg.mpr (ha (Nat.le_succ i))
                      · exact hbound (i + 1)
                _ = B * (a i - a (i + 1)) := by ring
        _ = B * (a 0 - a (n - 1)) := by
              rw [← Finset.mul_sum]
              have htel' := Finset.sum_range_sub (f := a) (n := n - 1)
              have htel : ∑ i ∈ Finset.range (n - 1), (a i - a (i + 1)) = a 0 - a (n - 1) := by
                calc
                  ∑ i ∈ Finset.range (n - 1), (a i - a (i + 1))
                      = ∑ i ∈ Finset.range (n - 1), -((a (i + 1) - a i)) := by
                          refine Finset.sum_congr rfl fun i hi => by ring
                  _ = -∑ i ∈ Finset.range (n - 1), (a (i + 1) - a i) := by
                        rw [Finset.sum_neg_distrib]
                  _ = a 0 - a (n - 1) := by linarith
              rw [htel]
    have hfirst : ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ ≤ B * a (n - 1) := by
      calc
        ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ =
            |a (n - 1)| * ‖∑ i ∈ Finset.range n, z i‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ = a (n - 1) * ‖∑ i ∈ Finset.range n, z i‖ := by
          rw [abs_of_nonneg (ha_nonneg _)]
        _ ≤ a (n - 1) * B := by
          gcongr
          · exact ha_nonneg _
          · exact hbound n
        _ = B * a (n - 1) := by ring
    calc
      ‖a (n - 1) • ∑ i ∈ Finset.range n, z i -
          ∑ i ∈ Finset.range (n - 1),
            (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖
          ≤ ‖a (n - 1) • ∑ i ∈ Finset.range n, z i‖ +
              ‖∑ i ∈ Finset.range (n - 1),
                  (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j‖ := by
              simpa [sub_eq_add_neg] using
                (norm_sub_le (a (n - 1) • ∑ i ∈ Finset.range n, z i)
                  (∑ i ∈ Finset.range (n - 1),
                    (a (i + 1) - a i) • ∑ j ∈ Finset.range (i + 1), z j))
      _ ≤ B * a (n - 1) + B * (a 0 - a (n - 1)) := add_le_add hfirst hsum_le
      _ = B * a 0 := by ring
lemma norm_sum_range_shift_le_of_bounded
    {E : Type*} [NormedAddCommGroup E]
    {z : ℕ → E} {B : ℝ}
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, z (m + i)‖ ≤ 2 * B := by
  have hshift :
      ∑ i ∈ Finset.range n, z (m + i) =
        ∑ i ∈ Finset.range (m + n), z i - ∑ i ∈ Finset.range m, z i := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm, add_left_comm, add_assoc] using (Finset.sum_range_add z m n).symm
  rw [hshift]
  calc
    ‖∑ i ∈ Finset.range (m + n), z i - ∑ i ∈ Finset.range m, z i‖
        ≤ ‖∑ i ∈ Finset.range (m + n), z i‖ + ‖∑ i ∈ Finset.range m, z i‖ := by
            simpa [sub_eq_add_neg] using
              (norm_sub_le (∑ i ∈ Finset.range (m + n), z i) (∑ i ∈ Finset.range m, z i))
    _ ≤ B + B := add_le_add (hbound _) (hbound _)
    _ = 2 * B := by ring
lemma norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℕ → ℝ} {z : ℕ → E} {B : ℝ}
    (ha : Antitone a) (ha_nonneg : ∀ n, 0 ≤ a n)
    (hbound : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (m n : ℕ) :
    ‖∑ i ∈ Finset.range n, a (m + i) • z (m + i)‖ ≤ (2 * B) * a m := by
  simpa [two_mul, add_comm, add_left_comm, add_assoc, mul_add, add_mul, mul_comm, mul_left_comm,
    mul_assoc] using
    (norm_sum_range_smul_le_of_antitone_of_nonneg_of_bounded
      (a := fun k => a (m + k)) (z := fun k => z (m + k)) (B := 2 * B)
      (ha := fun i j hij => ha (Nat.add_le_add_left hij m))
      (ha_nonneg := fun k => ha_nonneg (m + k))
      (hbound := fun k => norm_sum_range_shift_le_of_bounded (z := z) (B := B) hbound m k) n)
end KummerCriterion
end
end Module21

-- Source: KummerCriterion.LValueAtOne.Odd
section Module22
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p : ℕ) [hp : Fact p.Prime]
noncomputable def evenLValueLogSum (χ : DirichletCharacter ℂ p) : ℂ :=
  ∑ a : ZMod p, χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)
noncomputable def evenLValueRhs (χ : DirichletCharacter ℂ p) : ℂ :=
  -(gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ * evenLValueLogSum p χ
end LValueAtOne
end KummerCriterion
noncomputable section
open scoped BigOperators Topology
namespace KummerCriterion
section LValueAtOne
variable (p : ℕ) [hp : Fact p.Prime]
end LValueAtOne
end KummerCriterion
end
end
end Module22

-- Source: KummerCriterion.GaussSum.SignInvariant.BranchChoice
section Module23
noncomputable section
namespace KummerCriterion
section SignInvariant
open scoped BigOperators ComplexConjugate
variable (p : ℕ) [hp : Fact p.Prime]
local instance (α : Sort*) : DecidableEq α := Classical.decEq α
local instance (q : Prop) : Decidable q := Classical.propDecidable q
theorem card_even_characters (hp₂ : p ≠ 2) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 := by
  classical
  let E : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Even
  let O : Finset (DirichletCharacter ℂ p) := Finset.univ.filter fun χ => χ.Odd
  have hdisj : Disjoint E O := by
    refine Finset.disjoint_left.mpr ?_
    intro χ hχE hχO
    have hχ_even : χ.Even := by simpa [E] using hχE
    have hχ_odd : χ.Odd := by simpa [O] using hχO
    exact DirichletCharacter.Odd.not_even χ hχ_odd hχ_even
  have hunion : E ∪ O = (Finset.univ : Finset (DirichletCharacter ℂ p)) := by
    ext χ
    simp only [E, O, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact DirichletCharacter.even_or_odd χ
  have hneg_ne_one : (-1 : ZMod p) ≠ 1 := by
    have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp₂)⟩
    exact ZMod.neg_one_ne_one
  have hsum_zero :
      ∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p) = 0 :=
    DirichletCharacter.sum_characters_eq_zero (R := ℂ) (n := p) hneg_ne_one
  have hsum_split :
      (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) = (E.card : ℂ) - O.card := by
    have hsum_union :
        (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) =
          (E ∪ O).sum (fun χ => χ (-1 : ZMod p)) := by
      rw [hunion]
    have hsum_E : E.sum (fun χ => χ (-1 : ZMod p)) = E.card := by
      calc
        E.sum (fun χ => χ (-1 : ZMod p)) = E.sum (fun _ => (1 : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_even : χ.Even := by simpa [E] using hχ
          simpa [DirichletCharacter.Even] using hχ_even
        _ = E.card := by simp
    have hsum_O : O.sum (fun χ => χ (-1 : ZMod p)) = -(O.card : ℂ) := by
      calc
        O.sum (fun χ => χ (-1 : ZMod p)) = O.sum (fun _ => (-1 : ℂ)) := by
          refine Finset.sum_congr rfl ?_
          intro χ hχ
          have hχ_odd : χ.Odd := by simpa [O] using hχ
          simpa [DirichletCharacter.Odd] using hχ_odd
        _ = -(O.card : ℂ) := by simp
    calc
      (∑ χ : DirichletCharacter ℂ p, χ (-1 : ZMod p)) =
          E.sum (fun χ => χ (-1 : ZMod p)) + O.sum (fun χ => χ (-1 : ZMod p)) := by
            rw [hsum_union, Finset.sum_union hdisj]
      _ = (E.card : ℂ) - O.card := by
            rw [hsum_E, hsum_O]
            simp [sub_eq_add_neg]
  have hbalance : (E.card : ℂ) - O.card = 0 := by
    rw [← hsum_split]
    exact hsum_zero
  have hsame : E.card = O.card := by
    have hsame_real : (E.card : ℝ) = O.card := by
      have hdiff_real : (E.card : ℝ) - O.card = 0 := by
        simpa using congrArg Complex.re hbalance
      nlinarith
    exact_mod_cast hsame_real
  have hcard_total : E.card + O.card = p - 1 := by
    calc
      E.card + O.card = (E ∪ O).card := by
        rw [← Finset.card_union_of_disjoint hdisj]
      _ = Fintype.card (DirichletCharacter ℂ p) := by
        rw [hunion, Finset.card_univ]
      _ = p - 1 := by
        rw [← Nat.card_eq_fintype_card,
          DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
          Nat.totient_prime hp.out]
  have hcardE : E.card = (p - 1) / 2 := by
    omega
  simpa [E] using hcardE
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
variable (p : ℕ) [hp : Fact p.Prime]
noncomputable def localResidueDegreePlus (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  let d := localResidueDegree (p := p) ℓ hℓp
  if Even d then d / 2 else d
noncomputable def localPrimeCountPlus (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  let d := localResidueDegree (p := p) ℓ hℓp
  let c := localPrimeCount (p := p) ℓ hℓp
  if Even d then c else c / 2
lemma localResidueDegreePlus_eq_half {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_even : Even (localResidueDegree (p := p) ℓ hℓp)) :
    localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp / 2 := by
  simp [localResidueDegreePlus, hd_even]
lemma localResidueDegreePlus_eq_self {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_odd : ¬ Even (localResidueDegree (p := p) ℓ hℓp)) :
    localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp := by
  simp [localResidueDegreePlus, hd_odd]
lemma unitOfPrimeNe_pow_localResidueDegreePlus_eq_one_or_neg_one
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p) ^
        localResidueDegreePlus (p := p) ℓ hℓp = 1) ∨
      (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p) ^
        localResidueDegreePlus (p := p) ℓ hℓp = -1) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hsq : (((u : ZMod p) ^ (d / 2)) ^ 2) = 1 := by
      rw [← pow_mul]
      have : (d / 2) * 2 = d := by omega
      rw [this]
      dsimp [d, localResidueDegree]
      change (((u ^ orderOf u : (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one u)
    have hcases : ((u : ZMod p) ^ (d / 2)) = 1 ∨ ((u : ZMod p) ^ (d / 2)) = -1 :=
      sq_eq_one_iff.mp hsq
    have hnot_one : ((u : ZMod p) ^ (d / 2)) ≠ 1 := by
      intro hpow
      have hpow_units : u ^ (d / 2) = 1 := by
        apply Units.ext
        simpa using hpow
      have hdvd : d ∣ d / 2 := by
        simpa [d, localResidueDegree, u] using
          (orderOf_dvd_iff_pow_eq_one (x := u)).2 hpow_units
      have hk_pos : 0 < k := by
        have hd_pos : 0 < d := by
          dsimp [d, localResidueDegree]
          exact orderOf_pos u
        omega
      have hle : 2 * k ≤ k := by
        have hdvd' : 2 * k ∣ k := by
          rw [hk] at hdvd
          rw [show k + k = 2 * k by omega] at hdvd
          simpa using hdvd
        exact Nat.le_of_dvd hk_pos hdvd'
      omega
    rcases hcases with hpow | hpow
    · exact False.elim (hnot_one hpow)
    · right
      simpa [localResidueDegreePlus, d, hk] using hpow
  · left
    have hpow : (u : ZMod p) ^ d = 1 := by
      dsimp [d, localResidueDegree]
      change (((u ^ orderOf u : (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one u)
    simpa [localResidueDegreePlus, d, hd_even] using hpow
lemma orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    orderOf ((unitOfPrimeNe (p := p) ℓ hℓp) ^ 2) =
      localResidueDegreePlus (p := p) ℓ hℓp := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  have hfin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨d, by
      dsimp [d, localResidueDegree]
      exact orderOf_pos u,
      by
        dsimp [d, localResidueDegree]
        exact pow_orderOf_eq_one u⟩
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hd_even' : Even (localResidueDegree (p := p) ℓ hℓp) :=
      ⟨k, by simpa [d] using hk⟩
    have hgcd : d.gcd 2 = 2 := by
      apply Nat.dvd_antisymm
      · exact Nat.gcd_dvd_right d 2
      · exact Nat.dvd_gcd ⟨k, by omega⟩ dvd_rfl
    rw [show orderOf (u ^ 2) = d / d.gcd 2 by
        dsimp [d, localResidueDegree]
        rw [hfin.orderOf_pow], hgcd,
      localResidueDegreePlus_eq_half (p := p) hℓp hd_even']
  · have hd_odd : Odd d := Nat.not_even_iff_odd.mp hd_even
    have hgcd : d.gcd 2 = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hd_odd.coprime_two_right
    rw [show orderOf (u ^ 2) = d / d.gcd 2 by
        dsimp [d, localResidueDegree]
        rw [hfin.orderOf_pow], hgcd,
      localResidueDegreePlus_eq_self (p := p) hℓp (by simpa [d] using hd_even)]
    simp [d]
local instance (α : Sort*) : DecidableEq α := Classical.decEq α
local instance (q : Prop) : Decidable q := Classical.propDecidable q
lemma card_even_characters_kplus (hp_odd' : p ≠ 2) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 :=
  card_even_characters p hp_odd'
lemma card_evenNontrivialCharacters (hp_odd' : p ≠ 2) :
    (evenNontrivialCharacters (p := p)).card = (p - 3) / 2 := by
  classical
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := by
    change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1 : ZMod p) from isUnit_one.neg)]
  have hrewrite :
      evenNontrivialCharacters (p := p) =
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).erase 1 := by
    ext χ
    simp [evenNontrivialCharacters, and_comm]
  rw [hrewrite, Finset.card_erase_of_mem]
  · have hcard_even :
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 :=
      card_even_characters_kplus (p := p) hp_odd'
    omega
  · simp [htriv_even]
lemma localPrimeCountPlus_mul_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp =
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card := by
  classical
  set d := localResidueDegree (p := p) ℓ hℓp with hd
  set c := localPrimeCount (p := p) ℓ hℓp with hc
  have hprod_card : c * d = Nat.card (DirichletCharacter ℂ p) := by
    simpa [c, d] using (localPrimeCount_mul_localResidueDegree (p := p) hℓp)
  have hprod : c * d = p - 1 := by
    rw [hprod_card, card_dirichletCharacter_complex (p := p)]
  have hp_odd_nat : Odd p := hp.out.odd_of_ne_two hp_odd'
  rw [card_even_characters_kplus (p := p) hp_odd']
  rcases hp_odd_nat with ⟨m, hm⟩
  have hhalf : (p - 1) / 2 = m := by
    omega
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hkdiv : (k + k) / 2 = k := by
      omega
    have hlhs :
        localPrimeCountPlus (p := p) ℓ hℓp *
            localResidueDegreePlus (p := p) ℓ hℓp =
          c * k := by
      simp [localPrimeCountPlus, localResidueDegreePlus, d, hk, hkdiv, ← hc]
    have hck : c * k = m := by
      have hdouble : c * k + c * k = m + m := by
        calc
          c * k + c * k = c * (k + k) := by rw [Nat.mul_add]
          _ = p - 1 := by simpa [hk] using hprod
          _ = m + m := by rw [hm]; omega
      have hdouble' : 2 * (c * k) = 2 * m := by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble'
    rw [hlhs, hhalf, hck]
  · have hd_odd : Odd d := Nat.not_even_iff_odd.mp hd_even
    rcases hd_odd with ⟨k, hk⟩
    have hc_even : Even c := by
      have hprod' : c * (2 * k + 1) = p - 1 := by
        simpa [hk] using hprod
      have h_rhs_even : Even (p - 1) := by
        refine ⟨m, ?_⟩
        rw [hm]
        omega
      by_contra hc_not_even
      have hc_odd : Odd c := Nat.not_even_iff_odd.mp hc_not_even
      have hlhs_odd : Odd (c * (2 * k + 1)) :=
        hc_odd.mul ⟨k, rfl⟩
      have h_lhs_even : Even (c * (2 * k + 1)) := by
        simpa [hprod'] using h_rhs_even
      exact (Nat.not_even_iff_odd.mpr hlhs_odd) h_lhs_even
    rcases hc_even with ⟨j, hj⟩
    have hc_half : localPrimeCount (p := p) ℓ hℓp / 2 = j := by
      rw [← hc, hj]
      simpa [two_mul, Nat.mul_comm] using (Nat.mul_div_right j (by decide : 0 < 2))
    have hlhs :
        localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp =
          j * (2 * k + 1) := by
      simp [localPrimeCountPlus, localResidueDegreePlus, d, hk, hc_half]
    have hjk : j * (2 * k + 1) = m := by
      have hdouble : j * (2 * k + 1) + j * (2 * k + 1) = m + m := by
        calc
          j * (2 * k + 1) + j * (2 * k + 1) = (j + j) * (2 * k + 1) := by
            rw [Nat.add_mul]
          _ = p - 1 := by simpa [hj, hk] using hprod
          _ = m + m := by rw [hm]; omega
      have hdouble' : 2 * (j * (2 * k + 1)) = 2 * m := by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble'
    rw [hlhs, hhalf, hjk]
lemma prod_even_characters_eval_eq_pow_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (T : ℂ) :
    Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
      (fun χ => (1 - χ (ℓ : ZMod p) * T)) =
      (1 - T ^ localResidueDegreePlus (p := p) ℓ hℓp) ^
        localPrimeCountPlus (p := p) ℓ hℓp := by
  classical
  let E : Finset (DirichletCharacter ℂ p) :=
    Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even
  set n := Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units : Fintype.card (ZMod p)ˣ = n := by
    rw [hn_def, card_dirichletCharacter_complex (p := p), ZMod.card_units]
  have hn_units' : Nat.card (ZMod p)ˣ = n := by
    rw [Nat.card_eq_fintype_card, hn_units]
  have hn_pos : 0 < n := by
    rw [← hn_units]
    exact Fintype.card_pos
  have hp_odd_nat : Odd p := hp.out.odd_of_ne_two hp_odd'
  have hn_even : Even n := by
    rcases hp_odd_nat with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hn_def, card_dirichletCharacter_complex (p := p), hm]
    omega
  rcases hn_even with ⟨n2, hn2⟩
  have hn2' : n = 2 * n2 := by
    omega
  have hn2_pos : 0 < n2 := by
    omega
  have hnp1 : n = p - 1 := by
    rw [hn_def, card_dirichletCharacter_complex (p := p)]
  obtain ⟨g, hg_mon⟩ : ∃ g : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon' : ∀ x : (ZMod p)ˣ, ∃ m : ℕ, g ^ m = x := fun x => hg_mon x
  obtain ⟨a, ha⟩ := hg_mon' (unitOfPrimeNe (p := p) ℓ hℓp)
  have hg_zpow : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := fun x => by
    obtain ⟨m, hm⟩ := hg_mon' x
    refine ⟨(m : ℤ), ?_⟩
    change g ^ (m : ℤ) = x
    rw [zpow_natCast]
    exact hm
  have hg_order : orderOf g = n := by
    rw [← hn_units']
    exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hfin_g : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n, hn_pos, by rw [← hg_order]; exact pow_orderOf_eq_one g⟩
  have hgcd2 : n.gcd 2 = 2 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right n 2) (Nat.dvd_gcd ⟨n2, hn2'⟩ dvd_rfl)
  have hω : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hω_unit : IsUnit ω := hω.isUnit hn_pos.ne'
  set ωu : ℂˣ := hω_unit.unit with hωu_def
  have hωu_val : (ωu : ℂ) = ω := by simp [hωu_def]
  have hωu_roots : ∀ k : ℕ, (ωu ^ k : ℂˣ) ∈ rootsOfUnity n ℂ := by
    intro k
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm]
    have h1 : (ωu ^ n : ℂˣ) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one, hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul, h1, one_pow]
  let χAt : ℕ → DirichletCharacter ℂ p := fun k =>
    MulChar.ofRootOfUnity (M := ZMod p) (R := ℂ) (ζ := ωu ^ k)
      (by rw [hn_units]; exact hωu_roots k) hg_zpow
  have hχAt_g : ∀ k : ℕ, χAt k ((g : (ZMod p)ˣ) : ZMod p) = ω ^ k := fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val, hωu_val]
  have hℓ_eq : (ℓ : ZMod p) = (((g : (ZMod p)ˣ) : ZMod p)) ^ a := by
    have h1 : (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p)) = (ℓ : ZMod p) := by
      simp [unitOfPrimeNe]
    rw [← h1, ← ha, Units.val_pow_eq_pow_val]
  have hχAt_ℓ : ∀ k : ℕ, χAt k (ℓ : ZMod p) = ω ^ (k * a) := fun k => by
    rw [hℓ_eq, map_pow, hχAt_g, ← pow_mul]
  have hg_half_sq : ((((g : (ZMod p)ˣ) : ZMod p) ^ n2) ^ 2) = 1 := by
    rw [← pow_mul]
    have : n2 * 2 = n := by
      omega
    rw [this]
    simpa [Units.val_pow_eq_pow_val, hg_order] using
      congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one g)
  have hg_half_ne_one : (((g : (ZMod p)ˣ) : ZMod p) ^ n2) ≠ 1 := by
    intro hpow
    have hpow_units : g ^ n2 = 1 := by
      apply Units.ext
      simpa using hpow
    have hdvd : n ∣ n2 := by
      rw [← hg_order]
      exact (orderOf_dvd_iff_pow_eq_one (x := g)).2 hpow_units
    have hle : n ≤ n2 := Nat.le_of_dvd hn2_pos hdvd
    rw [hn2] at hle
    omega
  have hg_half_eq_neg_one : (((g : (ZMod p)ˣ) : ZMod p) ^ n2) = -1 := by
    rcases sq_eq_one_iff.mp hg_half_sq with h1 | h1
    · exact False.elim (hg_half_ne_one h1)
    · exact h1
  let χEvenAt : ℕ → DirichletCharacter ℂ p := fun k => χAt (2 * k)
  have hχEven_mem : ∀ k ∈ Finset.range n2, χEvenAt k ∈ E := by
    intro k hk
    have h_even : χAt (2 * k) (-1 : ZMod p) = 1 := by
      rw [← hg_half_eq_neg_one, map_pow, hχAt_g, ← pow_mul]
      have : (2 * k) * n2 = k * n := by
        rw [hn2']
        simp [Nat.mul_left_comm, Nat.mul_comm]
      rw [this, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    change χAt (2 * k) ∈ E
    rw [show E = Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even) from rfl,
      Finset.mem_filter]
    simp [DirichletCharacter.Even, h_even]
  have hχEven_inj : Set.InjOn χEvenAt ↑(Finset.range n2) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have hval : χEvenAt j ((g : (ZMod p)ˣ) : ZMod p) = χEvenAt k ((g : (ZMod p)ˣ) : ZMod p) :=
      congrArg (fun χ : DirichletCharacter ℂ p => χ ((g : (ZMod p)ˣ) : ZMod p)) hjk
    rw [hχAt_g, hχAt_g] at hval
    have hj2 : 2 * j < n := by
      omega
    have hk2 : 2 * k < n := by
      omega
    have h_eq : 2 * j = 2 * k := by
      simpa [χEvenAt] using hω.pow_inj hj2 hk2 hval
    omega
  have hE_card : E.card = n2 := by
    rw [card_even_characters_kplus (p := p) hp_odd']
    omega
  have himage_eq : Finset.image χEvenAt (Finset.range n2) = E := by
    apply Finset.eq_of_subset_of_card_le
    · intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨k, hk, rfl⟩
      exact hχEven_mem k hk
    · rw [hE_card, Finset.card_image_of_injOn hχEven_inj, Finset.card_range]
  have hprod_transfer :
      ∏ χ ∈ E, (1 - χ (ℓ : ZMod p) * T) =
        ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) := by
    calc
      ∏ χ ∈ E, (1 - χ (ℓ : ZMod p) * T)
          = ∏ χ ∈ Finset.image χEvenAt (Finset.range n2), (1 - χ (ℓ : ZMod p) * T) := by
              rw [← himage_eq]
      _ = ∏ k ∈ Finset.range n2, (1 - χEvenAt k (ℓ : ZMod p) * T) := by
            rw [Finset.prod_image hχEven_inj]
      _ = ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) := by
            refine Finset.prod_congr rfl (fun k _ => ?_)
            simpa [χEvenAt] using congrArg (fun z : ℂ => 1 - z * T) (hχAt_ℓ (2 * k))
  have hω_sq_prim' : IsPrimitiveRoot (ω ^ 2) (n / n.gcd 2) :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn_pos 2 hω
  have hω_sq_prim : IsPrimitiveRoot (ω ^ 2) n2 := by
    simpa [hgcd2, hn2'] using hω_sq_prim'
  have hcollapse :
      ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) =
        (1 - T ^ (n2 / n2.gcd a)) ^ n2.gcd a := by
    calc
      ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T)
          = ∏ k ∈ Finset.range n2, (1 - (ω ^ 2) ^ (k * a) * T) := by
              refine Finset.prod_congr rfl (fun k _ => ?_)
              congr 1
              have hexp : (2 * k) * a = 2 * (k * a) := by
                simp [Nat.mul_assoc, Nat.mul_comm]
              rw [hexp, pow_mul]
      _ = (1 - T ^ (n2 / n2.gcd a)) ^ n2.gcd a :=
            prod_pow_primRoot_eq_pow hn2_pos a hω_sq_prim T
  have hfin_g2 : IsOfFinOrder (g ^ 2) := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n2, hn2_pos, by
      rw [← pow_mul]
      have : 2 * n2 = n := by
        omega
      rw [this, ← hg_order]
      exact pow_orderOf_eq_one g⟩
  have hg_sq_order : orderOf (g ^ 2) = n2 := by
    rw [hfin_g.orderOf_pow, hg_order, hgcd2, hn2']
    simp
  have hu_sq : (unitOfPrimeNe (p := p) ℓ hℓp) ^ 2 = (g ^ 2) ^ a := by
    rw [← ha, ← pow_mul]
    have : a * 2 = 2 * a := by
      omega
    rw [this, pow_mul]
  have horder_u_sq : orderOf ((unitOfPrimeNe (p := p) ℓ hℓp) ^ 2) = n2 / n2.gcd a := by
    rw [hu_sq, hfin_g2.orderOf_pow, hg_sq_order]
  have hlocalResidue :
      localResidueDegreePlus (p := p) ℓ hℓp = n2 / n2.gcd a := by
    rw [← orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus (p := p) hℓp, horder_u_sq]
  have hlocalResiduePlus_pos : 0 < localResidueDegreePlus (p := p) ℓ hℓp := by
    rw [← orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus (p := p) hℓp]
    exact orderOf_pos _
  have hlocalResidue_pos : 0 < n2 / n2.gcd a := by
    simpa [hlocalResidue] using hlocalResiduePlus_pos
  have hcount_mul : localPrimeCountPlus (p := p) ℓ hℓp * (n2 / n2.gcd a) = n2 := by
    have hbase := localPrimeCountPlus_mul_localResidueDegreePlus (p := p) hp_odd' hℓp
    rw [hlocalResidue] at hbase
    simpa [E, hE_card] using hbase
  have hgcd_mul : n2.gcd a * (n2 / n2.gcd a) = n2 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left n2 a)
  have hlocalPrimeCount :
      localPrimeCountPlus (p := p) ℓ hℓp = n2.gcd a := by
    have hmul :
        (n2 / n2.gcd a) * localPrimeCountPlus (p := p) ℓ hℓp =
          (n2 / n2.gcd a) * (n2.gcd a) := by
      rw [Nat.mul_comm (n2 / n2.gcd a) (localPrimeCountPlus (p := p) ℓ hℓp),
        Nat.mul_comm (n2 / n2.gcd a) (n2.gcd a), hcount_mul, hgcd_mul]
    exact Nat.eq_of_mul_eq_mul_left hlocalResidue_pos hmul
  simpa [E] using
    (Eq.trans hprod_transfer (Eq.trans hcollapse (by rw [← hlocalResidue, ← hlocalPrimeCount])))
lemma trivial_mul_evenCharLocalFactor_eq_pow_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) {s : ℂ} :
    (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s =
      (1 - (ℓ : ℂ) ^ (-((localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s))) ^
        localPrimeCountPlus (p := p) ℓ hℓp := by
  classical
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := by
    change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1 : ZMod p) from isUnit_one.neg)]
  have hrewrite :
      evenNontrivialCharacters (p := p) =
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).erase 1 := by
    ext χ
    simp [evenNontrivialCharacters, and_comm]
  have htrivial_mul :
      (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s =
        Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
          (fun χ => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))) := by
    unfold evenCharLocalFactor
    rw [hrewrite, ← Finset.mul_prod_erase
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
      (fun χ : DirichletCharacter ℂ p => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s)))]
    · have hℓ_unit : IsUnit ((ℓ : ZMod p)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (coprime_of_prime_ne (p := p) hℓp).symm
      rw [MulChar.one_apply hℓ_unit, one_mul]
    · simp [htriv_even]
  calc
    (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s
        = Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
            (fun χ => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))) := htrivial_mul
    _ =
        (1 - (((ℓ : ℂ) ^ (-s)) ^ localResidueDegreePlus (p := p) ℓ hℓp)) ^
          localPrimeCountPlus (p := p) ℓ hℓp := by
            simpa using
              prod_even_characters_eval_eq_pow_localResidueDegreePlus (p := p) hp_odd' hℓp
                ((ℓ : ℂ) ^ (-s))
    _ =
        (1 - (ℓ : ℂ) ^ (-((localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s))) ^
          localPrimeCountPlus (p := p) ℓ hℓp := by
            congr 1
            congr 1
            rw [show ((ℓ : ℂ) ^ (-s)) ^ localResidueDegreePlus (p := p) ℓ hℓp =
                (ℓ : ℂ) ^ ((-s) * ((localResidueDegreePlus (p := p) ℓ hℓp : ℕ) : ℂ)) by
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
variable (p : ℕ) [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
noncomputable def primesOverFinsetPlus (ℓ : ℕ) : Finset (Ideal (𝓞 ((oMR K)))) :=
  IsDedekindDomain.primesOverFinset (rationalPrimeIdeal ℓ) (𝓞 ((oMR K)))
lemma primesOverFinsetPlus_card_eq_ncard (ℓ : ℕ) [Fact ℓ.Prime] :
    (primesOverFinsetPlus (K := K) ℓ).card =
      (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K)))).ncard := by
  classical
  have : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  unfold primesOverFinsetPlus
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset hne]
lemma mem_primesOverFinsetPlus_iff {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 ((oMR K)))} :
    P ∈ primesOverFinsetPlus (K := K) ℓ ↔
      P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K))) := by
  have : (rationalPrimeIdeal ℓ).IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  exact IsDedekindDomain.mem_primesOverFinset_iff hne (𝓞 ((oMR K)))
lemma under_mem_primesOverFinsetPlus {ℓ : ℕ} [Fact ℓ.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOverFinset K ℓ) :
    P.under (𝓞 ((oMR K))) ∈ primesOverFinsetPlus (K := K) ℓ := by
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  have : P.IsPrime := hP_over.1
  rw [mem_primesOverFinsetPlus_iff]
  refine ⟨Ideal.IsPrime.under (𝓞 ((oMR K))) P, ?_⟩
  rw [Ideal.liesOver_iff, Ideal.under_under]
  exact (Ideal.liesOver_iff _ _).1 hP_over.2
variable [IsCMField K]
lemma algEquiv_eq_one_or_complexConj (σ : K ≃ₐ[(oMR K)] K) :
    σ = 1 ∨ σ = complexConj K := by
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  · right
    have hcard : Nat.card (K ≃ₐ[(oMR K)] K) = 2 :=
      (IsGalois.card_aut_eq_finrank (oMR K) K).trans (finrank_K_over_Kplus (K := K))
    rw [Nat.card_eq_two_iff' (1 : K ≃ₐ[(oMR K)] K)] at hcard
    exact ExistsUnique.unique hcard hσ (complexConj_ne_one K)
lemma toRingHom_complexConj_eq_ringOfIntegersComplexConj :
    MulSemiringAction.toRingHom (K ≃ₐ[(oMR K)] K) (𝓞 K) (complexConj K) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  ext x
  change (((complexConj K) • x : 𝓞 K) : K) = ((ringOfIntegersComplexConj K x : 𝓞 K) : K)
  rfl
lemma pointwise_smul_complexConj_eq_map (P : Ideal (𝓞 K)) :
    complexConj K • P = P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  rw [Ideal.pointwise_smul_def, toRingHom_complexConj_eq_ringOfIntegersComplexConj (K := K)]
lemma map_ringOfIntegersComplexConj_mem_primesOverFinset {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ∈ primesOverFinset K ℓ := by
  let PPlus : Ideal (𝓞 ((oMR K))) := P.under (𝓞 ((oMR K)))
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  have hPPlus_mem : PPlus ∈ primesOverFinsetPlus (K := K) ℓ := by
    simpa [PPlus] using under_mem_primesOverFinsetPlus (K := K) hP
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K))) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hPPlus_mem
  have : P.IsPrime := hP_over.1
  have hmap_liesOver_PPlus :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus :=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus_over.2
  have hmap_liesOver :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver
        (rationalPrimeIdeal ℓ) :=
    Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 ((oMR K))) (C := 𝓞 K)
      (𝔓 := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (P := PPlus) (p := rationalPrimeIdeal ℓ)
  have : (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).IsPrime :=
    Ideal.map_isPrime_of_equiv (ringOfIntegersComplexConj K).toRingEquiv
  rw [mem_primesOverFinset_iff (K := K) (ℓ := ℓ)]
  exact ⟨inferInstance, hmap_liesOver⟩
lemma under_map_ringOfIntegersComplexConj_eq_under (P : Ideal (𝓞 K)) :
    (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).under (𝓞 ((oMR K))) =
      P.under (𝓞 ((oMR K))) := by
  let PPlus : Ideal (𝓞 ((oMR K))) := P.under (𝓞 ((oMR K)))
  have hmap_liesOver_PPlus :
      (P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom).LiesOver PPlus :=
    Ideal.LiesOver.of_eq_map_equiv PPlus (ringOfIntegersComplexConj K) rfl
  simpa [PPlus] using
    (Ideal.over_def
      (P := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
      (A := 𝓞 ((oMR K))) (p := PPlus)).symm
lemma eq_or_eq_map_ringOfIntegersComplexConj_of_under_eq {ℓ : ℕ} [Fact ℓ.Prime]
    {P Q : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) (hQ : Q ∈ primesOverFinset K ℓ)
    (hunder : P.under (𝓞 ((oMR K))) = Q.under (𝓞 ((oMR K)))) :
    Q = P ∨ Q = P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  let PPlus : Ideal (𝓞 ((oMR K))) := P.under (𝓞 ((oMR K)))
  have hP_over : P ∈ Ideal.primesOver PPlus (𝓞 K) := by
    refine ⟨((mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP).1,
      by simp [Ideal.liesOver_iff, PPlus]⟩
  have hQ_over : Q ∈ Ideal.primesOver PPlus (𝓞 K) := by
    refine ⟨((mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hQ).1,
      by simpa [Ideal.liesOver_iff, PPlus] using hunder⟩
  have : P.IsPrime := hP_over.1
  have : Q.IsPrime := hQ_over.1
  have : Q.LiesOver PPlus := hQ_over.2
  let _ : MulSemiringAction Gal(K/(oMR K)) (𝓞 K) := inferInstance
  have _ : IsGaloisGroup Gal(K/(oMR K)) (𝓞 ((oMR K))) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/(oMR K))) (𝓞 ((oMR K))) (𝓞 K) ((oMR K)) K
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup
    (A := 𝓞 ((oMR K))) (B := 𝓞 K) (p := PPlus) (P := P) (Q := Q) (G := Gal(K/(oMR K)))
  rcases algEquiv_eq_one_or_complexConj (K := K) σ with rfl | rfl
  · left
    simpa using hσ.symm
  · right
    rw [pointwise_smul_complexConj_eq_map (K := K) P] at hσ
    exact hσ.symm
lemma primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    let Pconj := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
    let fiber := (primesOverFinset K ℓ).filter
      (fun Q => Q.under (𝓞 ((oMR K))) = P.under (𝓞 ((oMR K))))
    (Pconj = P ∧ fiber = ({P} : Finset (Ideal (𝓞 K)))) ∨
      (Pconj ≠ P ∧ fiber = {P, Pconj}) := by
  classical
  let Pconj : Ideal (𝓞 K) := P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q => Q.under (𝓞 ((oMR K))) = P.under (𝓞 ((oMR K))))
  have hPconj : Pconj ∈ primesOverFinset K ℓ := by
    simpa [Pconj] using map_ringOfIntegersComplexConj_mem_primesOverFinset (K := K) hP
  have hunder_conj : Pconj.under (𝓞 ((oMR K))) = P.under (𝓞 ((oMR K))) := by
    simpa [Pconj] using under_map_ringOfIntegersComplexConj_eq_under (K := K) P
  have hP_fiber : P ∈ fiber := by
    simp [fiber, hP]
  have hPconj_fiber : Pconj ∈ fiber := by
    simp [fiber, hPconj, hunder_conj]
  have hfiber_subset {Q : Ideal (𝓞 K)} (hQ : Q ∈ fiber) : Q = P ∨ Q = Pconj := by
    have hQ_mem : Q ∈ primesOverFinset K ℓ := (Finset.mem_filter.1 hQ).1
    have hQ_under : Q.under (𝓞 ((oMR K))) = P.under (𝓞 ((oMR K))) := (Finset.mem_filter.1 hQ).2
    rcases eq_or_eq_map_ringOfIntegersComplexConj_of_under_eq (K := K) hP hQ_mem hQ_under.symm with
      hQP | hQconj
    · exact Or.inl hQP
    · exact Or.inr (by simpa [Pconj] using hQconj)
  by_cases hfix : Pconj = P
  · left
    refine ⟨hfix, Finset.ext fun Q => ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj, hfix]
        simp
    · intro hQ
      have hQP : Q = P := by simpa using hQ
      subst hQP
      exact hP_fiber
  · right
    refine ⟨hfix, Finset.ext fun Q => ?_⟩
    constructor
    · intro hQ
      rcases hfiber_subset hQ with hQP | hQconj
      · rw [hQP]
        simp
      · rw [hQconj]
        simp [Pconj]
    · intro hQ
      have hQ' : Q = P ∨ Q = Pconj := by
        simpa [hfix] using! hQ
      rcases hQ' with hQP | hQconj
      · rw [hQP]
        exact hP_fiber
      · rw [hQconj]
        exact hPconj_fiber
noncomputable def complexConjRat (hp_odd : p ≠ 2) : Gal(K/ℚ) := by
  letI : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  exact
    { (complexConj K).toRingEquiv with
      commutes' := fun q => by
        exact map_ratCast ((complexConj K).toRingEquiv.toRingHom) q }
@[simp] private lemma complexConjRat_apply (hp_odd : p ≠ 2) (x : K) :
    complexConjRat (p := p) (K := K) hp_odd x = complexConj K x := by
  rfl
lemma toRingHom_complexConjRat_eq_ringOfIntegersComplexConj (hp_odd : p ≠ 2) :
    MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K)
        (complexConjRat (p := p) (K := K) hp_odd) =
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  ext x
  change complexConjRat (p := p) (K := K) hp_odd x =
      ((ringOfIntegersComplexConj K x : 𝓞 K) : K)
  simp [complexConjRat_apply, coe_ringOfIntegersComplexConj]
lemma pointwise_smul_complexConjRat_eq_map (hp_odd : p ≠ 2) (P : Ideal (𝓞 K)) :
    (complexConjRat (p := p) (K := K) hp_odd • P) =
      P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom := by
  rw [Ideal.pointwise_smul_def, toRingHom_complexConjRat_eq_ringOfIntegersComplexConj
    (p := p) (K := K) hp_odd]
omit [IsCMField K] in
lemma galEquivZMod_complexConj_eq_neg_one (hp_odd : p ≠ 2) :
    IsCyclotomicExtension.Rat.galEquivZMod p K
        (complexConjRat (p := p) (K := K) hp_odd) = -1 := by
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  have hζ := IsCyclotomicExtension.zeta_spec p ℚ K
  have hc :
      c (IsCyclotomicExtension.zeta p ℚ K) =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    have hc' := congrArg (fun x : 𝓞 K => (x : K)) (complexConj_apply_zeta (p := p) (K := K))
    rw [coe_ringOfIntegersComplexConj] at hc'
    change (complexConj K) hζ.toInteger.1 =
      hζ.toInteger.1 ^ (p - 1) at hc'
    simpa [c, complexConjRat_apply, hζ.coe_toInteger] using hc'
  have hpow :
      (IsCyclotomicExtension.zeta p ℚ K) ^
          (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val =
        (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := by
    calc
      (IsCyclotomicExtension.zeta p ℚ K) ^ (IsCyclotomicExtension.Rat.galEquivZMod p K c).val.val
          = c (IsCyclotomicExtension.zeta p ℚ K) := by
              symm
              exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
                (n := p) (K := K) c hζ.pow_eq_one
      _ = (IsCyclotomicExtension.zeta p ℚ K) ^ (p - 1) := hc
  apply Units.ext
  have hpow' := hpow
  rw [(hζ.isOfFinOrder (NeZero.ne p)).pow_inj_mod, ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, Nat.cast_sub hp.out.one_le,
    ZMod.natCast_self, zero_sub, Nat.cast_one] at hpow'
  simpa [c] using hpow'
lemma unitOfPrimeNe_pow_localResidueDegreePlus_eq_neg_one_of_even
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_even : Even (localResidueDegree (p := p) ℓ hℓp)) :
    unitOfPrimeNe (p := p) ℓ hℓp ^ localResidueDegreePlus (p := p) ℓ hℓp =
      (-1 : (ZMod p)ˣ) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  rcases unitOfPrimeNe_pow_localResidueDegreePlus_eq_one_or_neg_one (p := p) hℓp with hpow | hpow
  · have hpow_units : u ^ localResidueDegreePlus (p := p) ℓ hℓp = 1 := by
      apply Units.ext
      simpa [u, Units.val_pow_eq_pow_val] using hpow
    have hdvd : d ∣ localResidueDegreePlus (p := p) ℓ hℓp := by
      simpa [d, localResidueDegree, u] using (orderOf_dvd_iff_pow_eq_one (x := u)).2 hpow_units
    have hd_pos : 0 < d := by
      dsimp [d, localResidueDegree, u]
      exact orderOf_pos u
    have hhalf : localResidueDegreePlus (p := p) ℓ hℓp = d / 2 := by
      simpa [d] using localResidueDegreePlus_eq_half (p := p) hℓp hd_even
    have hhalf_pos : 0 < d / 2 := by
      rcases hd_even with ⟨k, hk⟩
      rw [show d = 2 * k by omega]
      omega
    have hle : d ≤ d / 2 := by
      rw [hhalf] at hdvd
      exact Nat.le_of_dvd hhalf_pos hdvd
    omega
  · apply Units.ext
    simpa [u, Units.val_pow_eq_pow_val] using hpow
lemma neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (-1 : (ZMod p)ˣ) ∈ Subgroup.zpowers (unitOfPrimeNe (p := p) ℓ hℓp) ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  constructor
  · intro hneg
    have htwo : 2 ∣ orderOf u := by
      have horder_neg : orderOf (-1 : (ZMod p)ˣ) = 2 := by
        rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod p) p,
          if_neg hp_odd]
      exact horder_neg ▸ orderOf_dvd_of_mem_zpowers hneg
    simpa [u, localResidueDegree, even_iff_two_dvd] using htwo
  · intro hd_even
    refine Subgroup.mem_zpowers_iff.mpr ⟨localResidueDegreePlus (p := p) ℓ hℓp, ?_⟩
    rw [zpow_natCast]
    exact unitOfPrimeNe_pow_localResidueDegreePlus_eq_neg_one_of_even (p := p) hℓp hd_even
omit [IsCMField K] in
lemma complexConjRat_mem_stabilizer_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    (complexConjRat (p := p) (K := K) hp_odd ∈ MulAction.stabilizer Gal(K/ℚ) P) ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hP
  have : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hP_over.2
  have : (rationalPrimeIdeal ℓ).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime ℓ
  have : P.IsMaximal := Ideal.isMaximal_of_mem_primesOver hP_over
  constructor
  · intro hc
    have hmem_map : IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := ⟨c, hc, rfl⟩
    rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n := p) (K := K) (p := ℓ) (P := P)
      ((coprime_of_prime_ne (p := p) hℓp).symm), galEquivZMod_complexConj_eq_neg_one
      (p := p) (K := K) hp_odd] at hmem_map
    simpa [unitOfPrimeNe] using
      (neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree
        (p := p) hp_odd hℓp).1 hmem_map
  · intro h_even
    have hneg_mem : (-1 : (ZMod p)ˣ) ∈ Subgroup.zpowers (unitOfPrimeNe (p := p) ℓ hℓp) :=
      (neg_one_mem_zpowers_unitOfPrimeNe_iff_even_localResidueDegree (p := p) hp_odd hℓp).2 h_even
    have hmem_map : IsCyclotomicExtension.Rat.galEquivZMod p K c ∈
        (IsCyclotomicExtension.Rat.galEquivZMod p K).mapSubgroup
          (MulAction.stabilizer Gal(K/ℚ) P) := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_stabilizer (n := p) (K := K) (p := ℓ) (P := P)
        ((coprime_of_prime_ne (p := p) hℓp).symm), galEquivZMod_complexConj_eq_neg_one
        (p := p) (K := K) hp_odd]
      simpa [unitOfPrimeNe] using hneg_mem
    rcases hmem_map with ⟨σ, hσ, hσeq⟩
    have hc_eq : σ = c := (IsCyclotomicExtension.Rat.galEquivZMod p K).injective hσeq
    subst hc_eq
    exact hσ
lemma map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P ↔
      Even (localResidueDegree (p := p) ℓ hℓp) := by
  let c : Gal(K/ℚ) := complexConjRat (p := p) (K := K) hp_odd
  constructor
  · intro hmap
    have hsmul : c • P = P := by
      rw [pointwise_smul_complexConjRat_eq_map (p := p) (K := K) hp_odd]
      exact hmap
    have hc : c ∈ MulAction.stabilizer Gal(K/ℚ) P := by simpa [c] using hsmul
    exact (complexConjRat_mem_stabilizer_iff_even_localResidueDegree
      (p := p) (K := K) hp_odd hℓp hP).1 hc
  · intro h_even
    have hc : c ∈ MulAction.stabilizer Gal(K/ℚ) P :=
      (complexConjRat_mem_stabilizer_iff_even_localResidueDegree
        (p := p) (K := K) hp_odd hℓp hP).2 h_even
    have hsmul : c • P = P := by simpa [c] using hc
    rw [pointwise_smul_complexConjRat_eq_map (p := p) (K := K) hp_odd] at hsmul
    exact hsmul
lemma map_ringOfIntegersComplexConj_eq_self_iff_localResidueDegreePlus_eq_half
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ) :
    P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P ↔
      localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp / 2 := by
  rw [map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
    (p := p) (K := K) hp_odd hℓp hP]
  constructor
  · exact localResidueDegreePlus_eq_half (p := p) hℓp
  · intro hhalf
    by_contra hodd
    have hself := localResidueDegreePlus_eq_self (p := p) hℓp hodd
    have hpos : 0 < localResidueDegree (p := p) ℓ hℓp := by
      unfold localResidueDegree unitOfPrimeNe
      exact orderOf_pos _
    rw [hself] at hhalf
    omega
omit [IsCMField K] in
lemma primesOverFinsetContractionToPlus_fiber_card_eq_ncard_primesOver {ℓ : ℕ} [Fact ℓ.Prime]
    {P : Ideal (𝓞 K)} (hP : P ∈ primesOverFinset K ℓ)
    {PPlus : Ideal (𝓞 ((oMR K)))} (hPPlus : P.under (𝓞 ((oMR K))) = PPlus) :
    let fiber := (primesOverFinset K ℓ).filter
      (fun Q => Q.under (𝓞 ((oMR K))) = PPlus)
    fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard := by
  classical
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q => Q.under (𝓞 ((oMR K))) = PPlus)
  have hPPlus_mem : PPlus ∈ primesOverFinsetPlus (K := K) ℓ := by
    simpa [hPPlus] using under_mem_primesOverFinsetPlus (K := K) hP
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K))) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hPPlus_mem
  have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus_over.2
  have hfiber : (↑fiber : Set (Ideal (𝓞 K))) = Ideal.primesOver PPlus (𝓞 K) := by
    ext Q
    constructor
    · intro hQ
      rw [Finset.mem_coe, Finset.mem_filter] at hQ
      rcases hQ with ⟨hQ_fin, hQ_under⟩
      have hQ_over : Q ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) :=
        (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).1 hQ_fin
      have : Q.IsPrime := hQ_over.1
      exact ⟨inferInstance, (Ideal.liesOver_iff _ _).2 hQ_under.symm⟩
    · intro hQ
      have : Q.IsPrime := hQ.1
      have : Q.LiesOver PPlus := hQ.2
      have hQ_over : Q.LiesOver (rationalPrimeIdeal ℓ) :=
        Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 ((oMR K))) (C := 𝓞 K)
          (𝔓 := Q) (P := PPlus) (p := rationalPrimeIdeal ℓ)
      have hQ_fin : Q ∈ primesOverFinset K ℓ := by
        rw [mem_primesOverFinset_iff (K := K) (ℓ := ℓ)]
        exact ⟨inferInstance, hQ_over⟩
      have hQ_under : Q.under (𝓞 ((oMR K))) = PPlus :=
        ((Ideal.liesOver_iff _ _).1 (show Q.LiesOver PPlus from inferInstance)).symm
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hQ_fin, hQ_under⟩
  simpa [fiber] using (show fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard from by
    rw [← Set.ncard_coe_finset, hfiber])
omit [IsCMField K] in
lemma primesOver_inertiaDeg_eq_localResidueDegreePlus
    (hp_odd : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (PPlus : Ideal (𝓞 ((oMR K))))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K)))) :
    PPlus.inertiaDeg ℤ = localResidueDegreePlus (p := p) ℓ hℓp := by
  classical
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have : PPlus.IsPrime := hPPlus.1
  have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus.2
  obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
    refine ⟨hP_prime, ?_⟩
    exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 ((oMR K))) (C := 𝓞 K)
      (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal ℓ)
  have hP_fin : P ∈ primesOverFinset K ℓ :=
    (mem_primesOverFinset_iff (K := K) (ℓ := ℓ)).2 hP_over
  have hℓ_ne : rationalPrimeIdeal ℓ ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hPPlus_eq : P.under (𝓞 ((oMR K))) = PPlus :=
    ((Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)).symm
  let fiber : Finset (Ideal (𝓞 K)) := (primesOverFinset K ℓ).filter
    (fun Q => Q.under (𝓞 ((oMR K))) = PPlus)
  have hfiber_ncard : fiber.card = (Ideal.primesOver PPlus (𝓞 K)).ncard := by
    simpa [fiber] using primesOverFinsetContractionToPlus_fiber_card_eq_ncard_primesOver
      (K := K) hP_fin hPPlus_eq
  have hram_tower :
      P.ramificationIdx ℤ =
        PPlus.ramificationIdx ℤ * P.ramificationIdx (𝓞 ((oMR K))) := by
    simpa using Ideal.ramificationIdx_tower
      (R := ℤ) (S := 𝓞 ((oMR K))) (T := 𝓞 K) (q := PPlus) (r := P)
  have hram_rel : P.ramificationIdx (𝓞 ((oMR K))) = 1 := by
    apply Nat.eq_one_of_dvd_one
    refine ⟨PPlus.ramificationIdx ℤ, ?_⟩
    rw [mul_comm, ← hram_tower,
      primesOver_ramificationIdx_eq_one (p := p) (K := K) hℓp P hP_over]
  have hPPlus_ne_bot : PPlus ≠ ⊥ := by
    intro hbot
    have hlie : PPlus.LiesOver (rationalPrimeIdeal ℓ) := inferInstance
    have hover := (Ideal.liesOver_iff _ _).1 hlie
    have hcomap_bot :
        Ideal.comap (algebraMap ℤ (𝓞 ((oMR K)))) (⊥ : Ideal (𝓞 ((oMR K)))) = ⊥ := by
      ext x
      simp
    have hneq : rationalPrimeIdeal ℓ ≠ ⊥ := by
      rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
    exact hneq (by simpa [Ideal.under_def, hbot, hcomap_bot] using hover)
  have _ : IsGaloisGroup Gal(K/(oMR K)) (𝓞 ((oMR K))) (𝓞 K) :=
    IsGaloisGroup.of_isFractionRing (Gal(K/(oMR K))) (𝓞 ((oMR K))) (𝓞 K) ((oMR K)) K
  have hquad : (Ideal.primesOver PPlus (𝓞 K)).ncard * P.inertiaDeg (𝓞 ((oMR K))) = 2 := by
    have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (p := PPlus)
      (B := 𝓞 K) (G := Gal(K/(oMR K)))
    have hcard_gal : Nat.card Gal(K/(oMR K)) = 2 :=
      (IsGalois.card_aut_eq_finrank (oMR K) K).trans (finrank_K_over_Kplus (K := K))
    rw [hcard_gal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (p := PPlus) (P := P) (G := Gal(K/(oMR K))),
      Ideal.inertiaDegIn_eq_inertiaDeg (p := PPlus) (P := P) (G := Gal(K/(oMR K))),
      hram_rel] at hfund
    simpa using hfund
  have hinertia_tower :
      P.inertiaDeg ℤ =
        PPlus.inertiaDeg ℤ * P.inertiaDeg (𝓞 ((oMR K))) := by
    simpa using Ideal.inertiaDeg_tower
      (R := ℤ) (S := 𝓞 ((oMR K))) (T := 𝓞 K) (q := PPlus) (r := P)
  have hP_inertia :
      P.inertiaDeg ℤ = localResidueDegree (p := p) ℓ hℓp := by
    exact primesOver_inertiaDeg_eq_localResidueDegree (p := p) (K := K) hℓp P hP_over
  by_cases hfix : P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = P
  · have hfiber_card : fiber.card = 1 := by
      rcases primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair (K := K) hP_fin with
        hsingle | hpair
      · have hsingle_fiber : fiber = ({P} : Finset (Ideal (𝓞 K))) := by
          simpa [fiber, hPPlus_eq] using hsingle.2
        rw [hsingle_fiber]
        simp
      · exact (hpair.1 hfix).elim
    have hcard_primes : (Ideal.primesOver PPlus (𝓞 K)).ncard = 1 := by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia : P.inertiaDeg (𝓞 ((oMR K))) = 2 := by
      rw [hcard_primes] at hquad
      simpa using hquad
    have hhalf : localResidueDegreePlus (p := p) ℓ hℓp =
        localResidueDegree (p := p) ℓ hℓp / 2 :=
      (map_ringOfIntegersComplexConj_eq_self_iff_localResidueDegreePlus_eq_half
        (p := p) (K := K) hp_odd hℓp hP_fin).1 hfix
    rw [hhalf]
    rw [hP_inertia, hrel_inertia] at hinertia_tower
    omega
  · have hfiber_card : fiber.card = 2 := by
      rcases primesOverFinsetContractionToPlus_fiber_eq_singleton_or_pair (K := K) hP_fin with
        hsingle | hpair
      · exact (hfix hsingle.1).elim
      · have hpair_fiber :
            fiber =
              ({P, P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom} :
                Finset (Ideal (𝓞 K))) := by
          simpa [fiber, hPPlus_eq] using hpair.2
        rw [hpair_fiber]
        rw [Finset.card_eq_two]
        exact ⟨P, P.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          by simpa [eq_comm] using hpair.1, rfl⟩
    have hcard_primes : (Ideal.primesOver PPlus (𝓞 K)).ncard = 2 := by
      rw [← hfiber_ncard]
      exact hfiber_card
    have hrel_inertia : P.inertiaDeg (𝓞 ((oMR K))) = 1 := by
      rw [hcard_primes] at hquad
      omega
    have hnot_even : ¬ Even (localResidueDegree (p := p) ℓ hℓp) := fun h_even =>
      hfix
        ((map_ringOfIntegersComplexConj_eq_self_iff_even_localResidueDegree
          (p := p) (K := K) hp_odd hℓp hP_fin).2 h_even)
    have hself : localResidueDegreePlus (p := p) ℓ hℓp =
        localResidueDegree (p := p) ℓ hℓp :=
      localResidueDegreePlus_eq_self (p := p) hℓp hnot_even
    rw [hself]
    rw [hP_inertia, hrel_inertia] at hinertia_tower
    omega
omit [IsCMField K] in
lemma primesOverPlus_ramificationIdx_eq_one {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (PPlus : Ideal (𝓞 ((oMR K))))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K)))) :
    PPlus.ramificationIdx ℤ = 1 := by
  have : PPlus.IsPrime := hPPlus.1
  have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPPlus.2
  obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
  have hP_over : P ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 K) := by
    refine ⟨hP_prime, ?_⟩
    exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 ((oMR K))) (C := 𝓞 K)
      (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal ℓ)
  have hram_tower :
      P.ramificationIdx ℤ =
        PPlus.ramificationIdx ℤ * P.ramificationIdx (𝓞 ((oMR K))) := by
    simpa using Ideal.ramificationIdx_tower
      (R := ℤ) (S := 𝓞 ((oMR K))) (T := 𝓞 K) (q := PPlus) (r := P)
  have hℓ_ne : rationalPrimeIdeal ℓ ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hram_abs : P.ramificationIdx ℤ = 1 := by
    exact KummerCriterion.primesOver_ramificationIdx_eq_one (p := p) (K := K) hℓp P hP_over
  apply Nat.eq_one_of_dvd_one
  refine ⟨P.ramificationIdx (𝓞 ((oMR K))), ?_⟩
  rw [← hram_tower, hram_abs]
lemma ncard_primesOverPlus_eq_localPrimeCountPlus (hp_odd : p ≠ 2)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K)))).ncard =
      localPrimeCountPlus (p := p) ℓ hℓp := by
  have : (rationalPrimeIdeal ℓ).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime ℓ
  have hne : (rationalPrimeIdeal ℓ) ≠ ⊥ := by
    rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hcoe : ((primesOverFinsetPlus (K := K) ℓ : Finset (Ideal (𝓞 ((oMR K))))) :
      Set (Ideal (𝓞 ((oMR K))))) = Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K))) :=
    IsDedekindDomain.coe_primesOverFinset hne (𝓞 ((oMR K)))
  have hsum :
      ∑ PPlus ∈ primesOverFinsetPlus (K := K) ℓ,
          PPlus.ramificationIdx ℤ * PPlus.inertiaDeg ℤ = Module.finrank ℚ ((oMR K)) := by
    rw [← NumberField.RingOfIntegers.rank ((oMR K)),
      ← Ideal.sum_ramification_inertia_eq_finrank (rationalPrimeIdeal ℓ) (𝓞 ((oMR K))),
      ← Finset.sum_coe_sort]
    exact Fintype.sum_equiv (Equiv.setCongr hcoe) _ _ fun _ => rfl
  have hsum_const :
      (primesOverFinsetPlus (K := K) ℓ).card * localResidueDegreePlus (p := p) ℓ hℓp =
        Module.finrank ℚ ((oMR K)) := by
    calc
      (primesOverFinsetPlus (K := K) ℓ).card * localResidueDegreePlus (p := p) ℓ hℓp
          = ∑ PPlus ∈ primesOverFinsetPlus (K := K) ℓ,
              localResidueDegreePlus (p := p) ℓ hℓp := by
              simp
      _ = ∑ PPlus ∈ primesOverFinsetPlus (K := K) ℓ,
              PPlus.ramificationIdx ℤ * PPlus.inertiaDeg ℤ := by
              refine Finset.sum_congr rfl ?_
              intro PPlus hPPlus_fin
              have hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K))) :=
                (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hPPlus_fin
              rw [primesOverPlus_ramificationIdx_eq_one (p := p) (K := K) hℓp PPlus hPPlus,
                primesOver_inertiaDeg_eq_localResidueDegreePlus (p := p) (K := K)
                  hp_odd hℓp PPlus hPPlus]
              simp
      _ = Module.finrank ℚ ((oMR K)) := hsum
  rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := ℓ),
    finrank_Kplus_over_rat (p := p) (K := K)] at hsum_const
  have hlocal := localPrimeCountPlus_mul_localResidueDegreePlus (p := p) hp_odd hℓp
  rw [card_even_characters_kplus (p := p) hp_odd] at hlocal
  have hd_pos : 0 < localResidueDegree (p := p) ℓ hℓp := by
    dsimp [localResidueDegree]
    exact orderOf_pos (unitOfPrimeNe (p := p) ℓ hℓp)
  have hfd_pos : 0 < localResidueDegreePlus (p := p) ℓ hℓp := by
    by_cases hde : Even (localResidueDegree (p := p) ℓ hℓp)
    · rcases hde with ⟨k, hk⟩
      rw [localResidueDegreePlus_eq_half (p := p) hℓp ⟨k, hk⟩]
      omega
    · rw [localResidueDegreePlus_eq_self (p := p) hℓp hde]
      exact hd_pos
  have hmul :
      (Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K)))).ncard *
        localResidueDegreePlus (p := p) ℓ hℓp =
          localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp := by
    omega
  exact Nat.eq_of_mul_eq_mul_right hfd_pos (by simpa [Nat.mul_comm] using hmul)
lemma dedekindLocalFactor_eq_pow_localResidueDegreePlus (hp_odd : p ≠ 2)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) {s : ℂ} :
    dedekindLocalFactor (oMR K) ℓ s =
      (1 - (ℓ : ℂ) ^ (-(localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s)) ^
        localPrimeCountPlus (p := p) ℓ hℓp := by
  classical
  have hcard_eq :
      (primesOverFinsetPlus (K := K) ℓ).card =
        localPrimeCountPlus (p := p) ℓ hℓp := by
    rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := ℓ)]
    exact ncard_primesOverPlus_eq_localPrimeCountPlus (p := p) (K := K) hp_odd hℓp
  unfold dedekindLocalFactor
  change Finset.prod (primesOverFinsetPlus (K := K) ℓ) (fun PPlus =>
      (1 - (Ideal.absNorm PPlus : ℂ) ^ (-s))) =
        (1 - (ℓ : ℂ) ^ (-(localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s)) ^
          localPrimeCountPlus (p := p) ℓ hℓp
  have hprod_eq : ∀ PPlus ∈ primesOverFinsetPlus (K := K) ℓ,
      (1 - (Ideal.absNorm PPlus : ℂ) ^ (-s)) =
        1 - (ℓ : ℂ) ^ (-(localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s) := by
    intro PPlus hP
    have hPmem : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal ℓ) (𝓞 ((oMR K))) :=
      (mem_primesOverFinsetPlus_iff (K := K) (ℓ := ℓ)).1 hP
    have : PPlus.LiesOver (rationalPrimeIdeal ℓ) := hPmem.2
    have : PPlus.LiesOver (Ideal.span {(ℓ : ℤ)}) := hPmem.2
    have : (rationalPrimeIdeal ℓ).IsMaximal := by
      simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime ℓ
    have : PPlus.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPmem
    have habsNorm : Ideal.absNorm PPlus = ℓ ^ (localResidueDegreePlus (p := p) ℓ hℓp) := by
      rw [← primesOver_inertiaDeg_eq_localResidueDegreePlus (p := p) (K := K)
        hp_odd hℓp PPlus hPmem,
        ← Ideal.inertiaDeg'_eq_inertiaDeg (p := rationalPrimeIdeal ℓ) (q := PPlus)]
      simpa [rationalPrimeIdeal] using Ideal.absNorm_eq_pow_inertiaDeg' PPlus (Fact.out : ℓ.Prime)
    rw [habsNorm]
    push_cast
    have := Complex.natCast_cpow_natCast_mul ℓ (localResidueDegreePlus (p := p) ℓ hℓp) (-s)
    rw [show -((localResidueDegreePlus (p := p) ℓ hℓp : ℂ)) * s =
        ((localResidueDegreePlus (p := p) ℓ hℓp : ℕ) : ℂ) * (-s) by ring,
      this]
  rw [Finset.prod_congr rfl hprod_eq, Finset.prod_const, hcard_eq]
omit [IsCMField K] in
lemma zetaPrime_mem_primesOver_at_p :
    zetaPrime p K ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
  refine ⟨zetaPrime_isPrime p K, ?_⟩
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  simpa [zetaPrime, rationalPrimeIdeal] using
    (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p := p) (k := 0)
      (K := K) (hζ := IsCyclotomicExtension.zeta_spec (p ^ (0 + 1)) ℚ K))
omit [IsCMField K] in
lemma primesOver_at_p_eq_singleton_zetaPrime :
    Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) = {zetaPrime p K} := by
  classical
  obtain ⟨P, hP⟩ :=
    Set.ncard_eq_one.mp (ncard_primesOver_at_p_eq_one (p := p) (K := K))
  have hzeta : zetaPrime p K = P := by
    have hzeta_mem := zetaPrime_mem_primesOver_at_p (p := p) (K := K)
    rw [hP] at hzeta_mem
    simpa using hzeta_mem
  simpa [hzeta] using hP
lemma zetaPrimePlus_mem_primesOver_at_p :
    zetaPrimePlus p K ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 ((oMR K))) := by
  refine ⟨inferInstance, ?_⟩
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
  have hzeta_over : (zetaPrime p K).LiesOver (rationalPrimeIdeal p) := by
    simpa [zetaPrime, rationalPrimeIdeal] using
      (IsCyclotomicExtension.Rat.liesOver_span_zeta_sub_one (p := p) (k := 0)
        (K := K) (hζ := IsCyclotomicExtension.zeta_spec (p ^ (0 + 1)) ℚ K))
  rw [Ideal.liesOver_iff, zetaPrimePlus, Ideal.under_under]
  exact Ideal.over_def (P := zetaPrime p K) (A := ℤ) (p := rationalPrimeIdeal p)
lemma primesOverPlus_at_p_eq_singleton_zetaPrimePlus :
    Ideal.primesOver (rationalPrimeIdeal p) (𝓞 ((oMR K))) = {zetaPrimePlus p K} := by
  classical
  ext PPlus
  constructor
  · intro hPPlus
    have : PPlus.IsPrime := hPPlus.1
    have : PPlus.LiesOver (rationalPrimeIdeal p) := hPPlus.2
    obtain ⟨⟨P, hP_prime, hP_over_PPlus⟩⟩ := PPlus.nonempty_primesOver (S := 𝓞 K)
    have hP : P ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 K) := by
      refine ⟨hP_prime, ?_⟩
      exact Ideal.LiesOver.trans (A := ℤ) (B := 𝓞 ((oMR K))) (C := 𝓞 K)
        (𝔓 := P) (P := PPlus) (p := rationalPrimeIdeal p)
    have hP_eq : P = zetaPrime p K := by
      rw [primesOver_at_p_eq_singleton_zetaPrime (p := p) (K := K)] at hP
      simpa using hP
    have hPPlus_eq : PPlus = zetaPrimePlus p K := by
      simpa [zetaPrimePlus, hP_eq] using
        (Ideal.liesOver_iff _ _).1 (show P.LiesOver PPlus from inferInstance)
    simp [hPPlus_eq]
  · intro hPPlus
    rw [Set.mem_singleton_iff] at hPPlus
    simpa [hPPlus] using zetaPrimePlus_mem_primesOver_at_p (p := p) (K := K)
lemma ncard_primesOverPlus_at_p_eq_one :
    (Ideal.primesOver (rationalPrimeIdeal p) (𝓞 ((oMR K)))).ncard = 1 := by
  rw [primesOverPlus_at_p_eq_singleton_zetaPrimePlus (p := p) (K := K)]
  simp
lemma zetaPrimePlus_inertiaDeg_eq_one_at_p :
    (zetaPrimePlus p K).inertiaDeg ℤ = 1 := by
  have hinertia_tower :
      (zetaPrime p K).inertiaDeg ℤ =
        (zetaPrimePlus p K).inertiaDeg ℤ *
          (zetaPrime p K).inertiaDeg (𝓞 ((oMR K))) := by
    simpa using Ideal.inertiaDeg_tower
      (R := ℤ) (S := 𝓞 ((oMR K))) (T := 𝓞 K) (q := zetaPrimePlus p K) (r := zetaPrime p K)
  have hzeta_inertia :
      (zetaPrime p K).inertiaDeg ℤ = 1 := by
    exact primesOver_inertiaDeg_eq_one_at_p (p := p) (K := K) (zetaPrime p K)
      (zetaPrime_mem_primesOver_at_p (p := p) (K := K))
  rw [hzeta_inertia] at hinertia_tower
  exact Nat.eq_one_of_dvd_one <|
    ⟨(zetaPrime p K).inertiaDeg (𝓞 ((oMR K))), hinertia_tower⟩
lemma primesOverPlus_inertiaDeg_eq_one_at_p (PPlus : Ideal (𝓞 ((oMR K))))
    (hPPlus : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 ((oMR K)))) :
    PPlus.inertiaDeg ℤ = 1 := by
  have hPPlus_eq : PPlus = zetaPrimePlus p K := by
    rw [primesOverPlus_at_p_eq_singleton_zetaPrimePlus (p := p) (K := K)] at hPPlus
    simpa using hPPlus
  simpa [hPPlus_eq] using zetaPrimePlus_inertiaDeg_eq_one_at_p (p := p) (K := K)
lemma dedekindLocalFactorPlus_at_p {s : ℂ} :
    dedekindLocalFactor (oMR K) p s = 1 - (p : ℂ) ^ (-s) := by
  classical
  unfold dedekindLocalFactor primesOverFinset rationalPrimeIdeal
  have hne : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hcoe :=
    IsDedekindDomain.coe_primesOverFinset (p := (Ideal.span {(p : ℤ)} : Ideal ℤ)) hne
      (𝓞 ((oMR K)))
  have hcard : (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)} : Ideal ℤ)
      (𝓞 ((oMR K)))).card = 1 := by
    have hncard : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 ((oMR K)))).ncard = 1 := by
      simpa [rationalPrimeIdeal] using ncard_primesOverPlus_at_p_eq_one (p := p) (K := K)
    rw [← hcoe] at hncard
    simpa using hncard
  obtain ⟨PPlus, hPPlus⟩ := Finset.card_eq_one.mp hcard
  rw [hPPlus, Finset.prod_singleton]
  have hPPlus_mem : PPlus ∈ (Ideal.span {(p : ℤ)}).primesOver (𝓞 ((oMR K))) := by
    rw [← hcoe]
    rw [hPPlus]
    exact Finset.mem_singleton_self PPlus
  have : PPlus.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPPlus_mem.2
  have : PPlus.IsMaximal := Ideal.isMaximal_of_mem_primesOver (by
    simpa [rationalPrimeIdeal] using hPPlus_mem)
  have habsNorm : Ideal.absNorm PPlus = p ^ (1 : ℕ) := by
    rw [← primesOverPlus_inertiaDeg_eq_one_at_p (p := p) (K := K) PPlus]
    · rw [← Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(p : ℤ)}) PPlus]
      exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus hp.out
    · simpa [rationalPrimeIdeal] using hPPlus_mem
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
variable (L : Type*) [Field L] [NumberField L]
abbrev NonzeroIdeal : Type _ := {I : Ideal (𝓞 L) // I ≠ ⊥}
noncomputable def idealNormMultiplicity (n : ℕ) : ℕ :=
  Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}
lemma idealNormMultiplicity_zero : idealNormMultiplicity L 0 = 0 := by
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI⟩, hnorm⟩
  exact hI (Ideal.absNorm_eq_zero_iff.mp hnorm)
lemma idealNormMultiplicity_one : idealNormMultiplicity L 1 = 1 := by
  have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
    { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
      uniq := by
        rintro ⟨⟨I, hI⟩, hnorm⟩
        exact Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
  exact Nat.card_unique
lemma idealNormMultiplicity_mul {m n : ℕ} (hcop : Nat.Coprime m n) :
    idealNormMultiplicity L (m * n) =
      idealNormMultiplicity L m * idealNormMultiplicity L n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.Coprime, Nat.gcd_zero_left] at hcop
    subst hcop
    simp [idealNormMultiplicity_zero, idealNormMultiplicity_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
    subst hcop
    simp [idealNormMultiplicity_zero, idealNormMultiplicity_one]
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  all_goals rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · classical
    have h_cop_spans : (Ideal.span {(m : 𝓞 L)}) ⊔ (Ideal.span {(n : 𝓞 L)}) = ⊤ := by
      rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
      have hZ : IsCoprime (m : ℤ) (n : ℤ) := Nat.Coprime.isCoprime hcop
      simpa using hZ.map (algebraMap ℤ (𝓞 L))
    have h_mul_sup : ∀ (I : Ideal (𝓞 L)),
        (I ⊔ Ideal.span {(m : 𝓞 L)}) * (I ⊔ Ideal.span {(n : 𝓞 L)}) =
          I ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} := fun I => by
      rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup,
        mul_comm (Ideal.span {(m : 𝓞 L)}) I,
        Ideal.span_singleton_mul_span_singleton,
        show I * I ⊔ I * Ideal.span {(n : 𝓞 L)} ⊔
            (I * Ideal.span {(m : 𝓞 L)} ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)}) =
            (I * I ⊔ I * Ideal.span {(n : 𝓞 L)} ⊔ I * Ideal.span {(m : 𝓞 L)}) ⊔
              Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} from by ac_rfl,
        ← Ideal.mul_sup, ← Ideal.mul_sup,
        show I ⊔ Ideal.span {(n : 𝓞 L)} ⊔ Ideal.span {(m : 𝓞 L)} = ⊤ from by
          rw [sup_assoc, sup_comm (Ideal.span {(n : 𝓞 L)}) _, h_cop_spans, sup_top_eq],
        Ideal.mul_top]
    have h_sup_absNorm : ∀ (I : Ideal (𝓞 L)), Ideal.absNorm I = m * n →
        I ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} = I := fun I hI => by
      refine le_antisymm (sup_le le_rfl ?_) le_sup_left
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have : ((m * n : ℕ) : 𝓞 L) ∈ I := by
        rw [← hI]
        exact Ideal.absNorm_mem I
      push_cast at this
      exact this
    have h_cop_lift : ∀ (I : Ideal (𝓞 L)),
        IsCoprime (I ⊔ Ideal.span {(m : 𝓞 L)}) (I ⊔ Ideal.span {(n : 𝓞 L)}) := fun I => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = (Ideal.span {(m : 𝓞 L)}) ⊔ (Ideal.span {(n : 𝓞 L)}) := h_cop_spans.symm
        _ ≤ (I ⊔ Ideal.span {(m : 𝓞 L)}) ⊔ (I ⊔ Ideal.span {(n : 𝓞 L)}) :=
            sup_le_sup le_sup_right le_sup_right
    have h_abs_span_nat : ∀ (r : ℕ), Ideal.absNorm (Ideal.span {(r : 𝓞 L)}) =
        r ^ Module.finrank ℤ (𝓞 L) := fun r => by
      rw [Ideal.absNorm_span_singleton,
        show ((r : 𝓞 L)) = algebraMap ℤ (𝓞 L) (r : ℤ) from by push_cast; rfl,
        Algebra.norm_algebraMap_of_basis (Module.finBasis ℤ (𝓞 L))]
      simp
    have h_fwd_norms : ∀ (I : Ideal (𝓞 L)), Ideal.absNorm I = m * n →
        Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 L)}) = m ∧
          Ideal.absNorm (I ⊔ Ideal.span {(n : 𝓞 L)}) = n := fun I hI => by
      set a := Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 L)}) with ha_def
      set b := Ideal.absNorm (I ⊔ Ideal.span {(n : 𝓞 L)}) with hb_def
      have h_prod : (I ⊔ Ideal.span {(m : 𝓞 L)}) * (I ⊔ Ideal.span {(n : 𝓞 L)}) = I := by
        rw [h_mul_sup I, h_sup_absNorm I hI]
      have h_ab : a * b = m * n := by
        rw [ha_def, hb_def, ← map_mul, h_prod, hI]
      have h_a_dvd_md : a ∣ m ^ Module.finrank ℤ (𝓞 L) := by
        rw [← h_abs_span_nat m]
        exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
      have h_b_dvd_nd : b ∣ n ^ Module.finrank ℤ (𝓞 L) := by
        rw [← h_abs_span_nat n]
        exact Ideal.absNorm_dvd_absNorm_of_le le_sup_right
      have h_cop_an : Nat.Coprime a n :=
        (hcop.pow_left _).coprime_dvd_left h_a_dvd_md
      have h_cop_bm : Nat.Coprime b m :=
        (hcop.symm.pow_left _).coprime_dvd_left h_b_dvd_nd
      have h_a_dvd_m : a ∣ m :=
        h_cop_an.dvd_of_dvd_mul_right ⟨b, h_ab.symm⟩
      have h_b_dvd_n : b ∣ n :=
        h_cop_bm.dvd_of_dvd_mul_right ⟨a, by linarith [h_ab, mul_comm a b, mul_comm m n]⟩
      have ha_le : a ≤ m := Nat.le_of_dvd hm h_a_dvd_m
      have hb_le : b ≤ n := Nat.le_of_dvd hn h_b_dvd_n
      have ha_ge : m ≤ a := by
        have h1 : m * n ≤ a * n := by
          calc
            m * n = a * b := h_ab.symm
            _ ≤ a * n := Nat.mul_le_mul_left a hb_le
        exact Nat.le_of_mul_le_mul_right h1 hn
      have hb_ge : n ≤ b := by
        have h1 : m * n ≤ m * b := by
          calc
            m * n = a * b := h_ab.symm
            _ ≤ m * b := Nat.mul_le_mul_right b ha_le
        exact Nat.le_of_mul_le_mul_left h1 hm
      exact ⟨Nat.le_antisymm ha_le ha_ge, Nat.le_antisymm hb_le hb_ge⟩
    have h_cop_m_L : ∀ (L' : Ideal (𝓞 L)), Ideal.absNorm L' = n →
        IsCoprime (Ideal.span {(m : 𝓞 L)}) L' := fun L' hL => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = Ideal.span {(m : 𝓞 L)} ⊔ Ideal.span {(n : 𝓞 L)} := h_cop_spans.symm
        _ ≤ Ideal.span {(m : 𝓞 L)} ⊔ L' := sup_le_sup_left (by
            rw [Ideal.span_le, Set.singleton_subset_iff]
            have : ((n : ℕ) : 𝓞 L) ∈ L' := by
              rw [← hL]
              exact Ideal.absNorm_mem L'
            exact_mod_cast this) _
    have h_cop_n_J : ∀ (J : Ideal (𝓞 L)), Ideal.absNorm J = m →
        IsCoprime (Ideal.span {(n : 𝓞 L)}) J := fun J hJ => by
      rw [Ideal.isCoprime_iff_sup_eq]
      refine top_le_iff.mp ?_
      calc
        ⊤ = Ideal.span {(n : 𝓞 L)} ⊔ Ideal.span {(m : 𝓞 L)} := by
              rw [sup_comm]
              exact h_cop_spans.symm
        _ ≤ Ideal.span {(n : 𝓞 L)} ⊔ J := sup_le_sup_left (by
            rw [Ideal.span_le, Set.singleton_subset_iff]
            have : ((m : ℕ) : 𝓞 L) ∈ J := by
              rw [← hJ]
              exact Ideal.absNorm_mem J
            exact_mod_cast this) _
    have h_inv_m : ∀ (J L' : Ideal (𝓞 L)), Ideal.absNorm J = m → Ideal.absNorm L' = n →
        J * L' ⊔ Ideal.span {(m : 𝓞 L)} = J := fun J L' hJ hL => by
      have h_cop_mL_sup : Ideal.span {(m : 𝓞 L)} ⊔ L' = ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp (h_cop_m_L L' hL)
      refine le_antisymm (sup_le Ideal.mul_le_left ?_) ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        have : ((m : ℕ) : 𝓞 L) ∈ J := by
          rw [← hJ]
          exact Ideal.absNorm_mem J
        exact_mod_cast this
      · calc
          J = J * ⊤ := (Ideal.mul_top J).symm
          _ = J * (Ideal.span {(m : 𝓞 L)} ⊔ L') := by rw [h_cop_mL_sup]
          _ = J * Ideal.span {(m : 𝓞 L)} ⊔ J * L' := Ideal.mul_sup _ _ _
          _ ≤ Ideal.span {(m : 𝓞 L)} ⊔ J * L' := sup_le_sup_right Ideal.mul_le_right _
          _ = J * L' ⊔ Ideal.span {(m : 𝓞 L)} := sup_comm _ _
    have h_inv_n : ∀ (J L' : Ideal (𝓞 L)), Ideal.absNorm J = m → Ideal.absNorm L' = n →
        J * L' ⊔ Ideal.span {(n : 𝓞 L)} = L' := fun J L' hJ hL => by
      have h_cop_nJ_sup : Ideal.span {(n : 𝓞 L)} ⊔ J = ⊤ :=
        Ideal.isCoprime_iff_sup_eq.mp (h_cop_n_J J hJ)
      refine le_antisymm (sup_le Ideal.mul_le_right ?_) ?_
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        have : ((n : ℕ) : 𝓞 L) ∈ L' := by
          rw [← hL]
          exact Ideal.absNorm_mem L'
        exact_mod_cast this
      · calc
          L' = ⊤ * L' := (Ideal.top_mul L').symm
          _ = (Ideal.span {(n : 𝓞 L)} ⊔ J) * L' := by rw [h_cop_nJ_sup]
          _ = Ideal.span {(n : 𝓞 L)} * L' ⊔ J * L' := Ideal.sup_mul _ _ _
          _ ≤ Ideal.span {(n : 𝓞 L)} ⊔ J * L' := sup_le_sup_right Ideal.mul_le_left _
          _ = J * L' ⊔ Ideal.span {(n : 𝓞 L)} := sup_comm _ _
    let fwd : {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} →
        {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
          {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} :=
      fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
        ⟨⟨⟨I ⊔ Ideal.span {(m : 𝓞 L)}, fun h => hI_ne (by
            have : I ≤ I ⊔ Ideal.span {(m : 𝓞 L)} := le_sup_left
            rw [h, le_bot_iff] at this
            exact this)⟩,
          (h_fwd_norms I hI_norm).1⟩,
         ⟨⟨I ⊔ Ideal.span {(n : 𝓞 L)}, fun h => hI_ne (by
            have : I ≤ I ⊔ Ideal.span {(n : 𝓞 L)} := le_sup_left
            rw [h, le_bot_iff] at this
            exact this)⟩,
          (h_fwd_norms I hI_norm).2⟩⟩
    let bwd : {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
        {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} →
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} :=
      fun ⟨⟨⟨J, hJ_ne⟩, hJ_norm⟩, ⟨⟨L', hL_ne⟩, hL_norm⟩⟩ =>
        ⟨⟨J * L', fun h => by
            rcases Ideal.mul_eq_bot.mp h with h1 | h1
            · exact hJ_ne h1
            · exact hL_ne h1⟩,
         by rw [map_mul, hJ_norm, hL_norm]⟩
    have h_equiv :
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} ≃
          {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
            {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} :=
      { toFun := fwd
        invFun := bwd
        left_inv := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ => by
          simp only [fwd, bwd]
          refine Subtype.ext (Subtype.ext ?_)
          simp only
          rw [h_mul_sup, h_sup_absNorm I hI_norm]
        right_inv := fun ⟨⟨⟨J, hJ_ne⟩, hJ_norm⟩, ⟨⟨L', hL_ne⟩, hL_norm⟩⟩ => by
          simp only [fwd, bwd]
          refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_))
          · exact h_inv_m J L' hJ_norm hL_norm
          · exact h_inv_n J L' hJ_norm hL_norm }
    unfold idealNormMultiplicity
    rw [Nat.card_congr h_equiv, Nat.card_prod]
  · interval_cases n
    simp [idealNormMultiplicity_one]
  · interval_cases m
    simp [idealNormMultiplicity_one]
  · interval_cases m
    interval_cases n
    simp [idealNormMultiplicity_one]
lemma dedekindZeta_eq_tsum_idealNormMultiplicity {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n => ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [↓reduceIte]
    rw [idealNormMultiplicity_zero]
    push_cast
    rw [Complex.zero_cpow (by
      intro h
      have hs_ne : s ≠ 0 := by
        intro hs_zero
        rw [hs_zero, Complex.zero_re] at hs
        exact absurd hs (by norm_num)
      exact hs_ne (neg_eq_zero.mp h)), mul_zero]
  · simp only [hn.ne', ↓reduceIte]
    have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Complex.cpow_neg, div_eq_mul_inv]
    congr 1
    unfold idealNormMultiplicity
    have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
      refine {
        toFun := fun ⟨I, hI⟩ => ⟨⟨I, ?_⟩, hI⟩
        invFun := fun ⟨⟨I, _⟩, hI⟩ => ⟨I, hI⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      intro h
      rw [h] at hI
      rw [Ideal.absNorm_bot] at hI
      omega
    exact (Nat.card_congr hequiv).symm ▸ rfl
lemma summable_tsum_symGeometric (α : Type*) [Fintype α] [Finite α] {z : ℂ}
    (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n) ∧
      (∑' n : ℕ, (Fintype.card (Sym α n) : ℂ) * z ^ n) =
        ((1 - z)⁻¹) ^ Fintype.card α := by
  by_cases hα : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hα
    let term : ℕ → ℂ := fun n => (Fintype.card (Sym α n) : ℂ) * z ^ n
    have hzero : ∀ n ≠ 0, term n = 0 := by
      intro n hn
      cases n with
      | zero => contradiction
      | succ n => simp [term, Sym.card_sym_eq_multichoose, Nat.multichoose_zero_succ]
    have hsupport : {n : ℕ | term n ≠ 0}.Finite := by
      refine Set.Finite.subset ({0} : Set ℕ).toFinite ?_
      intro n hn
      by_contra hne
      exact hn (hzero n hne)
    constructor
    · exact summable_of_hasFiniteSupport hsupport
    · have hcard0 : Fintype.card (Sym α 0) = 1 := by
        rw [Sym.card_sym_eq_multichoose, Nat.multichoose_zero_right]
      simpa [term, hcard0, hα] using tsum_eq_single 0 hzero
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hα
    constructor
    · refine (summable_choose_mul_geometric_of_norm_lt_one k hz).congr ?_
      intro n
      rw [Sym.card_sym_eq_choose, hk, Nat.succ_add_sub_one, Nat.add_comm k n,
        Nat.choose_symm_add]
    · calc
        ∑' n : ℕ, (Fintype.card (Sym α n) : ℂ) * z ^ n
            = ∑' n : ℕ, ((n + k).choose k : ℂ) * z ^ n := by
                apply tsum_congr
                intro n
                rw [Sym.card_sym_eq_choose, hk, Nat.succ_add_sub_one, Nat.add_comm k n,
                  Nat.choose_symm_add]
        _ = 1 / (1 - z) ^ (k + 1) := tsum_choose_mul_geometric_of_norm_lt_one k hz
        _ = ((1 - z)⁻¹) ^ (k + 1) := by simp [one_div]
        _ = ((1 - z)⁻¹) ^ Fintype.card α := by simp [hk]
lemma tsum_symGeometric (α : Type*) [Fintype α] [Finite α] {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' n : ℕ, (Fintype.card (Sym α n) : ℂ) * z ^ n) = ((1 - z)⁻¹) ^ Fintype.card α :=
  (summable_tsum_symGeometric α hz).2
lemma summable_idealNormMultiplicity_mul_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ := by
  classical
  have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b => by
    refine Set.Finite.preimage (f := fun I : NonzeroIdeal L => I.1) ?_
      (Ideal.finite_setOfPred_absNorm_eq b)
    intro _ _ _ _; exact Subtype.ext
  have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n => by
    have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L =>
      Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ => h_finite b)
    rw [show ((fun I : NonzeroIdeal L => Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} from by
      ext ⟨I, hI⟩
      simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_ofPred_eq]
      exact ⟨fun h => h.2, fun h =>
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
    exact key.symm
  have h_bigO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    have h_card_bridge : ∀ n : ℕ,
        Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
        Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
      fun n =>
      Nat.card_congr
        { toFun := fun ⟨⟨I, hI⟩, hn⟩ =>
            ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
          invFun := fun ⟨⟨I, hI⟩, hn⟩ =>
            ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
      (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
        tendsto_natCast_atTop_atTop).congr' ?_)
    filter_upwards with n
    simp only [Function.comp_apply, Real.rpow_one]
    rw [show (∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ)) =
        ((∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k : ℕ) : ℝ) from by push_cast; rfl,
      h_sum_card n, h_card_bridge n]
    push_cast
    rfl
  have h_lss : LSeriesSummable (fun n : ℕ => ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f := fun n => (idealNormMultiplicity L n : ℝ))
      h_bigO (fun _ => Nat.cast_nonneg _) zero_le_one (by exact_mod_cast hs)
  have h_term_eq : LSeries.term (fun n : ℕ => ((idealNormMultiplicity L n : ℝ) : ℂ)) s =
      fun n => (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [idealNormMultiplicity_zero]
    · show ((idealNormMultiplicity L n : ℝ) : ℂ) / (n : ℂ) ^ s = _
      rw [Complex.cpow_neg, ← div_eq_mul_inv]
      push_cast
      rfl
  exact (h_term_eq ▸ h_lss :
    Summable fun n => (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)).norm
lemma dedekindZeta_eq_tprod_primePowerSeries {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' q : Nat.Primes,
        (∑' k : ℕ, (idealNormMultiplicity L ((q : ℕ) ^ k) : ℂ) *
          ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))) := by
  let f : ℕ → ℂ := fun n => (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)
  have hf_zero : f 0 = 0 := by simp [f, idealNormMultiplicity_zero L]
  have hf_one : f 1 = 1 := by simp [f, idealNormMultiplicity_one L]
  have hf_mul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := fun {m n} hcop => by
    simp only [f]
    rw [idealNormMultiplicity_mul L hcop, Nat.cast_mul, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  have hf_sum : Summable fun n => ‖f n‖ := summable_idealNormMultiplicity_mul_cpow_neg L hs
  rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs,
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
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
lemma LFunction_eq_prime_tprod_of_localFactors (χ : DirichletCharacter ℂ p) {s : ℂ}
    (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s =
      ∏' q : Nat.Primes, (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹ := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs,
    ← DirichletCharacter.LSeries_eulerProduct_tprod χ hs]
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
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
abbrev NonzeroIdealNF (L : Type*) [Field L] [NumberField L] : Type _ := NonzeroIdeal L
abbrev idealNormMultiplicityNF (L : Type*) [Field L] [NumberField L] (n : ℕ) : ℕ :=
  idealNormMultiplicity L n
lemma dedekindZeta_eq_tprod_primePowerSeriesNF
    (L : Type*) [Field L] [NumberField L] {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' q : Nat.Primes,
        (∑' k : ℕ, (idealNormMultiplicityNF L ((q : ℕ) ^ k) : ℂ) *
          ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))) := by
  simpa [idealNormMultiplicityNF] using
    (dedekindZeta_eq_tprod_primePowerSeries (L := L) hs)
lemma idealNormMultiplicityNF_p_pow_eq_one_plus (hp_odd : p ≠ 2) (k : ℕ) :
    idealNormMultiplicityNF (oMR K) (p ^ k) = 1 := by
  classical
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have hcard : (primesOverFinsetPlus (K := K) p).card = 1 := by
    rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := p)]
    exact ncard_primesOverPlus_at_p_eq_one (p := p) (K := K)
  obtain ⟨PPlus, hPPlus⟩ := Finset.card_eq_one.mp hcard
  have hPPlusmem : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (oMR K)) := by
    have hPPlus_fin : PPlus ∈ primesOverFinsetPlus (K := K) p := by
      rw [hPPlus]
      exact Finset.mem_singleton_self PPlus
    exact (mem_primesOverFinsetPlus_iff (K := K) (ℓ := p)).1 hPPlus_fin
  have hPPlus_ne : PPlus ≠ ⊥ := by
    intro hPPlus_bot
    have hunder := hPPlusmem.2
    rw [Ideal.liesOver_iff, Ideal.under_def, hPPlus_bot,
      Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 (oMR K)))
        (FaithfulSMul.algebraMap_injective ℤ (𝓞 (oMR K)))] at hunder
    have hne : (rationalPrimeIdeal p) ≠ ⊥ := by
      rw [rationalPrimeIdeal, Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hp.out.ne_zero
    exact hne hunder
  have : PPlus.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hPPlus_ne hPPlusmem.1
  have : PPlus.LiesOver (Ideal.span {(p : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPPlusmem.2
  have habsNormPPlus : Ideal.absNorm PPlus = p := by
    calc
      Ideal.absNorm PPlus = p ^ (1 : ℕ) := by
        rw [← primesOverPlus_inertiaDeg_eq_one_at_p (p := p) (K := K) PPlus hPPlusmem]
        rw [← Ideal.inertiaDeg'_eq_inertiaDeg (p := Ideal.span {(p : ℤ)}) (q := PPlus)]
        exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus hp.out
      _ = p := by simp
  have : Unique {I : NonzeroIdealNF (oMR K) // Ideal.absNorm I.1 = p ^ k} :=
    { default := ⟨⟨PPlus ^ k, pow_ne_zero k hPPlus_ne⟩, by
          rw [map_pow, habsNormPPlus]⟩
      uniq := by
        rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
        let m : ℕ := Multiset.count PPlus (UniqueFactorizationMonoid.normalizedFactors I)
        obtain ⟨Q, hPQ, hIeq⟩ := Ideal.eq_prime_pow_mul_coprime hI_ne PPlus
        have hQ_top : Q = ⊤ := by
          by_contra hQ_ne_top
          have hQ_ne : Q ≠ ⊥ := by
            intro hQ_bot
            apply hI_ne
            rw [hIeq, hQ_bot, Ideal.mul_bot]
          have hnf_ne : UniqueFactorizationMonoid.normalizedFactors Q ≠ 0 := by
            intro hnf
            apply hQ_ne_top
            rw [← Ideal.prod_normalizedFactors_eq_self hQ_ne, hnf]
            simp
          obtain ⟨R, hRmem⟩ := Multiset.exists_mem_of_ne_zero hnf_ne
          have hRfac := (Ideal.mem_normalizedFactors_iff hQ_ne).1 hRmem
          have hRprime : R.IsPrime := hRfac.1
          have hQ_le_R : Q ≤ R := hRfac.2
          have hR_ne : R ≠ ⊥ := fun hR_bot =>
            hQ_ne (le_bot_iff.mp (hQ_le_R.trans_eq hR_bot))
          have : NeZero R := ⟨hR_ne⟩
          have hI_le_Q : I ≤ Q := by
            rw [hIeq]
            exact Ideal.mul_le_right
          have hR_dvd_I : Ideal.absNorm R ∣ p ^ k := by
            rw [← hI_norm]
            exact dvd_trans (Ideal.absNorm_dvd_absNorm_of_le hQ_le_R)
              (Ideal.absNorm_dvd_absNorm_of_le hI_le_Q)
          have hunder_dvd : Ideal.absNorm (Ideal.under ℤ R) ∣ p ^ k :=
            dvd_trans (Int.absNorm_under_dvd_absNorm R) hR_dvd_I
          have hunder_prime : (Ideal.absNorm (Ideal.under ℤ R)).Prime := Nat.absNorm_under_prime R
          have hunder_dvd_p : Ideal.absNorm (Ideal.under ℤ R) ∣ p :=
            hunder_prime.dvd_of_dvd_pow hunder_dvd
          have hunder_eq_p : Ideal.absNorm (Ideal.under ℤ R) = p :=
            (Nat.prime_dvd_prime_iff_eq hunder_prime hp.out).1 hunder_dvd_p
          have hunder_eq_span_p : Ideal.under ℤ R = Ideal.span {(p : ℤ)} := by
            rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ R)]
            simp [hunder_eq_p]
          have hR_lies : R.LiesOver (Ideal.span {(p : ℤ)}) := by
            rw [Ideal.liesOver_iff, hunder_eq_span_p]
          have hRmem_p : R ∈ Ideal.primesOver (rationalPrimeIdeal p) (𝓞 (oMR K)) := by
            refine ⟨hRprime, ?_⟩
            simpa [rationalPrimeIdeal] using hR_lies
          have hRmem_fin : R ∈ primesOverFinsetPlus (K := K) p :=
            (mem_primesOverFinsetPlus_iff (K := K) (ℓ := p)).2 hRmem_p
          have hR_eq_PPlus : R = PPlus := by
            rw [hPPlus] at hRmem_fin
            exact Finset.mem_singleton.mp hRmem_fin
          have hQ_le_PPlus : Q ≤ PPlus := by
            simpa [hR_eq_PPlus] using hQ_le_R
          have htop_le_PPlus : (⊤ : Ideal (𝓞 (oMR K))) ≤ PPlus := by
            calc
              ⊤ = PPlus ⊔ Q := hPQ.symm
              _ ≤ PPlus := sup_le le_rfl hQ_le_PPlus
          exact hPPlusmem.1.ne_top (top_le_iff.mp htop_le_PPlus)
        have hI_pow : I = PPlus ^ m := by
          simpa [m, hQ_top] using hIeq
        have hm : m = k := by
          apply Nat.pow_right_injective hp.out.one_lt
          calc
            p ^ m = Ideal.absNorm I := by
              rw [hI_pow, map_pow, habsNormPPlus]
            _ = p ^ k := hI_norm
        refine Subtype.ext (Subtype.ext ?_)
        simpa [m, hm] using hI_pow }
  exact Nat.card_unique
lemma normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow
    {q : Nat.Primes} {I : Ideal (𝓞 (oMR K))} (hI_ne : I ≠ ⊥)
    {k : ℕ} (hI_norm : Ideal.absNorm I = (q : ℕ) ^ k) :
    (UniqueFactorizationMonoid.normalizedFactors I).toFinset ⊆
      primesOverFinsetPlus (K := K) (q : ℕ) := by
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  intro PPlus hPPlus
  have hPPlus_mem : PPlus ∈ UniqueFactorizationMonoid.normalizedFactors I :=
    Multiset.mem_toFinset.1 hPPlus
  have hPPlus_fac := (Ideal.mem_normalizedFactors_iff hI_ne).1 hPPlus_mem
  have hPPlus_prime : PPlus.IsPrime := hPPlus_fac.1
  have hI_le_PPlus : I ≤ PPlus := hPPlus_fac.2
  have hPPlus_ne : PPlus ≠ ⊥ := fun hPPlus_bot =>
    hI_ne (le_bot_iff.mp (hPPlus_bot ▸ hI_le_PPlus))
  have : NeZero PPlus := ⟨hPPlus_ne⟩
  have hPPlus_dvd : Ideal.absNorm PPlus ∣ (q : ℕ) ^ k := by
    rw [← hI_norm]
    exact Ideal.absNorm_dvd_absNorm_of_le hI_le_PPlus
  have hunder_dvd : Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q : ℕ) ^ k :=
    dvd_trans (Int.absNorm_under_dvd_absNorm PPlus) hPPlus_dvd
  have hunder_prime : (Ideal.absNorm (Ideal.under ℤ PPlus)).Prime := Nat.absNorm_under_prime PPlus
  have hunder_dvd_q : Ideal.absNorm (Ideal.under ℤ PPlus) ∣ (q : ℕ) :=
    hunder_prime.dvd_of_dvd_pow hunder_dvd
  have hunder_eq_q : Ideal.absNorm (Ideal.under ℤ PPlus) = (q : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq hunder_prime q.2).1 hunder_dvd_q
  have hunder_eq_span_q : Ideal.under ℤ PPlus = Ideal.span {((q : ℕ) : ℤ)} := by
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ PPlus)]
    simp [hunder_eq_q]
  have hPPlus_lies : PPlus.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    rw [Ideal.liesOver_iff, hunder_eq_span_q]
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 (oMR K)) := by
    refine ⟨hPPlus_prime, ?_⟩
    simpa [rationalPrimeIdeal] using hPPlus_lies
  exact (mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).2 hPPlus_over
lemma absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {PPlus : Ideal (𝓞 (oMR K))}
    (hPPlus : PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)) :
    Ideal.absNorm PPlus = (q : ℕ) ^ localResidueDegreePlus (p := p) (q : ℕ) hq := by
  have hPPlus_over : PPlus ∈ Ideal.primesOver (rationalPrimeIdeal (q : ℕ)) (𝓞 (oMR K)) :=
    (mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 hPPlus
  have : PPlus.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    simpa [rationalPrimeIdeal] using hPPlus_over.2
  have : (rationalPrimeIdeal (q : ℕ)).IsMaximal := by
    simpa [rationalPrimeIdeal] using Int.ideal_span_isMaximal_of_prime (q : ℕ)
  have : PPlus.IsMaximal := Ideal.isMaximal_of_mem_primesOver hPPlus_over
  rw [← primesOver_inertiaDeg_eq_localResidueDegreePlus
    (p := p) (K := K) hp_odd hq PPlus hPPlus_over]
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg
    (p := Ideal.span {((q : ℕ) : ℤ)}) (q := PPlus)]
  exact Ideal.absNorm_eq_pow_inertiaDeg' PPlus q.2
lemma normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {I : Ideal (𝓞 (oMR K))} (hI_ne : I ≠ ⊥) {k : ℕ}
    (hI_norm : Ideal.absNorm I = (q : ℕ) ^ k) :
    localResidueDegreePlus (p := p) (q : ℕ) hq *
        (UniqueFactorizationMonoid.normalizedFactors I).card = k := by
  classical
  set d := localResidueDegreePlus (p := p) (q : ℕ) hq with hd
  set m := UniqueFactorizationMonoid.normalizedFactors I with hm
  have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
    simpa [hm] using
      normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
  have hsum_count : ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus = m.card :=
    Multiset.sum_count_eq_card fun PPlus hPPlus => hsubset (Multiset.mem_toFinset.2 hPPlus)
  have hnorm_factors : Ideal.absNorm m.prod = (q : ℕ) ^ (d * m.card) := by
    rw [Finset.prod_multiset_count_of_subset m (primesOverFinsetPlus (K := K) (q : ℕ)) hsubset,
      map_prod]
    calc
      ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), Ideal.absNorm (PPlus ^ m.count PPlus)
          = ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ),
              ((q : ℕ) ^ d) ^ m.count PPlus := by
              apply Finset.prod_congr rfl
              intro PPlus hPPlus
              rw [map_pow]
              rw [absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
                (p := p) (K := K) hp_odd hq hPPlus, hd]
      _ = (q : ℕ) ^
          (d * ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus) := by
              rw [Finset.prod_pow_eq_pow_sum]
              simp [Nat.pow_mul]
      _ = (q : ℕ) ^ (d * m.card) := by rw [hsum_count]
  have hpow : (q : ℕ) ^ (d * m.card) = (q : ℕ) ^ k := by
    calc
      (q : ℕ) ^ (d * m.card) = Ideal.absNorm m.prod := hnorm_factors.symm
      _ = Ideal.absNorm I := by rw [hm, Ideal.prod_normalizedFactors_eq_self hI_ne]
      _ = (q : ℕ) ^ k := hI_norm
  exact Nat.pow_right_injective q.2.one_lt hpow
lemma idealNormMultiplicityNF_prime_pow_eq_zero_of_not_dvd_plus
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p)
    {k : ℕ} (hk : ¬ localResidueDegreePlus (p := p) (q : ℕ) hq ∣ k) :
    idealNormMultiplicityNF (oMR K) ((q : ℕ) ^ k) = 0 := by
  unfold idealNormMultiplicityNF idealNormMultiplicity
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨?_⟩
  rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
  apply hk
  refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card, ?_⟩
  simpa [mul_comm] using
    (normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
      (p := p) (K := K) hp_odd hq hI_ne hI_norm).symm
lemma idealNormMultiplicityNF_prime_pow_mul_localResidueDegreePlus_eq_card_sym
    (hp_odd : p ≠ 2) {q : Nat.Primes} [Fact (q : ℕ).Prime] (hq : (q : ℕ) ≠ p) (n : ℕ) :
    idealNormMultiplicityNF (oMR K)
        ((q : ℕ) ^ (localResidueDegreePlus (p := p) (q : ℕ) hq * n)) =
      Fintype.card (Sym {PPlus : Ideal (𝓞 (oMR K)) //
        PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)} n) := by
  classical
  set d := localResidueDegreePlus (p := p) (q : ℕ) hq with hd
  let α : Type _ :=
    {PPlus : Ideal (𝓞 (oMR K)) // PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)}
  let β : Type _ := {I : NonzeroIdealNF (oMR K) // Ideal.absNorm I.1 = (q : ℕ) ^ (d * n)}
  have hd_raw_pos : 0 < localResidueDegree (p := p) (q : ℕ) hq := by
    dsimp [localResidueDegree]
    exact orderOf_pos (unitOfPrimeNe (p := p) (q : ℕ) hq)
  have hd_pos : 0 < d := by
    rw [hd]
    by_cases hde : Even (localResidueDegree (p := p) (q : ℕ) hq)
    · rcases hde with ⟨k, hk⟩
      rw [localResidueDegreePlus_eq_half (p := p) hq ⟨k, hk⟩, hk]
      omega
    · rw [localResidueDegreePlus_eq_self (p := p) hq hde]
      exact hd_raw_pos
  have hpmap_val :
      ∀ {m : Multiset (Ideal (𝓞 (oMR K)))}
        (H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)),
        Multiset.map Subtype.val
          (Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H) = m := by
    intro m H
    rw [Multiset.map_pmap, Multiset.pmap_eq_map, Multiset.map_id']
  let toSym : β → Sym α n := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ =>
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
        simpa [m] using
          normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    have hm_card : m.card = n := by
      have hmul : d * m.card = d * n := by
        simpa [m, hd] using
          normalizedFactors_card_mul_localResidueDegreePlus_of_absNorm_prime_pow
            (p := p) (K := K) hp_odd hq hI_ne hI_norm
      exact Nat.eq_of_mul_eq_mul_left hd_pos hmul
    ⟨Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H, by
      simp [hm_card]⟩
  let ofSym : Sym α n → β := fun s =>
    let m : Multiset (Ideal (𝓞 (oMR K))) := s.1.map Subtype.val
    have hm_card : m.card = n := by
      simp [m]
    have hm_subset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      rcases Multiset.mem_toFinset.1 hPPlus with hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      exact QPlus.2
    have hm_prime : ∀ PPlus ∈ m, Prime PPlus := by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      have hQPlus_ne : (QPlus : Ideal (𝓞 (oMR K))) ≠ ⊥ := by
        intro hQPlus_bot
        have hQPlus_norm :=
          absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
            (p := p) (K := K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot, ← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 QPlus.2).1
    have hm_prod_ne : m.prod ≠ ⊥ := Multiset.prod_ne_zero_of_prime m hm_prime
    have hm_norm : Ideal.absNorm m.prod = (q : ℕ) ^ (d * n) := by
      have hsum_count :
          ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus = m.card :=
        Multiset.sum_count_eq_card fun PPlus hPPlus =>
          hm_subset (Multiset.mem_toFinset.2 hPPlus)
      rw [Finset.prod_multiset_count_of_subset m
        (primesOverFinsetPlus (K := K) (q : ℕ)) hm_subset, map_prod]
      calc
        ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), Ideal.absNorm (PPlus ^ m.count PPlus)
            = ∏ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ),
                ((q : ℕ) ^ d) ^ m.count PPlus := by
                apply Finset.prod_congr rfl
                intro PPlus hPPlus
                rw [map_pow]
                rw [absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
                  (p := p) (K := K) hp_odd hq hPPlus, hd]
        _ = (q : ℕ) ^
            (d * ∑ PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ), m.count PPlus) := by
                rw [Finset.prod_pow_eq_pow_sum]
                simp [Nat.pow_mul]
        _ = (q : ℕ) ^ (d * m.card) := by rw [hsum_count]
        _ = (q : ℕ) ^ (d * n) := by rw [hm_card]
    ⟨⟨m.prod, hm_prod_ne⟩, hm_norm⟩
  have htoSym_map_val :
      ∀ b : β,
        (toSym b).1.map Subtype.val = UniqueFactorizationMonoid.normalizedFactors b.1.1 := by
    rintro ⟨⟨I, hI_ne⟩, hI_norm⟩
    dsimp [toSym]
    let m := UniqueFactorizationMonoid.normalizedFactors I
    let H : ∀ PPlus, PPlus ∈ m → PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ) := by
      intro PPlus hPPlus
      have hsubset : m.toFinset ⊆ primesOverFinsetPlus (K := K) (q : ℕ) := by
        simpa [m] using
          normalizedFactors_subset_primesOverFinsetPlus_of_absNorm_prime_pow (K := K) hI_ne hI_norm
      exact hsubset (Multiset.mem_toFinset.2 hPPlus)
    change (Multiset.pmap (fun PPlus hPPlus => (⟨PPlus, hPPlus⟩ : α)) m H).map Subtype.val = m
    rw [hpmap_val H]
  have hofSym_nfactors :
      ∀ s : Sym α n,
        UniqueFactorizationMonoid.normalizedFactors (ofSym s).1.1 = s.1.map Subtype.val := by
    intro s
    dsimp [ofSym]
    let m : Multiset (Ideal (𝓞 (oMR K))) := s.1.map Subtype.val
    have hm_prime : ∀ PPlus ∈ m, Prime PPlus := by
      intro PPlus hPPlus
      rcases Multiset.mem_map.1 hPPlus with ⟨QPlus, hQPlus, rfl⟩
      have hQPlus_ne : (QPlus : Ideal (𝓞 (oMR K))) ≠ ⊥ := by
        intro hQPlus_bot
        have hQPlus_norm :=
          absNorm_eq_q_pow_localResidueDegreePlus_of_mem_primesOverFinsetPlus
            (p := p) (K := K) hp_odd hq QPlus.2
        rw [Ideal.absNorm_eq_zero_iff.mpr hQPlus_bot, ← hd] at hQPlus_norm
        exact pow_ne_zero d q.2.ne_zero hQPlus_norm.symm
      exact (Ideal.prime_iff_isPrime hQPlus_ne).2
        ((mem_primesOverFinsetPlus_iff (K := K) (ℓ := (q : ℕ))).1 QPlus.2).1
    change UniqueFactorizationMonoid.normalizedFactors m.prod = m
    exact UniqueFactorizationMonoid.normalizedFactors_prod_of_prime hm_prime
  have hleft : Function.LeftInverse ofSym toSym := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    change ((toSym b).1.map Subtype.val).prod = b.1.1
    rw [htoSym_map_val, Ideal.prod_normalizedFactors_eq_self b.1.2]
  have hright : Function.RightInverse ofSym toSym := by
    intro s
    apply Subtype.ext
    apply Multiset.map_injective Subtype.val_injective
    simpa [hofSym_nfactors s] using htoSym_map_val (ofSym s)
  unfold idealNormMultiplicityNF idealNormMultiplicity
  simpa [β, α, hd, Nat.card_eq_fintype_card] using
    Nat.card_congr (⟨toSym, ofSym, hleft, hright⟩ : β ≃ Sym α n)
lemma dedekind_prime_power_series_eq_localFactorPlus_at_p
    (hp_odd : p ≠ 2) {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (idealNormMultiplicityNF (oMR K) (p ^ k) : ℂ) *
      (((p ^ k : ℕ) : ℂ) ^ (-s))) =
      (dedekindLocalFactor (oMR K) p s)⁻¹ := by
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    have hle : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 :=
      Complex.norm_prime_cpow_le_one_half ⟨p, hp.out⟩ hs
    exact hle.trans_lt (by norm_num)
  rw [dedekindLocalFactorPlus_at_p (p := p) (K := K)]
  trans ∑' k : ℕ, ((p : ℂ) ^ (-s)) ^ k
  · refine tsum_congr fun k => ?_
    rw [idealNormMultiplicityNF_p_pow_eq_one_plus (p := p) (K := K) hp_odd k]
    simp only [Nat.cast_one, one_mul]
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul p k (-s), mul_comm,
      Complex.cpow_mul_nat]
  · simpa using tsum_geometric_of_norm_lt_one hnorm
lemma dedekind_prime_power_series_eq_localFactorPlus
    (hp_odd : p ≠ 2) {q : Nat.Primes} {s : ℂ} (hs : 1 < s.re) :
    (∑' k : ℕ, (idealNormMultiplicityNF (oMR K) ((q : ℕ) ^ k) : ℂ) *
      ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))) =
      (dedekindLocalFactor (oMR K) (q : ℕ) s)⁻¹ := by
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  by_cases hq : (q : ℕ) = p
  · have hq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq
    subst hq'
    simpa using dedekind_prime_power_series_eq_localFactorPlus_at_p
      (p := p) (K := K) hp_odd hs
  · classical
    have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
    set d := localResidueDegreePlus (p := p) (q : ℕ) hq with hd
    let α : Type _ := {PPlus : Ideal (𝓞 (oMR K)) //
      PPlus ∈ primesOverFinsetPlus (K := K) (q : ℕ)}
    let f : ℕ → ℂ := fun k =>
      (idealNormMultiplicityNF (oMR K) ((q : ℕ) ^ k) : ℂ) * ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))
    let g : ℕ → ℂ := fun n =>
      (idealNormMultiplicityNF (oMR K) ((q : ℕ) ^ (d * n)) : ℂ) *
        ((((q : ℕ) ^ (d * n) : ℕ) : ℂ) ^ (-s))
    let z : ℂ := (q : ℂ) ^ (-((d : ℂ) * s))
    have hd_raw_pos : 0 < localResidueDegree (p := p) (q : ℕ) hq := by
      dsimp [localResidueDegree]
      exact orderOf_pos (unitOfPrimeNe (p := p) (q : ℕ) hq)
    have hd_pos : 0 < d := by
      rw [hd]
      by_cases hde : Even (localResidueDegree (p := p) (q : ℕ) hq)
      · rcases hde with ⟨k, hk⟩
        rw [localResidueDegreePlus_eq_half (p := p) hq ⟨k, hk⟩, hk]
        omega
      · rw [localResidueDegreePlus_eq_self (p := p) hq hde]
        exact hd_raw_pos
    have hs_d : 1 < (((d : ℂ) * s).re) := by
      rw [Complex.mul_re]
      simp
      have hd_ge : (1 : ℝ) ≤ d := by
        exact_mod_cast Nat.succ_le_of_lt hd_pos
      nlinarith [hs, hd_ge]
    have hz : ‖z‖ < 1 := by
      have hle : ‖z‖ ≤ 1 / 2 := by
        dsimp [z]
        exact Complex.norm_prime_cpow_le_one_half ⟨q, q.2⟩ hs_d
      exact hle.trans_lt (by norm_num)
    have hg_term : ∀ n : ℕ, g n = (Fintype.card (Sym α n) : ℂ) * z ^ n := by
      intro n
      dsimp [g, z]
      rw [show idealNormMultiplicityNF (oMR K) ((q : ℕ) ^ (d * n)) = Fintype.card (Sym α n) by
        simpa [α, hd] using
          idealNormMultiplicityNF_prime_pow_mul_localResidueDegreePlus_eq_card_sym
            (p := p) (K := K) hp_odd hq n]
      rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul (q : ℕ) (d * n) (-s)]
      have hexp : (((d * n : ℕ) : ℂ) * (-s)) = (-((d : ℂ) * s)) * n := by
        push_cast
        ring
      rw [hexp, Complex.cpow_mul_nat]
    have hg_eq : g = fun n : ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n := funext hg_term
    have hg_hasSum0 : HasSum (fun n : ℕ => (Fintype.card (Sym α n) : ℂ) * z ^ n)
        (((1 - z)⁻¹) ^ Fintype.card α) := by
      rw [← tsum_symGeometric α hz]
      exact (summable_tsum_symGeometric α hz).1.hasSum
    have hg_hasSum : HasSum g (((1 - z)⁻¹) ^ Fintype.card α) := by
      simpa [hg_eq] using hg_hasSum0
    have hf_hasSum : HasSum f (((1 - z)⁻¹) ^ Fintype.card α) := by
      refine (hasSum_iff_hasSum_of_ne_zero_bij
        (f := f) (g := g) (i := fun x : Function.support g => d * x.1) ?_ ?_ ?_).2 hg_hasSum
      · intro x y hxy
        exact Subtype.ext <| Nat.eq_of_mul_eq_mul_left hd_pos hxy
      · intro k hk
        have hk_mult : idealNormMultiplicityNF (oMR K) ((q : ℕ) ^ k) ≠ 0 := fun hk_zero =>
          hk (by simp [f, hk_zero])
        have hk_dvd : d ∣ k := by
          by_contra hk_ndvd
          exact hk_mult <|
            idealNormMultiplicityNF_prime_pow_eq_zero_of_not_dvd_plus
              (p := p) (K := K) hp_odd hq hk_ndvd
        obtain ⟨n, rfl⟩ := hk_dvd
        refine ⟨⟨n, ?_⟩, rfl⟩
        simpa [f, g, mul_comm] using hk
      · intro x
        simp [f, g, mul_comm]
    have hcard_finset :
        (primesOverFinsetPlus (K := K) (q : ℕ)).card =
          localPrimeCountPlus (p := p) (q : ℕ) hq := by
      rw [primesOverFinsetPlus_card_eq_ncard (K := K) (ℓ := (q : ℕ))]
      exact ncard_primesOverPlus_eq_localPrimeCountPlus (p := p) (K := K) hp_odd hq
    have hα_card : Fintype.card α = localPrimeCountPlus (p := p) (q : ℕ) hq := by
      calc
        Fintype.card α = (primesOverFinsetPlus (K := K) (q : ℕ)).card :=
          Fintype.card_of_finset' (primesOverFinsetPlus (K := K) (q : ℕ)) fun PPlus => by simp
        _ = localPrimeCountPlus (p := p) (q : ℕ) hq := hcard_finset
    have hf_hasSum' : HasSum f ((dedekindLocalFactor (oMR K) (q : ℕ) s)⁻¹) := by
      rw [dedekindLocalFactor_eq_pow_localResidueDegreePlus
        (p := p) (K := K) hp_odd hq, ← inv_pow]
      simpa [z, hd, hα_card] using hf_hasSum
    simpa [f] using hf_hasSum'.tsum_eq
lemma dedekindZetaPlus_eq_eulerProduct (hp_odd : p ≠ 2) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (oMR K) s =
      ∏' q : Nat.Primes, (dedekindLocalFactor (oMR K) (q : ℕ) s)⁻¹ := by
  rw [dedekindZeta_eq_tprod_primePowerSeriesNF (L := (oMR K)) hs]
  exact tprod_congr fun q =>
    dedekind_prime_power_series_eq_localFactorPlus (p := p) (K := K) hp_odd hs
lemma evenLProduct_eq_tprod_localFactors {s : ℂ} (hs : 1 < s.re) :
    evenLProduct p s =
      ∏' q : Nat.Primes,
        ∏ χ ∈ evenNontrivialCharacters (p := p),
          (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹ := by
  classical
  unfold evenLProduct
  rw [Finset.prod_congr rfl (fun χ _ => LFunction_eq_prime_tprod_of_localFactors p χ hs)]
  exact (Multipliable.tprod_finsetProd
    (s := evenNontrivialCharacters (p := p))
    (fun χ _ => (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable)).symm
lemma evenLProduct_eq_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    evenLProduct p s =
      ∏' q : Nat.Primes, (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹ := by
  classical
  rw [evenLProduct_eq_tprod_localFactors (p := p) hs]
  refine tprod_congr fun q => ?_
  unfold evenCharLocalFactor
  rw [Finset.prod_inv_distrib]
lemma evenCharLocalFactor_at_p {s : ℂ} :
    evenCharLocalFactor (p := p) p s = 1 := by
  classical
  exact Finset.prod_eq_one fun χ _ => by
    rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, sub_zero]
lemma localFactorsPlus_agree_prime_ne_p (hp_odd : p ≠ 2)
    {q : Nat.Primes} (hq : (q : ℕ) ≠ p) {s : ℂ} :
    dedekindLocalFactor (oMR K) (q : ℕ) s =
      (1 - ((q : ℕ) : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) (q : ℕ) s := by
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  rw [dedekindLocalFactor_eq_pow_localResidueDegreePlus (p := p) (K := K) hp_odd hq]
  symm
  simpa [neg_mul] using
    (trivial_mul_evenCharLocalFactor_eq_pow_localResidueDegreePlus
      (p := p) hp_odd hq (s := s))
lemma localFactorsPlus_agree_at_p (hp_odd : p ≠ 2) {s : ℂ} :
    dedekindLocalFactor (oMR K) p s =
      (1 - (p : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) p s := by
  have : IsCMField K := isCMField_of_cyclotomic (p := p) (K := K) hp_odd
  rw [evenCharLocalFactor_at_p (p := p), mul_one, dedekindLocalFactorPlus_at_p (p := p) (K := K)]
lemma localFactorsPlus_agree (hp_odd : p ≠ 2) {q : Nat.Primes} {s : ℂ} :
    dedekindLocalFactor (oMR K) (q : ℕ) s =
      (1 - ((q : ℕ) : ℂ) ^ (-s)) * evenCharLocalFactor (p := p) (q : ℕ) s := by
  by_cases hq : (q : ℕ) = p
  · have hq' : q = ⟨p, Fact.out⟩ := by
      apply Subtype.ext
      simpa using hq
    subst hq'
    exact localFactorsPlus_agree_at_p (p := p) (K := K) hp_odd
  · exact localFactorsPlus_agree_prime_ne_p (p := p) (K := K) hp_odd hq
theorem dedekindZeta_eq_riemannZeta_mul_evenLProduct_of_one_lt_re
    (hp_odd : p ≠ 2) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta (oMR K) s = riemannZeta s * evenLProduct p s := by
  have hmul_riem :
      Multipliable (fun q : Nat.Primes => (1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹) :=
    (riemannZeta_eulerProduct_hasProd hs).multipliable
  have hmul_even :
      Multipliable (fun q : Nat.Primes => (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹) := by
    classical
    have h1 :
        (fun q : Nat.Primes => (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹) =
          (fun q : Nat.Primes =>
            ∏ χ ∈ evenNontrivialCharacters (p := p),
              (1 - χ ((q : ℕ) : ZMod p) * ((q : ℕ) : ℂ) ^ (-s))⁻¹) := by
      funext q
      unfold evenCharLocalFactor
      rw [Finset.prod_inv_distrib]
    rw [h1]
    exact multipliable_prod (s := evenNontrivialCharacters (p := p)) fun χ _ =>
      (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs).multipliable
  calc
    NumberField.dedekindZeta (oMR K) s
        = ∏' q : Nat.Primes, (dedekindLocalFactor (oMR K) (q : ℕ) s)⁻¹ :=
            dedekindZetaPlus_eq_eulerProduct (p := p) (K := K) hp_odd hs
    _ = ∏' q : Nat.Primes,
          ((1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹ *
            (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹) := by
            refine tprod_congr fun q => ?_
            rw [localFactorsPlus_agree (p := p) (K := K) hp_odd, mul_inv_rev, mul_comm]
    _ = (∏' q : Nat.Primes, (1 - ((q : ℕ) : ℂ) ^ (-s))⁻¹) *
          (∏' q : Nat.Primes, (evenCharLocalFactor (p := p) (q : ℕ) s)⁻¹) := by
            rw [Multipliable.tprod_mul hmul_riem hmul_even]
    _ = riemannZeta s * evenLProduct p s := by
            rw [riemannZeta_eulerProduct_tprod hs, evenLProduct_eq_eulerProduct (p := p) hs]
theorem tendsto_sub_one_mul_riemannZeta_mul_evenLProduct :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * (riemannZeta (s : ℂ) * evenLProduct p (s : ℂ)))
      (𝓝[>] 1)
      (𝓝 (evenLProduct p (1 : ℂ))) := by
  classical
  have h_cont : Continuous (evenLProduct p) :=
    continuous_finsetProd _ fun χ hχ =>
      (DirichletCharacter.differentiable_LFunction (Finset.mem_filter.mp hχ).2.2).continuous
  have h_embed :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        by
          filter_upwards [self_mem_nhdsWithin] with s hs h
          exact absurd (Complex.ofReal_injective h) (ne_of_gt hs)⟩
  have h_zeta : Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 1) :=
    riemannZeta_residue_one.comp h_embed
  have h_lprod : Filter.Tendsto (fun s : ℝ => evenLProduct p (s : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (evenLProduct p 1)) :=
    (h_cont.tendsto 1).comp (h_embed.mono_right nhdsWithin_le_nhds)
  have h_prod := h_zeta.mul h_lprod
  rw [one_mul] at h_prod
  refine (Filter.tendsto_congr' ?_).mp h_prod
  filter_upwards [self_mem_nhdsWithin] with s _
  ring
theorem tendsto_sub_one_mul_dedekindZetaPlus_via_evenLProducts (hp_odd : p ≠ 2) :
    Filter.Tendsto
      (fun s : ℝ ↦ (s - 1) * NumberField.dedekindZeta (oMR K) (s : ℂ))
      (𝓝[>] 1)
      (𝓝 (evenLProduct p (1 : ℂ))) := by
  refine (Filter.tendsto_congr' ?_).mp
    (tendsto_sub_one_mul_riemannZeta_mul_evenLProduct (p := p))
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [dedekindZeta_eq_riemannZeta_mul_evenLProduct_of_one_lt_re
    (p := p) (K := K) hp_odd (by exact_mod_cast hs)]
theorem complex_maximalRealSubfield_residue_eq_evenLProduct_one (hp_odd : p ≠ 2) :
    ((NumberField.dedekindZeta_residue (oMR K) : ℝ) : ℂ) = evenLProduct p (1 : ℂ) :=
  tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT (oMR K))
    (tendsto_sub_one_mul_dedekindZetaPlus_via_evenLProducts (p := p) (K := K) hp_odd)
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
variable (p : ℕ) [hp : Fact p.Prime]
lemma norm_sum_range_cos_le {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (n : ℕ) :
    ‖∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)‖ ≤
      2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
  let z : ℂ := Complex.exp ((2 * Real.pi * x) * Complex.I)
  have hz_ne_one : z ≠ 1 := by
    intro hz
    have hexp : Complex.exp ((2 * Real.pi * x) * Complex.I) = 1 := by simpa [z] using hz
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
    have him : 2 * Real.pi * x = (m : ℝ) * (2 * Real.pi) := by
      simpa using congrArg Complex.im hm
    have hm_pos : (0 : ℝ) < m := by nlinarith [Real.pi_pos, hx₀, him]
    have hm_lt_one : (m : ℝ) < 1 := by nlinarith [Real.pi_pos, hx₁, him]
    have hm_pos_int : 0 < m := by exact_mod_cast hm_pos
    have hm_lt_one_int : m < 1 := by exact_mod_cast hm_lt_one
    lia
  have hre :
      ((∑ i ∈ Finset.range n, z ^ i).re : ℝ) =
        ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show z ^ i = Complex.exp (((2 * Real.pi * x * i : ℝ) : ℂ) * Complex.I) by
      rw [← Complex.exp_nat_mul]
      congr 1
      norm_num
      ring, Complex.exp_ofReal_mul_I_re]
  have hgeom : ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ 2 / ‖z - 1‖ := by
    calc
      ‖∑ i ∈ Finset.range n, z ^ i‖ = ‖(z ^ n - 1) / (z - 1)‖ := by
        rw [geom_sum_eq hz_ne_one]
      _ = ‖z ^ n - 1‖ / ‖z - 1‖ := by rw [Complex.norm_div]
      _ ≤ 2 / ‖z - 1‖ := by
        have hden : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz_ne_one)
        have hnum : ‖z ^ n - 1‖ ≤ 2 := by
          calc
            ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 1 + 1 := by
              rw [norm_pow]
              have hz_norm : ‖z‖ = 1 := by
                simpa [z] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
              rw [hz_norm]
              simp
            _ = 2 := by norm_num
        simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden.le)
  calc
    ‖∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)‖
      = ‖((∑ i ∈ Finset.range n, z ^ i).re : ℝ)‖ := by rw [hre]
    _ ≤ ‖∑ i ∈ Finset.range n, z ^ i‖ := by
      simpa using (RCLike.norm_re_le_norm (∑ i ∈ Finset.range n, z ^ i))
    _ ≤ 2 / ‖z - 1‖ := hgeom
    _ = 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
      simp [z, norm_sub_rev]
lemma continuous_shiftedCosTerm (x : ℝ) (i : ℕ) :
    Continuous fun s : ℝ =>
      Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)) := by
  refine Continuous.div continuous_const ?_ ?_
  · exact Continuous.const_cpow Complex.continuous_ofReal (Or.inl (Nat.cast_add_one_ne_zero i))
  · intro s h
    exact (Nat.cast_add_one_ne_zero i) ((Complex.cpow_eq_zero_iff _ _).mp h).1
lemma hasSum_shifted_cosZeta (x s : ℝ) (hs : 1 < s) :
    HasSum (fun n : ℕ => Real.cos (2 * Real.pi * x * (n + 1)) / ((n + 1 : ℂ) ^ (s : ℂ)))
      (HurwitzZeta.cosZeta x s) := by
  let f : ℕ → ℂ := fun n => Real.cos (2 * Real.pi * x * n) / ((n : ℂ) ^ (s : ℂ))
  have hfull : HasSum f (HurwitzZeta.cosZeta x s) := by
    simpa [f] using HurwitzZeta.hasSum_nat_cosZeta x (show 1 < ((s : ℂ)).re by simpa)
  have hshift : HasSum (fun n : ℕ => f (n + 1)) (∑' n : ℕ, f (n + 1)) :=
    ((summable_nat_add_iff 1).2 hfull.summable).hasSum
  have hfull' : HasSum f (f 0 + ∑' n : ℕ, f (n + 1)) := hshift.zero_add
  have hvalue : (∑' n : ℕ, f (n + 1)) = HurwitzZeta.cosZeta x s := by
    have hs0 : ((s : ℂ)) ≠ 0 := by
      exact_mod_cast (show s ≠ 0 by linarith)
    have hf0 : f 0 = 0 := by
      simp [f, hs0]
    have := tendsto_nhds_unique hfull'.tendsto_sum_nat hfull.tendsto_sum_nat
    simpa [hf0] using this
  exact hvalue ▸ hshift.congr_fun (fun n => by simp [f])
lemma norm_sum_range_shifted_cos_term_le {x s : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) (hs : 1 ≤ s)
    (m n : ℕ) :
    ‖∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ))‖ ≤
      (8 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
        (1 / (m + 1 : ℝ) ^ s) := by
  let a : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ) ^ s
  let z : ℕ → ℂ := fun k => Real.cos (2 * Real.pi * x * (k + 1))
  have ha : Antitone a := by
    intro i j hij
    have hij' : (i + 1 : ℝ) ≤ j + 1 := by exact_mod_cast Nat.succ_le_succ hij
    have hi_pos : 0 < (i + 1 : ℝ) := by positivity
    have hs_nonneg : 0 ≤ s := le_trans zero_lt_one.le hs
    have hpow : (i + 1 : ℝ) ^ s ≤ (j + 1 : ℝ) ^ s :=
      Real.rpow_le_rpow hi_pos.le hij' hs_nonneg
    simpa [a, one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hi_pos _) hpow
  have ha_nonneg : ∀ k, 0 ≤ a k := by
    intro k
    positivity
  have hzbound :
      ∀ k, ‖∑ i ∈ Finset.range k, z i‖ ≤
        4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro k
    let f : ℕ → ℝ := fun i => Real.cos (2 * Real.pi * x * i)
    have hsum0 := Finset.sum_range_add f 1 k
    have hsum :
        ∑ i ∈ Finset.range k, Real.cos (2 * Real.pi * x * (i + 1)) =
          ∑ i ∈ Finset.range (k + 1), Real.cos (2 * Real.pi * x * i) - 1 := by
      rw [Finset.sum_range_one] at hsum0
      calc
        ∑ i ∈ Finset.range k, Real.cos (2 * Real.pi * x * (i + 1))
            = ∑ i ∈ Finset.range k, f (1 + i) := by simp [f, add_comm]
        _ = ∑ i ∈ Finset.range (k + 1), f i - f 0 :=
              eq_sub_iff_add_eq.mpr (by
                simpa [add_comm, add_left_comm, add_assoc, Nat.add_comm] using hsum0.symm)
        _ = ∑ i ∈ Finset.range (k + 1), Real.cos (2 * Real.pi * x * i) - 1 := by simp [f]
    rw [show (∑ i ∈ Finset.range k, z i) =
        ((∑ i ∈ Finset.range k, Real.cos (2 * Real.pi * x * (i + 1)) : ℝ) : ℂ) by
          simp [z, Complex.ofReal_sum]]
    rw [Complex.norm_real, hsum]
    calc
      |∑ i ∈ Finset.range (k + 1), Real.cos (2 * Real.pi * x * i) - 1|
          ≤ |∑ i ∈ Finset.range (k + 1), Real.cos (2 * Real.pi * x * i) - 0| +
              |0 - (1 : ℝ)| := by
              simpa using
                abs_sub_le
                  (∑ i ∈ Finset.range (k + 1), Real.cos (2 * Real.pi * x * i)) 0 1
      _ ≤ |∑ i ∈ Finset.range (k + 1), Real.cos (2 * Real.pi * x * i)| + 1 := by simp
      _ ≤ (2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) + 1 := by
            have hcos :
                |∑ i ∈ Finset.range (k + 1), Real.cos (2 * Real.pi * x * i)| ≤
                  2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
              simpa using norm_sum_range_cos_le hx₀ hx₁ (k + 1)
            exact add_le_add hcos le_rfl
      _ ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ +
            2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
            have hdenom :
                1 ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
              have hnorm : ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≤ 2 := by
                calc
                  ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
                      ≤ ‖(1 : ℂ)‖ + ‖Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                        norm_sub_le _ _
                  _ = 1 + 1 := by
                        rw [norm_one]
                        simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
                  _ = 2 := by norm_num
              have hzero : (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0 := by
                intro hzero
                have hexp : Complex.exp ((2 * Real.pi * x) * Complex.I) = 1 := by
                  simpa [eq_comm] using sub_eq_zero.mp hzero
                obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
                have him : 2 * Real.pi * x = (m : ℝ) * (2 * Real.pi) := by
                  simpa using congrArg Complex.im hm
                have hm_pos : (0 : ℝ) < m := by nlinarith [Real.pi_pos, hx₀, him]
                have hm_lt_one : (m : ℝ) < 1 := by nlinarith [Real.pi_pos, hx₁, him]
                have hm_pos_int : 0 < m := by exact_mod_cast hm_pos
                have hm_lt_one_int : m < 1 := by exact_mod_cast hm_lt_one
                lia
              have hden_pos : 0 < ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                norm_pos_iff.mpr hzero
              simpa using (one_le_div hden_pos).2 hnorm
            linarith
      _ = 4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by ring
  calc
    ‖∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (m + i + 1)) / (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ))‖
        = ‖∑ i ∈ Finset.range n, a (m + i) • z (m + i)‖ := by
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            have hcpow :
                (((m + i + 1 : ℕ) : ℂ) ^ (s : ℂ)) =
                  ((((m + i + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ) := by
              simpa using
                (Complex.ofReal_cpow (x := (m + i + 1 : ℝ)) (by positivity) (y := s)).symm
            rw [hcpow]
            simp [a, z, div_eq_mul_inv, mul_comm, mul_left_comm]
    _ ≤ (2 * (4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) * a m :=
          norm_sum_range_shift_smul_le_of_antitone_of_nonneg_of_bounded ha ha_nonneg hzbound m n
    _ = (8 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) *
          (1 / (m + 1 : ℝ) ^ s) := by
          have hcoef :
              (2 * (4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) =
                8 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
            ring
          rw [hcoef]
lemma exists_tendsto_sum_range_cos_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    ∃ l : ℝ,
      Tendsto
        (fun n ↦
          ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i)
        atTop (𝓝 l) := by
  let f : ℕ → ℝ := fun n => if n = 0 then 1 else 1 / n
  let z : ℕ → ℝ := fun n => if n = 0 then 0 else Real.cos (2 * Real.pi * x * n)
  have hf : Antitone f := by
    intro a b hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp [f]
      · simp [f, hb.ne']
        have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast Nat.succ_le_of_lt hb
        simpa [one_div] using one_div_le_one_div_of_le zero_lt_one hb1
    · have hb : 0 < b := lt_of_lt_of_le ha hab
      simp [f, ha.ne', (Nat.ne_of_gt hb)]
      have ha' : (0 : ℝ) < a := by exact_mod_cast ha
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      simpa [one_div] using one_div_le_one_div_of_le ha' hab'
  have hf0 : Tendsto f atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa [f]
      using
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0))
  have hbound :
      ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤
        4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    intro n
    rcases n.eq_zero_or_pos with rfl | hn
    · have : 0 ≤ 4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
        positivity
      simpa [z] using this
    · let g : ℕ → ℝ := fun i => Real.cos (2 * Real.pi * x * i)
      have hz0 := Finset.sum_range_add z 1 (n - 1)
      have hg0 := Finset.sum_range_add g 1 (n - 1)
      have hsum :
          ∑ i ∈ Finset.range n, z i =
            ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) - 1 := by
        have hn' : 1 + (n - 1) = n := by
          simpa [Nat.add_comm] using Nat.succ_pred_eq_of_pos hn
        have hz0' :
            ∑ x ∈ Finset.range n, z x =
              ∑ x ∈ Finset.range 1, z x + ∑ x ∈ Finset.range (n - 1), z (1 + x) := by
          simpa [hn', add_comm] using hz0
        have hg0' :
            ∑ x ∈ Finset.range n, g x =
              ∑ x ∈ Finset.range 1, g x + ∑ x ∈ Finset.range (n - 1), g (1 + x) := by
          simpa [hn', add_comm] using hg0
        rw [Finset.sum_range_one] at hz0' hg0'
        calc
          ∑ i ∈ Finset.range n, z i = z 0 + ∑ i ∈ Finset.range (n - 1), z (1 + i) := by
            simpa [add_comm, add_left_comm, add_assoc, Nat.add_comm] using hz0'
          _ = ∑ i ∈ Finset.range (n - 1), g (1 + i) := by simp [z, g]
          _ = ∑ i ∈ Finset.range n, g i - g 0 :=
                eq_sub_iff_add_eq.mpr (by
                  simpa [add_comm, add_left_comm, add_assoc, Nat.add_comm] using hg0'.symm)
          _ = ∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) - 1 := by simp [g]
      rw [hsum]
      calc
        |∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) - 1|
            ≤ |∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i) - 0| +
                |0 - (1 : ℝ)| := by
                simpa using
                  abs_sub_le
                    (∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)) 0 1
        _ ≤ |∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)| + 1 := by simp
        _ ≤ (2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖) + 1 := by
              have hcos :
                  |∑ i ∈ Finset.range n, Real.cos (2 * Real.pi * x * i)| ≤
                    2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
                simpa using norm_sum_range_cos_le hx₀ hx₁ n
              exact add_le_add hcos le_rfl
        _ ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ +
              2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
              have hnorm : ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≤ 2 := by
                calc
                  ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
                      ≤ ‖(1 : ℂ)‖ + ‖Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                        norm_sub_le _ _
                  _ = 1 + 1 := by
                        rw [norm_one]
                        simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
                  _ = 2 := by norm_num
              have hzero : (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0 := by
                intro hzero
                have hexp : Complex.exp ((2 * Real.pi * x) * Complex.I) = 1 := by
                  simpa [eq_comm] using sub_eq_zero.mp hzero
                obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
                have him : 2 * Real.pi * x = (m : ℝ) * (2 * Real.pi) := by
                  simpa using congrArg Complex.im hm
                have hm_pos : (0 : ℝ) < m := by nlinarith [Real.pi_pos, hx₀, him]
                have hm_lt_one : (m : ℝ) < 1 := by nlinarith [Real.pi_pos, hx₁, him]
                have hm_pos_int : 0 < m := by exact_mod_cast hm_pos
                have hm_lt_one_int : m < 1 := by exact_mod_cast hm_lt_one
                lia
              have hden_pos : 0 < ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
                norm_pos_iff.mpr hzero
              have hdenom :
                  1 ≤ 2 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
                simpa using (one_le_div hden_pos).2 hnorm
              linarith
        _ = 4 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by ring
  have hcauchy := hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hbound
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨l, ?_⟩
  have hseries :
      (fun n ↦ ∑ i ∈ Finset.range n, f i • z i) =
        fun n ↦
          ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i := by
    funext n
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [f, z]
    · simp [f, z, hi.ne', smul_eq_mul, div_eq_mul_inv, mul_comm]
  exact hseries ▸ hl
lemma tendsto_sum_range_cos_div_nat {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i)
      atTop (𝓝 (-Real.log (2 * Real.sin (Real.pi * x)))) := by
  obtain ⟨l, hl⟩ := exists_tendsto_sum_range_cos_div_nat hx₀ hx₁
  let coeff : ℕ → ℝ := fun n =>
    if n = 0 then 0 else Real.cos (2 * Real.pi * x * n) / n
  have habel :
      Tendsto (fun r : ℝ => ∑' n, coeff n * r ^ n) (𝓝[<] 1) (𝓝 l) :=
    Real.tendsto_tsum_powerSeries_nhdsWithin_lt hl
  have hcoeff :
      Set.EqOn
        (fun r : ℝ => ∑' n, coeff n * r ^ n)
        (fun r : ℝ =>
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (Set.Ioo 0 1) := by
    intro r hr
    have hr₀ : 0 ≤ r := hr.1.le
    have hr₁ : r < 1 := hr.2
    calc
      ∑' n : ℕ, coeff n * r ^ n
          = ∑' n : ℕ, (r ^ n / n) * Real.cos (2 * Real.pi * x * n) := by
              refine tsum_congr fun n : ℕ => ?_
              rcases n.eq_zero_or_pos with rfl | hn
              · simp [coeff]
              · simp [coeff, hn.ne', div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖ :=
            (hasSum_mul_rpow_cos x r hr₀ hr₁).tsum_eq
  have habel' :
      Tendsto
        (fun r : ℝ =>
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (𝓝[<] 1) (𝓝 l) :=
    Tendsto.congr' (hcoeff.eventuallyEq_of_mem (Ioo_mem_nhdsLT zero_lt_one)) habel
  have hzero :
      (1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I) ≠ 0 := by
    intro hzero
    have hexp : Complex.exp ((2 * Real.pi * x) * Complex.I) = 1 := by
      simpa [eq_comm] using sub_eq_zero.mp hzero
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp
    have him : 2 * Real.pi * x = (m : ℝ) * (2 * Real.pi) := by
      simpa using congrArg Complex.im hm
    have hm_pos : (0 : ℝ) < m := by nlinarith [Real.pi_pos, hx₀, him]
    have hm_lt_one : (m : ℝ) < 1 := by nlinarith [Real.pi_pos, hx₁, him]
    have hm_pos_int : 0 < m := by exact_mod_cast hm_pos
    have hm_lt_one_int : m < 1 := by exact_mod_cast hm_lt_one
    lia
  have hcont :
      Tendsto
        (fun r : ℝ =>
          -Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖)
        (𝓝[<] 1)
        (𝓝 (-Real.log ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖)) := by
    have hinner :
        ContinuousAt
          (fun r : ℝ => (1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)) 1 :=
      continuousAt_const.sub
        (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have hnorm :
        ContinuousAt
          (fun r : ℝ =>
            ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) 1 :=
      continuous_norm.continuousAt.comp hinner
    have hnorm_ne :
        ‖(1 : ℂ) - ((1 : ℝ) : ℂ) *
            Complex.exp ((2 * Real.pi * x) * Complex.I)‖ ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hzero)
    have hlog :
        ContinuousAt
          (fun r : ℝ =>
            Real.log ‖(1 : ℂ) - (r : ℂ) * Complex.exp ((2 * Real.pi * x) * Complex.I)‖) 1 :=
      hnorm.log hnorm_ne
    convert! tendsto_nhdsWithin_of_tendsto_nhds hlog.neg.tendsto using 2
    simp
  have ht₀ : 0 < 2 * Real.pi * x := by nlinarith [hx₀, Real.pi_pos]
  have ht₂π : 2 * Real.pi * x < 2 * Real.pi := by nlinarith [hx₁, Real.pi_pos]
  have hnorm_value :
      ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ =
        2 * Real.sin (Real.pi * x) := by
    simpa [show (2 * Real.pi * x) / 2 = Real.pi * x by ring] using
      norm_one_sub_exp_ofReal_mul_I ht₀ ht₂π
  have hl_eq : l = -Real.log (2 * Real.sin (Real.pi * x)) :=
    tendsto_nhds_unique habel' (by simpa [hnorm_value] using hcont)
  simpa [hl_eq] using hl
lemma tendsto_sum_range_shifted_cos_one {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (1 : ℂ)))
      atTop (nhds ((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)) := by
  let F : ℕ → ℂ := fun n =>
    ((∑ i ∈ Finset.range n,
        if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i : ℝ) : ℂ)
  have hbase : Tendsto F atTop (nhds (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))) := by
    simpa [F] using (tendsto_sum_range_cos_div_nat hx₀ hx₁).ofReal
  have hshifted : Tendsto (fun n : ℕ => F (n + 1)) atTop
      (nhds (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))) :=
    (tendsto_add_atTop_iff_nat 1).2 hbase
  refine hshifted.congr' <| Filter.Eventually.of_forall fun n => ?_
  have hsum :=
    Finset.sum_range_add
      (fun i : ℕ => (((if i = 0 then 0 else Real.cos (2 * Real.pi * x * i) / i : ℝ)) : ℂ)) 1 n
  simpa [F, add_comm, add_left_comm, add_assoc] using hsum
lemma uniformCauchySeqOn_shiftedCosPartialSums {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    UniformCauchySeqOn
      (fun n (s : ℝ) => ∑ i ∈ Finset.range n,
        Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
      atTop (Set.Ici 1) := by
  rw [Metric.uniformCauchySeqOn_iff]
  let B : ℝ :=
    8 / ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖
  have hdenom : 0 < ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ := by
    have ht₀ : 0 < 2 * Real.pi * x := by nlinarith [hx₀, Real.pi_pos]
    have ht₂π : 2 * Real.pi * x < 2 * Real.pi := by nlinarith [hx₁, Real.pi_pos]
    have hnorm_eq :
        ‖(1 : ℂ) - Complex.exp ((2 * Real.pi * x) * Complex.I)‖ =
          2 * Real.sin (Real.pi * x) := by
      simpa [show (2 * Real.pi * x) / 2 = Real.pi * x by ring] using
        norm_one_sub_exp_ofReal_mul_I ht₀ ht₂π
    rw [hnorm_eq]
    have hxπ : Real.pi * x ∈ Set.Ioo 0 Real.pi := by
      constructor <;> nlinarith [hx₀, hx₁, Real.pi_pos]
    have hsin : 0 < Real.sin (Real.pi * x) := Real.sin_pos_of_mem_Ioo hxπ
    positivity
  have hB_pos : 0 < B := by
    positivity
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (div_pos hε hB_pos)
  refine ⟨N, ?_⟩
  have htail_bound :
      ∀ ⦃m n : ℕ⦄, N ≤ m → m ≤ n → ∀ s ∈ Set.Ici (1 : ℝ),
        dist
            (∑ i ∈ Finset.range m,
              Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
            (∑ i ∈ Finset.range n,
              Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ)))
          < ε := by
    intro m n hm hmn s hs
    let term : ℕ → ℂ := fun k =>
      Real.cos (2 * Real.pi * x * (k + 1)) / ((k + 1 : ℂ) ^ (s : ℂ))
    have hsplit :
        ∑ i ∈ Finset.range n, term i =
          ∑ i ∈ Finset.range m, term i + ∑ i ∈ Finset.range (n - m), term (m + i) := by
      simpa [term, Nat.add_sub_of_le hmn] using Finset.sum_range_add term m (n - m)
    have hs' : 1 ≤ s := hs
    rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖∑ i ∈ Finset.range n, term i - ∑ i ∈ Finset.range m, term i‖
          = ‖∑ i ∈ Finset.range (n - m), term (m + i)‖ := by
              rw [hsplit]
              ring_nf
      _ ≤ B * (1 / (m + 1 : ℝ) ^ s) := by
            simpa [B, term, add_assoc, add_comm, add_left_comm] using
              norm_sum_range_shifted_cos_term_le (x := x) hx₀ hx₁ hs' m (n - m)
      _ ≤ B * (1 / (m + 1 : ℝ)) := by
            have hm1 : 1 ≤ (m + 1 : ℝ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
            have hpow : (m + 1 : ℝ) ^ (1 : ℝ) ≤ (m + 1 : ℝ) ^ s := by
              simpa using Real.rpow_le_rpow_of_exponent_le hm1 hs'
            have hpow_inv : 1 / (m + 1 : ℝ) ^ s ≤ 1 / (m + 1 : ℝ) := by
              simpa [Real.rpow_one] using
                (one_div_le_one_div_of_le (show 0 < (m + 1 : ℝ) ^ (1 : ℝ) by positivity) hpow)
            exact mul_le_mul_of_nonneg_left hpow_inv hB_pos.le
      _ ≤ B * (1 / (N + 1 : ℝ)) := by
            have hm_inv : 1 / (m + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) :=
              one_div_le_one_div_of_le (show 0 < (N + 1 : ℝ) by positivity)
                (by exact_mod_cast Nat.succ_le_succ hm)
            exact mul_le_mul_of_nonneg_left hm_inv hB_pos.le
      _ < B * (ε / B) :=
            mul_lt_mul_of_pos_left hN hB_pos
      _ = ε := by
            field_simp [hB_pos.ne']
  intro m hm n hn s hs
  rcases le_total m n with hmn | hnm
  · exact htail_bound hm hmn s hs
  · simpa [dist_comm] using htail_bound hn hnm s hs
theorem cosZeta_one_eq_boundary {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    HurwitzZeta.cosZeta x 1 = (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)) := by
  let boundary : ℂ := (((-Real.log (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ))
  let S : ℕ → ℝ → ℂ := fun n s =>
    ∑ i ∈ Finset.range n,
      Real.cos (2 * Real.pi * x * (i + 1)) / ((i + 1 : ℂ) ^ (s : ℂ))
  let G : ℝ → ℂ := fun s => if hs : s = 1 then boundary else HurwitzZeta.cosZeta x s
  have hCauchy : UniformCauchySeqOn S atTop (Set.Ici 1) := by
    simpa [S] using uniformCauchySeqOn_shiftedCosPartialSums (x := x) hx₀ hx₁
  have hpoint : ∀ s ∈ Set.Ici (1 : ℝ), Tendsto (fun n => S n s) atTop (𝓝 (G s)) := by
    intro s hs
    by_cases hs1 : s = 1
    · simpa [S, G, hs1, boundary] using tendsto_sum_range_shifted_cos_one (x := x) hx₀ hx₁
    · have hslt : 1 < s := lt_of_le_of_ne hs (by simpa [eq_comm] using hs1)
      simpa [S, G, hs1] using (hasSum_shifted_cosZeta (x := x) s hslt).tendsto_sum_nat
  have hunif : TendstoUniformlyOn S G atTop (Set.Ici 1) :=
    hCauchy.tendstoUniformlyOn_of_tendsto hpoint
  have hcont : ContinuousOn G (Set.Ici (1 : ℝ)) := by
    apply hunif.continuousOn
    refine Frequently.of_forall fun n => ?_
    classical
    dsimp [S]
    exact Continuous.continuousOn <|
      continuous_finsetSum _ fun i _ => continuous_shiftedCosTerm x i
  have hG_right : Tendsto G (𝓝[Set.Ioi 1] 1) (𝓝 boundary) := by
    have hG_Ici : Tendsto G (𝓝[Set.Ici 1] 1) (𝓝 boundary) := by
      simpa [G, boundary] using (hcont 1 (by simp)).tendsto
    exact hG_Ici.mono_left (nhdsWithin_mono _ Set.Ioi_subset_Ici_self)
  have hG_eq : G =ᶠ[𝓝[Set.Ioi 1] 1] fun s : ℝ => HurwitzZeta.cosZeta x s := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    have hslt : 1 < s := by simpa using hs
    simp [G, ne_of_gt hslt]
  have hcos_right : Tendsto (fun s : ℝ => HurwitzZeta.cosZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 boundary) :=
    Tendsto.congr' hG_eq hG_right
  have hcos_cont : Tendsto (fun s : ℝ => HurwitzZeta.cosZeta x s) (𝓝[Set.Ioi 1] 1)
      (𝓝 (HurwitzZeta.cosZeta x 1)) := by
    have hxadd : (x : UnitAddCircle) ≠ 0 := by
      intro hxzero
      rw [AddCircle.coe_eq_zero_iff] at hxzero
      rcases hxzero with ⟨n, hn⟩
      have hn' : (n : ℝ) = x := by simpa using hn
      have hn_pos : (0 : ℝ) < n := by nlinarith [hx₀, hn']
      have hn_lt_one : (n : ℝ) < 1 := by nlinarith [hx₁, hn']
      have hn_pos_int : 0 < n := by exact_mod_cast hn_pos
      have hn_lt_one_int : n < 1 := by exact_mod_cast hn_lt_one
      lia
    have hcomplex : Tendsto (fun z : ℂ => HurwitzZeta.cosZeta x z) (𝓝 (1 : ℂ))
        (𝓝 (HurwitzZeta.cosZeta x 1)) :=
      (HurwitzZeta.differentiableAt_cosZeta (a := (x : UnitAddCircle)) (s := (1 : ℂ))
        (Or.inr hxadd)).continuousAt.tendsto
    have hreal : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto
    have hcomp : Tendsto (fun s : ℝ => HurwitzZeta.cosZeta x (s : ℂ)) (𝓝 (1 : ℝ))
        (𝓝 (HurwitzZeta.cosZeta x 1)) := by
      simpa [Function.comp] using! hcomplex.comp hreal
    exact hcomp.mono_left nhdsWithin_le_nhds
  simpa [boundary] using (tendsto_nhds_unique hcos_right hcos_cont).symm
theorem cosZeta_toAddCircle_one_eq_boundary {a : ZMod p} (ha : a ≠ 0) :
    HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
      (((-Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ)) := by
  have hx := zmod_val_div_prime_mem_Ioo (p := p) ha
  rw [ZMod.toAddCircle_apply]
  exact cosZeta_one_eq_boundary (x := (a.val / p : ℝ)) hx.1 hx.2
lemma norm_one_sub_stdAddChar {a : ZMod p} (ha : a ≠ 0) :
    ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ =
      2 * Real.sin (Real.pi * (a.val / p : ℝ)) := by
  have hx := zmod_val_div_prime_mem_Ioo (p := p) ha
  have ht₀ : 0 < 2 * Real.pi * (a.val / p : ℝ) := by
    nlinarith [hx.1, Real.pi_pos]
  have ht₂π : 2 * Real.pi * (a.val / p : ℝ) < 2 * Real.pi := by
    nlinarith [hx.2, Real.pi_pos]
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hexp :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) / (p : ℂ)) =
        Complex.exp ((((2 * Real.pi * (a.val / p : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [hexp]
  convert norm_one_sub_exp_ofReal_mul_I ht₀ ht₂π using 1
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
variable (p : ℕ) [hp : Fact p.Prime]
theorem even_LFunction_one_eq_evenLValueRhs
    {χ : DirichletCharacter ℂ p} (hχ_prim : χ.IsPrimitive) (hχ_even : χ.Even)
    (hχ_ne_one : χ ≠ 1) :
    DirichletCharacter.LFunction χ 1 = evenLValueRhs p χ := by
  let _ := hχ_prim
  change ZMod.LFunction (fun a : ZMod p => χ a) 1 = evenLValueRhs p χ
  have hp_ne_one : p ≠ 1 := hp.out.ne_one
  have hχinv_ne_one : χ⁻¹ ≠ 1 := by
    intro h
    apply hχ_ne_one
    calc
      χ = χ⁻¹⁻¹ := (inv_inv χ).symm
      _ = 1 := by simp [h]
  have hχinv_even : (χ⁻¹).Even := by
    rw [DirichletCharacter.Even] at hχ_even ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_even]
    simp
  have hχinv_prim : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def]
    have hdiv : (χ⁻¹).conductor ∣ p := DirichletCharacter.conductor_dvd_level (χ⁻¹)
    rcases (Nat.dvd_prime hp.out).mp hdiv with hcond | hcond
    · exact (hχinv_ne_one <| (DirichletCharacter.eq_one_iff_conductor_eq_one).2 hcond).elim
    · exact hcond
  have hχinv_zero : χ⁻¹ 0 = 0 := (χ⁻¹).map_zero' hp_ne_one
  let χinv : ZMod p → ℂ := fun a => χ⁻¹ a
  have hdft :
      ZMod.LFunction (ZMod.dft χinv) 1 =
        ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 := by
    simpa using
      (ZMod.LFunction_dft (Φ := χinv) (s := (1 : ℂ))
        (hs := Or.inl hχinv_zero))
  have hft :
      ZMod.dft χinv = fun a : ZMod p =>
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * χ a := by
    funext a
    simpa [χinv, hχ_even.to_fun a, mul_comm] using
      (DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum
        (χ := χ⁻¹) hχinv_prim a)
  have hleft :
      ZMod.LFunction (ZMod.dft χinv) 1 =
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * ZMod.LFunction χ 1 := by
    rw [hft, ZMod.LFunction, ZMod.LFunction]
    calc
      (p : ℂ) ^ (-1 : ℂ) *
          ∑ a : ZMod p,
            (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * χ a) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1
          = (p : ℂ) ^ (-1 : ℂ) *
              (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) *
                ∑ a : ZMod p, χ a * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) 1) := by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by ring
      _ = gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * ZMod.LFunction χ 1 := by
            rw [ZMod.LFunction]
            ring
  have hsum_sin_zero :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 = 0 := by
    refine (hχinv_even.to_fun.mul_odd fun a => ?_).sum_eq_zero
    simpa using HurwitzZeta.sinZeta_neg (ZMod.toAddCircle a) (1 : ℂ)
  have hsum_isin_zero :
      ∑ a : ZMod p, χ⁻¹ a *
          (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) = 0 := by
    calc
      ∑ a : ZMod p, χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)
          = Complex.I *
              ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1 := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun a _ => by ring
      _ = 0 := by rw [hsum_sin_zero, mul_zero]
  have hsum_exp :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 =
        ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := by
    calc
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1
          = ∑ a : ZMod p,
              (χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
                χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1)) := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  have hneg : ZMod.toAddCircle (-a) = -ZMod.toAddCircle a :=
                    map_neg ZMod.toAddCircle a
                  rw [hneg, HurwitzZeta.expZeta, HurwitzZeta.cosZeta_neg,
                    HurwitzZeta.sinZeta_neg]
                  ring
      _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 -
            ∑ a : ZMod p,
              χ⁻¹ a * (Complex.I * HurwitzZeta.sinZeta (ZMod.toAddCircle a) 1) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := by
            rw [hsum_isin_zero, sub_zero]
  have hboundary :
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 =
        -evenLValueLogSum p χ := by
    unfold evenLValueLogSum
    calc
      ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1
          = ∑ a : ZMod p,
              -(χ⁻¹ a *
                ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)) := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  rcases eq_or_ne a 0 with rfl | ha
                  · simp [hχinv_zero]
                  · rw [cosZeta_toAddCircle_one_eq_boundary (p := p) ha]
                    have hlog :
                        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) =
                          ((Real.log
                            (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ) := by
                      congr 1
                      rw [norm_one_sub_stdAddChar (p := p) ha]
                    rw [hlog]
                    rw [show
                      (((-Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ)) =
                        -(((Real.log
                          (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ)) by simp]
                    exact mul_neg (χ⁻¹ a)
                      (((Real.log (2 * Real.sin (Real.pi * (a.val / p : ℝ))) : ℝ) : ℂ))
      _ = -∑ a : ZMod p,
            χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) :=
              Finset.sum_neg_distrib
                (s := Finset.univ)
                (f := fun a : ZMod p =>
                  χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ))
      _ = -evenLValueLogSum p χ := rfl
  have hcard_ne : (Fintype.card (ZMod p) : ℂ) ≠ 0 := by
    simpa [ZMod.card] using (show (p : ℂ) ≠ 0 by exact_mod_cast hp.out.ne_zero)
  have hgauss_ne : gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard_ne hχinv_ne_one (ZMod.isPrimitive_stdAddChar p)
  apply (mul_left_cancel₀ hgauss_ne)
  calc
    gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * ZMod.LFunction χ 1
        = ZMod.LFunction (ZMod.dft χinv) 1 := hleft.symm
    _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.expZeta (ZMod.toAddCircle (-a)) 1 := hdft
    _ = ∑ a : ZMod p, χ⁻¹ a * HurwitzZeta.cosZeta (ZMod.toAddCircle a) 1 := hsum_exp
    _ = -evenLValueLogSum p χ := hboundary
    _ = gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) * evenLValueRhs p χ := by
          simp [evenLValueRhs, hgauss_ne, mul_left_comm, mul_comm]
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
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
theorem evenLProduct_one_eq_prod_evenLValueRhs :
    evenLProduct p (1 : ℂ) =
      Finset.prod (evenNontrivialCharacters (p := p)) fun χ => evenLValueRhs p χ := by
  classical
  unfold evenLProduct
  refine Finset.prod_congr rfl fun χ hχ => ?_
  have hχ_mem := Finset.mem_filter.mp hχ
  have hχ_even : χ.Even := hχ_mem.2.1
  have hχ_ne_one : χ ≠ 1 := hχ_mem.2.2
  simpa using even_LFunction_one_eq_evenLValueRhs (p := p)
    (hχ_prim := DirichletCharacter.isPrimitive_of_ne_one (p := p) hχ_ne_one)
    (hχ_even := hχ_even) (hχ_ne_one := hχ_ne_one)
theorem hPlus_formula_of_evenLProduct (hp_odd' : p ≠ 2) :
    ((hPlus K : ℕ) : ℂ) =
      maximalRealSubfieldClassNumberFactor (K := K) * evenLProduct p (1 : ℂ) :=
  hPlus_formula_of_Kplus_residue (K := K)
    (KplusResidue := evenLProduct p (1 : ℂ))
    (complex_maximalRealSubfield_residue_eq_evenLProduct_one (p := p) (K := K) hp_odd')
theorem hPlus_formula_of_evenLValueRhs (hp_odd' : p ≠ 2) :
    ((hPlus K : ℕ) : ℂ) =
      maximalRealSubfieldClassNumberFactor (K := K) *
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ) := by
  calc
    ((hPlus K : ℕ) : ℂ) =
        maximalRealSubfieldClassNumberFactor (K := K) * evenLProduct p (1 : ℂ) :=
          hPlus_formula_of_evenLProduct (p := p) (K := K) hp_odd'
    _ =
        maximalRealSubfieldClassNumberFactor (K := K) *
          Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ) := by
            rw [evenLProduct_one_eq_prod_evenLValueRhs (p := p)]
theorem hPlus_formula_of_evenLValues_cyclotomicFactor (hp_odd' : p ≠ 2) :
    ((hPlus K : ℕ) : ℂ) =
      cyclotomicHPlusFactor (K := K) *
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ) := by
  simpa [cyclotomicHPlusFactor] using
    (hPlus_formula_of_evenLValueRhs (p := p) (K := K) hp_odd')
theorem hPlus_formula_of_evenLValues (hp_odd' : p ≠ 2) :
    ((hPlus K : ℕ) : ℂ) =
      cyclotomicHPlusFactor (K := K) *
        Finset.prod (evenNontrivialCharacters (p := p)) (fun χ => evenLValueRhs p χ) :=
  hPlus_formula_of_evenLValues_cyclotomicFactor (p := p) (K := K) hp_odd'
end LValues
end KummerCriterion
end
end Module31

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part2
section Module32
noncomputable section
open Complex Real
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
theorem normSq_one_sub_exp_I_mul (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) = 2 - 2 * Real.cos θ := by
  rw [Complex.exp_mul_I, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.cos_ofReal_re,
    Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re, Complex.I_im,
    Complex.sin_ofReal_im, Complex.cos_ofReal_im, mul_zero,
    mul_one, sub_self, Complex.sub_im, Complex.one_im,
    Complex.add_im, Complex.mul_im, zero_sub]
  have h_pyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  nlinarith [h_pyth]
theorem normSq_one_sub_exp_I_mul_eq_four_sin_sq (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) =
      4 * Real.sin (θ / 2) ^ 2 := by
  rw [normSq_one_sub_exp_I_mul]
  have h_cos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have : Real.cos (2 * (θ / 2)) = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      rw [Real.cos_two_mul]
      have h_pyth : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq _
      nlinarith [h_pyth]
    rw [show 2 * (θ / 2) = θ from by ring] at this
    exact this
  rw [h_cos]
  ring
theorem norm_one_sub_exp_I_mul (θ : ℝ) :
    ‖(1 - Complex.exp (θ * Complex.I))‖ = 2 * |Real.sin (θ / 2)| := by
  have h_sq : ‖(1 - Complex.exp (θ * Complex.I))‖ ^ 2 =
      (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [Complex.sq_norm, normSq_one_sub_exp_I_mul_eq_four_sin_sq]
    rw [mul_pow, sq_abs]; ring
  have h_nonneg : 0 ≤ ‖(1 - Complex.exp (θ * Complex.I))‖ := norm_nonneg _
  have h_pos : 0 ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith [h_sq, h_nonneg, h_pos]
theorem norm_one_sub_exp_two_pi_I_mul (q : ℝ) :
    ‖(1 - Complex.exp (((2 * Real.pi * q) : ℝ) * Complex.I))‖ =
      2 * |Real.sin (Real.pi * q)| := by
  rw [norm_one_sub_exp_I_mul]
  congr 2
  ring_nf
end Sinnott
end LehmerVandiver
end KummerCriterion
end
noncomputable section
open Real Complex
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
private theorem sum_zmod_eq_sum_Ico_of_zero
    {f : ZMod p → ℂ} (h_zero : f (0 : ZMod p) = 0) :
    ∑ a : ZMod p, f a = ∑ a ∈ Finset.Ico 1 p, f ((a : ℕ) : ZMod p) := by
  have hp_pos : 0 < p := hp.out.pos
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : ZMod p)),
    h_zero, add_zero]
  symm
  refine Finset.sum_bij (fun k _ => ((k : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h_eq
    rw [ZMod.natCast_eq_zero_iff] at h_eq
    have := Nat.le_of_dvd (by omega) h_eq
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    rw [Finset.mem_Ico] at hk₁ hk₂
    have h_val1 : ((k₁ : ZMod p)).val = k₁ := ZMod.val_natCast_of_lt hk₁.2
    have h_val2 : ((k₂ : ZMod p)).val = k₂ := ZMod.val_natCast_of_lt hk₂.2
    have h := congrArg ZMod.val heq
    rw [h_val1, h_val2] at h
    exact h
  · intro x hx
    rw [Finset.mem_erase] at hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt x⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h
    apply hx.1
    have h_val_eq : (x.val : ZMod p) = (0 : ZMod p) := by
      rw [h]; push_cast; rfl
    rw [← h_val_eq, ZMod.natCast_zmod_val]
  · intros; rfl
theorem evenLValueLogSum_eq_neg_DirichletLogSum_inv
    (χ : DirichletCharacter ℂ p) :
    KummerCriterion.evenLValueLogSum p χ = -DirichletLogSum p χ⁻¹ := by
  have hp_pos : 0 < p := hp.out.pos
  unfold KummerCriterion.evenLValueLogSum DirichletLogSum
  rw [neg_neg]
  set f : ZMod p → ℂ := fun a =>
    χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)
  have h_zero : f (0 : ZMod p) = 0 := by
    simp [f, MulChar.map_zero]
  rw [show (∑ a : ZMod p,
      χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)) =
      ∑ a : ZMod p, f a from rfl]
  rw [sum_zmod_eq_sum_Ico_of_zero (p := p) h_zero]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [Finset.mem_Ico] at ha
  have ha_pos : 0 < a := ha.1
  have ha_lt : a < p := ha.2
  change χ⁻¹ ((a : ℕ) : ZMod p) *
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p)‖ : ℝ) : ℂ) =
    χ⁻¹ ((a : ℕ) : ZMod p) *
      ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ)
  congr 2
  have h_std : ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / p) := by
    have h := ZMod.stdAddChar_coe (N := p) (a : ℤ)
    simpa using h
  rw [h_std]
  have h_norm : ‖(1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / p)‖ =
      2 * |Real.sin (Real.pi * a / p)| := by
    have h_eq : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / p) =
        ((2 * Real.pi * ((a : ℕ) / p : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h_eq, norm_one_sub_exp_two_pi_I_mul]
    ring_nf
  rw [h_norm]
private theorem prod_one_sub_stdAddChar_eq_p :
    ∏ a ∈ Finset.Ico 1 p, ((1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p)) =
      (p : ℂ) := by
  have hp_pos : 0 < p := hp.out.pos
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p) with hζ_def
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  have hμ : IsPrimitiveRoot ζ ((p - 1) + 1) := by
    rw [show (p - 1) + 1 = p from Nat.succ_pred_eq_of_pos hp_pos]
    exact hζ
  have h_prod_pow : ∏ k ∈ Finset.range (p - 1), (1 - ζ ^ (k + 1)) =
      ((p - 1 : ℕ) : ℂ) + 1 := hμ.prod_one_sub_pow_eq_order
  have h_p_cast : ((p - 1 : ℕ) : ℂ) + 1 = (p : ℂ) := by
    have h_pe : (p - 1 : ℕ) + 1 = p := Nat.succ_pred_eq_of_pos hp_pos
    exact_mod_cast h_pe
  have h_Ico : Finset.Ico 1 p = (Finset.range (p - 1)).image (· + 1) := by
    ext a
    rw [Finset.mem_image, Finset.mem_Ico]
    refine ⟨fun ⟨ha1, ha2⟩ => ⟨a - 1, ?_, ?_⟩, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
    · rintro ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      omega
  have h_inj : ∀ k₁ ∈ Finset.range (p - 1),
      ∀ k₂ ∈ Finset.range (p - 1), k₁ + 1 = k₂ + 1 → k₁ = k₂ :=
    fun _ _ _ _ h => by omega
  have h_eq_ζ : ∀ k ∈ Finset.range (p - 1),
      ZMod.stdAddChar (N := p) ((k + 1 : ℕ) : ZMod p) = ζ ^ (k + 1) := by
    intro k _
    rw [hζ_def, ← Complex.exp_nat_mul]
    have h := ZMod.stdAddChar_coe (N := p) ((k + 1 : ℕ) : ℤ)
    rw [show ((k + 1 : ℕ) : ZMod p) = (((k + 1 : ℕ) : ℤ) : ZMod p) from by push_cast; rfl, h]
    congr 1
    push_cast
    ring
  rw [h_Ico, Finset.prod_image h_inj]
  calc ∏ x ∈ Finset.range (p - 1),
        ((1 : ℂ) - ZMod.stdAddChar (N := p) ((x + 1 : ℕ) : ZMod p))
      = ∏ x ∈ Finset.range (p - 1), ((1 : ℂ) - ζ ^ (x + 1)) :=
        Finset.prod_congr rfl (fun k hk => by rw [h_eq_ζ k hk])
    _ = ((p - 1 : ℕ) : ℂ) + 1 := h_prod_pow
    _ = (p : ℂ) := h_p_cast
theorem DirichletLogSum_principal_eq_neg_log :
    DirichletLogSum p (1 : DirichletCharacter ℂ p) = -((Real.log p : ℝ) : ℂ) := by
  have hp_pos : 0 < p := hp.out.pos
  have h_eval : ∑ a ∈ Finset.Ico 1 p,
        ((1 : DirichletCharacter ℂ p) ((a : ℕ) : ZMod p)) *
        ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
      ∑ a ∈ Finset.Ico 1 p,
        ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [Finset.mem_Ico] at ha
    have h_unit : IsUnit ((a : ℕ) : ZMod p) := by
      rw [isUnit_iff_ne_zero]
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd ha.1 h) (by omega)
    rw [MulChar.one_apply h_unit, one_mul]
  rw [DirichletLogSum, h_eval]
  have h_pos : ∀ a ∈ Finset.Ico 1 p,
      (0 : ℝ) < 2 * |Real.sin (Real.pi * a / p)| := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    have hp_real : (0 : ℝ) < p := by positivity
    have h_arg_pos : 0 < Real.pi * a / p := by
      have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha.1
      positivity
    have h_arg_lt : Real.pi * a / p < Real.pi := by
      have h_a_lt : (a : ℝ) < p := by exact_mod_cast ha.2
      have h_div_lt : (a : ℝ) / p < 1 := (div_lt_one hp_real).mpr h_a_lt
      have hπ : Real.pi * ((a : ℝ) / p) < Real.pi * 1 :=
        mul_lt_mul_of_pos_left h_div_lt Real.pi_pos
      rw [mul_one] at hπ
      rw [mul_div_assoc]
      exact hπ
    have h_sin_pos : 0 < Real.sin (Real.pi * a / p) :=
      Real.sin_pos_of_pos_of_lt_pi h_arg_pos h_arg_lt
    rw [abs_of_pos h_sin_pos]
    positivity
  have h_real_sum : ∑ a ∈ Finset.Ico 1 p,
        ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
      ((∑ a ∈ Finset.Ico 1 p,
          Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_real_sum]
  have h_sum_log : (∑ a ∈ Finset.Ico 1 p,
        Real.log (2 * |Real.sin (Real.pi * a / p)|)) =
      Real.log (∏ a ∈ Finset.Ico 1 p,
        (2 * |Real.sin (Real.pi * a / p)| : ℝ)) :=
    (Real.log_prod (s := Finset.Ico 1 p)
      (f := fun a => 2 * |Real.sin (Real.pi * a / p)|)
      (fun a ha => (h_pos a ha).ne')).symm
  rw [h_sum_log]
  have h_prod_eq : (∏ a ∈ Finset.Ico 1 p,
        (2 * |Real.sin (Real.pi * a / p)| : ℝ)) = (p : ℝ) := by
    have h_complex := prod_one_sub_stdAddChar_eq_p (p := p)
    have h_norm := congrArg (‖·‖) h_complex
    simp only [Complex.norm_prod] at h_norm
    rw [Complex.norm_natCast p] at h_norm
    have h_eq_each : ∀ a ∈ Finset.Ico 1 p,
        (2 * |Real.sin (Real.pi * a / p)| : ℝ) =
        ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p)‖ := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      have h_std : ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p) =
          Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / p) := by
        have h := ZMod.stdAddChar_coe (N := p) (a : ℤ)
        simpa using h
      rw [h_std]
      have h_eq : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / p) =
          ((2 * Real.pi * ((a : ℕ) / p : ℝ) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h_eq, norm_one_sub_exp_two_pi_I_mul]
      ring_nf
    rw [Finset.prod_congr rfl h_eq_each]
    exact h_norm
  rw [h_prod_eq]
theorem evenLValueRhs_eq_gaussSum_inv_mul_DirichletLogSum
    (χ : DirichletCharacter ℂ p) :
    KummerCriterion.evenLValueRhs p χ =
      (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ * DirichletLogSum p χ⁻¹ := by
  unfold KummerCriterion.evenLValueRhs
  rw [evenLValueLogSum_eq_neg_DirichletLogSum_inv]
  ring
theorem gaussSum_mul_gaussSum_inv_eq_p
    (χ : DirichletCharacter ℂ p) (hχ_ne : χ ≠ 1) (hχ_even : χ.Even) :
    gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) =
      (p : ℂ) := by
  have h_primitive : (ZMod.stdAddChar (N := p)).IsPrimitive :=
    ZMod.isPrimitive_stdAddChar p
  have h_card := gaussSum_mul_gaussSum_eq_card hχ_ne h_primitive
  have h_χinv_neg_one : χ⁻¹ ((-1 : ZMod p)) = 1 := by
    rw [MulChar.inv_apply_eq_inv']
    rw [DirichletCharacter.Even] at hχ_even
    rw [hχ_even]
    norm_num
  have h_convert :=
    mul_gaussSum_inv_eq_gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))
  rw [h_χinv_neg_one, one_mul] at h_convert
  rw [h_convert] at h_card
  rw [ZMod.card] at h_card
  exact_mod_cast h_card
theorem prod_gaussSum_mul_gaussSum_inv_eq_p_pow (hp_odd' : p ≠ 2) :
    ∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        (gaussSum χ (ZMod.stdAddChar (N := p)) *
          gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))) =
      (p : ℂ) ^ ((p - 3) / 2) := by
  classical
  have h_per_χ : ∀ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
      gaussSum χ (ZMod.stdAddChar (N := p)) *
          gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) =
        (p : ℂ) := by
    intro χ hχ
    rw [KummerCriterion.evenNontrivialCharacters, Finset.mem_filter] at hχ
    obtain ⟨_, hχ_even, hχ_ne⟩ := hχ
    exact gaussSum_mul_gaussSum_inv_eq_p p χ hχ_ne hχ_even
  rw [Finset.prod_congr rfl h_per_χ, Finset.prod_const,
    KummerCriterion.card_evenNontrivialCharacters (p := p) hp_odd']
theorem inv_mem_evenNontrivialCharacters {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ KummerCriterion.evenNontrivialCharacters (p := p)) :
    χ⁻¹ ∈ KummerCriterion.evenNontrivialCharacters (p := p) := by
  classical
  rw [KummerCriterion.evenNontrivialCharacters, Finset.mem_filter] at hχ ⊢
  obtain ⟨_, hχ_even, hχ_ne⟩ := hχ
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · rw [DirichletCharacter.Even] at hχ_even ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_even]
    norm_num
  · intro h_inv_eq_one
    apply hχ_ne
    have h_mul : χ⁻¹ * χ = 1 := MulChar.inv_mul χ
    rw [h_inv_eq_one, one_mul] at h_mul
    exact h_mul
theorem prod_gaussSum_eq_prod_gaussSum_inv :
    ∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        gaussSum χ (ZMod.stdAddChar (N := p)) =
      ∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) := by
  classical
  refine (Finset.prod_bij (fun χ _ => χ⁻¹) ?_ ?_ ?_ ?_).symm
  · intro χ hχ
    exact inv_mem_evenNontrivialCharacters (p := p) hχ
  · intro χ₁ _ χ₂ _ heq
    have := congrArg (fun ψ => ψ⁻¹) heq
    simpa using this
  · intro χ hχ
    refine ⟨χ⁻¹, inv_mem_evenNontrivialCharacters (p := p) hχ, ?_⟩
    exact inv_inv χ
  · intro χ _; rfl
theorem prod_gaussSum_sq_eq_p_pow (hp_odd' : p ≠ 2) :
    (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        gaussSum χ (ZMod.stdAddChar (N := p))) ^ 2 =
      (p : ℂ) ^ ((p - 3) / 2) := by
  classical
  rw [sq]
  nth_rewrite 2 [prod_gaussSum_eq_prod_gaussSum_inv (p := p)]
  rw [← Finset.prod_mul_distrib]
  exact prod_gaussSum_mul_gaussSum_inv_eq_p_pow (p := p) hp_odd'
theorem hPlus_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) :
    ((KummerCriterion.hPlus K : ℕ) : ℂ) =
      KummerCriterion.cyclotomicHPlusFactor (K := K) *
        (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
            gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
        ∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹ := by
  rw [KummerCriterion.hPlus_formula_of_evenLValues (p := p) (K := K) hp_odd']
  have h_rhs : ∀ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
      KummerCriterion.evenLValueRhs p χ =
        (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ * DirichletLogSum p χ⁻¹ :=
    fun χ _ => evenLValueRhs_eq_gaussSum_inv_mul_DirichletLogSum p χ
  rw [Finset.prod_congr rfl h_rhs]
  rw [Finset.prod_mul_distrib]
  rw [show (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹) =
      (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ from
      Finset.prod_inv_distrib
        (fun χ : DirichletCharacter ℂ p => gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))]
  rw [← prod_gaussSum_eq_prod_gaussSum_inv (p := p)]
  ring
theorem cyclotomicHPlusFactor_mul_regulator_eq
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) :
    KummerCriterion.cyclotomicHPlusFactor (K := K) *
        ((NumberField.Units.regulator (oMR K) : ℝ) : ℂ) =
      ((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) := by
  have h_reg_pos : (0 : ℝ) < NumberField.Units.regulator
      (oMR K) :=
    NumberField.Units.regulator_pos _
  have h_reg_ne : (NumberField.Units.regulator
      (oMR K) : ℝ) ≠ 0 := h_reg_pos.ne'
  change KummerCriterion.maximalRealSubfieldClassNumberFactor (K := K) * _ = _
  rw [KummerCriterion.maximalRealSubfieldClassNumberFactor_eq_explicit
    (p := p) (K := K) hp_odd']
  push_cast
  have h_reg_C : ((NumberField.Units.regulator
      (oMR K) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h_reg_ne
  field_simp
theorem hPlus_mul_regulator_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) :
    ((KummerCriterion.hPlus K : ℕ) : ℂ) *
        ((NumberField.Units.regulator (oMR K) : ℝ) : ℂ) =
      ((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) *
        (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
            gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
        ∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹ := by
  rw [hPlus_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum (p := p) K hp_odd']
  rw [show
    KummerCriterion.cyclotomicHPlusFactor (K := K) *
      (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
          gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
      (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        DirichletLogSum p χ⁻¹) *
      ((NumberField.Units.regulator (oMR K) : ℝ) : ℂ) =
    (KummerCriterion.cyclotomicHPlusFactor (K := K) *
      ((NumberField.Units.regulator (oMR K) : ℝ) : ℂ)) *
      (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
          gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
      ∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        DirichletLogSum p χ⁻¹ from by ring]
  rw [cyclotomicHPlusFactor_mul_regulator_eq (p := p) K hp_odd']
theorem prefactor_sq_eq_inv_two_pow (hp_odd' : p ≠ 2) (hp_ge : 3 ≤ p) :
    (((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) *
        (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
            gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹) ^ 2 =
      ((2 : ℂ) ^ (p - 3))⁻¹ := by
  have hp_pos : 0 < p := hp.out.pos
  have hp_real : (0 : ℝ) ≤ p := by positivity
  have hp_pow_real : (0 : ℝ) ≤ (p : ℝ) ^ ((p - 1) / 2) := by positivity
  have hp_pow_nat : (0 : ℝ) ≤ (p : ℝ) ^ ((p - 3) / 2) := by positivity
  rw [mul_pow]
  have h_first_sq : (((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) /
        2 ^ ((p - 1) / 2) : ℝ) : ℂ)) ^ 2 =
      ((4 * (p : ℝ) ^ ((p - 3) / 2) / 2 ^ (p - 1) : ℝ) : ℂ) := by
    push_cast
    rw [div_pow, mul_pow]
    rw [show ((2 : ℂ) : ℂ) ^ 2 = 4 from by norm_num]
    have h_sq_sqrt : (Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) : ℂ) ^ 2 =
        ((p : ℝ) ^ ((p - 3) / 2) : ℂ) := by
      push_cast
      exact_mod_cast Real.sq_sqrt hp_pow_nat
    rw [h_sq_sqrt]
    rw [show ((2 : ℂ) ^ ((p - 1) / 2)) ^ 2 = (2 : ℂ) ^ (p - 1) from by
      rw [← pow_mul]
      congr 1
      have h_even : Even (p - 1) := hp.out.even_sub_one hp_odd'
      obtain ⟨k, hk⟩ := h_even
      omega]
    push_cast
    ring
  rw [h_first_sq]
  rw [show (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ ^ 2 =
      ((∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
          gaussSum χ (ZMod.stdAddChar (N := p))) ^ 2)⁻¹ from
      inv_pow _ _]
  rw [prod_gaussSum_sq_eq_p_pow (p := p) hp_odd']
  have h_p_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h_p_pow_ne : (p : ℂ) ^ ((p - 3) / 2) ≠ 0 := pow_ne_zero _ h_p_ne
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  rw [show ((4 * (p : ℝ) ^ ((p - 3) / 2) / 2 ^ (p - 1) : ℝ) : ℂ) =
      4 * (p : ℂ) ^ ((p - 3) / 2) / (2 : ℂ) ^ (p - 1) from by push_cast; ring]
  rw [show (2 : ℂ) ^ (p - 1) = (2 : ℂ) ^ ((p - 3) + 2) from by
    congr 1; omega]
  rw [pow_add, show (2 : ℂ) ^ 2 = 4 from by norm_num]
  field_simp
theorem hPlus_mul_regulator_sq_eq
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) (hp_ge : 3 ≤ p) :
    (((KummerCriterion.hPlus K : ℕ) : ℂ) *
        ((NumberField.Units.regulator (oMR K) : ℝ) : ℂ)) ^ 2 =
      (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹) ^ 2 / (2 : ℂ) ^ (p - 3) := by
  rw [hPlus_mul_regulator_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum
    (p := p) K hp_odd']
  rw [show
    (((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) *
        (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
            gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
        ∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹) ^ 2 =
      (((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) *
          (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
              gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹) ^ 2 *
        (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹) ^ 2 from by ring]
  rw [prefactor_sq_eq_inv_two_pow (p := p) hp_odd' hp_ge]
  rw [inv_mul_eq_div]
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module32

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part3
section Module33
noncomputable section
open Real Complex
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
def FrobeniusDetIdentity
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  ((NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
    (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
        DirichletLogSum p χ⁻¹) ^ 2
theorem KummerDirichletDeterminant_of_FrobeniusDetIdentity
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (h_frob : FrobeniusDetIdentity (p := p) K hp_odd hp_three) :
    LehmerVandiver.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three := by
  unfold LehmerVandiver.Sinnott.KummerDirichletDeterminant
  unfold FrobeniusDetIdentity at h_frob
  have h_analytic := hPlus_mul_regulator_sq_eq (p := p) K hp_odd hp_three
  have h_sq_eq_C : ((NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
      (((2 : ℝ) ^ ((p - 3) / 2) : ℝ) : ℂ) ^ 2 *
      (((KummerCriterion.hPlus K : ℕ) : ℂ) *
        ((NumberField.Units.regulator (oMR K) : ℝ) : ℂ)) ^ 2 := by
    rw [h_frob]
    rw [show (∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
            DirichletLogSum p χ⁻¹) ^ 2 =
        ((2 : ℂ) ^ (p - 3)) *
          ((∏ χ ∈ KummerCriterion.evenNontrivialCharacters (p := p),
            DirichletLogSum p χ⁻¹) ^ 2 / (2 : ℂ) ^ (p - 3)) from by
      field_simp]
    rw [← h_analytic]
    have h_pow_eq : (((2 : ℝ) ^ ((p - 3) / 2) : ℝ) : ℂ) ^ 2 = (2 : ℂ) ^ (p - 3) := by
      push_cast
      rw [← pow_mul]
      congr 1
      have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
      rcases h_p_odd with ⟨k, hk⟩
      omega
    rw [h_pow_eq]
  have h_sq_eq_R : (NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ^ 2 =
      ((2 : ℝ) ^ ((p - 3) / 2) * ((KummerCriterion.hPlus K : ℕ) : ℝ) *
        NumberField.Units.regulator (oMR K)) ^ 2 := by
    have h_cast : ((NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) ^ 2 : ℝ) : ℂ) =
        (((2 : ℝ) ^ ((p - 3) / 2) * ((KummerCriterion.hPlus K : ℕ) : ℝ) *
          NumberField.Units.regulator (oMR K)) ^ 2 : ℂ) := by
      push_cast
      push_cast at h_sq_eq_C
      linear_combination h_sq_eq_C
    exact_mod_cast h_cast
  have h_reg_nonneg : (0 : ℝ) ≤ NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) := by
    rw [KummerCriterion.LehmerVandiver.Sinnott.regOfFamily_cyclotomicUnitFamilyKplus_eq_det
      (p := p) (K := K) hp_odd hp_three]
    exact abs_nonneg _
  have h_rhs_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ ((p - 3) / 2) *
      ((KummerCriterion.hPlus K : ℕ) : ℝ) *
      NumberField.Units.regulator (oMR K) := by
    refine mul_nonneg (mul_nonneg ?_ ?_) (NumberField.Units.regulator_pos _).le
    · positivity
    · exact Nat.cast_nonneg _
  exact (sq_eq_sq₀ h_reg_nonneg h_rhs_nonneg).mp h_sq_eq_R
theorem log_norm_one_sub_stdAddChar_unit (a : (ZMod p)ˣ) :
    Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ =
      Real.log (2 * |Real.sin (Real.pi * (ZMod.val (a : ZMod p) : ℕ) / p)|) := by
  set k : ℕ := ZMod.val ((a : ZMod p))
  have h_val_cast : ((a : ZMod p)) = ((k : ℤ) : ZMod p) := by
    change (a : ZMod p) = ((ZMod.val (a : ZMod p) : ℤ) : ZMod p)
    push_cast
    exact (ZMod.natCast_zmod_val (a : ZMod p)).symm
  rw [h_val_cast, ZMod.stdAddChar_coe (N := p) (k : ℤ)]
  push_cast
  have h_eq : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) / p) =
      ((2 * Real.pi * ((k : ℕ) / p : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h_eq, norm_one_sub_exp_two_pi_I_mul]
  ring_nf
theorem sum_units_logNorm_eq_log_p :
    ∑ a : KummerCriterion.CyclotomicUnitDelta p,
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
      ((Real.log p : ℝ) : ℂ) := by
  have h_summand : ∀ a : KummerCriterion.CyclotomicUnitDelta p,
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
        ((Real.log
          (2 * |Real.sin (Real.pi * (ZMod.val (a : ZMod p) : ℕ) / p)|) : ℝ) :
            ℂ) := by
    intro a
    rw [log_norm_one_sub_stdAddChar_unit p a]
  simp_rw [h_summand]
  rw [sum_units_val_eq_sum_Ico (p := p)
      (fun n => ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ))]
  have h_dls := DirichletLogSum_principal_eq_neg_log p
  unfold DirichletLogSum at h_dls
  have h_eval : ∀ n ∈ Finset.Ico 1 p,
      (1 : DirichletCharacter ℂ p) ((n : ℕ) : ZMod p) *
        ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ) =
      ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have h_unit : IsUnit ((n : ℕ) : ZMod p) := by
      rw [isUnit_iff_ne_zero]
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      have hp_prime : Nat.Prime p := hp.out
      exact absurd (Nat.le_of_dvd hn.1 h) (by omega)
    rw [MulChar.one_apply h_unit, one_mul]
  have h_sum_eq : ∑ n ∈ Finset.Ico 1 p,
        ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ) =
      ∑ n ∈ Finset.Ico 1 p,
        (1 : DirichletCharacter ℂ p) ((n : ℕ) : ZMod p) *
          ((Real.log (2 * |Real.sin (Real.pi * n / p)|) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun n hn => (h_eval n hn).symm)
  rw [h_sum_eq]
  linear_combination -h_dls
noncomputable def dirichletOfQuotientChar
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :
    DirichletCharacter ℂ p :=
  MulChar.ofUnitHom
    ((KummerCriterion.evenDeltaCharacterPullback (p := p) ξ).toUnitHom.comp
      toUnits.toMonoidHom)
theorem dirichletOfQuotientChar_apply_unit
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)
    (a : KummerCriterion.CyclotomicUnitDelta p) :
    dirichletOfQuotientChar p ξ ((a : ZMod p)) =
      ξ (KummerCriterion.cyclotomicEvenDeltaQuotient p a) := by
  unfold dirichletOfQuotientChar
  rw [MulChar.ofUnitHom_coe]
  rw [MonoidHom.comp_apply]
  rw [MulChar.coe_toUnitHom]
  change (KummerCriterion.evenDeltaCharacterPullback (p := p) ξ)
      ((toUnits a).val) = _
  change (KummerCriterion.evenDeltaCharacterPullback (p := p) ξ) a = _
  rfl
theorem dirichletOfQuotientChar_even
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :
    (dirichletOfQuotientChar p ξ).Even := by
  change (dirichletOfQuotientChar p ξ) (-1 : ZMod p) = 1
  have h_cast : (-1 : ZMod p) = ((-1 : (ZMod p)ˣ) : ZMod p) := by
    rw [Units.val_neg, Units.val_one]
  rw [h_cast]
  rw [dirichletOfQuotientChar_apply_unit p ξ (-1 : (ZMod p)ˣ)]
  rw [KummerCriterion.cyclotomicEvenDeltaQuotient_neg_one]
  exact MulChar.map_one ξ
theorem dirichletOfQuotientChar_injective :
    Function.Injective (dirichletOfQuotientChar p) := by
  intro ξ₁ ξ₂ h
  apply MulChar.ext
  intro ā
  have h_repr : ∃ a : KummerCriterion.CyclotomicUnitDelta p,
      KummerCriterion.cyclotomicEvenDeltaQuotient p a =
        ((ā : KummerCriterion.CyclotomicEvenDelta p)) := by
    refine ⟨Quotient.out ((ā : KummerCriterion.CyclotomicEvenDelta p)), ?_⟩
    rw [KummerCriterion.cyclotomicEvenDeltaQuotient_apply]
    exact Quotient.out_eq _
  obtain ⟨a, ha⟩ := h_repr
  rw [← ha]
  have h_at_a : dirichletOfQuotientChar p ξ₁ ((a : ZMod p)) =
      dirichletOfQuotientChar p ξ₂ ((a : ZMod p)) := by
    rw [h]
  rw [dirichletOfQuotientChar_apply_unit p ξ₁ a,
      dirichletOfQuotientChar_apply_unit p ξ₂ a] at h_at_a
  exact h_at_a
theorem dirichletOfQuotientChar_one :
    dirichletOfQuotientChar p
        (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (1 : DirichletCharacter ℂ p) := by
  apply MulChar.ext
  intro u
  rw [dirichletOfQuotientChar_apply_unit]
  rw [MulChar.one_apply u.isUnit]
  rw [MulChar.one_apply (Group.isUnit _)]
theorem prod_mulChar_DLS_eq_trivial_mul_nontrivial :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    haveI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    ∏ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ,
        DirichletLogSum p (dirichletOfQuotientChar p ξ) =
      DirichletLogSum p (1 : DirichletCharacter ℂ p) *
        ∏ ξ ∈ (Finset.univ : Finset
            (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
          DirichletLogSum p (dirichletOfQuotientChar p ξ) := by
  classical
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  let : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ
    (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ))]
  rw [dirichletOfQuotientChar_one]
  ring
theorem quotientEigenvalue_trivial_eq_half_log_p (hp_two : 2 < p) :
    quotientEigenvalue p (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      ((Real.log p : ℝ) : ℂ) / 2 := by
  have h := two_mul_quotientEigenvalue_trivial_eq_sum_logNorm p hp_two
  rw [sum_units_logNorm_eq_log_p p] at h
  linear_combination h / 2
theorem frobenius_eigenvalue_eq_neg_DirichletLogSum
    (χ : DirichletCharacter ℂ p) :
    ∑ a : (ZMod p)ˣ, χ ((a : ZMod p)) *
        ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
      -DirichletLogSum p χ := by
  classical
  have h_units_sum_eq : ∑ a : (ZMod p)ˣ,
        χ ((a : ZMod p)) *
          ((Real.log ‖(1 : ℂ) -
            ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) =
      ∑ a : ZMod p,
        χ a * ((Real.log ‖(1 : ℂ) -
          ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p))]
    rw [χ.map_zero, zero_mul, add_zero]
    refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => (a : ZMod p)) ?_ ?_ ?_ ?_
    · intro a _
      rw [Finset.mem_erase]
      exact ⟨a.isUnit.ne_zero, Finset.mem_univ _⟩
    · intro a₁ _ a₂ _ h
      exact Units.ext h
    · intro b hb
      rw [Finset.mem_erase] at hb
      obtain ⟨hb_ne, _⟩ := hb
      have h_b_val_ne : b.val ≠ 0 := fun h_val =>
        hb_ne ((ZMod.val_eq_zero b).mp h_val)
      have h_b_val_lt : b.val < p := ZMod.val_lt b
      have hp_prime : Nat.Prime p := hp.out
      have h_coprime : Nat.Coprime b.val p := by
        rw [Nat.coprime_comm]
        rw [hp_prime.coprime_iff_not_dvd]
        intro h_dvd
        exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero h_b_val_ne) h_dvd) (by omega)
      refine ⟨ZMod.unitOfCoprime b.val h_coprime, Finset.mem_univ _, ?_⟩
      change ((ZMod.unitOfCoprime b.val h_coprime : (ZMod p)ˣ) : ZMod p) = b
      rw [ZMod.coe_unitOfCoprime]
      exact ZMod.natCast_zmod_val b
    · intro a _; rfl
  rw [h_units_sum_eq]
  have h_sum_eq_evenL : ∑ a : ZMod p,
        χ a * ((Real.log ‖(1 : ℂ) -
          ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ) =
      KummerCriterion.evenLValueLogSum p χ⁻¹ := by
    unfold KummerCriterion.evenLValueLogSum
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [inv_inv]
  rw [h_sum_eq_evenL]
  rw [evenLValueLogSum_eq_neg_DirichletLogSum_inv]
  rw [inv_inv]
theorem two_mul_quotientEigenvalue_eq_neg_DLS
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) (hp_two : 2 < p) :
    2 * quotientEigenvalue p ξ =
      -DirichletLogSum p (dirichletOfQuotientChar p ξ) := by
  rw [two_mul_quotientEigenvalue_eq_sum_full p ξ hp_two]
  rw [← frobenius_eigenvalue_eq_neg_DirichletLogSum p (dirichletOfQuotientChar p ξ)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  rw [dirichletOfQuotientChar_apply_unit]
  rfl
theorem quotientEigenvalue_sq_eq_DLS_sq_div_four
    (ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) (hp_two : 2 < p) :
    (quotientEigenvalue p ξ) ^ 2 =
      (DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 / 4 := by
  have h := two_mul_quotientEigenvalue_eq_neg_DLS p ξ hp_two
  have h_sq : (2 * quotientEigenvalue p ξ) ^ 2 =
      (-DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 := by
    rw [h]
  rw [neg_pow, neg_one_sq, one_mul] at h_sq
  linear_combination h_sq / 4
theorem det_convolutionMatrixLogNormEven_sq_eq_prod_DLS_sq_div_four_pow
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    (convolutionMatrixLogNormEven p).det ^ 2 =
      (∏ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ,
        (DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2) /
      4 ^ (Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)) := by
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  let : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  rw [det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq p hp_two]
  rw [← Finset.prod_pow]
  rw [prod_quot_eq_prod_mulChar p (fun ξ => (quotientEigenvalue p ξ) ^ 2)]
  have h_eigen_sq : ∀ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ,
      (quotientEigenvalue p ξ) ^ 2 =
        (DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 / 4 := fun ξ =>
    quotientEigenvalue_sq_eq_DLS_sq_div_four p ξ hp_two
  rw [Finset.prod_congr rfl (fun ξ _ => h_eigen_sq ξ)]
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_const, Finset.card_univ]
theorem det_convolutionMatrixLogNormEven_sq_eq_log_p_sq_mul_nontrivial_DLS_sq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    haveI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    (convolutionMatrixLogNormEven p).det ^ 2 =
      (((Real.log p : ℝ) : ℂ)) ^ 2 *
        (∏ ξ ∈ (Finset.univ : Finset
            (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
          DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 /
      4 ^ (Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)) := by
  classical
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  let : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  have h_sq_eq : (∏ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ,
      (DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2) =
    (∏ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ,
      DirichletLogSum p (dirichletOfQuotientChar p ξ)) ^ 2 := by
    rw [Finset.prod_pow]
  rw [det_convolutionMatrixLogNormEven_sq_eq_prod_DLS_sq_div_four_pow p hp_two]
  rw [h_sq_eq]
  rw [prod_mulChar_DLS_eq_trivial_mul_nontrivial p]
  rw [DirichletLogSum_principal_eq_neg_log p]
  rw [mul_pow]
  congr 1
  ring
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module33

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part4
section Module34
noncomputable section
open Real Complex
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
theorem prod_evenNontriv_eq_prod_evenNontriv_inv
    (f : DirichletCharacter ℂ p → ℂ) :
    ∏ χ ∈ KummerCriterion.evenNontrivialCharacters p, f χ =
      ∏ χ ∈ KummerCriterion.evenNontrivialCharacters p, f χ⁻¹ := by
  classical
  refine (Finset.prod_bij (fun χ _ => χ⁻¹) ?_ ?_ ?_ ?_).symm
  · intro χ hχ
    exact inv_mem_evenNontrivialCharacters (p := p) hχ
  · intro χ₁ _ χ₂ _ heq
    have := congrArg (fun ψ => ψ⁻¹) heq
    simpa using this
  · intro χ hχ
    refine ⟨χ⁻¹, inv_mem_evenNontrivialCharacters (p := p) hχ, ?_⟩
    exact inv_inv χ
  · intro χ _; rfl
def MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  (2 : ℂ) ^ (p - 3) * ((convolutionMatrixLogNormEven p).det) ^ 2 =
    (quotientEigenvalue p (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)) ^ 2 *
      ((NumberField.Units.regOfFamily
          (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2
def QuotientCharBijectionToEvenNontriv : Prop :=
  haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  (∏ ξ ∈ (Finset.univ : Finset
      (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
    DirichletLogSum p (dirichletOfQuotientChar p ξ)) =
  ∏ χ ∈ KummerCriterion.evenNontrivialCharacters p, DirichletLogSum p χ
theorem quotientCharBijectionToEvenNontriv_proof (hp_two : 2 < p) :
    QuotientCharBijectionToEvenNontriv (p := p) := by
  classical
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  let : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  change (∏ ξ ∈ (Finset.univ : Finset
        (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
      DirichletLogSum p (dirichletOfQuotientChar p ξ)) =
    ∏ χ ∈ KummerCriterion.evenNontrivialCharacters p, DirichletLogSum p χ
  have h_card_mc : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two
  have h_p_odd : Odd p := hp.out.odd_of_ne_two (by omega)
  refine Finset.prod_bij (fun ξ _ => dirichletOfQuotientChar p ξ) ?_ ?_ ?_ ?_
  · intro ξ hξ
    rw [Finset.mem_erase] at hξ
    obtain ⟨hξ_ne, _⟩ := hξ
    rw [KummerCriterion.evenNontrivialCharacters, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact dirichletOfQuotientChar_even p ξ
    · intro h_one
      apply hξ_ne
      have h_eq : dirichletOfQuotientChar p ξ = dirichletOfQuotientChar p 1 := by
        rw [dirichletOfQuotientChar_one]
        exact h_one
      exact dirichletOfQuotientChar_injective p h_eq
  · intro ξ₁ _ ξ₂ _ h
    exact dirichletOfQuotientChar_injective p h
  · intro χ hχ
    have h_card_eq : (KummerCriterion.evenNontrivialCharacters p).card =
        ((Finset.univ : Finset
            (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1).card := by
      rw [KummerCriterion.card_evenNontrivialCharacters (p := p) (by omega)]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
      rw [Finset.card_univ, h_card_mc]
      rcases h_p_odd with ⟨k, hk⟩
      omega
    have h_in : ∀ ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ,
        ξ ∈ (Finset.univ : Finset
              (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1 →
        dirichletOfQuotientChar p ξ ∈ KummerCriterion.evenNontrivialCharacters p := by
      intro ξ hξ
      rw [Finset.mem_erase] at hξ
      obtain ⟨hξ_ne, _⟩ := hξ
      rw [KummerCriterion.evenNontrivialCharacters, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact dirichletOfQuotientChar_even p ξ
      · intro h_one
        apply hξ_ne
        have h_eq : dirichletOfQuotientChar p ξ = dirichletOfQuotientChar p 1 := by
          rw [dirichletOfQuotientChar_one]
          exact h_one
        exact dirichletOfQuotientChar_injective p h_eq
    have h_surj := Finset.surj_on_of_inj_on_of_card_le
      (fun ξ (_ : ξ ∈ _) => dirichletOfQuotientChar p ξ)
      (fun ξ hξ => h_in ξ hξ)
      (fun ξ₁ ξ₂ _ _ h => dirichletOfQuotientChar_injective p h)
      h_card_eq.le χ hχ
    obtain ⟨a, ha_mem, ha_eq⟩ := h_surj
    exact ⟨a, ha_mem, ha_eq.symm⟩
  · intro ξ _
    rfl
theorem FrobeniusDetIdentity_of_named_hypotheses
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three)
    (h_bij : QuotientCharBijectionToEvenNontriv (p := p)) :
    FrobeniusDetIdentity (p := p) K hp_odd hp_three := by
  classical
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  let : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  unfold FrobeniusDetIdentity
  have h_det_sq := det_convolutionMatrixLogNormEven_sq_eq_log_p_sq_mul_nontrivial_DLS_sq
      p hp_two
  unfold MatrixRestrictionToSinnott at h_matrix
  unfold QuotientCharBijectionToEvenNontriv at h_bij
  have h_qe := quotientEigenvalue_trivial_eq_half_log_p p hp_two
  rw [h_qe] at h_matrix
  have h_card : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two
  rw [← prod_evenNontriv_eq_prod_evenNontriv_inv (p := p) (DirichletLogSum p)]
  have h_log_ne : ((Real.log p : ℝ) : ℂ) ≠ 0 := by
    have h_pos : (1 : ℝ) < (p : ℝ) := by
      have : (1 : ℝ) < (2 : ℝ) := by norm_num
      exact lt_of_lt_of_le this (by exact_mod_cast hp_two.le)
    exact_mod_cast (Real.log_pos h_pos).ne'
  rw [h_bij] at h_det_sq
  rw [h_det_sq] at h_matrix
  have h_two_pow_card : (4 : ℂ) ^ Fintype.card
      (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (2 : ℂ) ^ (p - 1) := by
    rw [h_card]
    rw [show (4 : ℂ) = 2 ^ 2 from by norm_num, ← pow_mul]
    congr 1
    have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
    rcases h_p_odd with ⟨k, hk⟩
    omega
  rw [h_two_pow_card] at h_matrix
  have h_log_sq_ne : (((Real.log p : ℝ) : ℂ)) ^ 2 ≠ 0 := pow_ne_zero _ h_log_ne
  have h_two_ne : ((2 : ℂ) ^ (p - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_two_ne' : ((2 : ℂ) ^ (p - 3)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h_p_ge : (2 : ℂ) ^ (p - 1) = 4 * (2 : ℂ) ^ (p - 3) := by
    rw [show p - 1 = (p - 3) + 2 from by omega, pow_add]
    ring
  rw [h_p_ge] at h_matrix
  field_simp at h_matrix
  linear_combination -h_matrix / 4
theorem FrobeniusDetIdentity_of_MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three) :
    FrobeniusDetIdentity (p := p) K hp_odd hp_three :=
  FrobeniusDetIdentity_of_named_hypotheses (p := p) K hp_odd hp_three hp_two
    h_matrix
    (quotientCharBijectionToEvenNontriv_proof (p := p) hp_two)
theorem KummerDirichletDeterminant_of_MatrixRestrictionToSinnott
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h_matrix : MatrixRestrictionToSinnott (p := p) K hp_odd hp_three) :
    KummerCriterion.LehmerVandiver.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three :=
  KummerDirichletDeterminant_of_FrobeniusDetIdentity (p := p) K hp_odd hp_three
    (FrobeniusDetIdentity_of_MatrixRestrictionToSinnott (p := p) K hp_odd
      hp_three hp_two h_matrix)
theorem fintype_card_InfinitePlace_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsTotallyComplex K] (_hp_two : 2 < p) :
    Fintype.card (NumberField.InfinitePlace K) = (p - 1) / 2 := by
  classical
  have h_finrank_eq : Module.finrank ℚ K = p - 1 := by
    have : Module.finrank ℚ K = (p : ℕ).totient :=
      IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hp.out.pos)
    rw [this, Nat.totient_prime hp.out]
  have h_totally_complex := NumberField.IsTotallyComplex.finrank K
  rw [h_finrank_eq] at h_totally_complex
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  rw [NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (K := K), zero_add]
  omega
noncomputable def InfinitePlaceEquivCyclotomicEvenDelta
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsTotallyComplex K] (hp_two : 2 < p) :
    NumberField.InfinitePlace K ≃ KummerCriterion.CyclotomicEvenDelta p := by
  classical
  refine Fintype.equivOfCardEq ?_
  rw [fintype_card_InfinitePlace_eq (p := p) K hp_two]
  rw [KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two]
noncomputable def KplusInfinitePlaceEquivCyclotomicEvenDelta
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    NumberField.InfinitePlace (oMR K) ≃
      KummerCriterion.CyclotomicEvenDelta p :=
  (NumberField.IsCMField.equivInfinitePlace K).symm.trans
    (InfinitePlaceEquivCyclotomicEvenDelta (p := p) K hp_two)
theorem sinnottMatrix_entry_decomp
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    Real.log
        (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
          ((LehmerVandiver.realCyclotomicUnit p K
            ((((NumberField.Units.equivFinRank
                (oMR K)).symm i).cast
              ((NumberField.IsCMField.units_rank_eq_units_rank
                  (K := K)).trans
                (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                  (p := p) (K := K)))) + 2) : 𝓞 K) : K)) =
      2 * Real.log
            (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
              (((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' :
                  (𝓞 K)ˣ) : 𝓞 K) : K) ^
                (((((NumberField.Units.equivFinRank
                    (oMR K)).symm i).cast
                  ((NumberField.IsCMField.units_rank_eq_units_rank
                      (K := K)).trans
                    (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                      (p := p) (K := K)))) + 2 : ℕ)) - 1)) -
        2 * Real.log
            (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
              ((((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' :
                  (𝓞 K)ˣ) : 𝓞 K) : K)) - 1)) := by
  set k_idx : ℕ := ((((NumberField.Units.equivFinRank
              (oMR K)).symm i).cast
            ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2 : ℕ) with hk_idx
  have h_idx_coprime : k_idx.Coprime p := by
    have h_p_prime : Nat.Prime p := hp.out
    rw [Nat.coprime_comm, h_p_prime.coprime_iff_not_dvd]
    intro h_dvd
    have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
    rcases h_p_odd with ⟨k, hk⟩
    have h_fin_lt :
        (((NumberField.Units.equivFinRank
            (oMR K)).symm i).cast
              ((NumberField.IsCMField.units_rank_eq_units_rank
                  (K := K)).trans
                (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                  (p := p) (K := K)))).val < (p - 3) / 2 :=
      Fin.isLt _
    have h_lt_p : k_idx < p := by
      change ((((NumberField.Units.equivFinRank
                (oMR K)).symm i).cast _) + 2 : ℕ) < p
      omega
    have h_pos : 0 < k_idx := by
      change 0 < ((((NumberField.Units.equivFinRank
                  (oMR K)).symm i).cast _) + 2 : ℕ)
      omega
    have := Nat.le_of_dvd h_pos h_dvd
    omega
  have h_p_ge_two : 2 ≤ p := by omega
  exact log_realCyclotomicUnit_at_Kplus_place_eq_sub_decomp (p := p) (K := K)
    k_idx h_idx_coprime h_p_ge_two w.val
noncomputable def sinnottMatrixA
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Matrix {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℝ :=
  Matrix.of fun i w =>
    Real.log
      (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
        (((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' :
            (𝓞 K)ˣ) : 𝓞 K) : K) ^
          (((((NumberField.Units.equivFinRank
              (oMR K)).symm i).cast
            ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2 : ℕ)) - 1))
noncomputable def sinnottMatrixB
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Matrix {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}
      {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ℝ :=
  Matrix.of fun (_ : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) w =>
    Real.log
      (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
        ((((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' :
            (𝓞 K)ˣ) : 𝓞 K) : K)) - 1))
theorem sinnottMatrix_eq_two_A_sub_two_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((LehmerVandiver.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (oMR K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))) =
      (2 : ℝ) • sinnottMatrixA p K - (2 : ℝ) • sinnottMatrixB p K := by
  ext i w
  simp only [Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    sinnottMatrixA, sinnottMatrixB]
  exact sinnottMatrix_entry_decomp p K hp_odd hp_three i w
theorem sinnottMatrix_eq_two_smul_A_sub_B
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((LehmerVandiver.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (oMR K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))) =
      (2 : ℝ) • (sinnottMatrixA p K - sinnottMatrixB p K) := by
  rw [sinnottMatrix_eq_two_A_sub_two_B p K hp_odd hp_three]
  rw [smul_sub]
theorem convolutionLogNormDescended_apply_quotient
    (a : KummerCriterion.CyclotomicUnitDelta p) :
    convolutionLogNormDescended p
        (KummerCriterion.cyclotomicEvenDeltaQuotient p a) =
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ZMod p))‖ : ℝ) : ℂ) := by
  unfold convolutionLogNormDescended
  rw [show KummerCriterion.cyclotomicEvenDeltaQuotient p a = QuotientGroup.mk a from rfl]
  rw [KummerCriterion.evenFunctionDescend_apply_mk]
theorem det_convolutionMatrixLogNormEven_sq_eq_qe_one_sq_mul_prod_nontrivial_qe_sq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    haveI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Classical.decEq _
    (convolutionMatrixLogNormEven p).det ^ 2 =
      quotientEigenvalue p (1 : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) ^ 2 *
        (∏ ξ ∈ (Finset.univ : Finset
            (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
          quotientEigenvalue p ξ) ^ 2 := by
  classical
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  let : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  rw [det_convolutionMatrixLogNormEven_sq_eq_prod_quotientEigenvalue_sq p hp_two,
    ← Finset.prod_pow, prod_quot_eq_prod_mulChar p (fun ξ => (quotientEigenvalue p ξ) ^ 2),
    Finset.prod_pow, ← Finset.prod_erase_mul _ _ (Finset.mem_univ 1)]
  ring
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module34

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part5
section Module35
noncomputable section
open Real Complex
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
def RegOfFamilySqEqProdNontrivialQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) : Prop :=
  haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  ((NumberField.Units.regOfFamily
    (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
  (2 : ℂ) ^ (p - 3) *
    (∏ ξ ∈ (Finset.univ : Finset
        (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
      quotientEigenvalue p ξ) ^ 2
def DetASubBSqEqProdNontrivialQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    [Fintype {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] : Prop :=
  haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Fintype.ofFinite _
  haveI : DecidableEq (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
    Classical.decEq _
  (((((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ)) ^ 2 : ℂ) =
    (∏ ξ ∈ (Finset.univ : Finset
        (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)).erase 1,
      quotientEigenvalue p ξ) ^ 2
theorem matrixRestrictionToSinnott_of_regOfFamily_sq_eq_prod_nontrivial_qe_sq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h : RegOfFamilySqEqProdNontrivialQeSq (p := p) K hp_odd hp_three) :
    MatrixRestrictionToSinnott (p := p) K hp_odd hp_three := by
  unfold MatrixRestrictionToSinnott
  unfold RegOfFamilySqEqProdNontrivialQeSq at h
  rw [det_convolutionMatrixLogNormEven_sq_eq_qe_one_sq_mul_prod_nontrivial_qe_sq p hp_two, h]
  ring
theorem KummerDirichletDeterminant_of_regOfFamilySqEqProdNontrivialQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h : RegOfFamilySqEqProdNontrivialQeSq (p := p) K hp_odd hp_three) :
    KummerCriterion.LehmerVandiver.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three :=
  KummerDirichletDeterminant_of_MatrixRestrictionToSinnott (p := p) K hp_odd
    hp_three hp_two
    (matrixRestrictionToSinnott_of_regOfFamily_sq_eq_prod_nontrivial_qe_sq
      (p := p) K hp_odd hp_three hp_two h)
theorem exists_embedding_index
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w : NumberField.InfinitePlace K) :
    ∃ a : (ZMod p)ˣ,
      w.embedding (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
        ZMod.stdAddChar (N := p) ((a : ZMod p)) := by
  classical
  have hp_prime : Nat.Prime p := hp.out
  have h_zeta_OK : IsPrimitiveRoot
      (KummerCriterion.cyclotomicZetaInteger (p := p) K) p :=
    KummerCriterion.cyclotomicZetaInteger_isPrimitiveRoot (p := p) K
  have h_zeta_K : IsPrimitiveRoot
      ((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K) p := by
    have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K
    exact h_zeta_OK.map_of_injective h_inj
  have h_emb_inj : Function.Injective (w.embedding) :=
    (w.embedding).injective
  have h_zeta_C : IsPrimitiveRoot
      (w.embedding (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K))) p :=
    h_zeta_K.map_of_injective h_emb_inj
  obtain ⟨a, ha_lt, ha_cop, ha_eq⟩ :=
    (Complex.isPrimitiveRoot_iff
      (w.embedding (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)))
      p hp_prime.ne_zero).mp h_zeta_C
  refine ⟨ZMod.unitOfCoprime a ha_cop, ?_⟩
  rw [← ha_eq]
  rw [ZMod.coe_unitOfCoprime]
  have h_coe : ((a : ZMod p) : ZMod p) = ((a : ℤ) : ZMod p) := by push_cast; rfl
  rw [show ((a : ℕ) : ZMod p) = ((a : ℤ) : ZMod p) from by push_cast; rfl]
  rw [ZMod.stdAddChar_coe (a : ℤ)]
  push_cast
  ring_nf
noncomputable def embeddingIndex
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w : NumberField.InfinitePlace K) : (ZMod p)ˣ :=
  Classical.choose (exists_embedding_index (p := p) K w)
theorem embeddingIndex_spec
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w : NumberField.InfinitePlace K) :
    w.embedding (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
      ZMod.stdAddChar (N := p) ((embeddingIndex (p := p) K w : ZMod p)) :=
  Classical.choose_spec (exists_embedding_index (p := p) K w)
theorem sinnottMatrixA_apply_eq_log_stdAddChar
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (_hp_odd : p ≠ 2) (_hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    let k_idx : ℕ := ((((NumberField.Units.equivFinRank
              (oMR K)).symm i).cast
            ((NumberField.IsCMField.units_rank_eq_units_rank
                (K := K)).trans
              (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                (p := p) (K := K)))) + 2 : ℕ)
    (sinnottMatrixA p K) i w =
      Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K
            ((NumberField.IsCMField.equivInfinitePlace K).symm w.val) : ZMod p) *
          (k_idx : ZMod p))‖ := by
  intro k_idx
  unfold sinnottMatrixA
  rw [Matrix.of_apply]
  set w_K : NumberField.InfinitePlace K :=
    (NumberField.IsCMField.equivInfinitePlace K).symm w.val with hw_K_def
  have h_zeta_eq : ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : (𝓞 K)ˣ) : 𝓞 K) : K) =
      ((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K) := rfl
  rw [h_zeta_eq]
  rw [← NumberField.InfinitePlace.norm_embedding_eq w_K]
  rw [map_sub, map_pow, map_one]
  rw [embeddingIndex_spec (p := p) K w_K]
  have h_pow : (ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p))) ^ k_idx =
      ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p) * (k_idx : ZMod p)) := by
    have h_smul : ((embeddingIndex (p := p) K w_K : ZMod p)) * (k_idx : ZMod p) =
        k_idx • ((embeddingIndex (p := p) K w_K : ZMod p)) := by
      rw [nsmul_eq_mul, mul_comm]
    rw [h_smul, AddChar.map_nsmul_eq_pow]
  rw [h_pow]
  rw [show ‖ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p) * (k_idx : ZMod p)) - 1‖ =
      ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p) * (k_idx : ZMod p))‖ from by
    rw [← neg_sub, norm_neg]]
theorem sinnottMatrixB_apply_eq_log_stdAddChar
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (sinnottMatrixB p K) i w =
      Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K
            ((NumberField.IsCMField.equivInfinitePlace K).symm w.val) : ZMod p))‖ := by
  unfold sinnottMatrixB
  rw [Matrix.of_apply]
  set w_K : NumberField.InfinitePlace K :=
    (NumberField.IsCMField.equivInfinitePlace K).symm w.val with hw_K_def
  have h_zeta_eq : ((((IsCyclotomicExtension.zeta_spec p ℚ K).unit' : (𝓞 K)ˣ) : 𝓞 K) : K) =
      ((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K) := rfl
  rw [h_zeta_eq]
  rw [← NumberField.InfinitePlace.norm_embedding_eq w_K]
  rw [map_sub, map_one]
  rw [embeddingIndex_spec (p := p) K w_K]
  rw [show ‖ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p)) - 1‖ =
      ‖(1 : ℂ) - ZMod.stdAddChar (N := p)
        ((embeddingIndex (p := p) K w_K : ZMod p))‖ from by
    rw [← neg_sub, norm_neg]]
noncomputable def kplusEmbeddingIndexQuotient
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (v : NumberField.InfinitePlace (oMR K)) :
    KummerCriterion.CyclotomicEvenDelta p :=
  KummerCriterion.cyclotomicEvenDeltaQuotient p
    (embeddingIndex (p := p) K
      ((NumberField.IsCMField.equivInfinitePlace K).symm v))
noncomputable def familyIndexAsUnit
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) : (ZMod p)ˣ := by
  classical
  set j : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (oMR K)).symm i).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (KummerCriterion.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K)))) with hj_def
  refine ZMod.unitOfCoprime (j + 2 : ℕ) ?_
  have h_p_prime : Nat.Prime p := hp.out
  have h_fin_lt : j.val < (p - 3) / 2 := Fin.isLt _
  have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨k, hk⟩
  rw [Nat.coprime_comm, h_p_prime.coprime_iff_not_dvd]
  intro h_dvd
  have h_lt_p : ((j : ℕ) + 2 : ℕ) < p := by
    omega
  have h_pos : 0 < ((j : ℕ) + 2 : ℕ) := by
    omega
  have := Nat.le_of_dvd h_pos h_dvd
  omega
theorem familyIndexAsUnit_val
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    let k_idx : ℕ := ((((NumberField.Units.equivFinRank
            (oMR K)).symm i).cast
          ((NumberField.IsCMField.units_rank_eq_units_rank
              (K := K)).trans
            (KummerCriterion.units_rank_eq_prime_sub_three_div_two
              (p := p) (K := K)))) + 2 : ℕ)
    ((familyIndexAsUnit p K hp_odd hp_three i) : ZMod p) = (k_idx : ZMod p) := by
  intro k_idx
  unfold familyIndexAsUnit
  rw [ZMod.coe_unitOfCoprime]
theorem sinnottMatrixA_apply_eq_convolutionLogNormDescended
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ((sinnottMatrixA p K) i w : ℂ) =
      convolutionLogNormDescended p
        (KummerCriterion.cyclotomicEvenDeltaQuotient p
          (embeddingIndex (p := p) K
              ((NumberField.IsCMField.equivInfinitePlace K).symm w.val) *
            familyIndexAsUnit p K hp_odd hp_three i)) := by
  rw [convolutionLogNormDescended_apply_quotient]
  rw [sinnottMatrixA_apply_eq_log_stdAddChar p K hp_odd hp_three i w]
  push_cast
  congr 2
  rw [familyIndexAsUnit_val p K hp_odd hp_three i]
  push_cast
  ring
theorem sinnottMatrixA_apply_eq_convolutionMatrixLogNormEven
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ((sinnottMatrixA p K) i w : ℂ) =
      convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient (p := p) K w.val)
        (KummerCriterion.cyclotomicEvenDeltaQuotient p
          (familyIndexAsUnit p K hp_odd hp_three i)) := by
  rw [sinnottMatrixA_apply_eq_convolutionLogNormDescended p K hp_odd hp_three i w]
  unfold convolutionMatrixLogNormEven kplusEmbeddingIndexQuotient
  rw [Matrix.of_apply]
  rw [(KummerCriterion.cyclotomicEvenDeltaQuotient p).map_mul]
theorem sinnottMatrixB_apply_eq_convolutionMatrixLogNormEven
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ((sinnottMatrixB p K) i w : ℂ) =
      convolutionMatrixLogNormEven p
        (kplusEmbeddingIndexQuotient (p := p) K w.val) 1 := by
  rw [sinnottMatrixB_apply_eq_log_stdAddChar p K i w]
  unfold convolutionMatrixLogNormEven kplusEmbeddingIndexQuotient
  rw [Matrix.of_apply]
  rw [mul_one]
  rw [convolutionLogNormDescended_apply_quotient]
theorem sinnottMatrix_A_sub_B_apply_eq_sub
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ) =
      convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotient (p := p) K w.val)
          (KummerCriterion.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotient (p := p) K w.val) 1 := by
  rw [Matrix.sub_apply]
  push_cast
  rw [sinnottMatrixA_apply_eq_convolutionMatrixLogNormEven p K hp_odd hp_three i w,
    sinnottMatrixB_apply_eq_convolutionMatrixLogNormEven p K i w]
theorem embeddingIndex_eq_iff_embedding_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w₁ w₂ : NumberField.InfinitePlace K) :
    embeddingIndex (p := p) K w₁ = embeddingIndex (p := p) K w₂ ↔
      w₁.embedding = w₂.embedding := by
  classical
  constructor
  · intro h_eq
    have h_emb :
        w₁.embedding
          (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
        w₂.embedding (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) := by
      rw [embeddingIndex_spec, embeddingIndex_spec, h_eq]
    have h_pb : IsPrimitiveRoot
        (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) p := by
      have h_OK := KummerCriterion.cyclotomicZetaInteger_isPrimitiveRoot (p := p) K
      have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
        FaithfulSMul.algebraMap_injective (𝓞 K) K
      exact h_OK.map_of_injective h_inj
    let φ₁ : K →ₐ[ℚ] ℂ := { w₁.embedding with commutes' := fun r => by simp }
    let φ₂ : K →ₐ[ℚ] ℂ := { w₂.embedding with commutes' := fun r => by simp }
    have h_phi_eq : φ₁ = φ₂ := by
      apply (h_pb.powerBasis ℚ).algHom_ext
      simp only [φ₁, φ₂]
      change w₁.embedding (h_pb.powerBasis ℚ).gen = w₂.embedding (h_pb.powerBasis ℚ).gen
      rw [IsPrimitiveRoot.powerBasis_gen]
      exact h_emb
    ext x
    have := congrArg (fun (f : K →ₐ[ℚ] ℂ) => f x) h_phi_eq
    simp only [φ₁, φ₂] at this
    exact this
  · intro h_eq
    have h_zeta_eq :
        w₁.embedding
          (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
        w₂.embedding (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) := by
      rw [h_eq]
    have h_spec_one := embeddingIndex_spec (p := p) K w₁
    have h_spec_two := embeddingIndex_spec (p := p) K w₂
    rw [h_spec_one, h_spec_two] at h_zeta_eq
    have h_inj := ZMod.injective_stdAddChar (N := p)
    have h_zmod_eq : ((embeddingIndex (p := p) K w₁ : ZMod p)) =
        ((embeddingIndex (p := p) K w₂ : ZMod p)) :=
      h_inj h_zeta_eq
    exact Units.ext h_zmod_eq
theorem embeddingIndex_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] :
    Function.Injective (embeddingIndex (p := p) K) := by
  intro w₁ w₂ h
  have h_emb : w₁.embedding = w₂.embedding :=
    (embeddingIndex_eq_iff_embedding_eq (p := p) K w₁ w₂).mp h
  rw [← NumberField.InfinitePlace.mk_embedding w₁,
      ← NumberField.InfinitePlace.mk_embedding w₂, h_emb]
theorem embeddingIndex_neg_implies_place_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w₁ w₂ : NumberField.InfinitePlace K)
    (h : embeddingIndex (p := p) K w₁ = -(embeddingIndex (p := p) K w₂)) :
    w₁ = w₂ := by
  classical
  have h_zeta_K_eq : w₁.embedding
      (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) =
        (starRingEnd ℂ) (w₂.embedding
          (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K))) := by
    rw [embeddingIndex_spec, embeddingIndex_spec]
    have h_cast : ((embeddingIndex (p := p) K w₁) : ZMod p) =
        -((embeddingIndex (p := p) K w₂) : ZMod p) := by
      rw [show ((embeddingIndex (p := p) K w₁) : ZMod p) =
              ((embeddingIndex (p := p) K w₁ : (ZMod p)ˣ) : ZMod p) from rfl]
      rw [h]
      rw [Units.val_neg]
    rw [h_cast]
    exact AddChar.map_neg_eq_conj _ _
  have h_pb : IsPrimitiveRoot
      (((KummerCriterion.cyclotomicZetaInteger (p := p) K : 𝓞 K) : K)) p := by
    have h_OK := KummerCriterion.cyclotomicZetaInteger_isPrimitiveRoot (p := p) K
    have h_inj : Function.Injective (algebraMap (𝓞 K) K) :=
      FaithfulSMul.algebraMap_injective (𝓞 K) K
    exact h_OK.map_of_injective h_inj
  let φ₁ : K →ₐ[ℚ] ℂ := w₁.embedding.toRatAlgHom
  let φ₂_conj : K →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp w₂.embedding).toRatAlgHom
  have h_phi_eq : φ₁ = φ₂_conj := by
    apply (h_pb.powerBasis ℚ).algHom_ext
    change w₁.embedding (h_pb.powerBasis ℚ).gen =
      (starRingEnd ℂ) (w₂.embedding (h_pb.powerBasis ℚ).gen)
    rw [IsPrimitiveRoot.powerBasis_gen]
    exact h_zeta_K_eq
  have h_emb_eq : w₁.embedding =
      NumberField.ComplexEmbedding.conjugate w₂.embedding := by
    ext x
    have := congrArg (fun (f : K →ₐ[ℚ] ℂ) => f x) h_phi_eq
    simpa [φ₁, φ₂_conj, RingHom.toRatAlgHom_apply] using this
  rw [← NumberField.InfinitePlace.mk_embedding w₁,
      ← NumberField.InfinitePlace.mk_embedding w₂, h_emb_eq,
      NumberField.InfinitePlace.mk_conjugate_eq]
theorem embeddingIndex_quotient_eq_implies_place_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (w₁ w₂ : NumberField.InfinitePlace K)
    (h : KummerCriterion.cyclotomicEvenDeltaQuotient p
            (embeddingIndex (p := p) K w₁) =
          KummerCriterion.cyclotomicEvenDeltaQuotient p
            (embeddingIndex (p := p) K w₂)) :
    w₁ = w₂ := by
  classical
  have h_qg : (QuotientGroup.mk (embeddingIndex (p := p) K w₁) :
      KummerCriterion.CyclotomicEvenDelta p) =
      QuotientGroup.mk (embeddingIndex (p := p) K w₂) := h
  rw [QuotientGroup.eq] at h_qg
  rw [KummerCriterion.CyclotomicEvenDeltaSubgroup, Subgroup.mem_zpowers_iff] at h_qg
  obtain ⟨k, hk⟩ := h_qg
  have h_sq : ((-1 : KummerCriterion.CyclotomicUnitDelta p)) ^ (2 : ℕ) = 1 := by
    rw [sq, neg_one_mul, neg_neg]
  rw [zpow_eq_zpow_emod' k h_sq] at hk
  have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases h_mod with h0 | h1
  ·
    rw [h0, zpow_zero] at hk
    have h_eq : embeddingIndex (p := p) K w₁ = embeddingIndex (p := p) K w₂ := by
      have : embeddingIndex (p := p) K w₁ *
          ((embeddingIndex (p := p) K w₁)⁻¹ * embeddingIndex (p := p) K w₂) =
          embeddingIndex (p := p) K w₁ * 1 := by
        rw [← hk]
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at this
      exact this.symm
    exact embeddingIndex_injective (p := p) K h_eq
  ·
    rw [h1, zpow_one] at hk
    have h_neg : embeddingIndex (p := p) K w₂ = -embeddingIndex (p := p) K w₁ := by
      have : embeddingIndex (p := p) K w₁ *
          ((embeddingIndex (p := p) K w₁)⁻¹ * embeddingIndex (p := p) K w₂) =
          embeddingIndex (p := p) K w₁ * (-1) := by
        rw [← hk]
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_neg_one] at this
      exact this
    have h_neg' : embeddingIndex (p := p) K w₁ = -embeddingIndex (p := p) K w₂ := by
      rw [h_neg, neg_neg]
    exact embeddingIndex_neg_implies_place_eq (p := p) K w₁ w₂ h_neg'
theorem kplusEmbeddingIndexQuotient_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    Function.Injective (kplusEmbeddingIndexQuotient (p := p) K) := by
  intro v₁ v₂ h
  unfold kplusEmbeddingIndexQuotient at h
  have h_K_eq : (NumberField.IsCMField.equivInfinitePlace K).symm v₁ =
      (NumberField.IsCMField.equivInfinitePlace K).symm v₂ :=
    embeddingIndex_quotient_eq_implies_place_eq (p := p) K _ _ h
  exact (NumberField.IsCMField.equivInfinitePlace K).symm.injective h_K_eq
theorem kplusEmbeddingIndexQuotient_bijective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    Function.Bijective (kplusEmbeddingIndexQuotient (p := p) K) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨kplusEmbeddingIndexQuotient_injective (p := p) K, ?_⟩
  exact Fintype.card_congr (KplusInfinitePlaceEquivCyclotomicEvenDelta (p := p) K hp_two)
noncomputable def KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    NumberField.InfinitePlace (oMR K) ≃
      KummerCriterion.CyclotomicEvenDelta p :=
  Equiv.ofBijective (kplusEmbeddingIndexQuotient (p := p) K)
    (kplusEmbeddingIndexQuotient_bijective (p := p) K hp_two)
theorem familyIndexAsUnit_val_in_range
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val ≥ 2 ∧
      ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val ≤ (p - 1) / 2 := by
  classical
  set j : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (oMR K)).symm i).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (KummerCriterion.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K)))) with hj_def
  have h_fin_lt : j.val < (p - 3) / 2 := Fin.isLt _
  have h_p_prime : Nat.Prime p := hp.out
  have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨k, hk⟩
  have h_lt_p : j.val + 2 < p := by omega
  have h_le_half : j.val + 2 ≤ (p - 1) / 2 := by omega
  have h_val_eq : ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val =
      j.val + 2 := by
    have h_val_spec :=
      familyIndexAsUnit_val (p := p) (K := K) hp_odd hp_three i
    rw [h_val_spec, ZMod.val_natCast, Nat.mod_eq_of_lt h_lt_p]
  refine ⟨?_, ?_⟩
  · rw [h_val_eq]; omega
  · rw [h_val_eq]; exact h_le_half
theorem familyIndexAsUnit_ne_one_and_neg_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    familyIndexAsUnit p K hp_odd hp_three i ≠ 1 ∧
      familyIndexAsUnit p K hp_odd hp_three i ≠ -1 := by
  classical
  obtain ⟨h_ge, h_le⟩ := familyIndexAsUnit_val_in_range (p := p) K hp_odd hp_three i
  have h_p_prime : Nat.Prime p := hp.out
  refine ⟨?_, ?_⟩
  ·
    intro h_eq
    have h_val : ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val =
        ((1 : (ZMod p)ˣ) : ZMod p).val := by
      rw [h_eq]
    have h_one : ((1 : (ZMod p)ˣ) : ZMod p).val = 1 := by
      change ((1 : ZMod p)).val = 1
      rw [ZMod.val_one_eq_one_mod]
      have : 1 < p := by omega
      exact Nat.mod_eq_of_lt this
    rw [h_one] at h_val
    omega
  ·
    intro h_eq
    have h_val : ((familyIndexAsUnit p K hp_odd hp_three i : (ZMod p)ˣ) : ZMod p).val =
        ((-1 : (ZMod p)ˣ) : ZMod p).val := by
      rw [h_eq]
    have h_neg_one : ((-1 : (ZMod p)ˣ) : ZMod p).val = p - 1 := by
      change ((-1 : ZMod p)).val = p - 1
      have h_v := ZMod.val_neg_of_ne_zero (a := (1 : ZMod p))
      have h_one_val : (1 : ZMod p).val = 1 := by
        rw [ZMod.val_one_eq_one_mod]
        exact Nat.mod_eq_of_lt (by omega : 1 < p)
      rw [h_v, h_one_val]
    rw [h_neg_one] at h_val
    omega
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module35

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part6
section Module36
noncomputable section
open Real Complex
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
theorem familyIndexAsUnit_quotient_ne_one
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    KummerCriterion.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i) ≠ 1 := by
  classical
  intro h
  have h_mem : familyIndexAsUnit p K hp_odd hp_three i ∈
      KummerCriterion.CyclotomicEvenDeltaSubgroup p := by
    rw [← QuotientGroup.eq_one_iff]
    exact h
  rw [KummerCriterion.CyclotomicEvenDeltaSubgroup, Subgroup.mem_zpowers_iff] at h_mem
  obtain ⟨k, hk⟩ := h_mem
  have h_sq : ((-1 : KummerCriterion.CyclotomicUnitDelta p)) ^ (2 : ℕ) = 1 := by
    rw [sq, neg_one_mul, neg_neg]
  rw [zpow_eq_zpow_emod' k h_sq] at hk
  have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  obtain ⟨h_ne_one, h_ne_neg_one⟩ :=
    familyIndexAsUnit_ne_one_and_neg_one (p := p) K hp_odd hp_three hp_ge_five i
  rcases h_mod with h0 | h1
  · rw [h0, zpow_zero] at hk
    exact h_ne_one hk.symm
  · rw [h1, zpow_one] at hk
    exact h_ne_neg_one hk.symm
theorem familyIndexAsUnit_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Function.Injective (familyIndexAsUnit p K hp_odd hp_three) := by
  classical
  intro i₁ i₂ h_eq
  have h_val_eq : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
      ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
    rw [h_eq]
  have h_p_prime : Nat.Prime p := hp.out
  have h_p_odd : Odd p := h_p_prime.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨n, hn⟩
  set j₁ : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (oMR K)).symm i₁).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (KummerCriterion.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K)))) with hj₁_def
  set j₂ : Fin ((p - 3) / 2) :=
    (((NumberField.Units.equivFinRank
        (oMR K)).symm i₂).cast
      ((NumberField.IsCMField.units_rank_eq_units_rank
          (K := K)).trans
        (KummerCriterion.units_rank_eq_prime_sub_three_div_two
          (p := p) (K := K)))) with hj₂_def
  have h_j₁_lt : j₁.val < (p - 3) / 2 := Fin.isLt _
  have h_j₂_lt : j₂.val < (p - 3) / 2 := Fin.isLt _
  have h_lt_p₁ : j₁.val + 2 < p := by omega
  have h_lt_p₂ : j₂.val + 2 < p := by omega
  have h_v1 : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
      j₁.val + 2 := by
    have h_v_spec := familyIndexAsUnit_val (p := p) K hp_odd hp_three i₁
    rw [h_v_spec, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt h_lt_p₁
  have h_v2 : ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val =
      j₂.val + 2 := by
    have h_v_spec := familyIndexAsUnit_val (p := p) K hp_odd hp_three i₂
    rw [h_v_spec, ZMod.val_natCast]
    exact Nat.mod_eq_of_lt h_lt_p₂
  rw [h_v1, h_v2] at h_val_eq
  have h_fin_eq : j₁.val = j₂.val := by omega
  have h_fin : j₁ = j₂ := Fin.ext h_fin_eq
  have h_symm_eq : (NumberField.Units.equivFinRank
      (oMR K)).symm i₁ =
      (NumberField.Units.equivFinRank
        (oMR K)).symm i₂ := by
    have h_val_symm : (((NumberField.Units.equivFinRank
          (oMR K)).symm i₁) : ℕ) =
        (((NumberField.Units.equivFinRank
          (oMR K)).symm i₂) : ℕ) := h_fin_eq
    exact Fin.ext h_val_symm
  exact (NumberField.Units.equivFinRank
      (oMR K)).symm.injective h_symm_eq
theorem familyIndexAsUnit_quotient_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) :
    Function.Injective (fun i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =>
      KummerCriterion.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i)) := by
  classical
  intro i₁ i₂ h_eq
  simp only at h_eq
  have h_div : familyIndexAsUnit p K hp_odd hp_three i₁ /
      familyIndexAsUnit p K hp_odd hp_three i₂ ∈
      KummerCriterion.CyclotomicEvenDeltaSubgroup p :=
    QuotientGroup.eq_iff_div_mem.mp h_eq
  rw [div_eq_mul_inv, KummerCriterion.CyclotomicEvenDeltaSubgroup,
      Subgroup.mem_zpowers_iff] at h_div
  obtain ⟨k, hk⟩ := h_div
  have h_sq : ((-1 : KummerCriterion.CyclotomicUnitDelta p)) ^ (2 : ℕ) = 1 := by
    rw [sq, neg_one_mul, neg_neg]
  rw [zpow_eq_zpow_emod' k h_sq] at hk
  have h_mod : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  obtain ⟨h_ge_one, h_le_one⟩ := familyIndexAsUnit_val_in_range
    (p := p) K hp_odd hp_three i₁
  obtain ⟨h_ge_two, h_le_two⟩ := familyIndexAsUnit_val_in_range
    (p := p) K hp_odd hp_three i₂
  rcases h_mod with h0 | h1
  ·
    rw [h0, zpow_zero] at hk
    have h_a_eq : familyIndexAsUnit p K hp_odd hp_three i₁ =
        familyIndexAsUnit p K hp_odd hp_three i₂ := by
      have : familyIndexAsUnit p K hp_odd hp_three i₁ *
          (familyIndexAsUnit p K hp_odd hp_three i₂)⁻¹ *
            familyIndexAsUnit p K hp_odd hp_three i₂ =
          1 * familyIndexAsUnit p K hp_odd hp_three i₂ := by rw [hk]
      rwa [inv_mul_cancel_right, one_mul] at this
    exact familyIndexAsUnit_injective (p := p) K hp_odd hp_three h_a_eq
  ·
    rw [h1, zpow_one] at hk
    have h_neg : familyIndexAsUnit p K hp_odd hp_three i₁ =
        -familyIndexAsUnit p K hp_odd hp_three i₂ := by
      have : familyIndexAsUnit p K hp_odd hp_three i₁ *
          (familyIndexAsUnit p K hp_odd hp_three i₂)⁻¹ *
            familyIndexAsUnit p K hp_odd hp_three i₂ =
          -1 * familyIndexAsUnit p K hp_odd hp_three i₂ := by rw [hk]
      rwa [inv_mul_cancel_right, neg_one_mul] at this
    have h_p_prime : Nat.Prime p := hp.out
    have h_v_eq : ((familyIndexAsUnit p K hp_odd hp_three i₁ : (ZMod p)ˣ) : ZMod p).val =
        ((-familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
      rw [h_neg]
    have h_v_neg : ((-familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val =
        p - ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val := by
      change ((-((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p))).val =
        p - ((familyIndexAsUnit p K hp_odd hp_three i₂ : (ZMod p)ˣ) : ZMod p).val
      exact ZMod.val_neg_of_ne_zero _
    rw [h_v_neg] at h_v_eq
    omega
noncomputable def familyIndexEquivNonTrivialCE
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (_hp_odd : p ≠ 2) (_hp_three : 3 ≤ p)
    (hp_two : 2 < p) :
    {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      {c : KummerCriterion.CyclotomicEvenDelta p // c ≠ 1} := by
  classical
  refine Fintype.equivOfCardEq ?_
  have h_bij : NumberField.InfinitePlace (oMR K) ≃
      KummerCriterion.CyclotomicEvenDelta p :=
    KplusInfinitePlaceEquivCyclotomicEvenDelta_canonical
      (p := p) K hp_two
  rw [Fintype.card_subtype_compl (p := fun w =>
    w = NumberField.Units.dirichletUnitTheorem.w₀)]
  rw [Fintype.card_subtype_compl (p := fun c => c = 1)]
  rw [Fintype.card_congr h_bij]
  rfl
noncomputable def familyIndexAsCEnotOne
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    {c : KummerCriterion.CyclotomicEvenDelta p // c ≠ 1} :=
  ⟨KummerCriterion.cyclotomicEvenDeltaQuotient p
      (familyIndexAsUnit p K hp_odd hp_three i),
    familyIndexAsUnit_quotient_ne_one (p := p) K hp_odd hp_three hp_ge_five i⟩
theorem familyIndexAsCEnotOne_injective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) :
    Function.Injective (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five) := by
  intro i₁ i₂ h_eq
  have h_eq_val : (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five i₁).val =
      (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five i₂).val := by
    rw [h_eq]
  exact familyIndexAsUnit_quotient_injective (p := p) K hp_odd hp_three hp_ge_five h_eq_val
noncomputable def familyIndexAsCEnotOneEquiv
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) (hp_two : 2 < p) :
    {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      {c : KummerCriterion.CyclotomicEvenDelta p // c ≠ 1} := by
  classical
  refine Equiv.ofBijective
    (familyIndexAsCEnotOne (p := p) K hp_odd hp_three hp_ge_five) ?_
  refine (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨familyIndexAsCEnotOne_injective (p := p) K hp_odd hp_three hp_ge_five, ?_⟩
  exact Fintype.card_congr
    (familyIndexEquivNonTrivialCE (p := p) K hp_odd hp_three hp_two)
@[simp]
theorem familyIndexAsCEnotOneEquiv_apply
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (hp_ge_five : 5 ≤ p) (hp_two : 2 < p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (familyIndexAsCEnotOneEquiv (p := p) K hp_odd hp_three hp_ge_five hp_two i).val =
      KummerCriterion.cyclotomicEvenDeltaQuotient p
        (familyIndexAsUnit p K hp_odd hp_three i) :=
  rfl
theorem fintype_card_nonTrivialCE_eq (hp_two : 2 < p) :
    Fintype.card {c : KummerCriterion.CyclotomicEvenDelta p // c ≠ 1} =
      (p - 1) / 2 - 1 := by
  classical
  rw [Fintype.card_subtype_compl (p := fun c => c = 1)]
  rw [KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two]
  rw [Fintype.card_subtype_eq]
noncomputable def kplusEmbeddingIndexQuotientShifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (v : NumberField.InfinitePlace (oMR K)) :
    KummerCriterion.CyclotomicEvenDelta p :=
  kplusEmbeddingIndexQuotient (p := p) K v *
    (kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)⁻¹
@[simp]
theorem kplusEmbeddingIndexQuotientShifted_w₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] :
    kplusEmbeddingIndexQuotientShifted (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀ = 1 := by
  unfold kplusEmbeddingIndexQuotientShifted
  exact mul_inv_cancel _
theorem kplusEmbeddingIndexQuotientShifted_bijective
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    Function.Bijective (kplusEmbeddingIndexQuotientShifted (p := p) K) := by
  classical
  set kw₀_inv : KummerCriterion.CyclotomicEvenDelta p :=
    (kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)⁻¹ with h_kw₀_inv
  have h_mul_bij : Function.Bijective
      (fun c : KummerCriterion.CyclotomicEvenDelta p => c * kw₀_inv) :=
    Group.mulRight_bijective kw₀_inv
  exact h_mul_bij.comp (kplusEmbeddingIndexQuotient_bijective (p := p) K hp_two)
noncomputable def KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    NumberField.InfinitePlace (oMR K) ≃
      KummerCriterion.CyclotomicEvenDelta p :=
  Equiv.ofBijective (kplusEmbeddingIndexQuotientShifted (p := p) K)
    (kplusEmbeddingIndexQuotientShifted_bijective (p := p) K hp_two)
@[simp]
theorem KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted_apply_w₀
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_two : 2 < p) :
    KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted (p := p) K hp_two
        NumberField.Units.dirichletUnitTheorem.w₀ = 1 :=
  kplusEmbeddingIndexQuotientShifted_w₀ (p := p) K
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module36

-- Source: KummerCriterion.LehmerVandiver.PlusCoprime.Sinnott.DetBridge
section Module37
noncomputable section
open Real Complex
open scoped NumberField
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
theorem sinnottMatrix_A_sub_B_apply_eq_sub_shifted
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    (i : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
    (w : {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (((sinnottMatrixA p K - sinnottMatrixB p K) i w : ℝ) : ℂ) =
      convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotientShifted (p := p) K w.val *
            kplusEmbeddingIndexQuotient (p := p) K
              NumberField.Units.dirichletUnitTheorem.w₀)
          (KummerCriterion.cyclotomicEvenDeltaQuotient p
            (familyIndexAsUnit p K hp_odd hp_three i)) -
        convolutionMatrixLogNormEven p
          (kplusEmbeddingIndexQuotientShifted (p := p) K w.val *
            kplusEmbeddingIndexQuotient (p := p) K
              NumberField.Units.dirichletUnitTheorem.w₀) 1 := by
  classical
  rw [sinnottMatrix_A_sub_B_apply_eq_sub p K hp_odd hp_three i w]
  unfold kplusEmbeddingIndexQuotientShifted
  rw [show (kplusEmbeddingIndexQuotient p K w.val *
      (kplusEmbeddingIndexQuotient p K
        NumberField.Units.dirichletUnitTheorem.w₀)⁻¹) *
      kplusEmbeddingIndexQuotient p K
        NumberField.Units.dirichletUnitTheorem.w₀ =
      kplusEmbeddingIndexQuotient p K w.val by group]
theorem det_sinnottMatrix_eq_pow_two_mul_det
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (hp_odd : p ≠ 2) (hp_three : 3 ≤ p)
    [Fintype {w : NumberField.InfinitePlace (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}]
    [DecidableEq {w : NumberField.InfinitePlace (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀}] :
    (Matrix.of fun (i : {w : NumberField.InfinitePlace
            (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
        (w : {w : NumberField.InfinitePlace
            (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        Real.log
          (((NumberField.IsCMField.equivInfinitePlace K).symm w.val)
            ((LehmerVandiver.realCyclotomicUnit p K
              ((((NumberField.Units.equivFinRank
                  (oMR K)).symm i).cast
                ((NumberField.IsCMField.units_rank_eq_units_rank
                    (K := K)).trans
                  (KummerCriterion.units_rank_eq_prime_sub_three_div_two
                    (p := p) (K := K)))) + 2) : 𝓞 K) : K))).det =
      (2 : ℝ) ^ Fintype.card {w : NumberField.InfinitePlace
            (oMR K) //
            w ≠ NumberField.Units.dirichletUnitTheorem.w₀} *
        (sinnottMatrixA p K - sinnottMatrixB p K).det := by
  rw [sinnottMatrix_eq_two_smul_A_sub_B p K hp_odd hp_three]
  exact Matrix.det_smul (sinnottMatrixA p K - sinnottMatrixB p K) 2
end Sinnott
end LehmerVandiver
end KummerCriterion
end
noncomputable section
namespace KummerCriterion
namespace LehmerVandiver
namespace Sinnott
variable (p : ℕ) [hp : Fact p.Prime]
open Classical in
theorem card_kplus_ne_w₀_eq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] (_hp_two : 2 < p) :
    Fintype.card {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      (p - 3) / 2 := by
  have h_rank_eq : NumberField.Units.rank
      (oMR K) = (p - 3) / 2 := by
    rw [NumberField.IsCMField.units_rank_eq_units_rank (K := K)]
    exact KummerCriterion.units_rank_eq_prime_sub_three_div_two (p := p) (K := K)
  have h_rank_def : NumberField.Units.rank
      (oMR K) =
      Fintype.card (NumberField.InfinitePlace
        (oMR K)) - 1 := rfl
  have h_card_compl :=
    Fintype.card_subtype_compl (α := NumberField.InfinitePlace
      (oMR K)) (p := fun w =>
      w = NumberField.Units.dirichletUnitTheorem.w₀)
  rw [Fintype.card_subtype_eq] at h_card_compl
  have h_eq : Fintype.card {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} =
      Fintype.card {w : NumberField.InfinitePlace
        (oMR K) // ¬ w =
        NumberField.Units.dirichletUnitTheorem.w₀} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [h_eq, h_card_compl]
  omega
open Classical in
theorem regOfFamily_sq_eq_two_pow_mul_det_A_sub_B_sq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) :
    (NumberField.Units.regOfFamily
        (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ^ 2 =
      (2 : ℝ) ^ (p - 3) *
        ((sinnottMatrixA p K - sinnottMatrixB p K).det) ^ 2 := by
  have h_card := card_kplus_ne_w₀_eq (p := p) K hp_two
  have h_reg_eq_abs_det := regOfFamily_cyclotomicUnitFamilyKplus_eq_det
    (p := p) (K := K) hp_odd hp_three
  have h_det_eq_two_pow := det_sinnottMatrix_eq_pow_two_mul_det
    (p := p) K hp_odd hp_three
  have h_reg_combined : NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      |(2 : ℝ) ^ Fintype.card {w : NumberField.InfinitePlace
              (oMR K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀} *
        (sinnottMatrixA p K - sinnottMatrixB p K).det| :=
    h_reg_eq_abs_det.trans (congr_arg abs h_det_eq_two_pow)
  have h_two_pow_nn : (0 : ℝ) ≤ (2 : ℝ) ^ Fintype.card
      {w : NumberField.InfinitePlace
        (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := by positivity
  rw [h_reg_combined, abs_mul, abs_of_nonneg h_two_pow_nn, mul_pow, sq_abs]
  congr 1
  rw [← pow_mul, h_card]
  congr 1
  have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
  rcases h_p_odd with ⟨k, hk⟩
  omega
open Classical in
theorem regOfFamilySqEqProdNontrivialQeSq_of_detASubBSqEqProdQeSq
    (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p)
    (h : DetASubBSqEqProdNontrivialQeSq (p := p) K) :
    RegOfFamilySqEqProdNontrivialQeSq (p := p) K hp_odd hp_three := by
  unfold RegOfFamilySqEqProdNontrivialQeSq
  unfold DetASubBSqEqProdNontrivialQeSq at h
  have h_reg_sq_R := regOfFamily_sq_eq_two_pow_mul_det_A_sub_B_sq
    (p := p) K hp_odd hp_three hp_two
  have h_reg_sq_C : ((NumberField.Units.regOfFamily
      (cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) : ℝ) : ℂ) ^ 2 =
      (2 : ℂ) ^ (p - 3) *
        (((sinnottMatrixA p K - sinnottMatrixB p K).det : ℝ) : ℂ) ^ 2 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) h_reg_sq_R
    push_cast at this
    exact this
  rw [h_reg_sq_C, h]
open Classical in
theorem card_nontriv_mulChar_eq
    (hp_two : 2 < p) :
    haveI : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Fintype.ofFinite _
    Fintype.card {ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
      (p - 3) / 2 := by
  let : Fintype (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  have h_card_mc :
      Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
      (p - 1) / 2 := by
    have h1 : Fintype.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) =
        Nat.card (MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ) :=
      Nat.card_eq_fintype_card.symm
    rw [h1, nat_card_mulChar_cyclotomicEvenDelta_eq p]
    rw [Nat.card_eq_fintype_card]
    exact KummerCriterion.cyclotomicEvenDelta_card (p := p) hp_two
  have h_card_compl :=
    Fintype.card_subtype_compl
      (α := MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ)
      (p := fun ξ => ξ = 1)
  rw [Fintype.card_subtype_eq] at h_card_compl
  have h_eq :
      Fintype.card {ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
      Fintype.card {ξ : MulChar (KummerCriterion.CyclotomicEvenDelta p) ℂ // ¬ ξ = 1} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))
  rw [h_eq, h_card_compl, h_card_mc]
  have h_p_odd : Odd p := hp.out.odd_of_ne_two (by omega)
  rcases h_p_odd with ⟨k, hk⟩
  omega
end Sinnott
end LehmerVandiver
end KummerCriterion
end
end Module37

-- Source: KummerCriterion.CyclotomicUnits.IndexDeterminant
section Module38
noncomputable section
open scoped BigOperators
namespace KummerCriterion
namespace CyclotomicUnits
variable (p : ℕ) [Fact p.Prime]
noncomputable def cyclotomicEvenNontrivCharEquivNonidentity (hp_two : 2 < p) :
    NontrivChar (CyclotomicEvenDelta p) ≃ Nonidentity (CyclotomicEvenDelta p) := by
  classical
  letI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  letI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  refine Fintype.equivOfCardEq ?_
  have hχ := LehmerVandiver.Sinnott.card_nontriv_mulChar_eq p hp_two
  have hG := LehmerVandiver.Sinnott.fintype_card_nonTrivialCE_eq p hp_two
  simp only [← Nat.card_eq_fintype_card] at hχ hG ⊢
  change Nat.card {ξ : MulChar (CyclotomicEvenDelta p) ℂ // ξ ≠ 1} =
    Nat.card {c : CyclotomicEvenDelta p // c ≠ 1}
  rw [hχ, hG]
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hp_odd with ⟨k, hk⟩
  omega
theorem det_cyclotomicEven_logNorm_deletedMulAtReindexed_sq_eq_prod_quotientEigenvalue_sq
    (hp_two : 2 < p) (h₀ : CyclotomicEvenDelta p) :
    haveI : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
    haveI : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
    (deletedConvolutionMulMatrixAtReindexed
      (G := CyclotomicEvenDelta p) h₀
      (LehmerVandiver.Sinnott.convolutionLogNormDescended p)).det ^ 2 =
      (∏ ξ ∈ (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1,
        LehmerVandiver.Sinnott.quotientEigenvalue p ξ) ^ 2 := by
  classical
  let : Fintype (MulChar (CyclotomicEvenDelta p) ℂ) := Fintype.ofFinite _
  let : DecidableEq (MulChar (CyclotomicEvenDelta p) ℂ) := Classical.decEq _
  rw [det_deletedConvolutionMulMatrixAtReindexed_sq_eq_prod_deletedFourierCoeffMul_sq
    (G := CyclotomicEvenDelta p)
    (cyclotomicEvenNontrivCharEquivNonidentity (p := p) hp_two) h₀
    (LehmerVandiver.Sinnott.convolutionLogNormDescended p)]
  congr 1
  erw [Finset.prod_subtype
    (p := fun ξ : MulChar (CyclotomicEvenDelta p) ℂ => ξ ≠ 1)
    (s := (Finset.univ : Finset (MulChar (CyclotomicEvenDelta p) ℂ)).erase 1)
    (f := fun ξ => LehmerVandiver.Sinnott.quotientEigenvalue p ξ)]
  · refine Finset.prod_congr rfl ?_
    intro ξ _
    unfold deletedFourierCoeffMul LehmerVandiver.Sinnott.quotientEigenvalue
    rfl
  · intro ξ
    simp [Finset.mem_erase]
end CyclotomicUnits
end KummerCriterion
noncomputable section
open scoped BigOperators
open NumberField
namespace KummerCriterion
namespace CyclotomicUnits
variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]
theorem det_submatrix_equiv_equiv_sq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e₁ e₂ : κ ≃ ι) (A : Matrix ι ι ℂ) :
    (A.submatrix e₁ e₂).det ^ 2 = A.det ^ 2 := by
  classical
  have hdet := Matrix.det_reindex e₁.symm e₂.symm A
  change (((Matrix.reindex e₁.symm e₂.symm) A).det) ^ 2 = A.det ^ 2
  rw [hdet, mul_pow]
  have hsign :
      ((↑↑(Equiv.Perm.sign (e₂.symm.trans e₁.symm.symm)) : ℂ)) ^ 2 = 1 := by
    let σ : Equiv.Perm ι := e₂.symm.trans e₁.symm.symm
    have hunit : (Equiv.Perm.sign σ) ^ 2 = 1 :=
      Int.units_pow_two _
    have hcast := congrArg (fun u : ℤˣ => ((u : ℂ))) hunit
    push_cast at hcast
    simpa [σ] using hcast
  rw [hsign, one_mul]
noncomputable def kplusPlaceStarEquivNonidentityShifted
    (hp_two : 2 < p) :
    {w : InfinitePlace (oMR K) // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} ≃
      Nonidentity (CyclotomicEvenDelta p) := by
  classical
  let e :=
    LehmerVandiver.Sinnott.KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted
      (p := p) K hp_two
  have h_w₀ : e NumberField.Units.dirichletUnitTheorem.w₀ = 1 :=
    LehmerVandiver.Sinnott.KplusInfinitePlaceEquivCyclotomicEvenDelta_shifted_apply_w₀
      (p := p) K hp_two
  exact e.subtypeEquiv fun v => not_congr (by rw [← h_w₀]; exact e.apply_eq_iff_eq.symm)
@[simp]
theorem kplusPlaceStarEquivNonidentityShifted_apply
    (hp_two : 2 < p)
    (w : {w : InfinitePlace (oMR K) // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) :
    (kplusPlaceStarEquivNonidentityShifted (p := p) (K := K) hp_two w).val =
      LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotientShifted (p := p) K w.val := by
  rfl
theorem detASubB_sq_eq_deletedFourier_sq
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    haveI : DecidableEq (InfinitePlace (oMR K)) := Classical.decEq _
    haveI : DecidablePred (fun w : InfinitePlace (oMR K) =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀) := fun _ => instDecidableNot
    haveI : Fintype {w : InfinitePlace (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
      Subtype.fintype (fun w : InfinitePlace (oMR K) =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀)
    haveI : DecidableEq {w : InfinitePlace (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := fun a b => a.instDecidableEq b
    (((((LehmerVandiver.Sinnott.sinnottMatrixA p K -
      LehmerVandiver.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ)) ^ 2 : ℂ) =
      (deletedConvolutionMulMatrixAtReindexed
        (G := CyclotomicEvenDelta p)
        (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
          NumberField.Units.dirichletUnitTheorem.w₀)
        (LehmerVandiver.Sinnott.convolutionLogNormDescended p)).det ^ 2 := by
  classical
  let rowEquiv :=
    kplusPlaceStarEquivNonidentityShifted (p := p) (K := K) hp_two
  let colEquiv :=
    LehmerVandiver.Sinnott.familyIndexAsCEnotOneEquiv
      (p := p) K hp_odd hp_three hp_ge_five hp_two
  let D :=
    deletedConvolutionMulMatrixAtReindexed
      (G := CyclotomicEvenDelta p)
      (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
        NumberField.Units.dirichletUnitTheorem.w₀)
      (LehmerVandiver.Sinnott.convolutionLogNormDescended p)
  have hcast :
      (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
          LehmerVandiver.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ) =
        (Matrix.of fun
          (i : {w : InfinitePlace (oMR K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (w : {w : InfinitePlace (oMR K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
              LehmerVandiver.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)).det := by
    rw [show (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
        LehmerVandiver.Sinnott.sinnottMatrixB p K).det : ℝ) : ℂ) =
        (Complex.ofRealHom ((LehmerVandiver.Sinnott.sinnottMatrixA p K -
          LehmerVandiver.Sinnott.sinnottMatrixB p K).det) : ℂ) from rfl]
    rw [Complex.ofRealHom.map_det]
    rfl
  have hmatrix :
      (Matrix.of fun
          (w : {w : InfinitePlace (oMR K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
          (i : {w : InfinitePlace (oMR K) //
              w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
            (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
              LehmerVandiver.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)) =
        D.submatrix rowEquiv colEquiv := by
    ext w i
    rw [Matrix.of_apply, Matrix.submatrix_apply]
    rw [LehmerVandiver.Sinnott.sinnottMatrix_A_sub_B_apply_eq_sub_shifted
      (p := p) K hp_odd hp_three i w]
    simp only [LehmerVandiver.Sinnott.convolutionMatrixLogNormEven, Matrix.of_apply, D,
      deletedConvolutionMulMatrixAtReindexed]
    rw [kplusPlaceStarEquivNonidentityShifted_apply
      (p := p) (K := K) hp_two w]
    rw [LehmerVandiver.Sinnott.familyIndexAsCEnotOneEquiv_apply
      (p := p) K hp_odd hp_three hp_ge_five hp_two i]
    congr 2
    · exact congrArg (fun t : CyclotomicEvenDelta p =>
        t * cyclotomicEvenDeltaQuotient p
          (LehmerVandiver.Sinnott.familyIndexAsUnit p K hp_odd hp_three i))
        (mul_comm (G := CyclotomicEvenDelta p)
          (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotientShifted p K w)
          (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotient p K
            NumberField.Units.dirichletUnitTheorem.w₀))
    · simpa only [mul_one] using (mul_comm (G := CyclotomicEvenDelta p)
        (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotientShifted p K w)
        (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotient p K
          NumberField.Units.dirichletUnitTheorem.w₀))
  rw [hcast]
  rw [← Matrix.det_transpose]
  change
    (Matrix.of fun
      (w : {w : InfinitePlace (oMR K) //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀})
      (i : {w : InfinitePlace (oMR K) //
          w ≠ NumberField.Units.dirichletUnitTheorem.w₀}) =>
        (((LehmerVandiver.Sinnott.sinnottMatrixA p K -
          LehmerVandiver.Sinnott.sinnottMatrixB p K) i w : ℝ) : ℂ)).det ^ 2 =
      D.det ^ 2
  rw [hmatrix]
  exact det_submatrix_equiv_equiv_sq rowEquiv colEquiv D
theorem detASubBSqEqProdNontrivialQeSq_of_deletedFourier
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    haveI : DecidableEq (InfinitePlace (oMR K)) := Classical.decEq _
    haveI : DecidablePred (fun w : InfinitePlace (oMR K) =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀) := fun _ => instDecidableNot
    haveI : Fintype {w : InfinitePlace (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} :=
      Subtype.fintype (fun w : InfinitePlace (oMR K) =>
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀)
    haveI : DecidableEq {w : InfinitePlace (oMR K) //
        w ≠ NumberField.Units.dirichletUnitTheorem.w₀} := fun a b => a.instDecidableEq b
    LehmerVandiver.Sinnott.DetASubBSqEqProdNontrivialQeSq (p := p) K := by
  classical
  unfold LehmerVandiver.Sinnott.DetASubBSqEqProdNontrivialQeSq
  rw [detASubB_sq_eq_deletedFourier_sq
    (p := p) (K := K) hp_odd hp_three hp_two hp_ge_five]
  exact det_cyclotomicEven_logNorm_deletedMulAtReindexed_sq_eq_prod_quotientEigenvalue_sq
    (p := p) hp_two
    (LehmerVandiver.Sinnott.kplusEmbeddingIndexQuotient (p := p) K
      NumberField.Units.dirichletUnitTheorem.w₀)
end CyclotomicUnits
end KummerCriterion
end
end
end Module38

-- Source: KummerCriterion.CyclotomicUnits.Saturation
section Module39
noncomputable section
open NumberField NumberField.IsCMField
namespace KummerCriterion
variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]
theorem realCyclotomicUnit_index_coprime {a : ℕ}
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : a.Coprime p := by
  have hp_prime : Nat.Prime p := Fact.out
  have ha_pos : 0 < a := by omega
  have ha_lt : a < p := by
    have hhalf : (p - 1) / 2 < p := by omega
    omega
  have hnot : ¬ p ∣ a := fun hpa => by
    exact (not_le_of_gt ha_lt) (Nat.le_of_dvd ha_pos hpa)
  exact (hp_prime.coprime_iff_not_dvd.mpr hnot).symm
noncomputable def realCyclotomicUnit (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) : (𝓞 (oMR K))ˣ :=
  LehmerVandiver.realCyclotomicUnitPlusUnit p K a
    (realCyclotomicUnit_index_coprime (p := p) ha_two ha_le)
    (Fact.out : Nat.Prime p).two_le
@[simp]
theorem realCyclotomicUnit_val (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le : 𝓞 (oMR K)) =
      LehmerVandiver.realCyclotomicUnitPlus p K a := by
  unfold realCyclotomicUnit
  rw [LehmerVandiver.realCyclotomicUnitPlusUnit_val]
theorem algebraMap_realCyclotomicUnit (a : ℕ)
    (ha_two : 2 ≤ a) (ha_le : a ≤ (p - 1) / 2) :
    algebraMap (𝓞 (oMR K)) (𝓞 K)
        (realCyclotomicUnit (p := p) (K := K) a ha_two ha_le : 𝓞 (oMR K)) =
      LehmerVandiver.realCyclotomicUnit p K a := by
  rw [realCyclotomicUnit_val, LehmerVandiver.algebraMap_realCyclotomicUnitPlus]
end KummerCriterion
end
noncomputable section
open NumberField
namespace KummerCriterion
variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]
abbrev CPlusGeneratorIndex (_hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) : ℕ :=
  (i : ℕ) + 2
omit [Fact p.Prime] in
theorem CPlusGeneratorIndex_two_le (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    2 ≤ CPlusGeneratorIndex (p := p) hp_three i := by
  simp [CPlusGeneratorIndex]
theorem CPlusGeneratorIndex_le_half (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    CPlusGeneratorIndex (p := p) hp_three i ≤ (p - 1) / 2 := by
  have hi : (i : ℕ) < (p - 3) / 2 := i.isLt
  have hp_odd_mod : p % 2 = 1 :=
    Nat.odd_iff.mp ((Fact.out : Nat.Prime p).odd_of_ne_two (by omega))
  have hhalf : (p - 1) / 2 = (p - 3) / 2 + 1 := by
    omega
  dsimp [CPlusGeneratorIndex]
  rw [hhalf]
  omega
noncomputable def CPlusGenerator (hp_three : 3 ≤ p)
    (i : Fin ((p - 3) / 2)) : (𝓞 (oMR K))ˣ :=
  realCyclotomicUnit (p := p) (K := K) (CPlusGeneratorIndex (p := p) hp_three i)
    (CPlusGeneratorIndex_two_le (p := p) hp_three i)
    (CPlusGeneratorIndex_le_half (p := p) hp_three i)
def CPlus (hp_three : 3 ≤ p) : Subgroup (𝓞 (oMR K))ˣ :=
  Subgroup.closure
    ({(-1 : (𝓞 (oMR K))ˣ)} ∪ Set.range (CPlusGenerator (p := p) (K := K) hp_three))
theorem neg_one_mem_CPlus (hp_three : 3 ≤ p) :
    (-1 : (𝓞 (oMR K))ˣ) ∈ CPlus (p := p) (K := K) hp_three :=
  Subgroup.subset_closure (by left; rfl)
theorem CPlusGenerator_mem (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    CPlusGenerator (p := p) (K := K) hp_three i ∈ CPlus (p := p) (K := K) hp_three :=
  Subgroup.subset_closure (by right; exact ⟨i, rfl⟩)
end KummerCriterion
end
end Module39

-- Source: KummerCriterion.CyclotomicUnits.NormalizedIndex
section Module40
noncomputable section
open NumberField
namespace KummerCriterion
variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]
def cyclotomicUnitIndexSubgroup (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Subgroup (𝓞 (oMR K))ˣ :=
  Subgroup.closure
      (Set.range (LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ⊔
    NumberField.Units.torsion (oMR K)
end KummerCriterion
end
noncomputable section
open NumberField
namespace KummerCriterion
variable {p : ℕ} [Fact p.Prime]
variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]
theorem CPlusGenerator_eq_cyclotomicUnitFamilyKplus
    (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    CPlusGenerator (p := p) (K := K) hp_three i =
      LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplus p K hp_three i := by
  apply Units.ext
  simp [CPlusGenerator, realCyclotomicUnit, LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplus]
theorem cyclotomicUnitFamilyKplus_mem_CPlus
    (hp_three : 3 ≤ p) (i : Fin ((p - 3) / 2)) :
    LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplus p K hp_three i ∈
      CPlus (p := p) (K := K) hp_three := by
  rw [← CPlusGenerator_eq_cyclotomicUnitFamilyKplus
    (p := p) (K := K) hp_three i]
  exact CPlusGenerator_mem (p := p) (K := K) hp_three i
theorem range_cyclotomicUnitFamilyKplusFinRank_eq
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Set.range (LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three) =
      Set.range (LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplus p K hp_three) := by
  classical
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    unfold LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplusFinRank
    exact ⟨i.cast ((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
      (units_rank_eq_prime_sub_three_div_two (p := p) (K := K))), rfl⟩
  · rintro ⟨i, rfl⟩
    unfold LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplusFinRank
    refine ⟨i.cast (((NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
      (units_rank_eq_prime_sub_three_div_two (p := p) (K := K))).symm), ?_⟩
    simp
theorem torsionKplus_le_CPlus (hp_three : 3 ≤ p) :
    NumberField.Units.torsion (oMR K) ≤ CPlus (p := p) (K := K) hp_three := by
  intro x hx
  rcases maximalRealSubfield_torsion_eq_one_or_neg_one
      (K := K) ⟨x, hx⟩ with h_one | h_neg
  · have hx_one : x = 1 := by
      simpa using h_one
    rw [hx_one]
    exact Subgroup.one_mem _
  · have hx_neg : x = -1 := by
      simpa using h_neg
    rw [hx_neg]
    exact neg_one_mem_CPlus (p := p) (K := K) hp_three
theorem closure_cyclotomicUnitFamilyKplus_le_CPlus
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    Subgroup.closure
        (Set.range
          (LehmerVandiver.Sinnott.cyclotomicUnitFamilyKplusFinRank p K hp_odd hp_three)) ≤
      CPlus (p := p) (K := K) hp_three := by
  rw [Subgroup.closure_le, range_cyclotomicUnitFamilyKplusFinRank_eq
    (p := p) (K := K) hp_odd hp_three]
  rintro x ⟨i, rfl⟩
  exact cyclotomicUnitFamilyKplus_mem_CPlus (p := p) (K := K) hp_three i
theorem CPlus_le_cyclotomicUnitIndexSubgroup
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    CPlus (p := p) (K := K) hp_three ≤
      cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three := by
  unfold CPlus cyclotomicUnitIndexSubgroup
  rw [Subgroup.closure_le]
  rintro x (hx | hx)
  · rcases hx with rfl
    exact Subgroup.mem_sup_right <| neg_one_mem_torsion
  · rcases hx with ⟨i, rfl⟩
    rw [CPlusGenerator_eq_cyclotomicUnitFamilyKplus (p := p) (K := K) hp_three i]
    exact Subgroup.mem_sup_left <| Subgroup.subset_closure <|
      range_cyclotomicUnitFamilyKplusFinRank_eq (p := p) (K := K) hp_odd hp_three ▸
        Set.mem_range_self i
theorem cyclotomicUnitIndexSubgroup_le_CPlus
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three ≤
      CPlus (p := p) (K := K) hp_three := by
  unfold cyclotomicUnitIndexSubgroup
  exact sup_le
    (closure_cyclotomicUnitFamilyKplus_le_CPlus (p := p) (K := K) hp_odd hp_three)
    (torsionKplus_le_CPlus (p := p) (K := K) hp_three)
theorem cyclotomicUnitIndexSubgroup_eq_CPlus
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) :
    cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three =
      CPlus (p := p) (K := K) hp_three :=
  le_antisymm
    (cyclotomicUnitIndexSubgroup_le_CPlus (p := p) (K := K) hp_odd hp_three)
    (CPlus_le_cyclotomicUnitIndexSubgroup (p := p) (K := K) hp_odd hp_three)
open Classical in
theorem kummerDirichletDeterminant_of_deletedFourier
    (hp_odd : p ≠ 2) (hp_three : 3 ≤ p) (hp_two : 2 < p) (hp_ge_five : 5 ≤ p) :
    LehmerVandiver.Sinnott.KummerDirichletDeterminant p K hp_odd hp_three := by
  have hdetAB :=
    CyclotomicUnits.detASubBSqEqProdNontrivialQeSq_of_deletedFourier
      (p := p) (K := K) hp_odd hp_three hp_two hp_ge_five
  have hreg :=
    LehmerVandiver.Sinnott.regOfFamilySqEqProdNontrivialQeSq_of_detASubBSqEqProdQeSq
      (p := p) K hp_odd hp_three hp_two hdetAB
  exact LehmerVandiver.Sinnott.KummerDirichletDeterminant_of_regOfFamilySqEqProdNontrivialQeSq
    (p := p) K hp_odd hp_three hp_two hreg
theorem hPlus_eq_one_of_eq_three (hp_odd : p ≠ 2) (hp_eq : p = 3) :
    hPlus K = 1 := by
  subst p
  have : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid K
  have h_dvd : hPlus K ∣ h K :=
    hPlus_dvd_h (p := 3) (hp_odd := by norm_num) (K := K)
  have h_one : h K = 1 := by
    have h_class : NumberField.classNumber K = 1 :=
      NumberField.classNumber_eq_one_iff.mpr inferInstance
    simpa [h, NumberField.classNumber] using h_class
  rw [h_one] at h_dvd
  exact Nat.eq_one_of_dvd_one h_dvd
theorem CPlus_eq_top_of_eq_three
    (hp_three : 3 ≤ p) (hp_eq : p = 3) :
    CPlus (p := p) (K := K) hp_three = ⊤ := by
  have h_rank : NumberField.Units.rank (oMR K) = 0 := by
    have h_rank_eq :=
      (NumberField.IsCMField.units_rank_eq_units_rank (K := K)).trans
        (units_rank_eq_prime_sub_three_div_two (p := p) (K := K))
    simpa [hp_eq] using h_rank_eq
  apply le_antisymm le_top
  rw [← NumberField.Units.closure_fundSystem_sup_torsion_eq_top (K := (oMR K))]
  refine sup_le ?_ (torsionKplus_le_CPlus (p := p) (K := K) hp_three)
  rw [Subgroup.closure_le]
  rintro x ⟨i, rfl⟩
  have hi : (i : ℕ) < 0 := by
    simpa [h_rank] using i.isLt
  omega
end KummerCriterion
end
end Module40

open NumberField KummerCriterion
open scoped NumberField BigOperators
namespace KummerIndexBridge
lemma generator_image (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K] (hp3 : 3 ≤ p)
    (a : Fin ((p - 3) / 2)) :
    algebraMap (𝓞 (maximalRealSubfield K)) K
      (CPlusGenerator (p := p) (K := K) hp3 a : 𝓞 (maximalRealSubfield K)) =
      (∑ i ∈ Finset.range (a.val + 2), (IsCyclotomicExtension.zeta p ℚ K) ^ i) *
        (∑ i ∈ Finset.range (a.val + 2), ((IsCyclotomicExtension.zeta p ℚ K)⁻¹) ^ i) := by
  let hz := IsCyclotomicExtension.zeta_spec p ℚ K
  have ht : hz.unit' ∈ NumberField.Units.torsion K :=
    (CommGroup.mem_torsion _).mpr
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨p, (Fact.out : p.Prime).pos, hz.unit'_pow⟩)
  have hv : (hz.unit' : 𝓞 K) = hz.toInteger :=
    IsUnit.unit_spec (hz.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p))
  have hvi : algebraMap (𝓞 K) K hz.toInteger = IsCyclotomicExtension.zeta p ℚ K := rfl
  have hvk : algebraMap (𝓞 K) K (hz.unit' : 𝓞 K) =
      IsCyclotomicExtension.zeta p ℚ K := by rw [hv, hvi]
  have hconj : IsCMField.complexConj K (IsCyclotomicExtension.zeta p ℚ K) =
      (IsCyclotomicExtension.zeta p ℚ K)⁻¹ := by
    have hc := IsCMField.complexConj_torsion (K := K) ⟨hz.unit', ht⟩
    change IsCMField.complexConj K (algebraMap (𝓞 K) K (hz.unit' : 𝓞 K)) =
      (algebraMap (𝓞 K) K (hz.unit' : 𝓞 K))⁻¹ at hc
    rwa [hvk] at hc
  change algebraMap (𝓞 (maximalRealSubfield K)) K
    (realCyclotomicUnit (p := p) (K := K) (CPlusGeneratorIndex (p := p) hp3 a) _ _ :
      𝓞 (maximalRealSubfield K)) = _
  rw [IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield K)) (𝓞 K) K,
    algebraMap_realCyclotomicUnit]
  simp [LehmerVandiver.realCyclotomicUnit, LehmerVandiver.cyclotomicUnit,
    map_sum, map_pow, map_mul, CPlusGeneratorIndex, hv, hvi, hconj]
end KummerIndexBridge
open KummerIndexBridge
theorem OMA.solution :
    OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1.H1 := by
  intro p hp hp2
  let K := CyclotomicField p ℚ
  let : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let : IsCMField K := isCMField_of_cyclotomic p hp2 K
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  refine ⟨CPlusGenerator (p := p) (K := K) hp3, generator_image p K hp3, ?_⟩
  change (CPlus (p := p) (K := K) hp3).index = 2 ^ ((p - 3) / 2) * hPlus K
  by_cases heq3 : p = 3
  · rw [CPlus_eq_top_of_eq_three hp3 heq3, Subgroup.index_top,
      hPlus_eq_one_of_eq_three hp2 heq3]
    simp [heq3]
  · have hp5 : 5 ≤ p := by
      have hodd := hp.out.odd_of_ne_two hp2
      obtain ⟨k, hk⟩ := hodd
      omega
    have hdet := kummerDirichletDeterminant_of_deletedFourier
      (p := p) (K := K) hp2 hp3 (by omega) hp5
    have hreg :=
      (LehmerVandiver.Sinnott.sinnottRegulatorIdentity_iff_kummerDirichletDeterminant
        (p := p) (K := K) hp2 hp3).1 hdet
    have hsinnott := LehmerVandiver.Sinnott.sinnottIndexFormula_of_regulatorIdentity
      p K hp2 hp3 hreg
    have hidx := LehmerVandiver.Sinnott.index_eq_twoPow_mul_hPlus_of_sinnottIndexFormula
      p K hp2 hp3 hsinnott
    change (cyclotomicUnitIndexSubgroup (p := p) (K := K) hp2 hp3).index =
      2 ^ ((p - 3) / 2) * hPlus K at hidx
    rwa [cyclotomicUnitIndexSubgroup_eq_CPlus (p := p) (K := K) hp2 hp3] at hidx
