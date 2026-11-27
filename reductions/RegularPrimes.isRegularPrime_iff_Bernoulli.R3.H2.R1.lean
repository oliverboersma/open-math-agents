/-
Copyright (c) 2026 Hanan Beer and the contributors credited below.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanan Beer, Riccardo Brasca, and the credited KummerCriterion contributors
-/
import OMAReductions.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3
import Mathlib

/-!
Weak reflection through the real cyclotomic-unit index and independence modulo p.
Reduction and interface adaptation: Hanan Beer (@hananzlt).
The route and adapted algebraic lemmas are due to Riccardo Brasca
(@riccardobrasca) and the KummerCriterion contributors, Apache-2.0,
at 470de714f3de5a1ec8c0f6209502c1c5272c2c43. The factorization and
relative Bernoulli inputs reuse the campaign's already checked integration
of that source and flt-regular at bd81b78ba6e9f1c57215ff096e9e8f45d5d4b54b.
Original reduction: @Noctluxis. Degree-one boundary integration reuses
Hanan Beer campaign PR6699; the approach was informed by @chris01-dev (PR2526).
The reused flt-regular history includes Ruben Van de Velde, Chris Birkbeck,
Andrew Yang, and Kim Morrison. All original Apache-2.0 attribution is retained.
-/

namespace OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1

open NumberField
open scoped NumberField BigOperators

/-- The squared real cyclotomic units generate a subgroup with the classical index. -/
def H1 : Prop := ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
  let K := CyclotomicField p ℚ
  let L := maximalRealSubfield K
  let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let z := IsCyclotomicExtension.zeta p ℚ K
  let m := (p - 3) / 2
  ∃ g : Fin m → (𝓞 L)ˣ,
    (∀ a, algebraMap (𝓞 L) K (g a : 𝓞 L) =
      (∑ i ∈ Finset.range (a.val + 2), z ^ i) *
        (∑ i ∈ Finset.range (a.val + 2), (z⁻¹) ^ i)) ∧
    (Subgroup.closure ({(-1 : (𝓞 L)ˣ)} ∪ Set.range g)).index =
      2 ^ m * classNumber L

/-- Bernoulli nonvanishing makes the real cyclotomic generators independent modulo pth powers. -/
def H2 : Prop := ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
  let K := CyclotomicField p ℚ
  let L := maximalRealSubfield K
  let _ : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  let z := IsCyclotomicExtension.zeta p ℚ K
  let m := (p - 3) / 2
  ∀ g : Fin m → (𝓞 L)ˣ,
    (∀ a, algebraMap (𝓞 L) K (g a : 𝓞 L) =
      (∑ i ∈ Finset.range (a.val + 2), z ^ i) *
        (∑ i ∈ Finset.range (a.val + 2), (z⁻¹) ^ i)) →
    (∀ j : ℕ, 1 ≤ j → 2 * j ≤ p - 3 → ¬ (p : ℤ) ∣ (bernoulli (2 * j)).num) →
    ∀ (s : ℤ) (e : Fin m → ℤ) (u : (𝓞 L)ˣ),
      u ^ p = (-1) ^ s * ∏ a, g a ^ e a → ∀ a, (p : ℤ) ∣ e a

/-- The real and relative class numbers multiply to the full class number. -/
def H3 : Prop := ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
  let K := CyclotomicField p ℚ
  classNumber K = classNumber (maximalRealSubfield K) *
    (classNumber K / classNumber (maximalRealSubfield K))

/-- The already established relative Bernoulli criterion, in the index convention used here. -/
def H4 : Prop := ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
  let K := CyclotomicField p ℚ
  p ∣ classNumber K / classNumber (maximalRealSubfield K) ↔
    ∃ j : ℕ, 1 ≤ j ∧ 2 * j ≤ p - 3 ∧ (p : ℤ) ∣ (bernoulli (2 * j)).num


open scoped BigOperators NumberField
open NumberField

lemma generator_expression {G : Type*} [CommGroup G] {n : ℕ}
    (ε : G) (g : Fin n → G) {x : G}
    (hx : x ∈ Subgroup.closure ({ε} ∪ Set.range g)) :
    ∃ (s : ℤ) (e : Fin n → ℤ), ε ^ s * ∏ a, g a ^ e a = x := by
  classical
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · rcases hx with rfl
        exact ⟨1, 0, by simp⟩
      · rcases hx with ⟨i, rfl⟩
        exact ⟨0, (fun j => if j = i then 1 else 0), by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x y _ _ hx hy =>
      rcases hx with ⟨s, e, rfl⟩
      rcases hy with ⟨t, f, rfl⟩
      exact ⟨s + t, e + f, by
        simp [zpow_add, Finset.prod_mul_distrib, mul_assoc, mul_left_comm]⟩
  | inv x _ hx =>
      rcases hx with ⟨s, e, rfl⟩
      exact ⟨-s, -e, by simp [Finset.prod_inv_distrib, mul_comm]⟩

lemma generator_expression_mem {G : Type*} [CommGroup G] {n : ℕ}
    (ε : G) (g : Fin n → G) (s : ℤ) (e : Fin n → ℤ) :
    ε ^ s * ∏ a, g a ^ e a ∈ Subgroup.closure ({ε} ∪ Set.range g) := by
  let C := Subgroup.closure ({ε} ∪ Set.range g)
  exact C.mul_mem
    (C.zpow_mem (Subgroup.subset_closure (Or.inl rfl)) s)
    (C.prod_mem fun a _ => C.zpow_mem
      (Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)) (e a))

lemma sign_zpow_pow {G : Type*} [CommGroup G] {ε : G}
    (hε : ε ^ 2 = 1) {p : ℕ} (hp : Odd p) (s : ℤ) :
    (ε ^ s) ^ p = ε ^ s := by
  have hsq : (ε ^ s) ^ 2 = 1 := by
    calc
      (ε ^ s) ^ 2 = (ε ^ s) ^ (2 : ℤ) := (zpow_natCast (ε ^ s) 2).symm
      _ = ε ^ (s * (2 : ℤ)) := by rw [zpow_mul]
      _ = (ε ^ (2 : ℤ)) ^ s := by rw [mul_comm, zpow_mul]
      _ = 1 := by simpa using congrArg (fun y : G => y ^ s) hε
  obtain ⟨k, hk⟩ := hp
  rw [hk, pow_add, pow_mul, hsq]
  simp

lemma index_prime_to_of_independent_generators {G : Type*} [CommGroup G]
    {n p : ℕ} [hp : Fact p.Prime] (hodd : Odd p)
    (ε : G) (hε : ε ^ 2 = 1) (g : Fin n → G)
    (hfinite : (Subgroup.closure ({ε} ∪ Set.range g)).index ≠ 0)
    (htors : ∀ x : G, x ^ p = 1 → x ∈ Subgroup.closure ({ε} ∪ Set.range g))
    (hind : ∀ (s : ℤ) (e : Fin n → ℤ) (u : G),
      u ^ p = ε ^ s * ∏ a, g a ^ e a → ∀ a, (p : ℤ) ∣ e a) :
    ¬ p ∣ (Subgroup.closure ({ε} ∪ Set.range g)).index := by
  classical
  let C := Subgroup.closure ({ε} ∪ Set.range g)
  let : C.FiniteIndex := ⟨hfinite⟩
  intro hdiv
  have hcard : p ∣ Nat.card (G ⧸ C) := by
    simpa [C, Subgroup.index_eq_card] using hdiv
  obtain ⟨q, hq_order⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ C) p hcard
  have hq_pow : q ^ p = 1 := by
    rw [← hq_order]
    exact pow_orderOf_eq_one q
  revert hq_order hq_pow
  refine QuotientGroup.induction_on q ?_
  intro u hq_order hq_pow
  have hup : u ^ p ∈ C :=
    (QuotientGroup.eq_one_iff (N := C) (u ^ p)).mp (by simpa using hq_pow)
  obtain ⟨s, e, he⟩ := generator_expression ε g hup
  have hd := hind s e u he.symm
  choose k hk using hd
  let v := ε ^ s * ∏ a, g a ^ k a
  have hvC : v ∈ C := generator_expression_mem ε g s k
  have hvp : v ^ p = u ^ p := by
    dsimp [v]
    rw [mul_pow, sign_zpow_pow hε hodd s, ← he]
    congr 1
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro a _
    rw [← zpow_natCast, ← zpow_mul, mul_comm, ← hk a]
  have huv : (u * v⁻¹) ^ p = 1 := by
    simp [mul_pow, hvp]
  have huC : u ∈ C := by
    simpa [mul_assoc] using C.mul_mem (htors (u * v⁻¹) huv) hvC
  have hq_one : ((u : G) : G ⧸ C) = 1 :=
    (QuotientGroup.eq_one_iff (N := C) u).mpr huC
  have hp_one : p = 1 := by
    rw [← hq_order, hq_one]
    simp
  exact hp.out.ne_one hp_one

lemma real_unit_torsion_sign (K : Type*) [Field K] [NumberField K]
    (u : (𝓞 (maximalRealSubfield K))ˣ) {n : ℕ}
    (hn : n ≠ 0) (hu : u ^ n = 1) : u = 1 ∨ u = -1 := by
  let L := maximalRealSubfield K
  let φ : L →+* ℂ := Classical.choice inferInstance
  let hφ : ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  let r : ℝ := hφ.embedding (u : L)
  have hur : (r : ℂ) = φ (u : L) := hφ.coe_embedding_apply (u : L)
  have hnorm : ‖φ (u : L)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one
      (by simpa [map_pow] using congrArg (fun z : (𝓞 L)ˣ => φ (z : L)) hu) hn
  have hr_abs : |r| = 1 := by
    rw [← hur] at hnorm
    simpa [Complex.norm_real] using hnorm
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

lemma classNumber_one_of_finrank_one (K : Type*) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) : classNumber K = 1 := by
  let e : ℚ ≃ₐ[ℚ] K := AlgEquiv.ofBijective (Algebra.ofId ℚ K)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h)
  have hc : classNumber ℚ = classNumber K :=
    Fintype.card_congr
      (ClassGroup.mulEquiv (RingOfIntegers.mapAlgEquiv e).toRingEquiv).toEquiv
  exact hc.symm.trans Rat.classNumber_eq

lemma conductor_two :
    2 ∣ classNumber (CyclotomicField 2 ℚ) ↔
      2 ∣ classNumber (CyclotomicField 2 ℚ) /
        classNumber (maximalRealSubfield (CyclotomicField 2 ℚ)) := by
  let K := CyclotomicField 2 ℚ
  have : IsCyclotomicExtension {2} ℚ K := CyclotomicField.isCyclotomicExtension 2 ℚ
  have hk : Module.finrank ℚ K = 1 := by
    rw [IsCyclotomicExtension.finrank (n := 2) K
      (Polynomial.cyclotomic.irreducible_rat (by decide))]
    norm_num
  have hplus : Module.finrank ℚ (maximalRealSubfield K) = 1 :=
    Nat.eq_one_of_mul_eq_one_right
      ((Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K).trans hk)
  change 2 ∣ classNumber K ↔ 2 ∣ classNumber K / classNumber (maximalRealSubfield K)
  rw [classNumber_one_of_finrank_one K hk,
    classNumber_one_of_finrank_one (maximalRealSubfield K) hplus]



theorem main : H1 → H2 → H3 → H4 →
    OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3.H2 := by
  intro hindex hindependent hfactor hrelative p hp
  by_cases hp2 : p = 2
  · subst p
    exact conductor_two
  · let K := CyclotomicField p ℚ
    let L := maximalRealSubfield K
    let m := (p - 3) / 2
    have hf : classNumber K = classNumber L * (classNumber K / classNumber L) :=
      hfactor p hp2
    change p ∣ classNumber K ↔ p ∣ classNumber K / classNumber L
    constructor
    · intro htotal
      rw [hf] at htotal
      rcases hp.out.dvd_mul.mp htotal with hplus | hminus
      · by_contra hnot
        have hB : ∀ j : ℕ, 1 ≤ j → 2 * j ≤ p - 3 →
            ¬ (p : ℤ) ∣ (bernoulli (2 * j)).num := by
          intro j hj hjp hnum
          exact hnot ((hrelative p hp2).mpr ⟨j, hj, hjp, hnum⟩)
        obtain ⟨g, hg, hidx⟩ := hindex p hp2
        let C := Subgroup.closure ({(-1 : (𝓞 L)ˣ)} ∪ Set.range g)
        have hfinite : C.index ≠ 0 := by
          rw [show C.index = 2 ^ m * classNumber L from hidx]
          exact mul_ne_zero (pow_ne_zero _ (by decide)) Fintype.card_ne_zero
        have htors : ∀ x : (𝓞 L)ˣ, x ^ p = 1 → x ∈ C := by
          intro x hx
          rcases real_unit_torsion_sign K x hp.out.ne_zero hx with hx1 | hxn
          · rw [hx1]
            exact C.one_mem
          · rw [hxn]
            exact Subgroup.subset_closure (Or.inl rfl)
        have hno : ¬ p ∣ C.index :=
          index_prime_to_of_independent_generators (hp.out.odd_of_ne_two hp2)
            (-1 : (𝓞 L)ˣ) (by ext; simp) g hfinite htors
            (hindependent p hp2 g hg hB)
        apply hno
        rw [show C.index = 2 ^ m * classNumber L from hidx]
        exact dvd_mul_of_dvd_right hplus (2 ^ m)
      · exact hminus
    · intro hminus
      rw [hf]
      exact dvd_mul_of_dvd_right hminus (classNumber L)

end OMA.R_RegularPrimes_isRegularPrime_iff_Bernoulli_R3_H2_R1
