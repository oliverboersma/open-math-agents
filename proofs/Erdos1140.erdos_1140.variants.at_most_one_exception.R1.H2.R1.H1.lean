import OMAReductions.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1_H2_R1
import Mathlib
/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
The quadratic field, integrality, discriminant and real-place lemmas below are adapted
from WangFrankie/QuadraticNumberFields, revision a458ae67e9a10e91355afaebfdd55ecbceebc4bc,
under the Apache 2.0 license. The application to the prime ideals of the order is original.
-/
noncomputable section
section
lemma Squarefree.not_mul_self_dvd_of_not_isUnit {R : Type*} [Monoid R]
    {r p : R} (hr : Squarefree r) (hp : ¬ IsUnit p) : ¬ p * p ∣ r := by
  intro h
  have hp2 : p ^ 2 ∣ r := by simpa [pow_two] using h
  have hsq : Squarefree (p ^ 2) := Squarefree.squarefree_of_dvd hp2 hr
  have hbad : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
    Squarefree.eq_zero_or_one_of_pow_of_not_isUnit hsq hp
  omega
lemma squarefree_int_not_dvd_four (d : ℤ) (hd : Squarefree d) : ¬ (4 : ℤ) ∣ d := by
  intro h
  exact Squarefree.not_mul_self_dvd_of_not_isUnit hd (p := (2 : ℤ))
    (fun hunit => absurd (Int.isUnit_iff.mp hunit) (by omega)) (by simpa using h)
lemma squarefree_int_emod_four (d : ℤ) (hd : Squarefree d) :
    d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
  have hnd : ¬ (4 : ℤ) ∣ d := squarefree_int_not_dvd_four d hd
  omega
lemma eq_one_of_squarefree_isSquare {d : ℤ} (hd : Squarefree d) (hsq : IsSquare d) :
    d = 1 ∨ d = -1 := by
  obtain ⟨z, rfl⟩ := hsq
  have hsqz2 : Squarefree (z ^ 2) := by simpa [pow_two] using hd
  have huz : IsUnit z := by
    by_contra hne
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 hne
    norm_num at h01
  rcases Int.isUnit_iff.mp huz with rfl | rfl <;> simp
end

section
namespace QuadraticAlgebra

section CommSemiring

variable {R : Type*} [CommSemiring R] {a b : R}
theorem leftMulMatrix_eq (x : QuadraticAlgebra R a b) :
    Algebra.leftMulMatrix (basis a b) x = !![x.re, a * x.im; x.im, x.re + b * x.im] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    simp [QuadraticAlgebra.basis]

end CommSemiring
section Int

open Matrix
theorem trace_int (a b : ℤ) (x : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) x = 2 * x.re + b * x.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b)]
  rw [leftMulMatrix_eq]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring
theorem traceMatrix_basis_int (a b : ℤ) :
    Algebra.traceMatrix ℤ (QuadraticAlgebra.basis a b) =
      !![2, b; b, 2 * a + b ^ 2] := by
  ext i j
  simp only [Algebra.traceMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trace_int, QuadraticAlgebra.basis, pow_two]
theorem discr_basis_int (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = 4 * a + b ^ 2 := by
  rw [Algebra.discr_def, traceMatrix_basis_int]
  simp [Matrix.det_fin_two]
  ring

end Int

end QuadraticAlgebra
end

section
lemma nat_eq_one_of_squarefree_intcast_of_isSquare (m : ℕ)
    (hsm : Squarefree (m : ℤ)) (hsq : IsSquare (m : ℤ)) : m = 1 := by
  have hmz : (m : ℤ) = 1 ∨ (m : ℤ) = -1 :=
    eq_one_of_squarefree_isSquare hsm hsq
  cases hmz with
  | inl h => exact_mod_cast h
  | inr h => omega
lemma int_dvd_of_ratio_square (d₁ d₂ : ℤ) (hd₂ : d₂ ≠ 0)
    (hsq_d₂ : Squarefree d₂) (hr : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₂ ∣ d₁ := by
  have hsq_den_nat : IsSquare (((d₁ : ℚ) / (d₂ : ℚ)).den) := (Rat.isSquare_iff.mp hr).2
  have hsq_den_int : IsSquare ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) := by
    rcases hsq_den_nat with ⟨n, hn⟩
    refine ⟨(n : ℤ), by exact_mod_cast hn⟩
  have hden_dvd : ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) ∣ d₂ := by
    simpa [← Rat.divInt_eq_div] using (Rat.den_dvd d₁ d₂)
  have hsqf_den_int : Squarefree ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) :=
    Squarefree.squarefree_of_dvd hden_dvd hsq_d₂
  have hden1_nat : ((d₁ : ℚ) / (d₂ : ℚ)).den = 1 :=
    nat_eq_one_of_squarefree_intcast_of_isSquare _ hsqf_den_int hsq_den_int
  exact (Rat.den_div_intCast_eq_one_iff d₁ d₂ hd₂).1 hden1_nat
end

section
lemma Int.sq_emod_four_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h
  ring_nf
  omega
lemma Int.sq_emod_four_of_odd (n : ℤ) (h : ¬ 2 ∣ n) : n ^ 2 % 4 = 1 := by
  set k := n / 2
  have hk : n = 2 * k + 1 := by omega
  rw [hk]
  ring_nf
  omega

private lemma div4_iff_mod (a' b' d : ℤ) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (a' ^ 2 - d * b' ^ 2) % 4 = 0 := by
  omega

private lemma sq_eq_four_mul_div_of_even (n : ℤ) (h : 2 ∣ n) :
    n ^ 2 = 4 * (n ^ 2 / 4) := by
  have hn2 : n ^ 2 % 4 = 0 := Int.sq_emod_four_of_even n h
  omega

private lemma sq_eq_four_mul_div_add_one_of_odd (n : ℤ) (h : ¬ 2 ∣ n) :
    n ^ 2 = 4 * (n ^ 2 / 4) + 1 := by
  have hn2 : n ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd n h
  omega

private lemma odd_eq_two_mul_div_add_one (n : ℤ) (h : ¬ 2 ∣ n) :
    n = 2 * (n / 2) + 1 := by
  omega

private lemma even_odd_impossible_of_mod_eq_zero
    (d a' b' : ℤ) (hd : Squarefree d)
    (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : 2 ∣ a') (hb : ¬ 2 ∣ b') : False := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) := sq_eq_four_mul_div_of_even a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd b' hb
  rw [hb_eq] at hmod'
  ring_nf at hmod'
  have hdvd : (4 : ℤ) ∣ d := by omega
  exact squarefree_int_not_dvd_four d hd hdvd

private lemma odd_even_impossible_of_mod_eq_zero
    (d a' b' : ℤ) (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : ¬ 2 ∣ a') (hb : 2 ∣ b') : False := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) := sq_eq_four_mul_div_of_even b' hb
  rw [ha_eq, hb_eq] at hmod'
  ring_nf at hmod'
  omega

private lemma mod_four_eq_one_of_odd_odd_of_mod_eq_zero
    (d a' b' : ℤ) (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : ¬ 2 ∣ a') (hb : ¬ 2 ∣ b') : d % 4 = 1 := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd b' hb
  rw [ha_eq, hb_eq] at hmod'
  ring_nf at hmod'
  omega
theorem dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one
    (d a' b' : ℤ) (hd : Squarefree d) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      (2 ∣ a' ∧ 2 ∣ b') ∨ (¬ 2 ∣ a' ∧ ¬ 2 ∣ b' ∧ d % 4 = 1) := by
  constructor
  · intro hdvd
    have hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0 := (div4_iff_mod a' b' d).1 hdvd
    by_cases ha : 2 ∣ a' <;> by_cases hb : 2 ∣ b'
    · exact Or.inl ⟨ha, hb⟩
    · exact (even_odd_impossible_of_mod_eq_zero d a' b' hd hmod ha hb).elim
    · exact (odd_even_impossible_of_mod_eq_zero d a' b' hmod ha hb).elim
    · exact Or.inr ⟨ha, hb, mod_four_eq_one_of_odd_odd_of_mod_eq_zero d a' b' hmod ha hb⟩
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hd1⟩
    · obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p ^ 2 - d * q ^ 2, by ring⟩
    · have ha_eq : a' = 2 * (a' / 2) + 1 := odd_eq_two_mul_div_add_one a' ha
      have hb_eq : b' = 2 * (b' / 2) + 1 := odd_eq_two_mul_div_add_one b' hb
      rw [ha_eq, hb_eq]
      ring_nf
      have hd_eq : d = 4 * (d / 4) + 1 := by omega
      rw [hd_eq]
      ring_nf
      omega
theorem even_even_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (h : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    2 ∣ a' ∧ 2 ∣ b' := by
  rcases (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).mp h with
      hab | ⟨_, _, hd1⟩
  · exact hab
  · exact absurd hd1 hd4
theorem dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · exact even_even_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd hd4
  · exact fun h => (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).2 (Or.inl h)
end

section
abbrev Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0
namespace Qsqrtd

open QuadraticAlgebra

variable {d : ℚ}

@[simp] theorem trace_eq_re_add_re_star (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = x.re + (star x).re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0),
    QuadraticAlgebra.leftMulMatrix_eq, Matrix.trace_fin_two_of]
  simp

theorem trace_eq_two_re (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = 2 * x.re := by
  rw [trace_eq_re_add_re_star]
  simp
  ring

abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

instance instFact_of_not_isSquare (d : ℚ) [Fact (¬ IsSquare d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ d + 0 * r) :=
  ⟨by intro r hr; exact (Fact.out : ¬ IsSquare d) ⟨r, by nlinarith [hr]⟩⟩

theorem finrank_ratAlgebra_eq_finrank_quadraticAlgebra (d : ℚ)
    [Fact (¬ IsSquare d)] :
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra) =
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ QuadraticAlgebra.instAlgebra) := by
  symm
  refine @Algebra.finrank_eq_of_equiv_equiv ℚ (Qsqrtd d) _ _
    QuadraticAlgebra.instAlgebra ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra
    (RingEquiv.refl ℚ) (RingEquiv.refl (Qsqrtd d)) ?_
  exact RingHom.ext_rat _ _

section RatAlgebra

local instance ratAlg1140 (d:ℚ) [Fact (¬IsSquare d)] : Algebra ℚ (Qsqrtd d) := DivisionRing.toRatAlgebra

theorem finrank_ratAlgebra_eq_two (d : ℚ) [Fact (¬ IsSquare d)] :
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra) = 2 := by
  rw [finrank_ratAlgebra_eq_finrank_quadraticAlgebra]
  exact QuadraticAlgebra.finrank_eq_two d 0

instance instRatAlgebraIsQuadraticExtension (d : ℚ) [Fact (¬ IsSquare d)] :
    Algebra.IsQuadraticExtension ℚ (Qsqrtd d) where
  finrank_eq_two' := finrank_ratAlgebra_eq_two d

end RatAlgebra
end Qsqrtd

lemma not_isSquare_int_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare d := by
  intro hsq
  rcases eq_one_of_squarefree_isSquare hd hsq with rfl | rfl <;> simp_all

lemma not_isSquare_ratCast_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare ((d : ℤ) : ℚ) := by
  intro hsqQ
  exact not_isSquare_int_of_squarefree_ne_one hd h1 (Rat.isSquare_intCast_iff.mp hsqQ)

instance instFact_not_isSquare_ratCast_of_squarefree_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
  ⟨not_isSquare_ratCast_of_squarefree_ne_one
    (d := d) (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
end

section

class QuadraticField (K : Type*) [Field K] [Algebra ℚ K] : Prop where

  isQuadratic : Algebra.IsQuadraticExtension ℚ K

instance (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℚ K :=
  QuadraticField.isQuadratic

namespace QuadraticField

theorem finrank_eq_two (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Module.finrank ℚ K = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two ℚ K

end QuadraticField

instance QuadraticField.instNumberField (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] : NumberField K where
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  to_finiteDimensional := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    convert FiniteDimensional.of_finrank_pos (K := ℚ) (V := K) (by
      rw [QuadraticField.finrank_eq_two K]; omega) using 1
    congr 1
    exact Subsingleton.elim _ _

namespace Qsqrtd

instance instQuadraticField (d : ℚ) [Fact (¬ IsSquare d)] :
    QuadraticField (Qsqrtd d) where
  isQuadratic := inferInstance

section RatAlgebra

local instance ratAlgB1140 (d:ℚ) [Fact (¬IsSquare d)] : Algebra ℚ (Qsqrtd d) := DivisionRing.toRatAlgebra

instance instRatAlgebraQuadraticField (d : ℚ) [Fact (¬ IsSquare d)] :
    QuadraticField (Qsqrtd d) where
  isQuadratic := @Qsqrtd.instRatAlgebraIsQuadraticExtension d _

end RatAlgebra

end Qsqrtd
end

section
namespace QuadraticNumberFields

abbrev Zsqrtd (d : ℤ) : Type := QuadraticAlgebra ℤ d 0

namespace Zsqrtd

variable {d : ℤ}
theorem ext {x y : Zsqrtd d} (hre : x.re = y.re) (him : x.im = y.im) : x = y :=
  QuadraticAlgebra.ext hre him

def toQsqrtd (z : Zsqrtd d) : Qsqrtd (d : ℚ) := ⟨(z.re : ℚ), (z.im : ℚ)⟩

def toQsqrtdHom (d : ℤ) : Zsqrtd d →+* Qsqrtd (d : ℚ) where
  toFun := fun z => ⟨(z.re : ℚ), (z.im : ℚ)⟩
  map_one' := by
    change ({ re := ((1 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 1
    rfl
  map_mul' := by
    intro x y
    ext <;> simp [mul_assoc, mul_comm, mul_left_comm]
  map_zero' := by
    change ({ re := ((0 : ℤ) : ℚ), im := ((0 : ℤ) : ℚ) } : Qsqrtd (d : ℚ)) = 0
    rfl
  map_add' := by
    intro x y
    ext <;> simp

@[simp] theorem toQsqrtdHom_apply (d : ℤ) (z : Zsqrtd d) :
    toQsqrtdHom d z = toQsqrtd z := rfl

theorem toQsqrtdHom_injective (d : ℤ) : Function.Injective (toQsqrtdHom d) := by
  intro x y hxy
  ext
  · simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.re hxy
  · simpa [toQsqrtdHom] using congrArg QuadraticAlgebra.im hxy

def halfInt (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  ⟨(a' : ℚ) / 2, (b' : ℚ) / 2⟩

theorem halfInt_mem_range_toQsqrtdHom_iff_even_even (d a' b' : ℤ) :
    (∃ z : Zsqrtd d, toQsqrtdHom d z = halfInt (d := d) a' b') ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · rintro ⟨z, hz⟩
    have hm : (a' : ℚ) / 2 = z.re := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.re hz.symm
    have hn : (b' : ℚ) / 2 = z.im := by
      simpa [toQsqrtdHom, halfInt] using congrArg QuadraticAlgebra.im hz.symm
    refine ⟨?_, ?_⟩
    · refine ⟨z.re, ?_⟩
      have hq : (a' : ℚ) = 2 * z.re := by nlinarith [hm]
      exact_mod_cast hq
    · refine ⟨z.im, ?_⟩
      have hq : (b' : ℚ) = 2 * z.im := by nlinarith [hn]
      exact_mod_cast hq
  · rintro ⟨ha, hb⟩
    rcases ha with ⟨m, hm⟩
    rcases hb with ⟨n, hn⟩
    refine ⟨⟨m, n⟩, ?_⟩
    ext <;> simp [toQsqrtdHom, halfInt, hm, hn]
end Zsqrtd
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers

abbrev halfInt (d : ℤ) (a' b' : ℤ) : Qsqrtd (d : ℚ) :=
  Zsqrtd.halfInt (d := d) a' b'

abbrev omegaHalf (d : ℤ) : Qsqrtd (d : ℚ) := halfInt d 1 1

@[simp] theorem halfInt_re (d a' b' : ℤ) :
    (halfInt d a' b').re = (a' : ℚ) / 2 := rfl

@[simp] theorem halfInt_im (d a' b' : ℤ) :
    (halfInt d a' b').im = (b' : ℚ) / 2 := rfl

theorem norm_halfInt (d a' b' : ℤ) :
    Qsqrtd.norm (halfInt d a' b') = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := by
  simp [halfInt, Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

end RingOfIntegers
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers
namespace TraceNorm

namespace Qsqrtd

theorem add_star_eq_trace_image {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    x + star x =
      algebraMap ℚ (Qsqrtd (d : ℚ)) (Algebra.trace ℚ (Qsqrtd (d : ℚ)) x) := by
  ext
  · simp [Qsqrtd.trace_eq_re_add_re_star, star]
  · simp [star]

theorem norm_image_eq_mul_star {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x) = x * star x := by
  simpa [Qsqrtd.norm, mul_comm] using
    (QuadraticAlgebra.algebraMap_norm_eq_mul_star (a := (d : ℚ)) (b := (0 : ℚ)) x)

end Qsqrtd

private lemma isIntegral_star {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd (Qsqrtd (d : ℚ))) hx

theorem norm_eq_sqr_minus_d_sqr {d : ℤ} (x : Qsqrtd (d : ℚ)) :
    Qsqrtd.norm x = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := by
  simp [Qsqrtd.norm, QuadraticAlgebra.norm]
  ring

private lemma isIntegral_trace_image {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Algebra.trace ℚ (Qsqrtd d) x)) := by
  simpa [Qsqrtd.add_star_eq_trace_image x] using hx.add (isIntegral_star hx)

private lemma isIntegral_trace {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (Algebra.trace ℚ (Qsqrtd d) x) :=
  (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
    (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 (isIntegral_trace_image hx)

lemma exists_int_trace {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' : ℤ, (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x := by
  obtain ⟨a', ha'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1
    (isIntegral_trace hx)
  exact ⟨a', by simpa using ha'⟩

private lemma isIntegral_norm_image {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (algebraMap ℚ (Qsqrtd (d : ℚ)) (Qsqrtd.norm x)) := by
  simpa [Qsqrtd.norm_image_eq_mul_star x] using hx.mul (isIntegral_star hx)

private lemma isIntegral_norm {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    IsIntegral ℤ (Qsqrtd.norm x) :=
  (isIntegral_algHom_iff (algebraMap ℚ (Qsqrtd (d : ℚ))).toIntAlgHom
    (algebraMap ℚ (Qsqrtd (d : ℚ))).injective).1 (isIntegral_norm_image hx)

lemma exists_int_norm {d : ℤ} {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ n' : ℤ, (n' : ℚ) = Qsqrtd.norm x := by
  obtain ⟨n', hn'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1
    (isIntegral_norm hx)
  exact ⟨n', by simpa using hn'⟩

lemma re_eq_half_trace_int {d : ℤ} {x : Qsqrtd (d : ℚ)} {a' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x) :
    x.re = (a' : ℚ) / 2 := by
  nlinarith [show 2 * x.re = (a' : ℚ) by
    calc
      2 * x.re = Algebra.trace ℚ (Qsqrtd d) x := (Qsqrtd.trace_eq_two_re x).symm
      _ = (a' : ℚ) := ha'trace.symm]

lemma isIntegral_of_sq_int {q : ℚ} {k : ℤ} (hq2 : q ^ 2 = (k : ℚ)) :
    IsIntegral ℤ q := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C k,
    Polynomial.monic_X_pow_sub_C (R := ℤ) (n := 2) k (by decide), ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
  simp [hq2]

private lemma double_im_sq_mul_eq
    (d : ℤ) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (d : ℚ) * (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) := by
  have hre : x.re = (a' : ℚ) / 2 := re_eq_half_trace_int ha'trace
  have hnorm' :
      (n' : ℚ) = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by
    calc
      (n' : ℚ) = Qsqrtd.norm x := hn'norm
      _ = x.re ^ 2 - (d : ℚ) * x.im ^ 2 := norm_eq_sqr_minus_d_sqr x
      _ = ((a' : ℚ) / 2) ^ 2 - (d : ℚ) * x.im ^ 2 := by simp [hre]
  have haux : (a' : ℚ) ^ 2 - 4 * (n' : ℚ) = 4 * (d : ℚ) * x.im ^ 2 := by
    nlinarith [hnorm']
  have hmcast : ((a' ^ 2 - 4 * n' : ℤ) : ℚ) = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by
    norm_cast
  calc
    (d : ℚ) * (2 * x.im) ^ 2 = 4 * (d : ℚ) * x.im ^ 2 := by ring
    _ = (a' : ℚ) ^ 2 - 4 * (n' : ℚ) := by linarith [haux]
    _ = (a' ^ 2 - 4 * n' : ℤ) := hmcast.symm

private lemma double_im_sq_eq_ratio
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) := by
  calc
    (2 * x.im) ^ 2 = ((d : ℚ) * (2 * x.im) ^ 2) / (d : ℚ) := by field_simp [hd0Q]
    _ = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) := by
      simp [double_im_sq_mul_eq d ha'trace hn'norm]

private lemma isSquare_trace_norm_ratio
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    IsSquare ((a' ^ 2 - 4 * n' : ℤ) / (d : ℚ)) :=
  ⟨2 * x.im, by simpa [pow_two] using (double_im_sq_eq_ratio d hd0Q ha'trace hn'norm).symm⟩

private lemma dvd_trace_norm_delta
    (d : ℤ) (hd0 : d ≠ 0) (hd_sf : Squarefree d) (hd0Q : (d : ℚ) ≠ 0)
    {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    d ∣ (a' ^ 2 - 4 * n') :=
  int_dvd_of_ratio_square (a' ^ 2 - 4 * n') d hd0 hd_sf
    (isSquare_trace_norm_ratio d hd0Q ha'trace hn'norm)

private lemma double_im_sq_eq_int
    (d : ℤ) (hd0Q : (d : ℚ) ≠ 0) {x : Qsqrtd (d : ℚ)} {a' n' k : ℤ}
    (hk : a' ^ 2 - 4 * n' = d * k)
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (2 * x.im) ^ 2 = (k : ℚ) := by
  have hmk : ((a' ^ 2 - 4 * n' : ℤ) : ℚ) = (d : ℚ) * k := by
    exact_mod_cast hk
  calc
    (2 * x.im) ^ 2 = (a' ^ 2 - 4 * n' : ℤ) / (d : ℚ) :=
      double_im_sq_eq_ratio d hd0Q ha'trace hn'norm
    _ = ((d : ℚ) * k) / (d : ℚ) := by simp [hmk]
    _ = (k : ℚ) := by field_simp [hd0Q]

private lemma exists_int_of_isIntegral_rat {q : ℚ} (hq : IsIntegral ℤ q) :
    ∃ b' : ℤ, (b' : ℚ) = q := by
  obtain ⟨b', hb'⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  exact ⟨b', by simpa using hb'⟩

private lemma im_eq_half_of_double_im_eq {d : ℤ} {x : Qsqrtd (d : ℚ)} {b' : ℤ}
    (hb' : (b' : ℚ) = 2 * x.im) :
    x.im = (b' : ℚ) / 2 := by
  nlinarith [hb']

lemma exists_int_double_im
    (d : ℤ) (hd_sf : Squarefree d) {x : Qsqrtd (d : ℚ)} {a' n' : ℤ}
    (ha'trace : (a' : ℚ) = Algebra.trace ℚ (Qsqrtd d) x)
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    ∃ b' : ℤ, x.im = (b' : ℚ) / 2 := by
  have hd0 : d ≠ 0 := hd_sf.ne_zero
  have hd0Q : (d : ℚ) ≠ 0 := by
    exact_mod_cast hd0
  rcases dvd_trace_norm_delta d hd0 hd_sf hd0Q ha'trace hn'norm with ⟨k, hk⟩
  rcases exists_int_of_isIntegral_rat
      (isIntegral_of_sq_int (double_im_sq_eq_int d hd0Q hk ha'trace hn'norm)) with
    ⟨b', hb'⟩
  exact ⟨b', im_eq_half_of_double_im_eq hb'⟩

lemma dvd_four_sub_sq_of_norm_eq_int
    (a' b' d n' : ℤ)
    (hnorm :
      (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ))) :
    (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) :=
  (Rat.den_div_intCast_eq_one_iff (a' ^ 2 - d * b' ^ 2) 4 (by norm_num)).1 <| by
    rw [← hnorm]
    simp

end TraceNorm
end RingOfIntegers
end QuadraticNumberFields
end

section
namespace QuadraticNumberFields
namespace RingOfIntegers

open scoped NumberField

section RingOfIntegersEquiv

noncomputable def ringOfIntegers_equiv_of_integralClosure
    (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 K ≃+* R :=
  NumberField.RingOfIntegers.equiv (K := K) (R := R)

@[simp]
lemma ringOfIntegers_equiv_of_integralClosure_apply
    {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K]
    (α : 𝓞 K) :
    algebraMap R K (ringOfIntegers_equiv_of_integralClosure K R α) = (algebraMap (𝓞 K) K) α := by
  change algebraMap R K ((IsIntegralClosure.equiv ℤ R K (𝓞 K)).symm α) =
    algebraMap (𝓞 K) K α
  have key := IsIntegralClosure.algebraMap_equiv ℤ R K (𝓞 K)
    ((IsIntegralClosure.equiv ℤ R K (𝓞 K)).symm α)
  rw [(IsIntegralClosure.equiv ℤ R K (𝓞 K)).apply_symm_apply α] at key
  exact key.symm

noncomputable def ringOfIntegers_equiv_of_embedding
    (K : Type*) [Field K]
    (R : Type*) [CommRing R]
    (φ : R →+* K)
    (h_inj : Function.Injective φ)
    (h_exists : ∀ x : K, IsIntegral ℤ x → ∃ z : R, φ z = x)
    (h_integral : ∀ z : R, IsIntegral ℤ (φ z)) :
    𝓞 K ≃+* R :=
  letI : Algebra R K := φ.toAlgebra
  letI : IsIntegralClosure R ℤ K :=
    { algebraMap_injective := by
        exact h_inj
      isIntegral_iff := by
        intro x
        refine ⟨fun hx => ?_, ?_⟩
        · rcases h_exists x hx with ⟨z, hz⟩
          exact ⟨z, hz⟩
        · rintro ⟨z, rfl⟩
          exact h_integral z }
  ringOfIntegers_equiv_of_integralClosure K R

lemma ringOfIntegers_equiv_of_embedding_apply
    {K : Type*} [Field K]
    {R : Type*} [CommRing R]
    (φ : R →+* K)
    (h_inj : Function.Injective φ)
    (h_exists : ∀ x : K, IsIntegral ℤ x → ∃ z : R, φ z = x)
    (h_integral : ∀ z : R, IsIntegral ℤ (φ z))
    (α : 𝓞 K) :
    φ (ringOfIntegers_equiv_of_embedding K R φ h_inj h_exists h_integral α) = (α : K) := by
  letI : Algebra R K := φ.toAlgebra
  letI : IsIntegralClosure R ℤ K :=
    { algebraMap_injective := h_inj
      isIntegral_iff := by
        intro x
        refine ⟨fun hx => ?_, ?_⟩
        · rcases h_exists x hx with ⟨z, hz⟩
          exact ⟨z, hz⟩
        · rintro ⟨z, rfl⟩
          exact h_integral z }
  change algebraMap R K _ = algebraMap (𝓞 K) K α
  exact ringOfIntegers_equiv_of_integralClosure_apply (R := R) α

end RingOfIntegersEquiv

theorem dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' := by
  rw [dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four d a' b' hd hd4,
    (Zsqrtd.halfInt_mem_range_toQsqrtdHom_iff_even_even d a' b').symm]

theorem exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (hdiv : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = Zsqrtd.halfInt (d := d) a' b' :=
  (dvd_four_sub_sq_iff_exists_zsqrtd_image_of_ne_one_mod_four d a' b' hd hd4).1 hdiv
private lemma isIntegral_of_intModel_image
    (R S : Type*) [CommRing R] [CommRing S]
    [Algebra.IsIntegral ℤ R] (φ : R →+* S) (z : R) :
    IsIntegral ℤ (φ z) :=
  map_isIntegral_int φ (Algebra.IsIntegral.isIntegral (R := ℤ) z)

lemma isIntegral_toQsqrtd (d : ℤ) (z : Zsqrtd d) :
    IsIntegral ℤ (Zsqrtd.toQsqrtdHom d z) :=
  isIntegral_of_intModel_image (Zsqrtd d) (Qsqrtd (d : ℚ)) (Zsqrtd.toQsqrtdHom d) z

private lemma eq_halfInt_of_re_im
    (d a' b' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hre : x.re = (a' : ℚ) / 2) (him : x.im = (b' : ℚ) / 2) :
    x = Zsqrtd.halfInt (d := d) a' b' := by
  ext <;> simp [Zsqrtd.halfInt, hre, him]

private lemma int_norm_eq_norm_halfInt
    (d a' b' n' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hxHalf : x = Zsqrtd.halfInt (d := d) a' b')
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (n' : ℚ) = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by
  calc
    (n' : ℚ) = Qsqrtd.norm x := hn'norm
    _ = Qsqrtd.norm (Zsqrtd.halfInt (d := d) a' b') := by simp [hxHalf]
    _ = (a' ^ 2 - (d : ℚ) * b' ^ 2) / 4 := norm_halfInt d a' b'
    _ = (((a' ^ 2 - d * b' ^ 2 : ℤ) : ℚ) / (4 : ℤ)) := by norm_num

private lemma dvd_four_sub_sq_of_int_norm_halfInt
    (d a' b' n' : ℤ) {x : Qsqrtd (d : ℚ)}
    (hxHalf : x = Zsqrtd.halfInt (d := d) a' b')
    (hn'norm : (n' : ℚ) = Qsqrtd.norm x) :
    (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) :=
  TraceNorm.dvd_four_sub_sq_of_norm_eq_int a' b' d n'
    (int_norm_eq_norm_halfInt d a' b' n' hxHalf hn'norm)

lemma exists_halfInt_with_div_four_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (_hd_ne : d ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ a' b' : ℤ,
      x = Zsqrtd.halfInt (d := d) a' b' ∧
      (4 : ℤ) ∣ (a' ^ 2 - d * b' ^ 2) := by
  obtain ⟨a', ha'trace⟩ := TraceNorm.exists_int_trace hx
  obtain ⟨n', hn'norm⟩ := TraceNorm.exists_int_norm hx
  obtain ⟨b', him⟩ := TraceNorm.exists_int_double_im d hd_sf ha'trace hn'norm
  have hxHalf : x = Zsqrtd.halfInt (d := d) a' b' :=
    eq_halfInt_of_re_im d a' b'
      (TraceNorm.re_eq_half_trace_int ha'trace) him
  exact ⟨a', b', hxHalf, dvd_four_sub_sq_of_int_norm_halfInt d a' b' n' hxHalf hn'norm⟩

private lemma exists_intModel_of_isIntegral
    (d : ℤ) (hd_sf : Squarefree d) (hd_ne : d ≠ 1)
    (R : Type*) [CommRing R]
    (φ : R →+* Qsqrtd (d : ℚ))
    (h_lift :
      ∀ a' b' : ℤ, 4 ∣ (a' ^ 2 - d * b' ^ 2) →
        ∃ z : R, φ z = Zsqrtd.halfInt (d := d) a' b')
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ z : R, φ z = x := by
  rcases exists_halfInt_with_div_four_of_isIntegral d hd_sf hd_ne (x := x) hx with
    ⟨a', b', hxHalf, hdiv⟩
  rcases h_lift a' b' hdiv with ⟨z, hz⟩
  exact ⟨z, by simpa [hxHalf] using hz⟩

lemma exists_zsqrtd_of_isIntegral_of_ne_one_mod_four
    (d : ℤ) (hd_sf : Squarefree d) (hd_ne : d ≠ 1) (hd4 : d % 4 ≠ 1)
    {x : Qsqrtd (d : ℚ)} (hx : IsIntegral ℤ x) :
    ∃ z : Zsqrtd d, Zsqrtd.toQsqrtdHom d z = x :=
  exists_intModel_of_isIntegral d hd_sf hd_ne (Zsqrtd d) (Zsqrtd.toQsqrtdHom d)
    (fun a' b' hdiv =>
      exists_zsqrtd_image_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd_sf hd4 hdiv)
    hx
end RingOfIntegers
end QuadraticNumberFields
end

section
open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

noncomputable def ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    𝓞 (Qsqrtd (d : ℚ)) ≃+* Zsqrtd d :=
  let hd_sf : Squarefree d := Fact.out
  let hd_ne : d ≠ 1 := Fact.out
  ringOfIntegers_equiv_of_embedding (Qsqrtd (d : ℚ)) (Zsqrtd d)
    (Zsqrtd.toQsqrtdHom d)
    (Zsqrtd.toQsqrtdHom_injective d)
    (fun _ hx => exists_zsqrtd_of_isIntegral_of_ne_one_mod_four d hd_sf hd_ne hd4 hx)
    (fun z => isIntegral_toQsqrtd d z)

end SquarefreeIntegerParameter

end RingOfIntegers
end QuadraticNumberFields
end

section
open scoped NumberField
namespace QuadraticNumberFields.RingOfIntegers

open Module

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

def ringEquivToIntAlgEquiv {R S : Type*} [CommRing R] [Algebra ℤ R]
    [CommRing S] [Algebra ℤ S] (e : R ≃+* S) : R ≃ₐ[ℤ] S :=
  AlgEquiv.ofRingEquiv (f := e) fun n => by
    simp only [eq_intCast, map_intCast]

end QuadraticNumberFields.RingOfIntegers
end

section
open scoped NumberField

namespace QuadraticNumberFields
namespace RingOfIntegers

theorem discr_zsqrtd_basis (d : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis d 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd d)) = 4 * d := by
  rw [QuadraticAlgebra.discr_basis_int]
  ring
section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

theorem discr_of_mod_four_ne_one (hd4 : d % 4 ≠ 1) :
    NumberField.discr (Qsqrtd (d : ℚ)) = 4 * d := by
  let e := ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let f : Zsqrtd d ≃ₐ[ℤ] 𝓞 (Qsqrtd (d : ℚ)) :=
    ringEquivToIntAlgEquiv e.symm
  let b' : Module.Basis (Fin 2) ℤ (𝓞 (Qsqrtd (d : ℚ))) :=
    (QuadraticAlgebra.basis d 0).map f.toLinearEquiv
  rw [← NumberField.discr_eq_discr (Qsqrtd (d : ℚ)) b']
  change Algebra.discr ℤ (⇑f ∘ ⇑(QuadraticAlgebra.basis d 0)) = 4 * d
  rw [← Algebra.discr_eq_discr_of_algEquiv _ f]
  exact discr_zsqrtd_basis d

end SquarefreeIntegerParameter

end RingOfIntegers
end QuadraticNumberFields
end

section

namespace Qsqrtd
section InternalLemmas

variable {d : ℤ} [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

instance : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two (d : ℚ) 0

theorem embedding_omega_sq
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    v.embedding QuadraticAlgebra.omega ^ 2 = ((d : ℚ) : ℂ) := by
  rw [sq, ← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp [Algebra.smul_def]

private theorem embedding_omega_sq_re
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    (v.embedding QuadraticAlgebra.omega).re ^ 2 -
    (v.embedding QuadraticAlgebra.omega).im ^ 2 = (d : ℝ) := by
  have := congr_arg Complex.re (embedding_omega_sq v)
  simp [sq, Complex.mul_re] at this; linarith

private theorem embedding_omega_sq_im
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    2 * (v.embedding QuadraticAlgebra.omega).re *
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have := congr_arg Complex.im (embedding_omega_sq v)
  simp [sq, Complex.mul_im] at this; linarith

private theorem embedding_omega_im_eq_zero
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ)))
    (hd : 0 < d) :
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have hre := embedding_omega_sq_re v
  have him := embedding_omega_sq_im v
  rcases mul_eq_zero.mp him with h | h
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · rw [h] at hre; simp at hre
      nlinarith [sq_nonneg (v.embedding QuadraticAlgebra.omega).im,
                 (show (d : ℝ) > 0 from by exact_mod_cast hd)]
  · exact h

private theorem conjugate_embedding_eq
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ)))
    (hω_im : (v.embedding QuadraticAlgebra.omega).im = 0) :
    NumberField.ComplexEmbedding.conjugate v.embedding = v.embedding := by
  rw [← @RingHom.toRatAlgHom_toRingHom (Qsqrtd (d : ℚ)) ℂ _ _ _ _
    (NumberField.ComplexEmbedding.conjugate v.embedding),
    ← @RingHom.toRatAlgHom_toRingHom (Qsqrtd (d : ℚ)) ℂ _ _ _ _
    v.embedding]
  congr 1
  apply QuadraticAlgebra.algHom_ext
  change (NumberField.ComplexEmbedding.conjugate v.embedding).toRatAlgHom
    QuadraticAlgebra.omega = v.embedding.toRatAlgHom QuadraticAlgebra.omega
  simp only [RingHom.toRatAlgHom_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.mpr hω_im

end InternalLemmas

section InfinitePlaceClassification

variable (d : ℤ) [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

theorem isTotallyReal (hd : 0 < d) :
    NumberField.IsTotallyReal (Qsqrtd (d : ℚ)) := {
    isReal := fun v => by
      rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
      simpa using conjugate_embedding_eq v (embedding_omega_im_eq_zero v hd)
  }

theorem nrComplexPlaces_eq_zero_of_pos (hd : 0 < d) :
    NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) = 0 := by
  haveI := isTotallyReal d hd
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (Qsqrtd (d : ℚ))

end InfinitePlaceClassification

end Qsqrtd
end

end
open NumberField Ideal
namespace SmallPrimes1140
noncomputable section
lemma of_le_same {K : Type} [Field K] [NumberField K] {I J:Ideal (𝓞 K)}
    (ij:I≤J) (h:I.absNorm=J.absNorm) (nz:J.absNorm≠0) : I=J := by
  obtain ⟨D,e⟩ := Ideal.dvd_iff_le.mpr ij
  have eq : J.absNorm * D.absNorm=J.absNorm*1 := by simpa only [e,map_mul,mul_one] using h
  have one : D.absNorm=1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero nz) eq
  simpa [Ideal.absNorm_eq_one_iff.mp one] using e

def bridge (d:ℤ) : QuadraticAlgebra ℤ d 0 ≃+* _root_.Zsqrtd d where
  toFun z := ⟨z.re,z.im⟩
  invFun z := ⟨z.re,z.im⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' x y := by
    apply _root_.Zsqrtd.ext
    · change x.re*y.re+d*x.im*y.im=_
      rfl
    · change x.re*y.im+x.im*y.re+0*x.im*y.im=_
      simp only [_root_.Zsqrtd.im_mul]; ring

set_option maxHeartbeats 1200000 in
lemma small_principal (n:ℕ) (hn:n.Prime) (res:n%4=3) (y:ℕ) (shape:2*n+2=(4*y)^2)
    (nonsq:∀ p:ℕ, p.Prime → p≠2 → p^2≤2*n → ∀ a:ZMod p,2*a^2≠(n:ZMod p)) :
    IsPrincipalIdealRing (_root_.Zsqrtd (2*(n:ℤ))) := by
  classical
  let d:ℤ := 2*n
  have he : n≠2 := by omega
  have sf : Squarefree (2*n) := (Nat.squarefree_mul (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))).mpr ⟨Nat.prime_two.squarefree,hn.squarefree⟩
  letI : Fact (Squarefree d) := ⟨by dsimp [d]; exact_mod_cast (Int.squarefree_natCast.mpr sf)⟩
  letI : Fact (d≠1) := ⟨by dsimp [d]; omega⟩
  have dpos : 0<d := by dsimp [d]; omega
  have modfour : d%4≠1 := by dsimp [d]; omega
  let K := Qsqrtd (d:ℚ)
  let e := QuadraticNumberFields.RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d modfour
  let j : QuadraticAlgebra ℤ d 0 ≃ₐ[ℤ] 𝓞 K := QuadraticNumberFields.RingOfIntegers.ringEquivToIntAlgEquiv e.symm
  let w : QuadraticAlgebra ℤ d 0 := ⟨0,1⟩
  have ws : w^2=(d:QuadraticAlgebra ℤ d 0) := by
    ext <;> simp [w,pow_two]
  let t:𝓞 K := j w
  have ts : t^2=(d:𝓞 K) := by simpa only [map_pow,map_intCast] using congrArg j ws
  have rk := Qsqrtd.finrank_ratAlgebra_eq_two (d:ℚ)
  letI : IsPrincipalIdealRing (𝓞 K) := by
    apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    intro I hI bound
    let P:Ideal (𝓞 K) := I.val
    have nz : P≠⊥ := nonZeroDivisors.coe_ne_zero I
    letI : P.IsMaximal := hI.isMaximal nz
    change (P.absNorm:ℝ) ≤ _ at bound
    rw [show NumberField.InfinitePlace.nrComplexPlaces K=0 from Qsqrtd.nrComplexPlaces_eq_zero_of_pos d dpos,rk,
      show NumberField.discr K=4*d from QuadraticNumberFields.RingOfIntegers.discr_of_mod_four_ne_one d modfour] at bound
    have dd : (0:ℝ)≤d := by exact_mod_cast dpos.le
    norm_num [abs_of_nonneg dd,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)] at bound
    have small : P.absNorm^2≤2*n := by
      have := Real.sq_sqrt dd
      have h : (P.absNorm:ℝ)^2≤d := by nlinarith [Nat.cast_nonneg (α:=ℝ) P.absNorm,Real.sqrt_nonneg (d:ℝ)]
      dsimp [d] at h
      exact_mod_cast h
    have pnz : P.absNorm≠0 := fun z => nz (Ideal.absNorm_eq_zero_iff.mp z)
    obtain ⟨p,i,ipos,pm,hp,hi⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    have le : span {(p:𝓞 K)}≤P := (span_singleton_le_iff_mem _).2 pm
    have size : (span {(p:𝓞 K)}).absNorm=p^2 := by rw [absNorm_span_natCast,NumberField.RingOfIntegers.rank,rk]
    have dvd : P.absNorm ∣ p^2 := size ▸ Ideal.absNorm_dvd_absNorm_of_le le
    obtain ⟨k,hk,hk'⟩ := (Nat.dvd_prime_pow hp).mp dvd
    interval_cases k
    · exact (hI.ne_top (Ideal.absNorm_eq_one_iff.mp (by simpa using hk'))).elim
    · have norm : P.absNorm=p := by simpa using hk'
      have qq := (Ideal.absNorm_ne_zero_iff P).mp pnz
      letI := Fintype.ofFinite (𝓞 K ⧸ P)
      let u := ZMod.ringEquivOfPrime (𝓞 K ⧸ P) hp (by rw [←Nat.card_eq_fintype_card]; exact norm)
      let f := u.symm.toRingHom.comp (Ideal.Quotient.mk P)
      have r : f t ^ 2=2*(n:ZMod p) := by
        rw [←map_pow,ts,map_intCast]; simp [d]
      by_cases two : p=2
      · rcases two with rfl
        have ft : f t=0 := by simpa only [show (2:ZMod 2)=0 from rfl,zero_mul,pow_eq_zero_iff (by decide : 2≠0)] using r
        let v:𝓞 K := (4*y:ℕ)+t
        have vm : v∈P := by
          apply Ideal.Quotient.eq_zero_iff_mem.mp
          apply u.symm.injective
          change f v=u.symm 0
          change f (((4*y:ℕ):𝓞 K)+t)=_
          rw [map_add,map_natCast,ft,map_zero,Nat.cast_mul,Nat.cast_ofNat,show (4:ZMod 2)=0 from rfl,zero_mul,add_zero]
        have nelem : Algebra.norm ℤ v=2 := by
          let x : QuadraticAlgebra ℤ d 0 := (4*y:ℕ)+w
          have jx : j x=v := by simp only [x,v,t,map_add,map_natCast]
          rw [←jx,Algebra.norm_eq_of_algEquiv j, Algebra.norm_eq_matrix_det (QuadraticAlgebra.basis d 0),QuadraticAlgebra.leftMulMatrix_eq,Matrix.det_fin_two]
          have hs : 2*(n:ℤ)+2=(4*(y:ℤ))^2 := by exact_mod_cast shape
          simp [x,w,d,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat] <;> nlinarith
        have en : (Ideal.span {v}).absNorm=P.absNorm := by rw [Ideal.absNorm_span_singleton,nelem,norm]; decide
        exact ⟨v,(of_le_same ((Ideal.span_singleton_le_iff_mem _).mpr vm) en pnz).symm⟩
      · letI : Fact p.Prime := ⟨hp⟩
        have ht : (2:ZMod p)≠0 := by
          change ((2:ℕ):ZMod p)≠0
          rw [Ne,ZMod.natCast_eq_zero_iff]
          exact (fun z : p∣2 => two ((Nat.dvd_prime Nat.prime_two).mp z |>.resolve_left hp.ne_one))
        apply False.elim (nonsq p hp two (norm ▸ small) ((f t)/2) ?_)
        field_simp
        linear_combination r
    · exact ⟨(p:𝓞 K),(of_le_same le (size.trans hk'.symm) pnz).symm⟩
  exact IsPrincipalIdealRing.of_surjective (e.trans (bridge d)) (by exact (e.trans (bridge d)).surjective)
end
end SmallPrimes1140

theorem OMA.solution : OMA.R_Erdos1140_erdos_1140_variants_at_most_one_exception_R1_H2_R1.H1 := by
  rintro n hn res ⟨y,hy⟩ sieve
  exact SmallPrimes1140.small_principal n hn res y hy sieve
