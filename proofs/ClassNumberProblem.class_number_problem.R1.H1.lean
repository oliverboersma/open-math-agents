import OMAReductions.R_ClassNumberProblem_class_number_problem_R1
import Mathlib

/-!
# A class-number-one criterion for a real quadratic field

Minkowski's bound reduces the class group to small prime ideals. A root of
the integral generator's polynomial modulo a prime gives a norm-prime ideal.
In the converse direction the norm equation makes a prime above each such
rational prime principal, and an inert rational prime is itself a generator.

The half-integral-coordinate argument for the ring of integers adapts
Genbox's proof of the non-one-mod-four quadratic discriminant on this board.
For the classical generation criterion see Louboutin, Mollin and Williams,
Canadian Journal of Mathematics 44 (1992), Theorem 2.7.
-/
-- Credit: @sobrien032

namespace ClassNumberScout

/-- The two discriminant conventions give the required integral coefficient. -/
theorem coefficient_exact (d : ℤ) :
    let D := if d % 4 = 1 then d else 4 * d
    let s := D % 2
    s ^ 2 - D = 4 * ((s ^ 2 - D) / 4) := by
  dsimp only
  split_ifs with hd
  · have hs : d % 2 = 1 := by omega
    rw [hs]
    norm_num
    omega
  · have hs : 4 * d % 2 = 0 := by omega
    rw [hs]
    norm_num
    omega

private theorem norm_identity (D s a b : ℤ)
    (hc : s ^ 2 - D = 4 * ((s ^ 2 - D) / 4)) :
    (2 * a + s * b) ^ 2 - D * b ^ 2 =
      4 * (a ^ 2 + s * a * b + (s ^ 2 - D) / 4 * b ^ 2) := by
  linear_combination b ^ 2 * hc

/-- Norm ±q in the basis (1, (s+√D)/2) is equivalent to the board's
parity-restricted square equation, in both discriminant cases. -/
theorem norm_coordinates_iff (d q : ℤ) :
    let D := if d % 4 = 1 then d else 4 * d
    let s := D % 2
    let c := (s ^ 2 - D) / 4
    (∃ a b : ℤ, (a ^ 2 + s*a*b + c*b^2 = q ∨ a ^ 2 + s*a*b + c*b^2 = -q)) ↔
      ∃ x y : ℤ, (x - s*y) % 2 = 0 ∧ (x^2 - D*y^2 = 4*q ∨ x^2 - D*y^2 = -4*q) := by
  intro D s c
  have hc : s ^ 2 - D = 4 * c := coefficient_exact d
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨2*a+s*b, b, by omega, ?_⟩
    have hnorm := norm_identity D s a b hc
    change (2*a+s*b)^2 - D*b^2 = 4*(a^2+s*a*b+c*b^2) at hnorm
    rcases h with h | h
    · exact Or.inl (by linarith only [hnorm, h])
    · exact Or.inr (by linarith only [hnorm, h])
  · rintro ⟨x, y, hpar, h⟩
    let a := (x - s*y)/2
    have hxy : 2*a+s*y = x := by dsimp [a]; omega
    have hnorm := norm_identity D s a y hc
    change (2*a+s*y)^2 - D*y^2 = 4*(a^2+s*a*y+c*y^2) at hnorm
    rw [hxy] at hnorm
    refine ⟨a, y, ?_⟩
    rcases h with h | h
    · exact Or.inl (by linarith only [hnorm, h])
    · exact Or.inr (by linarith only [hnorm, h])

/-- The divisibility test in H1 is a root of the integral-basis polynomial
in the residue ring. This holds even without primality of the modulus. -/
theorem residue_root_iff (q : ℕ) (s c : ℤ) :
    (∃ t : ℤ, (q : ℤ) ∣ t^2 - s*t + c) ↔
      ∃ u : ZMod q, u^2 - (s : ZMod q)*u + (c : ZMod q) = 0 := by
  constructor
  · rintro ⟨t, h⟩
    refine ⟨(t : ZMod q), ?_⟩
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr h
  · rintro ⟨u, h⟩
    obtain ⟨t, rfl⟩ := ZMod.intCast_surjective u
    refine ⟨t, (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ?_⟩
    simpa using h

end ClassNumberScout

/- The argument that integral elements have half-integral coordinates and the
non-one mod-four parity argument are adapted from @Genbox's board proof of
QuadraticAlgebra.discr_rat_of_not_modEq_one. -/

namespace ClassNumberOrder
open QuadraticAlgebra NumberField
noncomputable section

abbrev K (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0
abbrev D (d : ℤ) := if d % 4 = 1 then d else 4*d
abbrev S (d : ℤ) := D d % 2
abbrev C (d : ℤ) := ((S d)^2 - D d)/4
abbrev ZOrder (d : ℤ) := QuadraticAlgebra ℤ (-(C d)) (S d)
variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]
lemma norm_eq (z : (QuadraticAlgebra ℚ (d : ℚ) 0)) : (z * star z) = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (z.re ^ 2 - d * z.im ^ 2) := by
  have h := (QuadraticAlgebra.algebraMap_norm_eq_mul_star z).symm
  rw [h, QuadraticAlgebra.norm_def]; congr 1; ring

lemma add_star_eq (z : (QuadraticAlgebra ℚ (d : ℚ) 0)) : (z + star z) = algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) (2 * z.re) := by
  have h := (QuadraticAlgebra.algebraMap_trace_eq_add_star (z := z)).symm
  rw [h, QuadraticAlgebra.trace_def]; congr 1; ring

lemma int_of_integral {q : ℚ} (h : IsIntegral ℤ (algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0) q)) : ∃ n : ℤ, (n : ℚ) = q := by
  rw [isIntegral_algebraMap_iff (algebraMap ℚ (QuadraticAlgebra ℚ (d : ℚ) 0)).injective] at h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨n, by simpa using hn⟩

omit [Fact (d ≠ 1)] in
lemma int_of_mul_sq {q : ℚ} {k : ℤ} (h : (d : ℚ) * q ^ 2 = k) : ∃ n : ℤ, (n : ℚ) = q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have h1 : (d : ℚ) * (q.num : ℚ) ^ 2 = k * (q.den : ℚ) ^ 2 := by
    rw [← Rat.num_div_den q] at h
    field_simp at h
    linear_combination h
  have h2 : d * q.num ^ 2 = k * (q.den : ℤ) ^ 2 := by exact_mod_cast h1
  have hc : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa [Int.gcd, Nat.coprime_comm] using q.reduced
  have h3 : (q.den : ℤ) ^ 2 ∣ d * q.num ^ 2 := ⟨k, by rw [h2]; ring⟩
  have h4 : (q.den : ℤ) ^ 2 ∣ d := (hc.pow).dvd_of_dvd_mul_right h3
  have h5 : IsUnit (q.den : ℤ) := (Fact.out : Squarefree d) _ (by simpa [sq] using h4)
  have h6 : q.den = 1 := by
    rcases Int.isUnit_iff.mp h5 with h | h
    · exact_mod_cast h
    · have := q.den_pos; omega
  exact ⟨q.num, (Rat.den_eq_one_iff q).mp h6⟩

lemma two_dvd_of (A : ℤ) (h : (A : ZMod 4) = 0 ∨ (A : ZMod 4) = 2) : 2 ∣ A := by
  rcases h with h | h
  · rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h; omega
  · have : ((A - 2 : ℤ) : ZMod 4) = 0 := by push_cast; rw [h]; ring
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this; omega

lemma double_components (x : K d) (hx : IsIntegral ℤ x) :
    ∃ A B N : ℤ, (A:ℚ) = 2*x.re ∧ (B:ℚ) = 2*x.im ∧ A^2 - d*B^2 = 4*N := by
  have hs : IsIntegral ℤ (star x) := by
    exact hx.map (starRingEnd (QuadraticAlgebra ℚ (d : ℚ) 0)).toIntAlgHom
  obtain ⟨A, hA⟩ := int_of_integral (d := d) (q := 2 * x.re) (by rw [← add_star_eq]; exact hx.add hs)
  obtain ⟨N, hN⟩ := int_of_integral (d := d) (q := x.re ^ 2 - d * x.im ^ 2)
    (by rw [← norm_eq]; exact hx.mul hs)
  obtain ⟨B, hB⟩ := int_of_mul_sq (d := d) (q := 2 * x.im) (k := A ^ 2 - 4 * N)
    (by push_cast; rw [hA, hN]; ring)
  have hAB : A ^ 2 - d * B ^ 2 = 4 * N := by
    have : (A : ℚ) ^ 2 - d * B ^ 2 = 4 * N := by rw [hA, hB, hN]; ring
    exact_mod_cast this
  exact ⟨A, B, N, hA, hB, hAB⟩

lemma components (hd₄ : ¬ d ≡ 1 [ZMOD 4]) (x : (QuadraticAlgebra ℚ (d : ℚ) 0)) (hx : IsIntegral ℤ x) :
    ∃ m n : ℤ, x = ⟨m, n⟩ := by
  obtain ⟨A,B,N,hA,hB,hAB⟩ := double_components x hx
  have key : ∀ a b e : ZMod 4, e ≠ 1 → e ≠ 0 → a ^ 2 - e * b ^ 2 = 0 →
      (a = 0 ∨ a = 2) ∧ (b = 0 ∨ b = 2) := by decide
  have hd1 : (d : ZMod 4) ≠ 1 := by
    intro h; apply hd₄
    rw [show (1 : ZMod 4) = ((1 : ℤ) : ZMod 4) by simp, ZMod.intCast_eq_intCast_iff] at h
    exact h
  have hd0 : (d : ZMod 4) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have := (Fact.out : Squarefree d) 2 (by simpa using h)
    rcases Int.isUnit_iff.mp this with h | h <;> omega
  have h4 : ((A ^ 2 - d * B ^ 2 : ℤ) : ZMod 4) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact ⟨N, by push_cast; linarith⟩
  push_cast at h4
  obtain ⟨hA2, hB2⟩ := key _ _ _ hd1 hd0 h4
  obtain ⟨a, rfl⟩ := two_dvd_of A hA2
  obtain ⟨b, rfl⟩ := two_dvd_of B hB2
  refine ⟨a, b, ?_⟩
  ext
  · push_cast at hA; linarith
  · push_cast at hB; linarith

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private theorem discr_one (h : d % 4 = 1) : D d = d ∧ S d = 1 ∧ 4*C d = 1-d := by
  have hs : d%2=1 := by omega
  simp [D,S,C,h,hs]
  omega

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private theorem discr_other (h : d % 4 ≠ 1) : D d = 4*d ∧ S d = 0 ∧ C d = -d := by
  have hs : (4*d)%2=0 := by omega
  simp [D,S,C,h,hs]
  omega

def generator (d : ℤ) : K d := if d%4=1 then ⟨1/2,1/2⟩ else ⟨0,1⟩

private theorem gen_rel (d : ℤ) :
    generator d * generator d = (-(C d)) • (1 : K d) + (S d) • generator d := by
  by_cases h : d%4=1
  · obtain ⟨_,hs,hc⟩ := discr_one h
    have hcQ : 4*(C d:ℚ) = 1-d := by exact_mod_cast hc
    ext <;> norm_num [generator,h,hs]
    linarith
  · obtain ⟨_,hs,hc⟩ := discr_other h
    ext <;> simp [generator,h,hs,hc]

def fieldMap (d : ℤ) : ZOrder d →ₐ[ℤ] K d :=
  QuadraticAlgebra.lift ⟨generator d,gen_rel d⟩

def intMap (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ZOrder d →ₐ[ℤ] 𝓞 (K d) :=
  (fieldMap d).codRestrict (integralClosure ℤ (K d)) fun z =>
    (Algebra.IsIntegral.isIntegral (R := ℤ) z).map (fieldMap d)

private theorem intMap_val (z : ZOrder d) : ((intMap d z : 𝓞 (K d)) : K d) =
    z.re • 1 + z.im • generator d := rfl

private theorem coord_odd (h : d%4=1) (z : ZOrder d) :
    ((intMap d z : 𝓞 (K d)) : K d) = ⟨(z.re:ℚ)+(z.im:ℚ)/2, (z.im:ℚ)/2⟩ := by
  rw [intMap_val]
  ext <;> simp [generator,h] <;> ring

private theorem coord_other (h : d%4≠1) (z : ZOrder d) :
    ((intMap d z : 𝓞 (K d)) : K d) = ⟨(z.re:ℚ), (z.im:ℚ)⟩ := by
  rw [intMap_val]
  ext <;> simp [generator,h]

private theorem intMap_inj : Function.Injective (intMap d) := by
  intro x y hxy
  have hval := congrArg (fun w : 𝓞 (K d) => (w : K d)) hxy
  by_cases h : d%4=1
  · simp only [coord_odd h, QuadraticAlgebra.mk.injEq] at hval
    obtain ⟨h₁,h₂⟩ := hval
    have hi : (x.im:ℚ) = y.im := by linarith
    ext
    · exact_mod_cast (show (x.re:ℚ)=y.re by linarith)
    · exact_mod_cast hi
  · simp only [coord_other h, QuadraticAlgebra.mk.injEq] at hval
    exact QuadraticAlgebra.ext (by exact_mod_cast hval.1) (by exact_mod_cast hval.2)

private theorem intMap_surj : Function.Surjective (intMap d) := by
  intro z
  by_cases h : d%4=1
  · obtain ⟨A,B,N,hA,hB,hAB⟩ := double_components (z : K d) z.2
    have e : (A:ZMod 2)^2 - (d:ZMod 2)*(B:ZMod 2)^2 = 0 := by
      have := congrArg (fun n : ℤ => (n:ZMod 2)) hAB
      push_cast at this
      simpa [show (4 : ZMod 2) = 0 by decide] using this
    have hd2 : (d:ZMod 2)=1 := by
      rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by simp, ZMod.intCast_eq_intCast_iff]
      change d % 2 = 1 % 2
      omega
    rw [hd2,one_mul] at e
    have eqmod : (A:ZMod 2)=(B:ZMod 2) :=
      (show ∀ a b : ZMod 2, a^2-b^2=0 → a=b by decide) _ _ e
    rw [ZMod.intCast_eq_intCast_iff] at eqmod
    change A % 2 = B % 2 at eqmod
    have he : 2*((A-B)/2)=A-B := by omega
    have heQ : 2*(((A-B)/2:ℤ):ℚ)=(A:ℚ)-B := by exact_mod_cast he
    refine ⟨⟨(A-B)/2,B⟩, RingOfIntegers.ext ?_⟩
    rw [coord_odd h]
    ext <;> dsimp <;> linarith
  · have hd : ¬ d ≡ 1 [ZMOD 4] := fun hd => h hd
    obtain ⟨a,b,hab⟩ := components hd (z : K d) z.2
    exact ⟨⟨a,b⟩, RingOfIntegers.ext ((coord_other h _).trans hab.symm)⟩

def equiv (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ZOrder d ≃ₐ[ℤ] 𝓞 (K d) :=
  AlgEquiv.ofBijective (intMap d) ⟨intMap_inj,intMap_surj⟩

end
end ClassNumberOrder

/- The discriminant of the real quadratic field in the integral basis. -/

namespace ClassNumberOrder
open QuadraticAlgebra NumberField

private theorem basis_0 (a b : ℤ) : QuadraticAlgebra.basis a b 0 = 1 := by
  ext <;> simp [QuadraticAlgebra.basis]

private theorem basis_1 (a b : ℤ) : QuadraticAlgebra.basis a b 1 = ω := by
  ext <;> simp [QuadraticAlgebra.basis]

private theorem quadratic_trace {a b : ℤ} (z : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) z = 2*z.re + b*z.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis _ _), Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, basis_0, basis_1]
  ring

private theorem integral_discr (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = b^2 + 4*a := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, quadratic_trace, basis_0, basis_1]
  ring

theorem discr_eq (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    NumberField.discr (K d) = D d := by
  let b := QuadraticAlgebra.basis (-(C d)) (S d)
  let e := equiv d
  rw [← NumberField.discr_eq_discr (K d) (b.map e.toLinearEquiv)]
  change Algebra.discr ℤ (e ∘ b) = D d
  rw [← Algebra.discr_eq_discr_of_algEquiv b e]
  rw [show Algebra.discr ℤ b = (S d)^2 + 4*(-C d) from integral_discr ..]
  by_cases h : d%4 = 1
  · have hs : d%2=1 := by omega
    simp [D,S,C,h,hs]
    omega
  · have hs : (4*d)%2=0 := by omega
    simp [D,S,C,h,hs]
    omega

end ClassNumberOrder

namespace ClassNumberWork
open NumberField NumberField.InfinitePlace Module

theorem no_complex_of_discr_pos {K : Type*} [Field K] [NumberField K]
    (hrank : finrank ℚ K = 2) (hdisc : 0 < discr K) : nrComplexPlaces K = 0 := by
  have hc := card_add_two_mul_card_eq_rank K
  rw [hrank] at hc
  by_contra h
  have hone : nrComplexPlaces K = 1 := by omega
  have hs := sign_discr K
  rw [hone, pow_one, Int.sign_eq_one_of_pos hdisc] at hs
  contradiction

theorem cut_of_discr {K : Type*} [Field K] [NumberField K] {D : ℤ}
    (hrank : finrank ℚ K = 2) (hdisc : discr K = D) (hD : 0 < D) :
    ∀ q : ℕ, q ≤ ⌊(4 / Real.pi) ^ nrComplexPlaces K *
      ((Nat.factorial (finrank ℚ K) : ℝ) / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K|)⌋₊ →
      4*(q:ℤ)^2 ≤ D := by
  have hreal := no_complex_of_discr_pos hrank (hdisc ▸ hD)
  intro q hq
  have hDr : 0 ≤ (D : ℝ) := by exact_mod_cast hD.le
  rw [hrank, hdisc, hreal] at hq
  norm_num [Nat.factorial, abs_of_nonneg hDr] at hq
  have hb := (Nat.le_floor_iff (by positivity)).mp hq
  have hbound : 2 * (q:ℝ) ≤ Real.sqrt D := by linarith
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ 2*(q:ℝ)) hbound
  rw [Real.mul_self_sqrt hDr] at hsq
  exact_mod_cast (show 4 * (q:ℝ)^2 ≤ (D:ℝ) by nlinarith only [hsq])

end ClassNumberWork

namespace ClassNumberField
open Polynomial NumberField
noncomputable section

private abbrev Quad (d : ℤ) := QuadraticAlgebra ℚ (d : ℚ) 0
private abbrev poly (d : ℤ) := X^2 - C (d : ℚ)

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

theorem irred : Irreducible (poly d) := by
  apply (X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two).2
  intro b
  simpa using (Fact.out (p := ∀ r : ℚ, r ^ 2 ≠ (d : ℚ) + 0 * r) b)

private def fieldEquiv [Fact (Irreducible (poly d))] :
    Quad d ≃ₐ[ℚ] AdjoinRoot (poly d) := by
  let f : Quad d →ₐ[ℚ] AdjoinRoot (poly d) :=
    QuadraticAlgebra.lift ⟨AdjoinRoot.root (poly d), by
      simp only [Algebra.smul_def, map_zero, zero_mul, add_zero, mul_one, ← sq]
      exact root_X_pow_sub_C_pow 2 (d : ℚ)⟩
  have dim : Module.finrank ℚ (Quad d) = Module.finrank ℚ (AdjoinRoot (poly d)) := by
    rw [QuadraticAlgebra.finrank_eq_two]
    change 2 = Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {poly d})
    rw [finrank_quotient_span_eq_natDegree, poly, natDegree_X_pow_sub_C]
  exact AlgEquiv.ofBijective f ⟨f.injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := f.toLinearMap) dim).mp f.injective⟩

theorem class_one_iff : ClassNumberProblem.IsClassNumberOne d ↔
    NumberField.classNumber (Quad d) = 1 := by
  have h := irred d
  let : Fact (Irreducible (poly d)) := ⟨h⟩
  let e := RingOfIntegers.mapRingEquiv (fieldEquiv d).toRingEquiv
  constructor
  · rintro ⟨_, hclass⟩
    have := NumberField.classNumber_eq_one_iff.mp hclass
    exact NumberField.classNumber_eq_one_iff.mpr
      (IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective)
  · intro hclass
    have := NumberField.classNumber_eq_one_iff.mp hclass
    exact ⟨h, NumberField.classNumber_eq_one_iff.mpr
      (IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective)⟩

end
end ClassNumberField

open scoped NumberField
namespace ClassNumberWork
open NumberField

variable {K : Type*} [Field K] [NumberField K] {s c : ℤ}

omit [NumberField K] in
theorem alg_norm_coordinates (e : 𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (-c) s) (z : 𝓞 K) :
    Algebra.norm ℤ z = (e z).re^2 + s*(e z).re*(e z).im + c*(e z).im^2 := by
  rw [← Algebra.norm_eq_of_algEquiv e z]
  change (DistribSMul.toLinearMap ℤ _ (e z)).det = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, QuadraticAlgebra.norm_def]
  ring

theorem form_of_classNumber_one (e : 𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (-c) s)
    (hc : NumberField.classNumber K = 1) {q : ℕ} (hq : q.Prime)
    (ht : ∃ t : ZMod q, t^2-(s : ZMod q)*t+(c : ZMod q)=0) :
    ∃ a b : ℤ, a^2+s*a*b+c*b^2=(q : ℤ) ∨ a^2+s*a*b+c*b^2=-(q : ℤ) := by
  obtain ⟨t, ht⟩ := ht
  let : Fact q.Prime := ⟨hq⟩
  have rt : t*t = (-c) • (1 : ZMod q) + s • t := by
    simp only [zsmul_eq_mul, Int.cast_neg, mul_one]
    linear_combination ht
  let f : 𝓞 K →ₐ[ℤ] ZMod q := (QuadraticAlgebra.lift ⟨t,rt⟩).comp e.toAlgHom
  let I := RingHom.ker f.toRingHom
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨u, rfl⟩ := ZMod.intCast_surjective w
    exact ⟨u, map_intCast f u⟩
  have hind : Ideal.absNorm I = q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective (f:=f.toRingHom) hf).toEquiv).trans (Nat.card_zmod q)
  have := NumberField.classNumber_eq_one_iff.mp hc
  obtain ⟨z, hz⟩ := IsPrincipalIdealRing.principal I
  rw [hz, Ideal.submodule_span_eq, Ideal.absNorm_span_singleton, alg_norm_coordinates e] at hind
  exact ⟨(e z).re,(e z).im,Int.natAbs_eq_natAbs_iff.mp (by simpa using hind)⟩

theorem principal_over_of_form (e : 𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (-c) s)
    {q : ℕ} (hq : q.Prime)
    (hrep : ∃ a b : ℤ, a^2+s*a*b+c*b^2=(q : ℤ) ∨ a^2+s*a*b+c*b^2=-(q : ℤ)) :
    ∃ P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 K), Submodule.IsPrincipal P := by
  obtain ⟨a,b,h⟩ := hrep
  let z := e.symm ⟨a,b⟩
  let P := Ideal.span {z}
  have hz : Algebra.norm ℤ z = a^2+s*a*b+c*b^2 := by
    rw [alg_norm_coordinates e z]
    simp [z]
  have hn : Ideal.absNorm P = q := by
    rw [show P = Ideal.span {z} from rfl, Ideal.absNorm_span_singleton, hz]
    rcases h with h|h <;> rw [h] <;> simp
  have hp : (Ideal.absNorm P).Prime := hn.symm ▸ hq
  refine ⟨P, ⟨Ideal.isPrime_of_irreducible_absNorm ((Nat.irreducible_iff_nat_prime _).mpr hp), ⟨?_⟩⟩, ?_⟩
  · simpa only [hn] using Ideal.span_singleton_absNorm hp
  · exact ⟨z,rfl⟩

end ClassNumberWork

open NumberField NumberField.InfinitePlace Ideal Module
open scoped NumberField QuadraticAlgebra

namespace ClassNumberIdeals

private def reduce (s c : ℤ) (q : ℕ) :
    QuadraticAlgebra ℤ (-c) s →+* QuadraticAlgebra (ZMod q) (-(c : ZMod q)) (s : ZMod q) where
  toFun z := ⟨z.re, z.im⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp
  map_mul' := by intro x y; ext <;> simp

private theorem span_q_eq_ker {K : Type*} [Field K] [NumberField K]
    (s c : ℤ) (q : ℕ) (e : 𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (-c) s) :
    span {(q : 𝓞 K)} = RingHom.ker ((reduce s c q).comp e.toRingHom) := by
  ext x
  rw [Ideal.mem_span_singleton, RingHom.mem_ker, RingHom.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩
    simp [reduce]
    rfl
  · intro hz
    have h₁ := congrArg QuadraticAlgebra.re hz
    have h₂ := congrArg QuadraticAlgebra.im hz
    change ((e x).re : ZMod q) = 0 at h₁
    change ((e x).im : ZMod q) = 0 at h₂
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h₁
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp h₂
    refine ⟨e.symm ⟨a,b⟩, e.injective ?_⟩
    rw [map_mul, map_natCast, e.apply_symm_apply]
    ext <;> simp [ha,hb]

private theorem span_q_prime_over {K : Type*} [Field K] [NumberField K]
    (s c : ℤ) (q : ℕ) (hq : q.Prime) (e : 𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (-c) s)
    (h : ¬ ∃ u : ZMod q, u^2 - (s : ZMod q)*u + (c : ZMod q) = 0) :
    span {(q : 𝓞 K)} ∈ primesOver (span {(q : ℤ)}) (𝓞 K) := by
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (∀ r : ZMod q, r^2 ≠ -(c : ZMod q) + (s : ZMod q) * r) :=
    ⟨fun r hr => h ⟨r, by linear_combination hr⟩⟩
  rw [span_q_eq_ker s c q e]
  constructor
  · exact RingHom.ker_isPrime _
  · rw [Ideal.liesOver_iff]
    ext t
    rw [Ideal.mem_span_singleton, Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply]
    change (q : ℤ) ∣ t ↔ (reduce s c q) (e (t : 𝓞 K)) = 0
    rw [map_intCast, map_intCast]
    change (q : ℤ) ∣ t ↔ (⟨(t : ZMod q), 0⟩ : QuadraticAlgebra (ZMod q) _ _) = 0
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro ht; simp [ht]; rfl
    · exact fun ht => congrArg QuadraticAlgebra.re ht

theorem reverse_of_order {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
    (s c D : ℤ) (e : 𝓞 K ≃ₐ[ℤ] QuadraticAlgebra ℤ (-c) s)
    (cut : ∀ q : ℕ, q ≤ ⌊(4 / Real.pi) ^ nrComplexPlaces K *
      ((Nat.factorial (finrank ℚ K) : ℝ) / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K|)⌋₊ →
      4*(q:ℤ)^2 ≤ D)
    (h : ∀ q : ℕ, q.Prime → 4*(q:ℤ)^2 ≤ D →
      (∃ u : ZMod q, u^2 - (s : ZMod q)*u + (c : ZMod q) = 0) →
      ∃ a b : ℤ, a^2+s*a*b+c*b^2 = q ∨ a^2+s*a*b+c*b^2 = -q) :
    classNumber K = 1 := by
  classical
  apply classNumber_eq_one_iff.mpr
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
  intro q hq hp
  by_cases hr : ∃ u : ZMod q, u^2 - (s : ZMod q)*u + (c : ZMod q) = 0
  · obtain ⟨P, hP, hprin⟩ := ClassNumberWork.principal_over_of_form e hp
      (h q hp (cut q (Finset.mem_Icc.mp hq).2) hr)
    exact ⟨P, hP, Or.inr hprin⟩
  · exact ⟨_, span_q_prime_over s c q hp e hr, Or.inr (by infer_instance)⟩

end ClassNumberIdeals

open ClassNumberOrder in
theorem OMA.solution : OMA.R_ClassNumberProblem_class_number_problem_R1.H1 := by
  intro d hd hpos
  let : Fact (Squarefree d) := ⟨hd⟩
  let : Fact (d ≠ 1) := ⟨by omega⟩
  rw [ClassNumberField.class_one_iff d]
  let e := (ClassNumberOrder.equiv d).symm
  have hD : 0 < D d := by unfold D; split <;> omega
  constructor
  · intro hc _ _ q hq _ ht
    apply (ClassNumberScout.norm_coordinates_iff d (q : ℤ)).mp
    apply ClassNumberWork.form_of_classNumber_one e hc hq
    exact (ClassNumberScout.residue_root_iff q (S d) (C d)).mp ht
  · intro h
    apply ClassNumberIdeals.reverse_of_order (S d) (C d) (D d) e
      (ClassNumberWork.cut_of_discr (QuadraticAlgebra.finrank_eq_two ..) (discr_eq d) hD)
    intro q hp hbound hroot
    apply (ClassNumberScout.norm_coordinates_iff d (q : ℤ)).mpr
    exact h q hp hbound ((ClassNumberScout.residue_root_iff q (S d) (C d)).mpr hroot)
