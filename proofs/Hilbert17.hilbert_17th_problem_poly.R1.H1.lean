import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1
import Mathlib

-- Credit: @marcusbuffett
/-! Hilbert’s negative classification follows from the homogenized Motzkin sextic and the Choi–Lam quartic. For the quartic, extract the quadratic part of a putative square on each of eight lines. -/
open Finset MvPolynomial
open scoped Polynomial
namespace OMA.HilbertForms
def quartic {R : Type*} [CommRing R] (a b c d : R) : R := a^2*b^2+b^2*c^2+c^2*a^2+d^4-4*a*b*c*d
lemma quartic_nonneg (a b c d : ℝ) : 0 ≤ quartic a b c d := by
  have h : 0 ≤ quartic |a| |b| |c| |d| := by
    dsimp [quartic]
    nlinarith [sq_nonneg (|a| * |b| - |d| ^ 2), sq_nonneg (|b| * |c|-|c| * |a|),
      mul_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg b)) (sq_nonneg (|c|-|d|))]
  have hp := le_abs_self (a*b*c*d)
  simp only [abs_mul] at hp
  simp only [quartic, sq_abs, show |d| ^ 4 = d^4 by rw [show 4 = 2*2 by decide,pow_mul,pow_mul,sq_abs]] at h ⊢
  linarith

noncomputable def line (v : Fin 4 → ℝ) : MvPolynomial (Fin 4) ℝ →+* ℝ[X] :=
  eval₂Hom Polynomial.C (fun i ↦ Polynomial.C (v i) * Polynomial.X)
noncomputable def quadraticCoeff (v : Fin 4 → ℝ) (p : MvPolynomial (Fin 4) ℝ) : ℝ := (line v p).coeff 2

lemma monLine (v : Fin 4 → ℝ) (u : Fin 4 →₀ ℕ) (a : ℝ) :
    quadraticCoeff v (monomial u a) =
    if 2 = u 0 + u 1 + u 2 + u 3 then a*v 0^(u 0)*v 1^(u 1)*v 2^(u 2)*v 3^(u 3) else 0 := by
  unfold quadraticCoeff line
  rw [eval₂Hom_monomial,Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_four]
  have eq : Polynomial.C a *
      ((Polynomial.C (v 0)*Polynomial.X)^(u 0) * (Polynomial.C (v 1)*Polynomial.X)^(u 1) *
      (Polynomial.C (v 2)*Polynomial.X)^(u 2) * (Polynomial.C (v 3)*Polynomial.X)^(u 3)) =
      Polynomial.C (a*v 0^(u 0)*v 1^(u 1)*v 2^(u 2)*v 3^(u 3)) * Polynomial.X^(u 0+u 1+u 2+u 3) := by
    simp only [map_mul,map_pow,mul_pow,pow_add]; ring
  rw [eq,Polynomial.coeff_C_mul_X_pow]

private lemma vecFour2 {A : Type*} (a b c d : A) : (![a,b,c,d] : Fin 4 → A) 2 = c := rfl
private lemma vecFour3 {A : Type*} (a b c d : A) : (![a,b,c,d] : Fin 4 → A) 3 = d := rfl
private lemma degcases (a b c d : ℕ) (h : 2 = a+b+c+d) : (a=2 ∧ b=0 ∧ c=0 ∧ d=0) ∨ (a=0 ∧ b=2 ∧ c=0 ∧ d=0) ∨
        (a=0 ∧ b=0 ∧ c=2 ∧ d=0) ∨ (a=0 ∧ b=0 ∧ c=0 ∧ d=2) ∨
        (a=1 ∧ b=1 ∧ c=0 ∧ d=0) ∨ (a=1 ∧ b=0 ∧ c=1 ∧ d=0) ∨
        (a=1 ∧ b=0 ∧ c=0 ∧ d=1) ∨ (a=0 ∧ b=1 ∧ c=1 ∧ d=0) ∨
        (a=0 ∧ b=1 ∧ c=0 ∧ d=1) ∨ (a=0 ∧ b=0 ∧ c=1 ∧ d=1)  := by
  have ck : ∀ a b c d : Fin 3, 2 = a.val+b.val+c.val+d.val → (a.val=2 ∧ b.val=0 ∧ c.val=0 ∧ d.val=0) ∨ (a.val=0 ∧ b.val=2 ∧ c.val=0 ∧ d.val=0) ∨
        (a.val=0 ∧ b.val=0 ∧ c.val=2 ∧ d.val=0) ∨ (a.val=0 ∧ b.val=0 ∧ c.val=0 ∧ d.val=2) ∨
        (a.val=1 ∧ b.val=1 ∧ c.val=0 ∧ d.val=0) ∨ (a.val=1 ∧ b.val=0 ∧ c.val=1 ∧ d.val=0) ∨
        (a.val=1 ∧ b.val=0 ∧ c.val=0 ∧ d.val=1) ∨ (a.val=0 ∧ b.val=1 ∧ c.val=1 ∧ d.val=0) ∨
        (a.val=0 ∧ b.val=1 ∧ c.val=0 ∧ d.val=1) ∨ (a.val=0 ∧ b.val=0 ∧ c.val=1 ∧ d.val=1) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
  exact ck ⟨a,by omega⟩ ⟨b,by omega⟩ ⟨c,by omega⟩ ⟨d,by omega⟩ h

set_option maxHeartbeats 800000 in
lemma polarization (p : MvPolynomial (Fin 4) ℝ) :
    quadraticCoeff ![1,1,1,1] p + quadraticCoeff ![1,-1,-1,1] p +
      quadraticCoeff ![-1,1,-1,1] p + quadraticCoeff ![-1,-1,1,1] p =
    4*(quadraticCoeff ![1,0,0,0] p + quadraticCoeff ![0,1,0,0] p +
      quadraticCoeff ![0,0,1,0] p + quadraticCoeff ![0,0,0,1] p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [quadraticCoeff,map_add,Polynomial.coeff_add] at *
    linarith
  | monomial u r =>
    simp only [monLine]
    by_cases h : 2 = u 0 + u 1 + u 2 + u 3
    · simp only [if_pos h]
      generalize h0 : u 0 = a at *; generalize h1 : u 1 = b at *
      generalize h2 : u 2 = c at *; generalize h3 : u 3 = d at *
      have cases := degcases a b c d h
      rcases cases with h|h|h|h|h|h|h|h|h|h <;> rcases h with ⟨rfl,rfl,rfl,rfl⟩ <;> norm_num [vecFour2,vecFour3,Matrix.cons_val] <;> ring
    · simp [h]

lemma zero_of_squares {m : ℕ} (g : Fin m → ℝ) (h : ∑ i, (g i)^2 = 0) (i : Fin m) : g i = 0 := by
  have h0 := (sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg (g j))).mp h i (mem_univ _)
  simpa using h0

lemma quartic_squares {m : ℕ} (g : Fin m → ℝ[X]) (c : ℝ)
    (h : ∑ i, (g i)^2 = Polynomial.C c * Polynomial.X^4) :
    ∑ i, ((g i).coeff 2)^2 = c := by
  have h0 := congrArg (fun p : ℝ[X] ↦ p.coeff 0) h
  simp only [Polynomial.finsetSum_coeff, sq, Polynomial.mul_coeff_zero,Polynomial.coeff_C_mul_X_pow] at h0
  norm_num at h0
  have z0 (i) : (g i).coeff 0 = 0 := zero_of_squares _ (by simpa [sq] using h0) i
  have h2 := congrArg (fun p : ℝ[X] ↦ p.coeff 2) h
  simp only [Polynomial.finsetSum_coeff,sq,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_C_mul_X_pow] at h2
  norm_num [sum_range_succ,z0] at h2
  have z1 (i) : (g i).coeff 1 = 0 := zero_of_squares _ (by simpa [sq] using h2) i
  have h4 := congrArg (fun p : ℝ[X] ↦ p.coeff 4) h
  simp only [Polynomial.finsetSum_coeff,sq,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_C_mul_X_pow] at h4
  simpa [sq,sum_range_succ,z0,z1] using h4

lemma quartic_not_sos (m : ℕ) (g : Fin m → MvPolynomial (Fin 4) ℝ)
    (eq : quartic (X 0) (X 1) (X 2) (X 3) = ∑ i, (g i)^2) : False := by
  have lineeq (v : Fin 4 → ℝ) : ∑ i, (quadraticCoeff v (g i))^2 = quartic (v 0) (v 1) (v 2) (v 3) := by
    apply quartic_squares (fun i ↦ line v (g i))
    simp_rw [← map_pow (line v)]
    rw [← map_sum, ← eq]
    simp [quartic,line,map_add,map_mul,map_pow,Polynomial.C_ofNat]
    ring
  have z (v : Fin 4 → ℝ) (hv : quartic (v 0) (v 1) (v 2) (v 3) = 0) (i : Fin m) :
      quadraticCoeff v (g i) = 0 := zero_of_squares _ ((lineeq v).trans hv) i
  have e (i : Fin m) : quadraticCoeff ![0,0,0,1] (g i) = 0 := by
    have h := polarization (g i)
    rw [z _ (by norm_num [quartic,vecFour2,vecFour3,Matrix.cons_val]) i,z _ (by norm_num [quartic,vecFour2,vecFour3,Matrix.cons_val]) i,z _ (by norm_num [quartic,vecFour2,vecFour3,Matrix.cons_val]) i,
        z _ (by norm_num [quartic,vecFour2,vecFour3,Matrix.cons_val]) i,z _ (by norm_num [quartic,vecFour2,vecFour3,Matrix.cons_val]) i,z _ (by norm_num [quartic,vecFour2,vecFour3,Matrix.cons_val]) i,
        z _ (by norm_num [quartic,vecFour2,vecFour3,Matrix.cons_val]) i] at h
    linarith
  have hh := lineeq ![0,0,0,1]
  norm_num [e,quartic,vecFour2,vecFour3,Matrix.cons_val] at hh
end OMA.HilbertForms

-- Motzkin nonsquareness adapted from the merged proof by @philipsaint.
namespace OMA.H17

open MvPolynomial

/-- The exponent vector `x^a y^b`. -/
noncomputable def e (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma e_zero (a b : ℕ) : e a b 0 = a := by simp [e]

@[simp] lemma e_one (a b : ℕ) : e a b 1 = b := by simp [e]

lemma ext2 {β γ : Fin 2 →₀ ℕ} (h0 : β 0 = γ 0) (h1 : β 1 = γ 1) : β = γ := by
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma eq_e (β : Fin 2 →₀ ℕ) : β = e (β 0) (β 1) := ext2 (by simp) (by simp)

lemma e_inj (a b c d : ℕ) : e a b = e c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) h
    have h1 := congrArg (fun x : Fin 2 →₀ ℕ => x 1) h
    simp only [e_zero, e_one] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma e_eq_zero (a b : ℕ) : (0 : Fin 2 →₀ ℕ) = e a b ↔ 0 = a ∧ 0 = b := by
  rw [show (0 : Fin 2 →₀ ℕ) = e 0 0 from ext2 (by simp) (by simp), e_inj]

lemma f_coeff (a b : ℕ) : coeff (e a b) Hilbert17.f
    = (if 4 = a ∧ 2 = b then (1 : ℝ) else 0) + (if 2 = a ∧ 4 = b then 1 else 0)
      - (if 2 = a ∧ 2 = b then 3 else 0) + (if 0 = a ∧ 0 = b then 1 else 0) := by
  have h1 : (X 0 ^ 4 * X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) = monomial (e 4 2) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]; rfl
  have h2 : (X 0 ^ 2 * X 1 ^ 4 : MvPolynomial (Fin 2) ℝ) = monomial (e 2 4) 1 := by
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]; rfl
  have h3 : (3 * X 0 ^ 2 * X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) = monomial (e 2 2) 3 := by
    rw [mul_assoc, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul,
      show (3 : MvPolynomial (Fin 2) ℝ) = C 3 from (map_ofNat C 3).symm, C_mul_monomial, mul_one]
    rfl
  unfold Hilbert17.f
  rw [h1, h2, h3, coeff_add, coeff_sub, coeff_add, coeff_monomial, coeff_monomial, coeff_monomial,
    coeff_one]
  simp only [e_inj, e_eq_zero]

/-- The linear weight `p * a + q * b` of an exponent vector. -/
def ell (p q : ℤ) (β : Fin 2 →₀ ℕ) : ℤ := p * (β 0 : ℤ) + q * (β 1 : ℤ)

lemma ell_add (p q : ℤ) (β γ : Fin 2 →₀ ℕ) : ell p q (β + γ) = ell p q β + ell p q γ := by
  simp only [ell, Finsupp.add_apply]
  push_cast
  ring

lemma vertex {n : ℕ} (S : Fin n → MvPolynomial (Fin 2) ℝ) (p q : ℤ) (hq : q ≠ 0)
    (μ : Fin 2 →₀ ℕ)
    (h1 : ∀ i, ∀ β ∈ (S i).support, ell p q β ≤ ell p q μ)
    (h2 : ∀ i, ∀ β ∈ (S i).support, ell p q β = ell p q μ → β 0 ≤ μ 0) :
    coeff (μ + μ) (∑ i, S i ^ 2) = ∑ i, (coeff μ (S i)) ^ 2 := by
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two, coeff_mul, pow_two]
  apply Finset.sum_eq_single (μ, μ)
  · rintro ⟨β, γ⟩ hbg hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hbg
    by_contra hprod
    have hβ : β ∈ (S i).support := by
      rw [mem_support_iff]; intro h; exact hprod (by simp [h])
    have hγ : γ ∈ (S i).support := by
      rw [mem_support_iff]; intro h; exact hprod (by simp [h])
    have he := congrArg (ell p q) hbg
    rw [ell_add, ell_add] at he
    have b1 := h1 i β hβ
    have g1 := h1 i γ hγ
    have eβ : ell p q β = ell p q μ := by linarith
    have eγ : ell p q γ = ell p q μ := by linarith
    have b2 := h2 i β hβ eβ
    have g2 := h2 i γ hγ eγ
    have e0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hbg
    simp only [Finsupp.add_apply] at e0
    have β0 : β 0 = μ 0 := by omega
    have γ0 : γ 0 = μ 0 := by omega
    have β1 : β 1 = μ 1 := by
      simp only [ell] at eβ
      rw [β0] at eβ
      have h3 : q * ((β 1 : ℤ) - μ 1) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hq
      · exact_mod_cast (by linarith : (β 1 : ℤ) = μ 1)
    have γ1 : γ 1 = μ 1 := by
      simp only [ell] at eγ
      rw [γ0] at eγ
      have h3 : q * ((γ 1 : ℤ) - μ 1) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hq
      · exact_mod_cast (by linarith : (γ 1 : ℤ) = μ 1)
    exact hne (by rw [ext2 β0 β1, ext2 γ0 γ1])
  · intro h
    refine absurd ?_ h
    rw [Finset.HasAntidiagonal.mem_antidiagonal]

/-- The exponents `μ` with `2 μ` in the support of the Motzkin polynomial. -/
lemma half_support {μ : Fin 2 →₀ ℕ} (h : coeff (μ + μ) Hilbert17.f ≠ 0) :
    (μ 0 = 2 ∧ μ 1 = 1) ∨ (μ 0 = 1 ∧ μ 1 = 2) ∨ (μ 0 = 1 ∧ μ 1 = 1) ∨ (μ 0 = 0 ∧ μ 1 = 0) := by
  rw [eq_e (μ + μ), f_coeff] at h
  by_contra hc
  apply h
  have a0 : (μ + μ) 0 = μ 0 + μ 0 := Finsupp.add_apply _ _ _
  have a1 : (μ + μ) 1 = μ 1 + μ 1 := Finsupp.add_apply _ _ _
  rw [if_neg (by rw [a0, a1]; omega), if_neg (by rw [a0, a1]; omega),
    if_neg (by rw [a0, a1]; omega), if_neg (by rw [a0, a1]; omega)]
  norm_num

lemma top {n : ℕ} (S : Fin n → MvPolynomial (Fin 2) ℝ) (hS : Hilbert17.f = ∑ i, S i ^ 2)
    (p q : ℤ) (hq : q ≠ 0) :
    ∃ a b : ℕ, ((a = 2 ∧ b = 1) ∨ (a = 1 ∧ b = 2) ∨ (a = 1 ∧ b = 1) ∨ (a = 0 ∧ b = 0)) ∧
      ∀ i, ∀ β ∈ (S i).support, ell p q β ≤ p * a + q * b := by
  classical
  by_cases hU : ∃ i, ((S i).support).Nonempty
  · have hUne : (Finset.univ.biUnion fun i => (S i).support).Nonempty := by
      obtain ⟨i, β, hβ⟩ := hU
      exact ⟨β, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hβ⟩⟩
    obtain ⟨μ0, hμ0, hmax0⟩ := Finset.exists_max_image _ (ell p q) hUne
    have hU'ne : ((Finset.univ.biUnion fun i => (S i).support).filter
        fun β => ell p q β = ell p q μ0).Nonempty :=
      ⟨μ0, Finset.mem_filter.mpr ⟨hμ0, rfl⟩⟩
    obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image _ (fun β : Fin 2 →₀ ℕ => β 0) hU'ne
    rw [Finset.mem_filter] at hμ
    have h1 : ∀ i, ∀ β ∈ (S i).support, ell p q β ≤ ell p q μ := by
      intro i β hβ
      rw [hμ.2]
      exact hmax0 β (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hβ⟩)
    have h2 : ∀ i, ∀ β ∈ (S i).support, ell p q β = ell p q μ → β 0 ≤ μ 0 := by
      intro i β hβ he
      exact hmax β (Finset.mem_filter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hβ⟩, he.trans hμ.2⟩)
    have hv := vertex S p q hq μ h1 h2
    rw [← hS] at hv
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hμ.1
    have hpos : 0 < ∑ i, (coeff μ (S i)) ^ 2 := by
      apply Finset.sum_pos'
      · intro i _
        positivity
      · have hj' := mem_support_iff.mp hj
        exact ⟨j, Finset.mem_univ _, by positivity⟩
    have hne : coeff (μ + μ) Hilbert17.f ≠ 0 := by
      rw [hv]
      exact hpos.ne'
    refine ⟨μ 0, μ 1, half_support hne, ?_⟩
    intro i β hβ
    exact h1 i β hβ
  · refine ⟨0, 0, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)), ?_⟩
    intro i β hβ
    exact absurd ⟨i, β, hβ⟩ hU

end OMA.H17

open MvPolynomial OMA.H17 in
theorem OMA.HilbertForms.motzkin_not_sos : type_of% @Hilbert17.f_not_sum_of_squares := by
  rintro ⟨n, -, S, hS⟩
  have key : ∀ i, ∀ β ∈ (S i).support,
      β 0 + β 1 ≤ 3 ∧ β 0 ≤ 2 * β 1 ∧ β 1 ≤ 2 * β 0 := by
    intro i β hβ
    obtain ⟨a1, b1, hab1, h1⟩ := top S hS 1 1 (by norm_num)
    obtain ⟨a2, b2, hab2, h2⟩ := top S hS 1 (-2) (by norm_num)
    obtain ⟨a3, b3, hab3, h3⟩ := top S hS (-2) 1 (by norm_num)
    have k1 := h1 i β hβ
    have k2 := h2 i β hβ
    have k3 := h3 i β hβ
    simp only [ell] at k1 k2 k3
    omega
  have hc : coeff (e 1 1 + e 1 1) (∑ i, S i ^ 2) = ∑ i, (coeff (e 1 1) (S i)) ^ 2 := by
    rw [coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_two, coeff_mul, pow_two]
    apply Finset.sum_eq_single (e 1 1, e 1 1)
    · rintro ⟨β, γ⟩ hbg hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hbg
      by_contra hprod
      have hβ : β ∈ (S i).support := by
        rw [mem_support_iff]; intro h; exact hprod (by simp [h])
      have hγ : γ ∈ (S i).support := by
        rw [mem_support_iff]; intro h; exact hprod (by simp [h])
      have kβ := key i β hβ
      have kγ := key i γ hγ
      have e0 := congrArg (fun x : Fin 2 →₀ ℕ => x 0) hbg
      have e1 := congrArg (fun x : Fin 2 →₀ ℕ => x 1) hbg
      simp only [Finsupp.add_apply, e_zero, e_one] at e0 e1
      have hβe : β = e 1 1 := ext2 (by rw [e_zero]; omega) (by rw [e_one]; omega)
      have hγe : γ = e 1 1 := ext2 (by rw [e_zero]; omega) (by rw [e_one]; omega)
      exact hne (by rw [hβe, hγe])
    · intro h
      refine absurd ?_ h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
  rw [← hS, eq_e (e 1 1 + e 1 1), f_coeff] at hc
  simp only [Finsupp.add_apply, e_zero, e_one] at hc
  norm_num at hc
  have hnn : 0 ≤ ∑ i, (coeff (e 1 1) (S i)) ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  linarith


namespace OMA.HilbertForms
open MvPolynomial Finset Hilbert17
lemma restrictForms {n m d : ℕ} (hm : 0 < m) (hn : m ≤ n) (H : Hilbert17thProblemHomogenousPoly n d) :
    Hilbert17thProblemHomogenousPoly m d := by
  let e := Fin.castLE hn
  let r (i : Fin n) : Fin m := if h : i.val < m then ⟨i.val,h⟩ else ⟨0,hm⟩
  have re : r ∘ e = id := by funext i; simp [r,e,i.isLt]
  intro p hp hpos
  obtain ⟨k,g,eq⟩ := H (rename e p) hp.rename_isHomogeneous (fun x ↦ by rw [eval_rename]; exact hpos _)
  refine ⟨k,fun i ↦ rename r (g i), ?_⟩
  have he := congrArg (rename r : MvPolynomial (Fin n) ℝ → MvPolynomial (Fin m) ℝ) eq
  simpa only [rename_rename,re,rename_id_apply,map_sum,map_pow] using he

def mot {R : Type*} [CommRing R] (a b c : R) : R := a^4*b^2+a^2*b^4-3*(a^2*b^2*c^2)+c^6

lemma mot_nonneg (a b c : ℝ) : 0 ≤ mot a b c := by
  by_cases h : c=0
  · subst c; simp [mot]; positivity
  · have hp := Hilbert17.f_nonneg (a/c) (b/c)
    simp [Hilbert17.f] at hp
    have he : mot a b c = c^6 *((a/c)^4*(b/c)^2 + (a/c)^2*(b/c)^4 - 3*(a/c)^2*(b/c)^2+1) := by
      unfold mot; field_simp <;> ring
    rw [he]
    exact mul_nonneg (by positivity) hp

lemma notSextic {d : ℕ} (hd : 3 ≤ d) (H : Hilbert17thProblemHomogenousPoly 3 d) : False := by
  let x := X (R := ℝ) (0 : Fin 3)
  let y := X (R := ℝ) (1 : Fin 3)
  let z := X (R := ℝ) (2 : Fin 3)
  let F := mot x y z * z^(2*(d-3))
  have hh : (mot x y z).IsHomogeneous 6 := by
    have a : (x^4*y^2).IsHomogeneous 6 := (isHomogeneous_X_pow (R := ℝ) _ _).mul (isHomogeneous_X_pow (R := ℝ) _ _)
    have b : (x^2*y^4).IsHomogeneous 6 := (isHomogeneous_X_pow (R := ℝ) _ _).mul (isHomogeneous_X_pow (R := ℝ) _ _)
    have c : (x^2*y^2*z^2).IsHomogeneous 6 := ((isHomogeneous_X_pow (R := ℝ) _ _).mul (isHomogeneous_X_pow (R := ℝ) _ _)).mul (isHomogeneous_X_pow (R := ℝ) _ _)
    have h3 : (3*(x^2*y^2*z^2)).IsHomogeneous 6 := by simpa only [map_ofNat] using c.C_mul (3:ℝ)
    exact (((a.add b).sub h3).add (isHomogeneous_X_pow (R := ℝ) _ _))
  have homo : F.IsHomogeneous (2*d) := by
    have he : 2*d = 6+2*(d-3) := by omega
    rw [he]; exact hh.mul (isHomogeneous_X_pow (R := ℝ) _ _)
  have pos (w : Fin 3 → ℝ) : 0 ≤ eval w F := by
    simp only [F,mot,x,y,z,map_mul,map_add,map_sub,map_pow,eval_X,eval_ofNat]
    exact mul_nonneg (mot_nonneg _ _ _) (by rw [mul_comm 2 _,pow_mul]; positivity)
  obtain ⟨m,g,he⟩ := H F homo pos
  let ev := aeval (R := ℝ) ![X (R := ℝ) (0 : Fin 2),X 1,1]
  have hF : ev F = Hilbert17.f := by simp [ev,F,mot,x,y,z,Hilbert17.f,map_ofNat]; ring
  have he' : Hilbert17.f = ∑ i, (ev (g i))^2 := by rw [← hF,he,map_sum]; simp
  apply motzkin_not_sos
  exact ⟨m+1,Nat.succ_pos _,Fin.cons 0 (fun i ↦ ev (g i)),by simpa [Fin.sum_univ_succ] using he'⟩

lemma notQuartic (H : Hilbert17thProblemHomogenousPoly 4 2) : False := by
  let x := X (R := ℝ) (0 : Fin 4)
  let y := X (R := ℝ) (1 : Fin 4)
  let z := X (R := ℝ) (2 : Fin 4)
  let w := X (R := ℝ) (3 : Fin 4)
  let F := quartic x y z w
  have homo : F.IsHomogeneous 4 := by
    have a : (x^2*y^2).IsHomogeneous 4 := (isHomogeneous_X_pow (R := ℝ) _ _).mul (isHomogeneous_X_pow (R := ℝ) _ _)
    have b : (y^2*z^2).IsHomogeneous 4 := (isHomogeneous_X_pow (R := ℝ) _ _).mul (isHomogeneous_X_pow (R := ℝ) _ _)
    have c : (z^2*x^2).IsHomogeneous 4 := (isHomogeneous_X_pow (R := ℝ) _ _).mul (isHomogeneous_X_pow (R := ℝ) _ _)
    have t : (x*y*z*w).IsHomogeneous 4 :=
      (((isHomogeneous_X _ _).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X _ _)).mul (isHomogeneous_X _ _)
    have tw : (4*x*y*z*w).IsHomogeneous 4 := by simpa only [map_ofNat,mul_assoc] using t.C_mul (4:ℝ)
    exact ((((a.add b).add c).add (isHomogeneous_X_pow (R := ℝ) _ _)).sub tw)
  have pos (v : Fin 4 → ℝ) : 0 ≤ eval v F := by
    simpa [F,quartic,x,y,z,w] using quartic_nonneg (v 0) (v 1) (v 2) (v 3)
  obtain ⟨m,g,hg⟩ := H F homo pos
  exact quartic_not_sos m g hg
end OMA.HilbertForms
open OMA.HilbertForms in
theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1.H1 := by
  intro n d hn hd H
  by_contra! h
  by_cases h3 : 3 ≤ d
  · exact notSextic h3 (restrictForms (by decide : 0 < 3) (by omega) H)
  · have d2 : d = 2 := by omega
    subst d
    exact notQuartic (restrictForms (by decide : 0 < 4) (by omega) H)

