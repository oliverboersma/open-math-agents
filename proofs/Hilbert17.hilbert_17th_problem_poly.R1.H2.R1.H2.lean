import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1
import Mathlib
import Mathlib.Algebra.Polynomial.Homogenize

/-!
# Nonnegative ternary quartics with a real zero

Formalization by Hanan Beer, with Codex assistance.
This proves the real-zero auxiliary case of the classical Hilbert theorem:
every nonnegative homogeneous ternary quartic with a nonzero real zero is a
sum of squares of real polynomials.

The constructive argument follows Albrecht Pfister and Claus Scheiderer,
An elementary proof of Hilbert's theorem on ternary quartics,
https://arxiv.org/abs/1009.3144, Proposition 1.1 and Proposition 2.4.
Target reduction and the polynomial-to-quadratic-form bridge are by
@marcusbuffett, PR4945 of open-math-agents; this attribution is retained below.
The scalar leading-coefficient limit argument adapts Mathlib's
`discrim_le_zero`. All remaining algebraic and analytic infrastructure is Mathlib.
-/

/- Nonnegative real univariate polynomials as two squares, with degree bounds.
Formalization by Hanan Beer. The proof removes a positive quadratic factor, or
an even real-root factor, and uses the two-squares product identity. -/

namespace BinarySOS
open Polynomial Filter
open scoped Topology

lemma nonneg_quotient (p q : ℝ[X]) (a b : ℝ)
    (h : p = ((X-C a)^2 + (C b)^2)*q) (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∀ x : ℝ, 0 ≤ q.eval x := by
  have hne (x : ℝ) (hx : x ≠ a) : 0 ≤ q.eval x := by
    have hpos : 0 < (x-a)^2 + b^2 := add_pos_of_pos_of_nonneg
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hx)) (sq_nonneg b)
    have he := hp x
    rw [h] at he
    simp only [eval_mul, eval_add, eval_pow, eval_sub, eval_X, eval_C] at he
    exact nonneg_of_mul_nonneg_right he hpos
  intro x
  by_cases hx : x = a
  · subst x
    apply ge_of_tendsto (q.continuous.continuousAt.tendsto.mono_left
      (show 𝓝[≠] a ≤ 𝓝 a from inf_le_left))
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hne y (by simpa using hy)
  · exact hne x hx

lemma real_double_root (p : ℝ[X]) (a : ℝ) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (ha : p.eval a = 0) : (X-C a)^2 ∣ p := by
  have hmin : IsLocalMin (fun x : ℝ => p.eval x) a :=
    Filter.Eventually.of_forall (fun x => by simpa [ha] using hp x)
  have hd : p.derivative.eval a = 0 := (p.hasDerivAt a).deriv.symm.trans hmin.deriv_eq_zero
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr ha
  have hqa : q.eval a = 0 := by
    rw [hq] at hd
    simpa using hd
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr hqa
  refine ⟨r, ?_⟩
  rw [hq, hr]
  ring

lemma quadratic_degree (a b : ℝ) : ((X-C a)^2 + (C b)^2 : ℝ[X]).natDegree = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · simp

lemma factor_nonnegative (p : ℝ[X]) (hp0 : p ≠ 0) (hpdeg : 0 < p.natDegree)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) :
    ∃ a b : ℝ, ∃ q : ℝ[X], p = ((X-C a)^2 + (C b)^2)*q ∧
      (∀ x : ℝ, 0 ≤ q.eval x) ∧ q.natDegree + 2 = p.natDegree := by
  have hdeg : p.degree ≠ 0 := by
    intro h
    have hz : p.natDegree = 0 := natDegree_eq_of_degree_eq_some h
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero ℂ p hdeg
  have hdvd : ((X-C z.re)^2 + (C z.im)^2 : ℝ[X]) ∣ p := by
    by_cases hi : z.im = 0
    · have hr : p.eval z.re = 0 := by
        have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
        have hz' := hz
        rw [he] at hz'
        change p.aeval (algebraMap ℝ ℂ z.re) = 0 at hz'
        rw [aeval_algebraMap_apply_eq_algebraMap_eval] at hz'
        exact (algebraMap ℝ ℂ).injective (by simpa using hz')
      simpa [hi] using real_double_root p z.re hp hr
    · have h := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz hi
      have he : (X ^ 2 - C (2*z.re)*X + C (‖z‖^2) : ℝ[X]) =
          (X-C z.re)^2 + (C z.im)^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [map_add, map_mul, map_ofNat]
        ring
      rwa [he] at h
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨z.re, z.im, q, hq, nonneg_quotient p q _ _ hq hp, ?_⟩
  have hqn : q ≠ 0 := by intro he; simp [he] at hq; exact hp0 hq
  have hfn : ((X-C z.re)^2 + (C z.im)^2 : ℝ[X]) ≠ 0 := by
    intro he
    have := quadratic_degree z.re z.im
    simp [he] at this
  rw [hq, natDegree_mul hfn hqn, quadratic_degree]
  omega

end BinarySOS


/- Two-square degree induction for nonnegative real polynomials.
Formalization by Hanan Beer with Codex assistance. The step uses the classical
identity expressing a product of two sums of two squares as two squares. -/

namespace BinarySOSInduction
open Polynomial

lemma two_squares_of_quadratic_factor
    (factor : ∀ p : Polynomial ℝ, p ≠ 0 → 0 < p.natDegree →
      (∀ x : ℝ, 0 ≤ p.eval x) → ∃ a b : ℝ, ∃ q : Polynomial ℝ,
      p = ((X - C a)^2 + (C b)^2) * q ∧
        (∀ x : ℝ, 0 ≤ q.eval x) ∧ q.natDegree + 2 = p.natDegree) :
    ∀ (d : ℕ) (p : Polynomial ℝ), p.natDegree ≤ 2*d →
      (∀ x : ℝ, 0 ≤ p.eval x) → ∃ u v : Polynomial ℝ,
      p = u^2 + v^2 ∧ u.natDegree ≤ d ∧ v.natDegree ≤ d := by
  intro d
  induction d with
  | zero =>
      intro p hp hpos
      have hdeg : p.natDegree = 0 := by omega
      have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hc : 0 ≤ p.coeff 0 := by
          have hh := hpos 0
          rw [he, eval_C] at hh
          exact hh
      refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_, by simp, by simp⟩
      simp only [zero_pow (by decide : 2 ≠ 0), add_zero, ← map_pow]
      rw [Real.sq_sqrt hc]
      exact he
  | succ d ih =>
      intro p hp hpos
      by_cases hz : p.natDegree = 0
      · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hz
        have hc : 0 ≤ p.coeff 0 := by
          have hh := hpos 0
          rw [he, eval_C] at hh
          exact hh
        refine ⟨C (Real.sqrt (p.coeff 0)), 0, ?_, by simp, by simp⟩
        simp only [zero_pow (by decide : 2 ≠ 0), add_zero, ← map_pow]
        rw [Real.sq_sqrt hc]
        exact he
      · have hp0 : p ≠ 0 := by intro he; simp [he] at hz
        obtain ⟨a, b, q, hpq, hqpos, hqdeg⟩ := factor p hp0 (by omega) hpos
        obtain ⟨u, v, huv, hu, hv⟩ := ih q (by omega) hqpos
        refine ⟨(X - C a)*u - C b*v, (X - C a)*v + C b*u, ?_, ?_, ?_⟩
        · rw [hpq, huv]
          ring
        · apply (natDegree_sub_le _ _).trans
          apply max_le
          · apply natDegree_mul_le.trans
            simp only [natDegree_X_sub_C]
            omega
          · apply natDegree_mul_le.trans
            simp only [natDegree_C, zero_add]
            omega
        · apply (natDegree_add_le _ _).trans
          apply max_le
          · apply natDegree_mul_le.trans
            simp only [natDegree_X_sub_C]
            omega
          · apply natDegree_mul_le.trans
            simp only [natDegree_C, zero_add]
            omega

end BinarySOSInduction



/- Homogenization bridge for the binary case of Hilbert's polynomial theorem.
New formalization by Hanan Beer with Codex assistance, using Mathlib's homogenization API. -/

namespace BinaryHomogeneous
open Finset MvPolynomial

lemma degree_dehomogenize {n : ℕ} {p : MvPolynomial (Fin 2) ℝ}
    (hp : p.IsHomogeneous n) :
    (MvPolynomial.aeval ![Polynomial.X, 1] p : Polynomial ℝ).natDegree ≤ n := by
  classical
  rw [p.as_sum]
  simp only [MvPolynomial.aeval_sum, MvPolynomial.aeval_monomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  apply Polynomial.natDegree_mul_le.trans
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, ← Polynomial.C_eq_algebraMap,
    Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
  have h := hp.degree_eq_sum_deg_support hm
  rw [h]
  by_cases hm0 : m 0 = 0
  · simp [hm0]
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr hm0)

lemma binary_of_univariate
    (univariate : ∀ (d : ℕ) (p : Polynomial ℝ), p.natDegree ≤ 2*d →
      (∀ x : ℝ, 0 ≤ p.eval x) → ∃ u v : Polynomial ℝ,
      p = u^2 + v^2 ∧ u.natDegree ≤ d ∧ v.natDegree ≤ d) :
    ∀ d : ℕ, 0 < d → ∀ p : MvPolynomial (Fin 2) ℝ, p.IsHomogeneous (2*d) →
      (∀ x, 0 ≤ MvPolynomial.eval x p) →
      ∃ (m : ℕ) (g : Fin m → MvPolynomial (Fin 2) ℝ), p = ∑ i, (g i)^2 := by
  intro d _ p hp hpos
  let q : Polynomial ℝ := MvPolynomial.aeval ![Polynomial.X, 1] p
  have hq : q.natDegree ≤ 2*d := degree_dehomogenize hp
  have hqpos (x : ℝ) : 0 ≤ q.eval x := by
    change 0 ≤ Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, 1] p)
    have he : Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, 1] p) =
        MvPolynomial.eval ![x, 1] p := by
      rw [MvPolynomial.aeval_def, MvPolynomial.polynomial_eval_eval₂]
      congr 1
      · ext r; simp
      · ext i; fin_cases i <;> simp
    rw [he]
    exact hpos ![x, 1]
  obtain ⟨u, v, huv, hu, hv⟩ := univariate d q hq hqpos
  have hpq : q.homogenize (2*d) = p :=
    Polynomial.homogenize_eq_of_isHomogeneous hp rfl
  refine ⟨2, ![u.homogenize d, v.homogenize d], ?_⟩
  rw [← hpq, huv, Polynomial.homogenize_add, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [pow_two, two_mul, Polynomial.homogenize_mul u u hu hu,
    Polynomial.homogenize_mul v v hv hv]

end BinaryHomogeneous


namespace BinaryWeighted
open MvPolynomial

/-- Homogenize the weighted univariate two-square representation. -/
theorem binary_weighted_of_univariate
    (univariate : ∀ (d : ℕ) (p : Polynomial ℝ), p.natDegree ≤ 2*d →
      (∀ x : ℝ, 0 ≤ p.eval x) → ∃ u v : Polynomial ℝ,
      p = u^2 + (Polynomial.X^2 + 1)*v^2 ∧ u.natDegree ≤ d ∧
      (v = 0 ∨ v.natDegree + 1 ≤ d))
    (d : ℕ) (hd : 0 < d) (p : MvPolynomial (Fin 2) ℝ)
    (hp : p.IsHomogeneous (2*d)) (hpos : ∀ x, 0 ≤ MvPolynomial.eval x p) :
    ∃ u v : MvPolynomial (Fin 2) ℝ,
      p = u^2 + ((X 0)^2 + (X 1)^2)*v^2 ∧
      u.IsHomogeneous d ∧ v.IsHomogeneous (d-1) := by
  let q : Polynomial ℝ := MvPolynomial.aeval ![Polynomial.X, 1] p
  have hq : q.natDegree ≤ 2*d := BinaryHomogeneous.degree_dehomogenize hp
  have hqpos (x : ℝ) : 0 ≤ q.eval x := by
    change 0 ≤ Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, 1] p)
    have he : Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X, 1] p) =
        MvPolynomial.eval ![x, 1] p := by
      rw [MvPolynomial.aeval_def, MvPolynomial.polynomial_eval_eval₂]
      congr 1
      · ext r; simp
      · ext i; fin_cases i <;> simp
    rw [he]
    exact hpos ![x, 1]
  obtain ⟨u, v, huv, hu, hv⟩ := univariate d q hq hqpos
  have hvdeg : v.natDegree ≤ d-1 := by
    rcases hv with rfl | hv
    · simp
    · omega
  have hpq : q.homogenize (2*d) = p :=
    Polynomial.homogenize_eq_of_isHomogeneous hp rfl
  refine ⟨u.homogenize d, v.homogenize (d-1), ?_,
    Polynomial.isHomogeneous_homogenize u, Polynomial.isHomogeneous_homogenize v⟩
  rw [← hpq, huv, Polynomial.homogenize_add]
  have hu2 : (u^2).homogenize (2*d) = (u.homogenize d)^2 := by
    simpa only [pow_two, two_mul] using Polynomial.homogenize_mul u u hu hu
  have hv2 : (v^2).homogenize (2*(d-1)) = (v.homogenize (d-1))^2 := by
    simpa only [pow_two, two_mul] using Polynomial.homogenize_mul v v hvdeg hvdeg
  have hqdeg : (Polynomial.X^2 + 1 : Polynomial ℝ).natDegree ≤ 2 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · simp
  have hv2deg : (v^2).natDegree ≤ 2*(d-1) := by
    rw [Polynomial.natDegree_pow]
    omega
  have hprod := Polynomial.homogenize_mul (Polynomial.X^2 + 1 : Polynomial ℝ)
    (v^2) hqdeg hv2deg
  have hd2 : 2 + 2*(d-1) = 2*d := by omega
  rw [hd2, hv2] at hprod
  rw [hu2, hprod]
  simp

end BinaryWeighted


/- Weighted sum-of-two-squares representation for nonnegative univariate real polynomials.
Formalization by Hanan Beer with Codex assistance, following the factor/product method
of Pfister and Scheiderer, arXiv:1009.3144, Proposition 1.1. -/

namespace WeightedSOS
open Polynomial

lemma quadratic_coefficients (a b : ℝ) :
    ∃ α β γ : ℝ, α^2 + γ^2 = 1 ∧ α*β = -a ∧ β^2 + γ^2 = a^2+b^2 := by
  let s := a^2+b^2
  let m := min 1 s
  let f := fun t : ℝ => (1-t)*(s-t)-a^2
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hm : 0 ≤ m := le_min zero_le_one hs
  have hfm : f m ≤ 0 := by
    rcases le_total 1 s with h | h
    · simp only [m, min_eq_left h, f, sub_self, zero_mul, zero_sub]
      exact neg_nonpos.mpr (sq_nonneg a)
    · simp only [m, min_eq_right h, f, sub_self, mul_zero, zero_sub]
      exact neg_nonpos.mpr (sq_nonneg a)
  have hf0 : 0 ≤ f 0 := by dsimp [f,s]; nlinarith [sq_nonneg b]
  have hcont : ContinuousOn f (Set.Icc 0 m) := by dsimp [f]; fun_prop
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' hm hcont ⟨hfm,hf0⟩
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2.trans (min_le_left _ _)
  have hts : t ≤ s := ht.2.trans (min_le_right _ _)
  have heq : (1-t)*(s-t) = a^2 := by dsimp [f] at he; linarith
  let α := Real.sqrt (1-t)
  let γ := Real.sqrt t
  have ha : α^2 = 1-t := Real.sq_sqrt (sub_nonneg.mpr ht1)
  have hg : γ^2 = t := Real.sq_sqrt ht0
  by_cases hα : α = 0
  · have ht' : t = 1 := by simp [hα] at ha; linarith
    have az : a = 0 := by rw [ht'] at heq; nlinarith [sq_nonneg a]
    refine ⟨α, Real.sqrt (s-t), γ, ?_, ?_, ?_⟩
    · linarith
    · simp [hα,az]
    · rw [Real.sq_sqrt (sub_nonneg.mpr hts),hg]; dsimp [s]; ring
  · refine ⟨α, -a/α, γ, ?_, ?_, ?_⟩
    · linarith
    · field_simp
    · have hh : (-a/α)^2 = s-t := by
        apply (mul_left_cancel₀ (pow_ne_zero 2 hα))
        field_simp
        nlinarith [heq, ha]
      rw [hh,hg]; dsimp [s]; ring

lemma quadratic_weighted (a b : ℝ) :
    ∃ u : ℝ[X], ∃ c : ℝ,
      (X-C a)^2+(C b)^2 = u^2+(X^2+1)*(C c)^2 ∧ u.natDegree ≤ 1 := by
  obtain ⟨α,β,γ,hα,hβ,hγ⟩ := quadratic_coefficients a b
  refine ⟨C α*X+C β,γ,?_,?_⟩
  · apply Polynomial.funext
    intro x
    simp only [eval_add,eval_pow,eval_sub,eval_X,eval_C,eval_mul,eval_one]
    linear_combination -x^2*hα - 2*x*hβ - hγ
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans; simp
    · simp

lemma univariate_weighted :
    ∀ (d : ℕ) (p : ℝ[X]), p.natDegree ≤ 2*d →
      (∀ x : ℝ, 0 ≤ p.eval x) → ∃ u v : ℝ[X],
      p = u^2+(X^2+1)*v^2 ∧ u.natDegree ≤ d ∧ (v=0 ∨ v.natDegree+1 ≤ d) := by
  intro d
  induction d with
  | zero =>
      intro p hp hpos
      have hdeg : p.natDegree = 0 := by omega
      have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hdeg
      have hc : 0 ≤ p.coeff 0 := by
          have hh := hpos 0
          rw [he,eval_C] at hh
          exact hh
      refine ⟨C (Real.sqrt (p.coeff 0)),0,?_,by simp,Or.inl rfl⟩
      simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,← map_pow]
      rw [Real.sq_sqrt hc]
      exact he
  | succ d ih =>
      intro p hp hpos
      by_cases hz : p.natDegree = 0
      · have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hz
        have hc : 0 ≤ p.coeff 0 := by
          have hh := hpos 0
          rw [he,eval_C] at hh
          exact hh
        refine ⟨C (Real.sqrt (p.coeff 0)),0,?_,by simp,Or.inl rfl⟩
        simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero,← map_pow]
        rw [Real.sq_sqrt hc]
        exact he
      · have hp0 : p ≠ 0 := by intro h; simp [h] at hz
        obtain ⟨a,b,q,hpq,hqpos,hqdeg⟩ := BinarySOS.factor_nonnegative p hp0 (by omega) hpos
        obtain ⟨u,v,huv,hu,hv⟩ := ih q (by omega) hqpos
        obtain ⟨w,c,hw,hdw⟩ := quadratic_weighted a b
        refine ⟨w*u-(X^2+1)*C c*v,w*v+C c*u,?_,?_,Or.inr ?_⟩
        · rw [hpq,huv,hw]; ring
        · apply (natDegree_sub_le _ _).trans
          apply max_le
          · apply natDegree_mul_le.trans; omega
          · rcases hv with rfl|hv
            · simp
            · apply natDegree_mul_le.trans
              have hq : ((X^2+1)*C c : ℝ[X]).natDegree ≤ 2 := by
                apply natDegree_mul_le.trans
                have ht : (X^2+1 : ℝ[X]).natDegree ≤ 2 :=
                  (natDegree_add_le _ _).trans (by simp)
                simpa using ht
              omega
        · have he : (w*v+C c*u).natDegree ≤ d := by
            apply (natDegree_add_le _ _).trans
            apply max_le
            · rcases hv with rfl|hv
              · simp
              · apply natDegree_mul_le.trans; omega
            · apply natDegree_mul_le.trans; simpa using hu
          omega

end WeightedSOS



/- Polynomial cancellation for the positive-definite ternary-quartic case.
New formalization by Hanan Beer with Codex assistance, following the algebraic
identities in Pfister–Scheiderer, Proposition 2.4 (arXiv:1009.3144).
-/

namespace TernarySOSCancel
open Polynomial

private lemma quadratic_ne_zero : (X^2 + 1 : ℝ[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p : ℝ[X] => p.eval 0) h
  norm_num at this

private lemma quadratic_degree : (X^2 + 1 : ℝ[X]).natDegree = 2 := by
  rw [natDegree_add_eq_left_of_natDegree_lt]
  · simp
  · simp

private lemma quadratic_dvd {p : ℝ[X]} (hp : aeval Complex.I p = 0) :
    (X^2 + 1 : ℝ[X]) ∣ p := by
  simpa using p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hp (by simp)

private lemma quotient_degree {A U : ℝ[X]} (h : A = (X^2+1)*U)
    (hA : A.natDegree ≤ 4) : U.natDegree ≤ 2 := by
  by_cases hu : U = 0
  · simp [hu]
  rw [h, natDegree_mul quadratic_ne_zero hu, quadratic_degree] at hA
  omega

private lemma signed_cancel (g e K : ℝ[X]) (hg : g.natDegree ≤ 3)
    (he : e.natDegree ≤ 3) (h : e^2 + g^2 = (X^2+1)*K)
    (hi : aeval Complex.I e = Complex.I * aeval Complex.I g) :
    ∃ U V : ℝ[X], U.natDegree ≤ 2 ∧ V.natDegree ≤ 2 ∧
      X*U+V = g ∧ U^2+V^2 = K := by
  have hA : aeval Complex.I (g*X-e) = 0 := by
    simp only [map_sub, map_mul, aeval_X, hi]
    ring
  have hB : aeval Complex.I (e*X+g) = 0 := by
    simp only [map_add, map_mul, aeval_X, hi]
    linear_combination (aeval Complex.I g) * Complex.I_sq
  obtain ⟨U, hU⟩ := quadratic_dvd hA
  obtain ⟨V, hV⟩ := quadratic_dvd hB
  have hAd : (g*X-e).natDegree ≤ 4 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      simp only [natDegree_X]
      omega
    · omega
  have hBd : (e*X+g).natDegree ≤ 4 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · apply natDegree_mul_le.trans
      simp only [natDegree_X]
      omega
    · omega
  refine ⟨U, V, quotient_degree hU hAd, quotient_degree hV hBd, ?_, ?_⟩
  · apply mul_left_cancel₀ quadratic_ne_zero
    linear_combination -X * hU - hV
  · apply mul_left_cancel₀ (pow_ne_zero 2 quadratic_ne_zero)
    calc
      (X^2+1)^2 * (U^2+V^2) = ((X^2+1)*U)^2 + ((X^2+1)*V)^2 := by ring
      _ = (g*X-e)^2 + (e*X+g)^2 := by rw [← hU, ← hV]
      _ = (X^2+1)*(e^2+g^2) := by ring
      _ = (X^2+1)^2 * K := by rw [h]; ring

/-- Cancel the quadratic factor in the sum of two squares, preserving degree bounds. -/
theorem cancel (g e K : ℝ[X]) (hg : g.natDegree ≤ 3) (he : e.natDegree ≤ 3)
    (h : e^2 + g^2 = (X^2+1)*K) :
    ∃ U V : ℝ[X], U.natDegree ≤ 2 ∧ V.natDegree ≤ 2 ∧
      X*U+V = g ∧ U^2+V^2 = K := by
  have hz := congrArg (aeval Complex.I) h
  simp only [map_add, map_pow, map_mul, map_one, aeval_X, Complex.I_sq,
    neg_add_cancel, zero_mul] at hz
  have hs : (aeval Complex.I e)^2 = (Complex.I * aeval Complex.I g)^2 := by
    rw [mul_pow, Complex.I_sq]
    linear_combination hz
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with hi | hi
  · exact signed_cancel g e K hg he h hi
  · apply signed_cancel g (-e) K hg (by simpa using he) (by simpa using h)
    simp [hi]

end TernarySOSCancel



/- Positive-definite quadratic-coefficient case of the ternary quartic theorem.
Formalization by Hanan Beer with Codex assistance, using Pfister–Scheiderer,
arXiv:1009.3144, Proposition 2.4. -/

namespace TernarySOSRankTwo
open MvPolynomial
private abbrev A := MvPolynomial (Fin 2) ℝ

lemma homogeneous_eq {n : ℕ} {p q : A} (hp : p.IsHomogeneous n)
    (hq : q.IsHomogeneous n)
    (h : aeval ![Polynomial.X,1] p = (aeval ![Polynomial.X,1] q : Polynomial ℝ)) : p=q := by
  have hp' := Polynomial.homogenize_eq_of_isHomogeneous hp rfl
  have hq' := Polynomial.homogenize_eq_of_isHomogeneous hq rfl
  rw [← hp',← hq',h]

set_option maxHeartbeats 2000000 in
lemma rank_two_of_cancel
    (cancel : ∀ g η K : Polynomial ℝ, g.natDegree ≤ 3 → η.natDegree ≤ 3 →
      η^2+g^2=(Polynomial.X^2+1)*K → ∃ U V : Polynomial ℝ,
      U.natDegree ≤ 2 ∧ V.natDegree ≤ 2 ∧
      Polynomial.X*U+V=g ∧ U^2+V^2=K)
    (g h : A) (hg : g.IsHomogeneous 3) (hh : h.IsHomogeneous 4)
    (hpos : ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
      0 ≤ (x 0^2+x 1^2)*z^2+eval x g*z+eval x h) :
    ∃ U V ξ : A, U.IsHomogeneous 2 ∧ V.IsHomogeneous 2 ∧ ξ.IsHomogeneous 2 ∧
      ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
      (x 0^2+x 1^2)*z^2+eval x g*z+eval x h =
      (eval x ξ/2)^2+(x 0*z+eval x U/2)^2+(x 1*z+eval x V/2)^2 := by
  let q : A := (X 0)^2+(X 1)^2
  have hq : q.IsHomogeneous 2 := (isHomogeneous_X_pow _ _).add (isHomogeneous_X_pow _ _)
  let f : A := C 4*q*h-g^2
  have hf : f.IsHomogeneous 6 := by
    simpa only [f,mul_assoc] using ((hq.mul hh).C_mul 4).sub (hg.pow 2)
  have hfpos (x : Fin 2 → ℝ) : 0 ≤ eval x f := by
    have hc := discrim_le_zero (fun z : ℝ => by simpa [pow_two] using hpos x z)
    simp only [discrim] at hc
    simp only [f,q,map_sub,map_mul,map_pow,map_add,eval_C,eval_X]
    nlinarith
  obtain ⟨η,ξ,hfη,hη,hξ⟩ := BinaryWeighted.binary_weighted_of_univariate
    WeightedSOS.univariate_weighted 3 (by decide) f hf hfpos
  have he : η^2+g^2=q*(C 4*h-ξ^2) := by
    change C 4*q*h-g^2=η^2+q*ξ^2 at hfη
    linear_combination -hfη
  let D : A →ₐ[ℝ] Polynomial ℝ := aeval ![Polynomial.X,1]
  have hD : D q = Polynomial.X^2+1 := by simp [D,q]
  have hDη := BinaryHomogeneous.degree_dehomogenize hη
  have hDg := BinaryHomogeneous.degree_dehomogenize hg
  have hDe : (D η)^2+(D g)^2=(Polynomial.X^2+1)*(D (C 4*h-ξ^2)) := by
    have hz := congrArg D he
    simpa only [map_add,map_pow,map_mul,hD] using hz
  obtain ⟨u,v,hu,hv,huv,huk⟩ := cancel (D g) (D η) (D (C 4*h-ξ^2)) hDg hDη hDe
  let U := u.homogenize 2
  let V := v.homogenize 2
  have hU : U.IsHomogeneous 2 := Polynomial.isHomogeneous_homogenize u
  have hV : V.IsHomogeneous 2 := Polynomial.isHomogeneous_homogenize v
  have hsum : (X 0)*U+(X 1)*V=g := by
    apply homogeneous_eq (((isHomogeneous_X _ _).mul hU).add ((isHomogeneous_X _ _).mul hV)) hg
    simpa [U,V,hu,hv] using huv
  have hsquare : U^2+V^2=C 4*h-ξ^2 := by
    apply homogeneous_eq ((hU.pow 2).add (hV.pow 2)) ((hh.C_mul 4).sub (hξ.pow 2))
    simpa [U,V,hu,hv,D] using huk
  refine ⟨U,V,ξ,hU,hV,hξ,?_⟩
  intro x z
  have hv1 := congrArg (eval x) hsum
  have hv2 := congrArg (eval x) hsquare
  simp only [map_add,map_mul,eval_X] at hv1
  simp only [map_add,map_pow,map_sub,map_mul,eval_C] at hv2
  linear_combination -z*hv1-(1/4 : ℝ)*hv2

end TernarySOSRankTwo

/- Binary quadratic normalization for Hilbert17's ternary quartic case.
New formalization by Hanan Beer with Codex assistance. The polynomial-to-quadratic-form
bridge is adapted from @marcusbuffett's reduction PR4945; remaining infrastructure is Mathlib. -/
namespace TernarySOSNormalize
open Finset MvPolynomial
lemma quadAsForm {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous 2) :
    ∃ Q : QuadraticForm ℝ (Fin n → ℝ), ∀ x, Q x = eval x p := by
  classical
  let S := ↥p.support
  have pairs (u : S) : ∃ i j : Fin n, u.val = Finsupp.single i 1 + Finsupp.single j 1 := by
    have hc : u.val.toMultiset.card = 2 := by
      simpa [Finsupp.card_toMultiset,Finsupp.sum,id_def] using (hp.degree_eq_sum_deg_support u.property).symm
    obtain ⟨i,j,hij⟩ := Multiset.card_eq_two.mp hc
    refine ⟨i,j,?_⟩
    apply Multiset.toFinsupp.symm.injective
    change u.val.toMultiset = (Finsupp.single i 1 + Finsupp.single j 1).toMultiset
    simpa [Finsupp.toMultiset_add] using hij
  choose i j hpairs using pairs
  let Q : QuadraticForm ℝ (Fin n → ℝ) := ∑ u : S, p.coeff u.val • QuadraticMap.proj (R := ℝ) (i u) (j u)
  refine ⟨Q,fun x ↦ ?_⟩
  have mono (u : S) : monomial u.val (p.coeff u.val) = C (p.coeff u.val)*X (i u)*X (j u) := by
    conv_lhs => rw [hpairs u]
    rw [X, X, C_mul_monomial, monomial_mul, mul_one, mul_one, ← hpairs u]
  calc
    Q x = ∑ u : S, (p.coeff u.val * x (i u) * x (j u)) := by
      simp [Q,QuadraticMap.proj_apply,mul_assoc]
    _ = ∑ u : S, eval x (monomial u.val (p.coeff u.val)) := sum_congr rfl fun u _ ↦ by simp [mono u]
    _ = eval x p := by rw [← map_sum, p.support.sum_coe_sort (fun u ↦ monomial u (p.coeff u)),p.support_sum_monomial_coeff]


lemma normalize (q : MvPolynomial (Fin 2) ℝ) (hq : q.IsHomogeneous 2)
    (hpos : ∀ x, 0 ≤ eval x q) :
    ∃ e : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ),
      (∀ x, eval (e x) q = 0) ∨
      (∀ x, eval (e x) q = x 0 ^ 2) ∨
      (∀ x, eval (e x) q = x 0 ^ 2 + x 1 ^ 2) := by
  classical
  obtain ⟨Q, hQ⟩ := quadAsForm q hq
  have hdim : Module.finrank ℝ (Fin 2 → ℝ) = 2 := Module.finrank_fin_fun ℝ
  have H : ∃ w : Fin 2 → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      Q.Equivalent (QuadraticMap.weightedSumSquares ℝ w) := by
    have h := Q.equivalent_one_zero_neg_one_weighted_sum_squared
    rw [hdim] at h
    exact h
  obtain ⟨w, hw, ⟨e⟩⟩ := H
  have he (x : Fin 2 → ℝ) : eval (e.toLinearEquiv.symm x) q =
      w 0 * x 0 ^ 2 + w 1 * x 1 ^ 2 := by
    rw [← hQ, ← e.map_app]
    simp [QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_two, smul_eq_mul, pow_two]
  have hwpos (i : Fin 2) : 0 ≤ w i := by
    have h := hpos (e.toLinearEquiv.symm (Pi.single i 1))
    rw [← hQ, ← e.map_app] at h
    simpa [QuadraticMap.weightedSumSquares_apply, Pi.single_apply] using h
  have hw01 (i : Fin 2) : w i = 0 ∨ w i = 1 := by
    rcases hw i with h | h
    · have := hwpos i; linarith
    · exact h
  rcases hw01 0 with h0 | h0 <;> rcases hw01 1 with h1 | h1
  · exact ⟨e.toLinearEquiv.symm, Or.inl (fun x => by simpa only [h0, h1, zero_mul, one_mul, zero_add, add_zero] using he x)⟩
  · let swap : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
      LinearEquiv.funCongrLeft ℝ ℝ (Equiv.swap (0 : Fin 2) 1)
    refine ⟨swap.trans e.toLinearEquiv.symm, Or.inr (Or.inl ?_)⟩
    intro x
    change eval (e.toLinearEquiv.symm (swap x)) q = x 0 ^ 2
    rw [he]
    simp [swap, h0, h1]
  · exact ⟨e.toLinearEquiv.symm, Or.inr (Or.inl (fun x => by simpa only [h0, h1, zero_mul, one_mul, zero_add, add_zero] using he x))⟩
  · exact ⟨e.toLinearEquiv.symm, Or.inr (Or.inr (fun x => by simpa only [h0, h1, zero_mul, one_mul, zero_add, add_zero] using he x))⟩

end TernarySOSNormalize


/- Degenerate quadratic cases for nonnegative ternary quartics.
New formalization by Hanan Beer with Codex assistance. The dehomogenization
bound is from the team's binary Hilbert17 proof; other infrastructure is Mathlib. -/

namespace TernarySOSDegenerate
open MvPolynomial Filter
open scoped Topology
private abbrev A := MvPolynomial (Fin 2) ℝ

lemma linear_slope_zero (b c : ℝ) (h : ∀ z : ℝ, 0 ≤ b*z+c) : b = 0 := by
  by_contra hb
  have hh := h ((-c-1)/b)
  have he : b*((-c-1)/b)+c = -1 := by field_simp; ring
  rw [he] at hh
  linarith

lemma dehomog_eval (p : A) (x : ℝ) :
    Polynomial.eval x (MvPolynomial.aeval ![Polynomial.X,1] p) = eval ![x,1] p := by
  rw [MvPolynomial.aeval_def, MvPolynomial.polynomial_eval_eval₂]
  congr 1
  · ext r; simp
  · ext i; fin_cases i <;> simp

lemma cubic_factor (g : A) (hg : g.IsHomogeneous 3) (hzero : eval ![0,1] g = 0) :
    ∃ k : A, k.IsHomogeneous 2 ∧ g = MvPolynomial.X 0 * k := by
  let G : Polynomial ℝ := MvPolynomial.aeval ![Polynomial.X,1] g
  have hG : G.natDegree ≤ 3 := BinaryHomogeneous.degree_dehomogenize hg
  have hG0 : G.eval 0 = 0 := (dehomog_eval g 0).trans hzero
  obtain ⟨K, hK⟩ : Polynomial.X ∣ G := by
    simpa using (Polynomial.dvd_iff_isRoot.mpr hG0)
  have hKd : K.natDegree ≤ 2 := by
    by_cases hK0 : K = 0
    · simp [hK0]
    · rw [hK, Polynomial.natDegree_mul Polynomial.X_ne_zero hK0,
        Polynomial.natDegree_X] at hG
      omega
  refine ⟨K.homogenize 2, Polynomial.isHomogeneous_homogenize K, ?_⟩
  have he : G.homogenize 3 = g := Polynomial.homogenize_eq_of_isHomogeneous hg rfl
  rw [← he, hK]
  have hm := Polynomial.homogenize_mul (Polynomial.X : Polynomial ℝ) K
    (m := 1) (n := 2) (by simp) hKd
  simpa using hm

lemma rank_zero
    (binary : ∀ h : A, h.IsHomogeneous 4 → (∀ x, 0 ≤ eval x h) →
      ∃ m : ℕ, ∃ u : Fin m → A, h = ∑ i, (u i)^2)
    (g h : A) (hh : h.IsHomogeneous 4)
    (hpos : ∀ x : Fin 2 → ℝ, ∀ z : ℝ, 0 ≤ eval x g*z+eval x h) :
    ∃ m : ℕ, ∃ u : Fin m → A,
      ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
        eval x g*z+eval x h = ∑ i, (eval x (u i))^2 := by
  have hg0 (x : Fin 2 → ℝ) : eval x g = 0 := linear_slope_zero _ _ (hpos x)
  have hnn (x : Fin 2 → ℝ) : 0 ≤ eval x h := by simpa using hpos x 0
  obtain ⟨m,u,hu⟩ := binary h hh hnn
  refine ⟨m,u,?_⟩
  intro x z
  simp [hg0, hu]

lemma residual_nonneg (k h : A)
    (hpos : ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
      0 ≤ (x 0)^2*z^2+(x 0*eval x k)*z+eval x h) :
    ∀ x : Fin 2 → ℝ, 0 ≤ eval x h-(eval x k/2)^2 := by
  have off (x : Fin 2 → ℝ) (hx : x 0 ≠ 0) :
      0 ≤ eval x h-(eval x k/2)^2 := by
    have hp := hpos x (-eval x k/(2*x 0))
    have he : (x 0)^2*(-eval x k/(2*x 0))^2+
        (x 0*eval x k)*(-eval x k/(2*x 0))+eval x h =
        eval x h-(eval x k/2)^2 := by field_simp; ring
    rwa [he] at hp
  intro x
  by_cases hx : x 0 = 0
  · have hc : Continuous (fun t : ℝ =>
        eval ![t,x 1] h-(eval ![t,x 1] k/2)^2) := by
      have hv : Continuous (fun t : ℝ => (![t,x 1] : Fin 2 → ℝ)) := by fun_prop
      exact (h.continuous_eval.comp hv).sub (((k.continuous_eval.comp hv).div_const 2).pow 2)
    have he : (![0,x 1] : Fin 2 → ℝ) = x := by
      ext i; fin_cases i <;> simp [hx]
    have hl : 0 ≤ eval ![0,x 1] h-(eval ![0,x 1] k/2)^2 := by
      apply ge_of_tendsto (hc.continuousAt.tendsto.mono_left
        (show 𝓝[≠] (0:ℝ) ≤ 𝓝 (0:ℝ) from inf_le_left))
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact off ![t,x 1] (by simpa using ht)
    simpa only [he] using hl
  · exact off x hx

lemma rank_one
    (binary : ∀ h : A, h.IsHomogeneous 4 → (∀ x, 0 ≤ eval x h) →
      ∃ m : ℕ, ∃ u : Fin m → A, h = ∑ i, (u i)^2)
    (g h : A) (hg : g.IsHomogeneous 3) (hh : h.IsHomogeneous 4)
    (hpos : ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
      0 ≤ (x 0)^2*z^2+eval x g*z+eval x h) :
    ∃ k : A, k.IsHomogeneous 2 ∧ ∃ m : ℕ, ∃ u : Fin m → A,
      ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
        (x 0)^2*z^2+eval x g*z+eval x h =
          (x 0*z+eval x k)^2 + ∑ i, (eval x (u i))^2 := by
  have hg0 : eval ![0,1] g = 0 := by
    apply linear_slope_zero _ (eval ![0,1] h)
    intro z
    simpa using hpos ![0,1] z
  obtain ⟨K,hK,hgK⟩ := cubic_factor g hg hg0
  let k : A := MvPolynomial.C (1/2) * K
  have hk : k.IsHomogeneous 2 := hK.C_mul _
  let r : A := h-k^2
  have hr : r.IsHomogeneous 4 := hh.sub (hk.pow 2)
  have hnn : ∀ x, 0 ≤ eval x r := by
    have hp : ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
        0 ≤ (x 0)^2*z^2+(x 0*eval x K)*z+eval x h := by
      simpa [hgK] using hpos
    have hn := residual_nonneg K h hp
    intro x
    simpa [r, k, div_eq_mul_inv, mul_comm] using hn x
  obtain ⟨m,u,hu⟩ := binary r hr hnn
  refine ⟨k,hk,m,u,?_⟩
  intro x z
  have he : eval x h = (eval x k)^2 + ∑ i, (eval x (u i))^2 := by
    have ht := congrArg (eval x) hu
    simp only [r, map_sub, map_pow, map_sum] at ht
    linarith
  rw [he, hgK]
  simp only [map_mul, eval_X]
  dsimp [k]
  simp only [map_mul, eval_C]
  ring

end TernarySOSDegenerate



/- Coordinate changes for nonnegative ternary quartics with a real zero.
New formalization by Hanan Beer with Codex assistance. -/

namespace TernarySOSCoordinates
open Finset MvPolynomial

noncomputable def linearForm {n : ℕ} (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (i : Fin n) : MvPolynomial (Fin n) ℝ :=
  ∑ j, C (e (Pi.single j (1 : ℝ) : Fin n → ℝ) i) * X j

lemma eval_linearForm {n : ℕ} (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (x : Fin n → ℝ) (i : Fin n) : eval x (linearForm e i) = e x i := by
  classical
  have hx : ∑ j : Fin n, x j • Pi.single j (1 : ℝ) = x := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
  calc
    _ = ∑ j, x j * e (Pi.single j (1 : ℝ) : Fin n → ℝ) i := by simp [linearForm, mul_comm]
    _ = e (∑ j : Fin n, x j • Pi.single j (1 : ℝ)) i := by
      simp [Finset.sum_apply, smul_eq_mul]
    _ = _ := by rw [hx]

lemma homogeneous_linearForm {n : ℕ} (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (i : Fin n) : (linearForm e i).IsHomogeneous 1 := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_X _ _).C_mul _

noncomputable def pull {n : ℕ} (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  aeval (linearForm e) p

lemma eval_pull {n : ℕ} (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (p : MvPolynomial (Fin n) ℝ) (x : Fin n → ℝ) :
    eval x (pull e p) = eval (e x) p := by
  simp only [pull, aeval_def, algebraMap_eq, eval_eval₂, eval_linearForm]
  have he : (eval x).comp (C : ℝ →+* MvPolynomial (Fin n) ℝ) = RingHom.id ℝ := by
    ext r
    simp
  rw [he]
  rfl

lemma homogeneous_pull {n d : ℕ} (e : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d) :
    (pull e p).IsHomogeneous d := by
  simpa only [pull, one_mul] using hp.aeval (linearForm e) (homogeneous_linearForm e)

lemma sos_pullback {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (p : MvPolynomial (Fin n) ℝ) (m : ℕ) (g : Fin m → MvPolynomial (Fin n) ℝ)
    (h : ∀ x, eval (e x) p = ∑ i, (eval x (g i))^2) :
    ∃ m : ℕ, ∃ g : Fin m → MvPolynomial (Fin n) ℝ, p = ∑ i, (g i)^2 := by
  refine ⟨m, fun i => pull e.symm.toLinearMap (g i), ?_⟩
  apply MvPolynomial.funext
  intro x
  simp only [map_sum, map_pow, eval_pull]
  change eval x p = ∑ i, (eval (e.symm x) (g i))^2
  simpa only [LinearEquiv.apply_symm_apply] using h (e.symm x)

noncomputable def pivotMap {n : ℕ} (v : Fin n → ℝ) (j : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun x := x + x j • (v - Pi.single j 1)
  map_add' x y := by ext i; simp [add_mul]; ring
  map_smul' r x := by ext i; simp [mul_add, mul_assoc]

lemma pivot_injective {n : ℕ} (v : Fin n → ℝ) (j : Fin n) (hj : v j ≠ 0) :
    Function.Injective (pivotMap v j) := by
  intro x y h
  have hxyj : x j = y j := by
    have he := congrFun h j
    simp only [pivotMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_eq_same] at he
    apply (mul_right_inj' hj).mp
    nlinarith
  ext i
  have he := congrFun h i
  change x i + x j * (v i - (Pi.single j (1 : ℝ) : Fin n → ℝ) i) =
    y i + y j * (v i - (Pi.single j (1 : ℝ) : Fin n → ℝ) i) at he
  rw [hxyj] at he
  linarith

lemma exists_equiv_zero_axis (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    ∃ e : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ), e (Fin.cons 1 0) = v := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let swap : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    LinearEquiv.funCongrLeft ℝ ℝ (Equiv.swap (0 : Fin 3) j)
  let pivot := LinearEquiv.ofInjectiveEndo (pivotMap v j) (pivot_injective v j hj)
  refine ⟨swap.trans pivot, ?_⟩
  have base : (Fin.cons 1 0 : Fin 3 → ℝ) = Pi.single 0 1 := by
    ext i
    fin_cases i <;> rfl
  have hs : swap (Fin.cons 1 0) = Pi.single j 1 := by
    rw [base]
    ext i
    by_cases hi : i = j
    · subst i; simp [swap, LinearEquiv.funCongrLeft]
    · have hn : (Equiv.swap (0 : Fin 3) j) i ≠ 0 := by
        intro he
        apply hi
        have hh := congrArg (Equiv.swap (0 : Fin 3) j) he
        simpa using hh
      simp [swap, LinearEquiv.funCongrLeft, hn, hi]
  change pivot (swap (Fin.cons 1 0)) = v
  rw [hs]
  simp [pivot, LinearEquiv.ofInjectiveEndo, pivotMap]

lemma normalize_zero (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous 4)
    (hpos : ∀ x, 0 ≤ eval x p) (hz : ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ eval v p = 0) :
    ∃ e : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ),
      (pull e.toLinearMap p).IsHomogeneous 4 ∧
      (∀ x, 0 ≤ eval x (pull e.toLinearMap p)) ∧
      eval (Fin.cons 1 (0 : Fin 2 → ℝ)) (pull e.toLinearMap p) = 0 := by
  obtain ⟨v, hv, hz⟩ := hz
  obtain ⟨e, he⟩ := exists_equiv_zero_axis v hv
  refine ⟨e, homogeneous_pull e.toLinearMap hp, ?_, ?_⟩
  · intro x
    rw [eval_pull]
    exact hpos _
  · rw [eval_pull]
    change eval (e (Fin.cons 1 (0 : Fin 2 → ℝ))) p = 0
    rwa [he]

end TernarySOSCoordinates


/- A nonnegative homogeneous quartic vanishing on the first coordinate axis
has degree at most two in that coordinate. Formalization by Hanan Beer. -/

namespace TernarySOSCoordinates
open Finset MvPolynomial Filter
open scoped Polynomial

lemma leadingCoeff_nonneg (p : ℝ[X]) (hp : ∀ x, 0 ≤ p.eval x) :
    0 ≤ p.leadingCoeff := by
  by_cases hd : p.degree ≤ 0
  · have he := Polynomial.eq_C_of_degree_le_zero hd
    rw [he]
    simpa only [Polynomial.leadingCoeff_C, Polynomial.coeff_zero_eq_eval_zero] using hp 0
  · by_contra! h
    have ht := p.tendsto_atBot_of_leadingCoeff_nonpos (lt_of_not_ge hd) h.le
    obtain ⟨x, hx⟩ := (ht.eventually_lt_atBot (0 : ℝ)).exists
    exact (not_lt_of_ge (hp x)) hx

lemma cubic_coeff_zero (p : ℝ[X]) (hd : p.natDegree ≤ 3) (hp : ∀ x, 0 ≤ p.eval x) :
    p.coeff 3 = 0 := by
  by_contra hn
  have hd3 : p.natDegree = 3 := le_antisymm hd (Polynomial.le_natDegree_of_ne_zero hn)
  have hp0 : p ≠ 0 := by intro h; simp [h] at hn
  have h1 := leadingCoeff_nonneg p hp
  have h2 := leadingCoeff_nonneg (p.comp (-Polynomial.X)) (by simpa using fun x => hp (-x))
  rw [Polynomial.comp_neg_X_leadingCoeff_eq, hd3] at h2
  norm_num at h2
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp0) (by linarith)

lemma quartic_expansion (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous 4)
    (x : Fin 2 → ℝ) (z : ℝ) :
    eval (Fin.cons z x) p =
      ∑ i ∈ range 5, eval x ((finSuccEquiv ℝ 2 p).coeff i) * z^i := by
  rw [eval_eq_eval_mv_eval']
  rw [Polynomial.eval_eq_sum_range' (n := 5)]
  · simp only [Polynomial.coeff_map]
  · apply lt_of_le_of_lt Polynomial.natDegree_map_le
    rw [natDegree_finSuccEquiv]
    have := (degreeOf_le_totalDegree p 0).trans hp.totalDegree_le
    omega

lemma quartic_coeff_four (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous 4)
    (hz : eval (Fin.cons 1 (0 : Fin 2 → ℝ)) p = 0) :
    (finSuccEquiv ℝ 2 p).coeff 4 = 0 := by
  let P := finSuccEquiv ℝ 2 p
  have hs (i : ℕ) (hi : i < 4) : eval (0 : Fin 2 → ℝ) (P.coeff i) = 0 := by
    rw [eval_zero]
    change coeff 0 (P.coeff i) = 0
    apply (hp.finSuccEquiv_coeff_isHomogeneous i (4-i) (by omega)).coeff_eq_zero
    simp only [map_zero]
    omega
  have hc : eval (0 : Fin 2 → ℝ) (P.coeff 4) = 0 := by
    rw [quartic_expansion p hp] at hz
    change (∑ i ∈ range 5, eval (0 : Fin 2 → ℝ) (P.coeff i) * (1 : ℝ)^i) = 0 at hz
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, one_pow, mul_one, zero_add] at hz
    rw [hs 0 (by decide), hs 1 (by decide), hs 2 (by decide), hs 3 (by decide)] at hz
    simpa only [zero_add] using hz
  have hh : (P.coeff 4).IsHomogeneous 0 := hp.finSuccEquiv_coeff_isHomogeneous 4 0 rfl
  have he : P.coeff 4 = C (coeff 0 (P.coeff 4)) :=
    totalDegree_eq_zero_iff_eq_C.mp (le_antisymm hh.totalDegree_le (Nat.zero_le _))
  rw [eval_zero] at hc
  change coeff 0 (P.coeff 4) = 0 at hc
  simpa [hc] using he

lemma quartic_decomposition (p : MvPolynomial (Fin 3) ℝ) (hp : p.IsHomogeneous 4)
    (hpos : ∀ x, 0 ≤ eval x p) (hz : eval (Fin.cons 1 (0 : Fin 2 → ℝ)) p = 0) :
    ∃ f2 f3 f4 : MvPolynomial (Fin 2) ℝ,
      f2.IsHomogeneous 2 ∧ f3.IsHomogeneous 3 ∧ f4.IsHomogeneous 4 ∧
      ∀ x : Fin 2 → ℝ, ∀ z : ℝ, eval (Fin.cons z x) p =
        eval x f2 * z^2 + eval x f3 * z + eval x f4 := by
  let P := finSuccEquiv ℝ 2 p
  have h4 : P.coeff 4 = 0 := quartic_coeff_four p hp hz
  have hdeg : P.natDegree ≤ 3 := by
    have hle : P.natDegree ≤ 4 := by
      dsimp [P]
      rw [natDegree_finSuccEquiv]
      exact (degreeOf_le_totalDegree p 0).trans hp.totalDegree_le
    by_contra! hn
    have he : P.natDegree = 4 := by omega
    have hp0 : P ≠ 0 := by intro h; simp [h] at hn
    exact (Polynomial.leadingCoeff_ne_zero.mpr hp0) (by simpa [Polynomial.leadingCoeff, he] using h4)
  have h3 (x : Fin 2 → ℝ) : eval x (P.coeff 3) = 0 := by
    have hn : ∀ z : ℝ, 0 ≤ (P.map (eval x)).eval z := by
      intro z
      simpa only [P, ← eval_eq_eval_mv_eval'] using hpos (Fin.cons z x)
    simpa only [Polynomial.coeff_map] using cubic_coeff_zero (P.map (eval x))
      (Polynomial.natDegree_map_le.trans hdeg) hn
  refine ⟨P.coeff 2, P.coeff 1, P.coeff 0,
    hp.finSuccEquiv_coeff_isHomogeneous 2 2 rfl,
    hp.finSuccEquiv_coeff_isHomogeneous 1 3 rfl,
    hp.finSuccEquiv_coeff_isHomogeneous 0 4 rfl, ?_⟩
  intro x z
  rw [quartic_expansion p hp]
  change (∑ i ∈ range 5, eval x (P.coeff i) * z^i) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
    mul_one, pow_one, h3, h4, map_zero, zero_mul, add_zero]
  ring

end TernarySOSCoordinates


/- Extend a binary linear change of variables while fixing the leading coordinate.
Formalization by Hanan Beer with Codex assistance. -/

namespace TernarySOSBlock

noncomputable def extend (e : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)) :
    (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := Fin.cons (v 0) (e (Fin.tail v))
  invFun v := Fin.cons (v 0) (e.symm (Fin.tail v))
  left_inv v := by
    simp only [Fin.cons_zero, Fin.tail_cons, LinearEquiv.symm_apply_apply,
      Fin.cons_self_tail]
  right_inv v := by
    simp only [Fin.cons_zero, Fin.tail_cons, LinearEquiv.apply_symm_apply,
      Fin.cons_self_tail]
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change e (Fin.tail x + Fin.tail y) j = e (Fin.tail x) j + e (Fin.tail y) j
      rw [map_add]
      rfl
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change e (c • Fin.tail x) j = c * e (Fin.tail x) j
      rw [map_smul]
      rfl

@[simp] theorem extend_cons (e : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ))
    (z : ℝ) (x : Fin 2 → ℝ) : extend e (Fin.cons z x) = Fin.cons z (e x) := by
  simp [extend]

end TernarySOSBlock



/- Assembly of the real-zero ternary-quartic sum-of-squares theorem.
New formalization by Hanan Beer with Codex assistance, following Pfister–Scheiderer
(arXiv:1009.3144), Proposition 2.4, and the classical reduction by @marcusbuffett. -/
namespace TernarySOSAssembly
open MvPolynomial Finset Filter
open TernarySOSCoordinates
open scoped Topology
private abbrev A := MvPolynomial (Fin 2) ℝ
private abbrev B := MvPolynomial (Fin 3) ℝ

lemma quadratic_leading_nonneg (a b c : ℝ)
    (h : ∀ z : ℝ, 0 ≤ a*z^2+b*z+c) : 0 ≤ a := by
  by_contra! ha
  have ht : Tendsto (fun z : ℝ => (a*z+b)*z+c) atTop atBot :=
    tendsto_atBot_add_const_right _ c <|
      (tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop₀
        tendsto_id
  obtain ⟨z,hz⟩ := (ht.eventually (eventually_lt_atBot 0)).exists
  have hh := h z
  nlinarith

lemma binary_quartic (h : A) (hh : h.IsHomogeneous 4) (hpos : ∀ x, 0 ≤ eval x h) :
    ∃ m : ℕ, ∃ u : Fin m → A, h = ∑ i, (u i)^2 :=
  BinaryHomogeneous.binary_of_univariate
    (BinarySOSInduction.two_squares_of_quadratic_factor BinarySOS.factor_nonnegative)
    2 (by decide) h hh hpos

noncomputable def lift (p : A) : B := rename Fin.succ p
@[simp] lemma eval_lift (p : A) (x : Fin 2 → ℝ) (z : ℝ) :
    eval (Fin.cons z x) (lift p) = eval x p := by
  simp [lift,eval_rename]

@[simp] lemma cons_one (z : ℝ) (x : Fin 2 → ℝ) : (Fin.cons z x : Fin 3 → ℝ) 1 = x 0 := rfl
@[simp] lemma cons_two (z : ℝ) (x : Fin 2 → ℝ) : (Fin.cons z x : Fin 3 → ℝ) 2 = x 1 := rfl

lemma sos_pullback_cons (e : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (p : B) (m : ℕ) (F : Fin m → B)
    (h : ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
      eval (e (Fin.cons z x)) p = ∑ i, (eval (Fin.cons z x) (F i))^2) :
    ∃ m : ℕ, ∃ F : Fin m → B, p=∑ i,(F i)^2 := by
  apply sos_pullback e p m F
  intro w
  simpa only [Fin.cons_self_tail] using h (Fin.tail w) (w 0)

set_option maxHeartbeats 2000000 in
lemma normal_form_sos (p : B) (f2 g h : A)
    (h2 : f2.IsHomogeneous 2) (hg : g.IsHomogeneous 3) (hh : h.IsHomogeneous 4)
    (hp : ∀ x, 0 ≤ eval x p)
    (hf : ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
      eval (Fin.cons z x) p = eval x f2*z^2+eval x g*z+eval x h) :
    ∃ m : ℕ, ∃ F : Fin m → B, p=∑ i,(F i)^2 := by
  classical
  have hf2 (x : Fin 2 → ℝ) : 0 ≤ eval x f2 := by
    apply quadratic_leading_nonneg (eval x f2) (eval x g) (eval x h)
    intro z
    rw [← hf]
    exact hp _
  obtain ⟨e,he⟩ := TernarySOSNormalize.normalize f2 h2 hf2
  let E := TernarySOSBlock.extend e
  let G := pull e.toLinearMap g
  let H := pull e.toLinearMap h
  have hG : G.IsHomogeneous 3 := homogeneous_pull e.toLinearMap hg
  have hH : H.IsHomogeneous 4 := homogeneous_pull e.toLinearMap hh
  have hE (x : Fin 2 → ℝ) (z : ℝ) :
      eval (E (Fin.cons z x)) p = eval (e x) f2*z^2+eval x G*z+eval x H := by
    simpa only [E,TernarySOSBlock.extend_cons,G,H,eval_pull,LinearEquiv.coe_coe] using hf (e x) z
  have hnn (x : Fin 2 → ℝ) (z : ℝ) :
      0 ≤ eval (e x) f2*z^2+eval x G*z+eval x H := by rw [← hE]; exact hp _
  rcases he with he | he | he
  · have hnn' : ∀ x : Fin 2 → ℝ, ∀ z : ℝ, 0 ≤ eval x G*z+eval x H := by
      intro x z; simpa only [he,zero_mul,zero_add] using hnn x z
    obtain ⟨m,u,hu⟩ := TernarySOSDegenerate.rank_zero binary_quartic G H hH hnn'
    apply sos_pullback_cons E p m (fun i => lift (u i))
    intro x z
    rw [hE,he]
    simp only [zero_mul,zero_add,eval_lift]
    exact hu x z
  · have hnn' : ∀ x : Fin 2 → ℝ, ∀ z : ℝ, 0 ≤ x 0^2*z^2+eval x G*z+eval x H := by
      intro x z; simpa only [he] using hnn x z
    obtain ⟨k,hk,m,u,hu⟩ := TernarySOSDegenerate.rank_one binary_quartic G H hG hH hnn'
    let F : Fin (m+1) → B := Fin.cons (X 1*X 0+lift k) (fun i => lift (u i))
    apply sos_pullback_cons E p (m+1) F
    intro x z
    rw [hE,he]
    simpa [F,Fin.sum_univ_succ,eval_lift] using hu x z
  · have hnn' : ∀ x : Fin 2 → ℝ, ∀ z : ℝ,
        0 ≤ (x 0^2+x 1^2)*z^2+eval x G*z+eval x H := by
      intro x z; simpa only [he] using hnn x z
    obtain ⟨U,V,ξ,hU,hV,hξ,hu⟩ := TernarySOSRankTwo.rank_two_of_cancel
      TernarySOSCancel.cancel G H hG hH hnn'
    let F : Fin 3 → B := ![C (1/2)*lift ξ,X 1*X 0+C (1/2)*lift U,
      X 2*X 0+C (1/2)*lift V]
    apply sos_pullback_cons E p 3 F
    intro x z
    rw [hE,he]
    simpa [F,Fin.sum_univ_three,Matrix.cons_val,eval_lift,
      div_eq_mul_inv,mul_comm] using hu x z

lemma ternary_quartic (p : B) (hp : p.IsHomogeneous 4) (hpos : ∀ x,0≤eval x p)
    (hz : ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ eval v p=0) :
    ∃ m : ℕ, ∃ F : Fin m → B, p=∑ i,(F i)^2 := by
  obtain ⟨e,hp',hpos',hz'⟩ := normalize_zero p hp hpos hz
  obtain ⟨f2,g,h,h2,hg,hh,hf⟩ := quartic_decomposition (pull e.toLinearMap p) hp' hpos' hz'
  obtain ⟨m,F,hF⟩ := normal_form_sos (pull e.toLinearMap p) f2 g h h2 hg hh hpos' hf
  apply sos_pullback e p m F
  intro x
  have heval := eval_pull e.toLinearMap p x
  rw [hF,map_sum] at heval
  simpa only [map_pow,LinearEquiv.coe_coe] using heval.symm

end TernarySOSAssembly

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1.H2 :=
  TernarySOSAssembly.ternary_quartic
