import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1_H2_R1
import Mathlib

/-! A degree-bounded sum-of-two-squares decomposition for nonnegative real polynomials.
Credit: everything up to `dehom_natDegree` is reused verbatim from @Genbox's proof of
Hilbert17.hilbert_17th_problem_poly.R1.H2.R1.H1 (PR #5249); `binaryTwoSquares` is its
`binaryHomogeneous` with the two homogenized squares kept explicit. -/

open Polynomial Filter Set
open scoped Topology

namespace OMA.BinaryTwoSquares

private theorem quotientNonneg (p q A B : ℝ[X]) (hp : ∀ x, 0 ≤ p.eval x)
    (he : p = (A^2+B^2)*q) {a : ℝ} (hpos : ∀ x ≠ a, 0 < (A^2+B^2).eval x) :
    ∀ x, 0 ≤ q.eval x := by
  have hclosed : IsClosed {x : ℝ | 0 ≤ q.eval x} := isClosed_le continuous_const q.continuous
  have hs : ({a}ᶜ : Set ℝ) ⊆ {x : ℝ | 0 ≤ q.eval x} := by
    intro x hx
    have hh := hp x
    rw [he, eval_mul] at hh
    exact nonneg_of_mul_nonneg_right hh (hpos x (by simpa using hx))
  have hu := closure_minimal hs hclosed
  rw [(dense_compl_singleton a).closure_eq] at hu
  exact fun x => hu trivial

private theorem realRootPair (p : ℝ[X]) (hp : ∀ x, 0 ≤ p.eval x) (a : ℝ)
    (ha : p.eval a = 0) : ∃ q : ℝ[X], p = (X-C a)^2*q := by
  obtain ⟨r, hr⟩ := dvd_iff_isRoot.mpr ha
  have hz : r.eval a = 0 := by
    rcases lt_trichotomy (r.eval a) 0 with hneg | heq | hpos
    · have hcont : Tendsto (fun x : ℝ => r.eval x) (𝓝[>] a) (𝓝 (r.eval a)) :=
        r.continuous.continuousAt.continuousWithinAt
      have hnear : ∀ᶠ x : ℝ in 𝓝[>] a, r.eval x < 0 := hcont (Iio_mem_nhds hneg)
      have hside : ∀ᶠ x in 𝓝[>] a, a < x := self_mem_nhdsWithin
      obtain ⟨x, hx, hrx⟩ := (hside.and hnear).exists
      have hback := hp x
      rw [hr, eval_mul, eval_sub, eval_X, eval_C] at hback
      exact False.elim ((not_lt_of_ge hback) (mul_neg_of_pos_of_neg (sub_pos.mpr hx) hrx))
    · exact heq
    · have hcont : Tendsto (fun x : ℝ => r.eval x) (𝓝[<] a) (𝓝 (r.eval a)) :=
        r.continuous.continuousAt.continuousWithinAt
      have hnear : ∀ᶠ x : ℝ in 𝓝[<] a, 0 < r.eval x := hcont (Ioi_mem_nhds hpos)
      have hside : ∀ᶠ x in 𝓝[<] a, x < a := self_mem_nhdsWithin
      obtain ⟨x,hx,hrx⟩ := (hside.and hnear).exists
      have hback := hp x
      rw [hr, eval_mul, eval_sub, eval_X, eval_C] at hback
      exact False.elim ((not_lt_of_ge hback) (mul_neg_of_neg_of_pos (sub_neg.mpr hx) hrx))
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hz
  exact ⟨q, by rw [hr, hq, pow_two, mul_assoc]⟩

private theorem stripPair (p : ℝ[X]) (hp0 : 0 < p.natDegree) (hp : ∀ x, 0 ≤ p.eval x) :
    ∃ r A B : ℝ[X], p = (A^2+B^2)*r ∧ (A^2+B^2).natDegree = 2 ∧
      A.natDegree ≤ 1 ∧ B.natDegree ≤ 1 ∧ ∀ x, 0 ≤ r.eval x := by
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hp0
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z p = 0 := IsAlgClosed.exists_aeval_eq_zero ℂ p hdeg.ne'
  let A : ℝ[X] := X-C z.re
  let B : ℝ[X] := C z.im
  have hA : A.natDegree = 1 := natDegree_X_sub_C _
  have hB : B.natDegree = 0 := natDegree_C _
  have hcomp : A^2+B^2 = X ^ 2 - C (2*z.re)*X + C (‖z‖^2) := by
    have hn : ‖z‖^2 = z.re^2 + z.im^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    unfold A B
    rw [hn]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  have hquad : (A^2+B^2).natDegree = 2 := by
    have hlt : (B^2).natDegree < (A^2).natDegree := by
      rw [natDegree_pow, natDegree_pow, hA, hB]
      decide
    rw [natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_pow, hA]
  by_cases him : z.im = 0
  · have hre : (z.re : ℂ) = z := Complex.ext (by simp) (by simp [him])
    have hz' : p.eval z.re = 0 := by
      have h := hz
      rw [← hre] at h
      change aeval (algebraMap ℝ ℂ z.re) p = 0 at h
      rw [aeval_algebraMap_apply_eq_algebraMap_eval] at h
      exact (FaithfulSMul.algebraMap_injective ℝ ℂ) (h.trans (map_zero _).symm)
    obtain ⟨r, hr⟩ := realRootPair p hp z.re hz'
    have hE : p = (A^2+B^2)*r := by simpa [A,B,him] using hr
    refine ⟨r,A,B,hE,hquad,hA.le,by omega,quotientNonneg p r A B hp hE (a := z.re) ?_⟩
    intro x hx
    simp [A,B,him, sq_pos_of_ne_zero (sub_ne_zero.mpr hx)]
  · obtain ⟨r, hr⟩ := p.quadratic_dvd_of_aeval_eq_zero_im_ne_zero hz him
    rw [← hcomp] at hr
    refine ⟨r,A,B,hr,hquad,hA.le,by omega,quotientNonneg p r A B hp hr (a := 0) ?_⟩
    intro x _
    simp only [A,B,eval_add,eval_pow,eval_sub,eval_X,eval_C]
    positivity

theorem existsTwoSquares (d : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ 2*d)
    (hp : ∀ x, 0 ≤ p.eval x) :
    ∃ g h : ℝ[X], g.natDegree ≤ d ∧ h.natDegree ≤ d ∧ p = g^2+h^2 := by
  induction d generalizing p with
  | zero =>
    have hpdeg : p.natDegree = 0 := by omega
    have hC := eq_C_of_natDegree_eq_zero hpdeg
    have hc : 0 ≤ p.coeff 0 := by simpa only [coeff_zero_eq_eval_zero] using hp 0
    refine ⟨C (Real.sqrt (p.coeff 0)),0,by simp,by simp,?_⟩
    exact hC.trans (by rw [← map_pow, Real.sq_sqrt hc]; simp)
  | succ d ih =>
    by_cases he : p.natDegree = 0
    · have hC := eq_C_of_natDegree_eq_zero he
      have hc : 0 ≤ p.coeff 0 := by simpa only [coeff_zero_eq_eval_zero] using hp 0
      refine ⟨C (Real.sqrt (p.coeff 0)),0,by simp,by simp,?_⟩
      exact hC.trans (by rw [← map_pow, Real.sq_sqrt hc]; simp)
    · obtain ⟨r,A,B,heq,hq,hA,hB,hr⟩ := stripPair p (Nat.pos_of_ne_zero he) hp
      have hpne : p ≠ 0 := by intro he'; simp [he'] at he
      have hrne : r ≠ 0 := by intro hz; exact hpne (by simp [heq,hz])
      have hqne : A^2+B^2 ≠ 0 := by intro hz; exact hpne (by simp [heq,hz])
      have hrd : r.natDegree ≤ 2*d := by
        have h := natDegree_mul hqne hrne
        rw [← heq, hq] at h
        omega
      obtain ⟨g,h,hg,hh,hr'⟩ := ih r hrd hr
      have hmul {a b : ℝ[X]} (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ d) :
          (a*b).natDegree ≤ d+1 := by
        have hle : (a*b).natDegree ≤ a.natDegree + b.natDegree := natDegree_mul_le
        omega
      refine ⟨A*g-B*h, A*h+B*g, ?_, ?_, ?_⟩
      · exact (natDegree_sub_le _ _).trans (max_le (hmul hA hg) (hmul hB hh))
      · exact (natDegree_add_le _ _).trans (max_le (hmul hA hh) (hmul hB hg))
      · rw [heq,hr']
        ring
private theorem dehom_natDegree (f : MvPolynomial (Fin 2) ℝ) (n : ℕ)
    (hf : f.IsHomogeneous n) : (MvPolynomial.aeval ![(X : ℝ[X]),1] f).natDegree ≤ n := by
  classical
  let dehom : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] ℝ[X] := MvPolynomial.aeval ![X,1]
  change (dehom f).natDegree ≤ _
  have he : dehom f = ∑ m ∈ f.support, dehom (MvPolynomial.monomial m (f.coeff m)) := by
    conv_lhs => rw [f.as_sum]
    exact map_sum dehom _ _
  rw [he]
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro m hm
  have hw : m 0 + m 1 = n := by
    have hh : m.weight (1 : Fin 2 → ℕ) = n := hf (by simpa using hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using hh
  have hde : dehom (MvPolynomial.monomial m (f.coeff m)) = C (f.coeff m) * X^(m 0) := by
    change MvPolynomial.aeval ![(X : ℝ[X]),1] (MvPolynomial.monomial m (f.coeff m)) = _
    rw [MvPolynomial.aeval_monomial]
    simp [Finsupp.prod_fintype, Fin.prod_univ_two]
  rw [hde]
  exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le (m 0)).trans (by omega))

theorem binaryTwoSquares (d : ℕ) (f : MvPolynomial (Fin 2) ℝ) (hf : f.IsHomogeneous (2*d))
    (hpos : ∀ x, 0 ≤ MvPolynomial.eval x f) :
    ∃ u v : MvPolynomial (Fin 2) ℝ, u.IsHomogeneous d ∧ v.IsHomogeneous d ∧ f = u^2+v^2 := by
  let p : ℝ[X] := MvPolynomial.aeval ![X,1] f
  have hpdeg : p.natDegree ≤ 2*d := dehom_natDegree f _ hf
  have hp (x : ℝ) : 0 ≤ p.eval x := by
    have he : (fun i : Fin 2 => Polynomial.aeval x (![(X : ℝ[X]),1] i)) = ![x,1] := by
      funext i
      fin_cases i <;> simp
    change 0 ≤ Polynomial.aeval x (MvPolynomial.aeval ![(X : ℝ[X]),1] f)
    rw [MvPolynomial.comp_aeval_apply, he]
    exact hpos ![x,1]
  obtain ⟨u,v,hu,hv,h⟩ := existsTwoSquares d p hpdeg hp
  have hhom : p.homogenize (2*d) = f := homogenize_eq_of_isHomogeneous hf rfl
  refine ⟨u.homogenize d, v.homogenize d, isHomogeneous_homogenize u,
    isHomogeneous_homogenize v, ?_⟩
  calc
    f = p.homogenize (2*d) := hhom.symm
    _ = (u.homogenize d)^2+(v.homogenize d)^2 := by
      rw [h, homogenize_add, two_mul, pow_two u, pow_two v,
        homogenize_mul u u hu hu, homogenize_mul v v hv hv, ← pow_two, ← pow_two]

end OMA.BinaryTwoSquares

theorem OMA.solution : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1_H2_R1.H1 := by
  intro d _ p hp hpos
  exact OMA.BinaryTwoSquares.binaryTwoSquares d p hp hpos
