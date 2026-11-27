import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1
import Mathlib

/-! The real-zero case of Hilbert's theorem on ternary quartics, following the
coordinate expansion and discriminant in Pfister–Scheiderer, *An elementary
proof of Hilbert's theorem on ternary quartics*, §2 (arXiv:1009.3144).
Restricting the quartic to a line through the zero makes its first derivative
vanish. Completing the square reduces the problem to binary forms and
cancellation of a nonzero quadratic multiplier. -/
open MvPolynomial Finset
namespace Quartic17
lemma move {p : MvPolynomial (Fin 3) ℝ} (hp : p.IsHomogeneous 4)
    (pos : ∀ x, 0 ≤ eval x p) (v : Fin 3 → ℝ) (hv : v ≠ 0) (hz : eval v p=0) :
    ∃ f : MvPolynomial (Fin 3) ℝ, ∃ D : Fin 3 → MvPolynomial (Fin 3) ℝ,
      f.IsHomogeneous 4 ∧ (∀ x, 0 ≤ eval x f) ∧ eval (Fin.cons 1 (0 : Fin 2 → ℝ)) f=0 ∧
        aeval D f=p := by
  classical
  obtain ⟨k,hk⟩ : ∃ k, v k ≠ 0 := by contrapose! hv; ext i; exact hv i
  let e := Equiv.swap k (0 : Fin 3)
  have ek : e k=0 := Equiv.swap_apply_left _ _
  have ke : e.symm 0=k := e.symm_apply_eq.mpr ek.symm
  let W : Fin 3 → MvPolynomial (Fin 3) ℝ := Fin.cons 0 (fun i : Fin 2 => X i.succ)
  let L (j : Fin 3) : MvPolynomial (Fin 3) ℝ := C (v j)*X 0 + W (e j)
  let Z : MvPolynomial (Fin 3) ℝ := C (v k)⁻¹*X k
  let D : Fin 3 → MvPolynomial (Fin 3) ℝ := Fin.cons Z
    (fun i : Fin 2 => X (e.symm i.succ) - C (v (e.symm i.succ))*Z)
  have hW (i : Fin 3) : (W i).IsHomogeneous 1 := by
    refine Fin.cases (isHomogeneous_zero _ _ _) (fun j => isHomogeneous_X _ _) i
  have hL (j : Fin 3) : (L j).IsHomogeneous 1 := (isHomogeneous_C_mul_X _ _).add (hW _)
  let x0 : Fin 3 → ℝ := Fin.cons 1 (0 : Fin 2 → ℝ)
  have xW (i : Fin 3) : eval x0 (W i)=0 := by
    refine Fin.cases (by simp [W]) (fun j => by simp [W,x0]) i
  have xL (j : Fin 3) : aeval x0 (L j)=v j := by
    change eval x0 (C (v j)*X 0+W (e j)) = _
    simp [xW,x0]
  have back (j : Fin 3) : aeval D (L (e.symm j))=X (e.symm j) := by
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [L,ke,ek,W,D,Z]
      rw [←mul_assoc,←map_mul,mul_inv_cancel₀ hk,map_one,one_mul]
    · simp [L,W,D,Z]
  refine ⟨aeval L p,D,by simpa using hp.aeval L hL,?_,?_,?_⟩
  · intro x
    change 0 ≤ aeval x (aeval L p)
    rw [comp_aeval_apply]
    exact pos _
  · change aeval x0 (aeval L p)=0
    rw [comp_aeval_apply,show (fun i => aeval x0 (L i))=v from funext xL]
    exact hz
  · rw [comp_aeval_apply,show (fun i => aeval D (L i))=X by
      funext j; simpa using back (e j),aeval_X_left_apply]
end Quartic17
open MvPolynomial Finset
namespace Quartic17
lemma scale {n d : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d)
    (a : ℝ) (v : Fin n → ℝ) : eval (fun i ↦ a*v i) p = a^d * eval v p := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff]
  conv_rhs => rw [← p.support_sum_monomial_coeff]
  rw [map_sum,map_sum,mul_sum]
  apply sum_congr rfl
  intro u hu
  rw [eval_monomial,eval_monomial]
  simp only [Finsupp.prod,mul_pow,prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hu]
  ring

lemma tangent (a b c d : ℝ) (h : ∀ t : ℝ, 0 ≤ a*t+b*t^2+c*t^3+d*t^4) : a=0 := by
  let f : Polynomial ℝ := Polynomial.C a*Polynomial.X+Polynomial.C b*Polynomial.X^2+
    Polynomial.C c*Polynomial.X^3+Polynomial.C d*Polynomial.X^4
  have hm : IsLocalMin (fun t => f.eval t) 0 := Filter.Eventually.of_forall fun t => by
    simpa [f] using h t
  have he := hm.hasDerivAt_eq_zero (f.hasDerivAt 0)
  simpa [f,Polynomial.derivative_mul] using he

lemma coeffs (f : MvPolynomial (Fin 3) ℝ) (hf : f.IsHomogeneous 4)
    (hn : ∀ x, 0 ≤ eval x f) (hz : eval (Fin.cons 1 (0 : Fin 2 → ℝ)) f=0) :
    ∃ a b c : MvPolynomial (Fin 2) ℝ,
      a.IsHomogeneous 2 ∧ b.IsHomogeneous 3 ∧ c.IsHomogeneous 4 ∧
      finSuccEquiv ℝ 2 f = Polynomial.C a*Polynomial.X^2+Polynomial.C b*Polynomial.X+Polynomial.C c ∧
      (∀ x,0≤eval x a) ∧ (∀ x,0≤eval x c) ∧ (∀ x,0≤eval x (4*a*c-b^2)) := by
  classical
  let F := finSuccEquiv ℝ 2 f
  let c (i : ℕ) := F.coeff i
  have cd (i : ℕ) (hi : i ≤ 4) : (c i).IsHomogeneous (4-i) :=
    hf.finSuccEquiv_coeff_isHomogeneous i (4-i) (by omega)
  have ex : F = ∑ i ∈ range 5, Polynomial.C (c i)*Polynomial.X^i :=
    F.as_sum_range_C_mul_X_pow' (by
      have h := (degreeOf_le_totalDegree f 0).trans hf.totalDegree_le
      rw [←natDegree_finSuccEquiv] at h; exact Nat.lt_succ_of_le h)
  have value (z : ℝ) (x : Fin 2 → ℝ) : eval (Fin.cons z x) f =
      eval x (c 0)+eval x (c 1)*z+eval x (c 2)*z^2+eval x (c 3)*z^3+eval x (c 4)*z^4 := by
    rw [eval_eq_eval_mv_eval']
    change Polynomial.eval z (Polynomial.map (eval x) F)=_
    rw [ex]
    simp [Finset.sum_range_succ]
  have vanish (x : Fin 2 → ℝ) : eval x (c 4)=0 ∧ eval x (c 3)=0 := by
    have curve (t : ℝ) : eval (Fin.cons 1 (fun i => t*x i)) f =
        eval x (c 4)+eval x (c 3)*t+eval x (c 2)*t^2+eval x (c 1)*t^3+eval x (c 0)*t^4 := by
      rw [value,scale (cd 0 (by decide)),scale (cd 1 (by decide)),scale (cd 2 (by decide)),
        scale (cd 3 (by decide)),scale (cd 4 (by decide))]
      norm_num; ring
    have h0 := curve 0
    simp only [zero_mul,zero_pow (by decide : 2 ≠ 0),zero_pow (by decide : 3 ≠ 0),
      zero_pow (by decide : 4 ≠ 0),mul_zero,add_zero] at h0
    have z : eval x (c 4) = 0 := h0.symm.trans hz
    refine ⟨z,tangent _ (eval x (c 2)) (eval x (c 1)) (eval x (c 0)) (fun t => ?_)⟩
    have h := hn (Fin.cons 1 (fun i => t*x i))
    rwa [curve,z,zero_add] at h
  have z4 : c 4 = 0 := MvPolynomial.funext fun x => by simpa using (vanish x).1
  have z3 : c 3 = 0 := MvPolynomial.funext fun x => by simpa using (vanish x).2
  have pos (x : Fin 2 → ℝ) (z : ℝ) :
      0 ≤ eval x (c 2)*(z*z) + eval x (c 1)*z + eval x (c 0) := by
    have h := hn (Fin.cons z x)
    rw [value,z3,z4] at h
    simp only [map_zero,zero_mul,add_zero] at h
    linarith only [h]
  refine ⟨c 2,c 1,c 0,cd 2 (by decide),cd 1 (by decide),cd 0 (by decide),?_,?_,?_,?_⟩
  · change F=_
    conv_lhs => rw [ex]
    simp [sum_range_succ,z3,z4]; ring
  · intro x
    have one := discrim_le_zero (a:=eval x (c 2)) (b:=eval x (c 1)) (c:=eval x (c 0)+1)
      (fun z => by linarith only [pos x z])
    have cpos := pos x 0
    simp only [discrim] at one
    by_contra! h
    nlinarith only [one,sq_nonneg (eval x (c 1)),mul_neg_of_neg_of_pos h
      (by simpa using (show 0 < eval x (c 2)*(0*0)+eval x (c 1)*0+eval x (c 0)+1 by linarith) : 0<eval x (c 0)+1)]
  · intro x; simpa using pos x 0
  · intro x
    have h := discrim_le_zero (pos x)
    simpa [discrim,sq] using (sub_nonneg.mpr (sub_nonpos.mp h))
end Quartic17
namespace OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1_H2_R1
open MvPolynomial Finset Quartic17
open scoped Polynomial
/-- Nonnegative binary quartics and sextics are norms of complex forms. -/
def H1 : Prop := ∀ d : ℕ, d=2 ∨ d=3 → ∀ p : MvPolynomial (Fin 2) ℝ,
  p.IsHomogeneous (2*d) → (∀ x,0≤eval x p) → ∃ u v : MvPolynomial (Fin 2) ℝ,
   u.IsHomogeneous d ∧ v.IsHomogeneous d ∧ p=u^2+v^2

/-- Quadratic multiplier cancellation in Hilbert's three-square identity.
The coefficient of the free variable is a multiple of the factor to cancel,
and the remaining three forms are binary cubics. -/
def H2 : Prop := ∀ a b u v : MvPolynomial (Fin 2) ℝ,
    a.IsHomogeneous 2 → (∀ x,0≤eval x a) → a≠0 →
    b.IsHomogeneous 3 → u.IsHomogeneous 3 → v.IsHomogeneous 3 →
    ∀ F : Polynomial (MvPolynomial (Fin 2) ℝ),
    4*Polynomial.C a*F = (2*Polynomial.C a*Polynomial.X+Polynomial.C b)^2+
      (Polynomial.C u)^2+(Polynomial.C v)^2 →
    ∃ m : ℕ, ∃ g : Fin m → Polynomial (MvPolynomial (Fin 2) ℝ), F=∑ i,(g i)^2

theorem main : H1 → H2 → OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1.H2 := by
  classical
  rintro binary cancel p hp hn ⟨v,v0,zero⟩
  obtain ⟨f,D,hf,fn,fz,back⟩ := move hp hn v v0 zero
  obtain ⟨a,b,c,ha,hb,hc,form,an,cn,dn⟩ := coeffs f hf fn fz
  let F := finSuccEquiv ℝ 2 f
  have squares : ∃ m : ℕ, ∃ g : Fin m → Polynomial (MvPolynomial (Fin 2) ℝ), F=∑ i,(g i)^2 := by
    by_cases az : a=0
    · have bz : b=0 := MvPolynomial.funext fun x => by
        have h := dn x; simp [az] at h; simpa using h
      obtain ⟨u,v,_,_,eq⟩ := binary 2 (Or.inl rfl) c hc cn
      refine ⟨2,![Polynomial.C u, Polynomial.C v],?_⟩
      dsimp only [F]; rw [form,az,bz,eq]; simp [Fin.sum_univ_two]
    · have dh : (4*a*c-b^2).IsHomogeneous (2*3) := by
        apply IsHomogeneous.sub
        · simpa only [map_ofNat,mul_assoc] using (ha.mul hc).C_mul 4
        · simpa [sq] using hb.mul hb
      obtain ⟨u,v,hu,hv,eq⟩ := binary 3 (Or.inr rfl) _ dh dn
      apply cancel a b u v ha an az hb hu hv F
      have hcEq := congrArg (Polynomial.C : MvPolynomial (Fin 2) ℝ → Polynomial (MvPolynomial (Fin 2) ℝ)) eq
      simp only [map_sub,map_mul,map_add,map_pow,map_ofNat] at hcEq
      dsimp only [F]; rw [form]
      linear_combination hcEq
  obtain ⟨m,g,eq⟩ := squares
  let φ := (aeval D).comp (finSuccEquiv ℝ 2).symm.toAlgHom
  refine ⟨m,fun i => φ (g i),?_⟩
  calc
    p = φ F := by simpa [φ,F] using back.symm
    _ = _ := by rw [eq]; simp
end OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1_H2_R1
