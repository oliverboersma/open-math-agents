import FormalConjectures.HilbertProblems.«17»
import Mathlib

/-!
# Hilbert's classification of nonnegative homogeneous real forms

Formalization and assembly by Hanan Beer with Codex assistance.
The classification is classical; this file assembles complete Lean proofs.

Credits retained from the source contributions:
* @ihateSAS: outer implication reduction, PR4594.
* @marcusbuffett: negative classification, PR4925, and positive-case reduction, PR4945.
* @philipsaint: Motzkin nonsquareness proof adapted in PR4925.
* Mathlib contributors: algebraic, analytic and quadratic-form infrastructure.
The binary and real-zero ternary constructions are formalized by Hanan Beer.
The ternary argument follows Pfister–Scheiderer, arXiv:1009.3144, Sections 1–2.
-/
section PriorCases



-- Reduction Hilbert17.hilbert_17th_problem_poly.R1 of Hilbert's 17th problem for homogeneous
-- polynomials
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-
# The polynomial side of Hilbert's 17th problem, split into its two implications

A homogeneous polynomial of degree `2 * d` in `n` variables that is nonnegative on all of `ℝⁿ`
need not be a sum of squares of polynomials.  Hilbert classified exactly when it is:

`Hilbert17thProblemHomogenousPoly n d` holds if and only if
`n = 1 ∨ n = 2 ∨ d = 1 ∨ (n = 3 ∧ d = 2)`.

The two directions are of completely different nature, so they are separated here:

* `H1` is the *negative* direction: outside those parameters there is a nonnegative homogeneous
  polynomial that is not a sum of squares of polynomials.  Concretely the Motzkin polynomial
  `x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1` (already in the file as `Hilbert17.f`)
  after homogenization rules out `n = 3`, `d = 3`, and rescalings/embeddings of it rule out the rest of the complement.

* `H2` is the *positive* direction, Hilbert's theorem itself: in dimensions `n ≤ 2`, in degree
  `2` (`d = 1`), and for ternary quartics (`n = 3`, `d = 2`), every nonnegative homogeneous
  polynomial is a sum of squares of polynomials.

Neither direction implies the other, and neither is a formal consequence of the statement: `H1`
produces nonnegative non-sos forms, `H2` is an existence theorem for sos representations.
-/

namespace OMA.R_Hilbert17_hilbert_17th_problem_poly_R1

/-- The negative direction: if every nonnegative homogeneous polynomial of degree `2 * d` in `n`
variables is a sum of squares of polynomials, then `(n, d)` is one of the Hilbert cases. -/
def H1 : Prop :=
  ∀ {n d : ℕ}, 0 < n → 0 < d →
    Hilbert17.Hilbert17thProblemHomogenousPoly n d →
      (n = 1 ∨ n = 2 ∨ d = 1 ∨ n = 3 ∧ d = 2)

/-- The positive direction, Hilbert's theorem: for `n ≤ 2`, for `d = 1`, and for ternary quartics,
every nonnegative homogeneous polynomial is a sum of squares of polynomials. -/
def H2 : Prop :=
  ∀ {n d : ℕ}, 0 < n → 0 < d →
    (n = 1 ∨ n = 2 ∨ d = 1 ∨ n = 3 ∧ d = 2) →
      Hilbert17.Hilbert17thProblemHomogenousPoly n d

theorem main : H1 → H2 →
    type_of% @Hilbert17.hilbert_17th_problem_poly :=
  fun h1 h2 {_n _d} hn hd => ⟨h1 hn hd, h2 hn hd⟩

end OMA.R_Hilbert17_hilbert_17th_problem_poly_R1
-- Credit: @marcusbuffett
/- Diagonalize nonnegative quadratic forms, and subtract a maximal square of the Euclidean norm from a ternary quartic to produce a real zero. -/
namespace OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1
open Finset MvPolynomial Hilbert17
private lemma quadAsForm {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous 2) :
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

private lemma quadraticSOS (n : ℕ) : Hilbert17thProblemHomogenousPoly n 1 := by
  classical
  intro p hp hpos
  obtain ⟨Q,hQ⟩ := quadAsForm p hp
  obtain ⟨w,⟨e⟩⟩ := Q.equivalent_weightedSumSquares
  let k := Module.finrank ℝ (Fin n → ℝ)
  have weights (i : Fin k) : 0 ≤ w i := by
    let y : Fin k → ℝ := Pi.single i 1
    have pos := hpos (e.toLinearEquiv.symm y)
    rw [← hQ, ← e.map_app] at pos
    change 0 ≤ QuadraticMap.weightedSumSquares ℝ w (e.toLinearEquiv (e.toLinearEquiv.symm y)) at pos
    simpa [y,QuadraticMap.weightedSumSquares_apply,Pi.single_apply] using pos
  let P (i : Fin k) : MvPolynomial (Fin n) ℝ := ∑ j, C ((e (Pi.single j 1)) i) * X j
  have ev (i : Fin k) (x : Fin n → ℝ) : eval x (P i) = e x i := by
    have hx : ∑ j : Fin n, (x j) • (Pi.single j (1 : ℝ)) = x := by
      ext j; simp [Finset.sum_apply, Pi.single_apply,smul_eq_mul]
    calc
      _ = ∑ j, x j * e (Pi.single j 1) i := by simp [P,mul_comm]
      _ = e (∑ j : Fin n, (x j) • (Pi.single j (1:ℝ))) i := by simp [Finset.sum_apply,smul_eq_mul]
      _ = _ := by rw [hx]
  refine ⟨k,fun i ↦ C (Real.sqrt (w i)) * P i, MvPolynomial.funext fun x ↦ ?_⟩
  rw [← hQ x, ← e.map_app,QuadraticMap.weightedSumSquares_apply,map_sum]
  apply sum_congr rfl
  intro i _
  simp only [map_mul,eval_C,ev,smul_eq_mul,sq]
  nlinarith only [congrArg (fun z : ℝ ↦ z*(e x i)^2) (Real.sq_sqrt (weights i))]

private lemma homogeneousScale {n d : ℕ} {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous d)
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

private lemma ternaryReduce
    (hz : ∀ p : MvPolynomial (Fin 3) ℝ, p.IsHomogeneous 4 → (∀ x, 0 ≤ eval x p) →
      (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ eval v p = 0) → ∃ m : ℕ, ∃ g : Fin m → MvPolynomial (Fin 3) ℝ, p = ∑ i, (g i)^2) :
    Hilbert17thProblemHomogenousPoly 3 2 := by
  classical
  intro p hp hpos
  let F := fun x : EuclideanSpace ℝ (Fin 3) ↦ eval (fun i ↦ x i) p
  let S : Set (EuclideanSpace ℝ (Fin 3)) := Metric.sphere 0 1
  have ne : S.Nonempty := ⟨EuclideanSpace.single 0 1,by simp [S]⟩
  have con : Continuous F := p.continuous_eval.comp (PiLp.continuous_ofLp 2 (fun _ : Fin 3 ↦ ℝ))
  obtain ⟨y,hy,hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).exists_isMinOn ne con.continuousOn
  have ynorm : ‖y‖ = 1 := by simpa [S,Metric.mem_sphere] using hy
  let c := F y
  have cp : 0 ≤ c := hpos _
  let r : MvPolynomial (Fin 3) ℝ := ∑ i : Fin 3, (X i)^2
  have hr : r.IsHomogeneous 2 := MvPolynomial.IsHomogeneous.sum _ _ _ (fun _ _ ↦ isHomogeneous_X_pow _ _)
  let g := p-C c*r^2
  have hg : g.IsHomogeneous 4 := hp.sub ((hr.pow 2).C_mul c)
  have er (x : EuclideanSpace ℝ (Fin 3)) : eval (fun i ↦ x i) r = ‖x‖^2 := by simp [r,EuclideanSpace.real_norm_sq_eq]
  have eg (x : EuclideanSpace ℝ (Fin 3)) : eval (fun i ↦ x i) g = F x - c*‖x‖^4 := by simp only [g,map_sub,map_mul,map_pow,eval_C,er,F]; ring
  have pg (v : Fin 3 → ℝ) : 0 ≤ eval v g := by
    let x : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 v
    change 0 ≤ eval (fun i ↦ x i) g
    rw [eg]
    by_cases hx : x = 0
    · rw [hx]; simp; exact hpos _
    have xp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let z := ‖x‖⁻¹ • x
    have zs : z ∈ S := by simp [S,z,norm_smul,xp.ne']
    have le : c ≤ F z := hmin zs
    have scale : F z = ‖x‖⁻¹^4*F x := homogeneousScale hp _ _
    rw [scale,inv_pow, inv_mul_eq_div] at le
    exact sub_nonneg.mpr ((le_div_iff₀ (pow_pos xp 4)).mp le)
  have zy : eval (fun i ↦ y i) g = 0 := by rw [eg,ynorm]; simp [c]
  have yn : (fun i ↦ y i) ≠ 0 := by
    intro he
    have ey : y = 0 := by ext i; exact congrFun he i
    simp [ey] at ynorm
  obtain ⟨m,t,eq⟩ := hz g hg pg ⟨_,yn,zy⟩
  refine ⟨m+1,Fin.cons (C √c*r) t, ?_⟩
  simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,← eq,mul_pow,← map_pow,Real.sq_sqrt cp,g]
  ring

def H1 : Prop := ∀ d : ℕ, 0 < d → Hilbert17thProblemHomogenousPoly 2 d

def H2 : Prop := ∀ p : MvPolynomial (Fin 3) ℝ, p.IsHomogeneous 4 → (∀ x, 0 ≤ eval x p) →
      (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ eval v p = 0) → ∃ m : ℕ, ∃ g : Fin m → MvPolynomial (Fin 3) ℝ, p = ∑ i, (g i)^2

theorem main : H1 → H2 → OMA.R_Hilbert17_hilbert_17th_problem_poly_R1.H2 := by
  intro bin quart n d _ hd h
  rcases h with rfl|rfl|rfl|⟨rfl,rfl⟩
  · let e := Fin.castLE (by decide : 1 ≤ 2)
    intro p hp hpos
    obtain ⟨k,g,eq⟩ := bin d hd (rename e p) hp.rename_isHomogeneous (fun x ↦ by rw [eval_rename]; exact hpos _)
    have inj : Function.Injective e := Fin.castLE_injective _
    refine ⟨k,fun i ↦ killCompl inj (g i),?_⟩
    have he := congrArg (killCompl (R := ℝ) inj) eq
    simpa only [killCompl_rename_app,map_sum,map_pow] using he
  · exact bin d hd
  · exact quadraticSOS n
  · exact ternaryReduce quart
end OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1

-- Credit: @marcusbuffett
/- Hilbert’s negative classification follows from the homogenized Motzkin sextic and the Choi–Lam quartic. For the quartic, extract the quadratic part of a putative square on each of eight lines. -/
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
  simp only [Polynomial.finsetSum_coeff, sq, Polynomial.mul_coeff_zero] at h0
  norm_num at h0
  have z0 (i) : (g i).coeff 0 = 0 := zero_of_squares _ (by simpa [sq] using h0) i
  have h2 := congrArg (fun p : ℝ[X] ↦ p.coeff 2) h
  simp only [Polynomial.finsetSum_coeff,sq,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h2
  norm_num [sum_range_succ,z0] at h2
  have z1 (i) : (g i).coeff 1 = 0 := zero_of_squares _ (by simpa [sq] using h2) i
  have h4 := congrArg (fun p : ℝ[X] ↦ p.coeff 4) h
  simp only [Polynomial.finsetSum_coeff,sq,Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h4
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
      unfold mot; field_simp
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
theorem OMA.negative_case : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1.H1 := by
  intro n d hn hd H
  by_contra! h
  by_cases h3 : 3 ≤ d
  · exact notSextic h3 (restrictForms (by decide : 0 < 3) (by omega) H)
  · have d2 : d = 2 := by omega
    subst d
    exact notQuartic (restrictForms (by decide : 0 < 4) (by omega) H)

end PriorCases



/-
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

theorem OMA.ternary_case : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1.H2 :=
  TernarySOSAssembly.ternary_quartic

-- The binary-form case, with its complete proof above.
theorem OMA.binary_case : OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1.H1 :=
  BinaryHomogeneous.binary_of_univariate
    (BinarySOSInduction.two_squares_of_quadratic_factor BinarySOS.factor_nonnegative)

/-- Hilbert's complete classification for positive numbers of variables and half-degrees. -/
theorem OMA.solution : type_of% @Hilbert17.hilbert_17th_problem_poly :=
  OMA.R_Hilbert17_hilbert_17th_problem_poly_R1.main OMA.negative_case
    (OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1.main
      OMA.binary_case OMA.ternary_case)
