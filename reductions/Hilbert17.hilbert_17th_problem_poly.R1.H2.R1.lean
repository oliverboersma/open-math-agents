import OMAReductions.R_Hilbert17_hilbert_17th_problem_poly_R1
import Mathlib
-- Credit: @marcusbuffett
/-! Diagonalize nonnegative quadratic forms, and subtract a maximal square of the Euclidean norm from a ternary quartic to produce a real zero. -/
namespace OMA.R_Hilbert17_hilbert_17th_problem_poly_R1_H2_R1
open Finset MvPolynomial Hilbert17
open scoped Classical
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
      simp [Q,QuadraticMap.sum_apply,QuadraticMap.proj_apply,mul_assoc]
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
  simp only [map_pow,map_mul,eval_C,ev,mul_pow,Real.sq_sqrt (weights i),smul_eq_mul,sq] <;>
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
  have ne : S.Nonempty := ⟨EuclideanSpace.single 0 1,by simp [S,Metric.mem_sphere,EuclideanSpace.norm_single]⟩
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
    have zs : z ∈ S := by simp [S,Metric.mem_sphere,z,norm_smul,Real.norm_eq_abs,abs_of_nonneg xp.le,xp.ne']
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
