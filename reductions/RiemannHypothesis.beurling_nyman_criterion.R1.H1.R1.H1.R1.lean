import OMAReductions.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1
import Mathlib

/-! Báez-Duarte's strong criterion uses unconstrained reciprocal-integer
dilations on the positive half-line (arXiv:math/0205003). Beyond one, their
linear combination is exactly its first moment divided by x. Thus its
half-line error controls both the restricted error and the cost of adding
a single parameter 1 to enforce the catalogue's zero-moment constraint. -/
namespace OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1_H1_R1
open RiemannHypothesis MeasureTheory Set
open scoped ENNReal

/-- Positive-half-line approximation by reciprocal-integer dilations. -/
def H1 : Prop := RiemannHypothesis → ∀ ε : ℝ, 0<ε → ∃ n : ℕ, ∃ c : Fin n → ℝ,
  eLpNorm (fun x : ℝ => (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x -
    ∑ i, c i * fractScalarInv (1 / ((i.val:ℝ)+1)) x) 2 (volume.restrict (Ioi 0)) < ENNReal.ofReal ε

/-- Restriction to (0,1] and the tail on (1,2] control the local error and first moment. -/
def H2 : Prop := ∀ (n : ℕ) (c : Fin n → ℝ),
  let θ := fun i : Fin n => 1/((i.val:ℝ)+1)
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  let one := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1:ℝ)
  let E := eLpNorm (fun x : ℝ => (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x -
    ∑ i, c i * fractScalarInv (θ i) x) 2 (volume.restrict (Ioi 0))
  E ≠ ⊤ → dist one (fractScalarInvSumL2 n c θ) + |∑ i, c i*θ i| ≤ 3*E.toReal

theorem main : H1 → H2 → OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1.H1 := by
  intro approx control rh
  apply Metric.mem_closure_iff.mpr
  intro ε epos
  let μ := volume.restrict (Ioc (0:ℝ) 1)
  let one := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1:ℝ)
  let g := (fractScalarInv_memLp2 1).toLp _
  let δ := ε / (4*(1+‖g‖))
  have dp : 0<δ := div_pos epos (by positivity)
  obtain ⟨n,c,hc⟩ := approx rh δ dp
  let θ := fun i : Fin n => 1/((i.val:ℝ)+1)
  let y := fractScalarInvSumL2 n c θ
  let m := ∑ i, c i*θ i
  let E := eLpNorm (fun x : ℝ => (Ioc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x -
    ∑ i, c i * fractScalarInv (θ i) x) 2 (volume.restrict (Ioi 0))
  change E < ENNReal.ofReal δ at hc
  have fin : E ≠ ⊤ := (hc.trans_le le_top).ne
  have hδ : E.toReal < δ := by
    simpa [ENNReal.toReal_ofReal dp.le] using
      (ENNReal.toReal_lt_toReal fin ENNReal.ofReal_ne_top).mpr hc
  have bound : dist one y + |m| ≤ 3*E.toReal := control n c fin
  let cs : Fin (n+1) → ℝ := Fin.cons (-m) c
  let ts : Fin (n+1) → ℝ := Fin.cons 1 θ
  refine ⟨fractScalarInvSumL2 (n+1) cs ts, ⟨n+1,cs,ts,?_,?_,rfl⟩,?_⟩
  · intro i
    refine Fin.cases (by simp [ts]) (fun j => ?_) i
    change 0<1/((j.val:ℝ)+1) ∧ 1/((j.val:ℝ)+1)≤1
    constructor
    · positivity
    · apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) j.val]
  · simp [cs,ts,Fin.sum_univ_succ,m]
  · have ident : fractScalarInvSumL2 (n+1) cs ts = y+(-m) • g := by
      simp [fractScalarInvSumL2,cs,ts,Fin.sum_univ_succ,y,g] <;> abel
    change dist one (fractScalarInvSumL2 (n+1) cs ts) < ε
    rw [ident]
    have tri := dist_triangle one y (y+(-m) • g)
    have dd : dist y (y+(-m) • g) = abs m * ‖g‖ := by simp [dist_eq_norm,norm_smul]
    rw [dd] at tri
    have hb : dist one y+|m| < 3*δ := by linarith
    have hp := mul_lt_mul_of_pos_right hb (show 0<1+‖g‖ by positivity)
    have de : δ*(4*(1+‖g‖))=ε := by
      dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_nonneg (dist_nonneg : 0≤dist one y) (norm_nonneg g),abs_nonneg m,
      mul_pos dp (show 0<1+‖g‖ by positivity)]
end OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1_H1_R1_H1_R1
