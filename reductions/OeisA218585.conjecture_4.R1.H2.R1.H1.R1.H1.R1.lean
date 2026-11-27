import OMAReductions.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1
import Mathlib

/-! For the incomplete Eisenstein Hecke L-function, the two conjugate
prime ideals above a split prime give twice the angular cosine. The
remaining prime-power terms converge uniformly on the closed half-plane. -/
namespace OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1

open OeisA218585 Real ArithmeticFunction
open scoped Classical

/-- Analyticity and nonvanishing of the incomplete Hecke L-function of
nonzero angular type, together with its logarithmic Euler expansion.
The factor at the ramified prime three is omitted. -/
def H1 : Prop :=
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  ∀ k : ℕ, k ≠ 0 → ∃ (L : ℂ → ℂ) (a : ℕ → ℂ),
    (∀ s : ℂ, 1 ≤ s.re → AnalyticAt ℂ L s ∧ L s ≠ 0) ∧
    (∀ n, ‖a n‖ ≤ Λ n) ∧
    (∀ p : ℕ, p.Prime → a p = ((Λ p * (if p%3=1 then cos ((k:ℝ)*(6*(z p).arg))
      else 0) : ℝ) : ℂ)) ∧
    ∀ s : ℂ, 1 < s.re → LSeries a s = -deriv L s / (2*L s)

/-- Absolute convergence on the closed boundary for the higher prime powers. -/
def H2 : Prop := ∀ b : ℕ → ℂ, (∀ p : ℕ, p.Prime → b p=0) → (∀ n, ‖b n‖ ≤ Λ n) →
  ContinuousOn (LSeries b) {s : ℂ | 1 ≤ s.re}

lemma dominated_series {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ Λ n) {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable a s := by
  apply Summable.of_norm_bounded (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  intro n
  apply LSeries.norm_term_le
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg vonMangoldt_nonneg] using ha n

theorem main : H1 → H2 → OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1.H1 := by
  intro hecke power k hk e _he
  obtain ⟨L,a,hL,ha,hp,logder⟩ := hecke k hk
  let z (p : ℕ) : ℂ := ⟨(xp p : ℝ) + (yp p : ℝ) / 2, √3 * (yp p : ℝ) / 2⟩
  let w (n : ℕ) := if n.Prime ∧ n%3=1 then cos ((k:ℝ)*(6*(z n).arg)) else 0
  let b (n : ℕ) : ℂ := if n.Prime then 0 else a n
  let v (n : ℕ) : ℂ := (Λ n : ℝ)
  have hb n : ‖b n‖ ≤ Λ n := by dsimp [b]; split <;> simp_all only [norm_zero,vonMangoldt_nonneg]
  have H := power b (fun p h => by simp [b,h]) hb
  let F := vonMangoldt.LFunctionResidueClassAux (q:=1) 1
  have fC : ContinuousOn F {s : ℂ | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have lC : ContinuousOn L {s : ℂ | 1 ≤ s.re} := fun s hs => (hL s hs).1.continuousAt.continuousWithinAt
  have dC : ContinuousOn (deriv L) {s : ℂ | 1 ≤ s.re} := fun s hs =>
    (hL s hs).1.deriv.continuousAt.continuousWithinAt
  refine ⟨fun s => F s + (e:ℂ)*(-deriv L s/(2*L s)-LSeries b s), ?_, ?_⟩
  · exact fC.add (continuousOn_const.mul (((dC.neg.div (continuousOn_const.mul lC)
      (fun s hs => mul_ne_zero (by norm_num) (hL s hs).2))).sub H))
  intro s hs
  have hs' : 1<s.re := hs
  have fId : F s = LSeries v s - 1/(s-1) := by
    have old := vonMangoldt.eqOn_LFunctionResidueClassAux (q:=1) isUnit_one hs'
    rw [show F s = _ from old]
    simp only [Nat.totient_one,Nat.cast_one,inv_one,sub_left_inj]
    apply LSeries_congr
    intro n _
    simp [v,vonMangoldt.residueClass,Subsingleton.elim (n:ZMod 1) (1:ZMod 1)]
  have vSumm : LSeriesSummable v s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs'
  have aSumm := dominated_series ha hs'
  have bSumm := dominated_series hb hs'
  have recombine : (fun n => ((Λ n*(1+e*w n):ℝ):ℂ)) = v + (e:ℂ) • (a-b) := by
    funext n
    simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,v,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one]
    by_cases hn : n.Prime
    · rw [hp n hn]
      by_cases hm : n%3=1 <;> simp [w,b,hn,hm,z] <;> ring
    · simp [w,b,hn]
  change F s + (e:ℂ)*(-deriv L s/(2*L s)-LSeries b s) =
    LSeries (fun n => ((Λ n*(1+e*w n):ℝ):ℂ)) s - 1/(s-1)
  rw [recombine,LSeries_add vSumm ((aSumm.sub bSumm).smul _),LSeries_smul,
    LSeries_sub aSumm bSumm,fId,logder s hs']
  ring

end OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1
