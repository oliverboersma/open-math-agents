import OMAReductions.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1
import Mathlib

-- Step OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1.H2: hypothesis H2 of reduction OeisA218585.conjecture_4.R1.H2.R1.H1.R1.H1.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-!
A Dirichlet series whose coefficients vanish at the primes and are bounded by the von Mangoldt
function converges absolutely and uniformly on `1 ≤ re s`: its terms are bounded there by
`Λ n / n` restricted to non-primes, which is summable
(`ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div` with modulus `1`).
Continuity follows from the Weierstrass M-test.
-/

namespace OeisA218585StepCont

open ArithmeticFunction

lemma summable_nonprime : Summable fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (q := 1) (0 : ZMod 1)
  refine h.congr ?_
  intro n
  have hres : vonMangoldt.residueClass (0 : ZMod 1) n = Λ n :=
    Set.indicator_of_mem (show n ∈ {n : ℕ | (n : ZMod 1) = 0} from Subsingleton.elim _ _) _
  rw [hres]

theorem continuousOn_LSeries (b : ℕ → ℂ) (hb : ∀ p : ℕ, p.Prime → b p = 0)
    (hΛ : ∀ n, ‖b n‖ ≤ Λ n) : ContinuousOn (LSeries b) {s : ℂ | 1 ≤ s.re} := by
  have hb0 : b 0 = 0 := by
    have h := hΛ 0
    simpa using h
  show ContinuousOn (fun s : ℂ => ∑' n, LSeries.term b s n) {s : ℂ | 1 ≤ s.re}
  refine continuousOn_tsum (u := fun n : ℕ => (if n.Prime then 0 else Λ n) / (n : ℝ)) ?_
    summable_nonprime ?_
  · intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero]
      exact continuousOn_const
    · have e : (fun s : ℂ => LSeries.term b s n) = fun s : ℂ => b n * (n : ℂ) ^ (-s) := by
        funext s
        exact LSeries.term_def₀ hb0 s n
      rw [e]
      exact (continuous_const.mul
        (continuous_neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn)))).continuousOn
  · intro n s hs
    have hs' : 1 ≤ s.re := hs
    rw [LSeries.norm_term_eq]
    by_cases h0 : n = 0
    · subst h0
      simp
    · rw [if_neg h0]
      by_cases hp : n.Prime
      · rw [if_pos hp, hb n hp]
        simp
      · rw [if_neg hp]
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
        have hpow : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
          have := Real.rpow_le_rpow_of_exponent_le hn1 hs'
          rwa [Real.rpow_one] at this
        exact div_le_div₀ vonMangoldt_nonneg (hΛ n) (by linarith) hpow

end OeisA218585StepCont

theorem OMA.solution : OMA.R_OeisA218585_conjecture_4_R1_H2_R1_H1_R1_H1_R1.H2 :=
  fun b hb hL => OeisA218585StepCont.continuousOn_LSeries b hb hL
