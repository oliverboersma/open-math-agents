import OMAReductions.R_Erdos230_erdos_230_variants_ultraflat_R1
import Mathlib

/-! Exponential moment averaging over all sign vectors. For each j, the sum over sign
vectors of exp(t X_j) factors as a product over k of exp(t w) + exp(-t w) = 2 cosh(t w),
which is at most 2 exp((t w)^2/2). Summing over j, some sign vector has total at most
card J times exp(t^2 V/2), and taking logarithms gives the bound for every j. -/

open Finset Real

namespace OMA.P2b230

theorem pair_le (x : ℝ) : Real.exp x + Real.exp (-x) ≤ 2 * Real.exp (x ^ 2 / 2) := by
  have h := Real.cosh_le_exp_half_sq x
  rw [Real.cosh_eq] at h
  linarith

theorem col (n : ℕ) (v : Fin n → ℝ) (t : ℝ) :
    ∑ s : Fin n → Bool, Real.exp (t * ∑ k, (if s k then (1:ℝ) else -1) * v k) ≤
      2 ^ n * Real.exp (t ^ 2 * (∑ k, v k ^ 2) / 2) := by
  have h1 : ∀ s : Fin n → Bool, Real.exp (t * ∑ k, (if s k then (1:ℝ) else -1) * v k) =
      ∏ k, Real.exp (t * ((if s k then (1:ℝ) else -1) * v k)) := by
    intro s
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun k (b : Bool) => Real.exp (t * ((if b then (1:ℝ) else -1) * v k)))]
  have h2 : ∀ k, ∑ b : Bool, Real.exp (t * ((if b then (1:ℝ) else -1) * v k)) ≤
      2 * Real.exp ((t * v k) ^ 2 / 2) := by
    intro k
    rw [Fintype.sum_bool]
    simp only [if_true, Bool.false_eq_true, if_false]
    have := pair_le (t * v k)
    have e1 : t * (1 * v k) = t * v k := by ring
    have e2 : t * (-1 * v k) = -(t * v k) := by ring
    rw [e1, e2]
    exact this
  calc ∏ k, ∑ b : Bool, Real.exp (t * ((if b then (1:ℝ) else -1) * v k))
      ≤ ∏ k, 2 * Real.exp ((t * v k) ^ 2 / 2) :=
        Finset.prod_le_prod (fun k _ => Finset.sum_nonneg (fun b _ => (Real.exp_pos _).le))
          (fun k _ => h2 k)
    _ = 2 ^ n * Real.exp (t ^ 2 * (∑ k, v k ^ 2) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← Real.exp_sum]
        congr 2
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        ring

theorem sol : OMA.R_Erdos230_erdos_230_variants_ultraflat_R1.H2 := by
  unfold OMA.R_Erdos230_erdos_230_variants_ultraflat_R1.H2
  intro n J _ _ w V t ht hV
  let B : ℝ := Real.exp (t ^ 2 * V / 2)
  have hj : ∀ j, ∑ s : Fin n → Bool, Real.exp (t * ∑ k, (if s k then (1:ℝ) else -1) * w j k) ≤
      2 ^ n * B := by
    intro j
    refine (col n (w j) t).trans ?_
    show _ ≤ 2 ^ n * Real.exp (t ^ 2 * V / 2)
    have := hV j
    gcongr
  have htot : ∑ s : Fin n → Bool, ∑ j, Real.exp (t * ∑ k, (if s k then (1:ℝ) else -1) * w j k) ≤
      ∑ s : Fin n → Bool, (Fintype.card J : ℝ) * B := by
    rw [Finset.sum_comm]
    calc ∑ j, ∑ s : Fin n → Bool, Real.exp (t * ∑ k, (if s k then (1:ℝ) else -1) * w j k)
        ≤ ∑ j : J, 2 ^ n * B := Finset.sum_le_sum (fun j _ => hj j)
      _ = ∑ s : Fin n → Bool, (Fintype.card J : ℝ) * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_bool,
          Finset.prod_const, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  obtain ⟨s, -, hs⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty htot
  refine ⟨s, fun j => ?_⟩
  have hle : Real.exp (t * ∑ k, (if s k then (1:ℝ) else -1) * w j k) ≤ (Fintype.card J : ℝ) * B :=
    le_trans (Finset.single_le_sum (f := fun j => Real.exp (t * ∑ k, (if s k then (1:ℝ) else -1) * w j k))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ j)) hs
  have hcard : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have := Real.log_le_log (Real.exp_pos _) hle
  rw [Real.log_exp, Real.log_mul hcard.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  exact this

end OMA.P2b230

theorem OMA.solution : OMA.R_Erdos230_erdos_230_variants_ultraflat_R1.H2 := OMA.P2b230.sol
