import FormalConjectures.ErdosProblems.«710»
import Mathlib

/-! Erdős and Pomerance, Matching the natural numbers up to n with distinct
multiples in another interval (1980), Section 2. A shortage of smooth
multiples near a sparse sequence of endpoints obstructs a matching.
Restricting a matching to indices divisible by k transfers this obstruction
to every large n. The endpoint B below counts from zero, whereas f measures
an interval length. -/
namespace OMA.R_Erdos710_erdos_710_variants_lower_bound_R1

open Finset Filter Real Erdos710
open scoped Topology

/-- Sparse smooth-number windows from the de Bruijn estimate and the concave
majorant argument of Lemma 2. The witness size m is small compared with n. -/
def H1 : Prop := ∀ η : ℝ, 0 < η → η < 1 → ∀ᶠ n : ℕ in atTop,
  ∃ m y B : ℕ, 0 < m ∧ (m:ℝ) ≤ η*n ∧
    (1-η)*(2/√(exp 1))*m*√(log n / log (log n)) ≤ B ∧
    ((Ioc m B).filter (· ∈ Nat.smoothNumbers y)).card <
    ((Icc 1 m).filter (fun d => d ∈ Nat.smoothNumbers y ∧ B < d*y)).card

/-- A matching below B would inject the smooth sources into the smooth
targets: each complementary factor is less than y. -/
def H2 : Prop := ∀ m y B : ℕ, ((Ioc m B).filter (· ∈ Nat.smoothNumbers y)).card <
    ((Icc 1 m).filter (fun d => d ∈ Nat.smoothNumbers y ∧ B < d*y)).card → B ≤ m + f m

/-- Restriction to the indices k, 2k, ..., mk, followed by division by k.
The allowance 2n accounts for the two endpoints and rounding. -/
def H3 : Prop := ∀ n m k : ℕ, 0 < m → 0 < k → k*m ≤ n → k*f m ≤ f n + 2*n

private lemma scale_top : Tendsto (fun n : ℕ => √(log n/log (log n))) atTop atTop := by
  have h : Tendsto (fun x : ℝ => log x/x) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact div_pos (log_pos hx) (by linarith)
  have ht := Real.tendsto_sqrt_atTop.comp (h.inv_tendsto_nhdsGT_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  simpa [Function.comp_def,inv_div] using ht

theorem main : H1 → H2 → H3 → type_of% @Erdos710.erdos_710.variants.lower_bound := by
  intro sparse count dil ε hε
  let scale := fun n : ℕ => √(log n/log (log n))
  let C := 2/√(exp 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have cont : ContinuousAt (fun η : ℝ => (1-η)^2*C) 0 := by fun_prop
  have near : ∀ᶠ η in 𝓝[>] (0:ℝ), C-ε/2 < (1-η)^2*C :=
    (cont.tendsto.mono_left nhdsWithin_le_nhds).eventually_const_lt (by simp; linarith)
  have pos : ∀ᶠ η in 𝓝[>] (0:ℝ), 0 < η := self_mem_nhdsWithin
  have small : ∀ᶠ η in 𝓝[>] (0:ℝ), η < 1 := (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  obtain ⟨η, ⟨hp,hs⟩,hη⟩ := ((pos.and small).and near).exists
  filter_upwards [sparse η hp hs,scale_top.eventually_ge_atTop (6/ε),
    eventually_gt_atTop (0:ℕ)] with n hw hbig hn
  obtain ⟨m,y,B,hm,hsmall,hval,hshort⟩ := hw
  have hmn : m ≤ n := by
    have hmnR : (m:ℝ) ≤ n := hsmall.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.le (Nat.cast_nonneg n : (0:ℝ) ≤ n))
    exact_mod_cast hmnR
  let k := n/m
  have hk : 0 < k := Nat.div_pos hmn hm
  have hkm : k*m ≤ n := Nat.div_mul_le_self n m
  have hr := Nat.mod_lt n hm
  have hmod := Nat.mod_add_div n m
  have hremN : n ≤ k*m+m := by dsimp [k]; rw [Nat.mul_comm (n/m) m]; omega
  have hremR : (n:ℝ) ≤ k*(m:ℝ)+m := by exact_mod_cast hremN
  have hkfrac : (1-η)*(n:ℝ) ≤ k*(m:ℝ) := by linarith
  change (1-η)*C*(m:ℝ)*scale n ≤ B at hval
  change 6/ε ≤ scale n at hbig
  have hW : 0 ≤ scale n := Real.sqrt_nonneg _
  have hfac : 0 ≤ (1-η)*C*scale n := by positivity
  have hlow : (1-η)^2*C*n*scale n ≤ (k:ℝ)*B := by
    have hy := mul_le_mul_of_nonneg_right hkfrac hfac
    have hz := mul_le_mul_of_nonneg_left hval (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    calc
      _ = ((1-η)*(n:ℝ))*((1-η)*C*scale n) := by ring
      _ ≤ ((k:ℝ)*m)*((1-η)*C*scale n) := hy
      _ = (k:ℝ)*((1-η)*C*m*scale n) := by ring
      _ ≤ _ := hz
  have hiN : k*B ≤ f n + 3*n := by
    have h₁ := Nat.mul_le_mul_left k (count m y B hshort)
    rw [Nat.mul_add] at h₁
    have h₂ := dil n m k hm hk hkm
    omega
  have hhi : (k:ℝ)*B ≤ f n + 3*(n:ℝ) := by exact_mod_cast hiN
  have hloss := (div_le_iff₀ hε).mp hbig
  have ht := mul_le_mul_of_nonneg_right hη.le (mul_nonneg (Nat.cast_nonneg n) hW)
  change (C-ε)*n*scale n ≤ f n
  linarith only [hlow,hhi,ht,mul_le_mul_of_nonneg_right hloss (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

end OMA.R_Erdos710_erdos_710_variants_lower_bound_R1
