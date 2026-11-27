import FormalConjectures.ErdosProblems.«733»

/-!
Between consecutive square indices, monotonicity traps the line-profile
count. The two square-root normalizations have ratio tending to one.
-/

open Erdos733 Filter Topology

namespace OMA.R_Erdos733_erdos_733_variants_limit_exists_R1

def H1 : Prop :=
  Monotone (fun n => (allLinesSequences n).ncard) ∧
    ∀ n, 0 < (allLinesSequences n).ncard

def H2 : Prop :=
  ∃ c : ℝ, Tendsto
    (fun k : ℕ => Real.log ((allLinesSequences (k * k)).ncard : ℝ) / (k : ℝ))
    atTop (𝓝 c)

section Proof

private theorem sqrt_atTop_nat : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.mpr
  intro m
  filter_upwards [eventually_ge_atTop (m * m)] with n hn
  exact Nat.le_sqrt.mpr hn

private theorem sqrt_bounds (n : ℕ) :
    (n.sqrt : ℝ) ≤ Real.sqrt n ∧ Real.sqrt n ≤ (n.sqrt : ℝ) + 1 := by
  refine ⟨Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n), ?_⟩
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  exact_mod_cast (Nat.lt_succ_sqrt' n).le

private theorem sqrt_ratio_lower :
    Tendsto (fun n : ℕ => (n.sqrt : ℝ) / Real.sqrt n) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hL : Tendsto (fun n : ℕ => 1 - (Real.sqrt n)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    apply (le_div_iff₀ hp).mpr
    rw [sub_mul, one_mul, inv_mul_cancel₀ hp.ne']
    linarith [(sqrt_bounds n).2]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hp : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    exact (div_le_one hp).mpr (sqrt_bounds n).1

private theorem sqrt_ratio_upper :
    Tendsto (fun n : ℕ => ((n.sqrt : ℝ) + 1) / Real.sqrt n) atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [add_div, one_div, add_zero] using sqrt_ratio_lower.add hi

theorem main : H1 → H2 → type_of% @Erdos733.erdos_733.variants.limit_exists := by
  rintro ⟨hmono, hpos⟩ ⟨c, hc⟩
  refine ⟨c, ?_⟩
  let f := fun n : ℕ => Real.log ((allLinesSequences n).ncard : ℝ)
  let a := fun k : ℕ => f (k * k) / (k : ℝ)
  have hF : Monotone f := by
    intro n m hn
    apply Real.log_le_log
    · exact_mod_cast hpos n
    · exact_mod_cast hmono hn
  change Tendsto (fun n : ℕ => f n / Real.sqrt n) atTop (𝓝 c)
  have hlow : Tendsto (fun n : ℕ => a n.sqrt * ((n.sqrt : ℝ) / Real.sqrt n)) atTop (𝓝 c) := by
    simpa only [Function.comp_apply, mul_one] using (hc.comp sqrt_atTop_nat).mul sqrt_ratio_lower
  have hup : Tendsto (fun n : ℕ => a (n.sqrt + 1) * (((n.sqrt : ℝ) + 1) / Real.sqrt n))
      atTop (𝓝 c) := by
    simpa only [Function.comp_apply, mul_one] using
      (hc.comp ((tendsto_add_atTop_nat 1).comp sqrt_atTop_nat)).mul sqrt_ratio_upper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hm : (n.sqrt : ℝ) ≠ 0 := by exact_mod_cast
      (Nat.sqrt_pos.mpr (by omega : 0 < n)).ne'
    have he : a n.sqrt * ((n.sqrt : ℝ) / Real.sqrt n) =
        f (n.sqrt * n.sqrt) / Real.sqrt n := by
      dsimp [a]
      field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (hF (Nat.sqrt_le n)) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hm : (n.sqrt : ℝ) + 1 ≠ 0 := by positivity
    have he : a (n.sqrt + 1) * (((n.sqrt : ℝ) + 1) / Real.sqrt n) =
        f ((n.sqrt + 1) * (n.sqrt + 1)) / Real.sqrt n := by
      dsimp [a]
      push_cast
      field_simp
    rw [he]
    exact div_le_div_of_nonneg_right (hF (Nat.lt_succ_sqrt n).le) (Real.sqrt_nonneg _)

end Proof

end OMA.R_Erdos733_erdos_733_variants_limit_exists_R1
