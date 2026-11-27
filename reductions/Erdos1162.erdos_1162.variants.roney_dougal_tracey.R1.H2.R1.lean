import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R1
open Filter Real

/-- Passing from conjugacy representatives to all subgroups. -/
def H1 : Prop :=
  ∀ n : ℕ, ∀ R : Finset (Subgroup (Equiv.Perm (Fin n))),
    (∀ H : Subgroup (Equiv.Perm (Fin n)), ∃ K ∈ R, ∃ g : Equiv.Perm (Fin n),
      K.map (MulAut.conj g).toMonoidHom = H) →
    Erdos1162.f n ≤ R.card * n.factorial

/-- The permutation-group enumeration bound up to relabeling the underlying set. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∃ R : Finset (Subgroup (Equiv.Perm (Fin n))),
      (∀ H : Subgroup (Equiv.Perm (Fin n)), ∃ K ∈ R, ∃ g : Equiv.Perm (Fin n),
      K.map (MulAut.conj g).toMonoidHom = H) ∧
      logb 2 (R.card : ℝ) ≤ (1/16 + ε) * (n : ℝ)^2

theorem main : H1 → H2 → OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1.H2 := by
  intro orbit classes ε hε
  have l2 : 0 < log 2 := log_pos (by norm_num)
  have little := isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [classes (ε/2) (by positivity), little.bound (show 0 < ε/2 * log 2 by positivity),
    eventually_gt_atTop (0:ℕ)] with n hR hl hn
  obtain ⟨R,hrep,hcount⟩ := hR
  have hf := orbit n R hrep
  have hpos := Erdos1162.f_pos n
  have hRpos : 0 < R.card := Nat.pos_of_ne_zero (by intro h; simp [h] at hf; omega)
  have lh : log n ≤ ε/2 * log 2 * n := by
    change ‖log (n:ℝ)‖ ≤ ε/2 * log 2 * ‖(n:ℝ)‖ at hl
    rw [Real.norm_natCast] at hl
    exact (le_abs_self _).trans hl
  have lf : logb 2 (n.factorial : ℝ) ≤ ε/2 * (n:ℝ)^2 := by
    have ht : (n.factorial : ℝ) ≤ (n:ℝ)^n := by exact_mod_cast n.factorial_le_pow
    refine (logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (Nat.cast_pos.mpr n.factorial_pos) ht).trans ?_
    rw [logb_pow, logb, ← mul_div_assoc, div_le_iff₀ l2]
    nlinarith [mul_le_mul_of_nonneg_left lh (Nat.cast_nonneg (α := ℝ) n)]
  have hr : (Erdos1162.f n : ℝ) ≤ (R.card : ℝ)*n.factorial := by exact_mod_cast hf
  have h := logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (Nat.cast_pos.mpr hpos) hr
  rw [logb_mul (by positivity) (by exact_mod_cast n.factorial_ne_zero)] at h
  linarith

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R1
