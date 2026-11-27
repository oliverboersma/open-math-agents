import FormalConjectures.ErdosProblems.«3»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Erdos3_erdos_3_variants_gowers_R1
open Erdos3 Filter Real Asymptotics

/-- The stronger Leng–Sah–Sawhney quantitative Szemerédi bound in lengths at least five. -/
def H1 : Prop := ∀ l : ℕ, 5 ≤ l → ∃ c > (0 : ℝ),
  (fun N ↦ (r l N : ℝ)) =O[atTop] fun N : ℕ ↦
    (N : ℝ) * exp (-(log (log N) ^ c))

/-- Truncating progressions makes the extremal density monotone in the length. -/
def H2 : Prop := ∀ k l N : ℕ, 2 ≤ k → k ≤ l → r k N ≤ r l N

/-- A stretched exponential saves any fixed power at infinity. -/
def H3 : Prop := ∀ c a : ℝ, 0 < c → 0 < a →
  ∀ᶠ t : ℝ in atTop, exp (-(t^c)) ≤ t ^ (-a)

theorem main : H1 → H2 → H3 → type_of% @Erdos3.erdos_3.variants.gowers := by
  intro bound mono decay k hk
  obtain ⟨c,hc,upper⟩ := bound (max 5 k) (le_max_left ..)
  refine ⟨1,zero_lt_one,?_⟩
  have first : (fun N : ℕ ↦ (r k N : ℝ)) =O[atTop] (fun N : ℕ ↦ (r (max 5 k) N : ℝ)) := by
    apply IsBigO.of_bound'
    filter_upwards with n
    simp only [Real.norm_natCast]
    exact_mod_cast mono k _ n (by omega) (le_max_right ..)
  refine (first.trans upper).trans (IsBigO.of_bound' ?_)
  have tend : Tendsto (fun n : ℕ ↦ log (log (n : ℝ))) atTop atTop :=
    tendsto_log_atTop.comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [tend.eventually (decay c 1 hc zero_lt_one), tend.eventually (eventually_gt_atTop 0)]
    with n h hp
  simp only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (exp_pos _).le),
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hp.le _))]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

end OMA.R_Erdos3_erdos_3_variants_gowers_R1
