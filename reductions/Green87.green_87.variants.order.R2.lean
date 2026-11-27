import FormalConjectures.GreensOpenProblems.«87»
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Filter Asymptotics Green87
open scoped Topology BigOperators

namespace OMA.R_Green87_green_87_variants_order_R2

/-- Proposition 1.3 of Eberhard, Ford and Green. The series divided by k
is the expected number of distinct subset sums for independent Poisson
cycle counts of means 1 through 1/k, divided by k. -/
def H1 : Prop :=
  let mass : ℕ → ℝ := fun k ↦
    (∑' a : Fin k → ℕ,
      ((Finset.univ.image (fun b : (j : Fin k) → Fin (a j + 1) ↦
        ∑ j, (j.val + 1) * (b j).val)).card : ℝ) *
      ∏ j : Fin k, Real.exp (-(1 / ((j.val + 1 : ℕ) : ℝ))) /
        ((a j).factorial * (((j.val + 1 : ℕ) : ℝ) ^ a j))) / (k : ℝ)
  ∃ C c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, 2 * k ≤ n →
    ‖i n k‖ ≤ C * ‖mass k‖ ∧ c * ‖mass k‖ ≤ ‖i n k‖

/-- Proposition 1.4 of Eberhard, Ford and Green, normalized by k. -/
def H2 : Prop :=
  let mass : ℕ → ℝ := fun k ↦
    (∑' a : Fin k → ℕ,
      ((Finset.univ.image (fun b : (j : Fin k) → Fin (a j + 1) ↦
        ∑ j, (j.val + 1) * (b j).val)).card : ℝ) *
      ∏ j : Fin k, Real.exp (-(1 / ((j.val + 1 : ℕ) : ℝ))) /
        ((a j).factorial * (((j.val + 1 : ℕ) : ℝ) ^ a j))) / (k : ℝ)
  mass =Θ[atTop] fun k : ℕ ↦ (k : ℝ) ^ (-δ) * (1 + Real.log k) ^ (-(3 / 2 : ℝ))

theorem bridge_compare (A : ℕ → ℝ) (r : ℝ) :
    (fun k : ℕ ↦ A k * (1 + Real.log k) ^ r) =Θ[atTop]
      fun k : ℕ ↦ A k * (Real.log k) ^ r := by
  let L : ℕ → ℝ := fun k ↦ Real.log k
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : (fun k ↦ 1 + L k) ~[atTop] L :=
    (IsEquivalent.refl (u := L) (l := atTop)).const_add_of_norm_tendsto_atTop (tendsto_norm_atTop_atTop.comp hL)
  have hn : 0 ≤ L := by
    intro k
    cases k with
    | zero => simp [L]
    | succ k => exact Real.log_nonneg (by exact_mod_cast Nat.succ_pos k)
  exact (isTheta_refl A atTop).mul (hbase.rpow hn (r := r)).isTheta

theorem main : H1 → H2 → type_of% @Green87.green_87.variants.order := by
  intro h1 h2 p hp
  rcases h1 with ⟨C, c, hc, hfinite⟩
  apply IsTheta.trans _ (bridge_compare (fun k : ℕ ↦ (k : ℝ) ^ (-δ)) (-(3 / 2 : ℝ)))
  apply IsTheta.trans _ h2
  constructor
  · apply IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    apply le_of_tendsto (hp k).norm
    filter_upwards [eventually_ge_atTop (2 * k)] with n hn
    exact (hfinite k hk n hn).1
  · apply isBigO_iff''.2
    refine ⟨c, hc, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    apply ge_of_tendsto (hp k).norm
    filter_upwards [eventually_ge_atTop (2 * k)] with n hn
    exact (hfinite k hk n hn).2

end OMA.R_Green87_green_87_variants_order_R2
