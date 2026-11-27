import OMAStatements.S_mse_4452078
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-!
# Complete negative answer to the derivative-ratio existence question

Problem: https://lefttosolve.com/p/mse-4452078
Source question: Mathematics Stack Exchange 4452078, user1058535, 16 May 2022.

The main result proves impossibility under the weaker assumption that absolute
value is nondecreasing only on a tail. The reciprocal is bounded below there,
but its derivative would eventually be at most minus one. The mean value
inequality gives a contradiction. No sign restriction, derivative continuity,
or additional nonvanishing assumption is required.

The simultaneous positive-integer-power condition is ruled out explicitly.
The source's n = 1 example, exp composed with exp, is also verified below.
This is an elementary calculus argument; no research-novelty claim is made.
-/

open Filter Set

namespace OMA.MSE4452078

lemma bounded_below_not_uniformly_negative_derivative
    {g : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ x : ℝ, a < x → DifferentiableAt ℝ g x)
    (hb : ∀ x : ℝ, a < x → b ≤ g x)
    (hd : ∀ x : ℝ, a < x → deriv g x ≤ -1) : False := by
  let x := a + 1
  have hx : a < x := by dsimp [x]; linarith
  have hbx := hb x hx
  let y := x + (g x - b) + 1
  have hxy : x ≤ y := by dsimp [y]; linarith
  have hy : a < y := lt_of_lt_of_le hx hxy
  have hgon : DifferentiableOn ℝ g (Ioi a) :=
    fun z hz => (hg z hz).differentiableWithinAt
  have hgi : DifferentiableOn ℝ g (interior (Ioi a)) := by
    simpa only [isOpen_Ioi.interior_eq] using hgon
  have hdi : ∀ z ∈ interior (Ioi a), deriv g z ≤ -1 := by
    simpa only [isOpen_Ioi.interior_eq, mem_Ioi] using hd
  have hm := (convex_Ioi a).image_sub_le_mul_sub_of_deriv_le
    hgon.continuousOn hgi hdi x hx y hy hxy
  have hby := hb y hy
  dsimp [y] at hm hby
  linarith

lemma inv_lower_bound_of_abs_le {u v : ℝ}
    (hv : v ≠ 0) (h : |v| ≤ |u|) :
    -|v|⁻¹ ≤ u⁻¹ := by
  have hinv : |u|⁻¹ ≤ |v|⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (abs_pos.mpr hv) h
  calc
    -|v|⁻¹ ≤ -|u|⁻¹ := neg_le_neg hinv
    _ = -|u⁻¹| := by rw [abs_inv]
    _ ≤ u⁻¹ := neg_abs_le _

theorem no_square_ratio_divergence
    {f : ℝ → ℝ} {x₀ : ℝ}
    (hdiff : ∀ x : ℝ, x₀ < x → DifferentiableAt ℝ f x)
    (hmono : MonotoneOn (fun x : ℝ => |f x|) (Ioi x₀)) :
    ¬ Tendsto (fun x : ℝ => deriv f x / (f x) ^ 2) atTop atTop := by
  intro hlim
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hlim.eventually (eventually_ge_atTop (1 : ℝ)))
  let t := max a x₀ + 1
  have hat : a ≤ t := by dsimp [t]; linarith [le_max_left a x₀]
  have hxt : x₀ < t := by dsimp [t]; linarith [le_max_right a x₀]
  have hnonzero : ∀ x : ℝ, t ≤ x → f x ≠ 0 := by
    intro x hx hzero
    have hratio := ha x (hat.trans hx)
    simp [hzero] at hratio
    linarith
  apply bounded_below_not_uniformly_negative_derivative
    (g := fun x : ℝ => (f x)⁻¹) (a := t) (b := -|f t|⁻¹)
  · intro x hx
    exact (hdiff x (hxt.trans hx)).inv (hnonzero x hx.le)
  · intro x hx
    exact inv_lower_bound_of_abs_le (hnonzero t le_rfl)
      (hmono hxt (hxt.trans hx) hx.le)
  · intro x hx
    rw [deriv_fun_inv'' (hdiff x (hxt.trans hx)) (hnonzero x hx.le), neg_div]
    have hratio := ha x (hat.trans hx.le)
    linarith

theorem no_simultaneous_divergence
    {f : ℝ → ℝ} {x₀ : ℝ}
    (hdiff : ∀ x : ℝ, x₀ < x → DifferentiableAt ℝ f x)
    (hmono : MonotoneOn (fun x : ℝ => |f x|) (Ioi x₀)) :
    ¬ (∀ n : ℕ, 0 < n →
      Tendsto (fun x : ℝ => deriv f x / (f x) ^ n) atTop atTop) := by
  intro h
  exact no_square_ratio_divergence hdiff hmono (h 2 (by decide))

end OMA.MSE4452078


namespace OMA.MSE4452078

theorem exp_exp_witness :
    ∃ f : ℝ → ℝ, Differentiable ℝ f ∧ StrictMono (fun x => |f x|) ∧
      Tendsto (fun x => deriv f x / f x) atTop atTop := by
  refine ⟨fun x => Real.exp (Real.exp x), ?_, ?_, ?_⟩
  · fun_prop
  · simpa only [Function.comp_def, abs_of_pos (Real.exp_pos _)] using Real.exp_strictMono.comp Real.exp_strictMono
  · have hder : ∀ x : ℝ, deriv (fun y => Real.exp (Real.exp y)) x =
        Real.exp (Real.exp x) * Real.exp x := by
      intro x
      exact ((Real.hasDerivAt_exp (Real.exp x)).comp x (Real.hasDerivAt_exp x)).deriv
    simp_rw [hder, mul_div_cancel_left₀ _ (Real.exp_ne_zero _)]
    exact Real.tendsto_exp_atTop

end OMA.MSE4452078

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4452078.main) := by
  rintro ⟨f, x₀, hdiff, hmono, hlim⟩
  exact OMA.MSE4452078.no_square_ratio_divergence hdiff (hmono.monotoneOn _) hlim
