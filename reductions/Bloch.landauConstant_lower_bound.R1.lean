import FormalConjectures.Wikipedia.Bloch
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# Landau's lower bound via locally univalent functions

The reduction separates the covering-map argument from the quantitative
estimate for functions whose derivative does not vanish. The argument for the
covering step is described in Lemma 2.1 of Wikström, arXiv:2609.23236.
-/

namespace OMA.R_Bloch_landauConstant_lower_bound_R1

open Metric Set

private theorem disk_of_single_omission {s : Set ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hmiss : ¬ ∃ x y, x ∉ s ∧ y ∉ s ∧ x ≠ y) : ∃ c, ball c r ⊆ s := by
  classical
  by_cases hex : ∃ x, x ∉ s
  · obtain ⟨x, hx⟩ := hex
    refine ⟨x + (r : ℂ), ?_⟩
    intro y hy
    by_contra hyn
    have he : x = y := by
      by_contra hne
      exact hmiss ⟨x, y, hx, hyn, hne⟩
    rw [← he, mem_ball_iff_norm, show x - (x + (r : ℂ)) = -(r : ℂ) by ring,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hy
    exact (lt_irrefl _ hy)
  · exact ⟨0, fun y _ => by by_contra hy; exact hex ⟨y, hy⟩⟩

private theorem transfer_disk {g : ℂ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg' : ∀ z ∈ ball 0 1, deriv g z ≠ 0)
    (hnorm : 1 ≤ ‖deriv g 0‖)
    (hcover : ∀ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 1) → F 0 = 0 →
      deriv F 0 = 1 → (∀ z ∈ ball 0 1, deriv F z ≠ 0) →
      ∃ c, ball c r ⊆ F '' ball 0 1) :
    ∃ c, ball c r ⊆ g '' ball 0 1 := by
  let d := deriv g 0
  have hdpos : 0 < ‖d‖ := zero_lt_one.trans_le hnorm
  have hd : d ≠ 0 := norm_pos_iff.mp hdpos
  let F : ℂ → ℂ := fun z => (g z - g 0) / d
  have hF (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : HasDerivAt F (deriv g z / d) z :=
    (((hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt).sub_const (g 0)).div_const d
  have hF0 : deriv F 0 = 1 := by
    rw [(hF 0 (mem_ball_self zero_lt_one)).deriv]
    exact div_self hd
  obtain ⟨c, hc⟩ := hcover F
    (fun z hz => (hF z hz).differentiableAt.differentiableWithinAt)
    (by simp [F]) hF0
    (fun z hz => by rw [(hF z hz).deriv]; exact div_ne_zero (hg' z hz) hd)
  let b := d * c + g 0
  refine ⟨b, ?_⟩
  intro w hw
  have hmem : (w - g 0) / d ∈ ball c r := by
    rw [mem_ball_iff_norm] at hw ⊢
    have he : (w - g 0) / d - c = (w - b) / d := by
      dsimp [b]
      field_simp
      ring
    rw [he, norm_div, div_lt_iff₀ hdpos]
    exact hw.trans_le (le_mul_of_one_le_right hr hnorm)
  obtain ⟨z, hz, he⟩ := hc hmem
  exact ⟨z, hz, sub_left_inj.mp ((div_left_inj' hd).mp (by simpa [F] using he))⟩

/-- A holomorphic image omitting two points has a locally univalent disk
parametrization with derivative norm at least that of the original map at zero. -/
def H1 : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (ball 0 1) → deriv f 0 = 1 →
    (∃ x y, x ∉ f '' ball 0 1 ∧ y ∉ f '' ball 0 1 ∧ x ≠ y) →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) ∧
      (∀ z ∈ ball 0 1, deriv g z ≠ 0) ∧ 1 ≤ ‖deriv g 0‖ ∧
      g '' ball 0 1 ⊆ f '' ball 0 1

/-- The quantitative disk estimate for normalized locally univalent functions. -/
def H2 : Prop :=
  ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 1) → g 0 = 0 → deriv g 0 = 1 →
    (∀ z ∈ ball 0 1, deriv g z ≠ 0) →
    ∃ c, ball c (0.5 + 10 ^ (-335 : ℤ)) ⊆ g '' ball 0 1

theorem main : H1 → H2 → type_of% @Bloch.landauConstant_lower_bound := by
  intro h1 h2
  unfold Bloch.landauConstant
  apply le_csSup
  · refine ⟨1, ?_⟩
    intro r hr
    obtain ⟨c, hc⟩ := hr id differentiableOn_id (by simp)
    rw [image_id] at hc
    by_cases hp : 0 < r
    · exact Bloch.radius_le_of_ball_subset_ball (𝕜 := ℂ) hp hc
    · linarith
  intro f hf hf0
  have hr : (0 : ℝ) ≤ 0.5 + 10 ^ (-335 : ℤ) := by positivity
  by_cases hmiss : ∃ x y, x ∉ f '' ball 0 1 ∧ y ∉ f '' ball 0 1 ∧ x ≠ y
  · obtain ⟨g, hg, hcrit, hnorm, hsub⟩ := h1 f hf hf0 hmiss
    obtain ⟨c, hc⟩ := transfer_disk hr hg hcrit hnorm h2
    exact ⟨c, hc.trans hsub⟩
  · exact disk_of_single_omission hr hmiss

end OMA.R_Bloch_landauConstant_lower_bound_R1
