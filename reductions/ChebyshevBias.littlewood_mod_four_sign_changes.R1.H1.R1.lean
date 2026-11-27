import OMAReductions.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1
import Mathlib

/-!
A Fejér cutoff at height T, evaluated at time 1/T, has positive contributions
from all positive ordinates up to T. Each zero between 1 and T/2 contributes
at least its multiplicity divided by 8T. Compact-group recurrence repeats this
large value arbitrarily far out without any independence assumption.
-/

open Filter Finset Real
open scoped Topology
namespace OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1_H1_R1

private theorem trig_bounds {g T : ℝ} (hg : 0 < g) (hT : 0 < T) (hle : g ≤ T) :
    0 ≤ (1-g/T)*(cos (g/T)/2+g*sin (g/T))/(1/4+g^2) ∧
    (1 ≤ g → g ≤ T/2 → 1/(8*T) ≤ (1-g/T)*(cos (g/T)/2+g*sin (g/T))/(1/4+g^2)) := by
  have h0 : 0 ≤ g/T := div_nonneg hg.le hT.le
  have h1 : g/T ≤ 1 := (div_le_one hT).mpr hle
  have hp : g/T ≤ π/2 := by linarith [Real.pi_gt_three]
  have hcos := Real.cos_nonneg_of_mem_Icc (show g/T ∈ Set.Icc (-(π/2)) (π/2) by
    exact ⟨by linarith [Real.pi_pos],hp⟩)
  have hsin : (g/T)/2 ≤ sin (g/T) := by
    have hcoef : (1:ℝ)/2 ≤ 2/π := (le_div_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_lt_four])
    exact (show (g/T)/2 ≤ 2/π*(g/T) by nlinarith [mul_le_mul_of_nonneg_right hcoef h0]).trans
      (Real.mul_le_sin h0 hp)
  have hden : 0 < (1:ℝ)/4+g^2 := by positivity
  have hnon : 0 ≤ cos (g/T)/2+g*sin (g/T) := by
    have : 0 ≤ sin (g/T) := by linarith
    positivity
  refine ⟨div_nonneg (mul_nonneg (by linarith) hnon) hden.le,?_⟩
  intro hg1 hhalf
  apply (le_div_iff₀ hden).mpr
  calc
    1/(8*T)*(1/4+g^2) ≤ (1/2)*(g*((g/T)/2)) := by
      field_simp
      nlinarith [sq_nonneg (g-1)]
    _ ≤ (1-g/T)*(cos (g/T)/2+g*sin (g/T)) := by
      apply mul_le_mul _ _ (by positivity) (by linarith)
      · have ht : g/T ≤ 1/2 := (div_le_iff₀ hT).mpr (by linarith)
        linarith
      · nlinarith [mul_le_mul_of_nonneg_left hsin hg.le]

/-- Landau's one-sided singularity argument for the beta function. -/
def H1 : Prop := let L := DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
  (∀ᶠ n : ℕ in atTop,
    let layer (a : ℕ) := ∑ p ∈ (Nat.primesLE n).filter (fun p => p^a ≤ n),
      (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
    let J := ∑ j ∈ Finset.range (Nat.log 2 n), layer (j+1);
    -(Real.sqrt n / Real.log n) ≤ J) →
  ∀ s : ℂ, 1/2 < s.re → L s ≠ 0

/-- Under the zero-free half-plane, the critical-line count with multiplicity
eventually exceeds any fixed multiple of the height. Only one cutoff is needed. -/
def H2 : Prop := let L := DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
  (∀ s : ℂ, 1/2 < s.re → L s ≠ 0) →
  ∃ (T : ℝ) (Z : Finset ℝ), 2 ≤ T ∧ (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L (1/2+(g:ℂ)*Complex.I) = 0) ∧
    32*T < ∑ g ∈ Z.filter (fun g => 1 ≤ g ∧ g ≤ T/2), ((analyticOrderAt L (1/2+(g:ℂ)*Complex.I)).toNat : ℝ)

/-- One-sided Fejér explicit-formula bound for each fixed cutoff.
The phase is k+1/T and the denominator is the squared norm of the zero. -/
def H3 : Prop := let L := DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
  (∀ᶠ n : ℕ in atTop,
    let layer (a : ℕ) := ∑ p ∈ (Nat.primesLE n).filter (fun p => p^a ≤ n),
      (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
    let J := ∑ j ∈ Finset.range (Nat.log 2 n), layer (j+1);
    -(Real.sqrt n / Real.log n) ≤ J) →
  (∀ s : ℂ, 1/2 < s.re → L s ≠ 0) →
  ∀ (T : ℝ) (Z : Finset ℝ), 2 ≤ T → (∀ g : ℝ, g ∈ Z ↔ 0 < g ∧ g ≤ T ∧ L (1/2+(g:ℂ)*Complex.I) = 0) →
    ∀ᶠ k : ℕ in atTop,
      (∑ g ∈ Z, let v := (((Circle.exp g : Circle)^k : Circle) : ℂ) * (Circle.exp (g/T) : ℂ)
                ((analyticOrderAt L (1/2+(g:ℂ)*Complex.I)).toNat : ℝ) *
                  ((1-g/T)*(v.re/2+g*v.im)/(1/4+g^2))) ≤ 2

theorem main : H1 → H2 → H3 → OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1.H1 := by
  classical
  intro landau count explicit N
  by_contra hn
  let L := DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
  have low : (∀ᶠ n : ℕ in atTop,
    let layer (a : ℕ) := ∑ p ∈ (Nat.primesLE n).filter (fun p => p^a ≤ n),
      (ZMod.χ₄ (p : ZMod 4) : ℝ)^a / a
    let J := ∑ j ∈ Finset.range (Nat.log 2 n), layer (j+1);
    -(Real.sqrt n / Real.log n) ≤ J) := by
    filter_upwards [eventually_ge_atTop N] with n hnN
    exact le_of_not_gt (fun he => hn ⟨n,hnN,he⟩)
  have hz := landau low
  obtain ⟨T,Z,hT,hZ,hmass⟩ := count hz
  let w (g : ℝ) := ((analyticOrderAt L (1/2+(g:ℂ)*Complex.I)).toNat : ℝ)
  let term (g : ℝ) := (1-g/T)*(cos (g/T)/2+g*sin (g/T))/(1/4+g^2)
  let C := Z.filter (fun g => 1 ≤ g ∧ g ≤ T/2)
  have ht : 0<T := by linarith
  have mass : 32*T < ∑ g ∈ C,w g := hmass
  have lower : 2 < ∑ g ∈ Z,w g*term g := by
    have bound : (∑ g ∈ C,w g)/(8*T) ≤ ∑ g ∈ C,w g*term g := by
      rw [Finset.sum_div]
      apply sum_le_sum
      intro g hg
      obtain ⟨hgZ,hg1,hg2⟩ := mem_filter.mp hg
      obtain ⟨hg0,hgle,_⟩ := (hZ g).1 hgZ
      have hh := (trig_bounds hg0 ht hgle).2 hg1 hg2
      simpa only [term,div_eq_mul_inv,one_mul] using
        mul_le_mul_of_nonneg_left hh (show 0 ≤ w g by dsimp [w]; positivity)
    have inc : ∑ g ∈ C,w g*term g ≤ ∑ g ∈ Z,w g*term g := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro g hg _
      obtain ⟨hg0,hgle,_⟩ := (hZ g).1 hg
      exact mul_nonneg (by dsimp [w]; positivity) (trig_bounds hg0 ht hgle).1
    exact lt_of_lt_of_le ((lt_div_iff₀ (by positivity)).mpr (by linarith [mass])) (bound.trans inc)
  let phase (z : ℝ → Circle) : ℝ :=
    ∑ g ∈ Z, let v := (z g : ℂ)*(Circle.exp (g/T) : ℂ)
             w g*((1-g/T)*(v.re/2+g*v.im)/(1/4+g^2))
  have hc : Continuous phase := by dsimp only [phase]; fun_prop
  have atOne : 2 < phase 1 := by
    have hr (r : ℝ) : (Circle.exp r : ℂ).re = cos r := Complex.exp_ofReal_mul_I_re r
    have hi (r : ℝ) : (Circle.exp r : ℂ).im = sin r := Complex.exp_ofReal_mul_I_im r
    simpa only [phase,term,Pi.one_apply,Circle.coe_one,one_mul,hr,hi] using lower
  let a (g : ℝ) : Circle := Circle.exp g
  have hrec := mapClusterPt_one_atTop_pow a
  have hnear : {z : ℝ → Circle | 2 < phase z} ∈ 𝓝 1 :=
    hc.continuousAt.eventually (lt_mem_nhds atOne)
  have often := (mapClusterPt_iff_frequently.mp hrec) _ hnear
  have tail := explicit low hz T Z hT hZ
  obtain ⟨k,hlo,hhi⟩ := (often.and_eventually tail).exists
  exact (not_lt_of_ge hhi) hlo

end OMA.R_ChebyshevBias_littlewood_mod_four_sign_changes_R1_H1_R1
