import OMAStatements.S_mo_204379
import Mathlib

namespace JensenGap
open Set Finset OMA.S_mo_204379

noncomputable section

private def G (b a : ℝ) := a*b/(a+b)
private def slope (m b a : ℝ) := (2*m*b + m*a - a^2)/(a+b)^2
private def F {n : ℕ} (b : Fin n → ℝ) (m a : ℝ) := ∑ i, (G m a - G (b i) a)
private def H {n : ℕ} (b : Fin n → ℝ) (m a : ℝ) := ∑ i, (b i-m)^2*slope m (b i) a

private lemma G_deriv {b a : ℝ} (h : a+b ≠ 0) :
    HasDerivAt (G b) (b^2/(a+b)^2) a := by
  convert (((hasDerivAt_id a).mul_const b).div ((hasDerivAt_id a).add_const b) h) using 1
  all_goals first | rfl | (dsimp; ring)

private lemma slope_deriv {m b a : ℝ} (h : a+b ≠ 0) :
    HasDerivAt (slope m b) (-(m*a+2*a*b+3*m*b)/(a+b)^3) a := by
  have ha := hasDerivAt_id a
  have top := (((ha.const_mul m).const_add (2*m*b)).sub (ha.pow 2))
  have bot := ((ha.add_const b).pow 2)
  convert (top.div bot (pow_ne_zero 2 h)) using 1
  all_goals first | rfl | (dsimp; field_simp [h]; ring)

private lemma slope_anti {m b : ℝ} (hm : 0 < m) (hb : 0 < b) :
    StrictAntiOn (slope m b) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (fun a ha =>
    (slope_deriv (m := m) (show a+b ≠ 0 by have := ha.out; positivity)).continuousAt.continuousWithinAt)
  intro a ha
  have ha' : 0 ≤ a := interior_subset ha
  rw [(slope_deriv (m := m) (show a+b ≠ 0 by positivity)).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) (by positivity)

private lemma F_deriv {n : ℕ} {b : Fin n → ℝ} {m a : ℝ} (hm : 0 < m)
    (hb : ∀ i, 0<b i) (ha : 0≤a) (hmean : ∑ i, (b i-m) = 0) :
    HasDerivAt (F b m) (a/(a+m)^3 * H b m a) a := by
  have d (i : Fin n) : HasDerivAt (fun x => G m x-G (b i) x)
      (m^2/(a+m)^2 - (b i)^2/(a+b i)^2) a :=
    (G_deriv (by positivity)).sub (G_deriv (by have := hb i; positivity))
  have hterm (i : Fin n) : m^2/(a+m)^2 - (b i)^2/(a+b i)^2 =
      a/(a+m)^3 * ((b i-m)^2*slope m (b i) a) - 2*m*a/(a+m)^3*(b i-m) := by
    unfold slope
    field_simp [show a+m ≠ 0 by positivity, show a+b i ≠ 0 by have := hb i; positivity]
    ring
  convert (HasDerivAt.fun_sum (u := univ) (fun i _ => d i)) using 1
  all_goals first | rfl | simp only [hterm, sum_sub_distrib, ← mul_sum, hmean, mul_zero, sub_zero, H]

private theorem solve {n : ℕ} (hn : 0<n) (b : Fin n → ℝ) (hb : ∀ i, 0<b i)
    (hd : ∃ i j, b i ≠ b j) :
    ∃! a : ℝ, 0<a ∧ ∀ x : ℝ, 0<x → D b x ≤ D b a := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  let m := (∑ i, b i)/(n:ℝ)
  have hsum : 0 < ∑ i, b i := sum_pos' (fun i _ => (hb i).le)
    ⟨⟨0, hn⟩, mem_univ _, hb _⟩
  have hm : 0 < m := div_pos hsum hn'
  have hmean : (n:ℝ)*m = ∑ i, b i := by unfold m; field_simp
  have hcenter : ∑ i, (b i-m) = 0 := by simp [sum_sub_distrib, hmean]
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ m := by
    by_contra! hall
    obtain ⟨i,j,hd⟩ := hd
    exact hd ((hall i).trans (hall j).symm)
  have eqD (a : ℝ) (ha : 0<a) : D b a = F b m a := by
    simp only [D,F,sum_sub_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,G]
    congr 1
    rw [← hmean]
    field_simp [show a+m ≠ 0 by positivity,
      show (n:ℝ)*a+(n:ℝ)*m ≠ 0 by positivity]
  have anti : StrictAntiOn (H b m) (Ici 0) := by
    intro x hx y hy hxy
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left ((slope_anti hm (hb i) hx hy hxy).le) (sq_nonneg _)
    · exact ⟨j, mem_univ _, mul_lt_mul_of_pos_left (slope_anti hm (hb j) hx hy hxy)
        (sq_pos_of_ne_zero (sub_ne_zero.mpr hj))⟩
  have h0 : 0 < H b m 0 := by
    apply sum_pos'
    · intro i _
      have := hb i
      simp only [slope, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, zero_add]
      positivity
    · refine ⟨j, mem_univ _, mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hj)) ?_⟩
      have := hb j
      simp only [slope, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, zero_add]
      positivity
  let U := 2*((∑ i, b i)+m)+1
  have hU : 0 < U := by dsimp [U]; positivity
  have hright (i : Fin n) : slope m (b i) U < 0 := by
    have hle : b i ≤ ∑ j, b j := single_le_sum (fun k _ => (hb k).le) (mem_univ i)
    have h₁ : m < U := by dsimp [U]; linarith
    have h₂ : 2*b i < U-m := by dsimp [U]; linarith
    apply div_neg_of_neg_of_pos _ (by have := hb i; positivity)
    nlinarith [mul_lt_mul_of_pos_left h₂ hm, mul_lt_mul_of_pos_right h₁ (show 0 < U-m by linarith)]
  have hUneg : H b m U < 0 := by
    apply sum_neg'
    · intro i _
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hright i).le
    · exact ⟨j, mem_univ _, mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr hj)) (hright j)⟩
  have hc : ContinuousOn (H b m) (Icc 0 U) := by
    apply continuousOn_finsetSum
    intro i _ a ha
    exact (continuousAt_const.mul (slope_deriv (m := m) (show a+b i ≠ 0 by
      have := ha.1; have := hb i; positivity)).continuousAt).continuousWithinAt
  obtain ⟨r,hr,hr0⟩ := intermediate_value_Icc' hU.le hc (show 0 ∈ Icc (H b m U) (H b m 0) from ⟨hUneg.le,h0.le⟩)
  have hrpos : 0<r := lt_of_le_of_ne hr.1 (by intro e; subst r; linarith)
  have peak (x : ℝ) (hx : 0<x) (hne : x≠r) : F b m x < F b m r := by
    rcases lt_or_gt_of_ne hne with hxr|hrx
    · apply strictMonoOn_of_deriv_pos (convex_Icc x r) (fun a ha =>
        (F_deriv hm hb (hx.le.trans ha.1) hcenter).continuousAt.continuousWithinAt) _ (left_mem_Icc.mpr hxr.le) (right_mem_Icc.mpr hxr.le) hxr
      intro a ha
      rw [interior_Icc] at ha
      have hap := hx.trans ha.1
      rw [(F_deriv hm hb hap.le hcenter).deriv]
      have hs := anti (show a ∈ Set.Ici (0:ℝ) from hap.le) (show r ∈ Set.Ici (0:ℝ) from hrpos.le) ha.2
      rw [hr0] at hs
      positivity
    · apply strictAntiOn_of_deriv_neg (convex_Icc r x) (fun a ha =>
        (F_deriv hm hb (hrpos.le.trans ha.1) hcenter).continuousAt.continuousWithinAt) _ (left_mem_Icc.mpr hrx.le) (right_mem_Icc.mpr hrx.le) hrx
      intro a ha
      rw [interior_Icc] at ha
      have hap := hrpos.trans ha.1
      rw [(F_deriv hm hb hap.le hcenter).deriv]
      have hs := anti (show r ∈ Set.Ici (0:ℝ) from hrpos.le) (show a ∈ Set.Ici (0:ℝ) from hap.le) ha.1
      rw [hr0] at hs
      exact mul_neg_of_pos_of_neg (by positivity) hs
  refine ⟨r, ⟨hrpos, fun x hx => ?_⟩, fun y hy => ?_⟩
  · rw [eqD x hx,eqD r hrpos]
    by_cases e : x=r
    · rw [e]
    · exact (peak _ hx e).le
  · by_contra hne
    have h := hy.2 r hrpos
    rw [eqD r hrpos, eqD y hy.1] at h
    exact (peak y hy.1 hne).not_ge h

end
end JensenGap

/-- The derivative of the gap has the sign of a strictly decreasing sum H.
Each summand is a squared deviation from the mean times slope, whose derivative
is negative. The signs of H at zero and at a finite upper cutoff give one peak. -/
theorem OMA.solution : type_of% @OMA.S_mo_204379.main := fun _ hn b hb hd => JensenGap.solve hn b hb hd
