import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1
import Mathlib

/-!
Adapted from @ivillar, merged PR 3619, generalizing the circle-avoidance proof by @dk8827 in PR 1958.

The unit sphere in EuclideanSpace R (Fin (m + 3)) is simply connected. Approximate a based loop
by a Bernstein polynomial in ambient space, radially project it and the straight-line homotopy;
the projected loop omits a point (a nonzero coordinate polynomial has finitely many zeros), and
stereographic projection contracts the loop in the punctured sphere.
-/

-- Credit: adapted from the merged proof proofs/PoincareConjecture.poincare_conjecture.variants.
-- dimension_two.R1.H3.lean by @dk8827 (PR #1958), generalized from Fin 3 to Fin (m + 3).

open Metric Filter Set Polynomial
open scoped unitInterval BigOperators

namespace P5SphereLoops

private abbrev E (m : ℕ) := EuclideanSpace ℝ (Fin (m + 2 + 1))
private abbrev S (m : ℕ) := sphere (0 : E m) 1

private def i0 (m : ℕ) : Fin (m + 2 + 1) := ⟨0, by omega⟩
private def i1 (m : ℕ) : Fin (m + 2 + 1) := ⟨1, by omega⟩
private def i2 (m : ℕ) : Fin (m + 2 + 1) := ⟨2, by omega⟩

private noncomputable def radial {m : ℕ} (y : E m) : E m := ‖y‖⁻¹ • y

private theorem radial_mem {m : ℕ} (y : E m) (hy : y ≠ 0) : radial y ∈ sphere (0 : E m) 1 := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  change dist (radial y) 0 = 1
  rw [dist_zero_right, radial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    inv_mul_cancel₀ hn.ne']

private theorem radial_fixed {m : ℕ} (x : S m) : radial (x : E m) = x := by
  rw [radial, norm_eq_of_mem_sphere x, inv_one, one_smul]

private theorem radial_continuous {m : ℕ} : ContinuousOn (radial (m := m)) ({0}ᶜ : Set (E m)) := by
  exact (continuous_norm.continuousOn.inv₀
    (fun _ hy => norm_ne_zero_iff.2 (by simpa using hy))).smul continuous_id.continuousOn

private theorem bernstein_coord {m : ℕ} (n : ℕ) (f : C(I, E m)) :
    ∃ P : ℝ[X], ∀ t : I, P.eval (t : ℝ) = bernsteinApproximation n f t (i0 m) := by
  let l : E m →L[ℝ] ℝ := EuclideanSpace.proj (i0 m)
  refine ⟨∑ k : Fin (n + 1), C (l (f (bernstein.z k))) *
    bernsteinPolynomial ℝ n k, fun t => ?_⟩
  change _ = l (bernsteinApproximation n f t)
  rw [bernsteinApproximation.apply, map_sum, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  simp [bernstein, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap, mul_comm]

private theorem radial_ratio {m : ℕ} (u : E m) (hu : u ≠ 0) :
    radial u (i2 m) / radial u (i1 m) = u (i2 m) / u (i1 m) := by
  change ((‖u‖ : ℝ)⁻¹ * u (i2 m)) / ((‖u‖ : ℝ)⁻¹ * u (i1 m)) = _
  exact mul_div_mul_left _ _ (inv_ne_zero (norm_ne_zero_iff.2 hu))

private theorem omits_point {m : ℕ} (g : C(I, E m)) (hn : ∀ t, g t ≠ 0)
    (P : ℝ[X]) (hP : ∀ t : I, P.eval (t : ℝ) = g t (i0 m)) :
    ∃ y : S m, ∀ t : I, radial (g t) ≠ (y : E m) := by
  classical
  have h01 : i0 m ≠ i1 m := by simp [i0, i1]
  have h02 : i0 m ≠ i2 m := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 m ≠ i2 m := by simp [i1, i2, Fin.ext_iff]
  by_cases h : P = 0
  · let w : E m := WithLp.toLp 2 (fun i => if i = i0 m then 1 else 0)
    have hw0 : w (i0 m) = 1 := by simp [w]
    have hw : w ≠ 0 := by
      intro he
      have h0 := congrArg (fun x : E m => x (i0 m)) he
      simp only [hw0] at h0
      norm_num at h0
    refine ⟨⟨radial w, radial_mem w hw⟩, fun t he => ?_⟩
    have h0 : g t (i0 m) = 0 := by simp [← hP t, h]
    have he0 := congrArg (fun x : E m => x (i0 m)) he
    change ‖g t‖⁻¹ * g t (i0 m) = ‖w‖⁻¹ * w (i0 m) at he0
    have hp : 0 < (‖w‖ : ℝ)⁻¹ := inv_pos.2 (norm_pos_iff.2 hw)
    rw [h0, mul_zero, hw0, mul_one] at he0
    exact hp.ne' he0.symm
  · have ht : Set.Finite {t : I | P.eval (t : ℝ) = 0} :=
      (Polynomial.finite_setOfPred_isRoot h).preimage Subtype.val_injective.injOn
    let ratio (t : I) := g t (i2 m) / g t (i1 m)
    obtain ⟨r, hr⟩ := (ht.image ratio).exists_notMem
    let w : E m := WithLp.toLp 2 (fun i => if i = i1 m then 1 else if i = i2 m then r else 0)
    have hw0 : w (i0 m) = 0 := by simp [w, h01, h02]
    have hw1 : w (i1 m) = 1 := by simp [w]
    have hw2 : w (i2 m) = r := by simp [w, h12.symm]
    have hw : w ≠ 0 := by
      intro he
      have h1 := congrArg (fun x : E m => x (i1 m)) he
      simp only [hw1] at h1
      norm_num at h1
    refine ⟨⟨radial w, radial_mem w hw⟩, fun t he => ?_⟩
    have he0 := congrArg (fun x : E m => x (i0 m)) he
    change ‖g t‖⁻¹ * g t (i0 m) = ‖w‖⁻¹ * w (i0 m) at he0
    have ht0 : P.eval (t : ℝ) = 0 := by
      rw [hP]
      rw [hw0, mul_zero] at he0
      exact (mul_eq_zero.1 he0).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 (hn t)))
    have heR := congrArg (fun x : E m => x (i2 m) / x (i1 m)) he
    simp only at heR
    rw [radial_ratio _ (hn t), radial_ratio w hw, hw1, hw2] at heR
    change ratio t = r / 1 at heR
    exact hr ⟨t, ht0, by simpa using heR⟩

private theorem homotopic_omitting {m : ℕ} {x : S m} (p : Path x x) :
    ∃ q : Path x x, p.Homotopic q ∧ ∃ y : S m, ∀ t : I, q t ≠ y := by
  let f : C(I, E m) := ⟨fun t => (p t : E m), continuous_subtype_val.comp p.continuous⟩
  have hnear : ∀ᶠ n in atTop, dist (bernsteinApproximation n f) f < 1 :=
    (Metric.tendsto_nhds.1 (bernsteinApproximation_uniform f)) 1 zero_lt_one
  obtain ⟨m', hm⟩ := eventually_atTop.1 hnear
  let n := m' + 1
  let g := bernsteinApproximation n f
  have hclose (t : I) : dist (g t) (f t) < 1 :=
    (ContinuousMap.dist_apply_le_dist t).trans_lt (hm n (Nat.le_succ m'))
  have g_zero : g 0 = (x : E m) := by simp [g, f, p.source]
  have g_one : g 1 = (x : E m) := by
    rw [show g 1 = f 1 from bernsteinApproximation.apply_one (by simp [n]) f]
    exact congrArg Subtype.val p.target
  let B (u : I × I) : E m := f u.2 + (u.1 : ℝ) • (g u.2 - f u.2)
  have B_cont : Continuous B := by unfold B; fun_prop
  have B_ne (u : I × I) : B u ≠ 0 := by
    intro h
    have hneg : (u.1 : ℝ) • (g u.2 - f u.2) = -(f u.2) :=
      eq_neg_of_add_eq_zero_right h
    have hnorm : ‖(u.1 : ℝ) • (g u.2 - f u.2)‖ = 1 := by
      rw [hneg, norm_neg]
      exact norm_eq_of_mem_sphere (p u.2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg u.1.2.1, ← dist_eq_norm] at hnorm
    nlinarith [u.1.2.2, dist_nonneg (x := g u.2) (y := f u.2), hclose u.2]
  have g_ne (t : I) : g t ≠ 0 := by
    simpa [B] using B_ne (1, t)
  have g_radial_cont : Continuous (fun t => radial (g t)) :=
    radial_continuous.comp_continuous g.continuous (fun t => by simpa using g_ne t)
  let q : Path x x :=
    { toFun := fun t => ⟨radial (g t), radial_mem _ (g_ne t)⟩
      continuous_toFun := g_radial_cont.subtype_mk _
      source' := Subtype.ext (by simpa [g_zero] using radial_fixed x)
      target' := Subtype.ext (by simpa [g_one] using radial_fixed x) }
  have B_radial_cont : Continuous (fun u => radial (B u)) :=
    radial_continuous.comp_continuous B_cont (fun u => by simpa using B_ne u)
  refine ⟨q, ⟨{
    toFun := fun u => ⟨radial (B u), radial_mem _ (B_ne u)⟩
    continuous_toFun := B_radial_cont.subtype_mk _
    map_zero_left := fun t => Subtype.ext (by simpa [B, f] using radial_fixed (p t))
    map_one_left := fun t => Subtype.ext (by simp [B, q])
    prop' := ?_ }⟩, ?_⟩
  · intro t u hu
    have h := (show u = 0 ∨ u = 1 by simpa using hu)
    rcases h with rfl | rfl
    · apply Subtype.ext
      simp [B, f, g_zero, p.source, radial_fixed x]
    · apply Subtype.ext
      simp [B, f, g_one, p.target, radial_fixed x]
  · obtain ⟨P, hP⟩ := bernstein_coord n f
    obtain ⟨y, hy⟩ := omits_point g g_ne P hP
    exact ⟨y, fun t he => hy t (congrArg Subtype.val he)⟩

private theorem punctured_simplyConnected {m : ℕ} (y : S m) :
    SimplyConnectedSpace ↥(({y} : Set (S m))ᶜ) := by
  let e := stereographic (norm_eq_of_mem_sphere y)
  have hs : e.source = ({y} : Set (S m))ᶜ :=
    stereographic_source (norm_eq_of_mem_sphere y)
  have ht : e.target = Set.univ := stereographic_target (norm_eq_of_mem_sphere y)
  let h := (Homeomorph.setCongr hs.symm).trans
    (e.toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)))
  have : SimplyConnectedSpace ↥((ℝ ∙ (y : E m))ᗮ) :=
    SimplyConnectedSpace.ofContractible _
  exact h.toHomotopyEquiv.simplyConnectedSpace

theorem sphere_simplyConnected (m : ℕ) : SimplyConnectedSpace (S m) := by
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_sphere (by
      rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
      norm_cast; omega) (0 : E m) zero_le_one), ?_⟩
  intro x p
  obtain ⟨q, hpq, y, hy⟩ := homotopic_omitting p
  have := punctured_simplyConnected y
  let x' : ↥(({y} : Set (S m))ᶜ) := ⟨x, by simpa [q.source] using hy 0⟩
  have hmem (t : I) : q t ∈ ({y} : Set (S m))ᶜ := by simpa using hy t
  let q' : Path x' x' :=
    { toFun := fun t => ⟨q t, hmem t⟩
      continuous_toFun := q.continuous.subtype_mk hmem
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic q' (Path.refl x')
  let incl : C(↥(({y} : Set (S m))ᶜ), S m) := ⟨Subtype.val, continuous_subtype_val⟩
  have hq : q'.map incl.continuous = q := by ext t; rfl
  have hr : (Path.refl x').map incl.continuous = Path.refl x := by ext t; rfl
  refine hpq.trans ⟨?_⟩
  simpa only [hq, hr] using H.map incl

end P5SphereLoops

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_four_R1.H2 :=
  P5SphereLoops.sphere_simplyConnected 2
