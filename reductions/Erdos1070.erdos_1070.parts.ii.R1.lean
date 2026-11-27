import FormalConjectures.ErdosProblems.«1070»
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! A geometric averaging reduction for an independence ratio strictly below one quarter. -/

-- The finite dual certificate and the averaging method are due to Dúcz–Varga and
-- Matolcsi–Ruzsa–Varga–Zsámboki, arXiv:2606.28157 and arXiv:2311.10069.

-- Credit: @ysanatomic

namespace OMA.R_Erdos1070_erdos_1070_parts_ii_R1

open SimpleGraph BigOperators

private theorem complex_independent
    (h : ∀ n : ℕ, (n : ℝ) / 4 ≤ (Erdos1070.f n : ℝ)) :
    ∀ X : Finset ℂ, ∃ B ⊆ X, (X.card : ℝ) / 4 ≤ B.card ∧
      ∀ x ∈ B, ∀ y ∈ B, dist x y ≠ 1 := by
  classical
  intro X
  let e := Complex.orthonormalBasisOneI.repr
  let Y := X.map e.toEquiv.toEmbedding
  let G := UnitDistancePlaneGraph (Y : Set (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨D, hD⟩ := G.exists_isNIndepSet_indepNum
  let r : (Y : Set (EuclideanSpace ℝ (Fin 2))) ↪ ℂ :=
    ⟨fun v ↦ e.symm v.val, fun v w hvw ↦ Subtype.ext (e.symm.injective hvw)⟩
  refine ⟨D.map r, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp (show y.val ∈ Y from y.property)
    convert hz using 1
    change e.symm y.val = z
    exact e.symm_apply_eq.mpr hzy.symm
  · rw [Finset.card_map, hD.card_eq]
    have hc : Y.card = X.card := Finset.card_map _
    rw [← hc]
    exact (h Y.card).trans (by exact_mod_cast Erdos1070.f_le Y)
  · intro x hx y hy hxy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
    have hdist := e.symm.isometry.dist_eq v.val w.val
    change dist (e.symm v.val) (e.symm w.val) = 1 at hxy
    rw [hdist] at hxy
    have hne : v ≠ w := by
      intro eq
      subst w
      simp at hxy
    exact hD.isIndepSet hv hw hne hxy

/-- The G29 integer dual inequalities on independent subsets, with certified congruences. -/
def H1 : Prop := by
  classical
  exact ∃ p : Fin 29 → ℂ, ∃ C : List (ℤ × Finset (Fin 29) × Finset (Fin 29)),
    (∀ r ∈ C, ∃ a b : ℂ, ‖a‖ = 1 ∧
      (r.2.1.image (fun i ↦ a * p i + b) = r.2.2.image p ∨
        r.2.1.image (fun i ↦ a * (star (p i)) + b) = r.2.2.image p)) ∧
    ∃ D N : ℤ, 0 < D ∧ 4 * D < N ∧
    ∀ I : Finset (Fin 29), (∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1) →
      N * (if 0 ∈ I then 1 else 0) ≤ D +
        (C.map fun r ↦ r.1 * ((if r.2.1 ⊆ I then 1 else 0) -
                                      (if r.2.2 ⊆ I then 1 else 0))).sum

/-- Approximate local moments of independent sets, if every finite complex geometry has
an independent subset of relative size at least one quarter. -/
def H2 : Prop := by
  classical
  exact ∀ (p : Fin 29 → ℂ) (C : List (ℤ × Finset (Fin 29) × Finset (Fin 29))),
    (∀ r ∈ C, ∃ a b : ℂ, ‖a‖ = 1 ∧
      (r.2.1.image (fun i ↦ a * p i + b) = r.2.2.image p ∨
        r.2.1.image (fun i ↦ a * (star (p i)) + b) = r.2.2.image p)) →
    (∀ X : Finset ℂ, ∃ B ⊆ X, (X.card : ℝ) / 4 ≤ B.card ∧
      ∀ x ∈ B, ∀ y ∈ B, dist x y ≠ 1) →
    ∀ ε > (0 : ℝ), ∃ μ : Finset (Fin 29) → ℝ,
      (∀ I, 0 ≤ μ I) ∧ (∑ I, μ I) = 1 ∧
      (∀ I, ¬ (∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1) → μ I = 0) ∧
      let moment := fun S : Finset (Fin 29) ↦ ∑ I, if S ⊆ I then μ I else 0
      1 / 4 - ε ≤ moment {0} ∧ ∀ r ∈ C, |moment r.2.1 - moment r.2.2| ≤ ε


theorem main : H1 → H2 → type_of% @Erdos1070.erdos_1070.parts.ii := by
  classical
  intro hCert hAveraging h
  obtain ⟨p, C, hCongruent, d, n, hd, hnd, hDual⟩ := hCert
  let N : ℝ := n
  let D : ℝ := d
  have hD : 0 < D := by
    change (0 : ℝ) < (d : ℝ)
    exact_mod_cast hd
  have hND : 4 * D < N := by
    change (4 : ℝ) * (d : ℝ) < (n : ℝ)
    exact_mod_cast hnd
  have hgap : 0 < N / 4 - D := by linarith
  let W : ℝ := (C.map fun r ↦ |(r.1 : ℝ)|).sum
  have hW : 0 ≤ W := by
    change 0 ≤ (C.map fun r ↦ |(r.1 : ℝ)|).sum
    apply List.sum_nonneg
    intro x hx
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  let ε := (N / 4 - D) / (N + W + 1)
  have hN : 0 ≤ N := by linarith
  have hTotal : 0 < N + W + 1 := by linarith
  have hε : 0 < ε := div_pos hgap hTotal
  obtain ⟨μ, hμ, hmass, hzero, hroot, hshape⟩ :=
    hAveraging p C hCongruent (complex_independent h) ε hε
  let moment (S : Finset (Fin 29)) : ℝ := ∑ I, if S ⊆ I then μ I else 0
  let contribution (r : ℤ × Finset (Fin 29) × Finset (Fin 29)) (I : Finset (Fin 29)) :=
    (r.1 : ℝ) * ((if r.2.1 ⊆ I then μ I else 0) - (if r.2.2 ⊆ I then μ I else 0))
  have hPoint (I : Finset (Fin 29)) :
      N * (if ({0} : Finset (Fin 29)) ⊆ I then μ I else 0) ≤
        D * μ I + (C.map fun r ↦ contribution r I).sum := by
    by_cases hI : ∀ i ∈ I, ∀ j ∈ I, dist (p i) (p j) ≠ 1
    · have hr : N * (if 0 ∈ I then (1 : ℝ) else 0) ≤ D +
          (C.map fun r ↦ (r.1 : ℝ) * ((if r.2.1 ⊆ I then 1 else 0) -
                                               (if r.2.2 ⊆ I then 1 else 0))).sum := by
        have hi := (Int.cast_le (R := ℝ)).mpr (hDual I hI)
        simpa only [N, D, Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_list_sum,
          List.map_map, Function.comp_def, apply_ite (fun x : ℤ ↦ (x : ℝ)),
          Int.cast_one, Int.cast_zero, Int.cast_ofNat] using hi
      have hmul := mul_le_mul_of_nonneg_right hr (hμ I)
      rw [add_mul, ← List.sum_map_mul_right] at hmul
      simpa only [List.map_map, Function.comp_def, mul_assoc, sub_mul, ite_mul, one_mul,
        zero_mul, contribution, Finset.singleton_subset_iff] using hmul
    · simp [hzero I hI, contribution]
  have hSwap (L : List (ℤ × Finset (Fin 29) × Finset (Fin 29))) :
      ∑ I, (L.map fun r ↦ contribution r I).sum =
        (L.map fun r ↦ (r.1 : ℝ) * (moment r.2.1 - moment r.2.2)).sum := by
    induction L with
    | nil => simp
    | cons r L ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
      congr 1
      simp [contribution, moment, Finset.mul_sum, ← Finset.sum_sub_distrib, mul_sub]
  have hAvg :
      N * moment {0} ≤ D + (C.map fun r ↦ (r.1 : ℝ) * (moment r.2.1 - moment r.2.2)).sum := by
    have hm := Finset.sum_le_sum (fun I (_ : I ∈ (Finset.univ : Finset (Finset (Fin 29)))) ↦ hPoint I)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hmass, mul_one, hSwap] at hm
    exact hm
  have hErr :
      (C.map fun r ↦ (r.1 : ℝ) * (moment r.2.1 - moment r.2.2)).sum ≤ W * ε := by
    unfold W
    rw [← List.sum_map_mul_right]
    refine List.sum_le_sum ?_
    intro r hr
    calc
      (r.1 : ℝ) * (moment r.2.1 - moment r.2.2)
          ≤ |(r.1 : ℝ) * (moment r.2.1 - moment r.2.2)| := le_abs_self _
      _ = |(r.1 : ℝ)| * |moment r.2.1 - moment r.2.2| := abs_mul _ _
      _ ≤ |(r.1 : ℝ)| * ε := mul_le_mul_of_nonneg_left (hshape r hr) (abs_nonneg _)
  have hBound : (N + W) * ε < N / 4 - D := by
    dsimp [ε]
    rw [← mul_div_assoc, div_lt_iff₀ hTotal, mul_comm (N + W)]
    exact mul_lt_mul_of_pos_left (by linarith) hgap
  have hm : N * (1 / 4 - ε) ≤ N * moment {0} := mul_le_mul_of_nonneg_left hroot hN
  linarith

end OMA.R_Erdos1070_erdos_1070_parts_ii_R1
