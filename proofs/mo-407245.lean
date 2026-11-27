import OMAStatements.S_mo_407245
import Mathlib

/-!
# Lists of equipartitions forcing a pair to meet half the time

A list of length three or four fails to force such a pair exactly when its
partitions are pairwise orthogonal: every pair of distinct elements meets at
most once. Four orthogonal equipartitions, repeated cyclically, give a list of
any length `r ≥ 3` in which each pair meets at most `⌈r / 4⌉ < r / 2` times.
-/

namespace MO407245

open OMA.S_mo_407245

theorem orthogonal_of_true {k n r : ℕ} (h : hasOrthogonal k n r = true) :
    ∃ P : Family k n r, valid P ∧ ∀ x y, x ≠ y → (meetings P x y).card ≤ 1 := by
  unfold hasOrthogonal at h
  exact of_decide_eq_true h

theorem not_orthogonal_of_false {k n r : ℕ} (h : hasOrthogonal k n r = false) :
    ¬ ∃ P : Family k n r, valid P ∧ ∀ x y, x ≠ y → (meetings P x y).card ≤ 1 := by
  unfold hasOrthogonal at h
  exact of_decide_eq_false h

/-- Without `r` orthogonal equipartitions, every list of length `r` has a pair meeting twice. -/
theorem meets_twice {k n r : ℕ} (h : hasOrthogonal k n r = false) (P : Family k n r)
    (hP : valid P) : ∃ x y, x ≠ y ∧ 2 ≤ (meetings P x y).card := by
  by_contra hc
  apply not_orthogonal_of_false h
  refine ⟨P, hP, fun x y hxy => ?_⟩
  by_contra hlt
  exact hc ⟨x, y, hxy, by omega⟩

theorem forces_three {k n : ℕ} (h : hasOrthogonal k n 3 = false) : forces k n 3 := by
  intro P hP
  obtain ⟨x, y, hxy, hc⟩ := meets_twice h P hP
  exact ⟨x, y, hxy, by omega⟩

theorem forces_four {k n : ℕ} (h : hasOrthogonal k n 4 = false) : forces k n 4 := by
  intro P hP
  obtain ⟨x, y, hxy, hc⟩ := meets_twice h P hP
  exact ⟨x, y, hxy, by omega⟩

theorem not_forces_three {k n : ℕ} (h : hasOrthogonal k n 3 = true) : ¬ forces k n 3 := by
  obtain ⟨P, hP, horth⟩ := orthogonal_of_true h
  intro hf
  obtain ⟨x, y, hxy, hle⟩ := hf P hP
  have := horth x y hxy
  omega

/-- A residue class modulo four has at most `⌈r / 4⌉` members below `r`. -/
theorem residue_card (r j : ℕ) :
    (Finset.univ.filter (fun i : Fin r => i.val % 4 = j)).card ≤ (r + 3) / 4 := by
  have hinj : Set.InjOn (fun i : Fin r => i.val / 4)
      (Finset.univ.filter (fun i : Fin r => i.val % 4 = j) : Finset (Fin r)) := by
    intro a ha b hb hab
    have ha' : a.val % 4 = j := by simpa using ha
    have hb' : b.val % 4 = j := by simpa using hb
    have hab' : a.val / 4 = b.val / 4 := hab
    apply Fin.ext
    omega
  have himage : (Finset.univ.filter (fun i : Fin r => i.val % 4 = j)).image
      (fun i : Fin r => i.val / 4) ⊆ Finset.range ((r + 3) / 4) := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    have := i.isLt
    rw [Finset.mem_range]
    omega
  calc (Finset.univ.filter (fun i : Fin r => i.val % 4 = j)).card
      = ((Finset.univ.filter (fun i : Fin r => i.val % 4 = j)).image
          (fun i : Fin r => i.val / 4)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range ((r + 3) / 4)).card := Finset.card_le_card himage
    _ = (r + 3) / 4 := Finset.card_range _

theorem not_forces_of_four {k n : ℕ} (h : hasOrthogonal k n 4 = true) (r : ℕ) (hr : 3 ≤ r) :
    ¬ forces k n r := by
  obtain ⟨P, hP, horth⟩ := orthogonal_of_true h
  intro hf
  have hQ : valid (fun i : Fin r => P ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩) :=
    fun i b => hP _ b
  obtain ⟨x, y, hxy, hle⟩ := hf _ hQ
  obtain ⟨j, hj⟩ := Finset.card_le_one_iff_subset_singleton.mp (horth x y hxy)
  have hsub : meetings (fun i : Fin r => P ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩) x y ⊆
      Finset.univ.filter (fun i : Fin r => i.val % 4 = j.val) := by
    intro i hi
    have hi' : P ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ x =
        P ⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ y := by
      simpa [meetings] using hi
    have hmem : (⟨i.val % 4, Nat.mod_lt _ (by norm_num)⟩ : Fin 4) ∈ meetings P x y := by
      simp only [meetings, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi'
    have heq := Finset.mem_singleton.mp (hj hmem)
    have hval : i.val % 4 = j.val := congrArg Fin.val heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hval
  have h1 := Finset.card_le_card hsub
  have h2 := residue_card r j.val
  omega

end MO407245

theorem OMA.solution : type_of% @OMA.S_mo_407245.main := by
  intro k n _ _
  by_cases h3 : OMA.S_mo_407245.hasOrthogonal k n 3 = true
  · by_cases h4 : OMA.S_mo_407245.hasOrthogonal k n 4 = true
    · have ht : OMA.S_mo_407245.threshold k n = none := by
        unfold OMA.S_mo_407245.threshold
        rw [if_pos h3, if_pos h4]
      rw [ht]
      exact fun r hr => MO407245.not_forces_of_four h4 r hr
    · have ht : OMA.S_mo_407245.threshold k n = some 4 := by
        unfold OMA.S_mo_407245.threshold
        rw [if_pos h3, if_neg h4]
      rw [ht]
      refine ⟨⟨by norm_num, MO407245.forces_four (Bool.eq_false_iff.mpr h4)⟩, ?_⟩
      rintro r ⟨hr, hf⟩
      by_contra hlt
      have hr3 : r = 3 := by omega
      subst hr3
      exact MO407245.not_forces_three h3 hf
  · have ht : OMA.S_mo_407245.threshold k n = some 3 := by
      unfold OMA.S_mo_407245.threshold
      rw [if_neg h3]
    rw [ht]
    exact ⟨⟨le_refl 3, MO407245.forces_three (Bool.eq_false_iff.mpr h3)⟩, fun r hr => hr.1⟩
