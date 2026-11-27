import OMAReductions.R_Erdos100_erdos_100_variants_guth_katz_R1
import Mathlib

-- Step Erdos100.erdos_100.variants.guth_katz.R1.H2: hypothesis H2 of reduction Erdos100.erdos_100.variants.guth_katz.R1
-- Credit: @ivillar (original proof).
-- Strategy. The distances lie in [0, diam A] and are pairwise at least 1 apart, so by induction on the
-- largest element a finite such set has at most diam A + 1 elements.

namespace OMA.Erdos100H2

/-- A finite set of reals in `[0, L]` with pairwise gaps at least one has at most `L + 1` elements. -/
lemma card_le_of_separated : ∀ S : Finset ℝ, ∀ L : ℝ, 0 ≤ L → (∀ x ∈ S, 0 ≤ x ∧ x ≤ L) →
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) → (S.card : ℝ) ≤ L + 1 := by
  intro S
  refine Finset.induction_on_max S ?_ ?_
  · intro L hL _ _
    simp
    linarith
  · intro a s hlt ih L hL hS hsep
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    have haL := (hS a (Finset.mem_insert_self a s)).2
    rcases s.eq_empty_or_nonempty with hs | ⟨x0, hx0⟩
    · subst hs
      simp
      linarith
    · have hgap : ∀ x ∈ s, x ≤ a - 1 := by
        intro x hx
        have h1 := hsep x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self a s)
          (ne_of_lt (hlt x hx))
        rw [abs_sub_comm, abs_of_pos (by linarith [hlt x hx])] at h1
        linarith
      have h0 : 0 ≤ a - 1 := le_trans (hS x0 (Finset.mem_insert_of_mem hx0)).1 (hgap x0 hx0)
      have := ih (a - 1) h0
        (fun x hx => ⟨(hS x (Finset.mem_insert_of_mem hx)).1, hgap x hx⟩)
        (fun x hx y hy hxy => hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)
      linarith

end OMA.Erdos100H2

theorem OMA.solution : OMA.R_Erdos100_erdos_100_variants_guth_katz_R1.H2 := by
  intro A hA
  have hbdd : Bornology.IsBounded (A : Set (EuclideanSpace ℝ (Fin 2))) := A.finite_toSet.isBounded
  have hmem : ∀ d ∈ distanceSet A, ∃ p ∈ A, ∃ q ∈ A, d = dist p q := by
    intro d hd
    rw [distanceSet, Finset.mem_image] at hd
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hd
    rw [Finset.mem_offDiag] at hpq
    exact ⟨p, hpq.1, q, hpq.2.1, rfl⟩
  exact OMA.Erdos100H2.card_le_of_separated (distanceSet A) _ Metric.diam_nonneg
    (fun d hd => by
      obtain ⟨p, hp, q, hq, rfl⟩ := hmem d hd
      exact ⟨dist_nonneg, Metric.dist_le_diam_of_mem hbdd hp hq⟩)
    (fun x hx y hy hxy => by
      obtain ⟨p, hp, q, hq, rfl⟩ := hmem x hx
      obtain ⟨p', hp', q', hq', rfl⟩ := hmem y hy
      exact hA p q p' q' hp hq hp' hq' hxy)
