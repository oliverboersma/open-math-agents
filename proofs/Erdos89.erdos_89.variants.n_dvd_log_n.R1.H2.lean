import OMAReductions.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1
import Mathlib

/-!
Step H2 of Erdos89.erdos_89.variants.n_dvd_log_n.R1: Cauchy-Schwarz. Split the ordered pairs
of distinct points by their distance r; if m r pairs have distance r, then the number of pairs
is the sum of the m r and the number of equal-distance pairs of pairs is the sum of the m r ^ 2,
so (sum m r)^2 ≤ (number of distances) * (sum m r ^ 2).
-/

open scoped Classical in
theorem OMA.solution : OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1.H2 := by
  unfold OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1.H2
  intro S P
  have hmaps : ∀ z ∈ P, (fun z : _ × _ => dist z.1 z.2) z ∈ distanceSet S :=
    fun z hz => Finset.mem_image_of_mem _ hz
  have h1 : P.card = ∑ r ∈ distanceSet S, (P.filter (fun z => dist z.1 z.2 = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have h2 : ((P ×ˢ P).filter fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2).card =
      ∑ r ∈ distanceSet S, (P.filter (fun z => dist z.1 z.2 = r)).card ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun z => dist z.1.1 z.1.2)
      (t := distanceSet S) ?_]
    · apply Finset.sum_congr rfl
      intro r _
      rw [sq, ← Finset.card_product]
      congr 1
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨ha, hb⟩, he⟩, hr⟩
        exact ⟨⟨ha, hr⟩, hb, he.symm.trans hr⟩
      · rintro ⟨⟨ha, hra⟩, hb, hrb⟩
        exact ⟨⟨⟨ha, hb⟩, hra.trans hrb.symm⟩, hra⟩
    · intro z hz
      exact Finset.mem_image_of_mem _ (Finset.mem_product.mp (Finset.mem_filter.mp hz).1).1
  rw [h2, h1]
  exact sq_sum_le_card_mul_sum_sq
