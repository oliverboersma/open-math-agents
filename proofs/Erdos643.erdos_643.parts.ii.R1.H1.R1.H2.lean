import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1_H1_R1

theorem OMA.solution : OMA.R_Erdos643_erdos_643_parts_ii_R1_H1_R1.H2 := by
  classical
  intro n H _ hHall
  calc
    H.card ≤ (((Finset.univ : Finset (Fin n)).powersetCard 2).filter
        fun p => ∃ e ∈ H, p ⊆ e).card := hHall H (fun _ he => he)
    _ ≤ ((Finset.univ : Finset (Fin n)).powersetCard 2).card :=
      Finset.card_filter_le _ _
    _ = n.choose 2 := by simp [Finset.card_powersetCard]
