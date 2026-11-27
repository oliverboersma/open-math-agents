import OMAReductions.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1

-- Step Erdos997.erdos_997.variants.irrational.R1.H1.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_Erdos997_erdos_997_variants_irrational_R1_H1_R1.H2 := by
  rintro good k hk ⟨m, hm⟩
  refine ⟨m, m + k, ?_⟩
  have hfalse : (Finset.Ico m (m + k)).filter (fun i => good i = false) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i hi
    simp [hm i hi]
  have htrue : (Finset.Ico m (m + k)).filter (fun i => good i = true) = Finset.Ico m (m + k) :=
    Finset.filter_true_of_mem hm
  rw [hfalse, htrue, Finset.card_empty, Nat.card_Ico]
  omega
