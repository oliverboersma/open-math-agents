import OMAReductions.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1

/-! Every colour class of a proper colouring is an independent set of G, that is a clique of
the complement, so it has fewer than k vertices; summing over the c classes gives n ≤ c k. -/

open Finset in
theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1.H2 := by
  intro n k c G hfree hcol
  classical
  obtain ⟨C⟩ := hcol
  have hclass : ∀ i : Fin c, (univ.filter (fun v => C v = i)).card < k := by
    intro i
    by_contra h
    push_neg at h
    obtain ⟨t, hts, htc⟩ := exists_subset_card_eq h
    apply hfree t
    refine ⟨?_, htc⟩
    intro u hu v hv huv
    rw [SimpleGraph.compl_adj]
    refine ⟨huv, fun hadj => C.valid hadj ?_⟩
    have hu' := (mem_filter.1 (hts hu)).2
    have hv' := (mem_filter.1 (hts hv)).2
    rw [hu', hv']
  calc n = (univ : Finset (Fin n)).card := by simp
    _ = ∑ i : Fin c, (univ.filter (fun v => C v = i)).card :=
        card_eq_sum_card_fiberwise (fun x _ => mem_univ (C x))
    _ ≤ ∑ _i : Fin c, k := sum_le_sum (fun i _ => (hclass i).le)
    _ = c * k := by simp
