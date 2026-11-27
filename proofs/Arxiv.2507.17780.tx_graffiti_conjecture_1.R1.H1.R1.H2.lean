import OMAReductions.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1

-- Step Arxiv.2507.17780.tx_graffiti_conjecture_1.R1.H1.R1.H2: hypothesis H2 of reduction Arxiv.2507.17780.tx_graffiti_conjecture_1.R1.H1.R1

/-!
Strong induction on the length. The empty list has residue `0`; a list starting with `0` has
residue equal to its length; otherwise one Havel-Hakimi step shortens the list by one, and the
residue is that of the shorter list.
-/

theorem OMA.solution : OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1.H2 := by
  unfold OMA.R_Arxiv_2507_17780_tx_graffiti_conjecture_1_R1_H1_R1.H2
  intro s
  induction hn : s.length using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    cases s with
    | nil => simp [SimpleGraph.residueAux]
    | cons a t =>
      cases a with
      | zero =>
        simp only [List.length_cons] at hn
        simp [SimpleGraph.residueAux]
        omega
      | succ d =>
        rw [SimpleGraph.residueAux]
        have hlen : (SimpleGraph.havelHakimiStep ((d + 1) :: t)).length = t.length :=
          SimpleGraph.havelHakimiStep_length_cons _ _
        have hlt : (SimpleGraph.havelHakimiStep ((d + 1) :: t)).length < n := by
          rw [hlen, ← hn]
          simp
        have h := ih _ hlt (SimpleGraph.havelHakimiStep ((d + 1) :: t)) rfl
        rw [hlen] at h
        simp only [List.length_cons] at hn
        omega
        exact Nat.succ_ne_zero d
