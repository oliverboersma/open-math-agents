import OMAReductions.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2

-- Credit: @LDJAI

theorem OMA.solution : OMA.R_Erdos46_erdos_46_variants_infinitely_many_disjoint_R2.H2 := by
  intro P beyond
  classical
  choose block good above using beyond
  let bound : ℕ → ℕ := Nat.rec 0 (fun _ b => max b ((block b).sup id) + 1)
  have step (i : ℕ) : bound (i + 1) = max (bound i) ((block (bound i)).sup id) + 1 := rfl
  have inc : StrictMono bound := strictMono_nat_of_lt_succ (fun i => by
    rw [step]
    exact Nat.lt_succ_of_le (le_max_left _ _))
  have disj {i j : ℕ} (hij : i < j) : Disjoint (block (bound i)) (block (bound j)) := by
    apply Finset.disjoint_left.mpr
    intro n hi hj
    have hs : n ≤ (block (bound i)).sup id := Finset.le_sup (f := id) hi
    have hbefore : n < bound (i + 1) := by
      rw [step]
      exact Nat.lt_succ_of_le (hs.trans (le_max_right _ _))
    exact (Nat.not_lt_of_ge ((hbefore.le).trans (inc.monotone hij))) (above _ _ hj)
  exact ⟨fun i => block (bound i), fun i j h => (lt_or_gt_of_ne h).elim
    (fun hij => disj hij) (fun hji => (disj hji).symm), fun i => good _⟩
