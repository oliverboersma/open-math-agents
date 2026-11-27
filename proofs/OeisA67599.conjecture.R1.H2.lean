import OMAReductions.R_OeisA67599_conjecture_R1

-- Step OeisA67599.conjecture.R1.H2
-- Credit: @caa1982

theorem OMA.solution : OMA.R_OeisA67599_conjecture_R1.H2 := by
  intro q hq7 hq
  have hpf : (2401 * q).primeFactorsList = [7, 7, 7, 7, q] := by
    have hperm : ([7, 7, 7, 7, q] : List ℕ).Perm (2401 * q).primeFactorsList := by
      apply Nat.primeFactorsList_unique
      · simp; ring
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl
        · decide
        · decide
        · decide
        · decide
        · exact hq
    have hpw : ([7, 7, 7, 7, q] : List ℕ).Pairwise (· ≤ ·) := by
      simp [List.pairwise_cons, Nat.le_of_lt hq7]
    exact (List.Perm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hpw
      (Nat.primeFactorsList_sorted (2401 * q)).pairwise hperm).symm
  have hge2 : ¬ (2401 * q < 2) := by omega
  have h7ne : (7 : ℕ) ≠ q := by omega
  have hdedup : ([7, 7, 7, 7, q] : List ℕ).dedup = [7, q] := by
    rw [List.dedup_cons_of_mem (by simp), List.dedup_cons_of_mem (by simp),
        List.dedup_cons_of_mem (by simp), List.dedup_cons_of_notMem (by simp [h7ne]),
        List.dedup_cons_of_notMem (by simp), List.dedup_nil]
  have hc7 : ([7, 7, 7, 7, q] : List ℕ).count 7 = 4 := by
    simp [List.count_cons, h7ne.symm]
  have hcq : ([7, 7, 7, 7, q] : List ℕ).count q = 1 := by
    simp [List.count_cons, h7ne]
  unfold OeisA67599.a
  rw [if_neg hge2, hpf, hdedup]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, hc7, hcq, List.foldl_cons, List.foldl_nil, OeisA67599.concatenateNats]
  have hd7 : (Nat.digits 10 7).length = 1 := by decide
  have hd4 : (Nat.digits 10 4).length = 1 := by decide
  have hd1 : (Nat.digits 10 1).length = 1 := by decide
  rw [hd7, hd4, hd1]
  ring
