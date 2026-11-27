import OMAReductions.R_Erdos389_erdos_389_R1_H2_R1

-- Compare prime exponents in the factorizations of the two nonzero products.
theorem OMA.solution : OMA.R_Erdos389_erdos_389_R1_H2_R1.H2 := by
  intro n k hn _ hval
  have hleft : (∏ i ∈ Finset.range k, (n + i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by omega
  have hright : (∏ i ∈ Finset.range k, (n + k + i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by omega
  apply (Nat.factorization_le_iff_dvd hleft hright).mp
  intro p
  by_cases hp : p.Prime
  · simpa only [Nat.factorization_def _ hp] using hval p hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
