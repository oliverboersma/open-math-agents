import OMAStatements.S_oeis_a163767

open OMA.S_oeis_a163767

theorem OMA.solution : type_of% @OMA.S_oeis_a163767.main := by
  intro s hs
  set n := ∏ p ∈ s, p with hn
  have hn0 : n ≠ 0 := Finset.prod_ne_zero_iff.2 fun p hp ↦ (hs _ hp).ne_zero
  have hsq : Squarefree n := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hs p hp) (hs q hq)).2 hpq)
    · intro p hp
      exact (hs p hp).prime.squarefree
  have hpf : n.primeFactors = s := Nat.primeFactors_prod hs
  have hcard : a n = (Nat.finMulAntidiag n n).card := by
    unfold a
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun f ↦ by simp [hn0])
  rw [hcard, Nat.card_finMulAntidiag_of_squarefree hsq,
    ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset, Nat.toFinset_factors, hpf]
