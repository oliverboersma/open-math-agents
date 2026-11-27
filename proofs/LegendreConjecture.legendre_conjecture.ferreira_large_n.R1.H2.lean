import OMAReductions.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R1

/-! Let n + 1 be the number of primes up to m^2, so the n-th prime p is at most m^2, the next
prime q exceeds m^2, and n ≥ N. Andrica at n gives sqrt q < 1 + sqrt p ≤ 1 + m, hence
q < (m + 1)^2. -/

theorem OMA.solution : OMA.R_LegendreConjecture_legendre_conjecture_ferreira_large_n_R1.H2 := by
  intro N hN m hm
  have hinf := Nat.infinite_setOfPred_prime
  have hNc : N < Nat.count Nat.Prime (m ^ 2 + 1) :=
    (Nat.lt_nth_iff_count_lt (p := Nat.Prime) hinf).2 (Nat.lt_succ_of_lt hm)
  obtain ⟨n, hn⟩ : ∃ n, Nat.count Nat.Prime (m ^ 2 + 1) = n + 1 :=
    ⟨Nat.count Nat.Prime (m ^ 2 + 1) - 1, by omega⟩
  have hnN : N ≤ n := by omega
  have hp : Nat.nth Nat.Prime n < m ^ 2 + 1 :=
    (Nat.lt_nth_iff_count_lt (p := Nat.Prime) hinf).1 (by rw [hn]; exact Nat.lt_succ_self n)
  have hq : m ^ 2 + 1 ≤ Nat.nth Nat.Prime (n + 1) :=
    (Nat.count_le_iff_le_nth (p := Nat.Prime) hinf).1 (le_of_eq hn)
  have hA := hN n hnN
  refine ⟨(n + 1).nth Nat.Prime, ⟨by omega, ?_⟩, Nat.prime_nth_prime _⟩
  by_contra hcon
  have hge : (m + 1) ^ 2 ≤ (n + 1).nth Nat.Prime := not_lt.1 hcon
  have h1 : (m : ℝ) + 1 ≤ Real.sqrt ((n + 1).nth Nat.Prime) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast hge
  have h2 : Real.sqrt (n.nth Nat.Prime) ≤ m := by
    rw [Real.sqrt_le_left (Nat.cast_nonneg m)]
    exact_mod_cast (by omega : n.nth Nat.Prime ≤ m ^ 2)
  linarith
