import OMAStatements.S_oeis_a131401

-- Problem: A131401: Least number dividing Fibonacci(n) but not dividing Fibonacci(m) for m < n, or 0 if there is no such number.
-- Upstream: formal-conjectures statements/oeis-a131401.lean:0 (declaration OMA.S_oeis_a131401.main)
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- For n = 2 the set is empty, because fib 2 = fib 1, so its infimum is 0. For n = 1 and n >= 3 the number fib n itself lies in the set, since 0 < fib m < fib n for 1 <= m < n; the infimum of a nonempty set of naturals is a member, and 0 is not a member because 0 does not divide fib n > 0.

theorem OMA.solution : type_of% @OMA.S_oeis_a131401.main := by
  intro n hn
  unfold OMA.S_oeis_a131401.a
  constructor
  · intro h
    by_contra hne
    have hmem : Nat.fib n ∈
        {d : ℕ | d ∣ Nat.fib n ∧ ∀ m : ℕ, 1 ≤ m → m < n → ¬ d ∣ Nat.fib m} := by
      refine ⟨dvd_rfl, ?_⟩
      intro m hm1 hmn hdvd
      have hpos : 0 < Nat.fib m := Nat.fib_pos.2 (by omega)
      have hle := Nat.le_of_dvd hpos hdvd
      have hn3 : 3 ≤ n := by omega
      have hlt : Nat.fib m < Nat.fib n := by
        rcases Nat.lt_or_ge m 2 with h2 | h2
        · have hm : m = 1 := by omega
          subst hm
          have h3 : Nat.fib 3 ≤ Nat.fib n := Nat.fib_mono hn3
          have h32 : Nat.fib 3 = 2 := by decide
          rw [Nat.fib_one]
          omega
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
          obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
          exact Nat.fib_add_two_strictMono (by omega)
      omega
    have hs := Nat.sInf_mem ⟨_, hmem⟩
    rw [h] at hs
    have h0 := zero_dvd_iff.1 hs.1
    have hpos : 0 < Nat.fib n := Nat.fib_pos.2 (by omega)
    omega
  · rintro rfl
    have hempty : {d : ℕ | d ∣ Nat.fib 2 ∧ ∀ m : ℕ, 1 ≤ m → m < 2 → ¬ d ∣ Nat.fib m} = ∅ := by
      ext d
      constructor
      · rintro ⟨hd, hall⟩
        exact (hall 1 le_rfl (by norm_num) (by simpa using hd)).elim
      · intro h
        exact h.elim
    rw [hempty, Nat.sInf_empty]
