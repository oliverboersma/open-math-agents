import FormalConjectures.Wikipedia.RefactorableNumber

-- Problem: Zelinsky's Conjecture (2002, Conjecture 32)
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/RefactorableNumber.lean:76 (declaration RefactorableNumber.zelinsky_refactorable_progression_conjecture)
-- Credit: @sho-404 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof idea: pick a prime p > n0 with p = 1 mod m and take n = n0 * p^(p-1).
-- Then d(n) = d(n0) * p, which divides n0 * p^(p-1), and n = n0 mod m.
theorem OMA.solution : type_of% @RefactorableNumber.zelinsky_refactorable_progression_conjecture := by
  intro m n₀ hm hn₀
  obtain ⟨hpos, hdvd⟩ := hn₀
  obtain ⟨p, hp, hlt, hmod⟩ := Nat.exists_prime_gt_modEq_one n₀ (Nat.one_le_iff_ne_zero.mp hm)
  have hp2 : 2 ≤ p := hp.two_le
  have hcop : Nat.Coprime n₀ (p ^ (p - 1)) := by
    apply Nat.Coprime.pow_right
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (fun h => absurd (Nat.le_of_dvd hpos h) (not_le.mpr hlt))))
  have hcard : (p ^ (p - 1)).divisors.card = p := by
    rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    omega
  have hpow : 2 ≤ p ^ (p - 1) := by
    calc 2 ≤ p := hp2
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (p - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  refine ⟨n₀ * p ^ (p - 1), ?_, ⟨?_, ?_⟩, ?_⟩
  · nlinarith
  · exact Nat.mul_pos hpos (by omega)
  · rw [hcop.card_divisors_mul, hcard]
    exact Nat.mul_dvd_mul hdvd (dvd_pow_self p (by omega))
  · have h1 : p ^ (p - 1) ≡ 1 [MOD m] := by
      simpa using hmod.pow (p - 1)
    simpa using Nat.ModEq.mul_left n₀ h1
