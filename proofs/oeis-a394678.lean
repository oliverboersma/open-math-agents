import OMAStatements.S_oeis_a394678

open Nat

lemma dvd_fact_pred_of_composite (n : ℕ) (h1 : 1 < n) (hn : ¬ n.Prime) (h4 : n ≠ 4) :
    n ∣ (n - 1)! := by
  set p := n.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  obtain ⟨q, hq⟩ := hpn
  have hsq : p ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hn
  have hp2 : 2 ≤ p := hpp.two_le
  have hpq : p ≤ q := by
    rw [hq, pow_two] at hsq
    exact Nat.le_of_mul_le_mul_left hsq (by omega)
  have hqn : q < n := by
    rw [hq]; nlinarith
  rcases lt_or_eq_of_le hpq with hlt | heq
  · -- p < q ≤ n - 1
    have h1 : p * q ∣ q ! := by
      have hq1 : q ! = q * (q - 1)! := (Nat.mul_factorial_pred (by omega)).symm
      rw [hq1, mul_comm p q]
      exact Nat.mul_dvd_mul_left q (Nat.dvd_factorial (by omega) (by omega))
    rw [hq]
    exact h1.trans (Nat.factorial_dvd_factorial (by omega))
  · -- n = p ^ 2 with p ≥ 3
    subst heq
    have hp3 : 3 ≤ p := by
      by_contra hc
      have : p = 2 := by omega
      apply h4; rw [hq, this]
    have h1 : p * (2 * p) ∣ (2 * p)! := by
      have hq1 : (2 * p)! = (2 * p) * (2 * p - 1)! := (Nat.mul_factorial_pred (by omega)).symm
      rw [hq1, mul_comm p (2 * p)]
      exact Nat.mul_dvd_mul_left (2 * p) (Nat.dvd_factorial (by omega) (by omega))
    have h2 : p * p ∣ p * (2 * p) := Nat.mul_dvd_mul_left p (Dvd.intro_left 2 rfl)
    rw [hq]
    refine h2.trans (h1.trans (Nat.factorial_dvd_factorial ?_))
    have : 2 * p < p * p := by nlinarith
    omega

lemma mod_aux (N x r q : ℕ) (hx : x = N * q + r) (hr : r < N) : x % N = r := by
  rw [hx, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem OMA.solution : type_of% @OMA.S_oeis_a394678.main := by
  intro n hn1 hn4 hpr
  unfold OMA.S_oeis_a394678.a at hpr
  by_cases hn : n.Prime
  · refine ⟨hn, ?_⟩
    have hp2 := hn.two_le
    -- Wilson
    have hw : n ∣ (n - 1)! + 1 := by
      have := (Nat.prime_iff_fac_equiv_neg_one (by omega)).mp hn
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [this]; ring
    obtain ⟨m, hm⟩ := hw
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h] at hm; simp at hm
      · exact h
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hfac : n.factorial = n * (n - 1)! := (Nat.mul_factorial_pred (by omega)).symm
    have key : (n.factorial - 1) % n ^ 2 = n ^ 2 - n - 1 := by
      apply mod_aux (n ^ 2) _ _ m'
      · rw [hfac]
        have hz : n * (n - 1)! + n = n ^ 2 * m' + n ^ 2 := by
          calc n * (n - 1)! + n = n * ((n - 1)! + 1) := by ring
            _ = n * (n * (m' + 1)) := by rw [hm]
            _ = n ^ 2 * m' + n ^ 2 := by ring
        have : n + 1 ≤ n ^ 2 := by nlinarith
        omega
      · have : 1 ≤ n ^ 2 := by nlinarith
        omega
    rwa [key] at hpr
  · exfalso
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      norm_num at hpr
    have hd := dvd_fact_pred_of_composite n (by omega) hn hn4
    obtain ⟨k, hk⟩ := hd
    have hfac : n.factorial = n * (n - 1)! := (Nat.mul_factorial_pred (by omega)).symm
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · have := Nat.factorial_pos (n - 1); rw [hk, h0] at this; simp at this
      · exact h0
    have key : (n.factorial - 1) % n ^ 2 = n ^ 2 - 1 := by
      apply mod_aux (n ^ 2) _ _ (k - 1)
      · rw [hfac, hk]
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have : 1 ≤ n ^ 2 := by nlinarith
        have hz : n * (n * (k' + 1)) = n ^ 2 * k' + n ^ 2 := by ring
        rw [hz, Nat.add_sub_cancel]
        omega
      · have : 1 ≤ n ^ 2 := by nlinarith
        omega
    rw [key] at hpr
    have hf : n ^ 2 - 1 = (n - 1) * (n + 1) := by
      obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
      have : (t + 1) ^ 2 = t * (t + 1 + 1) + 1 := by ring
      rw [this, Nat.add_sub_cancel, Nat.add_sub_cancel]
    rw [hf] at hpr
    have h2 : n ≠ 2 := by rintro rfl; exact hn Nat.prime_two
    exact Nat.not_prime_mul (by omega) (by omega) hpr
