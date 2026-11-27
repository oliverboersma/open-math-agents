import FormalConjectures.ErdosProblems.«384»

/-!
An elementary proof of Ecklund's theorem (Erdős problem 384).

Write `n = m + k` with `2 ≤ k ≤ m` and suppose every prime factor `p` of `C(n, k)` has
`n < 2 * p`.  Any `a ≤ n` which is not prime is then coprime to `C(n, k)`.  Feeding this into
the classical identities

* `n * C(n-1, k-1) = k * C(n, k)`,
* `(m+1) * C(n, k-1) = k * C(n, k)`,
* `(k+1) * C(n, k+1) = m * C(n, k)`,
* `(m+1) * (m+2) * C(n, k-2) = k * (k-1) * C(n, k)`,
* `n * (n-1) * C(n-2, k-2) = k * (k-1) * C(n, k)`,

shows in turn that `n` and `m + 1` are prime (so `k` is odd and `m` is even), that `k + 1 ∣ m`,
that `m + 2 ∣ k * (k - 1)` and that `n - 1 ∣ k * (k - 1)`.  Writing `m = (k + 1) * s`, the last
divisibility is impossible for `s ≥ 2`, and for `s = 1` the one before it forces `k + 3 ∣ 12`,
that is `(n, k) = (7, 3)` or `(n, k) = (19, 9)`; the latter is excluded because `C(19, 9)` is even.
-/

/-- If every prime factor `p` of `N` satisfies `B < 2 * p`, then every non-prime `a` with
`0 < a ≤ B` is coprime to `N`. -/
theorem OMA.cop (N B a : ℕ) (hA : ∀ p : ℕ, p.Prime → p ∣ N → B < 2 * p)
    (ha0 : 0 < a) (haB : a ≤ B) (hnp : ¬ a.Prime) : Nat.Coprime a N := by
  by_contra h
  obtain ⟨p, hp, hpa, hpN⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have h2 := hA p hp hpN
  obtain ⟨c, rfl⟩ := hpa
  have hc : c = 1 := by
    rcases Nat.lt_or_ge c 2 with hc | hc
    · interval_cases c
      · simp at ha0
      · rfl
    · exfalso
      have h3 : p * 2 ≤ p * c := Nat.mul_le_mul_left p hc
      omega
  subst hc
  rw [mul_one] at hnp
  exact hnp hp

/-- The core statement, with `n = m + j + 2` and `k = j + 2`. -/
theorem OMA.core (m j : ℕ) (hkm : j + 2 ≤ m)
    (hA : ∀ p : ℕ, p.Prime → p ∣ (m + j + 2).choose (j + 2) → m + j + 2 < 2 * p) :
    m = 4 ∧ j = 1 := by
  obtain ⟨N, hN⟩ : ∃ N, N = (m + j + 2).choose (j + 2) := ⟨_, rfl⟩
  rw [← hN] at hA
  -- the central coefficient is even
  have hne : m ≠ j + 2 := by
    intro h
    have h2 : 2 ∣ N := by
      have h3 := Nat.two_dvd_centralBinom_of_one_le (n := j + 2) (by omega)
      rw [Nat.centralBinom_eq_two_mul_choose] at h3
      have h4 : m + j + 2 = 2 * (j + 2) := by omega
      rw [hN, h4]
      exact h3
    have h5 := hA 2 Nat.prime_two h2
    omega
  have hm : j + 3 ≤ m := by omega
  -- the five identities
  have I1 : (m + j + 2) * (m + j + 1).choose (j + 1) = N * (j + 2) := by
    rw [hN]
    exact Nat.add_one_mul_choose_eq (m + j + 1) (j + 1)
  have I2 : N * (j + 2) = (m + j + 2).choose (j + 1) * (m + 1) := by
    have h1 := Nat.choose_succ_right_eq (m + j + 2) (j + 1)
    have h2 : m + j + 2 - (j + 1) = m + 1 := by omega
    rw [h2] at h1
    rw [hN]
    exact h1
  have I2' : (m + j + 2).choose (j + 1) * (j + 1) = (m + j + 2).choose j * (m + 2) := by
    have h1 := Nat.choose_succ_right_eq (m + j + 2) j
    have h2 : m + j + 2 - j = m + 2 := by omega
    rw [h2] at h1
    exact h1
  have I3 : (m + j + 2).choose (j + 3) * (j + 3) = N * m := by
    have h1 := Nat.choose_succ_right_eq (m + j + 2) (j + 2)
    have h2 : m + j + 2 - (j + 2) = m := by omega
    rw [h2] at h1
    rw [hN]
    exact h1
  have I5 : (m + j + 1) * (m + j).choose j = (m + j + 1).choose (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq (m + j) j
  -- the divisibilities they give
  have D1 : (m + j + 2) ∣ N * (j + 2) := Dvd.intro _ I1
  have D2 : (m + 1) ∣ N * (j + 2) := Dvd.intro_left _ I2.symm
  have D3 : (j + 3) ∣ N * m := Dvd.intro_left _ I3
  have D4 : (m + 2) ∣ N * ((j + 2) * (j + 1)) := by
    have h1 : N * ((j + 2) * (j + 1)) = (m + j + 2).choose j * (m + 1) * (m + 2) := by
      calc N * ((j + 2) * (j + 1)) = N * (j + 2) * (j + 1) := by ring
        _ = (m + j + 2).choose (j + 1) * (m + 1) * (j + 1) := by rw [I2]
        _ = (m + j + 2).choose (j + 1) * (j + 1) * (m + 1) := by ring
        _ = (m + j + 2).choose j * (m + 2) * (m + 1) := by rw [I2']
        _ = (m + j + 2).choose j * (m + 1) * (m + 2) := by ring
    exact Dvd.intro_left _ h1.symm
  have D5 : (m + j + 1) ∣ N * ((j + 2) * (j + 1)) := by
    have h1 : N * ((j + 2) * (j + 1)) = (m + j + 1) * ((m + j + 2) * (m + j).choose j) := by
      calc N * ((j + 2) * (j + 1)) = N * (j + 2) * (j + 1) := by ring
        _ = (m + j + 2) * (m + j + 1).choose (j + 1) * (j + 1) := by rw [I1]
        _ = (m + j + 2) * ((m + j + 1).choose (j + 1) * (j + 1)) := by ring
        _ = (m + j + 2) * ((m + j + 1) * (m + j).choose j) := by rw [I5]
        _ = (m + j + 1) * ((m + j + 2) * (m + j).choose j) := by ring
    exact Dvd.intro _ h1.symm
  -- `n` is prime
  have hnP : (m + j + 2).Prime := by
    by_contra hnp
    have hc := OMA.cop N (m + j + 2) (m + j + 2) hA (by omega) le_rfl hnp
    have h1 := Nat.le_of_dvd (by omega) (Nat.Coprime.dvd_of_dvd_mul_left hc D1)
    omega
  -- `m + 1` is prime
  have hmP : (m + 1).Prime := by
    by_contra hnp
    have hc := OMA.cop N (m + j + 2) (m + 1) hA (by omega) (by omega) hnp
    have h1 := Nat.le_of_dvd (by omega) (Nat.Coprime.dvd_of_dvd_mul_left hc D2)
    omega
  -- parities
  have hn_odd : (m + j + 2) % 2 = 1 := by
    rcases hnP.eq_two_or_odd with h | h
    · omega
    · exact h
  have hm_odd : (m + 1) % 2 = 1 := by
    rcases hmP.eq_two_or_odd with h | h
    · omega
    · exact h
  -- `k + 1 ∣ m`
  have F2 : (j + 3) ∣ m := by
    have hnp : ¬ (j + 3).Prime := by
      intro hp
      rcases hp.eq_two_or_odd with h | h <;> omega
    have hc := OMA.cop N (m + j + 2) (j + 3) hA (by omega) (by omega) hnp
    exact Nat.Coprime.dvd_of_dvd_mul_left hc D3
  -- `m + 2 ∣ k (k - 1)`
  have F3 : (m + 2) ∣ (j + 2) * (j + 1) := by
    have hnp : ¬ (m + 2).Prime := by
      intro hp
      rcases hp.eq_two_or_odd with h | h <;> omega
    have hc := OMA.cop N (m + j + 2) (m + 2) hA (by omega) (by omega) hnp
    exact Nat.Coprime.dvd_of_dvd_mul_left hc D4
  -- `n - 1 ∣ k (k - 1)`
  have F4 : (m + j + 1) ∣ (j + 2) * (j + 1) := by
    have hnp : ¬ (m + j + 1).Prime := by
      intro hp
      rcases hp.eq_two_or_odd with h | h <;> omega
    have hc := OMA.cop N (m + j + 2) (m + j + 1) hA (by omega) (by omega) hnp
    exact Nat.Coprime.dvd_of_dvd_mul_left hc D5
  -- arithmetic
  obtain ⟨s, hs⟩ := F2
  have hs0 : s ≠ 0 := by
    rintro rfl
    omega
  rcases Nat.lt_or_ge s 2 with hs2 | hs2
  · -- `s = 1`
    have hs1 : s = 1 := by omega
    subst hs1
    have hm' : m = j + 3 := by omega
    subst hm'
    have h12 : (j + 5) ∣ 12 := by
      have e : (j + 2) * (j + 1) + (j + 5) * 2 = (j + 5) * j + 12 := by ring
      have h1 : (j + 5) ∣ (j + 2) * (j + 1) + (j + 5) * 2 :=
        Dvd.dvd.add F3 (dvd_mul_right _ _)
      rw [e] at h1
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h1
    have h1 := Nat.le_of_dvd (by norm_num) h12
    have hj : j ≤ 7 := by omega
    interval_cases j
    · omega
    · exact ⟨rfl, rfl⟩
    · omega
    · omega
    · omega
    · omega
    · omega
    · exfalso
      have h2 : 2 ∣ N := by
        rw [hN]
        decide
      have h3 := hA 2 Nat.prime_two h2
      omega
  · -- `s ≥ 2`
    exfalso
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
    subst hs
    have hle : (j + 3) * (t + 2) + j + 1 ≤ (j + 2) * (j + 1) :=
      Nat.le_of_dvd (by positivity) F4
    have hjt : t + 1 ≤ j := by
      by_contra h
      have h1 : j + 2 ≤ t + 2 := by omega
      have h2 : (j + 3) * (j + 2) ≤ (j + 3) * (t + 2) := Nat.mul_le_mul_left _ h1
      nlinarith
    have hd : ((j + 3) * (t + 2) + j + 1) ∣ 2 * ((t + 2) * (t + 1)) := by
      have e : (t + 3) ^ 2 * ((j + 2) * (j + 1))
          = ((j + 3) * (t + 2) + j + 1) * (j * t + 3 * j + 2) + 2 * ((t + 2) * (t + 1)) := by
        ring
      have h1 : ((j + 3) * (t + 2) + j + 1) ∣ (t + 3) ^ 2 * ((j + 2) * (j + 1)) :=
        Dvd.dvd.mul_left F4 _
      rw [e] at h1
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h1
    obtain ⟨c, hc⟩ := hd
    have hc1 : c = 1 := by
      have hc0 : c ≠ 0 := by
        rintro rfl
        have h1 : 0 < 2 * ((t + 2) * (t + 1)) := by positivity
        omega
      have hc2 : c < 2 := by
        by_contra h
        have h1 : 2 ≤ c := by omega
        have h2 : ((j + 3) * (t + 2) + j + 1) * 2 ≤ ((j + 3) * (t + 2) + j + 1) * c :=
          Nat.mul_le_mul_left _ h1
        have h3 : (t + 4) * (t + 2) ≤ (j + 3) * (t + 2) :=
          Nat.mul_le_mul_right _ (by omega)
        nlinarith
      omega
    subst hc1
    have h6 : (t + 3) ∣ 6 := by
      have e2 : (t + 3) * (j + 3) = (t + 3) * (2 * t) + 6 := by nlinarith
      have h1 : (t + 3) ∣ (t + 3) * (2 * t) + 6 := Dvd.intro _ e2
      exact (Nat.dvd_add_right (dvd_mul_right _ _)).mp h1
    have h7 := Nat.le_of_dvd (by norm_num) h6
    have ht : t ≤ 3 := by omega
    interval_cases t <;> omega

theorem OMA.solution : type_of% @Erdos384.erdos_384 := by
  intro n k hk hkn h₃ h₄
  by_contra hex
  have hcon : ∀ p : ℕ, p.Prime → p ∣ n.choose k → n < 2 * p := by
    intro p hp hd
    by_contra h
    exact hex ⟨p, hp, hd, by omega⟩
  rcases Nat.le_total k (n - k) with h | h
  · -- `k ≤ n - k`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + j + 2 := ⟨n - (j + 2), by omega⟩
    obtain ⟨h1, h2⟩ := OMA.core m j (by omega) hcon
    subst h1
    subst h2
    exact h₃ rfl
  · -- `n - k ≤ k`
    obtain ⟨j, rfl⟩ : ∃ j, n = k + j + 2 := ⟨n - k - 2, by omega⟩
    have e : (k + j + 2).choose k = (k + j + 2).choose (j + 2) := by
      rw [Nat.add_assoc]
      exact Nat.choose_symm_add
    rw [e] at hcon
    obtain ⟨h1, h2⟩ := OMA.core k j (by omega) hcon
    subst h1
    subst h2
    exact h₄ rfl
