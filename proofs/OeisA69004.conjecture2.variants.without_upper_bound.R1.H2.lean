import OMAReductions.R_OeisA69004_conjecture2_variants_without_upper_bound_R1

/-!
Proof of the sieve-count identity for OEIS A69004: primality of `n^2 + s^2` for
coprime opposite-parity inputs is detected exactly by the small-prime sieve.
-/

open Finset

theorem key_iff_69004 (n s : ℕ) (hs : s ∈ Finset.Ico 1 n) :
    (n ^ 2 + s ^ 2).Prime ↔
      n % 2 ≠ s % 2 ∧ n.Coprime s ∧
        ∀ p ∈ Finset.range ((n ^ 2 + s ^ 2).sqrt + 1), p.Prime → p % 4 = 1 →
          ¬p ∣ n ^ 2 + s ^ 2 := by
  rw [Finset.mem_Ico] at hs
  obtain ⟨hs1, hsn⟩ := hs
  have hn2 : 2 ≤ n := by omega
  have hsq2 : ∀ x : ℕ, (x ^ 2) % 2 = x % 2 := by
    intro x
    rw [Nat.pow_mod]
    rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with h | h <;> rw [h]
  have hs2pos : 1 ≤ s ^ 2 := by
    rw [pow_two]
    calc 1 = 1 * 1 := rfl
    _ ≤ s * s := Nat.mul_le_mul hs1 hs1
  have hq5 : 5 ≤ n ^ 2 + s ^ 2 := by
    have h1 : 4 ≤ n ^ 2 := by
      rw [pow_two]
      calc 4 = 2 * 2 := rfl
      _ ≤ n * n := Nat.mul_le_mul hn2 hn2
    have h2 : 1 ≤ s ^ 2 := by
      rw [pow_two]
      calc 1 = 1 * 1 := rfl
      _ ≤ s * s := Nat.mul_le_mul hs1 hs1
    omega
  constructor
  · intro hpq
    refine ⟨?_, ?_, ?_⟩
    · by_contra! hpar
      have e1 : (n ^ 2) % 2 = n % 2 := hsq2 n
      have e2 : (s ^ 2) % 2 = s % 2 := hsq2 s
      have hsum : (n ^ 2 + s ^ 2) % 2 = 0 := by
        rw [Nat.add_mod, e1, e2, hpar]
        omega
      rcases hpq.eq_two_or_odd with h2 | hodd
      · omega
      · omega
    · have hdvd : n.gcd s ∣ n ^ 2 + s ^ 2 := by
        have d1 : n.gcd s ∣ n ^ 2 := by
          rw [pow_two]
          exact dvd_mul_of_dvd_left (Nat.gcd_dvd_left n s) n
        have d2 : n.gcd s ∣ s ^ 2 := by
          rw [pow_two]
          exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right n s) s
        exact Nat.dvd_add d1 d2
      rcases hpq.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact h1
      · exfalso
        have hgcdle : n.gcd s ≤ n := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left n s)
        rw [h1] at hgcdle
        have hqgt : n < n ^ 2 + s ^ 2 := by
          have h3 : n ≤ n ^ 2 := by
            rw [pow_two]
            calc n = n * 1 := (mul_one n).symm
            _ ≤ n * n := Nat.mul_le_mul_left n (by omega)
          omega
        omega
    · intro p hpmem hpprime hp4 hdvd
      rw [Finset.mem_range] at hpmem
      rcases hpq.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact hpprime.ne_one h1
      · exfalso
        have hsqrtlt : (n ^ 2 + s ^ 2).sqrt < n ^ 2 + s ^ 2 := Nat.sqrt_lt_self (by omega)
        omega
  · intro ⟨hpar, hcop, hsieve⟩
    by_contra hnotprime
    have hq1 : n ^ 2 + s ^ 2 ≠ 1 := by omega
    have hpprime : (n ^ 2 + s ^ 2).minFac.Prime := Nat.minFac_prime hq1
    have hpdvd : (n ^ 2 + s ^ 2).minFac ∣ n ^ 2 + s ^ 2 := Nat.minFac_dvd _
    have hqpos : 0 < n ^ 2 + s ^ 2 := by omega
    have hplt : (n ^ 2 + s ^ 2).minFac < n ^ 2 + s ^ 2 := by
      rcases eq_or_ne (n ^ 2 + s ^ 2).minFac (n ^ 2 + s ^ 2) with h | h
      · exfalso
        rw [h] at hpprime
        exact hnotprime hpprime
      · exact lt_of_le_of_ne (Nat.le_of_dvd hqpos hpdvd) h
    have hpdvd' := hpdvd
    obtain ⟨m, hm⟩ := hpdvd'
    have hm0 : m ≠ 0 := by
      intro hm0
      rw [hm0, mul_zero] at hm
      omega
    have hm2 : 2 ≤ m := by
      rcases (by omega : m = 1 ∨ 2 ≤ m) with hm1 | hm2
      · exfalso
        have hqprime : (n ^ 2 + s ^ 2).Prime := by
          rw [hm, hm1, mul_one]
          exact hpprime
        exact hnotprime hqprime
      · exact hm2
    have hrprime : m.minFac.Prime := Nat.minFac_prime (by omega)
    have hrdvdm : m.minFac ∣ m := Nat.minFac_dvd m
    have hrdvdq : m.minFac ∣ n ^ 2 + s ^ 2 :=
      dvd_trans hrdvdm ⟨(n ^ 2 + s ^ 2).minFac, by rw [mul_comm]; exact hm⟩
    have hrge : (n ^ 2 + s ^ 2).minFac ≤ m.minFac := Nat.minFac_le_of_dvd hrprime.two_le hrdvdq
    have hrm : m.minFac ≤ m := Nat.le_of_dvd (by omega) hrdvdm
    have hp2 : (n ^ 2 + s ^ 2).minFac * (n ^ 2 + s ^ 2).minFac ≤ n ^ 2 + s ^ 2 := by
      calc (n ^ 2 + s ^ 2).minFac * (n ^ 2 + s ^ 2).minFac
          ≤ (n ^ 2 + s ^ 2).minFac * m.minFac :=
            Nat.mul_le_mul_left _ hrge
      _ ≤ (n ^ 2 + s ^ 2).minFac * m := Nat.mul_le_mul_left _ hrm
      _ = n ^ 2 + s ^ 2 := hm.symm
    have hpsqrt : (n ^ 2 + s ^ 2).minFac ≤ (n ^ 2 + s ^ 2).sqrt := Nat.le_sqrt.mpr hp2
    have hpmem : (n ^ 2 + s ^ 2).minFac ∈ Finset.range ((n ^ 2 + s ^ 2).sqrt + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hpsqrt)
    have hqodd : (n ^ 2 + s ^ 2) % 2 = 1 := by
      have e1 : (n ^ 2) % 2 = n % 2 := hsq2 n
      have e2 : (s ^ 2) % 2 = s % 2 := hsq2 s
      rw [Nat.add_mod, e1, e2]
      rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with hn0 | hn0 <;>
        rcases (by omega : s % 2 = 0 ∨ s % 2 = 1) with hs0 | hs0 <;> omega
    have hpodd : (n ^ 2 + s ^ 2).minFac % 2 = 1 := by
      rcases (by omega : (n ^ 2 + s ^ 2).minFac % 2 = 0 ∨ (n ^ 2 + s ^ 2).minFac % 2 = 1) with hp0 | hp0
      · exfalso
        have h2q : 2 ∣ n ^ 2 + s ^ 2 := dvd_trans (Nat.dvd_of_mod_eq_zero hp0) hpdvd
        rw [Nat.dvd_iff_mod_eq_zero] at h2q
        omega
      · exact hp0
    have hpndvdn : ¬(n ^ 2 + s ^ 2).minFac ∣ n := by
      intro hdn
      have hdn2 : (n ^ 2 + s ^ 2).minFac ∣ n ^ 2 :=
        dvd_trans hdn ⟨n, pow_two n⟩
      have hds2z : ((n ^ 2 + s ^ 2).minFac : ℤ) ∣ (s : ℤ) ^ 2 := by
        have hqz : ((n ^ 2 + s ^ 2).minFac : ℤ) ∣ (n : ℤ) ^ 2 + (s : ℤ) ^ 2 := by
          exact_mod_cast hpdvd
        have hnz : ((n ^ 2 + s ^ 2).minFac : ℤ) ∣ (n : ℤ) ^ 2 := by
          exact_mod_cast hdn2
        have hsub := dvd_sub hqz hnz
        have heq : (n : ℤ) ^ 2 + (s : ℤ) ^ 2 - (n : ℤ) ^ 2 = (s : ℤ) ^ 2 := by ring
        rwa [heq] at hsub
      have hds2 : (n ^ 2 + s ^ 2).minFac ∣ s ^ 2 := by exact_mod_cast hds2z
      have hds : (n ^ 2 + s ^ 2).minFac ∣ s := hpprime.dvd_of_dvd_pow hds2
      have hdg : (n ^ 2 + s ^ 2).minFac ∣ n.gcd s := Nat.dvd_gcd hdn hds
      have hg1 : n.gcd s = 1 := hcop
      rw [hg1] at hdg
      exact hpprime.ne_one (Nat.dvd_one.mp hdg)
    have : Fact (n ^ 2 + s ^ 2).minFac.Prime := ⟨hpprime⟩
    have hnmod : (n : ZMod (n ^ 2 + s ^ 2).minFac) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hpndvdn
    have hcast : ((n ^ 2 + s ^ 2 : ℕ) : ZMod (n ^ 2 + s ^ 2).minFac) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      exact hpdvd
    have hxy : (s : ZMod (n ^ 2 + s ^ 2).minFac) ^ 2 =
        -(n : ZMod (n ^ 2 + s ^ 2).minFac) ^ 2 := by
      have h2 : (n : ZMod (n ^ 2 + s ^ 2).minFac) ^ 2 +
          (s : ZMod (n ^ 2 + s ^ 2).minFac) ^ 2 = 0 := by
        rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
        exact hpdvd
      linear_combination h2
    have hp4ne3 : (n ^ 2 + s ^ 2).minFac % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_sq' hnmod hxy
    have hp4 : (n ^ 2 + s ^ 2).minFac % 4 = 1 := by omega
    exact (hsieve _ hpmem hpprime hp4) hpdvd

theorem OMA.solution : OMA.R_OeisA69004_conjecture2_variants_without_upper_bound_R1.H2 := by
  intro n
  unfold OeisA69004.a
  rw [← Finset.card_filter]
  congr 1
  ext s
  simp only [Finset.mem_filter]
  exact and_congr_right (fun hs => key_iff_69004 n s hs)
