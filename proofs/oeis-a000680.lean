import OMAStatements.S_oeis_a000680

-- Complete proof of OEIS A000680 (Schulte / Fried primality criterion)
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a000680

private lemma two_pow_dvd_two_mul_factorial (n : ℕ) : 2 ^ n ∣ (2 * n).factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h1, Nat.factorial_succ, Nat.factorial_succ, pow_succ']
    have h2 : 2 ∣ (2 * n + 1 + 1) := ⟨n + 1, by omega⟩
    have h3 : 2 * 2 ^ n ∣ (2 * n + 1 + 1) * (2 * n).factorial := mul_dvd_mul h2 ih
    calc
      2 * 2 ^ n ∣ (2 * n + 1 + 1) * (2 * n).factorial := h3
      _ ∣ (2 * n + 1 + 1) * ((2 * n + 1) * (2 * n).factorial) := by
        refine ⟨2 * n + 1, ?_⟩
        ring

private lemma mul_two_pow_eq (n : ℕ) :
    2 ^ n * (a n + 2 ^ n) = (2 * n).factorial + 4 ^ n := by
  rw [mul_add, a, Nat.mul_div_cancel' (two_pow_dvd_two_mul_factorial n)]
  have h4 : 2 ^ n * 2 ^ n = 4 ^ n := by
    rw [← mul_pow]
    norm_num
  rw [h4]

theorem OMA.solution : type_of% @OMA.S_oeis_a000680.main := by
  intro n hn
  constructor
  · intro hdvd
    by_contra hnp
    set m : ℕ := 2 * n + 1 with hm
    have hm1 : m ≠ 1 := by omega
    set q : ℕ := m.minFac with hq_def
    have hqp : q.Prime := Nat.minFac_prime hm1
    have hqm : q ∣ m := Nat.minFac_dvd m
    have hq_le : q ≤ m := Nat.le_of_dvd (by omega) hqm
    have hq_ne : q ≠ m := by
      intro hEq
      exact hnp (hEq ▸ hqp)
    have hq_le_2n : q ≤ 2 * n := by omega
    have hq_fac : q ∣ (2 * n).factorial := Nat.dvd_factorial hqp.pos hq_le_2n
    have hq_sum : q ∣ (2 * n).factorial + 4 ^ n := by
      rw [← mul_two_pow_eq]
      exact dvd_mul_of_dvd_right (dvd_trans hqm hdvd) (2 ^ n)
    have hq_4pow : q ∣ 4 ^ n := (Nat.dvd_add_right hq_fac).mp hq_sum
    have h4eq : 4 ^ n = 2 ^ (2 * n) := by
      rw [pow_mul]
      norm_num
    rw [h4eq] at hq_4pow
    have hq_dvd_2 : q ∣ 2 := hqp.dvd_of_dvd_pow hq_4pow
    have hq_eq_2 : q = 2 := by
      have hle2 : q ≤ 2 := Nat.le_of_dvd (by decide) hq_dvd_2
      have hge2 : 2 ≤ q := hqp.two_le
      omega
    rw [hq_eq_2] at hqm
    omega
  · intro hp
    have hcop2 : Nat.Coprime 2 (2 * n + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have hcop : Nat.Coprime (2 * n + 1) (2 ^ n) :=
      (hcop2.symm).pow_right n
    apply hcop.dvd_of_dvd_mul_left
    rw [mul_two_pow_eq]
    rw [← ZMod.natCast_eq_zero_iff]
    haveI : Fact (2 * n + 1).Prime := ⟨hp⟩
    have hw : (((2 * n).factorial : ℕ) : ZMod (2 * n + 1)) = -1 := by
      simpa using ZMod.wilsons_lemma (2 * n + 1)
    have h2ne : ((2 : ℕ) : ZMod (2 * n + 1)) ≠ 0 := by
      intro h0
      have hd : (2 * n + 1) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * n + 1)).mp h0
      have hle : 2 * n + 1 ≤ 2 := Nat.le_of_dvd (by decide) hd
      omega
    have hf : ((2 : ℕ) : ZMod (2 * n + 1)) ^ (2 * n) = 1 := by
      simpa using ZMod.pow_card_sub_one_eq_one h2ne
    have h4eq : 4 ^ n = 2 ^ (2 * n) := by
      rw [pow_mul]
      norm_num
    rw [Nat.cast_add, h4eq, Nat.cast_pow, hw, hf]
    ring
