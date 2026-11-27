import OMAStatements.S_mo_341315
import Mathlib

/-! For each odd prime, Euler's theorem supplies an exponent for which a high power of
two divides the number inside the radical. This proves Question 1 of MathOverflow 341315. -/

open UniqueFactorizationMonoid

theorem OMA.solution : type_of% @OMA.S_mo_341315.main := by
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨p, hbound, hp⟩ := Nat.exists_infinite_primes (B + 3)
  have ht : p < 2 ^ p := p.lt_two_pow_self
  let k := 2 ^ p - 1
  have hk : k + 1 = 2 ^ p := by dsimp [k]; omega
  refine ⟨p, ⟨hp, k, 1, by omega, le_rfl, by omega, ?_⟩, by omega⟩
  have hcop : p.Coprime 2 :=
    hp.coprime_iff_not_dvd.mpr fun h => by have := Nat.le_of_dvd (by decide : 0 < 2) h; omega
  have hpow := Nat.ModEq.pow_totient (hcop.pow_right (p + 1))
  rw [Nat.totient_prime_pow_succ Nat.prime_two, show 2 - 1 = 1 by decide, mul_one, ← hk] at hpow
  obtain ⟨d, hd⟩ := hpow.symm.dvd'
  have hp1 : 1 < p ^ (k + 1) := one_lt_pow₀ hp.one_lt (by omega)
  have hdpos : 0 < d := by
    by_contra! h
    have : d = 0 := by omega
    simp [this] at hd
    omega
  have hrad : radical (p ^ (k + 1) - 1) ≤ 2 * d := by
    rw [hd]
    have hdiv := radical_mul_dvd (a := (2 : ℕ) ^ (p + 1)) (b := d)
    rw [radical_pow 2 (by omega), radical_of_prime Nat.prime_two.prime, normalize_eq] at hdiv
    exact (Nat.le_of_dvd (by positivity) hdiv).trans
      (Nat.mul_le_mul_left 2 (Nat.radical_le_self_iff.mpr hdpos.ne'))
  have hlt : 2 * d < p ^ k := by
    apply Nat.lt_of_mul_lt_mul_right (a := p)
    calc
      2 * d * p ≤ 2 ^ (p + 1) * d := by
        rw [pow_succ]
        nlinarith [Nat.mul_le_mul_right (2*d) ht.le]
      _ < p ^ k * p := by rw [← hd, ← pow_succ]; omega
  simpa using lt_of_le_of_lt hrad hlt
