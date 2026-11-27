import OMAStatements.S_oeis_a276674
import Mathlib

namespace OMA.A276674Proof

open ArithmeticFunction

theorem two_carm_le (x m : ℕ) (hx : 1 ≤ x) (hm : 0 < m) (h : x - carmichael x = 2 * m) :
    2 * carmichael x ≤ x := by
  have : NeZero x := ⟨by omega⟩
  have hdvd := carmichael_dvd_totient x
  have htle : x.totient ≤ x := Nat.totient_le x
  have htpos : 0 < x.totient := Nat.totient_pos.mpr (by omega)
  have hcard : Nat.card (ZMod x)ˣ = x.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  by_cases hcyc : IsCyclic (ZMod x)ˣ
  · have he : carmichael x = x.totient := by
      rw [carmichael_eq_exponent', IsCyclic.exponent_eq_card, hcard]
    rcases (ZMod.isCyclic_units_iff x).mp hcyc with h0 | h0 | h0 | h0 | ⟨p, k, hp, hodd, hk, h0 | h0⟩
    · omega
    · subst h0
      rw [he] at h ⊢
      simp at h
      omega
    · subst h0
      rw [he] at h ⊢
      simp at h
      omega
    · subst h0
      rw [he]
      have : Nat.totient 4 = 2 := by decide
      omega
    · subst h0
      rw [he, Nat.totient_prime_pow hp (by omega)] at h
      have hp1 : 1 ≤ p := hp.one_lt.le
      have hpow : p ^ k = p ^ (k - 1) * p := by
        rw [← pow_succ]; congr 1; omega
      have hodd2 : Odd (p ^ (k - 1)) := hodd.pow
      obtain ⟨r, hr⟩ := hodd2
      have : p ^ (k - 1) * (p - 1) + p ^ (k - 1) = p ^ (k - 1) * p := by
        rw [← mul_add_one]; congr 1; omega
      exfalso
      omega
    · subst h0
      have hcop : Nat.Coprime 2 (p ^ k) := by
        apply Nat.Coprime.pow_right
        rw [Nat.coprime_two_left]
        exact hodd
      rw [he, Nat.totient_mul hcop, Nat.totient_two, one_mul]
      have := Nat.totient_le (p ^ k)
      omega
  · have hne : carmichael x ≠ x.totient := by
      intro he
      apply hcyc
      apply IsCyclic.of_exponent_eq_card
      rw [← carmichael_eq_exponent', he, hcard]
    obtain ⟨k, hk⟩ := hdvd
    rcases k with _ | _ | k
    · omega
    · omega
    · have : carmichael x * (k + 1 + 1) = carmichael x * k + 2 * carmichael x := by ring
      rw [hk, this] at htle
      omega

end OMA.A276674Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a276674.main := by
  intro x m hx hm h
  have := OMA.A276674Proof.two_carm_le x m hx hm h
  omega
