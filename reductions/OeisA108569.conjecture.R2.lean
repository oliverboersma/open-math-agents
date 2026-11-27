import FormalConjectures.OEIS.«108569»

/-! Eliminate odd prime powers of exponent at least two, then separate odd primes from the remaining composites. -/

namespace OMA.R_OeisA108569_conjecture_R2

open OeisA108569

/-- No odd prime power with exponent at least two belongs to the sequence. -/
theorem not_A_odd_prime_pow (p k : ℕ) (hp : p.Prime) (hpOdd : Odd p) :
    ¬ A (p ^ (k + 2)) := by
  rintro ⟨_, heq⟩
  have hp2 : 2 < p := by
    have := hp.two_le
    obtain ⟨d, hd⟩ := hpOdd
    omega
  have ht : p ^ (k + 2) + (p ^ (k + 2)).totient =
      p ^ (k + 1) * (2 * p - 1) := by
    rw [Nat.totient_prime_pow_succ hp, pow_succ, ← Nat.mul_add]
    congr 1
    omega
  have hc : p.Coprime (2 * p - 1) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    have := Nat.dvd_sub (show p ∣ 2 * p from dvd_mul_left p 2) h
    have hh : 2 * p - (2 * p - 1) = 1 := by omega
    rw [hh] at this
    exact hp.not_dvd_one this
  rw [ht, Nat.totient_mul (hc.pow_left _), Nat.totient_prime_pow_succ hp,
    Nat.totient_prime_pow_succ hp, pow_succ] at heq
  have hfac : 0 < p ^ k * (p - 1) := Nat.mul_pos (pow_pos hp.pos _) (by omega)
  have heq' : (p ^ k * (p - 1)) * p =
      (p ^ k * (p - 1)) * (2 * p - 1).totient := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using heq
  have h := Nat.eq_of_mul_eq_mul_left hfac heq'
  have he : Even p := h.symm ▸ Nat.totient_even (by omega : 2 < 2 * p - 1)
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hpOdd
  omega

/-- The indexed conjecture is equivalent to a statement about positive odd arguments. -/
theorem conjecture_iff_no_odd_collision :
    (∀ n, 0 < n → Even (a n)) ↔
      ∀ m : ℕ, 1 < m → Odd m → m.totient ≠ (m + m.totient).totient := by
  constructor
  · intro h m hm hodd heq
    have ha : A m := ⟨by omega, heq⟩
    have hindex : a (Nat.count A m) = m := Nat.nth_count ha
    have hcount : 0 < Nat.count A m := by
      by_contra! hle
      rw [show Nat.count A m = 0 by omega, a_0] at hindex
      omega
    have he := h _ hcount
    rw [hindex] at he
    obtain ⟨x, hx⟩ := he
    obtain ⟨y, hy⟩ := hodd
    omega
  · intro h n hn
    by_cases hz : a n = 0
    · simp [hz]
    have ha : A (a n) := Nat.nth_mem_of_ne_zero hz
    have hne : a n ≠ 1 := by
      intro heq
      have hzero : Nat.count A 1 = 0 := by decide
      have hindex : Nat.count A (a n) = n := Nat.count_nth (Nat.lt_card_toFinset_of_nth_ne_zero hz)
      rw [heq, hzero] at hindex
      omega
    rcases Nat.even_or_odd (a n) with he | ho
    · exact he
    · exact (h _ (by have := ha.1; omega) ho ha.2).elim

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → p.totient ≠ (p + p.totient).totient

def H2 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → ¬ m.Prime →
    (∀ p k : ℕ, p.Prime → m ≠ p ^ (k + 2)) →
    m.totient ≠ (m + m.totient).totient

theorem main : H1 → H2 → type_of% @OeisA108569.conjecture := by
  intro h1 h2
  apply conjecture_iff_no_odd_collision.mpr
  intro m hm ho he
  by_cases hp : m.Prime
  · exact h1 m hp ho he
  apply h2 m hm ho hp _ he
  intro p k hprime heq
  subst m
  have hodd : Odd p := (Nat.odd_pow_iff (by omega)).mp ho
  exact not_A_odd_prime_pow p k hprime hodd ⟨by omega, he⟩

end OMA.R_OeisA108569_conjecture_R2
