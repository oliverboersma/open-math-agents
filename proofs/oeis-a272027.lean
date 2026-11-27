import OMAStatements.S_oeis_a272027
import Mathlib

namespace OMAa272027

open ArithmeticFunction

theorem key (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ((p + 1) * sigma 1 n = sigma 1 (p * n) ↔ ¬ p ∣ n) := by
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
  have hcop : ∀ b, Nat.Coprime (p ^ b) m := fun b =>
    Nat.Coprime.pow_left b ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  have hm0 : m ≠ 0 := by rintro rfl; simp at hn
  have hM : 0 < sigma 1 m := sigma_pos 1 m hm0
  have h1 : p * (p ^ a * m) = p ^ (a + 1) * m := by ring
  rw [h1, isMultiplicative_sigma.map_mul_of_coprime (hcop _),
    isMultiplicative_sigma.map_mul_of_coprime (hcop _), sigma_one_apply_prime_pow hp,
    sigma_one_apply_prime_pow hp, Finset.sum_range_succ _ (a + 1)]
  set S := ∑ k ∈ Finset.range (a + 1), p ^ k with hS
  set M := sigma 1 m
  have iff1 : (p + 1) * (S * M) = (S + p ^ (a + 1)) * M ↔ S = p ^ a := by
    constructor
    · intro h
      have h' : (p * S) * M = (p * p ^ a) * M := by
        rw [pow_succ'] at h
        ring_nf at h ⊢
        linarith
      exact Nat.eq_of_mul_eq_mul_left hp.pos (Nat.eq_of_mul_eq_mul_right hM h')
    · intro h
      rw [h, pow_succ']
      ring
  rw [iff1]
  rcases a with _ | b
  · simp [hS, hm]
  · have hd : p ∣ p ^ (b + 1) * m := Dvd.dvd.mul_right (dvd_pow_self p (Nat.succ_ne_zero b)) m
    simp only [hd, not_true_eq_false, iff_false]
    rw [hS, Finset.sum_range_succ, Finset.sum_range_succ']
    simp

end OMAa272027

theorem OMA.solution : type_of% @OMA.S_oeis_a272027.main := by
  refine ⟨fun n hn => ?_, fun p hp n hn => OMAa272027.key p hp n hn⟩
  have h := OMAa272027.key 2 Nat.prime_two n hn
  simp only [OMA.S_oeis_a272027.a]
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact h
