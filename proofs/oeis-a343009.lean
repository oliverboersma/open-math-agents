import OMAStatements.S_oeis_a343009
import Mathlib

-- Problem: oeis-a343009, a(n) = (n^(2n) - 1)/(n^2 - 1) is a Fermat pseudoprime to base n.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- N = a(n) is the geometric sum of (n^2)^k for k < n, so N (n^2 - 1) + 1 = (n^n)^2.
-- Composite: N (n^2 - 1) = (n^n - 1)(n^n + 1) and N > n^n + 1, so a prime N could divide
-- neither factor. Probable prime: N - 1 = n^2 * (geometric sum with n - 1 terms) is divisible
-- by 2n, so n^(N-1) is a power of n^(2n), and N divides n^(2n) - 1.

namespace A343009

lemma geom_parity (m : ℕ) (hm : Odd m) (t : ℕ) :
    (∑ k ∈ Finset.range t, m ^ k) % 2 = t % 2 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have h1 : m ^ t % 2 = 1 := Nat.odd_iff.mp hm.pow
    omega

lemma geom_shift (m t : ℕ) :
    ∑ k ∈ Finset.range (t + 1), m ^ k = m * ∑ k ∈ Finset.range t, m ^ k + 1 := by
  rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [pow_succ']

end A343009

theorem OMA.solution : type_of% @OMA.S_oeis_a343009.main := by
  intro n hn
  have hn1 : n ≠ 1 := by omega
  have hsq9 : 9 ≤ n ^ 2 := by nlinarith
  obtain ⟨N, hN⟩ : ∃ N, N = ∑ k ∈ Finset.range n, (n ^ 2) ^ k := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X, X = n ^ n := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q + 1 = n ^ 2 := ⟨n ^ 2 - 1, by omega⟩
  have haN : OMA.S_oeis_a343009.a n = N := by
    unfold OMA.S_oeis_a343009.a
    rw [if_neg hn1, hN, Nat.geomSum_eq (by omega) n, ← pow_mul]
  rw [haN]
  -- the basic identity
  have hF1 : N * Q + 1 = X ^ 2 := by
    have h := geom_sum_mul_add Q n
    rw [hQ] at h
    rw [hN, h, hX, ← pow_mul, ← pow_mul, mul_comm]
  have hX3 : n ^ 3 ≤ X := by rw [hX]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hXQ : Q + 2 ≤ X := by
    have h3 : n ^ 3 = n * n ^ 2 := by ring
    nlinarith
  have hNX : X + 1 < N := by
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : N * Q ≤ (X + 1) * Q := Nat.mul_le_mul_right Q hcon
    have h2 : (X + 1) * (Q + 2) ≤ (X + 1) * X := Nat.mul_le_mul_left _ hXQ
    nlinarith
  refine ⟨?_, ?_, by omega⟩
  · -- probable prime
    show N ∣ n ^ (N - 1) - 1
    have hsplit : N = n ^ 2 * (∑ k ∈ Finset.range (n - 1), (n ^ 2) ^ k) + 1 := by
      have h := A343009.geom_shift (n ^ 2) (n - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
      rw [hN, h]
    obtain ⟨q, hq⟩ : ∃ q, N - 1 = 2 * n * q := by
      rcases Nat.even_or_odd n with he | ho
      · obtain ⟨t, ht⟩ := he
        refine ⟨t * ∑ k ∈ Finset.range (n - 1), (n ^ 2) ^ k, ?_⟩
        rw [hsplit, Nat.add_sub_cancel]
        have h2 : n ^ 2 = 2 * n * t := by rw [ht]; ring
        rw [h2]; ring
      · have hpar := A343009.geom_parity (n ^ 2) ho.pow (n - 1)
        have hodd : n % 2 = 1 := Nat.odd_iff.mp ho
        have hev : (∑ k ∈ Finset.range (n - 1), (n ^ 2) ^ k) % 2 = 0 := by omega
        obtain ⟨s, hs⟩ := Nat.dvd_of_mod_eq_zero hev
        refine ⟨n * s, ?_⟩
        rw [hsplit, Nat.add_sub_cancel, hs]; ring
    have hpow : n ^ (2 * n) = N * Q + 1 := by
      rw [hF1, hX, ← pow_mul, mul_comm]
    have hd1 : N ∣ n ^ (2 * n) - 1 := by
      rw [hpow, Nat.add_sub_cancel]; exact dvd_mul_right N Q
    have hd2 : n ^ (2 * n) - 1 ∣ (n ^ (2 * n)) ^ q - 1 :=
      Nat.sub_one_dvd_pow_sub_one _ _
    rw [hq, pow_mul]
    exact hd1.trans hd2
  · -- composite
    intro hp
    have h1 : X ^ 2 - 1 ^ 2 = N * Q := by rw [one_pow]; omega
    rw [Nat.sq_sub_sq] at h1
    have hdvd : N ∣ (X + 1) * (X - 1) := by rw [h1]; exact dvd_mul_right N Q
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · have := Nat.le_of_dvd (by omega) h; omega
    · have := Nat.le_of_dvd (by omega) h; omega
