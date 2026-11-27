import OMAStatements.S_oeis_a349958
import Mathlib

-- Problem: oeis-a349958, the first row of Pascal's triangle containing a multiple of n is
-- row n exactly for prime powers.
-- Credit: @justusklocke-cloud (the owner of the agent is credited as the solver)
--
-- Prime powers p^k: row p^k contains C(p^k, 1); for m < p^k the exponent of p in C(m, j) is
-- at most log_p m < k. Other n > 1: with p the least prime factor, u = p^a its full power,
-- W = n / u > 1 (odd and coprime to p) and U = 2u, the Chinese remainder theorem gives
-- m1 < 2n with U | m1 and W | m1 - 1; put m2 = 2n + 1 - m1. Neither is 0, 1 or n, so one of
-- them lies in [2, n), and 2n | m (m - 1) gives n | C(m, 2).

namespace A349958

lemma no_small_row (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (m j : ℕ) (hj : j ≤ m)
    (hm : m < p ^ k) : ¬ p ^ k ∣ m.choose j := by
  intro hd
  have hpos : m.choose j ≠ 0 := (Nat.choose_pos hj).ne'
  have h1 : k ≤ (m.choose j).factorization p := (hp.pow_dvd_iff_le_factorization hpos).mp hd
  have h2 : (m.choose j).factorization p ≤ Nat.log p m := Nat.factorization_choose_le_log
  have h3 : Nat.log p m < k := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, Nat.log_zero_right]; exact hk
    · exact Nat.log_lt_of_lt_pow h0.ne' hm
  omega

lemma row_ok (n m : ℕ) (hd : 2 * n ∣ m * (m - 1)) : n ∣ m.choose 2 := by
  obtain ⟨c, hc⟩ := hd
  rw [Nat.choose_two_right, hc, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
  exact dvd_mul_right n c

/-- For `n > 1` that is not a prime power there is a row `m < n` containing a multiple. -/
lemma small_row (n : ℕ) (hn : 2 ≤ n) (hnp : ¬ IsPrimePow n) :
    ∃ m, 2 ≤ m ∧ m < n ∧ 2 * n ∣ m * (m - 1) := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨p, hpdef⟩ : ∃ p, p = n.minFac := ⟨_, rfl⟩
  have hp : p.Prime := by rw [hpdef]; exact Nat.minFac_prime (by omega)
  have hpn : p ∣ n := by rw [hpdef]; exact Nat.minFac_dvd n
  obtain ⟨a, hadef⟩ : ∃ a, a = n.factorization p := ⟨_, rfl⟩
  have ha : 0 < a := by rw [hadef]; exact hp.factorization_pos_of_dvd hn0 hpn
  obtain ⟨u, hudef⟩ : ∃ u, u = p ^ a := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = n / p ^ a := ⟨_, rfl⟩
  have huW : u * W = n := by
    rw [hudef, hWdef, hadef]; exact Nat.ordProj_mul_ordCompl_eq_self n p
  have hcopW : Nat.Coprime p W := by
    rw [hWdef, hadef]; exact Nat.coprime_ordCompl hp hn0
  have hu0 : 0 < u := by rw [hudef]; exact pow_pos hp.pos a
  have hpu : p ∣ u := by rw [hudef]; exact dvd_pow_self p ha.ne'
  have hW0 : 0 < W := by
    rcases Nat.eq_zero_or_pos W with h | h
    · rw [h, mul_zero] at huW; omega
    · exact h
  have hW1 : W ≠ 1 := by
    intro h
    apply hnp
    rw [isPrimePow_nat_iff]
    exact ⟨p, a, hp, ha, by rw [← huW, h, mul_one, hudef]⟩
  have hWodd : ¬ 2 ∣ W := by
    intro h2
    have h2n : 2 ∣ n := by rw [← huW]; exact Dvd.dvd.mul_left h2 u
    have hp2 : p = 2 := by
      rw [hpdef]; exact (Nat.minFac_eq_two_iff n).mpr h2n
    rw [hp2] at hcopW
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcopW h2
  have hco : Nat.Coprime (2 * u) W := by
    apply Nat.Coprime.mul_left
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hWodd
    · rw [hudef]; exact Nat.Coprime.pow_left a hcopW
  have hUW : 2 * u * W = 2 * n := by rw [mul_assoc, huW]
  obtain ⟨m1, hm1def⟩ : ∃ m1, m1 = (Nat.chineseRemainder hco 0 1 : ℕ) := ⟨_, rfl⟩
  have hmod := (Nat.chineseRemainder hco 0 1).2
  rw [← hm1def] at hmod
  have hlt : m1 < 2 * n := by
    rw [hm1def, ← hUW]
    exact Nat.chineseRemainder_lt_mul hco 0 1 (by omega) (by omega)
  have hU1 : 2 * u ∣ m1 := (Nat.modEq_zero_iff_dvd).mp hmod.1
  have hm1pos : 1 ≤ m1 := by
    rcases Nat.eq_zero_or_pos m1 with h | h
    · exfalso
      have h1 := hmod.2
      rw [h] at h1
      have h2 : W ∣ 1 := by
        have h3 := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).mp h1
        simpa using h3
      exact hW1 (Nat.dvd_one.mp h2)
    · exact h
  have hW1' : W ∣ m1 - 1 := (Nat.modEq_iff_dvd' hm1pos).mp hmod.2.symm
  have hm1ne1 : m1 ≠ 1 := by
    intro h
    rw [h] at hU1
    have := Nat.le_of_dvd (by norm_num) hU1
    omega
  have hm1nen : m1 ≠ n := by
    intro h
    rw [h, ← huW] at hU1
    have h2 : u * 2 ∣ u * W := by rw [mul_comm u 2]; exact hU1
    exact hWodd (Nat.dvd_of_mul_dvd_mul_left hu0 h2)
  have hm1nen1 : m1 ≠ n + 1 := by
    intro h
    rw [h] at hU1
    have hp1 : p ∣ n + 1 := (hpu.trans (Dvd.intro_left 2 rfl)).trans hU1
    have hp2 : p ∣ 1 := (Nat.dvd_add_right hpn).mp hp1
    exact hp.one_lt.ne' (Nat.dvd_one.mp hp2)
  have hd1 : 2 * n ∣ m1 * (m1 - 1) := by
    rw [← hUW]; exact mul_dvd_mul hU1 hW1'
  rcases Nat.lt_or_ge m1 n with hcase | hcase
  · exact ⟨m1, by omega, hcase, hd1⟩
  · refine ⟨2 * n + 1 - m1, by omega, by omega, ?_⟩
    have hU2n : 2 * u ∣ 2 * n := ⟨W, hUW.symm⟩
    have hW2n : W ∣ 2 * n := ⟨2 * u, by rw [← hUW, mul_comm]⟩
    have h1 : 2 * u ∣ 2 * n + 1 - m1 - 1 := by
      have h2 : 2 * n + 1 - m1 - 1 = 2 * n - m1 := by omega
      rw [h2]; exact Nat.dvd_sub hU2n hU1
    have h3 : W ∣ 2 * n + 1 - m1 := by
      have h4 : 2 * n + 1 - m1 = 2 * n - (m1 - 1) := by omega
      rw [h4]; exact Nat.dvd_sub hW2n hW1'
    have h5 : 2 * u * W ∣ (2 * n + 1 - m1 - 1) * (2 * n + 1 - m1) := mul_dvd_mul h1 h3
    rw [hUW] at h5
    rw [mul_comm (2 * n + 1 - m1) (2 * n + 1 - m1 - 1)]
    exact h5

end A349958

open OMA.S_oeis_a349958 in
theorem OMA.solution : type_of% @OMA.S_oeis_a349958.main := by
  intro n hn
  constructor
  · intro h
    by_contra hnp
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      have hmem : (0 : ℕ) ∈ {row : ℕ | containsMultiple n row} :=
        ⟨0, le_rfl, by rw [hn1]; exact one_dvd _⟩
      have := h.2 hmem
      omega
    · obtain ⟨m, hm2, hmn, hd⟩ := A349958.small_row n h2 hnp
      have hmem : m ∈ {row : ℕ | containsMultiple n row} :=
        ⟨2, hm2, A349958.row_ok n m hd⟩
      have := h.2 hmem
      omega
  · intro h
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp h
    constructor
    · exact ⟨1, Nat.one_le_pow _ _ hp.pos, by rw [Nat.choose_one_right]⟩
    · intro m hm
      obtain ⟨j, hj, hd⟩ := hm
      by_contra hlt
      rw [not_le] at hlt
      exact A349958.no_small_row p k hp hk m j hj hlt hd
