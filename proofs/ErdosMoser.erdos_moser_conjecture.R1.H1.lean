import OMAReductions.R_ErdosMoser_erdos_moser_conjecture_R1
import Mathlib

-- Step ErdosMoser.erdos_moser_conjecture.R1.H1: hypothesis H1 of reduction ErdosMoser.erdos_moser_conjecture.R1
-- Credit: @ivillar
-- H1 := ∀ k m : ℕ, 0 < k → 0 < m → Odd k → ErdosMoser.powerSum k m = m ^ k → k = 1 ∧ m = 3
--
-- For odd k, pairing i with (m - 1) - i shows (m - 1) ∣ 2 * powerSum k m. If the sum equals
-- m ^ k, coprimality of m - 1 and m forces m - 1 ∣ 2, so m ≤ 3, and only (k, m) = (1, 3) works.

namespace OMA.ErdosMoserH1

lemma powerSum_eq_range (k m : ℕ) (hk : 0 < k) :
    ErdosMoser.powerSum k m = ∑ i ∈ Finset.range m, i ^ k := by
  unfold ErdosMoser.powerSum
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hm]
    simp [Nat.zero_pow hk]

lemma dvd_two_mul (k n : ℕ) (hk : Odd k) :
    n ∣ 2 * ∑ i ∈ Finset.range (n + 1), i ^ k := by
  have hrefl : ∑ i ∈ Finset.range (n + 1), (n - i) ^ k = ∑ i ∈ Finset.range (n + 1), i ^ k := by
    have := Finset.sum_range_reflect (fun i => i ^ k) (n + 1)
    simpa using this
  have h2 : 2 * ∑ i ∈ Finset.range (n + 1), i ^ k =
      ∑ i ∈ Finset.range (n + 1), (i ^ k + (n - i) ^ k) := by
    rw [Finset.sum_add_distrib, hrefl]
    ring
  rw [h2]
  apply Finset.dvd_sum
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have := Odd.nat_add_dvd_pow_add_pow i (n - i) hk
  rwa [Nat.add_sub_cancel' hin] at this

end OMA.ErdosMoserH1

theorem OMA.solution : OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H1 := by
  unfold OMA.R_ErdosMoser_erdos_moser_conjecture_R1.H1
  intro k m hk hm hodd hsum
  rw [OMA.ErdosMoserH1.powerSum_eq_range k m hk] at hsum
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hdvd := OMA.ErdosMoserH1.dvd_two_mul k n hodd
  rw [hsum] at hdvd
  have hcop : Nat.Coprime n ((n + 1) ^ k) := by
    apply Nat.Coprime.pow_right
    simp
  have hn2 : n ∣ 2 := hcop.dvd_of_dvd_mul_right hdvd
  have hnle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hn2
  interval_cases n
  · simp [Finset.sum_range_succ, Nat.zero_pow hk] at hsum
  · simp [Finset.sum_range_succ, Nat.zero_pow hk] at hsum
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  · simp [Finset.sum_range_succ, Nat.zero_pow hk] at hsum
    refine ⟨?_, rfl⟩
    by_contra hk1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have h1 : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by norm_num) j
    have h2 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_add, pow_add] at hsum
    omega
