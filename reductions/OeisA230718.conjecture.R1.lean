import FormalConjectures.OEIS.«230718»

-- Credit: @ArtemCherbaev

namespace OMA.R_OeisA230718_conjecture_R1

open Finset

/-- Find a suffix of consecutive powers divisible by the endpoint power.
The last two summands must fit beneath the endpoint power. This forces
the endpoint into a finite interval for every exponent. -/
def H1 : Prop :=
  ∃ n N k : ℕ, 3 < n ∧ 3 ≤ N ∧ k ∈ Icc 1 (N - 2) ∧
    (N - 1) ^ n + (N - 2) ^ n ≤ N ^ n ∧
    ∀ p ∈ N.primeFactors, p ^ (n * N.factorization p) ∣ ∑ i ∈ Ico k N, i ^ n

/-- Bound the whole prefix by two endpoint powers when the last pair fits. -/
def H2 : Prop :=
  ∀ n N : ℕ, 3 < n → 3 ≤ N → N ≤ 3 * n →
    (N - 1) ^ n + (N - 2) ^ n ≤ N ^ n →
    (∑ i ∈ range N, i ^ n) < 2 * N ^ n

theorem power_drop (x d m : ℕ) :
    x ^ (m + 1) ≤ (x - d) ^ (m + 1) + (m + 1) * d * x ^ m := by
  induction m with
  | zero => simp; omega
  | succ m ih =>
    have h₁ := Nat.mul_le_mul_right (x - d) ih
    have h₂ := Nat.mul_le_mul_left (x ^ (m + 1)) (show x ≤ (x - d) + d by omega)
    have h₃ := Nat.mul_le_mul_left ((m + 1) * d * x ^ m) (Nat.sub_le x d)
    simp only [pow_succ] at h₁ h₂ h₃ ⊢
    nlinarith only [h₁, h₂, h₃]

theorem endpoint_bound {n N : ℕ} (hn : 0 < n) (hN : 0 < N)
    (h : (N - 1) ^ n + (N - 2) ^ n ≤ N ^ n) : N ≤ 3 * n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h₁ := power_drop N 1 m
  have h₂ := power_drop N 2 m
  have total := Nat.add_le_add h₁ h₂
  have rearrange :
      (N - 1) ^ (m + 1) + (m + 1) * 1 * N ^ m +
      ((N - 2) ^ (m + 1) + (m + 1) * 2 * N ^ m) =
      ((N - 1) ^ (m + 1) + (N - 2) ^ (m + 1)) + N ^ m * (3 * (m + 1)) := by ring
  rw [rearrange] at total
  change (N - 1) ^ (m + 1) + (N - 2) ^ (m + 1) ≤ N ^ (m + 1) at h
  have hh : N ^ m * N ≤ N ^ m * (3 * (m + 1)) := by
    rw [← pow_succ]
    omega
  exact Nat.le_of_mul_le_mul_left hh (pow_pos hN _)

theorem main : H1 → H2 → type_of% @OeisA230718.conjecture := by
  classical
  rintro ⟨n, N, k, hn, hN, hk, hpair, hd⟩ hprefix
  let S := ∑ i ∈ Ico k N, i ^ n
  have hkr := mem_Icc.mp hk
  have hkN : k ∈ Ico k N := mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hsmall : S ≤ ∑ i ∈ range N, i ^ n := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact mem_range.mpr (mem_Ico.mp hi).2
    · intros
      exact Nat.zero_le _
  have hpos : 0 < S := lt_of_lt_of_le (pow_pos (by omega : 0 < k) n)
    (single_le_sum (fun i _ => Nat.zero_le (i ^ n)) hkN)
  have hlt : S < 2 * N ^ n :=
    lt_of_le_of_lt hsmall (hprefix n N hn hN (endpoint_bound (by omega) (by omega) hpair) hpair)
  have hdiv : N ^ n ∣ S := by
    apply (Nat.factorization_prime_le_iff_dvd (pow_ne_zero n (by omega)) hpos.ne').mp
    intro p hp
    by_cases hpd : p ∣ N
    · have hm := hd p (Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩)
      have hv := (hp.pow_dvd_iff_le_factorization hpos.ne').mp hm
      simpa [Nat.factorization_pow, S] using hv
    · simp [Nat.factorization_pow, Nat.factorization_eq_zero_of_not_dvd hpd]
  obtain ⟨q, hq⟩ := hdiv
  change S = N ^ n * q at hq
  have hq1 : q = 1 := by
    by_contra hne
    have hq0 : q ≠ 0 := by intro hz; simp [hz] at hq; omega
    have hmul := Nat.mul_le_mul_left (N ^ n) (show 2 ≤ q by omega)
    rw [Nat.mul_comm (N ^ n) 2] at hmul
    omega
  have heq : S = N ^ n := by simpa [hq1] using hq
  let T : Set ℕ := {M | 3 ≤ M ∧ ∃ j ∈ Icc 1 (M - 2), (∑ i ∈ Ico j M, i ^ n) = M ^ n}
  have hmem : N ∈ T := ⟨hN, k, hk, heq⟩
  have hinf : sInf T ∈ T := Nat.sInf_mem ⟨N, hmem⟩
  have hmin : sInf T ≠ 0 := by have := hinf.1; omega
  refine ⟨n, hn, ?_⟩
  unfold OeisA230718.a
  rw [if_neg (by omega : n ≠ 0)]
  change (if sInf T = 0 then 0 else sInf T ^ n) ≠ 0
  rw [if_neg hmin]
  exact pow_ne_zero _ hmin

end OMA.R_OeisA230718_conjecture_R1
