import OMAReductions.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2_R1
import Mathlib

-- Step Erdos258.erdos_258.variants.monotone.R2.H2.R1.H2.R1.H1: hypothesis H1 of reduction
-- Erdos258.erdos_258.variants.monotone.R2.H2.R1.H2.R1
-- Credit: @ivillar

/-!
Take `k²` distinct primes `q_m > M = H + k + 1` (`m < k²`), each at most `2^(m+1) M`, by iterating
Bertrand's postulate. By the Chinese remainder theorem choose `r` with
`r + j ≡ q_m^(t-1) (mod q_m^t)` for `j = ⌊m/k⌋ + 1`, and put `A = ∏ q_m^t`. For `N ≡ r (mod A)`,
the `k` primes of block `j` divide `N + j` exactly `t - 1` times, so `t^k ∣ d(N + j)`. Each `q_m`
divides `r + j`, hence does not divide `r + k + i + 1 = (r + j) + (k - j + i + 1)` as
`0 < k - j + i + 1 < q_m`. Finally `log A = t ∑ log q_m ≤ t k² (k² + log (H + k + 2))`.
-/

namespace OMA.Erdos258CRT

open Finset

noncomputable def nxt (n : ℕ) : ℕ :=
  if h : n ≠ 0 then Classical.choose (Nat.exists_prime_lt_and_le_two_mul n h) else 2

theorem nxt_spec {n : ℕ} (h : n ≠ 0) : (nxt n).Prime ∧ n < nxt n ∧ nxt n ≤ 2 * n := by
  unfold nxt
  rw [dif_pos h]
  exact Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul n h)

noncomputable def Q (M : ℕ) : ℕ → ℕ
  | 0 => nxt M
  | m + 1 => nxt (Q M m)

theorem Q_spec (M : ℕ) (hM : 0 < M) :
    ∀ m, (Q M m).Prime ∧ M < Q M m ∧ Q M m ≤ 2 ^ (m + 1) * M := by
  intro m
  induction m with
  | zero =>
    obtain ⟨h1, h2, h3⟩ := nxt_spec (n := M) hM.ne'
    exact ⟨h1, h2, by simpa [Q] using h3⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨g1, g2, g3⟩ := nxt_spec (n := Q M m) (by omega)
    show (nxt (Q M m)).Prime ∧ M < nxt (Q M m) ∧ nxt (Q M m) ≤ 2 ^ (m + 1 + 1) * M
    refine ⟨g1, by omega, ?_⟩
    calc nxt (Q M m) ≤ 2 * Q M m := g3
      _ ≤ 2 * (2 ^ (m + 1) * M) := Nat.mul_le_mul_left 2 h3
      _ = 2 ^ (m + 1 + 1) * M := by ring

theorem Q_strictMono (M : ℕ) (hM : 0 < M) : StrictMono (Q M) :=
  strictMono_nat_of_lt_succ fun m => by
    show Q M m < nxt (Q M m)
    exact (nxt_spec (by have := (Q_spec M hM m).2.1; omega)).2.1

end OMA.Erdos258CRT

open Finset OMA.Erdos258CRT in
theorem OMA.solution : OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2_R1.H1 := by
  unfold OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2_R1.H1
  intro k t H hk ht
  have hM : 0 < H + k + 1 := by omega
  let q : ℕ → ℕ := fun m => Q (H + k + 1) m
  have hqp : ∀ m, (q m).Prime := fun m => (Q_spec _ hM m).1
  have hqb : ∀ m, H + k + 1 < q m := fun m => (Q_spec _ hM m).2.1
  have hqinj : Function.Injective q := (Q_strictMono _ hM).injective
  let s : ℕ → ℕ := fun m => q m ^ t
  let a : ℕ → ℕ := fun m => q m ^ (t - 1) + q m ^ t - (m / k + 1)
  have hs : ∀ m ∈ range (k * k), s m ≠ 0 := fun m _ => pow_ne_zero _ (hqp m).ne_zero
  have pp : Set.Pairwise (range (k * k) : Set ℕ) (Function.onFun Nat.Coprime s) := by
    intro m _ m' _ hne
    exact Nat.Coprime.pow t t ((Nat.coprime_primes (hqp m) (hqp m')).mpr
      (fun h => hne (hqinj h)))
  let rr := Nat.chineseRemainderOfFinset a s (range (k * k)) hs pp
  have hrr : ∀ m ∈ range (k * k), rr.1 ≡ a m [MOD s m] := rr.2
  have hlt : rr.1 < ∏ m ∈ range (k * k), s m := Nat.chineseRemainderOfFinset_lt_prod a s hs pp
  have hpowlt : ∀ m, q m ^ (t - 1) < q m ^ t := fun m =>
    Nat.pow_lt_pow_right (hqp m).one_lt (by omega)
  -- the key congruence
  have KF : ∀ m ∈ range (k * k), rr.1 + (m / k + 1) ≡ q m ^ (t - 1) [MOD q m ^ t] := by
    intro m hm
    have hmk : m / k < k := Nat.div_lt_of_lt_mul (Finset.mem_range.mp hm)
    have hj : m / k + 1 ≤ q m ^ t := by
      have h1 : q m ≤ q m ^ t := Nat.le_self_pow (by omega) _
      have h2 := hqb m
      omega
    have h1 := (hrr m hm).add_right (m / k + 1)
    have h2 : a m + (m / k + 1) = q m ^ (t - 1) + q m ^ t := by
      show q m ^ (t - 1) + q m ^ t - (m / k + 1) + (m / k + 1) = _
      have := hpowlt m
      omega
    rw [h2] at h1
    exact h1.trans Nat.add_modEq_right
  refine ⟨∏ m ∈ range (k * k), s m, rr.1,
    Finset.prod_pos (fun m _ => pow_pos (hqp m).pos t), hlt, ?_, ?_, ?_⟩
  · -- the size of the modulus
    have hcast : ((∏ m ∈ range (k * k), s m : ℕ) : ℝ) = ∏ m ∈ range (k * k), ((q m : ℝ) ^ t) := by
      simp only [s, Nat.cast_prod, Nat.cast_pow]
    rw [hcast, Real.log_prod (fun m _ => pow_ne_zero _ (by exact_mod_cast (hqp m).ne_zero))]
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hLH : 0 ≤ Real.log ((H + k + 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have hterm : ∀ m ∈ range (k * k), Real.log ((q m : ℝ) ^ t) ≤
        (t : ℝ) * ((k : ℝ) ^ 2 + Real.log ((H + k + 2 : ℕ) : ℝ)) := by
      intro m hm
      rw [Real.log_pow]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg t)
      have hb := (Q_spec _ hM m).2.2
      have hm1 : m + 1 ≤ k * k := Finset.mem_range.mp hm
      have hqpos : (0 : ℝ) < q m := by exact_mod_cast (hqp m).pos
      have h1 : (q m : ℝ) ≤ 2 ^ (m + 1) * ((H + k + 1 : ℕ) : ℝ) := by exact_mod_cast hb
      have h2 : Real.log (q m : ℝ) ≤ (m + 1 : ℕ) * Real.log 2 + Real.log ((H + k + 1 : ℕ) : ℝ) := by
        calc Real.log (q m : ℝ) ≤ Real.log (2 ^ (m + 1) * ((H + k + 1 : ℕ) : ℝ)) :=
              Real.log_le_log hqpos h1
          _ = (m + 1 : ℕ) * Real.log 2 + Real.log ((H + k + 1 : ℕ) : ℝ) := by
              rw [Real.log_mul (by positivity) (by exact_mod_cast hM.ne'), Real.log_pow]
      have h3 : Real.log ((H + k + 1 : ℕ) : ℝ) ≤ Real.log ((H + k + 2 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast (by omega : H + k + 1 ≤ H + k + 2))
      have h4 : ((m + 1 : ℕ) : ℝ) ≤ (k : ℝ) ^ 2 := by
        rw [sq]; exact_mod_cast hm1
      have h5 : ((m + 1 : ℕ) : ℝ) * Real.log 2 ≤ (k : ℝ) ^ 2 := by
        have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        have := mul_le_mul h4 hlog2.le h0 (by positivity)
        linarith
      linarith
    calc (∑ m ∈ range (k * k), Real.log ((q m : ℝ) ^ t))
        ≤ ∑ _m ∈ range (k * k), (t : ℝ) * ((k : ℝ) ^ 2 + Real.log ((H + k + 2 : ℕ) : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) ^ 2 * ((t : ℝ) * ((k : ℝ) ^ 2 + Real.log ((H + k + 2 : ℕ) : ℝ))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ 4 * (t : ℝ) * (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 + Real.log ((H + k + 2 : ℕ) : ℝ)) := by
          have h0 : 0 ≤ (k : ℝ) ^ 2 * ((t : ℝ) * ((k : ℝ) ^ 2 + Real.log ((H + k + 2 : ℕ) : ℝ))) := by
            positivity
          nlinarith
  · -- divisor digits
    intro N hN j hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Icc.mp hj
    have hn0 : N + j ≠ 0 := by omega
    let B := Finset.Ico ((j - 1) * k) (j * k)
    have hBsub : B ⊆ range (k * k) := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      rw [Finset.mem_range]
      calc m < j * k := hm.2
        _ ≤ k * k := Nat.mul_le_mul_right k hjk
    have hdiv : ∀ m ∈ B, m / k + 1 = j := by
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hk0 : 0 < k := by omega
      have : m / k = j - 1 := Nat.div_eq_of_lt_le hm.1
        (by rw [show j - 1 + 1 = j by omega]; exact hm.2)
      omega
    have hfac : ∀ m ∈ B, (N + j).factorization (q m) = t - 1 := by
      intro m hm
      have hc : N + j ≡ q m ^ (t - 1) [MOD q m ^ t] := by
        have h1 : N ≡ rr.1 [MOD q m ^ t] :=
          Nat.ModEq.of_dvd (Finset.dvd_prod_of_mem s (hBsub hm)) hN
        have h2 := KF m (hBsub hm)
        rw [hdiv m hm] at h2
        exact (h1.add_right j).trans h2
      have hmod : (N + j) % (q m ^ t) = q m ^ (t - 1) := by
        rw [hc, Nat.mod_eq_of_lt (hpowlt m)]
      have hd1 : q m ^ (t - 1) ∣ N + j := by
        have := Nat.div_add_mod (N + j) (q m ^ t)
        rw [hmod] at this
        rw [← this]
        apply dvd_add _ dvd_rfl
        exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      have hd2 : ¬ q m ^ t ∣ N + j := by
        intro h
        have h0 := Nat.mod_eq_zero_of_dvd h
        rw [hmod] at h0
        exact (pow_pos (hqp m).pos _).ne' h0
      have l1 := ((hqp m).pow_dvd_iff_le_factorization hn0).mp hd1
      have l2 : ¬ t ≤ (N + j).factorization (q m) := fun h =>
        hd2 (((hqp m).pow_dvd_iff_le_factorization hn0).mpr h)
      omega
    have hBq : B.image q ⊆ (N + j).primeFactors := by
      intro p hp
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
      rw [Nat.mem_primeFactors]
      refine ⟨hqp m, ?_, hn0⟩
      have h1 : 1 ≤ (N + j).factorization (q m) := by rw [hfac m hm]; omega
      have h2 := ((hqp m).pow_dvd_iff_le_factorization hn0).mpr h1
      rwa [pow_one] at h2
    have e1 : ∏ m ∈ B, ((N + j).factorization (q m) + 1) = ∏ _m ∈ B, t :=
      Finset.prod_congr rfl (fun m hm => by rw [hfac m hm]; omega)
    have hcard : B.card = k := by
      rw [Nat.card_Ico, ← Nat.sub_mul, show j - (j - 1) = 1 by omega, one_mul]
    have hprod : ∏ p ∈ B.image q, ((N + j).factorization p + 1) = t ^ k := by
      rw [Finset.prod_image (fun x _ y _ h => hqinj h), e1, Finset.prod_const, hcard]
    rw [Nat.card_divisors hn0]
    calc t ^ j ∣ t ^ k := pow_dvd_pow t hjk
      _ = ∏ p ∈ B.image q, ((N + j).factorization p + 1) := hprod.symm
      _ ∣ ∏ p ∈ (N + j).primeFactors, ((N + j).factorization p + 1) :=
          Finset.prod_dvd_prod_of_subset _ _ _ hBq
  · -- coprimality of the following shifts
    intro i hi
    rw [Nat.coprime_prod_right_iff]
    intro m hm
    show Nat.Coprime _ (q m ^ t)
    apply Nat.Coprime.pow_right
    have hmk : m / k < k := Nat.div_lt_of_lt_mul (Finset.mem_range.mp hm)
    have hqd : q m ∣ rr.1 + (m / k + 1) := by
      have h3 : q m ∣ q m ^ (t - 1) := dvd_pow_self _ (by omega)
      have h2 : rr.1 + (m / k + 1) ≡ q m ^ (t - 1) [MOD q m] :=
        Nat.ModEq.of_dvd (dvd_pow_self _ (by omega)) (KF m hm)
      exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr h3))
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hqp m)]
    intro hd
    generalize hg : m / k = g at hqd hmk
    have hsplit : rr.1 + k + i + 1 = (rr.1 + (g + 1)) + (k - (g + 1) + i + 1) := by omega
    rw [hsplit] at hd
    have h3 := (Nat.dvd_add_right hqd).mp hd
    have h4 := Nat.le_of_dvd (by omega) h3
    have h5 := hqb m
    omega
