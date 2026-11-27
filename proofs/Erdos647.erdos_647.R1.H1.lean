import OMAReductions.R_Erdos647_erdos_647_R1

/-!
# A sharp divisor bound for the first reduction of Erdős problem 647

Maximizing `(a + 1)^6 / p^a` at each prime gives the largest possible value of
`(σ 0 m)^6 / m` over positive integers. Its sixth root lies between 138 and 139.
-/

open scoped BigOperators
open ArithmeticFunction.sigma

namespace OMA.Erdos647DivisorBound

/-- The exponent maximizing the factor `(a + 1)^6 / p^a` for a prime `p`. -/
private def peak (p : ℕ) : ℕ :=
  if p < 64 then
    match p with
    | 2 => 8
    | 3 => 4
    | 5 => 3
    | 7 | 11 => 2
    | _ => 1
  else 0

private def smallPrimes : Finset ℕ := (Finset.range 64).filter Nat.Prime

private theorem smallExponents :
    ∀ p : Fin 64, p.val.Prime → ∀ a : Fin 9,
      (a.val + 1) ^ 6 * p.val ^ peak p.val ≤
        (peak p.val + 1) ^ 6 * p.val ^ a.val := by
  decide

-- From exponent eight onward, the numerator grows by at most the smallest prime.
private theorem tailStep (a : ℕ) (ha : 8 ≤ a) :
    (a + 2) ^ 6 ≤ (a + 1) ^ 6 * 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ha
  ring_nf
  omega

private theorem localBound {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (a + 1) ^ 6 * p ^ peak p ≤ (peak p + 1) ^ 6 * p ^ a := by
  by_cases hsmall : p < 64
  · induction a with
    | zero => exact smallExponents ⟨p, hsmall⟩ hp 0
    | succ a ih =>
      by_cases ha : a < 8
      · exact smallExponents ⟨p, hsmall⟩ hp ⟨a + 1, by omega⟩
      · calc
          (a + 2) ^ 6 * p ^ peak p
              ≤ ((a + 1) ^ 6 * 2) * p ^ peak p :=
                Nat.mul_le_mul_right _ (tailStep a (by omega))
          _ = ((a + 1) ^ 6 * p ^ peak p) * 2 := mul_right_comm _ _ _
          _ ≤ ((a + 1) ^ 6 * p ^ peak p) * p := Nat.mul_le_mul_left _ hp.two_le
          _ ≤ _ := by simpa only [pow_succ, mul_assoc] using Nat.mul_le_mul_right p ih
  · have hlarge : 2 ^ 6 ≤ p := by omega
    simp only [peak, if_neg hsmall, pow_zero, zero_add, one_pow, one_mul, mul_one]
    calc
      (a + 1) ^ 6 ≤ (2 ^ a) ^ 6 := Nat.pow_le_pow_left a.lt_two_pow_self 6
      _ = (2 ^ 6) ^ a := by rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ ≤ p ^ a := Nat.pow_le_pow_left hlarge a

private theorem extendProduct {s t : Finset ℕ} (hst : s ⊆ t) {e : ℕ → ℕ}
    (he : ∀ p ∈ t, p ∉ s → e p = 0) (g : ℕ → ℕ → ℕ) (hg : ∀ p, g p 0 = 1) :
    (∏ p ∈ t, g p (e p)) = ∏ p ∈ s, g p (e p) :=
  (Finset.prod_subset hst (fun p hp hps => by rw [he p hp hps, hg])).symm

private theorem peakDivisors : (∏ p ∈ smallPrimes, (peak p + 1)) = 13271040 := by
  decide

private theorem peakNumber : (∏ p ∈ smallPrimes, p ^ peak p) = 780296143507862696557498656000 := by
  decide

/-- The divisor count of the product of all maximizing prime powers. -/
theorem attainingValue : σ 0 780296143507862696557498656000 = 13271040 := by
  have hprime {p : ℕ} (hp : p ∈ smallPrimes) : p.Prime := (Finset.mem_filter.mp hp).2
  rw [← peakNumber, ← peakDivisors,
    ArithmeticFunction.isMultiplicative_sigma.map_prod (fun p => p ^ peak p) smallPrimes
      (fun _ hp _ hq hne => Nat.coprime_pow_primes _ _ (hprime hp) (hprime hq) hne)]
  exact Finset.prod_congr rfl fun _ hp => ArithmeticFunction.sigma_zero_apply_prime_pow (hprime hp)

/-- The optimal bound for the sixth power of the divisor count, with denominators cleared. -/
theorem sharpBound (m : ℕ) :
    (σ 0 m) ^ 6 * 780296143507862696557498656000 ≤ 13271040 ^ 6 * m := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  let s := m.primeFactors ∪ smallPrimes
  have hs {p : ℕ} (hp : p ∈ s) : p.Prime := by
    rcases Finset.mem_union.mp hp with h | h
    · exact Nat.prime_of_mem_primeFactors h
    · exact (Finset.mem_filter.mp h).2
  have hfactor {p : ℕ} (_ : p ∈ s) (hp : p ∉ m.primeFactors) : m.factorization p = 0 :=
    Finsupp.notMem_support_iff.mp hp
  have hpeak {p : ℕ} (hp : p ∈ s) (hn : p ∉ smallPrimes) : peak p = 0 := by
    have h64 : ¬ p < 64 := fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hs hp⟩)
    simp [peak, h64]
  have em := extendProduct (e := m.factorization) (t := s) Finset.subset_union_left
    (fun _ => hfactor)
  have ep := extendProduct (e := peak) (t := s) Finset.subset_union_right (fun _ => hpeak)
  have h := Finset.prod_le_prod' (s := s)
    (fun p hp => localBound (hs hp) (m.factorization p))
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow] at h
  rw [em (fun _ a => a + 1) (fun _ => rfl), ep (· ^ ·) (fun _ => pow_zero _),
    ep (fun _ a => a + 1) (fun _ => rfl), em (· ^ ·) (fun _ => pow_zero _)] at h
  simpa only [← Nat.card_divisors hm, ← ArithmeticFunction.sigma_zero_apply,
    ← Nat.prod_primeFactors_pow_factorization hm, peakNumber, peakDivisors] using h

end OMA.Erdos647DivisorBound

theorem OMA.solution : OMA.R_Erdos647_erdos_647_R1.H1 := by
  intro m
  have hc : 13271040 ^ 6 ≤ 139 ^ 6 * 780296143507862696557498656000 := by decide
  apply le_of_mul_le_mul_right _ (by decide : 0 < (780296143507862696557498656000 : ℕ))
  exact (OMA.Erdos647DivisorBound.sharpBound m).trans
    (by simpa only [mul_right_comm] using Nat.mul_le_mul_right m hc)
