import OMAReductions.R_Erdos389_erdos_389_R1

namespace OMA.R_Erdos389_erdos_389_R1_H2_R1

/-- Legendre's calculation for primes above the smoothness bound: failure of the valuation
inequality would put such a prime in one of the excluded blocks `k + s`. -/
def H1 : Prop := ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    (∀ s : ℕ, n - 1 < 2 * s → s ≤ n - 1 → ∀ p : ℕ, p.Prime → p ∣ k + s →
      p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))) →
    ∀ p : ℕ, p.Prime → max (n - 1) (Nat.sqrt (n + 2 * k - 1)) < p →
      padicValNat p (∏ i ∈ Finset.range k, (n + i)) ≤
        padicValNat p (∏ i ∈ Finset.range k, (n + k + i))

/-- Factorization bookkeeping: if every prime occurs at least as often in the second consecutive
product as in the first, the first product divides the second. -/
def H2 : Prop := ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    (∀ p : ℕ, p.Prime →
      padicValNat p (∏ i ∈ Finset.range k, (n + i)) ≤
        padicValNat p (∏ i ∈ Finset.range k, (n + k + i))) →
    ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i)

theorem main : H1 → H2 → OMA.R_Erdos389_erdos_389_R1.H2 := by
  intro hlarge hdiv n k hn hk hsmooth hsmall
  refine hdiv n k hn hk fun p hp => ?_
  by_cases hpB : p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))
  · exact hsmall p hp hpB
  · exact hlarge n k hn hk hsmooth p hp (Nat.lt_of_not_ge hpB)

end OMA.R_Erdos389_erdos_389_R1_H2_R1
