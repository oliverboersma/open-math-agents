import FormalConjectures.ErdosProblems.«727»

/-!
For the two-extra-factor case, cancel the square of the smaller factorial.
Kummer's theorem then gives a carry test for only the primes dividing the
two extra factors. The logarithmic valuation bound also gives a prime-power
size restriction that can be checked before counting carries.
-/

open Finset Nat

namespace OMA.R_Erdos727_erdos_727_variants_k_2_R1

/-- Cancel the common square of the smaller factorial. -/
def H1 : Prop :=
  ∀ n : ℕ, (n + 2).factorial ^ 2 ∣ (2 * n).factorial ↔
    ((n + 1) * (n + 2)) ^ 2 ∣ (2 * n).choose n

/-- Characterize the binomial divisibility by prime-power sizes and carry counts. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    let W := (n + 1) * (n + 2)
    W ^ 2 ∣ (2 * n).choose n ↔
      ∀ p ∈ W.primeFactors,
        p ^ (2 * W.factorization p) ≤ 2 * n ∧
        2 * W.factorization p ≤
          ((Ico 1 (Nat.log p (2 * n) + 1)).filter
            (fun i ↦ p ^ i ≤ 2 * (n % p ^ i))).card

/-- The remaining infinitude question concerns only the prime factors of the two shifts. -/
def H3 : Prop :=
  {n : ℕ | 1 ≤ n ∧
    let W := (n + 1) * (n + 2)
    ∀ p ∈ W.primeFactors,
      p ^ (2 * W.factorization p) ≤ 2 * n ∧
      2 * W.factorization p ≤
        ((Ico 1 (Nat.log p (2 * n) + 1)).filter
          (fun i ↦ p ^ i ≤ 2 * (n % p ^ i))).card}.Infinite

section Proof

theorem main : H1 → H2 → H3 → type_of% @Erdos727.erdos_727.variants.k_2 := by
  intro cancel carries infinitely
  apply infinitely.mono
  intro n hn
  exact (cancel n).2 ((carries n hn.1).2 hn.2)

end Proof

end OMA.R_Erdos727_erdos_727_variants_k_2_R1
