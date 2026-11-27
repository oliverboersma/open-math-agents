import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1

-- Reduction Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite.R1.H2.R1
-- of step Erdos313.erdos_313.variants.primary_pseudoperfect_are_infinite.R1.H2
-- Credit: @marcusbuffett

/-!
# Prime sets for primary pseudoperfect numbers: what is known, and what is open

The parent step asks, for every `k`, for a set of at least `k` primes in which each prime divides
the product of the others plus one and whose reciprocals sum to less than one. Such a set is
exactly the set of prime factors of a primary pseudoperfect number.

* `H1` (known): a set of eight primes exists. Eight primary pseudoperfect numbers are known
  (OEIS A054377); the largest, `8490421583559688410706771261086`, has the eight prime factors
  `2, 3, 11, 23, 31, 47059, 2217342227, 1729101023519` (Butske, Jaje and Mayernik, Math. Comp.
  69 (2000)). Proving `H1` means checking this set, including the primality of the two large
  factors.
* `H2` (open): sets of nine or more primes, for every size. No primary pseudoperfect number with
  nine prime factors is known.
-/

open Finset

namespace OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1

/-- A set of at least eight primes with the cofactor congruences and reciprocal sum below one. -/
def H1 : Prop :=
  ∃ P : Finset ℕ, 8 ≤ P.card ∧ P.Nonempty ∧
    (∀ p ∈ P, p.Prime) ∧
    (∀ p ∈ P, p ∣ (∏ q ∈ P.erase p, q) + 1) ∧
    (∑ p ∈ P, (1 : ℚ) / p) < 1

/-- The open part: such sets of every size from nine on. -/
def H2 : Prop :=
  ∀ k : ℕ, 9 ≤ k → ∃ P : Finset ℕ, k ≤ P.card ∧ P.Nonempty ∧
    (∀ p ∈ P, p.Prime) ∧
    (∀ p ∈ P, p ∣ (∏ q ∈ P.erase p, q) + 1) ∧
    (∑ p ∈ P, (1 : ℚ) / p) < 1

theorem main : H1 → H2 →
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1.H2 := by
  intro h1 h2 k
  by_cases hk : k ≤ 8
  · obtain ⟨P, hcard, hrest⟩ := h1
    exact ⟨P, le_trans hk hcard, hrest⟩
  · exact h2 k (by omega)

end OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1
