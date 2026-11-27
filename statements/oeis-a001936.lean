import Mathlib

/-!
# A001936: Expansion of q^(-1/4) * (eta(q^4) / eta(q))^2 in powers of q.

Source: https://oeis.org/A001936
Credit: @rot13maxi

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a001936

/-- Number of partitions of `n` with no part divisible by `4`. -/
def restrictedCount (n : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun i => ¬ 4 ∣ i)).card

/-- A001936: number of 4-regular bipartitions of `n`, i.e. pairs of partitions
of total size `n` with no part divisible by `4`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), restrictedCount k * restrictedCount (n - k)

/-- MathOverflow conjecture recorded on OEIS A001936:
`a(n) ≡ a(9*n + 2) (mod 4)` for every `n`. -/
theorem main : ∀ n : ℕ, Nat.ModEq 4 (a n) (a (9 * n + 2)) := by
  sorry

end OMA.S_oeis_a001936
