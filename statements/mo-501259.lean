import Mathlib

/-!
# Sums of distinct powers of 3, 4 and 7

Source: https://mathoverflow.net/questions/501259
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

In the notation of Burr, Erdős, Graham and Li (Complete sequences of sets of integer powers,
Acta Arith. 1996), `Σ(Pow({3, 4, 7}; 1))` is the set of positive integers that are sums of
distinct powers of `3`, `4` and `7`. The paper states, using Diophantine approximation, that the
largest integer not in `Σ(Pow({3, 4, 7}; 1))` is `581`; the question asks how this is proved.
The statement below is that claim.

Conventions:
* `Pow({3, 4, 7}; 1)` is the set `{a ^ i | a ∈ {3, 4, 7}, i ≥ 1}`: the `1` is the least exponent,
  so `1 = a ^ 0` is not a power here. This matches the heuristic quoted in the question,
  `1/(3-1) + 1/(4-1) + 1/(7-1) = 1`, which is `∑_a ∑_{i ≥ 1} a^(-i)`. These powers are pairwise
  different numbers, so a sum of distinct powers is the sum of a finite set of them;
* `Σ(…)` consists of the sums of nonempty finite subsets of `Pow({3, 4, 7}; 1)`;
* largest integer not in `Σ` equal to `581` means: `581 ∉ Σ` and every `n > 581` is in `Σ`.
-/

namespace OMA.S_mo_501259

/-- `Pow({3, 4, 7}; 1)`: the powers `a ^ i` with `a ∈ {3, 4, 7}` and `i ≥ 1`. -/
def Pow347 : Set ℕ :=
  {m : ℕ | ∃ a ∈ ({3, 4, 7} : Finset ℕ), ∃ i : ℕ, 1 ≤ i ∧ m = a ^ i}

/-- `Σ(Pow({3, 4, 7}; 1))`: sums of distinct elements of `Pow347` (nonempty finite subsets). -/
def SigmaPow347 : Set ℕ :=
  {n : ℕ | ∃ s : Finset ℕ, (s : Set ℕ) ⊆ Pow347 ∧ s.Nonempty ∧ s.sum id = n}

/-- The largest integer that is not a sum of distinct powers of `3`, `4`, `7` is `581`. -/
theorem main : 581 ∉ SigmaPow347 ∧ ∀ n : ℕ, 581 < n → n ∈ SigmaPow347 := by
  sorry

end OMA.S_mo_501259
