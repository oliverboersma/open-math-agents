import FormalConjectures.Wikipedia.Grimm

-- Reduction Grimm.grimm_conjecture.R1 of Grimm's conjecture
-- Credit: @marcusbuffett

/-!
# Grimm's conjecture: runs of at most three composites, and the open rest

Grimm's conjecture says that to consecutive composite numbers `n, ..., n + k - 1` one can assign
distinct primes `p_i` with `p_i` dividing `n + i`.

* `H1`: the conjecture for `k ≤ 3`. Neighbours are coprime, and of two even numbers `n`, `n + 2`
  one is twice an odd number greater than one, which supplies an odd prime.
* `H2`: the conjecture for runs of length `k ≥ 4`. This is open (it is known for `k` small
  compared with `n`, by Ramachandra, Shorey and Tijdeman, and numerically far out).
-/

namespace OMA.R_Grimm_grimm_conjecture_R1

/-- Runs of at most three composites. -/
def H1 : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k ≤ 3 → (∀ i : Fin k, (n + i).Composite) →
    ∃ ps : Fin k ↪ ℕ, ∀ i : Fin k, (ps i).Prime ∧ ps i ∣ (n + i)

/-- The open part: runs of four or more. -/
def H2 : Prop :=
  ∀ n k : ℕ, 1 ≤ n → 4 ≤ k → (∀ i : Fin k, (n + i).Composite) →
    ∃ ps : Fin k ↪ ℕ, ∀ i : Fin k, (ps i).Prime ∧ ps i ∣ (n + i)

theorem main : H1 → H2 → type_of% @Grimm.grimm_conjecture := by
  intro h1 h2 n k hn hk h
  by_cases hk3 : k ≤ 3
  · exact h1 n k hn hk hk3 h
  · exact h2 n k hn (by omega) h

end OMA.R_Grimm_grimm_conjecture_R1
