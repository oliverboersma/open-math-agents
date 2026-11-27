import FormalConjectures.OEIS.«228425»

-- Reduction OeisA228425.conjecture_2.R1 of Number of ways to write n = x + y with p_k(x) + p_{k+1}(y) prime — conjecture2
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target characterises the shifts `k` for which every `n > 1` splits as `x + y` with
-- `p_k(x) + p_{k+1}(y)` prime: exactly `k` in `{3, 39, 99}`. The two directions of the iff are
-- independent — the forward one is the exclusion of all other `k`, the backward one is a
-- Goldbach-type statement for the three exceptional shifts.

namespace OMA.R_OeisA228425_conjecture_2_R1

/-- Forward direction: if every `n > 1` splits with `p_k(x) + p_{k+1}(y)` prime, then `k` is one
of `3`, `39`, `99`. -/
def H1 : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    (∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      Nat.Prime (Nat.polygonalNumber k x + Nat.polygonalNumber (k + 1) y)) →
    k = 3 ∨ k = 39 ∨ k = 99

/-- Backward direction: for `k` in `{3, 39, 99}` every `n > 1` splits with
`p_k(x) + p_{k+1}(y)` prime. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → (k = 3 ∨ k = 39 ∨ k = 99) →
    ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      Nat.Prime (Nat.polygonalNumber k x + Nat.polygonalNumber (k + 1) y)

theorem main : H1 → H2 → type_of% @OeisA228425.conjecture_2 := by
  intro h1 h2 k hk
  exact ⟨fun h => h1 k hk h, fun h => h2 k hk h⟩

end OMA.R_OeisA228425_conjecture_2_R1
