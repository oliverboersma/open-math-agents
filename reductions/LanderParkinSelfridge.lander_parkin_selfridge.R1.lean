import FormalConjectures.Wikipedia.LanderParkinAndSelfridgeConjecture

-- Reduction LanderParkinSelfridge.lander_parkin_selfridge.R1 of the Lander, Parkin and Selfridge conjecture
-- Credit: @marcusbuffett

/-!
# Lander, Parkin and Selfridge: exponents up to four, and the open rest

The conjecture says that if a sum of `n` positive `k`-th powers equals a sum of `m` positive
`k`-th powers with no common term, then `k ≤ n + m`.

* `H1`: the conjecture for `k ≤ 4`. For `k ≤ 2` there is nothing to prove; for `k = 3` one has
  to exclude `a ^ 3 = b ^ 3` with `a ≠ b`; for `k = 4` also `a ^ 4 = b ^ 4 + c ^ 4`, which is
  Fermat's theorem for exponent four (in Mathlib).
* `H2`: the conjecture for `k ≥ 5`. This is open (already `k = 5` with one term against three).
-/

namespace OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_R1

/-- Exponents up to four (Fermat for exponent four). -/
def H1 : Prop :=
  ∀ (k n m : ℕ) (x : Fin n → ℕ) (y : Fin m → ℕ), k ≤ 4 →
    0 < n → 0 < m → (∀ i, 0 < x i) → (∀ j, 0 < y j) → (∀ i j, x i ≠ y j) →
    ∑ i, x i ^ k = ∑ j, y j ^ k → k ≤ n + m

/-- The open part: exponents from five on. -/
def H2 : Prop :=
  ∀ (k n m : ℕ) (x : Fin n → ℕ) (y : Fin m → ℕ), 5 ≤ k →
    0 < n → 0 < m → (∀ i, 0 < x i) → (∀ j, 0 < y j) → (∀ i j, x i ≠ y j) →
    ∑ i, x i ^ k = ∑ j, y j ^ k → k ≤ n + m

theorem main : H1 → H2 → type_of% @LanderParkinSelfridge.lander_parkin_selfridge := by
  intro h1 h2 k n m x y hn hm hx hy hxy h
  by_cases hk : k ≤ 4
  · exact h1 k n m x y hk hn hm hx hy hxy h
  · exact h2 k n m x y (by omega) hn hm hx hy hxy h

end OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_R1
