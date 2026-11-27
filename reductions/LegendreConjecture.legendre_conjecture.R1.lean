import FormalConjectures.Wikipedia.LegendreConjecture

-- Reduction LegendreConjecture.legendre_conjecture.R1
-- Credit: @marcusbuffett

/-!
# Legendre's conjecture: a kernel-checked initial range, and the open rest

* `H1`: for `1 ≤ n ≤ 1000` there is a prime strictly between `n ^ 2` and `(n + 1) ^ 2`. Checked
  inside the Lean kernel by a verified trial-division search.
* `H2`: the same for every `n > 1000`. This is the open conjecture.
-/

namespace OMA.R_LegendreConjecture_legendre_conjecture_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ n ≥ 1, n ≤ 1000 → ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n → ∃ p ∈ Set.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p

theorem main : H1 → H2 → type_of% @LegendreConjecture.legendre_conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1000
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_LegendreConjecture_legendre_conjecture_R1
