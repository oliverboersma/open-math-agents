import FormalConjectures.Wikipedia.Lemoine

-- Reduction Lemoine.lemoine_conjecture.R1
-- Credit: @marcusbuffett

/-!
# Lemoine's conjecture: a kernel-checked initial range, and the open rest

* `H1`: every odd `n` with `6 < n ≤ 10001` is `p + 2 q` with `p`, `q` prime. Checked inside the
  Lean kernel by a verified trial-division search.
* `H2`: the same for every odd `n > 10001`. This is the open conjecture (verified numerically
  up to `10 ^ 13` by Corbitt; the range here is only what is cheap to check in the kernel).
-/

namespace OMA.R_Lemoine_lemoine_conjecture_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ n : ℕ, 6 < n → Odd n → n ≤ 10001 → ∃ (p q : ℕ), p.Prime ∧ q.Prime ∧ p + 2 * q = n

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 10001 < n → Odd n → ∃ (p q : ℕ), p.Prime ∧ q.Prime ∧ p + 2 * q = n

theorem main : H1 → H2 → type_of% @Lemoine.lemoine_conjecture := by
  intro h1 h2 n hn ho
  by_cases h : n ≤ 10001
  · exact h1 n hn ho h
  · exact h2 n (by omega) ho

end OMA.R_Lemoine_lemoine_conjecture_R1
