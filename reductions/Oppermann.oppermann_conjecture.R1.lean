import FormalConjectures.Wikipedia.Oppermann

-- Reduction Oppermann.oppermann_conjecture.R1
-- Credit: @marcusbuffett

/-!
# Oppermann's conjecture: a kernel-checked initial range, and the open rest

* `H1`: for `2 ≤ x ≤ 1000` there is a prime strictly between `x (x - 1)` and `x ^ 2`, and one
  strictly between `x ^ 2` and `x (x + 1)`. Checked inside the Lean kernel by a verified
  trial-division search.
* `H2`: the same for every `x > 1000`. This is the open conjecture.
-/

namespace OMA.R_Oppermann_oppermann_conjecture_R1

/-- The verified range. -/
def H1 : Prop :=
  ∀ x : ℕ, 2 ≤ x → x ≤ 1000 →
    (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime) ∧
    (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime)

/-- The open part. -/
def H2 : Prop :=
  ∀ x : ℕ, 1000 < x →
    (∃ p ∈ Finset.Ioo (x * (x - 1)) (x ^ 2), p.Prime) ∧
    (∃ p ∈ Finset.Ioo (x ^ 2) (x * (x + 1)), p.Prime)

theorem main : H1 → H2 → type_of% @Oppermann.oppermann_conjecture := by
  intro h1 h2 x hx
  by_cases h : x ≤ 1000
  · exact h1 x hx h
  · exact h2 x (by omega)

end OMA.R_Oppermann_oppermann_conjecture_R1
