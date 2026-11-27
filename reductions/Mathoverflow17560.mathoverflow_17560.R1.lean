import FormalConjectures.Mathoverflow.«17560»

-- Reduction Mathoverflow17560.mathoverflow_17560.R1 of the question whether 2^x and 3^x natural force x natural
-- Credit: @marcusbuffett

/-!
# If `2^x` and `3^x` are natural numbers, is `x` a natural number? The rational case

The question follows from the four exponentials conjecture and is open; the six exponentials
theorem only gives it with a third base. The rational case is elementary and needs only `2^x`.

* `H1` (elementary): if `x` is rational and `2^x` is a natural number then `x` is a natural
  number. (For `x < 0` the value lies strictly between `0` and `1`. For `x = a / b ≥ 0` and
  `2^x = m`, `m^b = 2^a`, so `m = 2^j` and `j * b = a`.)
* `H2`: no irrational `x` has both `2^x` and `3^x` natural. This is the open part.
-/

namespace OMA.R_Mathoverflow17560_mathoverflow_17560_R1

/-- The rational case, from `2^x` alone. -/
def H1 : Prop :=
  ∀ x : ℝ, (∃ q : ℚ, x = q) → (∃ m : ℕ, (2 : ℝ) ^ x = m) → ∃ m : ℕ, x = m

/-- The open part: an irrational exponent. -/
def H2 : Prop :=
  ∀ x : ℝ, Irrational x → (∃ m : ℕ, (2 : ℝ) ^ x = m) → (∃ m : ℕ, (3 : ℝ) ^ x = m) → False

theorem main : H1 → H2 → type_of% @Mathoverflow17560.mathoverflow_17560 := by
  intro h1 h2 x hx hx'
  by_cases hi : Irrational x
  · exact (h2 x hi hx hx').elim
  · have hmem : x ∈ Set.range ((↑) : ℚ → ℝ) := by
      by_contra h
      exact hi h
    obtain ⟨q, hq⟩ := hmem
    exact h1 x ⟨q, hq.symm⟩ hx

end OMA.R_Mathoverflow17560_mathoverflow_17560_R1
