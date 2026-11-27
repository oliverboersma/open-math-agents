import FormalConjectures.Wikipedia.HardyLittlewood

-- Reduction HardyLittlewood.second_hardy_littlewood_conjecture.R1 of the second Hardy-Littlewood conjecture
-- Credit: @marcusbuffett

/-!
# The second Hardy-Littlewood conjecture: a short summand, and the open rest

The conjecture says `π (x + y) ≤ π x + π y` for all `x, y ≥ 2`.

* `H1`: the inequality when one of `x`, `y` is at most `26`. A window of `y` consecutive
  integers above `3` contains at most as many integers coprime to `6` as there are primes up to
  `y`, for every `y ≤ 26`.
* `H2`: the inequality when both are at least `27`. This is open, and widely expected to be
  false for very large values (it contradicts the prime tuples conjecture, Hensley and Richards).
  It is known in a much longer range than the one in `H1`.
-/

namespace OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1

/-- One of the two arguments is at most 26. -/
def H1 : Prop :=
  ∀ x y : ℕ, 2 ≤ x → 2 ≤ y → (x ≤ 26 ∨ y ≤ 26) →
    HardyLittlewood.SecondHardyLittlewoodConjectureFor x y

/-- The open part: both arguments at least 27. -/
def H2 : Prop :=
  ∀ x y : ℕ, 27 ≤ x → 27 ≤ y → HardyLittlewood.SecondHardyLittlewoodConjectureFor x y

theorem main : H1 → H2 → type_of% @HardyLittlewood.second_hardy_littlewood_conjecture := by
  intro h1 h2 x y hx hy
  by_cases h : x ≤ 26 ∨ y ≤ 26
  · exact h1 x y hx hy h
  · exact h2 x y (by omega) (by omega)

end OMA.R_HardyLittlewood_second_hardy_littlewood_conjecture_R1
