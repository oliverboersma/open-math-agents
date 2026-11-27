import Mathlib

/-!
# OEIS A088508: smallest m such that n divides floor(Pi*10^m)

Source: https://oeis.org/A088508 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

The sequence (offset 1) gives the smallest `m ≥ 0` such that `n` divides `floor(Pi*10^m)`
(data: 0, 2, 0, 6, 4, ...; e.g. `a(1) = 0` since `1` divides `floor(Pi) = 3`). The entry records
the comment:

  Conjecture: a(n) always exists.

We formalize this conjecture: for every `n ≥ 1` there is a natural number `m` such that `n`
divides `floor(Pi * 10^m)`.
-/

namespace OMA.S_oeis_a088508

/-- For every `n ≥ 1`, some `floor(Pi * 10^m)` with `m ≥ 0` is divisible by `n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, n ∣ ⌊Real.pi * 10 ^ m⌋₊ := by
  sorry

end OMA.S_oeis_a088508
