import Mathlib

/-!
# Is ζ(5) irrational?

Source: https://en.wikipedia.org/wiki/Ap%C3%A9ry%27s_theorem
Credit: @OrangeHeadz

The source asks whether ζ(5) = Σ_{n ≥ 1} 1 / n ^ 5 is irrational, and records that this is not
known: Apéry proved ζ(3) irrational, Ball and Rivoal that infinitely many ζ(2n+1) are irrational,
and Zudilin that at least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational.

The question is stated as the affirmative assertion (the expected answer); it is open.

Conventions:
* ζ(5) is the real series over the positive integers, written with the index shifted by one:
  `∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5`, so the term for `n` is `1 / (n + 1) ^ 5` and no term divides
  by zero.
-/

namespace OMA.S_wpc_zeta_5_irrational

/-- `ζ(5) = Σ_{n ≥ 1} 1 / n ^ 5` is irrational. -/
theorem main : Irrational (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5) := by
  sorry

end OMA.S_wpc_zeta_5_irrational
