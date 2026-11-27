import OMAStatements.S_oeis_a052183
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a052183.main := by
  intro t
  simp only [OMA.S_oeis_a052183.a]
  rw [show 3 * (t + 2) = 3 * t + 5 + 1 by ring, show 3 * (t + 1) = 3 * t + 2 + 1 by ring,
    show 2 * (t + 2) + 1 = 2 * t + 4 + 1 by ring, show 2 * (t + 1) + 1 = 2 * t + 2 + 1 by ring]
  simp only [Nat.factorial_succ, show 3 * t + 5 = 3 * t + 4 + 1 by ring,
    show 3 * t + 4 = 3 * t + 3 + 1 by ring, show 3 * t + 3 = 3 * t + 2 + 1 by ring,
    show 3 * t + 2 = 3 * t + 1 + 1 by ring, show 2 * t + 4 = 2 * t + 3 + 1 by ring,
    show 2 * t + 3 = 2 * t + 2 + 1 by ring, show 2 * t + 2 = 2 * t + 1 + 1 by ring,
    Nat.factorial_succ]
  have : ((3 * t).factorial : ℚ) ≠ 0 := by positivity
  have : ((2 * t + 1).factorial : ℚ) ≠ 0 := by positivity
  have : (t.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
