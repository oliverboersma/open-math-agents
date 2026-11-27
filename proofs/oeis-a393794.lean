import OMAStatements.S_oeis_a393794

open OMA.S_oeis_a393794

-- Repeating the digit block 1089 twice gives 10891089, whose reversal is
-- nine times as large. Appending a zero therefore gives a second fixed point.
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a393794.main) := by
  intro h
  have fixed : 10 ^ (5 + 3) ≤ (108910890 : ℕ) ∧ 108910890 < 10 ^ (5 + 4) ∧
      step 108910890 = 108910890 := by decide
  have distinct : (108910890 : ℕ) ≠ term 5 := by decide
  exact distinct ((h 5 (by decide) 108910890).mp fixed)
