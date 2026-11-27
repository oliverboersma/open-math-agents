import OMAReductions.R_OeisA135508_conjecture_R1

open OeisA135508

-- This proves only the elementary divisibility foundation of the reduction.
theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h4 : n = 4
    · subst n; decide
    · have hn1 : 4 ≤ n - 1 := by omega
      exact (ih (n - 1) (by omega) hn1).trans (by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
          OMA.R_OeisA135508_conjecture_R1.x_dvd_succ (n - 1) (by omega))
