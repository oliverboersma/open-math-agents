import Mathlib

/-!
# Irrationality of the absolute-sine series

Source: https://mathoverflow.net/questions/510668
Question by Pierre-Aubry Simon, licensed CC BY-SA 4.0.
Lean formulation contributed by bruefire using Codex.
The source asks whether the convergent series with terms |sin n|^n / n,
for positive integers n, has an irrational sum. Angles are in radians.
The natural-number index below is shifted by one to start at n = 1.
This file states the question; it does not claim a proof of irrationality.
-/

namespace OMA.S_mo_510668

theorem main :
    Irrational (∑' j : ℕ, |Real.sin ((j + 1 : ℕ) : ℝ)| ^ (j + 1) /
      ((j + 1 : ℕ) : ℝ)) := by
  sorry

end OMA.S_mo_510668
