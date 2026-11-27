import OMAStatements.S_oeis_a110199
import Mathlib.Tactic.LinearCombination

/-!
Mathar's recurrence compares two consecutive differences two positions
apart. Both differences vanish at odd indices. At even indices they give
two consecutive Catalan numbers. Proof by @anmolspace.
-/

private theorem catalan_ratio (k : ℕ) :
    ((k : ℤ) + 2) * (catalan (k + 1) : ℤ) = 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [← succ_mul_catalan_eq_centralBinom (k + 1), ← succ_mul_catalan_eq_centralBinom k] at h
  have z : ((k : ℤ) + 1) * (((k : ℤ) + 2) * (catalan (k + 1) : ℤ)) =
      2 * (2 * (k : ℤ) + 1) * (((k : ℤ) + 1) * (catalan k : ℤ)) := by
    exact_mod_cast h
  have product : ((k : ℤ) + 1) *
      (((k : ℤ) + 2) * (catalan (k + 1) : ℤ) - 2 * (2 * (k : ℤ) + 1) * (catalan k : ℤ)) = 0 := by
    linear_combination z
  exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left (by omega))

open OMA.S_oeis_a110199 in
theorem OMA.solution : type_of% @OMA.S_oeis_a110199.main := by
  let S (j : ℕ) : ℤ := ((∑ x ∈ Finset.range (j+1), catalan x : ℕ) : ℤ)
  have term (n : ℕ) : (a n : ℤ) = S (n/2) := rfl
  have step (j : ℕ) : S (j+1) = S j + (catalan (j+1) : ℤ) := by
    simp [S, Finset.sum_range_succ]
  intro n hn
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ k by omega)
    simp only [term, show 2*(j+2)/2 = j+2 by omega,
      show (2*(j+2)-1)/2 = j+1 by omega, show (2*(j+2)-2)/2 = j+1 by omega,
      show (2*(j+2)-3)/2 = j by omega]
    rw [step (j+1), step j]
    have h := catalan_ratio (j+1)
    push_cast at h ⊢
    linear_combination -2*h
  · simp only [term, show (2*k+1)/2 = (2*k+1-1)/2 by omega,
      show (2*k+1-2)/2 = (2*k+1-3)/2 by omega]
    ring
