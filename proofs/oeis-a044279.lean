import OMAStatements.S_oeis_a044279
import Mathlib

namespace NineCarry

theorem main : ∀ k : ℕ, 0 < k →
    ([1, 3] : List ℕ).IsInfix (Nat.digits 9 k) →
    ¬ ([1, 3] : List ℕ).IsInfix (Nat.digits 9 (k - 1)) →
    (Nat.digits 10 k).sum % 9 = 0 ∨ (Nat.digits 10 k).sum % 9 = 1 := by
  intro k hk hi hprev
  have hsum : (Nat.digits 10 k).sum % 9 = k % 9 := (Nat.modEq_nine_digits_sum k).symm
  rw [hsum]
  by_contra! h
  have hrem : 2 ≤ k % 9 := by omega
  have hpos : 0 < k-1 := by omega
  have hd : (k-1)/9 = k/9 := by omega
  rw [Nat.digits_def' (by decide : 1 < 9) hk] at hi
  rcases List.infix_cons_iff.mp hi with hp | ht
  · have he := (List.cons_prefix_cons.mp hp).1
    omega
  · apply hprev
    rw [Nat.digits_def' (by decide : 1 < 9) hpos, hd]
    exact List.infix_cons_iff.mpr (Or.inr ht)

end NineCarry

theorem OMA.solution : type_of% @OMA.S_oeis_a044279.main := NineCarry.main