import OMAStatements.S_oeis_a329227
import Mathlib

namespace A329227Proof

open PowerSeries OMA.S_oeis_a329227

lemma P_rec (n : ℕ) : P (n + 3) = P (n + 1) + P n := by
  rw [P]

lemma a_zero : a 0 = 0 := by unfold a; simp [P]
lemma a_one : a 1 = 0 := by unfold a; simp [P]
lemma a_two : a 2 = 0 := by unfold a; simp [P]
lemma a_three : a 3 = 0 := by unfold a; simp [P]
lemma a_four : a 4 = 0 := by unfold a; simp [P]
lemma a_five : a 5 = 1 := by unfold a; simp [P]

lemma rec6 (m : ℕ) :
    a (m + 6) = a (m + 5) + a (m + 4) + a (m + 3) - a (m + 2) + a (m + 1) - a m := by
  unfold a
  have p3 := P_rec m
  have p4 := P_rec (m + 1)
  have p5 := P_rec (m + 2)
  have p6 := P_rec (m + 3)
  have p7 := P_rec (m + 4)
  simp only [Nat.add_assoc, Nat.reduceAdd] at p3 p4 p5 p6 p7 ⊢
  rw [p7, p6, p5, p4, p3]
  ring

end A329227Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a329227.main := by
  have hD : ((1 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - PowerSeries.X ^ 3)
      * (1 + PowerSeries.X - PowerSeries.X ^ 3) : PowerSeries ℤ)
      = 1 - PowerSeries.X ^ 1 - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4
        - PowerSeries.X ^ 5 + PowerSeries.X ^ 6 := by
    ring
  rw [hD]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n)
    with rfl | rfl | rfl | rfl | rfl | rfl | h
  · simp [A329227Proof.a_zero]
  · simp [A329227Proof.a_zero, A329227Proof.a_one]
  · simp [A329227Proof.a_zero, A329227Proof.a_one, A329227Proof.a_two]
  · simp [A329227Proof.a_zero, A329227Proof.a_one, A329227Proof.a_two, A329227Proof.a_three]
  · simp [A329227Proof.a_zero, A329227Proof.a_one, A329227Proof.a_two, A329227Proof.a_three,
      A329227Proof.a_four]
  · simp [A329227Proof.a_zero, A329227Proof.a_one, A329227Proof.a_two, A329227Proof.a_three,
      A329227Proof.a_four, A329227Proof.a_five]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    have hr := A329227Proof.rec6 m
    have e1 : m + 6 - 1 = m + 5 := by omega
    have e2 : m + 6 - 2 = m + 4 := by omega
    have e3 : m + 6 - 3 = m + 3 := by omega
    have e4 : m + 6 - 4 = m + 2 := by omega
    have e5 : m + 6 - 5 = m + 1 := by omega
    have e6 : m + 6 - 6 = m := by omega
    have c1 : 1 ≤ m + 6 := by omega
    have c2 : 2 ≤ m + 6 := by omega
    have c3 : 3 ≤ m + 6 := by omega
    have c4 : 4 ≤ m + 6 := by omega
    have c5 : 5 ≤ m + 6 := by omega
    have c6 : 6 ≤ m + 6 := by omega
    have z5 : ¬ m + 6 = 5 := by omega
    simp only [if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_pos c6,
      if_neg z5, e1, e2, e3, e4, e5, e6]
    rw [hr]
    ring
