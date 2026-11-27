import OMAStatements.S_oeis_a091540
import Mathlib

namespace A091540
open OMA.S_oeis_a091540

lemma q_succ (n : ℕ) : q (n + 1) = q n * (3 * (n : ℤ) + 1) := by
  unfold q
  rw [Finset.prod_range_succ]

lemma two_dvd_q (m : ℕ) : (2 : ℤ) ∣ q (m + 2) := by
  have h : (3 * ((1 : ℕ) : ℤ) + 1) ∣ q (m + 2) := by
    unfold q
    exact Finset.dvd_prod_of_mem (fun j : ℕ => (3 * (j : ℤ) + 1))
      (Finset.mem_range.mpr (by omega))
  exact Dvd.dvd.trans ⟨2, by norm_num⟩ h

lemma two_dvd_fact (m : ℕ) : (2 : ℤ) ∣ ((m + 2).factorial : ℤ) := by
  have h : (2 : ℕ) ∣ (m + 2).factorial := Nat.dvd_factorial (by norm_num) (by omega)
  exact_mod_cast h

lemma six_dvd (m : ℕ) : (6 : ℤ) ∣ numerator (m + 2) := by
  obtain ⟨u, hu⟩ := two_dvd_q m
  obtain ⟨v, hv⟩ := two_dvd_fact m
  unfold numerator
  rw [hu, hv]
  exact ⟨3 ^ (m + 1) * v - u, by ring⟩

lemma a_eq (m : ℕ) : 6 * a (m + 2) = numerator (m + 2) := by
  unfold a
  exact Int.mul_ediv_cancel' (six_dvd m)

lemma num_rec (m : ℕ) :
    numerator (m + 2) + (-6 * ((m : ℤ) + 2) + 5) * numerator (m + 1) +
      3 * ((m : ℤ) + 1) * (3 * (m : ℤ) + 1) * numerator m = 0 := by
  unfold numerator
  rw [q_succ (m + 1), q_succ m, Nat.factorial_succ (m + 1), Nat.factorial_succ m]
  push_cast
  ring

end A091540

theorem OMA.solution : type_of% @OMA.S_oeis_a091540.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := by omega
  have e2 : m + 4 - 2 = m + 2 := by omega
  rw [e1, e2]
  have h0 : 6 * OMA.S_oeis_a091540.a (m + 2) = OMA.S_oeis_a091540.numerator (m + 2) :=
    A091540.a_eq m
  have h1 : 6 * OMA.S_oeis_a091540.a (m + 3) = OMA.S_oeis_a091540.numerator (m + 3) :=
    A091540.a_eq (m + 1)
  have h2 : 6 * OMA.S_oeis_a091540.a (m + 4) = OMA.S_oeis_a091540.numerator (m + 4) :=
    A091540.a_eq (m + 2)
  have hr : OMA.S_oeis_a091540.numerator (m + 4) +
      (-6 * (((m + 2 : ℕ) : ℤ) + 2) + 5) * OMA.S_oeis_a091540.numerator (m + 3) +
      3 * (((m + 2 : ℕ) : ℤ) + 1) * (3 * ((m + 2 : ℕ) : ℤ) + 1) *
        OMA.S_oeis_a091540.numerator (m + 2) = 0 := A091540.num_rec (m + 2)
  push_cast at hr ⊢
  have h6 : (6 : ℤ) * (OMA.S_oeis_a091540.a (m + 4) +
      (-6 * ((m : ℤ) + 4) + 5) * OMA.S_oeis_a091540.a (m + 3) +
      3 * ((m : ℤ) + 4 - 1) * (3 * ((m : ℤ) + 4) - 5) * OMA.S_oeis_a091540.a (m + 2)) = 0 := by
    linear_combination h2 + (-6 * ((m : ℤ) + 4) + 5) * h1 +
      3 * ((m : ℤ) + 4 - 1) * (3 * ((m : ℤ) + 4) - 5) * h0 + hr
  rcases mul_eq_zero.mp h6 with h | h
  · norm_num at h
  · exact h
