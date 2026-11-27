import OMAStatements.S_oeis_a266225
import Mathlib

namespace A266225

lemma exists_x (p : ℕ) : ∃ x : ℕ, 1 < x ∧ (p * x + x - 1).Prime := by
  have hcop : Nat.Coprime p (p + 1) := by simp
  obtain ⟨q, hq1, hq2, hq3⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (2 * (p + 1)) (q := p + 1) (a := p) (by omega) hcop
  have hmod : q % (p + 1) = p := by
    have h := hq3
    unfold Nat.ModEq at h
    rw [h]
    exact Nat.mod_eq_of_lt (by omega)
  have hd2 : 2 ≤ q / (p + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    omega
  refine ⟨q / (p + 1) + 1, by omega, ?_⟩
  have hdiv := Nat.div_add_mod q (p + 1)
  rw [hmod] at hdiv
  have e : p * (q / (p + 1) + 1) + (q / (p + 1) + 1) - 1 = q := by
    generalize q / (p + 1) = d at hdiv ⊢
    have e' : p * (d + 1) + (d + 1) = (p + 1) * d + p + 1 := by ring
    omega
  rw [e]
  exact hq2

end A266225

open scoped Classical in
theorem OMA.solution : type_of% @OMA.S_oeis_a266225.main := by
  intro n hn
  have hex : ∃ x : ℕ, OMA.S_oeis_a266225.qualifies n x :=
    A266225.exists_x (OMA.S_oeis_a266225.primeAt n)
  unfold OMA.S_oeis_a266225.a
  rw [dif_pos hex]
  have h : 1 < Nat.find hex := (Nat.find_spec hex).1
  exact_mod_cast h
