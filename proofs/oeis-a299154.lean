import OMAStatements.S_oeis_a299154
import Mathlib

/-!
# Proof of OEIS-A299154 conjecture

Credit: @AkiRA-COM-FP
-/

open OMA.S_oeis_a299154

private theorem iterate_digits (k m : ℕ) :
    (Nat.iterate (fun j => (Nat.digits 10 j).sum) k m ≡ m [MOD 9]) ∧
      (m < k + 10 → Nat.iterate (fun j => (Nat.digits 10 j).sum) k m < 10) := by
  induction k generalizing m with
  | zero => exact ⟨Nat.ModEq.refl m, fun h => by simpa using h⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨hmod, hbound⟩ := ih ((Nat.digits 10 m).sum)
    refine ⟨hmod.trans (Nat.modEq_nine_digits_sum m).symm, fun hm => hbound ?_⟩
    by_cases h : m < 10
    · have hle := Nat.digit_sum_le 10 m
      omega
    · rw [Nat.digits_def' (by decide : 1 < 10) (by omega : 0 < m), List.sum_cons]
      have hle := Nat.digit_sum_le 10 (m / 10)
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a299154.main := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have hc : d.Coprime 9 := by
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hd₁ : 1 ≤ d := by omega
  have hd₉ : d < 9 := by omega
  refine (Nat.infinite_setOfPred_prime_and_modEq (by decide) hc).mono ?_
  intro p hp
  obtain ⟨hmod, hbound⟩ := iterate_digits p p
  have hr : digitalRoot p < 10 := hbound (by omega)
  have hres : digitalRoot p % 9 = d := by
    calc
      _ = p % 9 := hmod
      _ = d % 9 := hp.2
      _ = d := Nat.mod_eq_of_lt hd₉
  exact ⟨hp.1, by omega⟩
