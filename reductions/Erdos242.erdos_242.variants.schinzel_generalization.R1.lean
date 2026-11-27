import FormalConjectures.ErdosProblems.«242»
import Mathlib

/-!
A three-term decomposition scales from a divisor to its multiples. Only
numerators at least four and denominators with no sufficiently large
divisor in one of the three explicit residue classes remain.
-/

open Filter

namespace OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1

def H1 : Prop :=
  ∀ a : ℕ, 4 ≤ a →
    ∀ᶠ n : ℕ in atTop,
      (∀ d : ℕ, d ∣ n → 2*a ≤ d → 0 < d%a ∧ d%a+2 < a) →
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (a/n : ℚ) = 1/x+1/y+1/z

def H2 : Prop :=
  ∀ a n : ℕ, 0 < a → 2*a ≤ n → (n%a = 0 ∨ a ≤ n%a+2) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a/n : ℚ) = 1/x+1/y+1/z

section Proof

private theorem scale_expansion {a d n : ℕ} (hn : 0 < n) (hd : d ∣ n)
    (h : ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a/d : ℚ) = 1/x+1/y+1/z) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧ (a/n : ℚ) = 1/x+1/y+1/z := by
  obtain ⟨k,hk⟩ := hd
  obtain ⟨x,y,z,hx,hxy,hyz,hEq⟩ := h
  have hk0 : 0 < k := by
    by_contra! h
    have hk' := Nat.eq_zero_of_le_zero h
    rw [hk',mul_zero] at hk
    omega
  refine ⟨x*k,y*k,z*k,(Nat.mul_pos (by omega) hk0),Nat.mul_lt_mul_of_pos_right hxy hk0,
    Nat.mul_lt_mul_of_pos_right hyz hk0,?_⟩
  have hh := congrArg (fun r : ℚ => r/(k : ℚ)) hEq
  simpa only [hk,Nat.cast_mul,div_div,add_div] using hh

theorem main : H1 → H2 → type_of% @Erdos242.erdos_242.variants.schinzel_generalization := by
  classical
  intro hHard hEasy a ha
  by_cases h4 : 4 ≤ a
  · filter_upwards [hHard a h4,eventually_ge_atTop (2*a)] with n hN hSize
    by_cases hDiv : ∃ d : ℕ, d ∣ n ∧ 2*a ≤ d ∧ (d%a = 0 ∨ a ≤ d%a+2)
    · obtain ⟨d,hd,hds,hr⟩ := hDiv
      exact scale_expansion (by omega) hd (hEasy a d ha hds hr)
    · apply hN
      intro d hd hds
      have hh : ¬ (d%a = 0 ∨ a ≤ d%a+2) := fun h => hDiv ⟨d,hd,hds,h⟩
      omega
  · filter_upwards [eventually_ge_atTop (2*a)] with n hSize
    exact hEasy a n ha hSize (by have := Nat.mod_lt n ha; omega)

theorem converse :
    (type_of% @Erdos242.erdos_242.variants.schinzel_generalization) → H1 := by
  intro h a ha
  filter_upwards [h a (by omega)] with n hn _
  exact hn

end Proof

end OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1
