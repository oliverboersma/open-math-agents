import OMAStatements.S_mo_47888
import Mathlib

/-!
Disproof of MathOverflow 47888 (multinomial expectation does not preserve monotone vector fields).

Counterexample with `n = 1` draw and `k = 3` categories. Let `u = (0, 1, -1)` and
`f x = h (x 1 - x 2) • u` with `h d = -1` for `d < 0` and `h d = 1` otherwise. Since `h` is
nondecreasing, `∑ⱼ (xⱼ - yⱼ) (f x j - f y j) = (dₓ - d_y) (h dₓ - h d_y) ≥ 0`, so `f` is monotone.
With one draw, `g(p) = ∑ᵢ pᵢ f(eᵢ) = (p₀ + p₁ - p₂) u`. For `p = (1, 0, 0)` and `q = (0, 3/4, 1/4)`
we get `g(p) - g(q) = (0, 1/2, -1/2)` and `(p - q) · (g(p) - g(q)) = -3/8 + 1/8 = -1/4 < 0`.
-/

namespace OMA.D_mo_47888

/-- Nondecreasing step function. -/
def stepH (d : ℤ) : ℝ := if d < 0 then -1 else 1

/-- The monotone field `f x = stepH (x 1 - x 2) • (0, 1, -1)`. -/
noncomputable def field3 (x : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun j => stepH (x 1 - x 2) * (![0, 1, -1] : Fin 3 → ℝ) j

lemma stepH_mono (a b : ℤ) : 0 ≤ ((a : ℝ) - (b : ℝ)) * (stepH a - stepH b) := by
  unfold stepH
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp only [ha, hb, if_true, if_false]
  · simp
  · have : (a : ℝ) < 0 := by exact_mod_cast ha
    have : (0 : ℝ) ≤ b := by exact_mod_cast (not_lt.mp hb)
    nlinarith
  · have : (b : ℝ) < 0 := by exact_mod_cast hb
    have : (0 : ℝ) ≤ a := by exact_mod_cast (not_lt.mp ha)
    nlinarith
  · simp

lemma field3_monotone : OMA.S_mo_47888.fieldMonotone field3 := by
  intro x y
  have key := stepH_mono (x 1 - x 2) (y 1 - y 2)
  simp only [Fin.sum_univ_three, field3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  push_cast at key
  nlinarith [key]

end OMA.D_mo_47888

open OMA.D_mo_47888 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_47888.main) := by
  intro h
  have hp : OMA.S_mo_47888.onSimplex (![1, 0, 0] : Fin 3 → ℝ) := by
    refine ⟨fun j => ?_, ?_⟩
    · fin_cases j <;> norm_num
    · simp [Fin.sum_univ_three]
  have hq : OMA.S_mo_47888.onSimplex (![0, 3/4, 1/4] : Fin 3 → ℝ) := by
    refine ⟨fun j => ?_, ?_⟩
    · fin_cases j <;> norm_num
    · simp [Fin.sum_univ_three]; norm_num
  have := h 1 3 one_pos (by norm_num) field3 field3_monotone _ _ hp hq
  simp [OMA.S_mo_47888.smooth, OMA.S_mo_47888.average, OMA.S_mo_47888.bump, Fin.sum_univ_three,
    field3, stepH] at this
  norm_num at this
