import OMAStatements.S_oeis_a224669
import Mathlib

open PowerSeries

namespace IdempotentRows

open OMA.S_oeis_a224669

private theorem completion_rec (k : ℕ) (r : Row) :
    completions (k+4) r + completions (k+1) r = 2 * completions (k+3) r := by
  induction k generalizing r with
  | zero =>
    have h : ∀ r : Row, completions 4 r + completions 1 r = 2 * completions 3 r := by decide
    exact h r
  | succ k ih =>
    have advance (n : ℕ) : completions (n+1) r =
        ∑ s : Row, if compatible r s then completions n s else 0 := rfl
    rw [show k+1+4=k+4+1 by omega, 
      show k+1+3=k+3+1 by omega, advance (k+4), advance (k+1), advance (k+3)]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp [ih]

private theorem term_rec (k : ℕ) : term (k+4)+term (k+1) = 2*term (k+3) := by
  unfold term
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => completion_rec k r

private theorem term₁ : term 1 = 12 := by decide
private theorem term₂ : term 2 = 25 := by decide
private theorem term₃ : term 3 = 41 := by decide

private noncomputable def closed (n : ℕ) : ℝ :=
  -4 + (((1-Real.sqrt 5)/2)^n*(-19+13*Real.sqrt 5) +
        ((1+Real.sqrt 5)/2)^n*(19+13*Real.sqrt 5))/(2*Real.sqrt 5)

private theorem closed_rec (n : ℕ) : closed (n+3) + closed n = 2*closed (n+2) := by
  let s := Real.sqrt 5
  have hs : s^2 = 5 := Real.sq_sqrt (by norm_num)
  have root (x : ℝ) (h : x^2 - x - 1 = 0) : x^(n+3) + x^n = 2*x^(n+2) := by
    rw [pow_add x n 3, pow_add x n 2]
    linear_combination x^n*(x-1)*h
  have hm : ((1-s)/2)^2 - (1-s)/2 - 1 = 0 := by linear_combination (1/4:ℝ)*hs
  have hp : ((1+s)/2)^2 - (1+s)/2 - 1 = 0 := by linear_combination (1/4:ℝ)*hs
  change -4+( ((1-s)/2)^(n+3)*(-19+13*s) + ((1+s)/2)^(n+3)*(19+13*s))/(2*s)
       + (-4+( ((1-s)/2)^n*(-19+13*s) + ((1+s)/2)^n*(19+13*s))/(2*s)) =
       2*(-4+( ((1-s)/2)^(n+2)*(-19+13*s) + ((1+s)/2)^(n+2)*(19+13*s))/(2*s))
  linear_combination ((-19+13*s)/(2*s))*root _ hm + ((19+13*s)/(2*s))*root _ hp

private theorem term_closed (n : ℕ) (hn : 1 ≤ n) : (term n : ℝ) = closed n := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h₃ : Real.sqrt 5 ^ 3 = 5 * Real.sqrt 5 := by linear_combination Real.sqrt 5 * hs
  have h₄ : Real.sqrt 5 ^ 4 = 25 := by
    calc
      Real.sqrt 5 ^ 4 = (Real.sqrt 5 ^ 2)^2 := by ring
      _ = 25 := by rw [hs]; norm_num
  have hs0 : Real.sqrt 5 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn3 : n ≤ 3
    · interval_cases n <;> norm_num [closed,term₁,term₂,term₃] <;>
        field_simp [hs0] <;> nlinarith only [hs,h₃,h₄]
    have h₁ := ih (n-3) (by omega) (by omega)
    have h₂ := ih (n-1) (by omega) (by omega)
    have r := term_rec (n-4)
    rw [show n-4+4=n by omega, show n-4+1=n-3 by omega, show n-4+3=n-1 by omega] at r
    have r' : (term n:ℝ)+(term (n-3):ℝ) = 2*(term (n-1):ℝ) := by exact_mod_cast r
    have q := closed_rec (n-3)
    rw [show n-3+3=n by omega, show n-3+2=n-1 by omega] at q
    linarith only [h₁,h₂,r',q]

private theorem generating : ((1-X)*(1-X-X^2))*series = X*(12+X-9*X^2) := by
  have L : ((1-X)*(1-X-X^2))*series =
      series - (X^1*series+X^1*series) + X^3*series := by ring
  have R : X*(12+X-9*X^2) = C (12:ℚ)*X^1 + C (1:ℚ)*X^2 - C (9:ℚ)*X^3 := by
    rw [show C (12:ℚ) = 12 by exact map_natCast _ 12,
      show C (9:ℚ) = 9 by exact map_natCast _ 9, map_one]
    ring
  rw [L,R]
  ext n
  simp only [map_add,map_sub,coeff_X_pow_mul',coeff_C_mul_X_pow,series,coeff_mk]
  by_cases h : n ≤ 3
  · interval_cases n <;> norm_num [term₁,term₂,term₃]
  have hn : 4 ≤ n := by omega
  rw [if_neg (by omega : n ≠ 0), if_pos (by omega : 1 ≤ n), if_pos (by omega : 3 ≤ n),
    if_neg (by omega : n-1 ≠ 0), if_neg (by omega : n-3 ≠ 0),
    if_neg (by omega : n ≠ 1), if_neg (by omega : n ≠ 2), if_neg (by omega : n ≠ 3)]
  have r := term_rec (n-4)
  rw [show n-4+4=n by omega, show n-4+1=n-3 by omega, show n-4+3=n-1 by omega] at r
  have r' : (term n:ℚ)+(term (n-3):ℚ) = 2*(term (n-1):ℚ) := by exact_mod_cast r
  linarith

theorem main :
    (∀ n : ℕ, 1 ≤ n → (term n : ℝ) =
      -4 + ((1-Real.sqrt 5)^n*(-19+13*Real.sqrt 5) + (1+Real.sqrt 5)^n*(19+13*Real.sqrt 5)) /
        (2^(n+1)*Real.sqrt 5)) ∧
    (∀ k : ℕ, term (k+4)+term (k+1) = 2*term (k+3)) ∧
    ((1-X)*(1-X-X^2))*series = X*(12+X-9*X^2) := by
  refine ⟨?_, term_rec, generating⟩
  intro n hn
  rw [term_closed n hn]
  unfold closed
  rw [div_pow, div_pow, pow_succ]
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<5)]

end IdempotentRows

theorem OMA.solution : type_of% @OMA.S_oeis_a224669.main := IdempotentRows.main