import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-!
# Does multinomial expectation preserve monotonicity of vector fields?
Source: https://mathoverflow.net/questions/47888 (daizhuo, December 1, 2010).
Formalization by @LDJAI with OpenAI Codex.
-/

namespace OMA.S_mo_47888

def onSimplex {k : ℕ} (p : Fin k → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1

def fieldMonotone {k : ℕ} (f : (Fin k → ℤ) → Fin k → ℝ) : Prop :=
  ∀ x y, 0 ≤ ∑ j, ((x j : ℝ) - (y j : ℝ)) * (f x j - f y j)

/-- Add one count to category j. -/
def bump {k : ℕ} (x : Fin k → ℤ) (j : Fin k) : Fin k → ℤ :=
  fun i => x i + if i = j then 1 else 0

/-- Expectation of a scalar observable of the count vector after n independent
categorical draws, starting with counts x. The multinomial law starts at x = 0. -/
noncomputable def average {k : ℕ} (p : Fin k → ℝ) (h : (Fin k → ℤ) → ℝ) :
    ℕ → (Fin k → ℤ) → ℝ
  | 0, x => h x
  | n + 1, x => ∑ j, p j * average p h n (bump x j)

/-- Expectation taken component by component. -/
noncomputable def smooth {k : ℕ} (n : ℕ) (f : (Fin k → ℤ) → Fin k → ℝ)
    (p : Fin k → ℝ) (j : Fin k) : ℝ :=
  average p (fun x => f x j) n 0

theorem main :
    ∀ n k : ℕ, 0 < n → 0 < k → ∀ f : (Fin k → ℤ) → Fin k → ℝ,
    fieldMonotone f → ∀ p q : Fin k → ℝ, onSimplex p → onSimplex q →
    0 ≤ ∑ j, (p j - q j) * (smooth n f p j - smooth n f q j) := by
  sorry

end OMA.S_mo_47888
