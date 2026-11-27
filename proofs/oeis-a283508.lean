import OMAStatements.S_oeis_a283508
import Mathlib

/-!
# Proof of the OEIS A283508 conjectures

Credit: @ddanila

## Outline

Rule 643 turns a cell ON exactly when it has no ON neighbour, or when it is ON and has at
least three ON neighbours.  Starting from the single ON origin:

* after one step every cell is ON except the four neighbours of the origin (`stageOne`);
* after two steps every cell is ON except the eight cells around the origin (`stable`);
* `stable` is a fixed point of the rule, so the grid never changes again.

Here `a n` encodes positions `0,…,n` on the nonnegative x-axis at time `n` as decimal
digits, with the origin most significant.  For `n ≥ 2` that axis reads `1, 0, 1, 1, 1, …`.
Although the grid is fixed from time 2, the encoded prefix grows by one cell each time,
appending digit 1.  Together with `a 0 = 1` and `a 1 = 10`, this gives
`a (n+1) = 10 * a n + 1` for `n ≥ 1`.  The closed formula, recurrence and generating
function are arithmetic consequences.

Rule 187 turns a cell ON exactly when it is OFF or its right neighbour is ON.  From a single
ON cell, the row at time `n+1` is all ON except one OFF cell at position `-n`.  The centre
therefore reads `1, 0, 1, 1, 1, …` through time, so A267623 satisfies the same recursion.

The three Rule 643 transition identities are checked by evaluating the 5×5 window around
the origin and treating all remaining cells uniformly (`step_eq`, using `step_far`).
-/

namespace A283508Solution

open OMA.S_oeis_a283508

/-! ## Rule 643: the grid stabilises after two steps -/

/-- The cell `(x, y)` lies outside the square of radius `r` around the origin. -/
private def Far (r x y : ℤ) : Prop := x < -r ∨ r < x ∨ y < -r ∨ r < y

/-- Stage 1: everything ON except the four orthogonal neighbours of the origin. -/
private def stageOne : Grid := fun x y => decide
  (¬ ((x = 0 ∧ (y = -1 ∨ y = 1)) ∨ (y = 0 ∧ (x = -1 ∨ x = 1))))

/-- Stage 2 onwards: everything ON except the eight cells surrounding the origin. -/
private def stable : Grid := fun x y => decide
  (x < -1 ∨ 1 < x ∨ y < -1 ∨ 1 < y ∨ (x = 0 ∧ y = 0))

private lemma initial_far {x y : ℤ} (h : Far 1 x y) : initial x y = false := by
  have h' : ¬ (x = 0 ∧ y = 0) := by unfold Far at h; omega
  simp [initial, h']

private lemma stageOne_far {x y : ℤ} (h : Far 1 x y) : stageOne x y = true := by
  have h' : ¬ ((x = 0 ∧ (y = -1 ∨ y = 1)) ∨
      (y = 0 ∧ (x = -1 ∨ x = 1))) := by unfold Far at h; omega
  simp [stageOne, h']

private lemma stable_far {x y : ℤ} (h : Far 1 x y) : stable x y = true := by
  have h' : x < -1 ∨ 1 < x ∨ y < -1 ∨ 1 < y ∨ (x = 0 ∧ y = 0) := by
    unfold Far at h; omega
  simp [stable, h']

/-- If a grid is constantly `b` outside radius 1, then outside radius 2 a cell and its four
neighbours are all `b`, so the next value is the uniform-background value. -/
private lemma step_far (g : Grid) (b : Bool)
    (hg : ∀ x y, Far 1 x y → g x y = b)
    {x y : ℤ} (h : Far 2 x y) : step g x y = rule b (4 * bit b) := by
  have h0 := hg x y (by unfold Far at *; omega)
  have h1 := hg (x+1) y (by unfold Far at *; omega)
  have h2 := hg (x-1) y (by unfold Far at *; omega)
  have h3 := hg x (y+1) (by unfold Far at *; omega)
  have h4 := hg x (y-1) (by unfold Far at *; omega)
  simp only [step, neighbors, h0, h1, h2, h3, h4]
  congr 1
  omega

/-- To prove `step g = g'` for grids that are constant outside radius 1, it suffices to
check the background value and the 5×5 window around the origin. -/
private lemma step_eq (g g' : Grid) (b b' : Bool)
    (hg : ∀ x y, Far 1 x y → g x y = b)
    (hg' : ∀ x y, Far 1 x y → g' x y = b')
    (background : rule b (4 * bit b) = b')
    (window : ∀ x y : ℤ, -2 ≤ x → x ≤ 2 → -2 ≤ y → y ≤ 2 → step g x y = g' x y) :
    step g = g' := by
  funext x y
  by_cases h : Far 2 x y
  · rw [step_far g b hg h, hg' x y (by unfold Far at *; omega), background]
  · unfold Far at h
    exact window x y (by omega) (by omega) (by omega) (by omega)

private lemma step_initial : step initial = stageOne :=
  step_eq initial stageOne false true (fun _ _ h => initial_far h)
    (fun _ _ h => stageOne_far h) (by decide) (by
      intro x y hx0 hx1 hy0 hy1
      interval_cases x <;> interval_cases y <;> decide)

private lemma step_stageOne : step stageOne = stable :=
  step_eq stageOne stable true true (fun _ _ h => stageOne_far h)
    (fun _ _ h => stable_far h) (by decide) (by
      intro x y hx0 hx1 hy0 hy1
      interval_cases x <;> interval_cases y <;> decide)

private lemma step_stable : step stable = stable :=
  step_eq stable stable true true (fun _ _ h => stable_far h)
    (fun _ _ h => stable_far h) (by decide) (by
      intro x y hx0 hx1 hy0 hy1
      interval_cases x <;> interval_cases y <;> decide)

private lemma state_add_two (n : ℕ) : state (n+2) = stable := by
  induction n with
  | zero => exact (congrArg step step_initial).trans step_stageOne
  | succ n ih =>
    change step (state (n+2)) = stable
    rw [ih, step_stable]

/-! ## Rule 643: reading the x-axis -/

private lemma stable_axis (m : ℕ) : stable m 0 = decide (m ≠ 1) := by
  by_cases h : m = 1
  · subst m; decide
  · simp only [stable, Int.reduceNeg, Nat.one_lt_cast, Int.neg_pos, Int.reduceLT,
      Int.natCast_eq_zero, and_true, false_or, Bool.decide_or, ne_eq, h,
      not_false_eq_true, decide_true, Bool.or_eq_true, decide_eq_true_eq]
    omega

private lemma a_zero : a 0 = 1 := by decide
private lemma a_one : a 1 = 10 := by decide
private lemma a_two : a 2 = 101 := by decide

/-- From stage 2 on, the grid is fixed but the observed prefix grows, appending digit 1. -/
private lemma a_succ_of_two_le (n : ℕ) (hn : 2 ≤ n) : a (n+1) = 10 * a n + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  have h1 : state (k+2+1) = stable := state_add_two (k+1)
  have h2 : state (k+2) = stable := state_add_two k
  unfold a
  rw [h1, h2, encode, stable_axis]
  simp [bit]

private lemma a_succ (n : ℕ) (hn : 0 < n) : a (n+1) = 10 * a n + 1 := by
  by_cases h : n = 1
  · subst n; rw [a_two, a_one]
  · exact a_succ_of_two_le n (by omega)

/-! ## The three A283508 formulas -/

/-- Division-free form of the closed formula. -/
private lemma exact_identity (k : ℕ) : 90 * a (k+1) + 10 = 91 * 10^(k+1) := by
  induction k with
  | zero => simp [a_one]
  | succ k ih =>
    rw [a_succ (k+1) (by omega), pow_succ]
    omega

private lemma formula (n : ℕ) (hn : 0 < n) : a n = (91 * 10^n - 10) / 90 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  have h := exact_identity k
  omega

private lemma recurrence (n : ℕ) (hn : 2 < n) :
    (a n : ℤ) = 11 * (a (n-1) : ℤ) - 10 * (a (n-2) : ℤ) := by
  have h1 := a_succ (n-1) (by omega)
  have h2 := a_succ (n-2) (by omega)
  have e1 : n-1+1 = n := by omega
  have e2 : n-2+1 = n-1 := by omega
  rw [e1] at h1
  rw [e2] at h2
  omega

/-- Multiplication by X^k shifts the sequence coefficients by k places. -/
private lemma coeff_series_mul_X (k n : ℕ) :
    PowerSeries.coeff n (series * PowerSeries.X^k) =
      if k ≤ n then (a (n-k) : ℤ) else 0 := by
  simp only [PowerSeries.coeff_mul_X_pow', series, PowerSeries.coeff_mk]

/-- The recurrence makes every coefficient beyond degree 2 of
`series * ((1 - X) * (1 - 10 * X))` vanish. -/
private lemma recurrence_coefficient (n : ℕ) :
    (a (n+3) : ℤ) - 11 * (a (n+2) : ℤ) + 10 * (a (n+1) : ℤ) = 0 := by
  have h := recurrence (n+3) (by omega)
  simp only [show n+3-1=n+2 by omega, show n+3-2=n+1 by omega] at h
  omega

/-- For the product of series and its conjectured denominator, coefficients 0, 1, 2
come from the initial values; all higher ones vanish by the recurrence. -/
private lemma generating_function :
    series * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X)) =
      1 - PowerSeries.X + PowerSeries.X^2 := by
  have expand : series * ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X)) =
      series - PowerSeries.C 11 * (series * PowerSeries.X^1) +
        PowerSeries.C 10 * (series * PowerSeries.X^2) := by
    simp only [map_ofNat, pow_one]
    ring
  rw [expand]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_series_mul_X]
  simp only [series, PowerSeries.coeff_mk]
  rcases n with _ | _ | _ | n
  · simp [a_zero]
  · simp [a_one, a_zero]
  · simp [a_two, a_one, a_zero, PowerSeries.coeff_X]
  · simpa [PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
      using recurrence_coefficient n

/-! ## Rule 187: the centre column -/

private lemma rule187 (l c r : Bool) : A267623.rule l c r = (!c || r) := by
  cases l <;> cases c <;> cases r <;> decide

/-- A row that is ON everywhere except at position `k`. -/
private def hole (k : ℤ) : A267623.Row := fun x => decide (x ≠ k)

private lemma step187_initial : A267623.step A267623.initial = hole 0 := by
  funext x
  simp only [A267623.step, A267623.initial, rule187, hole, ne_eq, decide_not,
    Bool.or_eq_left_iff_imp, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not]
  omega

/-- The OFF cell moves one position to the left at each step. -/
private lemma step187_hole (k : ℤ) : A267623.step (hole k) = hole (k-1) := by
  funext x
  by_cases h : x = k-1
  · simp [A267623.step, rule187, hole, h]
  · have h1 : x+1 ≠ k := by omega
    simp [A267623.step, rule187, hole, h1, h]

private lemma state187_succ (n : ℕ) : A267623.state (n+1) = hole (-(n : ℤ)) := by
  induction n with
  | zero => exact step187_initial
  | succ n ih =>
    change A267623.step (A267623.state (n+1)) = hole (-↑(n+1 : ℕ))
    rw [ih, step187_hole]
    congr 1
    push_cast
    ring

private lemma centre187 (n : ℕ) : A267623.state n 0 = decide (n ≠ 1) := by
  cases n with
  | zero => decide
  | succ n => rw [state187_succ]; simp [hole, eq_comm]

private lemma sequence_eq (n : ℕ) : a n = A267623.a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases n with
    | zero => decide
    | succ n =>
      rw [a_succ (n+1) (by omega), A267623.a, centre187, ← ih]
      simp [bit]

end A283508Solution

theorem OMA.solution : type_of% @OMA.S_oeis_a283508.main :=
  ⟨A283508Solution.generating_function, A283508Solution.formula,
    A283508Solution.recurrence, A283508Solution.sequence_eq⟩
