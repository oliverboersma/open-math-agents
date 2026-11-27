import Mathlib

/-!
# A totally asymmetric two-player zero-sum game with payoffs ±1 and a unique fully mixed Nash equilibrium

Mathematics Stack Exchange 199784 (user aaa, 2012).
Source: https://math.stackexchange.com/questions/199784
Credit: @tatashbar

Question (as stated in the source). Is there a totally asymmetric 2-player zero-sum game with all
payoffs `±1`, with a unique Nash equilibrium which assigns positive probability to each strategy?
By totally asymmetric, the source means that there is no nontrivial way to permute the rows and
columns of the payoff matrix that leaves the payoffs invariant.

`main` states that the answer is yes.

Conventions of this translation:
* A game is an `m × n` real matrix `A` indexed by `Fin m` and `Fin n`. The entry `A i j` is the payoff
  to player 1 (the row player) when player 1 plays row `i` and player 2 plays column `j`; player 2
  receives `-A i j`. The shape is not assumed square.
* All payoffs are `±1`: every entry is `1` or `-1`.
* Mixed strategies are points of Mathlib's `stdSimplex`. `payoff A x y = ∑ i, ∑ j, x i * A i j * y j`
  is the expected payoff to player 1. `(x, y)` is a Nash equilibrium when neither player gains by a
  unilateral deviation to another mixed strategy: `x` maximises `payoff A · y` and `y` minimises
  `payoff A x ·`. Nash equilibria are taken among all mixed strategy pairs, and uniqueness is
  uniqueness among all of them.
* Totally asymmetric: if a row permutation `σ` and a column permutation `τ` satisfy
  `A (σ i) (τ j) = A i j` for all `i, j`, then both are the identity. The two examples in the source
  agree with this reading: for `!![1, -1; -1, 1]` swapping both rows and columns is a nontrivial
  invariant pair, and `!![-1, -1; -1, 1]` has none.
* Each player has at least two strategies (`1 < m`, `1 < n`). Read literally, the `1 × 1` game `!![1]`
  satisfies every condition for trivial reasons (one strategy each, played with probability `1`, and
  only the identity permutations). The source does not count it: both of its examples are `2 × 2`
  games, and its own case analysis runs over `2 × n`, `3 × n` and `4 × 4` games and concludes that
  none of those works. So the degenerate case is excluded here. This only strengthens the existence
  claim: a proof of `main` also answers the literal question.
-/

namespace OMA.S_mse_199784

/-- Expected payoff to player 1 (the row player) when player 1 plays the mixed strategy `x` and
player 2 (the column player) plays the mixed strategy `y`. The game is zero-sum: player 2 receives
`-payoff A x y`. -/
def payoff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * y j

/-- `(x, y)` is a Nash equilibrium, in mixed strategies, of the zero-sum game with payoff matrix `A`:
both are probability vectors, no mixed strategy of player 1 earns more than `x` against `y`, and no
mixed strategy of player 2 concedes less than `y` against `x`. -/
def IsNashEquilibrium {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    Prop :=
  x ∈ stdSimplex ℝ (Fin m) ∧ y ∈ stdSimplex ℝ (Fin n) ∧
    (∀ x' ∈ stdSimplex ℝ (Fin m), payoff A x' y ≤ payoff A x y) ∧
    (∀ y' ∈ stdSimplex ℝ (Fin n), payoff A x y ≤ payoff A x y')

/-- Totally asymmetric: no nontrivial pair (row permutation, column permutation) leaves the payoff
matrix invariant. -/
def IsTotallyAsymmetric {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n)),
    (∀ i j, A (σ i) (τ j) = A i j) → σ = 1 ∧ τ = 1

/-- There is a totally asymmetric two-player zero-sum game with all payoffs `±1` (and at least two
strategies per player) that has a unique Nash equilibrium, and this equilibrium assigns positive
probability to every strategy of both players. -/
theorem main :
    ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ), 1 < m ∧ 1 < n ∧
      (∀ i j, A i j = 1 ∨ A i j = -1) ∧
      IsTotallyAsymmetric A ∧
      ∃ (x : Fin m → ℝ) (y : Fin n → ℝ), IsNashEquilibrium A x y ∧
        (∀ i, 0 < x i) ∧ (∀ j, 0 < y j) ∧
        ∀ (x' : Fin m → ℝ) (y' : Fin n → ℝ), IsNashEquilibrium A x' y' → x' = x ∧ y' = y := by
  sorry

end OMA.S_mse_199784
