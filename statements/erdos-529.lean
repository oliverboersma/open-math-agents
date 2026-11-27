import Mathlib

/-!
# Erdős Problem 529

Source: https://www.erdosproblems.com/529
Credit: @timlantin

Let $d_k(n)$ be the expected distance from the origin after taking $n$ random steps from the
origin in $\mathbb{Z}^k$, conditional on no self intersections (a self-avoiding walk). Is it true
that $\lim_{n\to\infty} d_2(n)/n^{1/2} = \infty$? Is it true that $d_k(n) \ll n^{1/2}$ for
$k \geq 3$?

Formalization notes:
* A walk of `n` steps is a sequence of unit steps `Fin n → Fin k × Bool` (direction, sign).
  It is self-avoiding when its `n + 1` positions are distinct.
* $d_k(n)$ is the average, over all self-avoiding walks of `n` steps from the origin, of the
  Euclidean distance of the endpoint from the origin.
* The two questions of the source are joined by a conjunction.
* Written with Claude Code (AI-assisted).
-/

namespace OMA.S_erdos_529

open Filter

/-- The unit step in $\mathbb{Z}^k$ in direction `s.1`, positive if `s.2` is true. -/
def step {k : ℕ} (s : Fin k × Bool) : Fin k → ℤ :=
  Pi.single s.1 (if s.2 then 1 else -1)

/-- The position after the first `j` steps of the walk with steps `w`. -/
def position {k n : ℕ} (w : Fin n → Fin k × Bool) (j : ℕ) : Fin k → ℤ :=
  ∑ t : Fin n with t.val < j, step (w t)

/-- The walk is self-avoiding: its positions after `0, 1, …, n` steps are distinct. -/
def IsSelfAvoiding {k n : ℕ} (w : Fin n → Fin k × Bool) : Prop :=
  Function.Injective fun j : Fin (n + 1) ↦ position w j

/-- The self-avoiding walks of `n` steps in $\mathbb{Z}^k$ from the origin. -/
noncomputable def selfAvoidingWalks (k n : ℕ) : Finset (Fin n → Fin k × Bool) := by
  classical
  exact Finset.univ.filter IsSelfAvoiding

/-- Euclidean distance from the origin of a point of $\mathbb{Z}^k$. -/
noncomputable def dist0 {k : ℕ} (p : Fin k → ℤ) : ℝ :=
  Real.sqrt (∑ i, ((p i : ℝ)) ^ 2)

/-- $d_k(n)$: the mean endpoint distance of a uniformly random self-avoiding walk. -/
noncomputable def d (k n : ℕ) : ℝ :=
  (∑ w ∈ selfAvoidingWalks k n, dist0 (position w n)) / (selfAvoidingWalks k n).card

/-- $d_2(n)/\sqrt{n} \to \infty$, and $d_k(n) \ll \sqrt{n}$ for every $k \geq 3$. -/
theorem main :
    Tendsto (fun n : ℕ ↦ d 2 n / Real.sqrt n) atTop atTop ∧
      ∀ k ≥ 3, (fun n : ℕ ↦ d k n) =O[atTop] (fun n : ℕ ↦ Real.sqrt n) := by
  sorry

end OMA.S_erdos_529
