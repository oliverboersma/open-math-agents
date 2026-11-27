import Mathlib

/-!
# Erdős Problem 1045

Source: https://www.erdosproblems.com/1045
Credit: @YourFriendPollux

## The problem

Let $z_1,\ldots,z_n \in \mathbb{C}$ with $\lvert z_i - z_j\rvert \le 2$ for all $i,j$, and

$$\Delta(z_1,\ldots,z_n) = \prod_{i \ne j} \lvert z_i - z_j \rvert.$$

What is the maximum possible value of $\Delta$? Is it maximised by taking the $z_i$ to be
the vertices of a regular polygon?

Erdős, Herzog and Piranian proved that for a monic polynomial $f$ with connected
$\{z : \lvert f(z)\rvert < 1\}$ and roots $z_1,\ldots,z_n$ one has
$\prod_{i\ne j}\lvert z_i - z_j\rvert < n^n$. For the vertices of a regular polygon the
value of $\Delta$ is $n^n$ for even $n$ and $\cos(\pi/2n)^{-n(n-1)} n^n$ for odd $n$.
Pommerenke proved $\Delta \le 2^{O(n)} n^n$ for all $z_i$ with
$\lvert z_i - z_j\rvert \le 2$. Hu and Tang ($n = 4, 6$) and Cambie (all even $n \ge 4$)
showed that the vertices of a regular polygon do *not* maximise $\Delta$.

## Formalization notes

* `delta z` is $\prod_{i \ne j}\lvert z_i - z_j\rvert$ for the `n`-tuple `z`.
* The source asks "what is the maximum", and the regular polygon is known not to be a
  maximiser, so the statement below records the bound that is actually known, Pommerenke's
  $\Delta \le 2^{O(n)}n^n$, in the form
  `∃ C ≥ 1, ∀ n, ∀ z with pairwise distances ≤ 2, delta z ≤ C ^ n * n ^ n`.
-/

namespace OMA.S_erdos_1045

/-- $\Delta(z_1,\ldots,z_n) = \prod_{i \ne j}\lvert z_i - z_j\rvert$. -/
noncomputable def delta {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖

theorem main :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (z : Fin n → ℂ),
      (∀ i j, ‖z i - z j‖ ≤ 2) → delta z ≤ C ^ n * (n : ℝ) ^ n := by
  sorry

end OMA.S_erdos_1045
