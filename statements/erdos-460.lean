import Mathlib

/-!
# Erdős Problem 460

Source: https://www.erdosproblems.com/460
Credit: @YourFriendPollux

## The problem

Let $a_0 = 0$ and $a_1 = 1$, and in general define $a_k$ to be the least integer
$> a_{k-1}$ for which $(n - a_k, n - a_i) = 1$ for all $0 \le i < k$. Does

$$\sum_{0 < a_i < n} \frac{1}{a_i} \to \infty$$

as $n \to \infty$? What about if we restrict the sum to those $i$ such that $n - a_j$ is
divisible by some prime $\le a_j$, or the complement of such $i$?

This question arose in work of Eggleton, Erdős and Selfridge.

## Formalization notes

* `a n k` is $a_k$ for the parameter $n$: `a n 0 = 0`, `a n 1 = 1`, and for `k ≥ 2` it is
  the least integer `m > a n (k-1)` with $\gcd(n - m, n - a_i) = 1$ for all `i < k`. The
  gcds are those of the *integers* `n - m` and `n - a i`, so `a` is allowed to exceed `n`
  (the definition is a genuine recursion on the sequence, not truncated subtraction).
  The set in the `sInf` is nonempty for every `k` (infinitely many `m` are coprime to all
  the finitely many differences `n - a i`), so the recursion is well defined.
* `partialSum n` is $\sum_{0 < a_i < n} 1/a_i$, summing over all indices `i < n` (a term
  with `a i ≥ n` is excluded, and since `a` is strictly increasing only `i < n` can
  contribute, so the range `Finset.range n` captures exactly the indices with `a_i < n`).
* The statement formalizes the *first* question. The two refinements of the source
  (restricting the sum to the `i` for which `n - a_i` has a prime factor `≤ a_i`, or to
  its complement) are further questions and are not part of `main`.
-/

namespace OMA.S_erdos_460

open Filter
open scoped Topology Classical

/-- The Eggleton–Erdős–Selfridge sequence for the parameter `n`. -/
noncomputable def a (n : ℕ) : ℕ → ℕ :=
  fun k => Nat.strongRec (motive := fun _ => ℕ) (fun k ih =>
    if h0 : k = 0 then 0
    else if k = 1 then 1
    else sInf {m : ℕ | ih (k - 1) (Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos) < m ∧
      ∀ i : ℕ, ∀ hi : i < k,
        Int.gcd ((n : ℤ) - (m : ℤ)) ((n : ℤ) - ((ih i hi : ℕ) : ℤ)) = 1}) k

/-- $\sum_{0 < a_i < n} 1/a_i$ for the sequence attached to `n`. -/
noncomputable def partialSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, if 0 < a n i ∧ a n i < n then (1 : ℝ) / (a n i : ℝ) else 0

theorem main : Tendsto (fun n : ℕ => partialSum n) atTop atTop := by
  sorry

end OMA.S_erdos_460
