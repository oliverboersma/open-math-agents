import Mathlib

/-!
# On the polynomials $\sum_{k=0}^n\binom{n+k}k^m q^k$

Source: https://mathoverflow.net/questions/479301
Credit: @zarnab222-dev

A sequence P_0, P_1, P_2, ... of polynomials with real coefficients is q-log-convex if for each
n = 1, 2, 3, ... every coefficient of P_{n+1} P_{n-1} - P_n^2 is nonnegative. The question asks
whether, for every integer m ≥ 2, the sequence S^m_n(q) = ∑_{k=0}^n binom(n+k, k)^m q^k (n ≥ 0)
is q-log-convex. We state the affirmative claim (the conjecture in the question).

Translation choices: polynomials live in `Polynomial ℝ` with `X` playing the role of q; m and n
are natural numbers; the sum over k = 0..n is `Finset.range (n + 1)`; the index n - 1 is natural
subtraction, used only under the hypothesis 1 ≤ n, where it is exact; `coeff i` is 0 beyond the
degree, so quantifying over all i : ℕ is the same as quantifying over every coefficient.
-/

namespace OMA.S_mo_479301

open Polynomial

/-- The polynomial `S^m_n(q) = ∑_{k=0}^{n} binom(n+k, k)^m q^k`. -/
noncomputable def S (m n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (((n + k).choose k : ℝ) ^ m) * X ^ k

/-- A sequence of real polynomials is q-log-convex if for each `n ≥ 1` every coefficient of
`P (n+1) * P (n-1) - P n ^ 2` is nonnegative. -/
def QLogConvex (P : ℕ → ℝ[X]) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ i : ℕ, 0 ≤ (P (n + 1) * P (n - 1) - P n ^ 2).coeff i

/-- The conjecture: for every integer `m ≥ 2` the sequence `(S^m_n(q))_{n ≥ 0}` is
q-log-convex. -/
theorem main : ∀ m : ℕ, 2 ≤ m → QLogConvex (fun n => S m n) := by
  sorry

end OMA.S_mo_479301
