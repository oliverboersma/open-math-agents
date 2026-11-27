import Mathlib

/-!
# An Entropy Inequality (generalized)

Source: https://mathoverflow.net/questions/138395
Credit: @koolkao

Question (Daniel Friedan, MathOverflow 138395, 2013). Let `X, Y` be probability measures on
`{1, 2, …, n}`. For `0 ≤ α ≤ 1`, set `K = ∑ᵢ X(i)^α Y(i)^(1-α)`, so that `Z := X^α Y^(1-α) / K` is
also a probability measure on `{1, 2, …, n}`. Prove the inequality
`α H(X) + (1 - α) H(Y) ≥ K² H(Z)`, where `H(X) = -∑ᵢ X(i) log X(i)` is the entropy function.

Reading of the source (conventions it leaves implicit):
* `{1, …, n}` is `Fin n`, and a probability measure on it is a vector of nonnegative weights
  summing to `1` (written out rather than via `stdSimplex`, which is deprecated in later Mathlib).
  `n` is arbitrary.
* `H` uses the convention `0 log 0 = 0`, via `Real.negMulLog`. Any logarithm base greater than `1`
  gives an equivalent inequality, since both sides are linear in `H` and `K` does not involve the
  logarithm; we use the natural logarithm.
* `X(i)^α` is the real power `Real.rpow`, with `0^0 = 1`. This matters only for `α ∈ {0, 1}`,
  where it gives `K = 1` and `Z = Y` (resp. `Z = X`), and both sides are equal. (The other natural
  reading, the limit `α → 0⁺`, also makes the endpoint cases true and easy.)
* `K > 0` is assumed, because the source says that `Z` is a probability measure, which needs
  `K ≠ 0`. (`K = 0` happens only for `0 < α < 1` and `X`, `Y` with disjoint supports.) The
  hypothesis is harmless: without it, Lean's `0 / 0 = 0` would make the left side `0` there, and the
  inequality would hold trivially since entropy is nonnegative.
* The source also restates the inequality for commuting Hamiltonians and asks whether it extends
  to non-commuting ones. The commuting form is the same inequality with full supports, which is a
  special case of this one. The quantum extension is a separate further question, not stated here.

Status: the case `α = 1/2` (MathOverflow 138275, `H(X) + H(Y) ≥ 2K² H(Z)`) was proved by fedja
(accepted answer, August 2013). For general `α` the two MathOverflow answers to 138395 contain no
proof. Fedja's argument reduces to a one-coordinate inequality with `K` replaced by its Hölder upper
bound `x^α y^(1-α) + (1-x)^α (1-y)^(1-α)`; for general `α` that reduction fails (our numerics, e.g.
`x = 0.98680`, `y = 0.0015171`, `α = 0.077897`, deficit about `-5.7e-5`), although the full
inequality held in all our numerical searches. No proof or counterexample for general `α` is known
to us (November 2026).
-/

namespace OMA.S_mo_138395

/-- Shannon entropy `H(P) = -∑ᵢ P(i) log P(i)` (natural logarithm, `0 log 0 = 0`). -/
noncomputable def entropy {n : ℕ} (P : Fin n → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (P i)

theorem main :
    ∀ (n : ℕ) (X Y : Fin n → ℝ), (∀ i, 0 ≤ X i) → ∑ i, X i = 1 → (∀ i, 0 ≤ Y i) → ∑ i, Y i = 1 →
      ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
        0 < ∑ i, X i ^ α * Y i ^ (1 - α) →
        (∑ i, X i ^ α * Y i ^ (1 - α)) ^ 2 *
            entropy (fun i => X i ^ α * Y i ^ (1 - α) / (∑ j, X j ^ α * Y j ^ (1 - α))) ≤
          α * entropy X + (1 - α) * entropy Y := by
  sorry

end OMA.S_mo_138395
