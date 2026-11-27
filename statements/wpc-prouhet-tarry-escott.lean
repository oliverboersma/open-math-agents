import Mathlib

/-!
# Ideal solutions of the Prouhet–Tarry–Escott problem

Source: https://en.wikipedia.org/wiki/Prouhet%E2%80%93Tarry%E2%80%93Escott_problem
Credit: @Andyi955

The Prouhet–Tarry–Escott problem asks for two disjoint multisets `A` and `B` of `n` integers each
whose first `k` power sums agree, that is `∑ a ∈ A, a ^ i = ∑ b ∈ B, b ^ i` for every
`i = 1, …, k`. It is known that `n` must be strictly greater than `k`, and solutions with
`k = n - 1` are called *ideal solutions*.

The source indexes by the size `n = k + 1` of each multiset, and reports that ideal solutions are
known for `3 ≤ n ≤ 10` and for `n = 12`, while no ideal solution is known for `n = 11` or for
`n ≥ 13`. The question posed in the catalogue is whether ideal solutions exist for every degree,
which is `main` below with the same indexing: `k` is the degree and each multiset has `k + 1`
elements.
-/

namespace OMA.S_wpc_prouhet_tarry_escott

/-- `IsIdealSolution k A B` holds when `A` and `B` are disjoint multisets of `k + 1` integers each
whose power sums agree for every exponent `i` with `1 ≤ i ≤ k`. Such a pair is an *ideal solution
of degree `k`*: for multisets of `k + 1` integers the exponent `k` is the largest one for which
agreement can be asked. -/
def IsIdealSolution (k : ℕ) (A B : Multiset ℤ) : Prop :=
  A.card = k + 1 ∧ B.card = k + 1 ∧ Disjoint A B ∧
    ∀ i ∈ Finset.Icc 1 k,
      (A.map (fun a => a ^ i)).sum = (B.map (fun b => b ^ i)).sum

/-- **Prouhet–Tarry–Escott problem**: for every degree `k` there are two disjoint multisets of
`k + 1` integers each whose power sums agree up to exponent `k`.

The source states this by size: ideal solutions are known for `3 ≤ n ≤ 10` and `n = 12`, and none
is known for `n = 11` or `n ≥ 13`, so the case `k = 10` and all `k ≥ 12` are open. -/
theorem main : ∀ k : ℕ, ∃ A B : Multiset ℤ, IsIdealSolution k A B := by
  sorry

end OMA.S_wpc_prouhet_tarry_escott
