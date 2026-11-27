import Mathlib

/-!
# Erdős Problem 708

Source: https://www.erdosproblems.com/708
Credit: @YourFriendPollux

## The problem

Let $g(n)$ be minimal such that for any $A \subseteq [2,\infty) \cap \mathbb{N}$ with
$|A| = n$ and any set $I$ of $\max(A)$ consecutive integers there exists some
$B \subseteq I$ with $|B| = g(n)$ such that

$$\prod_{a \in A} a \mid \prod_{b \in B} b.$$

Is it true that $g(n) \le (2+o(1))n$? Or perhaps even $g(n) \le 2n$?

Erdős and Surányi [ErSu59] proved $g(n) \ge (2-o(1))n$ and $g(3) = 4$.

## Formalization notes

* The question asked is the first one, $g(n) \le (2+o(1))n$, stated as
  `∀ ε > 0, ∀ᶠ n, g n ≤ (2 + ε) * n`; the stronger guess $g(n) \le 2n$ of the source is
  the same statement with `ε = 0`. Both are recorded here, the first as `main`.
* "a set `I` of `max(A)` consecutive integers" is `I = Finset.Icc m (m + max(A) - 1)`.
* `A` ranges over finite subsets of `[2, ∞) ∩ ℕ`, encoded as `∀ a ∈ A, 2 ≤ a`.
* `B ⊆ I` is stated for finite sets; a finite `B` of cardinality `g n` inside `I` is the
  intended reading, and the product is over that finite set.
-/

namespace OMA.S_erdos_708

/-- `I` is a block of `L` consecutive natural numbers. -/
def IsConsecutiveBlock (I : Finset ℕ) (L : ℕ) : Prop :=
  ∃ m : ℕ, I = Finset.Icc m (m + L - 1)

/-- `k` is admissible for `n`: for every `n`-element set `A ⊆ [2, ∞) ∩ ℕ` and every block
`I` of `max A` consecutive integers there is a `k`-element `B ⊆ I` whose product is
divisible by the product of the elements of `A`. -/
def AdmissibleSize (n k : ℕ) : Prop :=
  ∀ (A : Finset ℕ) (hA : A.Nonempty), A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ I : Finset ℕ, IsConsecutiveBlock I (A.max' hA) →
      ∃ B : Finset ℕ, B ⊆ I ∧ B.card = k ∧ ((∏ a ∈ A, a) ∣ (∏ b ∈ B, b))

/-- `g n` is the least admissible size for `n`. -/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {k : ℕ | AdmissibleSize n k}

theorem main : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (g n : ℝ) ≤ (2 + ε) * n := by
  sorry

end OMA.S_erdos_708
