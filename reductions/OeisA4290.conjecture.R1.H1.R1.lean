import OMAReductions.R_OeisA4290_conjecture_R1

-- Reduction OeisA4290.conjecture.R1.H1.R1 of step OeisA4290.conjecture.R1.H1
-- Credit: @marcusbuffett

/-!
# Two provable families in the coprime case of Radcliffe's question on A004290

The parent step asks, for every `n < 10^k - 1` coprime to `10`, for a positive multiple of `n`
with decimal digits `0` and `1` that is smaller than the repunit `(10^(9k) - 1) / 9`.

Two families of `n` can be settled outright, and they are the ones for which the bound is
approached (the divisors of `99...9` and of repunits):

* `H1` (digit stacking). If `n` divides `10^t - 1` for some `0 < t ≤ k`, write `d_j` for the
  decimal digits of `n` and take `m` to be the sum of `10^(j + t r)` over `j < t`, `r < d_j`.
  Since `10^t` is `1` modulo `10^t - 1`, `m` is congruent to `n`, hence divisible by `n`. It has
  digits `0` and `1`, at most `9t ≤ 9k` of them, and it is not the full repunit because
  `n < 10^k - 1` leaves some digit below `9` or some block unused.
* `H2` (short repunits). If `9n` divides `10^t - 1` for some `0 < t < 9k`, the repunit with `t`
  digits is such a multiple.
* `H3` is everything else, and stays open. Measured over all `n < 10^4`, the cases outside `H1`
  and `H2` need far fewer than `9k` digits (about `3.3k`), but no proof is known.

`main` is the case distinction. The hypotheses `H1` and `H2` do not need coprimality.
-/

namespace OMA.R_OeisA4290_conjecture_R1_H1_R1

/-- Digit stacking: the divisors of `10^t - 1` with `0 < t ≤ k`. -/
def H1 : Prop :=
  ∀ k n t : ℕ, 0 < n → n < 10 ^ k - 1 → 0 < t → t ≤ k → n ∣ 10 ^ t - 1 →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- Short repunits: the `n` dividing a repunit with fewer than `9k` digits. -/
def H2 : Prop :=
  ∀ k n t : ℕ, 0 < n → n < 10 ^ k - 1 → 0 < t → t < 9 * k → 9 * n ∣ 10 ^ t - 1 →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- The open remainder: `n` coprime to `10` outside both families. -/
def H3 : Prop :=
  ∀ k n : ℕ, 0 < n → n < 10 ^ k - 1 → Nat.Coprime n 10 →
    (∀ t : ℕ, 0 < t → t ≤ k → ¬ n ∣ 10 ^ t - 1) →
    (∀ t : ℕ, 0 < t → t < 9 * k → ¬ 9 * n ∣ 10 ^ t - 1) →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

theorem main : H1 → H2 → H3 → OMA.R_OeisA4290_conjecture_R1.H1 := by
  intro h1 h2 h3 k n hn hlt hco
  by_cases c1 : ∃ t : ℕ, 0 < t ∧ t ≤ k ∧ n ∣ 10 ^ t - 1
  · obtain ⟨t, ht0, htk, hd⟩ := c1
    exact h1 k n t hn hlt ht0 htk hd
  by_cases c2 : ∃ t : ℕ, 0 < t ∧ t < 9 * k ∧ 9 * n ∣ 10 ^ t - 1
  · obtain ⟨t, ht0, htk, hd⟩ := c2
    exact h2 k n t hn hlt ht0 htk hd
  exact h3 k n hn hlt hco (fun t a b c => c1 ⟨t, a, b, c⟩) (fun t a b c => c2 ⟨t, a, b, c⟩)

end OMA.R_OeisA4290_conjecture_R1_H1_R1
