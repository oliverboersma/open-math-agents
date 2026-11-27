import Mathlib

/-!
# n conjecture (Browkin–Brzeziński)

Source: https://en.wikipedia.org/wiki/n_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement (first formulation; Browkin–Brzeziński 1994): given `n ≥ 3`, let
`a₁, …, aₙ ∈ ℤ` satisfy
(i) `gcd(a₁, …, aₙ) = 1`,
(ii) `a₁ + ⋯ + aₙ = 0`,
(iii) no proper subsum of `a₁, …, aₙ` equals `0`.
The n conjecture states that for every `ε > 0` there is a constant `C` depending on `n` and `ε`
such that `max(|a₁|, …, |aₙ|) < C_{n,ε} · rad(|a₁| ⋯ |aₙ|) ^ (2n - 5 + ε)`, where `rad(m)` is the
product of the distinct prime factors of `m`.

`main` states this first formulation (the source's second formulation, via a limsup of the
quality, is a related form that also asserts the lower bound; the strong n conjecture of Ramaekers is a different variant and is
not stated here).

Conventions:
* `a : Fin n → ℤ`; `gcd(a₁, …, aₙ)` is `Finset.univ.gcd a` (normalized, so `= 1` means the
  entries are setwise coprime);
* a proper subsum is the sum over a non-empty proper subset `S` of the indices
  (`S.Nonempty ∧ S ≠ univ`); the empty sum and the full sum are excluded since they are
  trivially resp. by (ii) equal to `0`. Since `n ≥ 3`, (iii) forces every `aᵢ ≠ 0`, so the
  product is non-zero and its radical is a positive integer;
* `rad m = ∏ p ∈ m.primeFactors, p` for `m : ℕ`, and the product is `∏ i, |aᵢ|` as a natural
  number (`Int.natAbs`);
* `max |aᵢ|` is `Finset.univ.sup (fun i => (a i).natAbs)`;
* the inequality is read in `ℝ` with the real power `Real.rpow`, exponent `2n - 5 + ε`;
* `C` is a real constant chosen after `n` and `ε` (so it may depend on both), before the `aᵢ`.
-/

namespace OMA.S_wp_n_conjecture

/-- The radical of a natural number: the product of its distinct prime factors. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

theorem main : ∀ n : ℕ, 3 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
    ∀ a : Fin n → ℤ,
      Finset.univ.gcd a = 1 →
      ∑ i, a i = 0 →
      (∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → ∑ i ∈ S, a i ≠ 0) →
      ((Finset.univ.sup (fun i => (a i).natAbs) : ℕ) : ℝ) <
        C * ((rad (∏ i, (a i).natAbs) : ℕ) : ℝ) ^ ((2 * (n : ℝ) - 5) + ε) := by
  sorry

end OMA.S_wp_n_conjecture
