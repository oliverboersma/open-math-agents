import FormalConjectures.ErdosProblems.«1057»

-- Reduction Erdos1057.erdos_1057.variants.harman_lower_bound.R1
-- Source: G. Harman, Watt's mean value theorem and Carmichael numbers, Int. J. Number Theory 4
-- (2008), 241-248, and J. D. Lichtman, Primes in arithmetic progressions to large moduli and
-- shifted primes without large prime factors, arXiv:2211.09641, Theorem 1.1.
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Carmichael counting function exceeds `x ^ 0.33336704`

The exponent `0.33336704` is exactly `0.4736 * 0.7039`, the product of Harman's level `0.4736`
for the Alford–Granville–Pomerance construction and `1 - 0.2961`, where `0.2961` is the
Baker–Harman exponent for smooth shifted primes (Acta Arith. 83 (1998), Theorem 1). The
Alford–Granville–Pomerance theorem loses an arbitrary `ε` in the exponent, so these two inputs as
published give `C(x) ≥ x ^ (0.33336704 - ε)` (in particular Harman's stated `C(x) > x ^ (1/3)`),
with no room left for the exact product. The exact exponent needs smooth shifted primes at some
`β < 0.2961`, which is what Lichtman's theorem provides.

The two hypotheses are therefore, character for character, those of the reduction
`Erdos1057.erdos_1057.variants.lichtman_lower_bound.R1`, so that one proof of each closes both
problems.

* `H1` (Lichtman, Theorem 1.1, with `a = 1`): for every `β > 15 / (32 √e) = 0.2843...` there is
  `C ≥ 1` such that the number of primes `x < p ≤ 2x` with every prime factor of `p - 1` at most
  `x ^ β` is `≫ x / (log x) ^ C`. This is the deep input.
* `H2` (Alford, Granville and Pomerance, 1994, with Harman's level `0.4736` from the 2008 paper):
  if `β` admits such a lower bound for smooth shifted primes, then
  `C(x) ≥ x ^ (0.4736 (1 - β) - ε)` for every `ε > 0` and all large `x`.

`main` checks `15 / (32 √e) < 0.2844` and
`0.4736 * (1 - 0.2844) - 10⁻⁶ = 0.33890716 > 0.33336704`, and combines the two.
-/

namespace OMA.R_Erdos1057_erdos_1057_variants_harman_lower_bound_R1

open Filter Real

/-- Lichtman, Theorem 1.1 (`a = 1`): shifted primes `p - 1` without prime factors above `x ^ β`,
for every `β > 15 / (32 √e)`. -/
def H1 : Prop :=
  ∀ β : ℝ, 15 / (32 * Real.sqrt (Real.exp 1)) < β →
    ∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x / Real.log x ^ C ≤
        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ β}.ncard : ℕ) : ℝ)

/-- Alford–Granville–Pomerance with Harman's level `0.4736`: smooth shifted primes at exponent
`β` give `C(x) ≥ x ^ (0.4736 (1 - β) - ε)`. -/
def H2 : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 →
    (∃ C : ℝ, 1 ≤ C ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x / Real.log x ^ C ≤
        (({p : ℕ | p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ x ^ β}.ncard : ℕ) : ℝ)) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
      x ^ ((0.4736 : ℝ) * (1 - β) - ε) ≤ Erdos1057.carmichaelCounting x

lemma threshold : 15 / (32 * Real.sqrt (Real.exp 1)) < (0.2844 : ℝ) := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hs : (1.6483 : ℝ) < Real.sqrt (Real.exp 1) := by
    apply Real.lt_sqrt_of_sq_lt
    norm_num at he ⊢
    linarith
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

theorem main : H1 → H2 →
    type_of% @Erdos1057.erdos_1057.variants.harman_lower_bound := by
  intro h1 h2
  have h := h2 0.2844 (by norm_num) (by norm_num) (h1 0.2844 threshold)
    (1 / 1000000) (by norm_num)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  refine lt_of_lt_of_le ?_ hx
  exact Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num)

end OMA.R_Erdos1057_erdos_1057_variants_harman_lower_bound_R1
