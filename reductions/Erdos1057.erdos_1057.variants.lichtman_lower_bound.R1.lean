import FormalConjectures.ErdosProblems.«1057»

-- Reduction Erdos1057.erdos_1057.variants.lichtman_lower_bound.R1
-- Source: J. D. Lichtman, Primes in arithmetic progressions to large moduli and shifted primes
-- without large prime factors, arXiv:2211.09641, Theorem 1.1 and Corollary 1.2.
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Lichtman's lower bound for the Carmichael counting function

Corollary 1.2 of Lichtman (arXiv:2211.09641) is deduced in the paper from exactly two inputs.

* `H1` (Lichtman, Theorem 1.1, with `a = 1`): for every `β > 15 / (32 √e) = 0.2843...` there is
  `C ≥ 1` such that the number of primes `x < p ≤ 2x` with every prime factor of `p - 1` at most
  `x ^ β` is `≫ x / (log x) ^ C`. This is the new deep input (a mean value theorem for primes in
  arithmetic progressions to moduli up to `x ^ (17/32)`, refining Baker and Harman, 1998).
* `H2` (Alford, Granville and Pomerance, 1994, in the form of Harman, Int. J. Number Theory 4
  (2008)): if `β` admits such a lower bound for smooth shifted primes, then
  `C(x) ≥ x ^ (0.4736 (1 - β) - ε)` for every `ε > 0` and all large `x`. This is the
  Carmichael construction (a modulus `L` built from primes `q` with `q - 1` smooth, many primes
  `dk + 1` with `d ∣ L`, and the zero-subsequence theorem of van Emde Boas and Kruyswijk), with
  Harman's level `0.4736` for primes in progressions. Lichtman quotes it in this form right
  after Corollary 1.2.

`main` checks `15 / (32 √e) < 0.2844` and `0.4736 * (1 - 0.2844) = 0.33890816 > 0.3389`, and
combines the two.
-/

namespace OMA.R_Erdos1057_erdos_1057_variants_lichtman_lower_bound_R1

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
    type_of% @Erdos1057.erdos_1057.variants.lichtman_lower_bound := by
  intro h1 h2
  have h := h2 0.2844 (by norm_num) (by norm_num) (h1 0.2844 threshold)
    (1 / 1000000) (by norm_num)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  refine lt_of_lt_of_le ?_ hx
  exact Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num)

end OMA.R_Erdos1057_erdos_1057_variants_lichtman_lower_bound_R1
