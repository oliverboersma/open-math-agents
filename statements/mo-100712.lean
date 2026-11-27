import Mathlib

/-!
# Proving generating functions equality

Source: https://mathoverflow.net/questions/100712
Credit: @zarnab222-dev

The question asks for a proof of the identity of generating functions in `z₁, z₂`
`∑_{r,s,t ≥ 0} q^(r²+rs+s²+st+t²) / ((q)_r (q)_s (q)_t) · z₁^(r+s) z₂^(s+t)
   = ∑_{a,b ≥ 0} q^(a²-ab+b²) / ((q)_a (q)_b) · z₁^a z₂^b`,
where `(q)_n = ∏_{i=1}^{n} (1 - q^i)`.

Translation choices.
* `q` is an indeterminate: coefficients live in the field `ℚ(q) = RatFunc ℚ`, `q = RatFunc.X`,
  so every `(q)_n` is nonzero and the divisions are genuine.
* An identity of formal power series in `z₁, z₂` is an identity of coefficients. The coefficient
  of `z₁^a z₂^b` on the left is the sum over all triples `(r, s, t) : ℕ × ℕ × ℕ` with `r + s = a`
  and `s + t = b`; this index set is finite, and the sum is written as a `finsum` over all triples
  subject to that condition. `main` is the equality of the two coefficients for every `a, b : ℕ`,
  the summation variables starting at `0`.
* A triple is `p = (r, s, t)` with `r = p.1`, `s = p.2.1`, `t = p.2.2`.
* The exponent `a² - ab + b²` is written `a ^ 2 + b ^ 2 - a * b`; since `a * b ≤ a ^ 2 + b ^ 2`
  the natural-number subtraction does not truncate.
-/

namespace OMA.S_mo_100712

/-- The `q`-Pochhammer symbol `(q)_n = ∏_{i=1}^{n} (1 - q^i)` in `ℚ(q)`, with `q = RatFunc.X`. -/
noncomputable def qPoch (n : ℕ) : RatFunc ℚ :=
  ∏ i ∈ Finset.range n, (1 - (RatFunc.X : RatFunc ℚ) ^ (i + 1))

theorem main : ∀ a b : ℕ,
    ∑ᶠ (p : ℕ × ℕ × ℕ) (_ : p.1 + p.2.1 = a ∧ p.2.1 + p.2.2 = b),
        (RatFunc.X : RatFunc ℚ) ^ (p.1 ^ 2 + p.1 * p.2.1 + p.2.1 ^ 2 + p.2.1 * p.2.2 + p.2.2 ^ 2) /
          (qPoch p.1 * qPoch p.2.1 * qPoch p.2.2)
      = (RatFunc.X : RatFunc ℚ) ^ (a ^ 2 + b ^ 2 - a * b) / (qPoch a * qPoch b) := by
  sorry

end OMA.S_mo_100712
