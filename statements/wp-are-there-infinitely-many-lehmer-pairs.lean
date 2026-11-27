import Mathlib

/-!
# Are there infinitely many Lehmer pairs?

Source: https://en.wikipedia.org/wiki/Lehmer_pair
Credit: @lzvxck

The source: a Lehmer pair is a pair of zeros of the Riemann zeta function that are unusually
close to each other. Writing the zeros on the critical line as `1/2 + i γ_n`, consecutive zeros
`γ_n, γ_{n+1}` form a Lehmer pair if
`1 / (γ_n - γ_{n+1})^2 ≥ C * ∑_{m ∉ {n, n+1}} (1 / (γ_m - γ_n)^2 + 1 / (γ_m - γ_{n+1})^2)`
for a constant `C > 5/4`. It is an unsolved problem whether there exist infinitely many
Lehmer pairs (a positive answer would imply that the de Bruijn-Newman constant is
non-negative).

Conventions made explicit here: `γ` ranges over the real ordinates `t` with
`ζ(1/2 + i t) = 0` (zeros on the critical line, of either sign, as in the source's indexing of
all zeros), counted as a set; consecutive means no such ordinate lies strictly between them.
The sum is over all other such ordinates (it converges, since the sum of `1 / |ρ|^2` over the
nontrivial zeros converges).
-/

namespace OMA.S_wp_are_there_infinitely_many_lehmer_pairs

/-- The ordinates `t` of the zeros `1/2 + i t` of the Riemann zeta function on the critical
line. -/
def criticalOrdinates : Set ℝ :=
  {t : ℝ | riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) = 0}

/-- `γ < γ'` are consecutive ordinates of zeros on the critical line. -/
def AreConsecutive (γ γ' : ℝ) : Prop :=
  γ ∈ criticalOrdinates ∧ γ' ∈ criticalOrdinates ∧ γ < γ' ∧
    ∀ t ∈ criticalOrdinates, ¬ (γ < t ∧ t < γ')

/-- The sum `∑_{m ∉ {n, n+1}} (1 / (γ_m - γ_n)^2 + 1 / (γ_m - γ_{n+1})^2)` over all other
ordinates of zeros on the critical line. -/
noncomputable def lehmerSum (γ γ' : ℝ) : ℝ :=
  ∑' t : {t : ℝ // t ∈ criticalOrdinates ∧ t ≠ γ ∧ t ≠ γ'},
    (1 / ((t : ℝ) - γ) ^ 2 + 1 / ((t : ℝ) - γ') ^ 2)

/-- `(γ, γ')` is a Lehmer pair: consecutive ordinates with
`1 / (γ - γ')^2 ≥ C * lehmerSum γ γ'` for some constant `C > 5/4`. -/
def IsLehmerPair (γ γ' : ℝ) : Prop :=
  AreConsecutive γ γ' ∧ ∃ C : ℝ, 5 / 4 < C ∧ C * lehmerSum γ γ' ≤ 1 / (γ - γ') ^ 2

/-- **Lehmer pairs.** There are infinitely many Lehmer pairs. -/
theorem main : Set.Infinite {p : ℝ × ℝ | IsLehmerPair p.1 p.2} := by
  sorry

end OMA.S_wp_are_there_infinitely_many_lehmer_pairs
