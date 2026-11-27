import FormalConjectures.Paper.RiemannHypothesisEquivalents

-- Reduction RiemannHypothesis.beurling_nyman_criterion.R1 of the Beurling-Nyman criterion
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The Beurling-Nyman criterion, split into its two implications

The Beurling-Nyman criterion identifies the Riemann Hypothesis with the density in `L²(0, 1)` of
the finite linear combinations

$$\sum_{\nu = 1}^{n} c_{\nu}\,\rho_{\theta_{\nu}}, \qquad \theta_{\nu} \in (0, 1], \quad
\sum_{\nu = 1}^{n} c_{\nu}\,\theta_{\nu} = 0 .$$

The two implications are proved by completely different means and it is worth separating them.

* `H1` (RH forces density) goes through the explicit formula: under RH the test functions of the
  Nyman–Beurling space are dense because the zeros give enough control over the corresponding
  dilations.

* `H2` (density forces RH) is the converse, and is the harder direction of the equivalence: a
  failure of RH produces a functional vanishing on the space, equivalently a nonzero element of
  the orthogonal complement, which forbids density.

Neither direction is in Mathlib, and neither is a formal consequence of the other.  Together they
are the statement, and the assembly is formal.
-/

namespace OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1

/-- The forward direction: the Riemann Hypothesis implies that the Beurling–Nyman space is dense
in `L²(0, 1)`. -/
def H1 : Prop :=
  RiemannHypothesis →
    Dense { RiemannHypothesis.fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (h : ∑ ν, c ν * θ ν = 0) }

/-- The converse direction: density of the Beurling–Nyman space in `L²(0, 1)` implies the
Riemann Hypothesis. -/
def H2 : Prop :=
  Dense { RiemannHypothesis.fractScalarInvSumL2 n c θ | (n) (c) (θ)
      (hθ : ∀ ν, θ ν ∈ Set.Ioc 0 1) (h : ∑ ν, c ν * θ ν = 0) } →
    RiemannHypothesis

theorem main : H1 → H2 →
    type_of% @RiemannHypothesis.beurling_nyman_criterion := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_RiemannHypothesis_beurling_nyman_criterion_R1
