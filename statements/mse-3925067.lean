import Mathlib

/-!
# Is there a group $G$ for which $\mathrm{Aut}(G) \simeq (\mathbb{R},+)$?

Source: https://math.stackexchange.com/questions/3925067/is-there-a-group-g-for-which-mathrmautg-simeq-mathbbr
Credit: @mgv27

It is classical that $(\mathbb{Q},+)$ is not the automorphism group of any group. How about
$(\mathbb{R},+)$: is there a group $G$ with $\mathrm{Aut}(G)\simeq(\mathbb{R},+)$? The asker
thinks the answer might be no.

Formalization notes:
* `main` states the asker's conjectured direction: there is no group `G` (in `Type`) whose
  automorphism group `MulAut G` is isomorphic, as a group, to `(ℝ, +)` (written
  `Multiplicative ℝ`).
* The ambient logic is Lean's (with choice), matching the asker's use of the axiom of choice.
* Comments observe that such a `G` cannot be abelian (inversion is an automorphism).
-/

namespace OMA.S_mse_3925067

/-- `G` has automorphism group isomorphic to `(ℝ, +)`. -/
def AutIsReal (G : Type) [Group G] : Prop :=
  Nonempty (MulAut G ≃* Multiplicative ℝ)

/-- There is no group `G` with `Aut(G) ≃ (ℝ, +)`. -/
theorem main : ¬ ∃ (G : Type) (_ : Group G), AutIsReal G := by
  sorry

end OMA.S_mse_3925067
