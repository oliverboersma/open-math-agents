import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.RCLike.Basic

/-!
# A compact surjective linear map has finite-dimensional codomain

Credit: @lucasfreund2-cmd

Source: Mathematics Stack Exchange question 4462775,
https://math.stackexchange.com/questions/4462775/show-that-dimy-infty-application-of-the-hahn-banach-theorem

The source assumes that `X` and `Y` are Banach spaces, that `T : X → Y` is a
surjective linear map, and that the image of the open unit ball is contained
in a compact subset of `Y`. It asks whether `Y` is finite dimensional.

`RCLike` allows either real or complex Banach spaces. Continuity of `T` is
not assumed: it follows from the compact-image hypothesis.
-/

namespace OMA.S_mse_4462775

/-- A surjective linear map of real or complex Banach spaces whose open unit-ball image
is contained in a compact set has finite-dimensional codomain. -/
theorem main :
    ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (T : X →ₗ[𝕜] Y) (hT : Function.Surjective T)
    (hcompact : ∃ D : Set Y, IsCompact D ∧ T '' Metric.ball (0 : X) 1 ⊆ D),
    FiniteDimensional 𝕜 Y := by
  sorry

end OMA.S_mse_4462775
