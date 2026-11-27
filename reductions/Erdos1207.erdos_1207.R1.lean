import FormalConjectures.ErdosProblems.«1207»

-- Reduction Erdos1207.erdos_1207.R1: the planar bound from an unramified 2-tower, and the tower
-- Credit: openhuman (agent: claude-code, model claude-opus-5-5). Layered port of
-- github.com/tadamcz/erdos1207 (commit 228fcd87a53ab2d7d925d2c849096dcc4438d96b), (c) 2026 Tom Adamczewski / Epoch AI, Apache-2.0.

/-!
# Erdős 1207 (planar isosceles-free subsets): the geometric half and the arithmetic half

Lee, Pohoata and Zhu [LPZ26] proved the planar power saving `P 2 n < n ^ (1 - c)`; this is a Lean
port of a machine-written, unrefereed proof (github.com/tadamcz/erdos1207) and is not independently
refereed. The proof splits at a Mathlib-only interface:

* `H1` (geometry and counting): if `B` is a number field with `a ^ 2 = 5` carrying, for every `m`, a
  totally real Galois extension `L m` of `B` that is a 2-group, has degree at least `2 ^ m` and has
  trivial different (unramified at all finite primes), then the planar power saving holds.
* `H2` (arithmetic): such a field `B` and such a family `L` exist. This is a class-field-tower
  construction (Golod-Shafarevich type cohomology bounds for a quartic field of controlled
  discriminant, and a unit/Herbrand-quotient argument for total reality).

`main` combines the two.
-/

namespace OMA.R_Erdos1207_erdos_1207_R1

open NumberField Filter

/-- Geometry and counting: an unbounded unramified totally real 2-tower over a field containing the
square root of five gives `P 2 n < n ^ (1 - c)`. -/
def H1 : Prop :=
  ∀ (B : Type) [Field B] [NumberField B] (a : B), a ^ 2 = 5 →
  ∀ (L : ℕ → Type) [∀ m, Field (L m)] [∀ m, NumberField (L m)] [∀ m, Algebra B (L m)]
    [∀ m, IsGalois B (L m)] [∀ m, IsTotallyReal (L m)],
    (∀ m, IsPGroup 2 (L m ≃ₐ[B] L m)) → (∀ m, 2 ^ m ≤ Module.finrank B (L m)) →
    (∀ m, differentIdeal (𝓞 B) (𝓞 (L m)) = ⊤) →
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, (Erdos1207.P 2 n : ℝ) < (n : ℝ) ^ (1 - c)

/-- Arithmetic: a number field `B` with a square root of five has totally real Galois 2-extensions of
unboundedly large degree, all unramified at the finite primes. -/
def H2 : Prop :=
  ∃ (B : Type) (_ : Field B) (_ : NumberField B) (a : B), a ^ 2 = 5 ∧
  ∃ (L : ℕ → Type) (_ : ∀ m, Field (L m)) (_ : ∀ m, NumberField (L m))
    (_ : ∀ m, Algebra B (L m)),
    (∀ m, IsGalois B (L m)) ∧ (∀ m, IsTotallyReal (L m)) ∧
    (∀ m, IsPGroup 2 (L m ≃ₐ[B] L m)) ∧ (∀ m, 2 ^ m ≤ Module.finrank B (L m)) ∧
    (∀ m, differentIdeal (𝓞 B) (𝓞 (L m)) = ⊤)

theorem main : H1 → H2 → type_of% @Erdos1207.erdos_1207 := by
  intro h1 h2
  obtain ⟨B, iF, iN, a, ha, L, jF, jN, jA, hGal, hReal, hG, hdeg, hun⟩ := h2
  exact @h1 B iF iN a ha L jF jN jA hGal hReal hG hdeg hun

end OMA.R_Erdos1207_erdos_1207_R1
