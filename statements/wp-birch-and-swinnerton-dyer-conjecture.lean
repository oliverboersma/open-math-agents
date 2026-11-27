import Mathlib

/-!
# Birch and Swinnerton-Dyer conjecture

Source: https://en.wikipedia.org/wiki/Birch_and_Swinnerton-Dyer_conjecture
Credit: @carterleffen

We use the strong form for elliptic curves over number fields from the introduction.
The displayed formula in the article is its specialization to the rationals.
For a general number field we use the relative height and discriminant conventions of
Dokchitser and Dokchitser, Ann. of Math. 172 (2010), Conjecture 2.1.

The period, Tamagawa factors and height pairing are adapted from google-deepmind/formal-conjectures
at 9097e2f90e66, copyright 2026 The Formal Conjectures Authors and The Tau Ceti contributors,
licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

namespace OMA.S_wp_birch_and_swinnerton_dyer_conjecture

open WeierstrassCurve NumberField IsDedekindDomain
open scoped Classical

noncomputable section

variable {K : Type*} [Field K]

/-- The absolute discriminant of the equation divided by the norm of the minimal
discriminant ideal corrects the differential of a possibly nonminimal equation. -/
def period [NumberField K] (E : WeierstrassCurve K) : ℝ :=
  let minDisc : Ideal (𝓞 K) := ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    let V := v.adicCompletion K
    let R := v.adicCompletionIntegers K
    let d := ((E⁄V).minimal R).Δ
    v.asIdeal ^ (-WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation V d)).toNat
  (|(Algebra.norm ℚ E.Δ : ℝ)| / minDisc.absNorm) ^ (1 / 12 : ℝ) *
    ∏ v : InfinitePlace K, if h : v.IsReal then
      let W := E.map (InfinitePlace.embedding_of_isReal h)
      2 * ∫ x : ℝ, (Real.sqrt (W.Ψ₂Sq.eval x))⁻¹
    else
      let W := E.map v.embedding
      4 * ∫ x : ℂ, ‖W.Ψ₂Sq.eval x‖⁻¹

/-- On a minimal model the index of the points with nonsingular reduction is the
local Tamagawa number. Count their distinct cosets in the full local group. -/
def tamagawaNumber {R V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field V] [Algebra R V] [IsFractionRing R V] (W : Projective R) : ℕ :=
  let good : Set (Projective.Point (W⁄V)) := {P | ∃ q : Fin 3 → R,
    P.point = ⟦(algebraMap R V <| q ·)⟧ ∧
      Projective.Nonsingular (W.map (IsLocalRing.residue R)) (IsLocalRing.residue R <| q ·)}
  Nat.card (Set.range fun P : Projective.Point (W⁄V) ↦ (P + ·) '' good)

def tamagawaProduct [NumberField K] (E : Projective K) : ℕ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    let R := v.adicCompletionIntegers K
    tamagawaNumber (V := v.adicCompletion K) (((E⁄(v.adicCompletion K)).minimal R).integralModel R)

def xHeight [NumberField K] {E : Affine K} : E.Point → ℝ
  | .zero => 0
  | .some x .. => Height.logHeight₁ x

def canonicalHeight [NumberField K] {E : Affine K} (P : E.Point) : ℝ :=
  Filter.atTop.limUnder fun n : ℕ ↦ xHeight (2 ^ n • P) / 4 ^ n

/-- Regulator on representatives of a basis of the free part, including the empty
basis when the Mordell–Weil rank is zero. -/
def regulator [NumberField K] {E : Affine K} {r : ℕ} (P : Fin r → E.Point) : ℝ :=
  let gram : Matrix (Fin r) (Fin r) ℝ := fun i j ↦
    (canonicalHeight (P i + P j) - canonicalHeight (P i) - canonicalHeight (P j)) / 2
  |gram.det|

/-- A global 1-cocycle becomes a coboundary with coefficients in the geometric points
over the completion V. The compatibility equation expresses restriction of a local
Galois automorphism along the chosen embedding of algebraic closures. -/
def locallyTrivial (E : Affine K)
    (c : Field.absoluteGaloisGroup K → Affine.Point (E⁄(AlgebraicClosure K)))
    (V : Type*) [Field V] [Algebra K V] : Prop :=
  ∀ j : AlgebraicClosure K →ₐ[K] AlgebraicClosure V,
    ∃ P : Affine.Point (E⁄(AlgebraicClosure V)),
      ∀ (τ : Field.absoluteGaloisGroup V) (σ : Field.absoluteGaloisGroup K),
        (∀ x, τ.toAlgHom (j x) = j (σ.toAlgHom x)) →
          Affine.Point.map (W' := E) j (c σ) =
            Affine.Point.map (W' := E) (τ.restrictScalars K).toAlgHom P - P

/-- Continuous cocycles that split at every place. Continuity into the discrete
group of geometric points means that each fibre is open. -/
def locallyTrivialCocycles [NumberField K] (E : Affine K) :=
  {c : Field.absoluteGaloisGroup K → Affine.Point (E⁄(AlgebraicClosure K)) //
    (∀ P, IsOpen {σ | c σ = P}) ∧
    (∀ σ τ, c (σ * τ) = c σ + Affine.Point.map (W' := E) σ.toAlgHom (c τ)) ∧
    (∀ v : InfinitePlace K, locallyTrivial E c v.Completion) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), locallyTrivial E c (v.adicCompletion K))}

/-- The underlying set of the Tate–Shafarevich group. Two locally trivial cocycles
represent the same class precisely when their difference is a global coboundary. -/
def sha [NumberField K] (E : Affine K) :=
  Quot fun c d : locallyTrivialCocycles E ↦ ∃ P : Affine.Point (E⁄(AlgebraicClosure K)),
    ∀ σ, c.val σ - d.val σ = Affine.Point.map (W' := E) σ.toAlgHom P - P

theorem main :
    ∀ (K : Type*) [Field K] [NumberField K] (E : Affine K) [E.IsElliptic],
      ∃ L : ℂ → ℂ, Meromorphic L ∧ (∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s) ∧
        meromorphicOrderAt L 1 = Module.finrank ℤ E.Point ∧ Finite (sha E) ∧
        ∃ (b : Module.Basis (Fin (Module.finrank ℤ E.Point)) ℤ
            (E.Point ⧸ Submodule.torsion ℤ E.Point)) (P : Fin (Module.finrank ℤ E.Point) → E.Point),
          (∀ i, (Submodule.torsion ℤ E.Point).mkQ (P i) = b i) ∧
          meromorphicTrailingCoeffAt L 1 =
            ((period E * regulator P * Nat.card (sha E) * tamagawaProduct E.toProjective /
              (Real.sqrt |(discr K : ℝ)| * (Nat.card (AddCommGroup.torsion E.Point) : ℝ) ^ 2) : ℝ) : ℂ) := by
  sorry

end

end OMA.S_wp_birch_and_swinnerton_dyer_conjecture
