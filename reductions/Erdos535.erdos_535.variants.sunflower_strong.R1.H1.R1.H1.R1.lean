import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- Reduction Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.H1.R1 of step Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.H1
-- Credit: @my-other-github-account

/-!
# The uniform word-sunflower bound from a planar spectral point and the sunflower comparison

Source: OpenAI, *An exponential bound for sunflowers* and *Euclidean geometry in the asymptotic spectrum
of tensors* (OpenAI Math Release, Nov 2026), formalized in Lean 4 in github.com/openai/math at commit
3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). The parent step is the word bound behind
`OAI.Combinatorics.Sunflower.fixedBase_words`; it is split exactly as in that proof, along the planar
input `exists_planar_point` (H1) and the comparison of Part I (H2). The hypothesis texts are the same
as those of the merged reduction Erdos20.erdos_20.R1.H2.R1 by @JamesSlash, reused so that one proof of
each step serves both problems.

- `H1`: every planar placement of at least two sites carries one spectral point whose one-bit prices
  are the normalized Gaussian mean widths.
- `H2`: for each `r ≥ 3` some planar placement forces, for any spectral point with those prices, a
  bound `D ^ n` on word-sunflower-free families, uniformly in the alphabet size.
-/

namespace OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nontrivial I] (x : I ↪ EuclideanSpace ℝ (Fin 2)),
    ∃ Φ : (Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ) → ℝ,
      (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧
      (∀ X : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧
      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) ∧
      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,
        Φ ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *
          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩ = Φ X * Φ Y) ∧
      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,
        Φ ⟨fun i => X.1 i + Y.1 i, fun z =>
          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)
          else if h' : ∀ i, X.1 i ≤ z i then
            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h' i; omega⟩)
          else 0⟩ = Φ X + Φ Y) ∧
      ∀ (S : Finset I) (hS : S.Nonempty),
        Real.logb 2 (Φ ⟨fun i => if i ∈ S then 2 else 1,
          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) =
        (∫ u, S.sup' hS (fun i => inner ℝ u (x i)) ∂ProbabilityTheory.stdGaussian _) /
          ∫ u, Finset.univ.sup' Finset.univ_nonempty (fun i => inner ℝ u (x i))
            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))

def H2 : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ (I : Type) (_ : Fintype I) (_ : DecidableEq I) (_ : Nontrivial I)
    (x : I ↪ EuclideanSpace ℝ (Fin 2)),
    ∀ Φ : (Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ) → ℝ,
      ((∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧
      (∀ X : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧
      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,
        (∃ A : ∀ i, Matrix (Fin (Y.1 i)) (Fin (X.1 i)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ i, A i (y i) (z i)) * X.2 z) → Φ Y ≤ Φ X) ∧
      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,
        Φ ⟨fun i => X.1 i * Y.1 i, fun z => X.2 (fun i => (finProdFinEquiv.symm (z i)).1) *
          Y.2 (fun i => (finProdFinEquiv.symm (z i)).2)⟩ = Φ X * Φ Y) ∧
      (∀ X Y : Σ d : I → ℕ, (∀ i, Fin (d i)) → ℂ,
        Φ ⟨fun i => X.1 i + Y.1 i, fun z =>
          if h : ∀ i, (z i : ℕ) < X.1 i then X.2 (fun i => ⟨z i, h i⟩)
          else if h' : ∀ i, X.1 i ≤ z i then
            Y.2 (fun i => ⟨z i - X.1 i, by have h2 : (z i : ℕ) < X.1 i + Y.1 i := (z i).2; have := h' i; omega⟩)
          else 0⟩ = Φ X + Φ Y) ∧
      ∀ (S : Finset I) (hS : S.Nonempty),
        Real.logb 2 (Φ ⟨fun i => if i ∈ S then 2 else 1,
          fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) =
        (∫ u, S.sup' hS (fun i => inner ℝ u (x i)) ∂ProbabilityTheory.stdGaussian _) /
          ∫ u, Finset.univ.sup' Finset.univ_nonempty (fun i => inner ℝ u (x i))
            ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))) →
      ∃ D : ℕ, 1 ≤ D ∧ ∀ (n m : ℕ) (W : Finset (Fin n → Fin m)),
        (∀ w : Fin r → Fin n → Fin m, (∀ i, w i ∈ W) →
          (∀ j : Fin n, (∀ a b, w a j = w b j) ∨ Function.Injective (fun i => w i j)) →
          ∀ a b, w a = w b) →
        W.card ≤ D ^ n

theorem main : H1 → H2 → OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1.H1 := by
  intro h1 h2 r hr
  obtain ⟨I, _, _, _, x, hx⟩ := h2 r hr
  obtain ⟨Φ, hΦ⟩ := h1 I x
  exact hx Φ hΦ

end OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1
