import FormalConjectures.GreensOpenProblems.«92»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Green92_green_92_variants_chase_upper_R1
open Finset Filter Green92
open scoped Classical

/-- Amplified pairwise tests at Chase's sample complexity. -/
def H1 : Prop :=
  ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    let m := ⌈Real.exp (C * (n:ℝ)^(1/5 : ℝ) * Real.log n ^ 5)⌉₊
    ∃ D : (Fin n → Bool) → (Fin n → Bool) → (Fin m → List Bool) → Prop,
      (∀ x y o, x ≠ y → D x y o → ¬ D y x o) ∧ (∀ x y, x ≠ y →
      (univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ D x y (fun j => Green92.trace x (S j))).card ≤
        Fintype.card (Fin m → Finset (Fin n)) / (10 * 2^n))

/-- A candidate winning every pairwise test gives a decoder, by a union bound. -/
def H2 : Prop :=
  ∀ (n m : ℕ) (D : (Fin n → Bool) → (Fin n → Bool) → (Fin m → List Bool) → Prop),
    (∀ x y o, x ≠ y → D x y o → ¬ D y x o) → (∀ x y, x ≠ y →
      (univ.filter fun S : Fin m → Finset (Fin n) =>
        ¬ D x y (fun j => Green92.trace x (S j))).card ≤
        Fintype.card (Fin m → Finset (Fin n)) / (10 * 2^n)) →
    ∃ R : (Fin m → List Bool) → Fin n → Bool, ∀ x, (9/10 : ℝ) ≤ successProb R x

theorem main : H1 → H2 → type_of% @Green92.green_92.variants.chase_upper := by
  rintro ⟨C,hC,pairs⟩ decode
  refine ⟨C,hC,?_⟩
  filter_upwards [pairs] with n hn
  obtain ⟨D,hD,he⟩ := hn
  exact Nat.sInf_le (decode _ _ D hD he)

end OMA.R_Green92_green_92_variants_chase_upper_R1
