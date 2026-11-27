import Mathlib

/-!
# MathOverflow 342399

Source: https://mathoverflow.net/questions/342399
-/

namespace OMA.S_mo_342399

open CategoryTheory

universe u v u₁ v₁ u₂

theorem main : ∀ (R : Type u) [CommRing R] (C : Type u₁) (D : Type u₂)
      [Category.{v₁} C] [Category.{v} D] [Preadditive C] [Preadditive D]
      [Linear R C] [Linear R D] (F : C ⥤ D) (G : D ⥤ C) [F.Linear R],
      (F ⊣ G) → G.Linear R := by
  sorry

end OMA.S_mo_342399
