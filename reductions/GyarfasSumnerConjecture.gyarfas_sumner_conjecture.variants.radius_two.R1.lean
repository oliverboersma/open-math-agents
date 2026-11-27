import FormalConjectures.Wikipedia.GyarfasSumnerConjecture
import Mathlib

/-! Reduction of the Kierstead-Penrice theorem (chi-boundedness of trees of radius at most 2)
to the star case (trees of radius 1, which follows from Ramsey's theorem) and the strict
radius-2 case, handling the radius-0 (singleton tree) case directly in `main`. -/

namespace OMA.R_GyarfasSumnerConjecture_gyarfas_sumner_conjecture_variants_radius_two_R1

open SimpleGraph

private lemma isChiBoundedBy_zero_of_dist_zero {W : Type} [Fintype W] [DecidableEq W]
    (T : SimpleGraph W) [DecidableRel T.Adj] (c : W) (hc : ∀ w : W, T.dist c w = 0)
    (hconn : T.Connected) :
    GyarfasSumnerConjecture.IsChiBoundedBy T (fun _ => 0) := by
  intro V _ _ G _ hT
  have hV : IsEmpty V := by
    by_contra h
    rw [not_isEmpty_iff] at h
    obtain ⟨v⟩ := h
    have hsub : ∀ w : W, w = c := fun w =>
      ((hconn c w).dist_eq_zero_iff.mp (hc w)).symm
    refine hT ⟨⟨⟨fun _ => v, fun a b _ => by rw [hsub a, hsub b]⟩, ?_⟩⟩
    intro a b
    rw [hsub a, hsub b]
    simp
  simp

/-- Trees of radius 1 (stars) specify chi-bounded classes. -/
def H1 : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
    T.IsTree → (∃ c : W, (∀ w : W, T.dist c w ≤ 1) ∧ (∃ w : W, T.dist c w = 1)) →
      ∃ f : ℕ → ℕ, GyarfasSumnerConjecture.IsChiBoundedBy T f

/-- Kierstead-Penrice (1994) for trees of radius exactly 2: every finite tree with a centre
at distance at most 2 from all vertices and distance 2 from some vertex specifies a
chi-bounded class. -/
def H2 : Prop :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
    T.IsTree → (∃ c : W, (∀ w : W, T.dist c w ≤ 2) ∧ (∃ w : W, T.dist c w = 2)) →
      ∃ f : ℕ → ℕ, GyarfasSumnerConjecture.IsChiBoundedBy T f

theorem main : H1 → H2 →
    type_of% @GyarfasSumnerConjecture.gyarfas_sumner_conjecture.variants.radius_two := by
  intro h1 h2 W _ _ T _ hT ⟨c, hrad⟩
  by_cases h2ex : ∃ w : W, T.dist c w = 2
  · exact h2 T hT ⟨c, hrad, h2ex⟩
  · push_neg at h2ex
    have hle1 : ∀ w : W, T.dist c w ≤ 1 := fun w => by
      have hw := hrad w
      have hne := h2ex w
      omega
    by_cases h1ex : ∃ w : W, T.dist c w = 1
    · exact h1 T hT ⟨c, hle1, h1ex⟩
    · push_neg at h1ex
      have h0 : ∀ w : W, T.dist c w = 0 := fun w => by
        have hw := hle1 w
        have hne := h1ex w
        omega
      exact ⟨fun _ => 0, isChiBoundedBy_zero_of_dist_zero T c h0 hT.connected⟩

end OMA.R_GyarfasSumnerConjecture_gyarfas_sumner_conjecture_variants_radius_two_R1
