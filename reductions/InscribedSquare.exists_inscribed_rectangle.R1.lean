import FormalConjectures.Wikipedia.InscribedSquare
import Mathlib

/-!
Vaughan's chord argument for an inscribed rectangle of unspecified aspect ratio.
Unordered chords form a Möbius band. The sum of the endpoints records twice
the midpoint, and the chord length records a nonnegative height. An additional
identification gives the two diagonals. Reflecting an embedded band across its
boundary plane would embed the closed Klein bottle in three-space.
-/

namespace OMA.R_InscribedSquare_exists_inscribed_rectangle_R1

open Topology
open scoped unitInterval

/-- Parameterize unordered chords by a square with its vertical sides glued in
opposite directions. The two horizontal sides parameterize coincident endpoints. -/
def H1 : Prop :=
  let seam (p q : I × I) := p = q ∨
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
  ∃ u v : I × I → Circle, Continuous u ∧ Continuous v ∧
    (∀ t : I, u (0,t) = v (1,unitInterval.symm t) ∧ v (0,t) = u (1,unitInterval.symm t)) ∧
    (∀ p : I × I, u p = v p ↔ p.2 = 0 ∨ p.2 = 1) ∧
    ∀ p q : I × I, ((u p = u q ∧ v p = v q) ∨ (u p = v q ∧ v p = u q)) → seam p q

/-- An upper-half-space map of the Möbius strip whose boundary is in the
horizontal plane must identify two points other than the prescribed seam. -/
def H2 : Prop :=
  let seam (p q : I × I) := p = q ∨
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
  ∀ (f : I × I → EuclideanSpace ℝ (Fin 2)) (h : I × I → ℝ),
    Continuous f → Continuous h →
    (∀ t : I, f (0,t) = f (1,unitInterval.symm t) ∧ h (0,t) = h (1,unitInterval.symm t)) →
    (∀ p : I × I, 0 ≤ h p) → (∀ p : I × I, h p = 0 ↔ p.2 = 0 ∨ p.2 = 1) →
    ∃ p q : I × I, f p = f q ∧ h p = h q ∧ ¬ seam p q

theorem main : H1 → H2 → type_of% @InscribedSquare.exists_inscribed_rectangle := by
  intro chord collision γ hγ
  obtain ⟨u,v,hu,hv,glue,diagonal,unique⟩ := chord
  let f (p : I × I) := γ (u p) + γ (v p)
  let h (p : I × I) := dist (γ (u p)) (γ (v p))
  have hu' := hγ.continuous.comp hu
  have hv' := hγ.continuous.comp hv
  have edge (t : I) : f (0,t) = f (1,unitInterval.symm t) ∧ h (0,t) = h (1,unitInterval.symm t) := by
    obtain ⟨h₁,h₂⟩ := glue t
    simp only [f,h,h₁,h₂]
    exact ⟨add_comm _ _, dist_comm _ _⟩
  have zeroHeight (p : I × I) : h p = 0 ↔ p.2 = 0 ∨ p.2 = 1 := by
    rw [← diagonal p]
    exact dist_eq_zero.trans hγ.injective.eq_iff
  obtain ⟨p,q,hm,hd,hne⟩ := collision f h (hu'.add hv') (hu'.dist hv') edge
    (fun _ => dist_nonneg) zeroHeight
  change γ (u p) + γ (v p) = γ (u q) + γ (v q) at hm
  have hab : γ (u p) ≠ γ (u q) := by
    intro e
    have e' : γ (v p) = γ (v q) := add_left_cancel (e ▸ hm)
    exact hne (unique p q (.inl ⟨hγ.injective e,hγ.injective e'⟩))
  have hbc : γ (u q) ≠ γ (v p) := by
    intro e
    have hpair : γ (u p) + γ (v p) = γ (v q) + γ (v p) := by
      calc
        _ = γ (u q) + γ (v q) := hm
        _ = _ := by rw [e,add_comm]
    have e' := add_right_cancel hpair
    exact hne (unique p q (.inr ⟨hγ.injective e',hγ.injective e.symm⟩))
  exact ⟨u p,u q,v p,v q,_,hm,hd,hab,hbc,rfl⟩

end OMA.R_InscribedSquare_exists_inscribed_rectangle_R1
