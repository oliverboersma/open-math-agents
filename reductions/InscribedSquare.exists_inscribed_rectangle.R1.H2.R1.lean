import OMAReductions.R_InscribedSquare_exists_inscribed_rectangle_R1
import Mathlib

/-!
Cap a Möbius band in the nonnegative half-space by a cone in the negative
half-space. Scaling the boundary by its cone radius makes the cap injective
off its apex. The quotient then embeds in three-space if the original band
has no additional identifications. This is the capping argument in Vaughan's
inscribed-rectangle theorem.
-/

open scoped unitInterval
namespace OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1

/-- The capped strip is parametrized by a sphere with antipodal points identified. -/
def H1 : Prop :=
  let B := {p : I × I // p.2 = 0 ∨ p.2 = 1}
  let seam (p q : I × I) := p = q ∨
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
  let glue : ((I × I) ⊕ (B × I)) → ((I × I) ⊕ (B × I)) → Prop := fun x y =>
    match x,y with
    | .inl p, .inl q => seam p q
    | .inl p, .inr w => w.2 = 1 ∧ seam p w.1.val
    | .inr w, .inl p => w.2 = 1 ∧ seam p w.1.val
    | .inr v, .inr w => v.2 = w.2 ∧ (v.2 = 0 ∨ seam v.1.val w.1.val)
  ∃ π : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → Quot glue,
    Continuous π ∧ ∀ x y, π x = π y ↔ x = y ∨ x.val = -y.val

/-- Every continuous antipodally invariant map of the two-sphere to real three-space
identifies a pair outside the same antipodal orbit. -/
def H2 : Prop :=
  ∀ g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 2) × ℝ,
    Continuous g → (∀ x y, x.val = -y.val → g x = g y) →
    ∃ x y, g x = g y ∧ x ≠ y ∧ x.val ≠ -y.val

theorem main : H1 → H2 → OMA.R_InscribedSquare_exists_inscribed_rectangle_R1.H2 := by
  intro chart obstruction f h hf hh hseam hnonneg hzero
  let B := {p : I × I // p.2 = 0 ∨ p.2 = 1}
  let seam (p q : I × I) := p = q ∨
    (p.1 = 0 ∧ q.1 = 1 ∧ q.2 = unitInterval.symm p.2) ∨
    (p.1 = 1 ∧ q.1 = 0 ∧ p.2 = unitInterval.symm q.2)
  let glue : ((I × I) ⊕ (B × I)) → ((I × I) ⊕ (B × I)) → Prop := fun x y =>
    match x,y with
    | .inl p, .inl q => seam p q
    | .inl p, .inr w => w.2 = 1 ∧ seam p w.1.val
    | .inr w, .inl p => w.2 = 1 ∧ seam p w.1.val
    | .inr v, .inr w => v.2 = w.2 ∧ (v.2 = 0 ∨ seam v.1.val w.1.val)
  by_contra hn
  let band (p : I × I) := (f p, h p)
  let cap (v : B × I) := ((v.2 : ℝ) • f v.1.val, (v.2 : ℝ) - 1)
  have hband (p q : I × I) : band p = band q ↔ seam p q := by
    constructor
    · intro he
      by_contra hne
      exact hn ⟨p,q,congrArg Prod.fst he,congrArg Prod.snd he,hne⟩
    · rintro (e | ⟨hs,hs',ht⟩ | ⟨hs,hs',ht⟩)
      · rw [e]
      · obtain ⟨s,t⟩ := p
        obtain ⟨s',t'⟩ := q
        change s = 0 at hs
        change s' = 1 at hs'
        change t' = unitInterval.symm t at ht
        subst s; subst s'; subst t'
        exact Prod.ext (hseam t).1 (hseam t).2
      · obtain ⟨s,t⟩ := p
        obtain ⟨s',t'⟩ := q
        change s = 1 at hs
        change s' = 0 at hs'
        change t = unitInterval.symm t' at ht
        subst s; subst s'; subst t
        exact Prod.ext (hseam t').1.symm (hseam t').2.symm
  have hbzero (b : B) : h b.val = 0 := (hzero b.val).2 b.property
  have base (b : B) : cap (b,1) = band b.val := by
    simp [cap,band,hbzero]
  have hmix (p : I × I) (w : B × I) : band p = cap w ↔ w.2 = 1 ∧ seam p w.1.val := by
    obtain ⟨b,t⟩ := w
    change band p = cap (b,t) ↔ t = 1 ∧ seam p b.val
    constructor
    · intro he
      have hd := congrArg Prod.snd he
      change h p = (t : ℝ) - 1 at hd
      have ht : t = 1 := Subtype.ext (by
        change (t : ℝ) = 1
        linarith [hnonneg p,t.property.2])
      subst t
      exact ⟨rfl,(hband p b.val).mp (he.trans (base b))⟩
    · rintro ⟨rfl,hs⟩
      exact ((hband p b.val).mpr hs).trans (base b).symm
  have hcap (v w : B × I) : cap v = cap w ↔
      v.2 = w.2 ∧ (v.2 = 0 ∨ seam v.1.val w.1.val) := by
    obtain ⟨a,t⟩ := v
    obtain ⟨b,u⟩ := w
    change cap (a,t) = cap (b,u) ↔ t = u ∧ (t = 0 ∨ seam a.val b.val)
    constructor
    · intro he
      have hd := congrArg Prod.snd he
      change (t : ℝ)-1 = (u : ℝ)-1 at hd
      have ht : t = u := Subtype.ext (by linarith)
      subst u
      refine ⟨rfl, ?_⟩
      by_cases hz : t = 0
      · exact Or.inl hz
      · right
        have he' := congrArg Prod.fst he
        have hs : (t : ℝ) ≠ 0 := fun e => hz (Subtype.ext e)
        have hab : f a.val = f b.val := smul_right_injective _ hs he'
        exact (hband _ _).mp (Prod.ext hab ((hbzero a).trans (hbzero b).symm))
    · rintro ⟨rfl,hx⟩
      rcases hx with rfl | hx
      · simp [cap]
      · have he := congrArg Prod.fst ((hband _ _).mpr hx)
        change f a.val = f b.val at he
        simp [cap,he]
  let F : (I × I) ⊕ (B × I) → EuclideanSpace ℝ (Fin 2) × ℝ := Sum.elim band cap
  have hF : Continuous F := by
    apply continuous_sum_dom.mpr
    constructor
    · exact hf.prodMk hh
    · change Continuous (fun v : B × I => ((v.2 : ℝ) • f v.1.val, (v.2 : ℝ) - 1))
      have hb : Continuous (fun v : B × I => v.1.val) := continuous_subtype_val.comp continuous_fst
      have ht : Continuous (fun v : B × I => (v.2 : ℝ)) := continuous_subtype_val.comp continuous_snd
      exact (ht.smul (hf.comp hb)).prodMk (ht.sub continuous_const)
  have hglue (x y) : F x = F y ↔ glue x y := by
    cases x with
    | inl p =>
      cases y with
      | inl q => exact hband p q
      | inr w => exact hmix p w
    | inr v =>
      cases y with
      | inl q => exact eq_comm.trans (hmix q v)
      | inr w => exact hcap v w
  let G : Quot glue → EuclideanSpace ℝ (Fin 2) × ℝ :=
    Quot.lift F (fun x y hxy => (hglue x y).mpr hxy)
  have hc : Continuous G := continuous_quot_lift _ hF
  have hi : Function.Injective G := by
    rintro ⟨x⟩ ⟨y⟩ he
    exact Quot.sound ((hglue x y).mp he)
  obtain ⟨π,hπ,horbit⟩ := chart
  obtain ⟨x,y,he,hne,hnneg⟩ := obstruction (G ∘ π) (hc.comp hπ)
    (fun x y hxy => congrArg G ((horbit x y).mpr (Or.inr hxy)))
  exact ((horbit x y).mp (hi he)).elim hne hnneg

end OMA.R_InscribedSquare_exists_inscribed_rectangle_R1_H2_R1
