import FormalConjectures.GreensOpenProblems.«100»
import Mathlib
open Filter Finset Green100
open scoped Topology
namespace OMA.R_Green100_green_100_variants_operator_norm_R1

lemma lampGroup (G X : Type) [Group G] [Countable G] [Countable X] [MulAction G X] :
    ∃ W : Type, ∃ wk : Group W, ∃ _ : Countable W, ∃ r : G →* W, ∃ a : X → W,
    (∀ x, a x * a x = 1) ∧ (∀ x y, Commute (a x) (a y)) ∧
      (∀ g x, r g * a x = a (g • x) * r g) ∧
      ∀ x y, x ≠ y → a x * a y ≠ 1 := by
  classical
  let Y := X × Bool
  let lift : G →* Equiv.Perm Y := {
    toFun := fun g => (MulAction.toPerm g).prodCongr (Equiv.refl Bool)
    map_one' := by apply Equiv.ext; rintro ⟨y,b⟩; change ((1:G)•y,b) = (y,b); rw [one_smul]
    map_mul' := by intro g h; apply Equiv.ext; rintro ⟨y,b⟩; change ((g*h)•y,b) = (g•(h•y),b); rw [mul_smul] }
  let flip (x : X) (p : Y) : Y := (p.1,if p.1=x then !p.2 else p.2)
  have invol (x : X) : Function.Involutive (flip x) := by
    rintro ⟨y,b⟩; by_cases h : y=x <;> simp [flip,h]
  let lamp (x : X) : Equiv.Perm Y := (invol x).toPerm _
  let gen : G ⊕ X → Equiv.Perm Y := Sum.elim lift lamp
  let f : FreeGroup (G ⊕ X) →* Equiv.Perm Y := FreeGroup.lift gen
  have rg (g : G) : lift g ∈ f.range := ⟨FreeGroup.of (.inl g),by simp [f,gen]⟩
  have ra (x : X) : lamp x ∈ f.range := ⟨FreeGroup.of (.inr x),by simp [f,gen]⟩
  let W := f.range
  let r : G →* W := lift.codRestrict W rg
  let a (x : X) : W := ⟨lamp x,ra x⟩
  have ct : Countable W := Function.Surjective.countable f.rangeRestrict_surjective
  refine ⟨W, inferInstance, ct, r, a, ?_, ?_, ?_, ?_⟩
  · intro x; apply Subtype.ext; apply Equiv.ext; exact invol x
  · intro x y
    apply Subtype.ext; apply Equiv.ext
    rintro ⟨z,b⟩
    change flip x (flip y (z,b)) = flip y (flip x (z,b))
    dsimp only [flip]; split_ifs <;> simp_all
  · intro g x
    apply Subtype.ext; apply Equiv.ext
    rintro ⟨y,b⟩
    change ((g•y),if y=x then !b else b) = ((g•y),if g•y=g•x then !b else b)
    simp
  · intro x y h ee
    have e := congrArg (fun w : W => ((w.val : Equiv.Perm Y) (x,false)).2) ee
    change (flip x (flip y (x,false))).2 = false at e
    simp [flip,h] at e

lemma sequences (W : Type) [Group W] [Countable W] (H : OperatorNormApprox W) :
    ∃ d : ℕ → ℕ, ∃ φ : ∀ j : ℕ, W → Matrix.unitaryGroup (Fin (d j)) ℂ,
    (∀ j, φ j 1 = 1) ∧
    (∀ a b, Tendsto (fun j => opDist (φ j (a*b)) (φ j a * φ j b)) atTop (𝓝 0)) ∧
    ∀ a ≠ (1:W), ∀ᶠ j : ℕ in atTop, 1 ≤ opDist (φ j a) 1 := by
  classical
  obtain ⟨e,surj⟩ := exists_surjective_nat W
  let F (j : ℕ) := insert 1 ((range j).image e)
  have exhaust (a : W) : ∀ᶠ j : ℕ in atTop, a ∈ F j := by
    obtain ⟨i,rfl⟩ := surj a
    filter_upwards [eventually_gt_atTop i] with j hj using mem_insert_of_mem (mem_image.mpr ⟨i,mem_range.mpr hj,rfl⟩)
  choose d φ one mul sep using fun j => H (F j) (mem_insert_self _ _) (1/((j:ℝ)+1)) (by positivity)
  refine ⟨d,φ,one,?_,fun a ha => (exhaust a).mono fun j hj => sep j a hj ha⟩
  intro a b
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [exhaust a,exhaust b,exhaust (a*b)] with j ha hb hab using (mul j a ha b hb hab).le

/- Eckhardt, Non-MF groups and non-finite full group C*-algebras, 2026,
Examples 3.2 and 4.5. The affine lattice group in dimension three has the
fixed-point property and embeds into an ambient group with contracting conjugation. -/
def H1 : Prop := ∃ G : Type, ∃ _ : Group G, ∃ _ : Countable G, ∃ Γ : Subgroup G,
  Group.FG Γ ∧ (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : Γ →* E ≃ₗᵢ[ℂ] E) (c : Γ → E), (∀ g h, c (g*h) = c g + ρ g (c h)) →
    ∃ v : E, ∀ g, c g = ρ g v - v) ∧
  ∃ t : G, (∀ g ∈ Γ, t*g*t⁻¹ ∈ Γ) ∧ ∃ g ∈ Γ, t⁻¹*g*t ∉ Γ

/- The weighted Hilbert–Schmidt construction in Theorem 4.3. The resulting
representation is dominated in norm by a sequence of finite matrix models. -/
def H2 : Prop := ∀ (G : Type) [Group G] [Countable G] (Γ : Subgroup G), Group.FG Γ →
  ∀ (X : Type) [Countable X] [MulAction G X] (x : X) (γ : Γ)
    (W : Type) [Group W] [Countable W] (r : G →* W) (a : X → W),
  (∀ y, a y*a y=1) → (∀ y z, Commute (a y) (a z)) →
  (∀ g y, r g*a y=a (g•y)*r g) →
  ∀ (d : ℕ → ℕ) (φ : ∀ j, W → Matrix.unitaryGroup (Fin (d j)) ℂ), (∀ j, φ j 1=1) →
  (∀ g h, Tendsto (fun j => opDist (φ j (g*h)) (φ j g*φ j h)) atTop (𝓝 0)) →
  (∀ᶠ j in atTop, 1 ≤ opDist (φ j (a ((γ:G)•x)*a x)) 1) →
  ∃ E : Type, ∃ _ : NormedAddCommGroup E, ∃ _ : InnerProductSpace ℂ E, ∃ _ : CompleteSpace E,
  ∃ ρ : G →* E ≃ₗᵢ[ℂ] E, ∃ c : Γ → E,
  (∀ g h, c (g*h) = c g + ρ (g:G) (c h)) ∧ (∀ g : Γ, (g:G)•x=x → c g=0) ∧
  (∃ g, c g ≠ 0) ∧ ∃ n : ℕ → ℕ, ∃ U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ,
    (∀ g h, Tendsto (fun j => opDist (U j (g*h)) (U j g*U j h)) atTop (𝓝 0)) ∧
    ∀ (A : Finset G) (z : G → ℂ) (b : ℝ),
      (∀ᶠ j in atTop, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (∑ g ∈ A, z g • (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ))‖ ≤ b) →
      ∀ v : E, ‖∑ g ∈ A, z g • ρ g v‖ ≤ b*‖v‖

/- Theorem 3.1 for representations factoring through a matrix sequence
quotient. Equivalent nested Kazhdan projections coincide by finiteness. -/
def H3 : Prop := ∀ (G : Type) [Group G] [Countable G] (Γ : Subgroup G),
  (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : Γ →* E ≃ₗᵢ[ℂ] E) (c : Γ → E), (∀ g h, c (g*h) = c g + ρ g (c h)) →
    ∃ v : E, ∀ g, c g = ρ g v - v) →
  ∀ t : G, (∀ g ∈ Γ, t*g*t⁻¹ ∈ Γ) →
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : G →* E ≃ₗᵢ[ℂ] E), (∃ n : ℕ → ℕ, ∃ U : ∀ j, G → Matrix.unitaryGroup (Fin (n j)) ℂ,
    (∀ g h, Tendsto (fun j => opDist (U j (g*h)) (U j g*U j h)) atTop (𝓝 0)) ∧
    ∀ (A : Finset G) (z : G → ℂ) (b : ℝ),
      (∀ᶠ j in atTop, ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
        (∑ g ∈ A, z g • (U j g : Matrix (Fin (n j)) (Fin (n j)) ℂ))‖ ≤ b) →
      ∀ v : E, ‖∑ g ∈ A, z g • ρ g v‖ ≤ b*‖v‖) →
    ∀ v : E, (∀ g ∈ Γ, ρ (t*g*t⁻¹) v = v) → ∀ g ∈ Γ, ρ g v = v

theorem main : H1 → H2 → H3 → type_of% @Green100.green_100.variants.operator_norm := by
  classical
  intro witness weighted projection all
  obtain ⟨G,gi,ct,Γ,fg,fh,t,contract,γ,hγ,miss⟩ := witness
  let X := G ⧸ Γ
  have : Countable X := Function.Surjective.countable (QuotientGroup.mk_surjective (s := Γ))
  let x : X := QuotientGroup.mk t
  have fixes (g : G) (hg : g ∈ Γ) : (t*g*t⁻¹) • x = x := by
    change (QuotientGroup.mk ((t*g*t⁻¹)*t) : X) = QuotientGroup.mk t
    rw [mul_assoc (t*g),inv_mul_cancel,mul_one]
    exact QuotientGroup.mk_mul_of_mem _ hg
  have moved : γ • x ≠ x := by
    intro e
    change (QuotientGroup.mk (γ*t) : X) = QuotientGroup.mk t at e
    have hh := QuotientGroup.eq.mp e.symm
    exact miss (by simpa [mul_assoc] using hh)
  obtain ⟨W,wg,wc,r,a,sq,comm,act,distinct⟩ := lampGroup G X
  obtain ⟨d,φ,one,mul,sep⟩ := sequences W (all W)
  obtain ⟨E,ng,ip,cp,ρ,c,coc,zero,⟨g,hg⟩,models⟩ := weighted G Γ fg X x ⟨γ,hγ⟩ W r a sq comm act d φ one mul
    (sep _ (distinct _ _ moved))
  obtain ⟨v,hv⟩ := fh E (ρ.comp Γ.subtype) c coc
  have fixed (s : G) (hs : s ∈ Γ) : ρ (t*s*t⁻¹) v = v := by
    let h : Γ := ⟨_,contract _ hs⟩
    exact sub_eq_zero.mp ((hv h).symm.trans (zero h (fixes _ hs)))
  have hh := projection G Γ fh t contract E ρ models v fixed g g.property
  exact hg ((hv g).trans (sub_eq_zero.mpr hh))


end OMA.R_Green100_green_100_variants_operator_norm_R1
