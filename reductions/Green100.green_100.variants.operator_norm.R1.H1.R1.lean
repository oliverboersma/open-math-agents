import OMAReductions.R_Green100_green_100_variants_operator_norm_R1
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1

/-- The affine lattice in Eckhardt, Example 3.2: the integral special linear
group in dimension three acts on the translation lattice, and the resulting
semidirect product is finitely generated and has the Hilbert fixed point property. -/
def H1 : Prop := ∃ L : Type, ∃ _ : Group L, ∃ _ : Countable L,
  ∃ a : L →* MulAut (Multiplicative (Fin 3 → ℤ)),
  let B := Multiplicative (Fin 3 → ℤ) ⋊[a] L
  Group.FG B ∧ ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : B →* E ≃ₗᵢ[ℂ] E) (c : B → E), (∀ g h, c (g*h) = c g + ρ g (c h)) →
    ∃ v : E, ∀ g, c g = ρ g v - v

/-- Ascending HNN extensions place every proper self-embedding of a
countable group inside a countable group as a contracting conjugation. -/
def H2 : Prop := ∀ (B : Type) [Group B] [Countable B] (φ : B →* B),
  Function.Injective φ → ¬Function.Surjective φ →
  ∃ G : Type, ∃ _ : Group G, ∃ _ : Countable G, ∃ i : B →* G,
  Function.Injective i ∧ ∃ t : G, (∀ x : B, t*i x*t⁻¹ = i (φ x)) ∧
    ∃ x : B, t⁻¹*i x*t ∉ i.range

/-- Doubling the translation coordinates gives a proper self-embedding for
any action on the free abelian lattice of rank three. -/
def H3 : Prop := ∀ (L : Type) [Group L] (a : L →* MulAut (Multiplicative (Fin 3 → ℤ))),
  let B := Multiplicative (Fin 3 → ℤ) ⋊[a] L
  ∃ φ : B →* B, Function.Injective φ ∧ ¬Function.Surjective φ

theorem main : H1 → H2 → H3 → OMA.R_Green100_green_100_variants_operator_norm_R1.H1 := by
  rintro ⟨L,groupL,countL,a,fg,fix⟩ extendGroup dilate
  let B := Multiplicative (Fin 3 → ℤ) ⋊[a] L
  letI : Countable L := countL
  letI : Countable (Multiplicative (Fin 3 → ℤ)) := by change Countable (Fin 3 → ℤ); infer_instance
  letI : Countable B := (SemidirectProduct.equivProd (φ := a)).injective.countable
  obtain ⟨φ,inj,proper⟩ := dilate L a
  obtain ⟨G,_,_,i,inj',t,conj,g,hg⟩ := extendGroup B φ inj proper
  let e : B ≃* i.range := MonoidHom.ofInjective inj'
  letI : Group.FG B := fg
  refine ⟨G,inferInstance,inferInstance,i.range,inferInstance,?_,t,?_,i g,⟨g,rfl⟩,hg⟩
  · intro E _ _ _ ρ c hc
    obtain ⟨v,hv⟩ := fix E (ρ.comp e.toMonoidHom) (fun a ↦ c (e a))
      (fun a b ↦ by simpa only [map_mul,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom] using hc (e a) (e b))
    exact ⟨v, fun a ↦ by simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.apply_symm_apply] using hv (e.symm a)⟩
  · rintro _ ⟨x,rfl⟩
    exact ⟨φ x,(conj x).symm⟩

end OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1

