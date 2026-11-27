import OMAReductions.R_Green100_green_100_variants_operator_norm_R1_H1_R1
import Mathlib

-- Step Green100.green_100.variants.operator_norm.R1.H1.R1.H2: hypothesis H2 of reduction Green100.green_100.variants.operator_norm.R1.H1.R1
-- Credit: @ivillar

/-!
The ascending HNN extension of a proper self-embedding, via Mathlib's `HNNExtension`
(with `A = ⊤`, `B = range φ`) and Britton's lemma.
-/
namespace F2G100

theorem hnn : ∀ (B : Type) [Group B] [Countable B] (φ : B →* B),
    Function.Injective φ → ¬Function.Surjective φ →
    ∃ G : Type, ∃ _ : Group G, ∃ _ : Countable G, ∃ i : B →* G,
    Function.Injective i ∧ ∃ t : G, (∀ x : B, t*i x*t⁻¹ = i (φ x)) ∧
      ∃ x : B, t⁻¹*i x*t ∉ i.range := by
  intro B _ _ φ hinj hns
  let e : (⊤ : Subgroup B) ≃* φ.range := Subgroup.topEquiv.trans (MonoidHom.ofInjective hinj)
  have he : ∀ x : B, ((e ⟨x, Subgroup.mem_top x⟩ : φ.range) : B) = φ x := fun x => rfl
  have hc : Countable (HNNExtension B ⊤ φ.range e) := by
    obtain ⟨d⟩ := HNNExtension.NormalWord.TransversalPair.nonempty B ⊤ φ.range
    have hinj' : Function.Injective
        (fun w : HNNExtension.NormalWord d => (w.head, w.toList)) := by
      intro w w' h
      simp only [Prod.mk.injEq] at h
      exact HNNExtension.NormalWord.ext h.1 h.2
    have : Countable (HNNExtension.NormalWord d) := hinj'.countable
    exact (HNNExtension.NormalWord.equiv e d).injective.countable
  refine ⟨HNNExtension B ⊤ φ.range e, inferInstance, hc, HNNExtension.of,
    HNNExtension.of_injective e, HNNExtension.t, ?_, ?_⟩
  · intro x
    have h := HNNExtension.t_mul_of (φ := e) ⟨x, Subgroup.mem_top x⟩
    rw [he] at h
    rw [h]
    simp
  · obtain ⟨x, hx⟩ := not_forall.mp hns
    have hx' : x ∉ φ.range := fun hm => hx (MonoidHom.mem_range.mp hm)
    refine ⟨x, fun hmem => ?_⟩
    let w : HNNExtension.NormalWord.ReducedWord B ⊤ φ.range :=
      { head := 1
        toList := [((-1 : ℤˣ), x), (1, 1)]
        chain := List.isChain_pair.mpr (fun hm => (hx' (by simpa using hm)).elim) }
    have hw : w.prod e = (HNNExtension.t)⁻¹ * HNNExtension.of x * HNNExtension.t := by
      simp [HNNExtension.NormalWord.ReducedWord.prod, w, mul_assoc]
    have hnil := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range e w (by rw [hw]; exact hmem)
    simp [w] at hnil

end F2G100

theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1.H2 :=
  F2G100.hnn
