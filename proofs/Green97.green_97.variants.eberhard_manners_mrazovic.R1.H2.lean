import OMAReductions.R_Green97_green_97_variants_eberhard_manners_mrazovic_R1

-- Step Green97.green_97.variants.eberhard_manners_mrazovic.R1.H2
-- Credit: @caa1982

open Green97

theorem OMA.solution : OMA.R_Green97_green_97_variants_eberhard_manners_mrazovic_R1.H2 := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  unfold numAdditiveTriples
  let e : {π : (Fin n ≃ ZMod n) × (Fin n ≃ ZMod n) //
      Function.Bijective fun i ↦ π.1 i + π.2 i} ≃
      (Fin n ≃ ZMod n) × {σ : Equiv.Perm (ZMod n) //
        Function.Bijective fun x ↦ x + σ x} :=
    { toFun := fun ⟨⟨π₁, π₂⟩, h⟩ =>
        (π₁, ⟨π₁.symm.trans π₂, by
          have hcomp : (fun x : ZMod n => x + (π₁.symm.trans π₂) x) =
              (fun i : Fin n => π₁ i + π₂ i) ∘ π₁.symm := by
            ext x
            simp [Equiv.trans_apply]
          rw [hcomp]
          exact h.comp π₁.symm.bijective⟩)
      invFun := fun ⟨π₁, ⟨σ, h⟩⟩ =>
        ⟨(π₁, π₁.trans σ), by
          have hcomp : (fun i : Fin n => π₁ i + (π₁.trans σ) i) =
              (fun x : ZMod n => x + σ x) ∘ π₁ := by
            ext i
            simp [Equiv.trans_apply]
          rw [hcomp]
          exact h.comp π₁.bijective⟩
      left_inv := fun ⟨⟨π₁, π₂⟩, _⟩ => by
        ext i <;> simp
      right_inv := fun ⟨π₁, ⟨σ, _⟩⟩ => by
        ext x <;> simp }
  rw [Nat.card_congr e, Nat.card_prod]
  congr 1
  rw [Nat.card_eq_fintype_card,
    Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin n)) (ZMod.finEquiv n).toEquiv.symm),
    Fintype.card_perm, Fintype.card_fin]
