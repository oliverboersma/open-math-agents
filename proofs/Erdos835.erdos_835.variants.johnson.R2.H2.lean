import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2

/-! The complement of the common intersection has exactly p vertices. The
surjective extension-color map from this complement is therefore a bijection. -/
open Finset

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R2.H2 := by
  classical
  intro p _ hp c coverage A B hA hB hAB
  let T := A ∩ B
  have ht : T.card = p-3 := hAB
  let f (x : (Tᶜ : Finset (Fin (2*p-3)))) := c (insert x.val T)
  have onto : Function.Surjective f := by
    intro i
    obtain ⟨v,hv,he⟩ := coverage T ht i
    exact ⟨⟨v, mem_compl.mpr hv⟩,he⟩
  have hc : Fintype.card (↑(Tᶜ : Finset (Fin (2*p-3)))) = Fintype.card (Fin p) := by
    rw [Fintype.card_coe,card_compl,Fintype.card_fin,Fintype.card_fin,ht]
    omega
  let E := Fintype.equivOfCardEq hc.symm
  have inj : Function.Injective (E ∘ f) := Finite.injective_iff_surjective.mpr (E.surjective.comp onto)
  obtain ⟨a,ha,ea⟩ := exists_eq_insert_iff.mpr (show T ⊆ A ∧ T.card+1=A.card from ⟨inter_subset_left,by omega⟩)
  obtain ⟨b,hb,eb⟩ := exists_eq_insert_iff.mpr (show T ⊆ B ∧ T.card+1=B.card from ⟨inter_subset_right,by omega⟩)
  intro h
  let a' : (Tᶜ : Finset (Fin (2*p-3))) := ⟨a,mem_compl.mpr ha⟩
  let b' : (Tᶜ : Finset (Fin (2*p-3))) := ⟨b,mem_compl.mpr hb⟩
  have eq : f a' = f b' := by change c (insert a T) = c (insert b T); rwa [ea,eb]
  have hab : a=b := congrArg Subtype.val (inj (congrArg E eq))
  have eAB : A=B := by rw [← ea, ← eb, hab]
  rw [← eAB,inter_self,hA] at hAB
  omega
