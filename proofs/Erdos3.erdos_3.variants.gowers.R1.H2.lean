import OMAReductions.R_Erdos3_erdos_3_variants_gowers_R1
import Mathlib

open Erdos3 Finset Set

theorem OMA.solution : OMA.R_Erdos3_erdos_3_variants_gowers_R1.H2 := by
  classical
  intro k l N hk hkl
  refine csSup_le' ?_
  rintro q ⟨S,hS,hf,rfl⟩
  change _ ≤ sSup _
  apply le_csSup
  · refine ⟨(Finset.Icc 1 N).card,?_⟩
    rintro v ⟨T,hT,_,rfl⟩
    exact Finset.card_le_card hT
  refine ⟨S,hS,?_,rfl⟩
  rintro T hTS ⟨a,d,ht,he⟩
  have hd : d ≠ 0 := by
    intro h
    have hsub : T ⊆ ({a} : Set ℕ) := by
      rw [he]
      rintro _ ⟨i,_,rfl⟩
      simp [h]
    have cap := Set.encard_mono hsub
    change T.encard = l at ht
    rw [ht,Set.encard_singleton] at cap
    have : l ≤ 1 := by exact_mod_cast cap
    omega
  let U := (Finset.range k).image (fun i ↦ a+i*d)
  have hinj : Function.Injective (fun i : ℕ ↦ a+i*d) := by
    intro i j heq
    exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd)) (Nat.add_left_cancel heq)
  have hU : (U : Set ℕ) ⊆ T := by
    rw [he]
    intro x hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    have hil := (Finset.mem_range.mp hi).trans_le hkl
    exact ⟨i,by exact_mod_cast hil,by simp⟩
  have hap : (U : Set ℕ).IsAPOfLength k := by
    refine ⟨a,d,?_,?_⟩
    · change (U : Set ℕ).encard = k
      rw [Set.encard_coe_eq_coe_finsetCard,show U.card = k by
        dsimp [U]; rw [Finset.card_image_of_injective _ hinj,Finset.card_range]]
    · ext x
      simp [U]
  have impossible := hf _ (hU.trans hTS) hap
  have : k ≤ 1 := by exact_mod_cast impossible
  omega
