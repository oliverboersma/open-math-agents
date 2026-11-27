import OMAReductions.R_Erdos1162_erdos_1162_variants_pyber_R1
import Mathlib

-- Step Erdos1162.erdos_1162.variants.pyber.R1.H1: hypothesis H1 of reduction
-- Erdos1162.erdos_1162.variants.pyber.R1
-- Credit: @ivillar

/-!
With `a = ⌊⌊n/2⌋/2⌋` and `b = ⌊n/2⌋ - a`, the group `V = (ℤ/2)^(a+b)` acts faithfully on
`(Fin a ⊕ Fin b) × ℤ/2` by translations in the second factor, and this set (of size `2(a+b) ≤ n`)
embeds in `Fin n`; so `V` embeds in `S_n`. The graphs of the `2^(a b)` matrices `M : 𝔽₂^(b × a)`
are pairwise distinct subgroups of `V`, and an injective homomorphism maps distinct subgroups to
distinct subgroups.
-/

namespace OMA.Erdos1162LowerBoundH1

open Equiv

/-- The graph of `M : 𝔽₂^a → 𝔽₂^b` inside `𝔽₂^(a ⊕ b)`. -/
def graph (a b : ℕ) (M : Fin b → Fin a → ZMod 2) : AddSubgroup (Fin a ⊕ Fin b → ZMod 2) where
  carrier := {v | ∀ j, v (Sum.inr j) = ∑ i, M j i * v (Sum.inl i)}
  add_mem' := by
    intro v w hv hw j
    simp only [Set.mem_ofPred_eq] at hv hw ⊢
    rw [Pi.add_apply, hv j, hw j, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.add_apply, mul_add]
  zero_mem' := by
    intro j
    simp
  neg_mem' := by
    intro v hv j
    simp only [Set.mem_ofPred_eq] at hv
    rw [Pi.neg_apply, hv j, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.neg_apply, mul_neg]

lemma graph_injective (a b : ℕ) : Function.Injective (graph a b) := by
  intro M M' h
  funext j i
  let e : Fin a ⊕ Fin b → ZMod 2 := fun s => match s with
    | Sum.inl i' => if i' = i then 1 else 0
    | Sum.inr j' => M j' i
  have he : e ∈ graph a b M := by
    intro j'
    simp [e]
  rw [h] at he
  have h2 := he j
  simpa [e] using h2

/-- Translation of the second coordinate. -/
def shift {ι : Type*} (c : ι → ZMod 2) : Perm (ι × ZMod 2) where
  toFun p := (p.1, c p.1 + p.2)
  invFun p := (p.1, p.2 - c p.1)
  left_inv p := by simp
  right_inv p := by simp

def T (ι : Type*) : Multiplicative (ι → ZMod 2) →* Perm (ι × ZMod 2) where
  toFun c := shift (Multiplicative.toAdd c)
  map_one' := Equiv.ext fun p => by simp [shift]
  map_mul' c d := Equiv.ext fun p => by simp [shift, Perm.mul_apply, add_assoc]

lemma T_injective (ι : Type*) : Function.Injective (T ι) := by
  rw [injective_iff_map_eq_one]
  intro c hc
  apply Multiplicative.toAdd.injective
  funext i
  have h2 := congrArg (fun f : Perm (ι × ZMod 2) => (f (i, 0)).2) hc
  simpa [T, shift] using h2

end OMA.Erdos1162LowerBoundH1

open Equiv OMA.Erdos1162LowerBoundH1 in
theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_pyber_R1.H1 := by
  unfold OMA.R_Erdos1162_erdos_1162_variants_pyber_R1.H1
  intro n
  have hcard : Fintype.card ((Fin (n / 2 / 2) ⊕ Fin (n / 2 - n / 2 / 2)) × ZMod 2) ≤
      Fintype.card (Fin n) := by
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, ZMod.card]
    omega
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  let F : (Fin (n / 2 - n / 2 / 2) → Fin (n / 2 / 2) → ZMod 2) → Subgroup (Perm (Fin n)) :=
    fun M => ((AddSubgroup.toSubgroup (graph _ _ M)).map (T _)).map (Perm.viaEmbeddingHom ι)
  have hF : Function.Injective F := by
    intro M M' h
    apply graph_injective
    apply AddSubgroup.toSubgroup.injective
    apply Subgroup.map_injective (T_injective _)
    exact Subgroup.map_injective (Perm.viaEmbeddingHom_injective ι) h
  have : Finite (Subgroup (Perm (Fin n))) :=
    Finite.of_injective (fun H : Subgroup (Perm (Fin n)) => (H : Set (Perm (Fin n))))
      SetLike.coe_injective
  have hle := Nat.card_le_card_of_injective F hF
  unfold Erdos1162.f
  calc 2 ^ ((n / 2 / 2) * (n / 2 - n / 2 / 2))
        = Nat.card (Fin (n / 2 - n / 2 / 2) → Fin (n / 2 / 2) → ZMod 2) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fun, ZMod.card,
            Fintype.card_fin, Fintype.card_fin, ← pow_mul]
    _ ≤ _ := hle
