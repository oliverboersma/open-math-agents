import OMAReductions.R_Green75_green_75_variants_pinchasi_R1
import Mathlib

-- Step Green75.green_75.variants.pinchasi.R1.H1: hypothesis H1 of reduction Green75.green_75.variants.pinchasi.R1
-- Credit: @ivillar

/-!
# A shear makes the first coordinates distinct without changing any imbalance

The shear `(a, b) ↦ (a + c * b, b)` preserves every cross product, hence every left and right
count. Two distinct points of `X` get the same first coordinate for at most one value of `c`, so
some `c` avoids all of these finitely many values.
-/

namespace Green75ShearStep

open Green75 Finset
open scoped Classical

theorem shear : ∀ X : Finset (ℝ × ℝ), ∃ e : (ℝ × ℝ) ↪ (ℝ × ℝ),
    Set.InjOn Prod.fst (↑(X.map e) : Set (ℝ × ℝ)) ∧
    ∀ p q, imbalance (X.map e) (e p) (e q) = imbalance X p q := by
  intro X
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    ((X ×ˢ X).image (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => (pq.2.1 - pq.1.1) / (pq.1.2 - pq.2.2)))
  have hinj : Function.Injective (fun x : ℝ × ℝ => (x.1 + c * x.2, x.2)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    refine Prod.ext ?_ h2
    rw [h2] at h1
    linarith
  have hcross : ∀ p q x : ℝ × ℝ,
      cross (p.1 + c * p.2, p.2) (q.1 + c * q.2, q.2) (x.1 + c * x.2, x.2) = cross p q x := by
    intro p q x
    simp only [cross]
    ring
  refine ⟨⟨fun x => (x.1 + c * x.2, x.2), hinj⟩, ?_, ?_⟩
  · intro a ha b hb hab
    rw [coe_map, Set.mem_image] at ha hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    simp only [Function.Embedding.coeFn_mk] at hab ⊢
    by_cases h2 : p.2 = q.2
    · have h1 : p.1 = q.1 := by
        rw [h2] at hab
        linarith
      rw [Prod.ext h1 h2]
    · exfalso
      apply hc
      rw [mem_image]
      refine ⟨(p, q), mem_product.mpr ⟨by exact_mod_cast hp, by exact_mod_cast hq⟩, ?_⟩
      have hne : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr h2
      rw [div_eq_iff hne]
      linarith
  · intro p q
    unfold imbalance leftCount rightCount
    rw [filter_map, filter_map, card_map, card_map]
    simp only [Function.comp_def, Function.Embedding.coeFn_mk, hcross]

end Green75ShearStep

theorem OMA.solution : OMA.R_Green75_green_75_variants_pinchasi_R1.H1 :=
  Green75ShearStep.shear
