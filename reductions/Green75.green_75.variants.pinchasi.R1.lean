import FormalConjectures.GreensOpenProblems.«75»
import Mathlib

-- Credit: @marcusbuffett
namespace OMA.R_Green75_green_75_variants_pinchasi_R1
open Green75 Finset
open scoped Classical

/-- A shear puts a finite configuration into distinct horizontal coordinates without
changing its oriented side counts. -/
def H1 : Prop :=
  ∀ X : Finset (ℝ × ℝ), ∃ e : (ℝ × ℝ) ↪ (ℝ × ℝ),
    Set.InjOn Prod.fst (↑(X.map e) : Set (ℝ × ℝ)) ∧
    ∀ p q, imbalance (X.map e) (e p) (e q) = imbalance X p q

/-- Pinchasi's crossing-level bound for finite arrangements of lines with distinct slopes.
The line indexed by (a,b) has height b − at. Concurrent lines count on neither side. -/
def H2 : Prop :=
  ∃ C : ℝ, ∀ A : Finset (ℝ × ℝ), 3 ≤ A.card →
    Set.InjOn Prod.fst (↑A : Set (ℝ × ℝ)) →
    ∃ p ∈ A, ∃ q ∈ A, p.1 < q.1 ∧ ∃ t : ℝ, q.2 - t*q.1 = p.2 - t*p.1 ∧
      ((|((A.filter fun x ↦ p.2 - t*p.1 < x.2 - t*x.1).card : ℤ) -
        ((A.filter fun x ↦ x.2 - t*x.1 < p.2 - t*p.1).card : ℤ)| : ℤ) : ℝ)
          ≤ C * Real.log (Real.log A.card)

theorem main : H1 → H2 → type_of% @Green75.green_75.variants.pinchasi := by
  classical
  rintro shear ⟨C,hC⟩
  refine ⟨C,fun X hn ↦ ?_⟩
  obtain ⟨e,hinj,him⟩ := shear X
  let A := X.map e
  obtain ⟨p,hp,q,hq,hpq,t,ht,hl⟩ := hC A (by simpa [A] using hn) hinj
  have hc (x : ℝ × ℝ) : cross p q x = (q.1-p.1) * ((x.2-t*x.1)-(p.2-t*p.1)) := by
    unfold cross
    linear_combination (p.1-x.1)*ht
  have hpos : 0 < q.1-p.1 := sub_pos.mpr hpq
  have hleft : leftCount A p q = (A.filter fun x ↦ p.2-t*p.1 < x.2-t*x.1).card := by
    unfold leftCount
    congr 1
    ext x
    simp [hc, hpos, mul_pos_iff_of_pos_left]
  have hright : rightCount A p q = (A.filter fun x ↦ x.2-t*x.1 < p.2-t*p.1).card := by
    unfold rightCount
    congr 1
    ext x
    simp only [mem_filter,hc]
    apply and_congr_right
    intro _
    exact ⟨fun h ↦ sub_neg.mp (neg_of_mul_neg_right h hpos.le),
      fun h ↦ mul_neg_of_pos_of_neg hpos (sub_neg.mpr h)⟩
  have hbound : (imbalance A p q : ℝ) ≤ C * Real.log (Real.log A.card) := by
    simpa only [imbalance,hleft,hright] using hl
  obtain ⟨p',hp',rfl⟩ := mem_map.mp hp
  obtain ⟨q',hq',rfl⟩ := mem_map.mp hq
  refine ⟨p',hp',q',hq',fun he ↦ hpq.ne (by rw [he]),?_⟩
  simpa only [A,him,card_map] using hbound

end OMA.R_Green75_green_75_variants_pinchasi_R1
