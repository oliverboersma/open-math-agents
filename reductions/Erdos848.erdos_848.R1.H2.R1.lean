import OMAReductions.R_Erdos848_erdos_848_R1
import Mathlib

/-! Choose the least representative of each of the twelve types: residue 7, residue 18,
or neither modulo 25, together with the residue modulo 4. Every member lies in the
common compatibility neighbourhood of these representatives and above its type minimum.
The two estimates use the ranges of MacchaCat's explicit sieve in MacchaCat/erdos848,
99b8d9bf40fdd090a2a117328c5707ca21ec748e, Apache-2.0. -/

namespace OMA.R_Erdos848_erdos_848_R1_H2_R1
open Finset

def H1 : Prop := open scoped Classical in
  ∀ N : ℕ, 5000000 < N → N < 160000000 → ∀ W : Finset ℕ,
    let key := fun x : ℕ => (if x % 25 = 7 then 4 else if x % 25 = 18 then 8 else 0) + x % 4
    W ⊆ Icc 1 N → W.card ≤ 12 → Set.InjOn key (W : Set ℕ) →
    (∀ u ∈ W, ∀ v ∈ W, ¬ Squarefree (u*v+1)) →
    (∃ u ∈ W, u % 25 ≠ 7) → (∃ v ∈ W, v % 25 ≠ 18) →
    ((Icc 1 N).filter fun x =>
      ¬ Squarefree (x*x+1) ∧ (∀ w ∈ W, ¬ Squarefree (x*w+1)) ∧
      ∃ w ∈ W, key w = key x ∧ w ≤ x).card ≤ ((Icc 1 N).filter fun x => x % 25 = 7).card

def H2 : Prop := open scoped Classical in
  ∀ N : ℕ, 160000000 ≤ N → ∀ W : Finset ℕ,
    let key := fun x : ℕ => (if x % 25 = 7 then 4 else if x % 25 = 18 then 8 else 0) + x % 4
    W ⊆ Icc 1 N → W.card ≤ 12 → Set.InjOn key (W : Set ℕ) →
    (∀ u ∈ W, ∀ v ∈ W, ¬ Squarefree (u*v+1)) →
    (∃ u ∈ W, u % 25 ≠ 7) → (∃ v ∈ W, v % 25 ≠ 18) →
    ((Icc 1 N).filter fun x =>
      ¬ Squarefree (x*x+1) ∧ (∀ w ∈ W, ¬ Squarefree (x*w+1)) ∧
      ∃ w ∈ W, key w = key x ∧ w ≤ x).card ≤ ((Icc 1 N).filter fun x => x % 25 = 7).card

theorem main : H1 → H2 → OMA.R_Erdos848_erdos_848_R1.H2 := by
  classical
  intro low high N cutoff A sub adm mixed7 mixed18
  let key := fun x : ℕ => (if x % 25 = 7 then 4 else if x % 25 = 18 then 8 else 0) + x % 4
  let W := A.filter fun x => ∀ y ∈ A, key y = key x → x ≤ y
  have subW : W ⊆ A := filter_subset _ _
  have injW : Set.InjOn key (W : Set ℕ) := by
    intro x hx y hy eq
    exact le_antisymm ((mem_filter.mp hx).2 y (subW hy) eq.symm)
      ((mem_filter.mp hy).2 x (subW hx) eq)
  have rep (x : ℕ) (hx : x ∈ A) : ∃ w ∈ W, key w = key x ∧ w ≤ x := by
    let S := A.filter fun y => key y = key x
    have hxs : x ∈ S := mem_filter.mpr ⟨hx,rfl⟩
    let w := S.min' ⟨x,hxs⟩
    have hw : w ∈ S := min'_mem _ _
    obtain ⟨hwa,hkey⟩ := mem_filter.mp hw
    refine ⟨w,mem_filter.mpr ⟨hwa,?_⟩,hkey,min'_le _ x hxs⟩
    intro y hy heq
    exact min'_le S y (mem_filter.mpr ⟨hy,heq.trans hkey⟩)
  have cardW : W.card ≤ 12 := by
    calc W.card ≤ (range 12).card := by
          apply card_le_card_of_injOn key _ injW
          intro x _
          apply mem_range.mpr
          dsimp [key]
          split_ifs <;> omega
         _ = 12 := card_range _
  have same {x y : ℕ} (eq : key x = key y) :
      (x % 25 = 7 ↔ y % 25 = 7) ∧ (x % 25 = 18 ↔ y % 25 = 18) := by
    dsimp [key] at eq
    split_ifs at eq <;> omega
  have mw7 : ∃ x ∈ W, x % 25 ≠ 7 := by
    obtain ⟨x,hx,hr⟩ := mixed7
    obtain ⟨w,hw,hk,_⟩ := rep x hx
    exact ⟨w,hw,fun h => hr ((same hk).1.mp h)⟩
  have mw18 : ∃ x ∈ W, x % 25 ≠ 18 := by
    obtain ⟨x,hx,hr⟩ := mixed18
    obtain ⟨w,hw,hk,_⟩ := rep x hx
    exact ⟨w,hw,fun h => hr ((same hk).2.mp h)⟩
  have pairs : ∀ u ∈ W, ∀ v ∈ W, ¬ Squarefree (u*v+1) :=
    fun u hu v hv => adm u (subW hu) v (subW hv)
  let C := (Icc 1 N).filter fun x =>
    ¬ Squarefree (x*x+1) ∧ (∀ w ∈ W, ¬ Squarefree (x*w+1)) ∧
    ∃ w ∈ W, key w = key x ∧ w ≤ x
  have bound : A.card ≤ C.card := by
    apply card_le_card
    intro x hx
    exact mem_filter.mpr ⟨sub hx,adm x hx x hx,fun w hw => adm x hx w (subW hw),rep x hx⟩
  apply bound.trans
  by_cases h : N < 160000000
  · exact low N cutoff h W (subW.trans sub) cardW injW pairs mw7 mw18
  · exact high N (by omega) W (subW.trans sub) cardW injW pairs mw7 mw18

end OMA.R_Erdos848_erdos_848_R1_H2_R1

