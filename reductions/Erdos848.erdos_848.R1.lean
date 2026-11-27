import FormalConjectures.ErdosProblems.«848»

/-! Port of the finite colouring argument of A. C. Li,
crabsatellite/erdos-848-squarefree-product at 4c367cc6bc5a22641ac15935dd92d1df2236e9d7,
under Apache-2.0. The publication uses the positive closed interval and cuts
the explicit colouring certificate at five million. The pinned range starts
at zero. Beyond the cut, only sets meeting the complements of both candidate
residue classes require the large-range estimate. -/
-- Credit: @marcusbuffett

open Finset Erdos848
namespace OMA.R_Erdos848_erdos_848_R1

def H1 : Prop := ∀ n : ℕ, 1 ≤ n → n ≤ 5000000 → ∃ c : ℕ → ℕ,
  (∀ x ∈ Icc 1 n, ¬ Squarefree (x*x+1) → c x ∈ (Icc 1 n).filter (fun i => i % 25 = 7)) ∧
  ∀ x ∈ Icc 1 n, ¬ Squarefree (x*x+1) → ∀ y ∈ Icc 1 n, ¬ Squarefree (y*y+1) →
    x ≠ y → c x = c y → Squarefree (x*y+1)

def H2 : Prop := ∀ n : ℕ, 5000000 < n → ∀ A : Finset ℕ, A ⊆ Icc 1 n →
  NonSquarefreeProductProp A → (∃ x ∈ A, x % 25 ≠ 7) → (∃ y ∈ A, y % 25 ≠ 18) →
  A.card ≤ ((Icc 1 n).filter (fun i => i % 25 = 7)).card

theorem main : H1 → H2 → type_of% @Erdos848.erdos_848 := by
  intro colourings tail N A hA hv
  have hx0 {x : ℕ} (hx : x ∈ A) : 0 < x := by
    by_contra! hx0
    have he : x = 0 := by omega
    simpa [he] using hv x hx x hx
  have hpos : A ⊆ Icc 1 (N-1) := by
    intro x hx
    exact mem_Icc.mpr ⟨hx0 hx, by have := mem_range.mp (hA hx); omega⟩
  have same : (Icc 1 (N-1)).filter (fun i => i % 25 = 7) = A₇ N := by
    ext x
    simp only [A₇, mem_filter, mem_Icc, mem_range]
    omega
  by_cases small : N-1 ≤ 5000000
  · by_cases nonempty : 1 ≤ N-1
    · obtain ⟨c, hc, hs⟩ := colourings (N-1) nonempty small
      rw [← same]
      apply card_le_card_of_injOn c
      · intro x hx
        exact hc x (hpos hx) (hv x hx x hx)
      · intro x hx y hy heq
        by_contra hne
        exact hv x hx y hy (hs x (hpos hx) (hv x hx x hx) y (hpos hy) (hv y hy y hy) hne heq)
    · have hEmpty : A = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
        have := mem_Icc.mp (hpos hx)
        omega
      simp [hEmpty]
  by_cases h7 : ∃ x ∈ A, x % 25 ≠ 7
  · by_cases h18 : ∃ y ∈ A, y % 25 ≠ 18
    · simpa only [same] using tail (N-1) (by omega) A hpos hv h7 h18
    · apply card_le_card_of_injOn (fun x : ℕ => x-11)
      · intro x hx
        have hr : x % 25 = 18 := by by_contra h; exact h18 ⟨x,hx,h⟩
        have hlt := mem_range.mp (hA hx)
        change x-11 ∈ (range N).filter (fun i => i % 25 = 7)
        exact mem_filter.mpr ⟨mem_range.mpr (by omega), by omega⟩
      · intro x hx y hy heq
        have hr : x % 25 = 18 := by by_contra h; exact h18 ⟨x,hx,h⟩
        have hs : y % 25 = 18 := by by_contra h; exact h18 ⟨y,hy,h⟩
        change x-11 = y-11 at heq
        omega
  · exact card_le_card fun x hx => mem_filter.mpr ⟨hA hx, by by_contra h; exact h7 ⟨x,hx,h⟩⟩

end OMA.R_Erdos848_erdos_848_R1
