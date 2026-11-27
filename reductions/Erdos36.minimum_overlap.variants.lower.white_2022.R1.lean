import FormalConjectures.ErdosProblems.«36»
import Mathlib

-- Reduction Erdos36.minimum_overlap.variants.lower.white_2022.R1 of Erdős Problem 36 — white 2022
-- Credit: @ivillar
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
White (arXiv 2201.05704, Theorem 1) proves his bound for the function form of the minimum
overlap problem due to Moser, Murdeshwar and Swinnerton-Dyer: for measurable f from [-1,1] to
[0,1] with integral 1 and g = 1 - f on [-1,1], the overlap integral of f(t) g(x+t) over t is at
least 0.379005 for some x. This is `H1`. The statement about partitions of {1,...,2n} follows
from the elementary half of the Swinnerton-Dyer correspondence, split here into two steps.
`H3`: the step function of a partition (A,B) has overlap function at most 1/n times the
piecewise linear interpolation of the discrete overlap counts, written as a sum of tent
functions over A x B. `H2`: that interpolation never exceeds the maximum overlap.
-/

namespace OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1

open Filter MeasureTheory

/-- White's theorem for the function form of the minimum overlap problem. -/
def H1 : Prop := ∀ f : ℝ → ℝ, Measurable f → (∀ t, 0 ≤ f t ∧ f t ≤ 1) →
  (∫ t in (-1 : ℝ)..1, f t) = 1 →
  ∃ x : ℝ, (0.379005 : ℝ) ≤
    ∫ t in (-1 : ℝ)..1, f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t)

/-- The tent interpolation of the overlap counts is at most the maximum overlap. -/
def H2 : Prop := ∀ (A B : Finset ℤ) (y : ℝ),
  ∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - y|) ≤ (Erdos36.MaxOverlap A B : ℝ)

/-- The step function of a partition has overlap function at most the tent interpolation
divided by n. -/
def H3 : Prop := ∀ (n : ℕ), 0 < n → ∀ A B : Finset ℤ, Disjoint A B →
  A ∪ B = Finset.Icc (1 : ℤ) (2 * n) → A.card = B.card →
  ∃ f : ℝ → ℝ, Measurable f ∧ (∀ t, 0 ≤ f t ∧ f t ≤ 1) ∧ (∫ t in (-1 : ℝ)..1, f t) = 1 ∧
    ∀ x : ℝ,
      (∫ t in (-1 : ℝ)..1, f t * (Set.Icc (-1 : ℝ) 1).indicator (fun y => 1 - f y) (x + t)) ≤
        (∑ p ∈ A ×ˢ B, max 0 (1 - |((p.2 - p.1 : ℤ) : ℝ) - n * x|)) / n

lemma overlap_le_card (A B : Finset ℤ) (k : ℤ) : Erdos36.Overlap A B k ≤ A.card := by
  unfold Erdos36.Overlap
  refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p hp q hq h => ?_)
  · exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · have hp2 := (Finset.mem_filter.mp hp).2
    have hq2 := (Finset.mem_filter.mp hq).2
    exact Prod.ext h (by omega)

lemma maxOverlap_le_card (A B : Finset ℤ) : Erdos36.MaxOverlap A B ≤ A.card :=
  ciSup_le fun k => overlap_le_card A B k

lemma card_left {n : ℕ} {A B : Finset ℤ} (hd : Disjoint A B)
    (hu : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (hc : A.card = B.card) : A.card = n := by
  have h1 : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hd
  rw [hu, Int.card_Icc] at h1
  omega

lemma exists_min (n : ℕ) : ∃ A B : Finset ℤ, Disjoint A B ∧
    A ∪ B = Finset.Icc (1 : ℤ) (2 * n) ∧ A.card = B.card ∧
    Erdos36.MaxOverlap A B = Erdos36.M n := by
  have hne : {x : ℕ | ∃ (A : Finset ℤ) (B : Finset ℤ) (_ : Disjoint A B)
      (_ : A ∪ B = Finset.Icc (1 : ℤ) (2 * n)) (_ : A.card = B.card),
      Erdos36.MaxOverlap A B = x}.Nonempty := by
    refine ⟨_, Finset.Icc 1 n, Finset.Icc (n + 1) (2 * n), ?_, ?_, ?_, rfl⟩
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_Icc] at ha hb
      omega
    · ext a
      simp only [Finset.mem_union, Finset.mem_Icc]
      omega
    · rw [Int.card_Icc, Int.card_Icc]
      omega
  obtain ⟨A, B, hd, hu, hc, hm⟩ := Nat.sInf_mem hne
  exact ⟨A, B, hd, hu, hc, hm⟩

theorem main : H1 → H2 → H3 →
    type_of% @Erdos36.minimum_overlap.variants.lower.white_2022 := by
  intro h1 h2 h3
  have hle : ∀ n : ℕ, Erdos36.MinOverlapQuotient n ≤ 1 := by
    intro n
    obtain ⟨A, B, hd, hu, hc, hm⟩ := exists_min n
    have h4 : Erdos36.M n ≤ n := by
      rw [← hm, ← card_left hd hu hc]
      exact maxOverlap_le_card A B
    unfold Erdos36.MinOverlapQuotient
    have h5 : (Erdos36.M n : ℝ) ≤ n := by exact_mod_cast h4
    exact div_le_one_of_le₀ h5 (Nat.cast_nonneg n)
  have key : ∀ n : ℕ, 1 ≤ n → (0.379005 : ℝ) ≤ Erdos36.MinOverlapQuotient n := by
    intro n hn
    obtain ⟨A, B, hd, hu, hc, hm⟩ := exists_min n
    obtain ⟨f, hfm, hf01, hfint, hfx⟩ := h3 n hn A B hd hu hc
    obtain ⟨x, hx⟩ := h1 f hfm hf01 hfint
    have h6 := hfx x
    have h7 := h2 A B (n * x)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    unfold Erdos36.MinOverlapQuotient
    rw [← hm]
    calc (0.379005 : ℝ) ≤ _ := hx
      _ ≤ _ := h6
      _ ≤ (Erdos36.MaxOverlap A B : ℝ) / n := by gcongr
  exact Filter.le_liminf_of_le (Filter.isCoboundedUnder_ge_of_le _ hle)
    (Filter.eventually_atTop.mpr ⟨1, key⟩)

end OMA.R_Erdos36_minimum_overlap_variants_lower_white_2022_R1
