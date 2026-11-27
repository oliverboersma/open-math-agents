import FormalConjectures.Wikipedia.AlspachConjecture
import Mathlib

/-! Reduction of the even case of Alspach's conjecture (Bryant-Horsley-Pettersson 2014) to
`n >= 4` with all prescribed cycle lengths even (`H1`) and `n >= 4` with at least one odd
prescribed cycle length (`H2`). In `main`, we prove the base cases `n = 0` and `n = 2`
directly by showing `m = 0` and that `K_n \ I` has no edges for any perfect matching `I`. -/

namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R1

open SimpleGraph AlspachConjecture
open Classical

private lemma multiset_eq_zero_of_le_two {m : Multiset ℕ} (hm : ∀ x ∈ m, 3 ≤ x ∧ x ≤ 2) :
    m = 0 := by
  rw [Multiset.eq_zero_iff_forall_notMem]
  intro x hx
  have := hm x hx
  omega

/-- Even Alspach conjecture for even `n >= 4` when all prescribed cycle lengths are even. -/
def H1 : Prop :=
  ∀ (n : ℕ), Even n → 4 ≤ n →
    ∀ (I : (completeGraph (Fin n)).Subgraph), I.IsPerfectMatching →
      ∀ (m : Multiset ℕ), (∀ x ∈ m, 3 ≤ x ∧ x ≤ n) → (∀ x ∈ m, Even x) →
        m.sum = n.choose 2 - n / 2 →
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ I.spanningCoe) C ∧ lengths C = m

/-- Even Alspach conjecture for even `n >= 4` when at least one prescribed cycle length is odd. -/
def H2 : Prop :=
  ∀ (n : ℕ), Even n → 4 ≤ n →
    ∀ (I : (completeGraph (Fin n)).Subgraph), I.IsPerfectMatching →
      ∀ (m : Multiset ℕ), (∀ x ∈ m, 3 ≤ x ∧ x ≤ n) → (∃ x ∈ m, Odd x) →
        m.sum = n.choose 2 - n / 2 →
        ∃ C : Multiset (Cycle (completeGraph (Fin n) \ I.spanningCoe)),
          IsCycleDecomposition (completeGraph (Fin n) \ I.spanningCoe) C ∧ lengths C = m

theorem main : H1 → H2 → type_of% @AlspachConjecture.alspach_conjecture.variants.even := by
  intro h1 h2 n hn I hI m hm hsum
  rcases hn with ⟨k, rfl⟩
  have hcases : k = 0 ∨ k = 1 ∨ 4 ≤ k + k := by omega
  rcases hcases with rfl | rfl | hge4
  · have hm0 : m = 0 := multiset_eq_zero_of_le_two fun x hx => by
      have := hm x hx; omega
    subst hm0
    refine ⟨0, fun e he => ?_, Multiset.map_zero _⟩
    exfalso
    have he' : e ∈ (completeGraph (Fin 0) \ I.spanningCoe).edgeSet := by simpa using he
    induction e using Sym2.ind with
    | _ u _ => exact u.elim0
  · have hm0 : m = 0 := multiset_eq_zero_of_le_two fun x hx => by
      have := hm x hx; omega
    subst hm0
    refine ⟨0, fun e he => ?_, Multiset.map_zero _⟩
    exfalso
    have he' : e ∈ (completeGraph (Fin 2) \ I.spanningCoe).edgeSet := by simpa using he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.sdiff_adj] at he'
      have hne : u ≠ v := he'.1
      obtain ⟨w, hw, _⟩ := hI.1 (hI.2 u)
      have hw_ne : w ≠ u := ((completeGraph (Fin 2)).ne_of_adj (I.adj_sub hw)).symm
      have hwu : w = v := by
        fin_cases u <;> fin_cases v <;> fin_cases w <;> simp_all
      subst hwu
      exact he'.2 hw
  · by_cases hall : ∀ x ∈ m, Even x
    · exact h1 (k + k) ⟨k, rfl⟩ hge4 I hI m hm hall hsum
    · push Not at hall
      obtain ⟨x, hx, hnot⟩ := hall
      exact h2 (k + k) ⟨k, rfl⟩ hge4 I hI m hm ⟨x, hx, Nat.not_even_iff_odd.1 hnot⟩ hsum

end OMA.R_AlspachConjecture_alspach_conjecture_variants_even_R1
