import FormalConjectures.Wikipedia.AlspachConjecture
import Mathlib

/-! Reduction of the long-cycles case of Alspach's conjecture
(`AlspachConjecture.alspach_conjecture.variants.long_cycles`, Bryant-Horsley-Pettersson 2014)
to odd `n >= 5` with all cycle lengths equal to `n` (Walecki's Hamilton cycle decomposition
theorem, `H1`) and odd `n >= 5` with at least one prescribed cycle length strictly less than
`n` (`H2`). In `main`, we prove the base cases `n = 1` (empty decomposition) and `n = 3`
(vacuous, since `(3 + 5) / 2 = 4 > 3` forces `m = 0` contradicting `m.sum = 3`) directly. -/

namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1

open SimpleGraph AlspachConjecture

/-- Walecki's theorem (1892) for odd `n >= 5`: `K_n` decomposes into `(n - 1) / 2` Hamilton
cycles. -/
def H1 : Prop :=
  ∀ (n : ℕ), Odd n → 5 ≤ n → ∀ m : Multiset ℕ,
    (∀ x ∈ m, x = n) → m.sum = n.choose 2 →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))),
        IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m

/-- Long-cycle Alspach decomposition for odd `n >= 5` when at least one prescribed cycle length
is strictly less than `n`. -/
def H2 : Prop :=
  ∀ (n : ℕ), Odd n → 5 ≤ n → ∀ m : Multiset ℕ,
    (∀ x ∈ m, (n + 5) / 2 ≤ x ∧ x ≤ n) → (∃ x ∈ m, x < n) → m.sum = n.choose 2 →
      ∃ C : Multiset (Cycle (completeGraph (Fin n))),
        IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m

theorem main : H1 → H2 → type_of% @AlspachConjecture.alspach_conjecture.variants.long_cycles := by
  intro h1 h2 n hn m hm hsum
  rcases hn with ⟨k, rfl⟩
  have hcases : k = 0 ∨ k = 1 ∨ 5 ≤ 2 * k + 1 := by omega
  rcases hcases with rfl | rfl | hge5
  · exact alspach_conjecture.variants.one m (fun x hx => by have := hm x hx; omega) hsum
  · exfalso
    have hm0 : m = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro x hx
      have := hm x hx
      omega
    rw [hm0] at hsum
    norm_num at hsum
  · by_cases hall : ∀ x ∈ m, x = 2 * k + 1
    · exact h1 (2 * k + 1) ⟨k, rfl⟩ hge5 m hall hsum
    · push_neg at hall
      obtain ⟨x, hx, hne⟩ := hall
      have hlt : x < 2 * k + 1 := lt_of_le_of_ne (hm x hx).2 hne
      exact h2 (2 * k + 1) ⟨k, rfl⟩ hge5 m hm ⟨x, hx, hlt⟩ hsum

end OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1
