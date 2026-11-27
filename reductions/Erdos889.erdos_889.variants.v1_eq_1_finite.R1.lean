import FormalConjectures.ErdosProblems.«889»

/-!
Erdős and Selfridge count a prime divisor of n+k exactly when it exceeds k.
If there are two counted primes, their product is at least (k+1)² and divides
n+k. Thus a finite window suffices to determine whether the supremum is one.
Separate the odd values, where the first shift forces n+1 to be a power of
two, from the remaining even values.

Source: Erdős and Selfridge, Some Problems on the Prime Factors of Consecutive
Integers, https://combinatorica.hu/~p_erdos/1967-21.pdf.
-/

open Finset Nat

namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R1

/-- The exact finite window for detecting whether v₁(n) equals one. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → (Erdos889.v_l 1 n = 1 ↔
    ∀ k : ℕ, 1 ≤ k → k ^ 2 < n →
      ((n + k).primeFactors.filter (fun p ↦ k < p)).card ≤ 1)

/-- The odd case reduces to four small values. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n →
    (∀ k : ℕ, 1 ≤ k → k ^ 2 < n →
      ((n + k).primeFactors.filter (fun p ↦ k < p)).card ≤ 1) →
    n ∈ ({1, 3, 7, 15} : Set ℕ)

/-- The remaining finiteness problem for even starting points. -/
def H3 : Prop :=
  Set.Finite {n : ℕ | 0 < n ∧ Even n ∧
    ∀ k : ℕ, 1 ≤ k → k ^ 2 < n →
      ((n + k).primeFactors.filter (fun p ↦ k < p)).card ≤ 1}

section Proof

theorem main : H1 → H2 → H3 → type_of% @Erdos889.erdos_889.variants.v1_eq_1_finite := by
  intro window oddCase evenCase
  have hsmall : ({0, 1, 3, 7, 15} : Set ℕ).Finite := by simp
  refine (hsmall.union evenCase).subset ?_
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Or.inl (by simp)
  have ht := (window n hpos).mp hn
  rcases Nat.even_or_odd n with he | ho
  · exact Or.inr ⟨hpos, he, ht⟩
  · exact Or.inl (Set.mem_insert_of_mem 0 (oddCase n ho ht))

end Proof

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R1
