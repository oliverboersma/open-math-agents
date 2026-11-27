import Mathlib

/-!
# Permutation counts in OEIS A001764

Source: https://oeis.org/A001764 (OEIS Foundation, CC BY-SA 4.0).
Credit: @jared-jasinski.

David Callan's count is indexed by `n ≥ 1`, since a permutation of length one
has no final ascent. For Alexander Burstein's count, the size is `n + 1`,
starting with the unique sum-indecomposable permutation of length one.
-/

namespace OMA.S_oeis_a001764

def Avoids {n k : ℕ} (σ : Equiv.Perm (Fin n)) (pattern : Fin k → ℕ) : Prop :=
  ¬ ∃ positions : Fin k → Fin n, StrictMono positions ∧
    ∀ i j, σ (positions i) < σ (positions j) ↔ pattern i < pattern j

def EndsWithAscent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : Prop :=
  ∃ i : Fin (n + 1), i.val + 1 = n ∧ σ i < σ (Fin.last n)

def SumIndecomposable {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ¬ ∃ k : ℕ, 0 < k ∧ k < n ∧ ∀ i : Fin n, i.val < k → (σ i).val < k

def a (n : ℕ) : ℕ := (3 * n).choose n / (2 * n + 1)

theorem main :
    (∀ n : ℕ, 0 < n →
      Nat.card {σ : Equiv.Perm (Fin (n + 1)) //
        Avoids σ ![4, 2, 3, 1] ∧ Avoids σ ![4, 2, 5, 1, 3] ∧ EndsWithAscent σ} = a n) ∧
    (∀ n : ℕ,
      Nat.card {σ : Equiv.Perm (Fin (n + 1)) //
        Avoids σ ![2, 4, 3, 1] ∧ Avoids σ ![4, 5, 2, 3, 1] ∧ SumIndecomposable σ} = a n) := by
  sorry

end OMA.S_oeis_a001764
