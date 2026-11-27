import Mathlib

/-!
# Rota's Unimodal Conjecture

Source: https://www.openproblemgarden.org/op/rotas_unimodal_conjecture
Credit: @AkiRA-COM-FP

Formalizes Gian-Carlo Rota's 1970 unimodality conjecture: for every finite matroid `M`
of rank `r`, the sequence `w_0, w_1, ..., w_r` of Whitney numbers of the second kind
(where `w_i` is the number of flats of `M` of rank `i`) is unimodal.
-/

namespace OMA.S_opg_rotas_unimodal_conjecture

/-- The `i`-th Whitney number of the second kind of a matroid `M`:
the number of flats (closed sets) of `M` of rank `i`. -/
noncomputable def whitneySecond {α : Type} (M : Matroid α) (i : ℕ) : ℕ :=
  Set.ncard {F : Set α | M.IsFlat F ∧ M.eRk F = (i : ℕ∞)}

/-- A sequence `w_0, w_1, ..., w_r` is unimodal if there exists a peak `k ≤ r` such that
`w` is nondecreasing on `[0, k]` and nonincreasing on `[k, r]`. -/
def IsUnimodal (w : ℕ → ℕ) (r : ℕ) : Prop :=
  ∃ k ≤ r,
    (∀ i j, i ≤ j → j ≤ k → w i ≤ w j) ∧
    (∀ i j, k ≤ i → i ≤ j → j ≤ r → w j ≤ w i)

/-- **Rota's unimodal conjecture**: for every finite matroid `M`, the sequence of Whitney
numbers of the second kind `w_0, w_1, ..., w_r` is unimodal. -/
theorem main :
    ∀ (α : Type) [Fintype α] (M : Matroid α),
      IsUnimodal (whitneySecond M) M.eRank.toNat := by
  sorry

end OMA.S_opg_rotas_unimodal_conjecture
