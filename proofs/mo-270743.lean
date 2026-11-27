import OMAStatements.S_mo_270743
import Mathlib

namespace MO270743
open Finset Matrix OMA.S_mo_270743

lemma topk {n : ℕ} (d : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∃ S : Finset (Fin n), S.card = k ∧ (∀ i ∈ S, ∀ j ∉ S, d j ≤ d i) ∧
      ∀ T : Finset (Fin n), T.card = k → ∑ i ∈ T, d i ≤ ∑ i ∈ S, d i := by
  have hne : (Finset.powersetCard k (Finset.univ : Finset (Fin n))).Nonempty := by
    rw [Finset.powersetCard_nonempty]
    simpa using hk
  obtain ⟨S, hS, hmax⟩ :=
    Finset.exists_max_image _ (fun S : Finset (Fin n) => ∑ i ∈ S, d i) hne
  rw [Finset.mem_powersetCard] at hS
  refine ⟨S, hS.2, ?_, ?_⟩
  · intro i hi j hj
    by_contra hlt
    have hlt' : d i < d j := lt_of_not_ge hlt
    have hjS : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
    have hcard : (insert j (S.erase i)).card = k := by
      rw [Finset.card_insert_of_notMem hjS, Finset.card_erase_of_mem hi, hS.2]
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
      omega
    have hmem : insert j (S.erase i) ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)) := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hcard⟩
    have h1 : ∑ x ∈ insert j (S.erase i), d x ≤ ∑ x ∈ S, d x := hmax _ hmem
    rw [Finset.sum_insert hjS] at h1
    have h2 : d i + ∑ x ∈ S.erase i, d x = ∑ x ∈ S, d x := Finset.add_sum_erase S d hi
    linarith
  · intro T hT
    have hmem : T ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)) := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hT⟩
    exact hmax T hmem

lemma row_eq {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (S : Finset (Fin n)) (i : Fin n) :
    rowEnergy (A - retain A S) i = if i ∈ S then 0 else rowEnergy A i := by
  unfold rowEnergy retain
  by_cases h : i ∈ S
  · simp [h]
  · simp [h]

lemma frob_eq {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (S : Finset (Fin n)) :
    squaredFrobenius (A - retain A S) = (∑ i, rowEnergy A i) - ∑ i ∈ S, rowEnergy A i := by
  unfold squaredFrobenius
  have h1 := Finset.sum_sdiff (Finset.subset_univ S)
    (f := fun i => rowEnergy (A - retain A S) i)
  have h2 := Finset.sum_sdiff (Finset.subset_univ S) (f := fun i => rowEnergy A i)
  have h3 : ∑ i ∈ S, rowEnergy (A - retain A S) i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [row_eq, if_pos hi]
  have h4 : ∑ i ∈ Finset.univ \ S, rowEnergy (A - retain A S) i =
      ∑ i ∈ Finset.univ \ S, rowEnergy A i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [row_eq, if_neg (Finset.mem_sdiff.mp hi).2]
  linarith

end MO270743

theorem OMA.solution : type_of% @OMA.S_mo_270743.main := by
  intro n m s _ hs A
  obtain ⟨S, hcard, htop, hmax⟩ := MO270743.topk (fun i => OMA.S_mo_270743.rowEnergy A i) s hs
  refine ⟨S, hcard, htop, ?_⟩
  intro T hT
  rw [MO270743.frob_eq, MO270743.frob_eq]
  have := hmax T hT
  linarith
