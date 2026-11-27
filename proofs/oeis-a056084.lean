import OMAStatements.S_oeis_a056084
import Mathlib

/-!
# Proof of OEIS-A056084 conjecture

Credit: @AkiRA-COM-FP
-/

open OMA.S_oeis_a056084

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
private theorem residue_check :
    ∀ r : Fin 729, (r : ℕ) ^ 8 % 729 = 1 ↔ (r : ℕ) = 1 ∨ (r : ℕ) = 728 := by
  decide

private theorem roots (k : ℕ) :
    k ^ 8 % 9 ^ 3 = 1 ↔ k % 729 = 1 ∨ k % 729 = 728 := by
  rw [show (9 : ℕ) ^ 3 = 729 by decide, Nat.pow_mod]
  exact residue_check ⟨k % 729, Nat.mod_lt k (by decide)⟩

private def enumerate (m : ℕ) : ℕ :=
  729 * (m / 2) + if m % 2 = 0 then 1 else 728

private theorem enumerate_strictMono : StrictMono enumerate := by
  apply strictMono_nat_of_lt_succ
  intro m
  unfold enumerate
  split <;> split <;> omega

private theorem enumerate_root (m : ℕ) : enumerate m ^ 8 % 9 ^ 3 = 1 := by
  rw [roots]
  unfold enumerate
  split <;> omega

private theorem exists_enumerate (k : ℕ) (hk : k ^ 8 % 9 ^ 3 = 1) :
    ∃ m, enumerate m = k := by
  rcases (roots k).1 hk with hr | hr
  · refine ⟨2 * (k / 729), ?_⟩
    unfold enumerate
    split <;> omega
  · refine ⟨2 * (k / 729) + 1, ?_⟩
    unfold enumerate
    split <;> omega

private theorem nth_eq_enumerate (m : ℕ) :
    Nat.nth (fun k : ℕ => k ^ 8 % 9 ^ 3 = 1) m = enumerate m := by
  have hrange : Set.range enumerate = Set.ofPred (fun k : ℕ => k ^ 8 % 9 ^ 3 = 1) := by
    ext k
    exact ⟨fun ⟨i, hi⟩ => hi ▸ enumerate_root i, exists_enumerate k⟩
  have hinf : (Set.ofPred (fun k : ℕ => k ^ 8 % 9 ^ 3 = 1)).Infinite := by
    rw [← hrange]
    exact Set.infinite_range_of_injective enumerate_strictMono.injective
  have index_mem (i : ℕ) :
      ∀ hf : (Set.ofPred (fun k : ℕ => k ^ 8 % 9 ^ 3 = 1)).Finite,
        i < hf.toFinset.card :=
    fun hf => (hinf hf).elim
  symm
  refine Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn enumerate ?_ ?_
    (enumerate_strictMono.strictMonoOn _) (index_mem m)
  · intro k hk
    obtain ⟨i, hi⟩ := exists_enumerate k hk
    exact ⟨i, index_mem i, hi⟩
  · exact fun i _ => enumerate_root i

theorem OMA.solution : type_of% @OMA.S_oeis_a056084.main := by
  intro n hn
  rw [a, nth_eq_enumerate]
  by_cases h : (n - 1) % 2 = 0
  · have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    have hnq : (n : ℚ) = 2 * (((n - 1) / 2 : ℕ) : ℚ) + 1 := by
      exact_mod_cast hn'
    have hsign : (-1 : ℚ) ^ n = -1 :=
      (Nat.odd_iff.mpr (by omega : n % 2 = 1)).neg_one_pow
    simp only [enumerate, if_pos h, hsign]
    push_cast
    rw [hnq]
    ring
  · have hn' : n = 2 * ((n - 1) / 2) + 2 := by omega
    have hnq : (n : ℚ) = 2 * (((n - 1) / 2 : ℕ) : ℚ) + 2 := by
      exact_mod_cast hn'
    have hsign : (-1 : ℚ) ^ n = 1 :=
      (Nat.even_iff.mpr (by omega : n % 2 = 0)).neg_one_pow
    simp only [enumerate, if_neg h, hsign]
    push_cast
    rw [hnq]
    ring
