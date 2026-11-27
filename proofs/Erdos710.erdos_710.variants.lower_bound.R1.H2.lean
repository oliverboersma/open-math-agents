import OMAReductions.R_Erdos710_erdos_710_variants_lower_bound_R1
import Mathlib
open Erdos710 Finset

private lemma smooth_obstruction (m y B : ℕ)
    (h : ((Ioc m B).filter (· ∈ Nat.smoothNumbers y)).card <
      ((Icc 1 m).filter (fun d => d ∈ Nat.smoothNumbers y ∧ B < d*y)).card) :
    B ≤ m + f m := by
  by_contra! htop
  have tuple : Erdos711.HasDivisibleDistinctTuple m m (f m) :=
    Nat.sInf_mem (s := {L : ℕ | Erdos711.HasDivisibleDistinctTuple m m L})
      ⟨_,hasDivisibleDistinctTuple_sq m⟩
  obtain ⟨a,ainj,ha⟩ := tuple
  let S := (Icc 1 m).filter (fun d => d ∈ Nat.smoothNumbers y ∧ B < d*y)
  let T := (Ioc m B).filter (· ∈ Nat.smoothNumbers y)
  have info (d : S) : 1 ≤ d.val ∧ d.val ≤ m ∧
      d.val ∈ y.smoothNumbers ∧ B < d.val*y := by
    obtain ⟨hd,hs⟩ := mem_filter.mp d.prop
    exact ⟨(mem_Icc.mp hd).1,(mem_Icc.mp hd).2,hs⟩
  let idx (d : S) : Fin m := ⟨d.val-1,by have := info d; omega⟩
  have val (d : S) : (idx d).val+1 = d.val := by dsimp [idx]; have := info d; omega
  have maps (d : S) : a (idx d) ∈ T := by
    obtain ⟨hl,hu,hd⟩ := ha (idx d)
    rw [val d] at hd
    obtain ⟨q,hq⟩ := hd
    have hqpos : 0 < q := by
      by_contra! hz
      have : q = 0 := by omega
      simp [this] at hq
      omega
    have low : d.val*q < d.val*y := by linarith only [hq,hu,htop,(info d).2.2.2]
    have small : q < y := Nat.lt_of_mul_lt_mul_left low
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hl,by omega⟩,
      hq ▸ Nat.mul_mem_smoothNumbers (info d).2.2.1 (Nat.mem_smoothNumbers_of_lt hqpos small)⟩
  let g (d:S) : T := ⟨a (idx d), maps d⟩
  have gi : Function.Injective g := by
    intro p q eq
    have hi : idx p = idx q := ainj (congrArg Subtype.val eq)
    apply Subtype.ext
    rw [← val p, ← val q, hi]
  have card := Fintype.card_le_of_injective g gi
  have le : S.card ≤ T.card := by simpa only [Fintype.card_coe] using card
  exact (not_lt_of_ge le) h

theorem OMA.solution : OMA.R_Erdos710_erdos_710_variants_lower_bound_R1.H2 := smooth_obstruction
