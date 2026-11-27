import OMAReductions.R_OeisA280864_conjecture_R1
import Mathlib.Data.Nat.Prime.Infinite

/-! A fresh prime extends every finite history, so the greedy rule is total. -/

open OeisA280864 Finset
open scoped Classical

namespace CupSequence

private lemma eligible_above (u v B : ℕ) : ∃ a, B < a ∧ Eligible u v a := by
  let R := requiredFactors u v
  let F := forbiddenFactors u v
  let d := ∏ p ∈ R, p
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (max B v + 1)
  have hd : 0 < d := Finset.prod_pos fun p hp =>
    (Nat.mem_primeFactors.mp (mem_sdiff.mp hp).1).1.pos
  have hlarge : B < q := by omega
  have hqle : q ≤ d * q := by
    simpa using Nat.mul_le_mul_right q (show 1 ≤ d by omega)
  refine ⟨d * q, hlarge.trans_le hqle, mul_pos hd hprime.pos, ?_, ?_⟩
  · intro p hp
    exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id hp) q
  · intro p hp
    obtain ⟨hpv, hpu⟩ := mem_inter.mp hp
    have hp' := (Nat.mem_primeFactors.mp hpv).1
    intro h
    rcases hp'.dvd_mul.mp h with h | h
    · have hpp : Prime p := Nat.prime_iff.mp hp'
      obtain ⟨r, hr, hpr⟩ := hpp.exists_mem_finset_dvd h
      have hr' := Nat.mem_primeFactors.mp (mem_sdiff.mp hr).1
      have hpr' := (Nat.dvd_prime hr'.1).mp hpr
      rcases hpr' with h1 | hEq
      · exact hp'.ne_one h1
      · exact (mem_sdiff.mp hr).2 (hEq ▸ hpu)
    · have he := ((Nat.dvd_prime hprime).mp h).resolve_left hp'.ne_one
      have hv : p ≤ v := Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hpv).2.2)
        (Nat.mem_primeFactors.mp hpv).2.1
      omega

private lemma available (n : ℕ) (f : ∀ i, i < n → ℕ) (hn : 2 ≤ n) :
    ∃ a, Eligible (f (n-2) (by omega)) (f (n-1) (by omega)) a ∧
      ∀ i (hi : i < n), f i hi ≠ a := by
  let B := (Finset.univ : Finset (Fin n)).sup (fun i => f i i.isLt)
  obtain ⟨a, ha, hel⟩ := eligible_above (f (n-2) (by omega)) (f (n-1) (by omega)) B
  refine ⟨a, hel, fun i hi => ne_of_lt (lt_of_le_of_lt ?_ ha)⟩
  exact Finset.le_sup (f := fun j : Fin n => f j j.isLt) (mem_univ (⟨i, hi⟩ : Fin n))

private noncomputable def step (n : ℕ) (f : ∀ i, i < n → ℕ) : ℕ :=
  if hn : 2 ≤ n then Nat.find (available n f hn) else if n = 0 then 1 else 2

private noncomputable def sequence (n : ℕ) : ℕ := Nat.strongRecOn n step

private lemma sequence_step (n : ℕ) : sequence n = step n (fun i _ => sequence i) :=
  Nat.strongRecOn_eq step n

theorem total : ∃ a : ℕ → ℕ, FollowsRule a := by
  refine ⟨sequence, ?_, ?_, ?_⟩
  · rw [sequence_step]
    norm_num [step]
  · rw [sequence_step]
    norm_num [step]
  · intro n hn
    let h := available n (fun i _ => sequence i) hn
    have H : sequence n = Nat.find h := by
      rw [sequence_step, step, dif_pos hn]
    unfold GreedyAt UnusedBefore
    rw [H]
    exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2,
      fun a hel hnot => Nat.find_min' h ⟨hel, hnot⟩⟩

end CupSequence

theorem OMA.solution : OMA.R_OeisA280864_conjecture_R1.H1 := CupSequence.total