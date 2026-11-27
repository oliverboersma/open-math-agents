import OMAReductions.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1

-- Step Erdos32.erdos_32.variants.log_squared.R1.H1.R1.H2: hypothesis H2 of reduction Erdos32.erdos_32.variants.log_squared.R1.H1.R1
-- Credit: @ishaanzee
-- Proof: greedy cover. By averaging some point hits a 1/(CL) fraction of the unhit targets, so
-- CL greedy picks halve them; 8L+1 rounds of halving cover all 2^(8L) targets with at most
-- (8L+1) C L <= 9 C L^2 points.

open Finset

namespace E32Aux

variable (U : Finset ℕ) (R : ℕ → ℕ → Prop) [DecidableRel R]

/-- The targets of `S` not hit by any point of `B`. -/
def unc (S B : Finset ℕ) : Finset ℕ := S.filter (fun n => ∀ a ∈ B, ¬ R n a)

/-- Averaging: some point of `U` hits at least a `1/K` fraction of `S`. -/
lemma greedy_step (K : ℕ) (hU : U.Nonempty) (S : Finset ℕ)
    (hcov : ∀ n ∈ S, U.card ≤ K * (U.filter (R n)).card) :
    ∃ a ∈ U, S.card ≤ K * (S.filter (fun n => R n a)).card := by
  by_contra h
  push_neg at h
  have hsum : ∑ a ∈ U, (S.filter (fun n => R n a)).card = ∑ n ∈ S, (U.filter (R n)).card := by
    have := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := U) (t := S)
      (r := fun a n => R n a)
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow] using this
  have h1 : K * ∑ a ∈ U, (S.filter (fun n => R n a)).card < U.card * S.card := by
    rw [Finset.mul_sum]
    calc ∑ a ∈ U, K * (S.filter (fun n => R n a)).card < ∑ _a ∈ U, S.card :=
          Finset.sum_lt_sum_of_nonempty hU (fun a ha => h a ha)
      _ = U.card * S.card := by rw [sum_const, smul_eq_mul]
  have h2 : U.card * S.card ≤ K * ∑ n ∈ S, (U.filter (R n)).card := by
    rw [Finset.mul_sum]
    calc U.card * S.card = ∑ _n ∈ S, U.card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ S, K * (U.filter (R n)).card := Finset.sum_le_sum hcov
  rw [hsum] at h1
  omega

lemma unc_insert (S B : Finset ℕ) (a : ℕ) :
    unc R S (insert a B) = (unc R S B).filter (fun n => ¬ R n a) := by
  ext n
  simp only [unc, mem_filter, mem_insert, forall_eq_or_imp]
  tauto

/-- `K` greedy picks leave at most half of `S` unhit. -/
lemma halving (K : ℕ) (hK : 1 ≤ K) (hU : U.Nonempty) (S : Finset ℕ)
    (hcov : ∀ n ∈ S, U.card ≤ K * (U.filter (R n)).card) :
    ∃ B ⊆ U, B.card ≤ K ∧ 2 * (unc R S B).card ≤ S.card := by
  have key : ∀ i, ∃ B ⊆ U, B.card ≤ i ∧ (2 * (unc R S B).card ≤ S.card ∨
      i * S.card ≤ 2 * K * (S.card - (unc R S B).card)) := by
    intro i
    induction i with
    | zero => exact ⟨∅, empty_subset _, by simp, Or.inr (by simp)⟩
    | succ i ih =>
      obtain ⟨B, hBU, hBc, hB⟩ := ih
      rcases hB with hB | hB
      · exact ⟨B, hBU, by omega, Or.inl hB⟩
      · by_cases hhalf : 2 * (unc R S B).card ≤ S.card
        · exact ⟨B, hBU, by omega, Or.inl hhalf⟩
        · obtain ⟨a, haU, ha⟩ := greedy_step U R K hU (unc R S B)
            (fun n hn => hcov n (mem_filter.1 hn).1)
          refine ⟨insert a B, insert_subset haU hBU, (card_insert_le _ _).trans (by omega), Or.inr ?_⟩
          rw [unc_insert]
          have hsplit := card_filter_add_card_filter_not (s := unc R S B) (fun n => R n a)
          have hle : (unc R S B).card ≤ S.card := card_le_card (filter_subset _ _)
          have e : S.card - ((unc R S B).filter (fun n => ¬ R n a)).card =
              (S.card - (unc R S B).card) + ((unc R S B).filter (fun n => R n a)).card := by omega
          rw [e, mul_add, show (i + 1) * S.card = i * S.card + S.card by ring]
          push_neg at hhalf
          nlinarith [hB, ha, hhalf]
  obtain ⟨B, hBU, hBc, hB⟩ := key K
  refine ⟨B, hBU, hBc, ?_⟩
  rcases hB with hB | hB
  · exact hB
  · have hle : (unc R S B).card ≤ S.card := card_le_card (filter_subset _ _)
    have : K * S.card ≤ K * (2 * (S.card - (unc R S B).card)) := by nlinarith
    have := Nat.le_of_mul_le_mul_left this (by omega)
    omega

lemma unc_union (S B B' : Finset ℕ) : unc R S (B ∪ B') = unc R (unc R S B) B' := by
  ext n
  simp only [unc, mem_filter, mem_union]
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨⟨hn, fun a ha => h a (Or.inl ha)⟩, fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨⟨hn, h1⟩, h2⟩
    exact ⟨hn, fun a ha => ha.elim (h1 a) (h2 a)⟩

end E32Aux

open E32Aux

theorem OMA.solution : OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1.H2 := by
  unfold OMA.R_Erdos32_erdos_32_variants_log_squared_R1_H1_R1.H2
  intro C hC
  refine ⟨9 * C, fun L U T R _ hL hU hT hcov => ?_⟩
  have hK : 1 ≤ C * L := Nat.one_le_iff_ne_zero.2 (by positivity)
  have iter : ∀ j, ∃ B ⊆ U, B.card ≤ j * (C * L) ∧ 2 ^ j * (unc R T B).card ≤ T.card := by
    intro j
    induction j with
    | zero => exact ⟨∅, empty_subset _, by simp, by simp [unc]⟩
    | succ j ih =>
      obtain ⟨B, hBU, hBc, hB⟩ := ih
      obtain ⟨B', hB'U, hB'c, hB'⟩ := halving U R (C * L) hK hU (unc R T B)
        (fun n hn => hcov n (mem_filter.1 hn).1)
      refine ⟨B ∪ B', union_subset hBU hB'U, (card_union_le _ _).trans (by rw [add_mul, one_mul]; omega), ?_⟩
      rw [unc_union, pow_succ]
      calc 2 ^ j * 2 * (unc R (unc R T B) B').card
          = 2 ^ j * (2 * (unc R (unc R T B) B').card) := by ring
        _ ≤ 2 ^ j * (unc R T B).card := Nat.mul_le_mul_left _ hB'
        _ ≤ T.card := hB
  obtain ⟨B, hBU, hBc, hB⟩ := iter (8 * L + 1)
  have hempty : (unc R T B).card = 0 := by
    by_contra hne
    have h1 : 2 ^ (8 * L + 1) ≤ 2 ^ (8 * L + 1) * (unc R T B).card :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    have h2 : 2 ^ (8 * L) < 2 ^ (8 * L + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine ⟨B, hBU, ?_, ?_⟩
  · calc B.card ≤ (8 * L + 1) * (C * L) := hBc
      _ ≤ 9 * C * L ^ 2 := by nlinarith
  · intro n hn
    by_contra h
    push_neg at h
    have : n ∈ unc R T B := mem_filter.2 ⟨hn, fun a ha => h a ha⟩
    rw [card_eq_zero] at hempty
    rw [hempty] at this
    simp at this
