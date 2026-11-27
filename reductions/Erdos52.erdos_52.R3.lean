import FormalConjectures.ErdosProblems.«52»

-- Reduction Erdos52.erdos_52.R3 of Erdős Problem 52
-- Credit: @GiridhariPradeep (agent: Claude Code, model claude-opus-5-5)

/-!
# Erdős 52: reduction to sets of one sign

Every finite set of integers has at least a third of its elements (or at most one element)
of a single sign, and sums and products of a subset lie in those of the whole set. So the
sum-product conjecture follows from its versions for sets of positive integers (`H1`) and
for sets of negative integers (`H2`), at the cost of a constant factor. Solymosi's bound and
most of the literature work with positive sets, so `H1` is the natural form of the core.
-/
namespace OMA.R_Erdos52_erdos_52_R3
open Finset
open scoped Pointwise

/-- The sum-product conjecture for finite sets of positive integers. -/
def H1 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
  (∀ a ∈ A, 0 < a) → (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

/-- The sum-product conjecture for finite sets of negative integers. -/
def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
  (∀ a ∈ A, a < 0) → (max (A + A).card (A * A).card : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

lemma transfer (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1) (C : ℝ) (hC : 0 < C) (A B : Finset ℤ) (hBA : B ⊆ A)
    (hB : (max (B + B).card (B * B).card : ℝ) ≥ C * (B.card : ℝ) ^ (2 - ε))
    (hcard : A.card ≤ 3 * B.card) :
    (max (A + A).card (A * A).card : ℝ) ≥ C / 9 * (A.card : ℝ) ^ (2 - ε) := by
  have h1 : (B + B).card ≤ (A + A).card := card_le_card (add_subset_add hBA hBA)
  have h2 : (B * B).card ≤ (A * A).card := card_le_card (mul_subset_mul hBA hBA)
  have hmax : (max (B + B).card (B * B).card : ℝ) ≤ (max (A + A).card (A * A).card : ℝ) := by
    have : max (B + B).card (B * B).card ≤ max (A + A).card (A * A).card := max_le_max h1 h2
    exact_mod_cast this
  have hpos : (0 : ℝ) ≤ 2 - ε := by linarith
  have hA : (A.card : ℝ) ^ (2 - ε) ≤ ((3 : ℝ) * B.card) ^ (2 - ε) := by
    apply Real.rpow_le_rpow (by positivity) _ hpos
    exact_mod_cast hcard
  have h3 : ((3 : ℝ) * B.card) ^ (2 - ε) = (3 : ℝ) ^ (2 - ε) * (B.card : ℝ) ^ (2 - ε) :=
    Real.mul_rpow (by norm_num) (by positivity)
  have h9 : (3 : ℝ) ^ (2 - ε) ≤ 9 := by
    have : (3 : ℝ) ^ (2 - ε) ≤ (3 : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h32 : (3 : ℝ) ^ (2 : ℝ) = 9 := by norm_num [Real.rpow_two]
    linarith
  have hBpos : (0 : ℝ) ≤ (B.card : ℝ) ^ (2 - ε) := by positivity
  calc C / 9 * (A.card : ℝ) ^ (2 - ε) ≤ C / 9 * (9 * (B.card : ℝ) ^ (2 - ε)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [h3] at hA
        nlinarith
    _ = C * (B.card : ℝ) ^ (2 - ε) := by ring
    _ ≤ _ := le_trans hB hmax

theorem main : H1 → H2 → type_of% @Erdos52.erdos_52 := by
  intro hP hN ε hε hε1
  obtain ⟨C1, hC1, h1⟩ := hP ε hε hε1
  obtain ⟨C2, hC2, h2⟩ := hN ε hε hε1
  refine ⟨min (min C1 C2 / 9) (1 / 4), by positivity, fun A => ?_⟩
  set P := A.filter (fun a => 0 < a) with hPdef
  set N := A.filter (fun a => a < 0) with hNdef
  have hsplit : A ⊆ P ∪ N ∪ {0} := by
    intro a ha
    rcases lt_trichotomy a 0 with h | h | h
    · simp [hPdef, hNdef, ha, h]
    · simp [h]
    · simp [hPdef, hNdef, ha, h]
  have hcardA : A.card ≤ P.card + N.card + 1 := by
    calc A.card ≤ (P ∪ N ∪ {0}).card := card_le_card hsplit
      _ ≤ (P ∪ N).card + ({0} : Finset ℤ).card := card_union_le _ _
      _ ≤ P.card + N.card + 1 := by
        have := card_union_le P N
        simp only [card_singleton]
        omega
  have hPsub : P ⊆ A := filter_subset _ _
  have hNsub : N ⊆ A := filter_subset _ _
  have hPB := h1 P (fun a ha => (mem_filter.mp ha).2)
  have hNB := h2 N (fun a ha => (mem_filter.mp ha).2)
  have hm1 : min (min C1 C2 / 9) (1 / 4) ≤ min C1 C2 / 9 := min_le_left _ _
  have hpos : (0 : ℝ) ≤ (A.card : ℝ) ^ (2 - ε) := by positivity
  by_cases hbig : 1 ≤ P.card ∨ 1 ≤ N.card
  · rcases le_total N.card P.card with hle | hle
    · have hc : A.card ≤ 3 * P.card := by omega
      have := transfer ε hε hε1 C1 hC1 A P hPsub hPB hc
      have hm : min C1 C2 / 9 ≤ C1 / 9 := by
        have := min_le_left C1 C2; linarith
      nlinarith
    · have hc : A.card ≤ 3 * N.card := by omega
      have := transfer ε hε hε1 C2 hC2 A N hNsub hNB hc
      have hm : min C1 C2 / 9 ≤ C2 / 9 := by
        have := min_le_right C1 C2; linarith
      nlinarith
  · simp only [not_or, not_le] at hbig
    have hA1 : A.card ≤ 1 := by omega
    have hm2 : min (min C1 C2 / 9) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hA1 with h0 | h0
    · rw [h0]
      have : (0 : ℝ) ^ (2 - ε) = 0 := Real.zero_rpow (by linarith)
      simp [this]
    · rw [h0]
      have hne : A.Nonempty := card_pos.mp (by omega)
      have hsum : 1 ≤ (A + A).card := card_pos.mpr (hne.add hne)
      have : (1 : ℝ) ≤ (max (A + A).card (A * A).card : ℝ) := by
        have : 1 ≤ max (A + A).card (A * A).card := le_max_of_le_left hsum
        exact_mod_cast this
      simp only [Nat.cast_one, Real.one_rpow, mul_one, ge_iff_le]
      linarith

end OMA.R_Erdos52_erdos_52_R3
