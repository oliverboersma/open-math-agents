import OMAReductions.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Squarefree

/-!
Separate the rough almost-prime supply from the loss caused by squares of
large primes. This follows the two inputs distinguished by Hildebrand
after Lemma 2 in The divisor function at consecutive integers.

Source: https://msp.org/pjm/1987/129-2/pjm-v129-n2-p06-s.pdf
Credit: @justusklocke-cloud
-/

open Filter Finset Real
open scoped Classical BigOperators

namespace OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1

/-- The rough almost-prime count before imposing squarefreeness. -/
def H1 : Prop :=
  ∀ s c : Fin 7 → ℕ, (∀ i, 0 < s i) →
    (∀ i j, i ≠ j → s i * c j ≠ s j * c i) →
    (∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i, ¬ p ∣ s i * t + c i) →
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ᶠ x : ℝ in atTop,
      ∃ V : Finset ℕ, x / (log x)^7 ≤ C * V.card ∧ ∀ n ∈ V, 0 < n ∧ (n : ℝ) ≤ x ∧
        let v := fun i => s i * n + c i
        (∀ i, 1 < v i ∧ ∀ p ∈ (v i).primeFactors, x ^ δ < (p : ℝ)) ∧
        (∑ i, (v i).primeFactors.card) ≤ 27

/-- A single linear form has negligibly many values with a large square factor. -/
def H2 : Prop :=
  ∀ a b : ℕ, 0 < a → ∀ δ K : ℝ, 0 < δ → 0 < K → ∀ᶠ x : ℝ in atTop,
    K * (((Icc 1 ⌊x⌋₊).filter fun n =>
      ∃ p ∈ (a * n + b).primeFactors, x ^ δ < (p : ℝ) ∧ p ^ 2 ∣ a * n + b).card : ℝ)
      ≤ x / (log x)^7

theorem main : H1 → H2 → OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1.H1 := by
  classical
  intro supply loss s c hs hdistinct hadm B
  obtain ⟨C, δ, hC, hδ, hmany⟩ := supply s c hs hdistinct hadm
  refine ⟨2 * C, by positivity, ?_⟩
  have hE : ∀ᶠ x : ℝ in atTop, ∀ i : Fin 7,
      (14 * C) * (((Icc 1 ⌊x⌋₊).filter fun n =>
        ∃ p ∈ (s i * n + c i).primeFactors, x ^ δ < (p : ℝ) ∧
          p ^ 2 ∣ s i * n + c i).card : ℝ) ≤ x / (log x)^7 :=
    eventually_all.mpr fun i => loss (s i) (c i) (hs i) δ (14 * C) hδ (by positivity)
  have hlarge := (tendsto_rpow_atTop hδ).eventually_ge_atTop (B : ℝ)
  filter_upwards [hmany, hE, hlarge] with x hmany hE hlarge
  obtain ⟨V, hVsize, hV⟩ := hmany
  let E (i : Fin 7) := (Icc 1 ⌊x⌋₊).filter fun n =>
    ∃ p ∈ (s i * n + c i).primeFactors, x ^ δ < (p : ℝ) ∧
      p ^ 2 ∣ s i * n + c i
  let U := V.filter (fun n => ∀ i : Fin 7, Squarefree (s i * n + c i))
  let D := V.filter (fun n => ¬ ∀ i : Fin 7, Squarefree (s i * n + c i))
  have hsub : D ⊆ univ.biUnion E := by
    intro n hn
    obtain ⟨hnV, hnot⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnx, hvalues, _⟩ := hV n hnV
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    rw [Nat.squarefree_iff_prime_squarefree] at hi
    push Not at hi
    obtain ⟨p, hp, hsq⟩ := hi
    have hdvd : p ∣ s i * n + c i := (dvd_mul_right p p).trans hsq
    have hmem : p ∈ (s i * n + c i).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hdvd, (ne_of_gt ((hvalues i).1.trans' Nat.zero_lt_one))⟩
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr
      ⟨mem_Icc.mpr ⟨hnpos, Nat.le_floor hnx⟩,
        p, hmem, (hvalues i).2 p hmem, by simpa only [pow_two] using hsq⟩⟩
  have hsum : D.card ≤ ∑ i, (E i).card := (card_le_card hsub).trans card_biUnion_le
  have hbudget : (14 * C) * (D.card : ℝ) ≤ 7 * (x / (log x)^7) := by
    calc
      _ ≤ (14 * C) * (∑ i, ((E i).card : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact_mod_cast hsum
      _ = ∑ i, (14 * C) * ((E i).card : ℝ) := by rw [mul_sum]
      _ ≤ ∑ _i : Fin 7, x / (log x)^7 := sum_le_sum fun i _ => hE i
      _ = _ := by simp [nsmul_eq_mul]
  have hpartition : U.card + D.card = V.card := card_filter_add_card_filter_not _
  have hpartitionR : (V.card : ℝ) = (U.card : ℝ) + (D.card : ℝ) := by exact_mod_cast hpartition.symm
  refine ⟨U, ?_, ?_⟩
  · rw [hpartitionR, mul_add] at hVsize
    nlinarith only [hVsize, hbudget]
  · intro n hn
    obtain ⟨hnV, hsquare⟩ := mem_filter.mp hn
    obtain ⟨hnpos, hnx, hvalues, hcap⟩ := hV n hnV
    refine ⟨hnpos, hnx, fun i => ⟨(hvalues i).1, hsquare i, ?_⟩, hcap⟩
    intro p hp
    exact_mod_cast hlarge.trans_lt ((hvalues i).2 p hp)

end OMA.R_Erdos946_erdos_946_variants_heathbrown_lower_bound_R1_H1_R1_H1_R1
