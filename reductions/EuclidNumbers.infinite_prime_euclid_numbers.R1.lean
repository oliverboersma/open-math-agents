import FormalConjectures.Wikipedia.Euclid
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
For each interval of indices, weight the number of hits of each modulus d
by the Möbius function at d times log d. A hit means that the primorial
is minus one modulo d. Interchanging the two finite sums turns the signed
total into minus the von Mangoldt mass of the Euclid numbers in the interval.
Only squarefree moduli coprime to the primorial at the lower endpoint can contribute.
The separate arithmetic step removes all contributions from proper powers.
-/

namespace OMA.R_EuclidNumbers_infinite_prime_euclid_numbers_R1

open Finset EuclidNumbers ArithmeticFunction

/-- An interval beyond every cutoff has a negative signed sum of divisor hits. -/
def H1 : Prop := ∀ L : ℕ, ∃ U : ℕ,
    (∑ d ∈ (range (Euclid U + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d (Euclid L - 1)),
      (ArithmeticFunction.moebius d : ℝ) * Real.log d *
      (((Ico L U).filter fun n => d ∣ Euclid n).card : ℝ)) < 0

/-- A Euclid number cannot be a proper power. -/
def H2 : Prop := ∀ n a k : ℕ, 1 < k → Euclid n ≠ a ^ k

theorem euclid_pos (n : ℕ) : 0 < Euclid n := by
  unfold Euclid
  omega

theorem euclid_mono : Monotone Euclid := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [Euclid, prod_range_succ]
  exact Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.prime_nth_prime n).pos) _

theorem coprime_of_hit {L n d : ℕ} (hL : L ≤ n) (hd : d ∣ Euclid n) :
    Nat.Coprime d (Euclid L - 1) := by
  have hdiv := prod_dvd_prod_of_subset (range L) (range n) (Nat.nth Nat.Prime)
    (range_subset_range.mpr hL)
  have hc := (Nat.coprime_add_iff_left (b := 1) hdiv).mpr (Nat.coprime_one_right _)
  apply Nat.Coprime.of_dvd_left hd
  simpa [Euclid] using hc.symm

theorem divisor_hits (L U : ℕ) :
    (∑ d ∈ (range (Euclid U + 1)).filter (fun d => Squarefree d ∧ Nat.Coprime d (Euclid L - 1)),
      (ArithmeticFunction.moebius d : ℝ) * Real.log d *
      (((Ico L U).filter fun n => d ∣ Euclid n).card : ℝ)) =
    ∑ n ∈ Ico L U, -vonMangoldt (Euclid n) := by
  classical
  let w : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log d
  calc
    _ = ∑ d ∈ range (Euclid U + 1), w d * (((Ico L U).filter fun n => d ∣ Euclid n).card : ℝ) := by
      apply sum_subset (filter_subset _ _)
      intro d hd hex
      by_cases hsq : Squarefree d
      · have hcop : ¬ Nat.Coprime d (Euclid L - 1) := fun hc => hex (mem_filter.mpr ⟨hd, hsq, hc⟩)
        have hempty : ((Ico L U).filter fun n => d ∣ Euclid n) = ∅ := by
          apply filter_eq_empty_iff.mpr
          intro n hn h
          exact hcop (coprime_of_hit (mem_Ico.mp hn).1 h)
        simp [hempty]
      · simp [moebius_eq_zero_of_not_squarefree hsq]
    _ = ∑ d ∈ range (Euclid U + 1), ∑ n ∈ Ico L U, if d ∣ Euclid n then w d else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter]
      simp [w, mul_comm]
    _ = ∑ n ∈ Ico L U, ∑ d ∈ range (Euclid U + 1), if d ∣ Euclid n then w d else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro n hn
      rw [← sum_filter]
      have hs : ((range (Euclid U + 1)).filter fun d => d ∣ Euclid n) = (Euclid n).divisors := by
        ext d
        simp only [mem_filter, mem_range, Nat.mem_divisors]
        have hbound := euclid_mono (mem_Ico.mp hn).2.le
        exact ⟨fun h => ⟨h.2, (euclid_pos n).ne'⟩, fun h =>
          ⟨by have := Nat.le_of_dvd (euclid_pos n) h.1; omega, h.1⟩⟩
      rw [hs]
      exact sum_moebius_mul_log_eq

theorem main : H1 → H2 → type_of% @EuclidNumbers.infinite_prime_euclid_numbers := by
  intro hsieve hpow
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨U, hU⟩ := hsieve (B + 1)
  rw [divisor_hits] at hU
  obtain ⟨n, hn, hneg⟩ : ∃ n ∈ Ico (B + 1) U, -vonMangoldt (Euclid n) < 0 := by
    by_contra! hall
    exact hU.not_ge (Finset.sum_nonneg hall)
  have hpp := vonMangoldt_pos_iff.mp (by linarith : 0 < vonMangoldt (Euclid n))
  obtain ⟨p, k, hp, hk, he⟩ := (isPrimePow_nat_iff _).mp hpp
  have hk1 : k = 1 := by
    by_contra h
    exact hpow n p k (by omega) he.symm
  rw [hk1, pow_one] at he
  exact ⟨n, (show (Euclid n).Prime from he ▸ hp), (mem_Ico.mp hn).1⟩

end OMA.R_EuclidNumbers_infinite_prime_euclid_numbers_R1
