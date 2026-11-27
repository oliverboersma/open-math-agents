import OMAReductions.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1
import Mathlib

-- Step Erdos297.erdos_297.variants.general.R1.H3.R1.H2.R1.H2: hypothesis H2 of reduction Erdos297.erdos_297.variants.general.R1.H3.R1.H2.R1
-- Credit: @ivillar

/-! Every positive integer `j` is a sum of distinct unit fractions: take the last harmonic number
`H_K < j` (the harmonic series diverges), then expand the remainder `j - H_K < 1 / K` by the
greedy (Fibonacci–Sylvester) algorithm, whose denominators all exceed `K`; the greedy step lowers
the numerator, which drives a strong induction. -/

namespace O2E297
open Finset

lemma greedy : ∀ a : ℕ, ∀ b M : ℕ, 0 < a → 0 < b → 1 ≤ M → (a:ℚ) / b < 1 / M →
    ∃ S : Finset ℕ, (∀ n ∈ S, M < n) ∧ ∑ n ∈ S, (1:ℚ) / n = a / b := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b M ha hb hM hr
  have hbq : (0:ℚ) < b := by exact_mod_cast hb
  have hMq : (0:ℚ) < M := by exact_mod_cast hM
  have hab : a * M < b := by
    rw [div_lt_div_iff₀ hbq hMq, one_mul] at hr
    exact_mod_cast hr
  have hab' : a < b := lt_of_le_of_lt (Nat.le_mul_of_pos_right a hM) hab
  by_cases hdvd : a ∣ b
  · obtain ⟨n, rfl⟩ := hdvd
    refine ⟨{n}, fun x hx => ?_, ?_⟩
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact Nat.lt_of_mul_lt_mul_left hab
    · have hn : 0 < n := Nat.pos_of_mul_pos_left hb
      rw [Finset.sum_singleton]
      push_cast
      field_simp
  · set n := b / a + 1 with hn
    have hdiv := Nat.div_add_mod b a
    have hmodpos : 0 < b % a := Nat.pos_of_ne_zero (fun h => hdvd (Nat.dvd_of_mod_eq_zero h))
    have hmodlt : b % a < a := Nat.mod_lt b ha
    have han : a * n = b + (a - b % a) := by rw [hn, mul_add, mul_one]; omega
    have hMn : M < n := by
      have : a * M < a * n := by omega
      exact Nat.lt_of_mul_lt_mul_left this
    set a' := a - b % a with ha'
    have ha'pos : 0 < a' := by omega
    have ha'lt : a' < a := by omega
    have hnpos : 0 < n := by omega
    have hr' : (a':ℚ) / (b * n : ℕ) < 1 / n := by
      have hnq : (0:ℚ) < n := by exact_mod_cast hnpos
      rw [div_lt_div_iff₀ (by positivity) hnq, one_mul]
      have : a' * n < b * n := Nat.mul_lt_mul_of_pos_right (by omega) hnpos
      exact_mod_cast this
    obtain ⟨S, hS, hsum⟩ := ih a' ha'lt (b * n) n ha'pos (Nat.mul_pos hb hnpos) hnpos hr'
    have hnS : n ∉ S := fun h => lt_irrefl n (hS n h)
    refine ⟨insert n S, fun x hx => ?_, ?_⟩
    · rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hMn
      · exact lt_trans hMn (hS x hx)
    · rw [Finset.sum_insert hnS, hsum]
      have hnq : (0:ℚ) < n := by exact_mod_cast hnpos
      have hcast : (a':ℚ) = (a:ℚ) * n - b := by
        have : (a' : ℤ) = (a:ℤ) * n - b := by rw [ha']; push_cast [Nat.cast_sub hmodlt.le]; omega
        exact_mod_cast this
      rw [hcast]
      push_cast
      field_simp
      ring

theorem main_H2 : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1.H2 := by
  intro j hj
  have hex : ∃ N : ℕ, (j:ℚ) ≤ harmonic N := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, Real.exp j ≤ N := exists_nat_ge _
    refine ⟨N, ?_⟩
    have h1 : (j:ℝ) ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
      rw [Real.le_log_iff_exp_le (by positivity)]; push_cast; linarith
    have h2 := log_add_one_le_harmonic N
    exact_mod_cast h1.trans h2
  classical
  have hN0 : (j:ℚ) ≤ harmonic (Nat.find hex) := Nat.find_spec hex
  have hjq : (0:ℚ) < j := by exact_mod_cast hj
  have hN0pos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · rw [h, harmonic_zero] at hN0; linarith
    · exact h
  obtain ⟨K, hK⟩ : ∃ K, Nat.find hex = K + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hKlt : harmonic K < j := by
    have := Nat.find_min hex (show K < Nat.find hex by omega)
    push Not at this
    exact this
  rw [hK, harmonic_succ] at hN0
  have hIcc : ∀ m : ℕ, ∑ n ∈ Icc 1 m, (1:ℚ) / n = harmonic m := by
    intro m; rw [harmonic_eq_sum_Icc]; simp [one_div]
  by_cases hreq : (j:ℚ) - harmonic K = (↑(K + 1))⁻¹
  · refine ⟨Icc 1 (K + 1), fun n hn => by rw [Finset.mem_Icc] at hn; omega, ?_⟩
    rw [hIcc, harmonic_succ]
    linarith
  · have hrlt : (j:ℚ) - harmonic K < (↑(K + 1))⁻¹ := lt_of_le_of_ne (by linarith) hreq
    have hK1 : 1 ≤ K := by
      rcases Nat.eq_zero_or_pos K with h | h
      · exfalso
        rw [h, harmonic_zero] at hrlt
        have : (1:ℚ) ≤ j := by exact_mod_cast hj
        norm_num at hrlt
        linarith
      · exact h
    set r : ℚ := (j:ℚ) - harmonic K with hr
    have hr0 : 0 < r := by linarith
    have hKq : (0:ℚ) < K := by exact_mod_cast hK1
    have hrK : r < 1 / K := by
      have : (↑(K + 1) : ℚ)⁻¹ ≤ 1 / K := by
        rw [one_div]; apply inv_anti₀ hKq; push_cast; linarith
      linarith
    have hnum : 0 < r.num := Rat.num_pos.mpr hr0
    have hrdef : (r.num.toNat : ℚ) / r.den = r := by
      have : ((r.num.toNat : ℤ) : ℚ) = (r.num : ℚ) := by rw [Int.toNat_of_nonneg hnum.le]
      push_cast at this
      rw [this]
      exact Rat.num_div_den r
    obtain ⟨S, hS, hsum⟩ := greedy r.num.toNat r.den K (by omega) r.den_pos hK1 (by rw [hrdef]; exact hrK)
    have hdisj : Disjoint (Icc 1 K) S := by
      rw [Finset.disjoint_left]
      intro x hx hxS
      rw [Finset.mem_Icc] at hx
      have := hS x hxS
      omega
    refine ⟨Icc 1 K ∪ S, fun n hn => ?_, ?_⟩
    · rw [Finset.mem_union, Finset.mem_Icc] at hn
      rcases hn with hn | hn
      · omega
      · have := hS n hn; omega
    · rw [Finset.sum_union hdisj, hIcc, hsum, hrdef, hr]
      ring

end O2E297

theorem OMA.solution : OMA.R_Erdos297_erdos_297_variants_general_R1_H3_R1_H2_R1.H2 := O2E297.main_H2
