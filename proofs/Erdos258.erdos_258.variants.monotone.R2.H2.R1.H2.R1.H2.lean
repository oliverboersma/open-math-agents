import OMAReductions.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2_R1
import Mathlib

-- Step Erdos258.erdos_258.variants.monotone.R2.H2.R1.H2.R1.H2: hypothesis H2 of reduction
-- Erdos258.erdos_258.variants.monotone.R2.H2.R1.H2.R1
-- Credit: @ivillar

/-!
Divisor hyperbola: `d(n) ≤ 2 #{a ∣ n : a² ≤ n}`, so
`∑_{n ≤ X, n ≡ r (A)} d(n) ≤ 2 ∑_{a ≤ √X} #{n ≤ X : a ∣ n, n ≡ r (A)}`. A divisor `a` of such an
`n` is coprime to `A` (as `gcd(n, A) = gcd(r, A) = 1`), so these `n` are congruent modulo `a A`
and there are at most `X / (a A) + 1` of them. Summing, `∑_{a ≤ √X} (X/(aA) + 1) ≤
(X / A)(1 + log X) + √X` by `harmonic_le_one_add_log`.
-/

namespace OMA.Erdos258DivisorSum

open Finset

lemma card_divisors_le_two_mul (n : ℕ) (hn : 0 < n) :
    n.divisors.card ≤ 2 * (n.divisors.filter (fun a => a * a ≤ n)).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := n.divisors)
    (p := fun a => a * a ≤ n)
  have hle : (n.divisors.filter (fun a => ¬ a * a ≤ n)).card ≤
      (n.divisors.filter (fun a => a * a ≤ n)).card := by
    apply Finset.card_le_card_of_injOn (fun a => n / a)
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at ha ⊢
      obtain ⟨⟨had, hn0⟩, hlt⟩ := ha
      refine ⟨⟨Nat.div_dvd_of_dvd had, hn0⟩, ?_⟩
      have h1 : a * (n / a) = n := Nat.mul_div_cancel' had
      have h2 : n / a < a := Nat.lt_of_mul_lt_mul_left (by rw [h1]; omega)
      calc n / a * (n / a) ≤ n / a * a := Nat.mul_le_mul_left _ h2.le
        _ = n := by rw [mul_comm]; exact h1
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at ha hb
      have h1 := Nat.div_div_self ha.1.1 hn.ne'
      have h2 := Nat.div_div_self hb.1.1 hn.ne'
      simp only at hab
      rw [← h1, ← h2, hab]
  omega

lemma card_le_of_modEq (X m : ℕ) (T : Finset ℕ) (hT : ∀ x ∈ T, x ≤ X)
    (hc : ∀ x ∈ T, ∀ y ∈ T, x ≡ y [MOD m]) : (T.card : ℝ) ≤ (X : ℝ) / m + 1 := by
  have hinj : Set.InjOn (fun x => x / m) (T : Set ℕ) := by
    intro x hx y hy hxy
    have hmod : x % m = y % m := hc x hx y hy
    simp only at hxy
    rw [← Nat.div_add_mod x m, ← Nat.div_add_mod y m, hxy, hmod]
  have hsub : T.image (fun x => x / m) ⊆ Finset.range (X / m + 1) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hT x hx)))
  have h1 : T.card ≤ X / m + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    exact (Finset.card_le_card hsub).trans (Finset.card_range _).le
  have h2 : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / m := Nat.cast_div_le
  have h3 : (T.card : ℝ) ≤ ((X / m : ℕ) : ℝ) + 1 := by exact_mod_cast h1
  linarith

lemma main_bound (X A r : ℕ) (hA : 1 ≤ A) (hr : Nat.Coprime r A) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ X ∧ n ≡ r [MOD A]) :
    (∑ n ∈ S, (n.divisors.card : ℝ)) ≤ 2 * ((X : ℝ) / A * (1 + Real.log X) + Real.sqrt X) := by
  set K := Nat.sqrt X with hK
  have step1 : ∀ n ∈ S, (n.divisors.card : ℝ) ≤
      2 * (((Icc 1 K).filter (fun a => a ∣ n)).card : ℝ) := by
    intro n hn
    obtain ⟨hn1, hnX, _⟩ := hS n hn
    have h := card_divisors_le_two_mul n hn1
    have hsub : n.divisors.filter (fun a => a * a ≤ n) ⊆ (Icc 1 K).filter (fun a => a ∣ n) := by
      intro a ha
      simp only [Finset.mem_filter, Nat.mem_divisors] at ha
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos ha.1.1 hn1, ?_⟩, ha.1.1⟩
      exact Nat.le_sqrt.mpr (le_trans ha.2 hnX)
    have h2 := Finset.card_le_card hsub
    exact_mod_cast (h.trans (Nat.mul_le_mul_left 2 h2))
  have step2 : (∑ n ∈ S, (((Icc 1 K).filter (fun a => a ∣ n)).card : ℝ)) =
      ∑ a ∈ Icc 1 K, ((S.filter (fun n => a ∣ n)).card : ℝ) := by
    simp only [Finset.card_filter]
    push_cast
    rw [Finset.sum_comm]
  have step3 : ∀ a ∈ Icc 1 K, ((S.filter (fun n => a ∣ n)).card : ℝ) ≤
      (X : ℝ) / A * (1 / (a : ℝ)) + 1 := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hapos : (0 : ℝ) < a := by exact_mod_cast ha1
    have hApos : (0 : ℝ) < A := by exact_mod_cast hA
    have heq : (X : ℝ) / A * (1 / (a : ℝ)) = (X : ℝ) / ((a * A : ℕ) : ℝ) := by
      push_cast
      field_simp
    rw [heq]
    by_cases hne : (S.filter (fun n => a ∣ n)).Nonempty
    · obtain ⟨n0, hn0⟩ := hne
      have hn0S := (Finset.mem_filter.mp hn0).1
      have hcopn : Nat.Coprime n0 A := by
        have h := Nat.ModEq.gcd_eq (hS n0 hn0S).2.2
        unfold Nat.Coprime
        rw [h]
        exact hr
      have hcop : Nat.Coprime a A :=
        Nat.Coprime.coprime_dvd_left (Finset.mem_filter.mp hn0).2 hcopn
      apply card_le_of_modEq X (a * A)
      · intro x hx
        exact (hS x (Finset.mem_filter.mp hx).1).2.1
      · intro x hx y hy
        have hxA := (hS x (Finset.mem_filter.mp hx).1).2.2
        have hyA := (hS y (Finset.mem_filter.mp hy).1).2.2
        have h1 : x ≡ y [MOD A] := hxA.trans hyA.symm
        have h2 : x ≡ y [MOD a] := (Nat.modEq_zero_iff_dvd.mpr (Finset.mem_filter.mp hx).2).trans
          (Nat.modEq_zero_iff_dvd.mpr (Finset.mem_filter.mp hy).2).symm
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, h1⟩
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
      positivity
  have hharm : (∑ a ∈ Icc 1 K, (1 / (a : ℝ))) = (harmonic K : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro a _
    push_cast
    ring
  have hHK : (harmonic K : ℝ) ≤ 1 + Real.log X := by
    refine (harmonic_le_one_add_log K).trans ?_
    have hlogK : Real.log K ≤ Real.log X := by
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]
        exact Real.log_natCast_nonneg X
      · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast Nat.sqrt_le_self X)
    linarith
  have hKs : (K : ℝ) ≤ Real.sqrt X := Real.nat_sqrt_le_real_sqrt
  have hXA : (0 : ℝ) ≤ (X : ℝ) / A := by positivity
  have hsum3 : (∑ a ∈ Icc 1 K, ((S.filter (fun n => a ∣ n)).card : ℝ)) ≤
      (X : ℝ) / A * (harmonic K : ℝ) + K := by
    refine (Finset.sum_le_sum step3).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hharm]
    simp
  calc (∑ n ∈ S, (n.divisors.card : ℝ))
      ≤ ∑ n ∈ S, 2 * (((Icc 1 K).filter (fun a => a ∣ n)).card : ℝ) := Finset.sum_le_sum step1
    _ = 2 * ∑ a ∈ Icc 1 K, ((S.filter (fun n => a ∣ n)).card : ℝ) := by
        rw [← Finset.mul_sum, step2]
    _ ≤ 2 * ((X : ℝ) / A * (harmonic K : ℝ) + K) := by linarith
    _ ≤ 2 * ((X : ℝ) / A * (1 + Real.log X) + Real.sqrt X) := by
        have := mul_le_mul_of_nonneg_left hHK hXA
        linarith

end OMA.Erdos258DivisorSum

theorem OMA.solution : OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2_R1.H2 := by
  unfold OMA.R_Erdos258_erdos_258_variants_monotone_R2_H2_R1_H2_R1.H2
  intro X A r hA hr
  apply OMA.Erdos258DivisorSum.main_bound X A r hA hr
  intro n hn
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
  exact ⟨(Finset.mem_Icc.mp h1).1, (Finset.mem_Icc.mp h1).2, h2⟩
