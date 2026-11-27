import FormalConjectures.ErdosProblems.«364»
import Mathlib

/-!
Split the strong gap conjecture into eventual gaps for arithmetic and
non-arithmetic triples, and the absence of three consecutive powerful integers.
A positive exponent can be decreased to cover the finitely many small starts.
-/

open Nat

namespace OMA.R_Erdos364_erdos_364_variants_strong_R1

def H1 : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, ∀ a b c : ℕ, N ≤ a → a < b → b < c →
    a.Powerful → b.Powerful → c.Powerful → a+c ≠ 2*b →
      (a : ℝ)^e < (c : ℝ)-(a : ℝ)

def H2 : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∃ N : ℕ, ∀ a b c : ℕ, N ≤ a → a < b → b < c →
    a.Powerful → b.Powerful → c.Powerful → a+c = 2*b →
      (a : ℝ)^e < (c : ℝ)-(a : ℝ)

def H3 : Prop :=
  ¬ ∃ a : ℕ, a.Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful

section Proof

private theorem infinitely_many_powerful : (Set.ofPred Powerful).Infinite := by
  have hSquare : ∀ n : ℕ, Powerful (n^2) := by
    intro n p hp
    obtain ⟨hPrime,hDvd,_⟩ := mem_primeFactors.mp hp
    change p^2 ∣ n^2
    have hd : p ∣ n := (hPrime.dvd_mul.mp (by simpa [pow_two] using hDvd)).elim id id
    simpa only [pow_two] using mul_dvd_mul hd hd
  apply (Set.infinite_range_of_injective (f := fun n : ℕ => n^2) ?_).mono
  · rintro a ⟨n,rfl⟩
    exact hSquare n
  · intro a b h
    exact (pow_left_inj₀ (Nat.zero_le _) (Nat.zero_le _) (by decide : 2 ≠ 0)).mp h

private theorem below_power_of_two (N : ℕ) : N < 2^(N+1) := by
  induction N with
  | zero => decide
  | succ n ih =>
    rw [pow_succ (2 : ℕ) (n+1)]
    have hPos : 0 < (2 : ℕ)^(n+1) := by positivity
    omega

private theorem small_starts {a N : ℕ} {e : ℝ} (ha : a ≤ N) (he : 0 < e)
    (he' : e ≤ 1/((N : ℝ)+1)) : (a : ℝ)^e ≤ 2 := by
  have hb : (a : ℝ) ≤ (2 : ℝ)^(N+1) := by
    exact_mod_cast (ha.trans (below_power_of_two N).le)
  calc
    (a : ℝ)^e ≤ ((2 : ℝ)^(N+1))^e := Real.rpow_le_rpow (by positivity) hb he.le
    _ = (2 : ℝ)^(((N : ℝ)+1)*e) := by
      rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      push_cast
      rfl
    _ ≤ 2 := by
      have h : ((N : ℝ)+1)*e ≤ 1 := by
        rw [mul_comm]
        exact (le_div_iff₀ (by positivity)).mp he'
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h

theorem all_powerful_triples (h1 : H1) (h2 : H2) (h3 : H3) :
    ∃ e : ℝ, 0 < e ∧ ∀ a b c : ℕ, a < b → b < c →
      a.Powerful → b.Powerful → c.Powerful →
        (a : ℝ)^e < (c : ℝ)-(a : ℝ) := by
  obtain ⟨e1,he1,N1,h1⟩ := h1
  obtain ⟨e2,he2,N2,h2⟩ := h2
  let N := max 1 (max N1 N2)
  let e : ℝ := min (min e1 e2) (1/((N : ℝ)+1))
  have he : 0 < e := lt_min (lt_min he1 he2) (by positivity)
  have hN1 : N1 ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hN2 : N2 ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨e,he,?_⟩
  intro a b c hab hbc ha hb hc
  by_cases hLarge : N ≤ a
  · have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a from (le_max_left _ _).trans hLarge)
    by_cases hAP : a+c = 2*b
    · have hPow : (a : ℝ)^e ≤ (a : ℝ)^e2 := Real.rpow_le_rpow_of_exponent_le ha1
        ((min_le_left _ _).trans (min_le_right _ _))
      exact hPow.trans_lt (h2 a b c (hN2.trans hLarge) hab hbc ha hb hc hAP)
    · have hPow : (a : ℝ)^e ≤ (a : ℝ)^e1 := Real.rpow_le_rpow_of_exponent_le ha1
        ((min_le_left _ _).trans (min_le_left _ _))
      exact hPow.trans_lt (h1 a b c (hN1.trans hLarge) hab hbc ha hb hc hAP)
  · have hSpan : a+2 < c := by
      by_contra! hSmall
      have hB : b = a+1 := by omega
      have hC : c = a+2 := by omega
      exact h3 ⟨a,ha,hB ▸ hb,hC ▸ hc⟩
    have hSpan' : (a : ℝ)+2 < c := by exact_mod_cast hSpan
    exact (small_starts (a := a) (N := N) (by omega) he (min_le_right _ _)).trans_lt (by linarith)

theorem main : H1 → H2 → H3 → type_of% @Erdos364.erdos_364.variants.strong := by
  intro h1 h2 h3
  obtain ⟨e,he,h⟩ := all_powerful_triples h1 h2 h3
  refine ⟨e,he,fun k => ?_⟩
  exact h (nth Powerful k) (nth Powerful (k+1)) (nth Powerful (k+2))
    ((nth_lt_nth infinitely_many_powerful).mpr (by omega))
    ((nth_lt_nth infinitely_many_powerful).mpr (by omega))
    (nth_mem_of_infinite infinitely_many_powerful _)
    (nth_mem_of_infinite infinitely_many_powerful _)
    (nth_mem_of_infinite infinitely_many_powerful _)

end Proof

end OMA.R_Erdos364_erdos_364_variants_strong_R1
