import OMAReductions.R_Green92_green_92_variants_chase_lower_R1
import Mathlib

-- Step Green92.green_92.variants.chase_lower.R1.H2: hypothesis H2 of reduction
-- Green92.green_92.variants.chase_lower.R1
-- Credit: @ivillar

/-!
Take `m = 10 · 2^n` traces and decode by reading off any trace of full length `n` (a trace has
full length only when no bit was deleted, and then it is `x` itself). Decoding fails only if no
trace is full, which happens for `(2^n - 1)^m` of the `(2^n)^m` deletion patterns, and
`(1 - 2^{-n})^m ≤ exp(-10) ≤ 1/10`.
-/

open Finset Green92

namespace OMA.Green92Lower

theorem trace_univ (n : ℕ) (x : Fin n → Bool) :
    trace x univ = (List.finRange n).map x := by
  unfold trace
  congr 1
  rw [List.filter_eq_self]
  intro a _
  simp

theorem trace_univ_len (n : ℕ) (x : Fin n → Bool) : (trace x univ).length = n := by
  rw [trace_univ, List.length_map, List.length_finRange]

theorem trace_len_lt (n : ℕ) (x : Fin n → Bool) (s : Finset (Fin n)) (hs : s ≠ univ) :
    (trace x s).length < n := by
  unfold trace
  rw [List.length_map]
  obtain ⟨i, hi⟩ : ∃ i, i ∉ s := by
    by_contra h
    push Not at h
    exact hs (eq_univ_iff_forall.mpr h)
  have h1 : (List.filter (fun i => decide (i ∈ s)) (List.finRange n)).length <
      (List.finRange n).length := by
    rw [List.length_filter_lt_length_iff_exists]
    exact ⟨i, List.mem_finRange i, by simpa using hi⟩
  rwa [List.length_finRange] at h1

theorem trace_univ_get (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    (trace x univ).getD i.val false = x i := by
  have hl : i.val < (trace x univ).length := by rw [trace_univ_len]; exact i.2
  rw [List.getD_eq_getElem _ _ hl]
  simp [trace_univ]

end OMA.Green92Lower

open OMA.Green92Lower in
theorem OMA.solution : OMA.R_Green92_green_92_variants_chase_lower_R1.H2 := by
  unfold OMA.R_Green92_green_92_variants_chase_lower_R1.H2
  intro n
  classical
  refine ⟨10 * 2 ^ n, fun o i => if h : ∃ j, (o j).length = n then
    (o (Classical.choose h)).getD i.val false else false, ?_⟩
  intro x
  unfold successProb
  set m := 10 * 2 ^ n with hm
  have hsub : (univ : Finset (Fin m → Finset (Fin n))).filter (fun S => ∃ j, S j = univ) ⊆
      (univ : Finset (Fin m → Finset (Fin n))).filter (fun S =>
        (fun (o : Fin m → List Bool) (i : Fin n) => if h : ∃ j, (o j).length = n then
          (o (Classical.choose h)).getD i.val false else false) (fun j => trace x (S j)) = x) := by
    intro S hS
    obtain ⟨j0, hj0⟩ := (Finset.mem_filter.mp hS).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h : ∃ j, (trace x (S j)).length = n := ⟨j0, by rw [hj0]; exact trace_univ_len n x⟩
    funext i
    simp only [dif_pos h]
    have hj1 := Classical.choose_spec h
    have hfull : S (Classical.choose h) = univ := by
      by_contra hne
      exact absurd hj1 (ne_of_lt (trace_len_lt n x _ hne))
    rw [hfull]
    exact trace_univ_get n x i
  have hbadset : (univ : Finset (Fin m → Finset (Fin n))).filter (fun S => ¬ ∃ j, S j = univ) =
      Fintype.piFinset (fun _ : Fin m => (univ : Finset (Finset (Fin n))).erase univ) := by
    ext S
    simp [Fintype.mem_piFinset]
  have hbadcard : ((univ : Finset (Fin m → Finset (Fin n))).filter
      (fun S => ¬ ∃ j, S j = univ)).card = (2 ^ n - 1) ^ m := by
    rw [hbadset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset,
      Fintype.card_fin]
  have htot : Fintype.card (Fin m → Finset (Fin n)) = (2 ^ n) ^ m := by
    rw [Fintype.card_fun, Fintype.card_finset, Fintype.card_fin, Fintype.card_fin]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m → Finset (Fin n))))
    (p := fun S => ∃ j, S j = univ)
  rw [hbadcard, Finset.card_univ, htot] at hsplit
  have hK : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hKpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hbad : (((2 ^ n - 1 : ℕ) : ℝ)) ^ m ≤ ((2 : ℝ) ^ n) ^ m / 10 := by
    have e1 : ((2 ^ n - 1 : ℕ) : ℝ) = (2 : ℝ) ^ n * (1 - 1 / (2 : ℝ) ^ n) := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
      field_simp
    rw [e1, mul_pow]
    have hnn : 0 ≤ 1 - 1 / (2 : ℝ) ^ n := by
      rw [sub_nonneg, div_le_one hKpos]
      exact hK
    have e2 : (1 - 1 / (2 : ℝ) ^ n) ^ m ≤ Real.exp (-10) := by
      calc (1 - 1 / (2 : ℝ) ^ n) ^ m ≤ (Real.exp (-(1 / (2 : ℝ) ^ n))) ^ m :=
            pow_le_pow_left₀ hnn (Real.one_sub_le_exp_neg _) m
        _ = Real.exp (-10) := by
            rw [← Real.exp_nat_mul]
            congr 1
            rw [hm]
            push_cast
            field_simp
    have e3 : Real.exp (-10) ≤ 1 / 10 := by
      rw [Real.exp_neg, one_div]
      apply inv_anti₀ (by norm_num)
      have := Real.add_one_le_exp 10
      linarith
    calc ((2 : ℝ) ^ n) ^ m * (1 - 1 / (2 : ℝ) ^ n) ^ m ≤ ((2 : ℝ) ^ n) ^ m * (1 / 10) :=
          mul_le_mul_of_nonneg_left (e2.trans e3) (by positivity)
      _ = ((2 : ℝ) ^ n) ^ m / 10 := by ring
  have hgood := Finset.card_le_card hsub
  refine le_trans ?_ (div_le_div_of_nonneg_right (Nat.cast_le.mpr hgood) (Nat.cast_nonneg _))
  have hNpos : (0 : ℝ) < ((2 ^ n) ^ m : ℕ) := by positivity
  rw [htot, le_div_iff₀ hNpos]
  have hsplitR : (((univ : Finset (Fin m → Finset (Fin n))).filter
      (fun S => ∃ j, S j = univ)).card : ℝ) + (((2 ^ n - 1 : ℕ) : ℝ)) ^ m = ((2 ^ n) ^ m : ℕ) := by
    exact_mod_cast hsplit
  push_cast at hsplitR ⊢
  linarith
