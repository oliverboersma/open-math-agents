import OMAStatements.S_oeis_a266072

section Aux
open OMA.S_oeis_a266072

lemma upd_eq (l c r : Bool) : update l c r = (!l && !c) := by
  cases l <;> cases c <;> cases r <;> decide

lemma cell_succ (n : ℕ) (i : ℤ) : cell (n + 1) i = (!cell n (i - 1) && !cell n i) := by
  simp only [cell, upd_eq]

lemma cell_pair (k : ℕ) : (∀ i, cell (2 * k) i = decide (i = k)) ∧
    (∀ i, cell (2 * k + 1) i = !(decide (i = k) || decide (i = k + 1))) := by
  induction k with
  | zero =>
    have h0 : ∀ i, cell 0 i = decide (i = 0) := fun i => rfl
    refine ⟨by simpa using h0, fun i => ?_⟩
    rw [cell_succ, h0, h0]
    by_cases h1 : i = 0 <;> by_cases h2 : i - 1 = 0 <;> simp [h1] <;> omega
  | succ k ih =>
    obtain ⟨he, ho⟩ := ih
    have h2 : ∀ i, cell (2 * (k + 1)) i = decide (i = ((k + 1 : ℕ) : ℤ)) := by
      intro i
      have : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [this, cell_succ, ho, ho]
      by_cases a : i = k + 1 <;> simp [a] <;> omega
    refine ⟨h2, fun i => ?_⟩
    have : 2 * (k + 1) + 1 = 2 * (k + 1) + 1 := rfl
    rw [cell_succ, h2, h2]
    push_cast
    by_cases a : i - 1 = k + 1 <;> by_cases b : i = k + 1 <;> simp [a, b] <;> omega

lemma a_closed (n : ℕ) : a n = (n : ℤ) - (-1 : ℤ) ^ n * ((n : ℤ) - 1) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have h := (cell_pair k).1
    unfold a
    have : ∀ j : ℕ, (cell (2 * k) ((j : ℤ) - ((2 * k : ℕ) : ℤ))) = decide (j = 3 * k) := by
      intro j; rw [h]; simp only [decide_eq_decide]; push_cast; omega
    simp only [this, decide_eq_true_eq]
    rw [Finset.sum_ite_eq']
    have hk : 3 * k ∈ Finset.range (2 * (2 * k) + 1) := by simp; omega
    simp [hk]
  · have h := (cell_pair k).2
    unfold a
    have : ∀ j : ℕ, (cell (2 * k + 1) ((j : ℤ) - ((2 * k + 1 : ℕ) : ℤ))) = !(decide (j = 3 * k + 1) || decide (j = 3 * k + 2)) := by
      intro j; rw [h]; simp only [Bool.not_inj_iff]; push_cast
      have e1 : ((j : ℤ) - (2 * k + 1) = k) ↔ (j = 3 * k + 1) := by omega
      have e2 : ((j : ℤ) - (2 * k + 1) = k + 1) ↔ (j = 3 * k + 2) := by omega
      simp only [decide_eq_decide.mpr e1, decide_eq_decide.mpr e2]
    simp only [this]
    have pt : ∀ j : ℕ, (if (!(decide (j = 3 * k + 1) || decide (j = 3 * k + 2))) = true then (1 : ℤ) else 0)
        = 1 - (if j = 3 * k + 1 then 1 else 0) - (if j = 3 * k + 2 then 1 else 0) := by
      intro j
      by_cases a : j = 3 * k + 1 <;> by_cases b : j = 3 * k + 2 <;> simp [a, b] <;> omega
    simp only [pt]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    have h1 : 3 * k + 1 ∈ Finset.range (2 * (2 * k + 1) + 1) := by simp; omega
    have h2 : 3 * k + 2 ∈ Finset.range (2 * (2 * k + 1) + 1) := by simp; omega
    simp [h1, h2]
    rw [Odd.neg_one_pow ⟨k, by ring⟩]
    push_cast; ring

end Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a266072.main := by
  open OMA.S_oeis_a266072 in
  refine ⟨a_closed, fun n hn => ?_, ?_⟩
  · rw [a_closed, a_closed, a_closed]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have e : m + 4 - 2 = m + 2 := by omega
    have e2 : m + 4 - 4 = m := by omega
    rw [e, e2]
    rw [pow_add, pow_add]
    push_cast
    ring_nf
  · have hP : ((-1 : PowerSeries ℚ) + PowerSeries.X ^ 2) ^ 2 = 1 - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4 := by ring
    have hQ : (1 + PowerSeries.X - PowerSeries.X ^ 2 + 3 * PowerSeries.X ^ 3 : PowerSeries ℚ)
        = 1 + PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 3 := by rw [map_ofNat]
    have hM : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 4)
        = PowerSeries.mk (fun n => (a n : ℚ)) - PowerSeries.C (2 : ℚ) * (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
          + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4 := by
      simp only [map_ofNat]; ring
    rw [hP, hM, hQ]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
      PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    simp only [PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | m
    · norm_num [a_closed]
    · norm_num [a_closed]
    · norm_num [a_closed]
    · norm_num [a_closed]
    · have e1 : m + 4 - 2 = m + 2 := by omega
      have e2 : m + 4 - 4 = m := by omega
      have e3 : m + 4 - 3 = m + 1 := by omega
      simp only [e1, e2, e3, a_closed]
      simp
      push_cast
      ring_nf
