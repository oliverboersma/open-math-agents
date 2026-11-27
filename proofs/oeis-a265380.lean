import OMAStatements.S_oeis_a265380

-- Credit: @anmolspace
-- Colin Barker's middle-column conjectures for Rule 158 (OEIS A265380).
-- The cell definitions are those of @snoozingnewt's statement.

open OMA.S_oeis_a265380

private def live (t i : ℤ) : Prop :=
  -t ≤ i ∧ i ≤ t ∧
    (if t % 2 = 0 then (i+t) % 4 ≠ 3
     else i = -t ∨ (i+t) % 4 = 1 ∨ (i+t) % 4 = 2)

private lemma rule158_table (l c r : Bool) :
    ruleOut 158 l c r = true ↔
      ((¬l = true) ∧ (c = true ∨ r = true)) ∨
      (l = true ∧ (c = true ↔ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

private lemma live_step (t i : ℤ) (ht : 0 ≤ t) :
    ((¬ live t (i-1)) ∧ (live t i ∨ live t (i+1)) ∨
      live t (i-1) ∧ (live t i ↔ live t (i+1))) ↔ live (t+1) i := by
  unfold live
  split_ifs <;> omega

private lemma row_description (t : ℕ) (i : ℤ) : cell 158 t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [cell, live]; omega
  | succ t ih =>
    simp only [cell, rule158_table, ih, Nat.cast_succ]
    exact live_step _ _ (by positivity)

private lemma middle_bit (t : ℕ) : cell 158 t 0 = true ↔ t % 4 ≠ 3 := by
  rw [row_description]
  unfold live
  split_ifs <;> omega

private def digit (n : ℕ) : ℤ := if n % 4 = 3 then 0 else 1

private lemma next_a (n : ℕ) : a (n+1) = 10 * a n + digit (n+1) := by
  unfold a
  rw [Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [show n+1-t = n-t+1 by omega, pow_succ]
    split <;> ring
  · simp only [Nat.sub_self, pow_zero, middle_bit, digit]
    split_ifs <;> omega

private lemma recurrence (n : ℕ) (hn : 4 < n) :
    a n = 10 * a (n - 1) + a (n - 4) - 10 * a (n - 5) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 5 := ⟨n-5, by omega⟩
  simp only [show q+5-1 = q+4 by omega, show q+5-4 = q+1 by omega,
    show q+5-5 = q by omega]
  rw [next_a (q+4), next_a q]
  have he : digit (q+4+1) = digit (q+1) := by
    unfold digit
    split_ifs <;> omega
  omega

private lemma initials : a 0 = 1 ∧ a 1 = 11 ∧ a 2 = 111 ∧ a 3 = 1110 ∧ a 4 = 11101 := by
  decide +kernel

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a265380.main := by
  refine ⟨recurrence, ?_⟩
  let F : PowerSeries ℚ := mk (fun n => (a n : ℚ))
  change F * _ = _
  have product : F * ((1-X)*(1+X)*(1-10*X)*(1+X^2)) =
      F - 10 • (F * X^1) - F * X^4 + 10 • (F * X^5) := by
    simp only [nsmul_eq_mul]
    ring
  rw [product]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', F, coeff_mk,
    coeff_one, coeff_X, coeff_X_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases h : 4 < n
  · have h1 : 1 ≤ n := by omega
    have h4 : 4 ≤ n := by omega
    have h5 : 5 ≤ n := by omega
    have h0' : n ≠ 0 := by omega
    have h1' : n ≠ 1 := by omega
    have h2' : n ≠ 2 := by omega
    simp only [h1, h4, h5, h0', h1', h2', if_true, if_false, zero_add]
    have hr : (a n : ℚ) = 10 * (a (n-1) : ℚ) + (a (n-4) : ℚ) - 10 * (a (n-5) : ℚ) := by
      exact_mod_cast recurrence n h
    linarith
  · obtain ⟨h0, h1, h2, h3, h4⟩ := initials
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4]
