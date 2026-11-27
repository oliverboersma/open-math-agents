import OMAStatements.S_oeis_a263806

-- Credit: @anmolspace
-- Colin Barker's Rule 157 conjectures, with the statement by @snoozingnewt.

open OMA.S_oeis_a263806

private def lit (t i : ℤ) : Prop :=
  i < -t ∨ 0 ≤ i ∨ (-t < i ∧ i % 2 = 0)

private lemma rule157_table (l c r : Bool) : ruleOut 157 l c r = true ↔
    (l = true ∧ (c = true ↔ r = true)) ∨ (¬l = true ∧ (c = true ∨ ¬r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

private lemma row_lit (n : ℕ) (hn : 0 < n) (i : ℤ) : cell 157 n i = true ↔ lit n i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp only [cell, rule157_table, decide_eq_true_eq]; unfold lit; omega
    | succ n =>
      change ruleOut 157 (cell 157 (n+1) (i-1)) (cell 157 (n+1) i) (cell 157 (n+1) (i+1)) = true ↔ _
      simp only [rule157_table, ih (by omega), Nat.cast_succ]
      unfold lit
      omega

private def weight (n j : ℕ) : ℤ :=
  if cell 157 n ((j : ℤ)-n) then (2 : ℤ) ^ (2*n-j) else 0

private def extra (n : ℕ) : ℤ := if n%2 = 0 then (2 : ℤ)^(2*n+1) else 0

private lemma first_weight (n : ℕ) (hn : 0 < n) : weight n 0 = 0 := by
  unfold weight
  simp only [row_lit n hn, lit, Nat.cast_zero, zero_sub]
  split_ifs <;> omega

private lemma second_weight (n : ℕ) (hn : 0 < n) : weight (n+1) 1 = extra n := by
  unfold weight extra
  simp only [row_lit (n+1) (by omega), lit, Nat.cast_one, Nat.cast_add]
  rw [show 2*(n+1)-1=2*n+1 by omega]
  split_ifs <;> omega

private lemma last_weight (n : ℕ) : weight (n+1) (2*n+2) = 1 := by
  unfold weight
  rw [show 2*(n+1)-(2*n+2)=0 by omega, pow_zero]
  simp only [row_lit (n+1) (by omega), lit, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  split_ifs <;> omega

private lemma shift_weight (n j : ℕ) (hn : 0<n) (hj : j<2*n) :
    weight (n+1) (j+2) = 2 * weight n (j+1) := by
  unfold weight
  simp only [row_lit (n+1) (by omega), row_lit n hn, lit, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  rw [show 2*(n+1)-(j+2) = 2*n-(j+1)+1 by omega, pow_succ]
  split_ifs <;> omega

private lemma append_bit (n : ℕ) (hn : 0<n) : a (n+1) = 2*a n+1+extra n := by
  change (∑ j ∈ Finset.range (2*(n+1)+1), weight (n+1) j) =
    2*(∑ j ∈ Finset.range (2*n+1), weight n j)+1+extra n
  rw [show 2*(n+1)+1=2*n+2+1 by omega, Finset.sum_range_succ, last_weight]
  rw [Finset.sum_range_succ' (fun j => weight (n+1) j) (2*n+1),
    Finset.sum_range_succ' (fun j => weight (n+1) (j+1)) (2*n),
    Finset.sum_range_succ' (weight n) (2*n)]
  rw [first_weight n hn, first_weight (n+1) (by omega), second_weight n hn, add_zero, add_zero,
    Finset.mul_sum]
  have hs : (∑ j ∈ Finset.range (2*n), weight (n+1) (j+1+1)) =
      ∑ j ∈ Finset.range (2*n), 2 * weight n (j+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact shift_weight n j hn (Finset.mem_range.mp hj)
  rw [hs]
  ring

private lemma extra_shift (n : ℕ) : extra (n+2) = 16 * extra n := by
  unfold extra
  rw [show (n+2)%2=n%2 by omega, show 2*(n+2)+1=2*n+1+4 by omega, pow_add]
  split <;> ring

private lemma third_difference (n : ℕ) (hn : 0<n) :
    a (n+3)-2*a (n+2)-16*a (n+1)+32*a n = -15 := by
  have h0 := append_bit n hn
  have h2 := append_bit (n+2) (by omega)
  rw [extra_shift] at h2
  linarith

private lemma recurrence157 (n : ℕ) (hn : 4<n) :
    a n=3*a (n-1)+14*a (n-2)-48*a (n-3)+32*a (n-4) := by
  obtain ⟨q,rfl⟩ : ∃ q, n=q+5 := ⟨n-5, by omega⟩
  have h1 := third_difference (q+1) (by omega)
  have h2 := third_difference (q+2) (by omega)
  simp only [show q+5-1=q+4 by omega, show q+5-2=q+3 by omega,
    show q+5-3=q+2 by omega, show q+5-4=q+1 by omega]
  linarith

private lemma initial157 : a 0=1 ∧ a 1=3 ∧ a 2=7 ∧ a 3=47 ∧ a 4=95 := by
  decide +kernel

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a263806.main := by
  refine ⟨recurrence157, ?_⟩
  let F : PowerSeries ℚ := mk (fun n => (a n : ℚ))
  change F * _ = _
  have product : F * ((1-X)*(1-2*X)*(1-4*X)*(1+4*X)) =
      F - 3 • (F*X^1) - 14 • (F*X^2) + 48 • (F*X^3) - 32 • (F*X^4) := by
    simp only [nsmul_eq_mul]
    ring
  have numerator : (1-16*X^2+32*X^3-32*X^4 : PowerSeries ℚ) =
      1 - 16 • X^2 + 32 • X^3 - 32 • X^4 := by simp only [nsmul_eq_mul, Nat.cast_ofNat]
  rw [product, numerator]
  ext n
  simp only [map_sub, map_add, map_nsmul, coeff_mul_X_pow', F, coeff_mk, coeff_one, coeff_X_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases h : 4<n
  · have h1 : 1≤n := by omega
    have h2 : 2≤n := by omega
    have h3 : 3≤n := by omega
    have h4 : 4≤n := by omega
    have h0' : n≠0 := by omega
    have h2' : n≠2 := by omega
    have h3' : n≠3 := by omega
    have h4' : n≠4 := by omega
    simp only [h1,h2,h3,h4,h0',h2',h3',h4',if_true,if_false,mul_zero,sub_zero,add_zero]
    have hr : (a n : ℚ) = 3*(a (n-1):ℚ)+14*(a (n-2):ℚ)-48*(a (n-3):ℚ)+32*(a (n-4):ℚ) := by
      exact_mod_cast recurrence157 n h
    linarith
  · obtain ⟨h0,h1,h2,h3,h4⟩ := initial157
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4]
