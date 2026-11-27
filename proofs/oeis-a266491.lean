import OMAStatements.S_oeis_a266491

/-! For the multiplier sequence 1,1,2,2, its translate by two is its
complement to three. Every positive difference row of that multiplier is
therefore antiperiodic, and two differences multiply by -2 and shift by one.
Use the discrete product rule to recover the rows of n times the multiplier.
Credit: @caa1982. -/

namespace A266491Proof
open OMA.S_oeis_a266491

def s (n : ℕ) : ℤ := if n % 4 < 2 then 1 else 2

def diff : ℕ → ℕ → ℤ
  | 0, n => s n
  | i + 1, n => diff i (n + 1) - diff i n

lemma shift_two (n : ℕ) : s (n + 2) + s n = 3 := by
  unfold s
  split_ifs <;> omega

lemma anti (i n : ℕ) : diff (i + 1) (n + 2) = - diff (i + 1) n := by
  induction i generalizing n with
  | zero =>
    change s (n + 1 + 2) - s (n + 2) = -(s (n + 1) - s n)
    linarith only [shift_two n, shift_two (n + 1)]
  | succ i ih =>
    change diff (i + 1) (n + 1 + 2) - diff (i + 1) (n + 2) =
      -(diff (i + 1) (n + 1) - diff (i + 1) n)
    rw [ih, ih]
    ring

lemma step_two (i n : ℕ) : diff (i + 3) n = -2 * diff (i + 1) (n + 1) := by
  change (diff (i + 1) (n + 2) - diff (i + 1) (n + 1)) -
    (diff (i + 1) (n + 1) - diff (i + 1) n) = _
  rw [anti]
  ring

lemma diff_odd (j n : ℕ) : diff (2 * j + 1) n = (-2 : ℤ) ^ j * diff 1 (n + j) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega, step_two, ih,
      pow_succ, show n + 1 + j = n + (j + 1) by omega]
    ring

lemma diff_even (j n : ℕ) : diff (2 * j + 2) n = (-2 : ℤ) ^ j * diff 2 (n + j) := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 2 = (2 * j + 1) + 3 by omega, step_two, ih,
      pow_succ, show n + 1 + j = n + (j + 1) by omega]
    ring

lemma row_product (i n : ℕ) :
    row (i + 1) n = (n : ℤ) * diff (i + 1) n + ((i : ℤ) + 1) * diff i (n + 1) := by
  induction i generalizing n with
  | zero =>
    change ((n : ℤ) + 1) * s (n + 1) - (n : ℤ) * s n =
      (n : ℤ) * (s (n + 1) - s n) + (0 + 1) * s (n + 1)
    ring
  | succ i ih =>
    change row (i + 1) (n + 1) - row (i + 1) n =
      (n : ℤ) * diff (i + 2) n + ((↑(i + 1) : ℤ) + 1) * diff (i + 1) (n + 1)
    rw [ih, ih]
    rw [show diff (i + 2) n = diff (i + 1) (n + 1) - diff (i + 1) n by rfl]
    rw [show diff (i + 1) (n + 1) = diff i (n + 2) - diff i (n + 1) by rfl]
    push_cast
    ring

lemma row_even (j n : ℕ) :
    row (2 * j + 2) n = (-2 : ℤ) ^ j * ((n : ℤ) * diff 2 (n + j) +
      (↑(2 * j + 2) : ℤ) * diff 1 (n + 1 + j)) := by
  change row (2*j+1+1) n = _
  rw [row_product]
  change (n : ℤ) * diff (2*j+2) n + ((↑(2*j+1) : ℤ) + 1) * diff (2*j+1) (n+1) = _
  rw [diff_even, diff_odd]
  push_cast
  ring

lemma row_odd (j n : ℕ) :
    row (2 * j + 3) n = (-2 : ℤ) ^ j * (-2 * (n : ℤ) * diff 1 (n + (j + 1)) +
      (↑(2 * j + 3) : ℤ) * diff 2 (n + 1 + j)) := by
  change row (2*j+2+1) n = _
  rw [row_product]
  rw [show 2*j+2+1 = 2*(j+1)+1 by omega, diff_odd, diff_even, pow_succ]
  push_cast
  ring

lemma sign_power (j : ℕ) : (-2 : ℤ) ^ j = 2 ^ j * (-1) ^ j := by rw [← mul_pow]; norm_num

lemma abs_one (n : ℕ) : (diff 1 n).natAbs = if n % 2 = 0 then 0 else 1 := by
  simp only [diff, s]
  split_ifs <;> norm_num <;> omega

lemma abs_two (n : ℕ) : (diff 2 n).natAbs = 1 := by
  simp only [diff, s]
  split_ifs <;> norm_num <;> omega

lemma two_forms {i : ℕ} (h : 2 ≤ i) : (∃ j : ℕ, i = 2 * j + 2) ∨ ∃ j : ℕ, i = 2 * j + 3 := by
  by_cases he : i % 2 = 0
  · exact Or.inl ⟨i / 2 - 1, by omega⟩
  · exact Or.inr ⟨i / 2 - 1, by omega⟩

lemma divides_row (i n : ℕ) : scale i ∣ row i n := by
  by_cases h : 2 ≤ i
  · rcases two_forms h with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [row_even, scale, show (2*j+2)/2-1 = j by omega, sign_power, mul_assoc]
      exact dvd_mul_right _ _
    · rw [row_odd, scale, show (2*j+3)/2-1 = j by omega, sign_power, mul_assoc]
      exact dvd_mul_right _ _
  · interval_cases i <;> simp [scale]

lemma first_column (i : ℕ) : (row i 0 / scale i).natAbs = if i % 4 = 0 then 0 else i := by
  by_cases h : 2 ≤ i
  · rcases two_forms h with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [row_even, scale, show (2*j+2)/2-1 = j by omega, sign_power, mul_assoc,
        Int.mul_ediv_cancel_left _ (by positivity)]
      simp only [Nat.cast_zero, zero_mul, zero_add, Int.natAbs_mul, Int.natAbs_pow,
        Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast, abs_one]
      split_ifs <;> simp_all <;> omega
    · rw [row_odd, scale, show (2*j+3)/2-1 = j by omega, sign_power, mul_assoc,
        Int.mul_ediv_cancel_left _ (by positivity)]
      simp only [Nat.cast_zero, mul_zero, zero_mul, zero_add, Int.natAbs_mul, Int.natAbs_pow,
        Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul, Int.natAbs_natCast, abs_two, mul_one]
      split_ifs <;> omega
  · interval_cases i <;> norm_num [row, scale, base]

end A266491Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266491.main :=
  ⟨A266491Proof.divides_row, A266491Proof.first_column⟩
