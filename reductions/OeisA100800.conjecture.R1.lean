import FormalConjectures.OEIS.«100800»

/-! Split the first-return problem by whether the start is divisible by three.
The orbit of a multiple of three stays in the multiples of three.
The first nine positive starts are discharged directly. -/

namespace OMA.R_OeisA100800_conjecture_R1

open OeisA100800

open Function

theorem le_f (n : ℕ) : n ≤ f n := by
  exact Nat.le_add_right n (sumDigits n)

theorem le_iterate_f (k n : ℕ) : n ≤ f^[k] n := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (le_f _)

theorem a_ne_zero_iff_return {n : ℕ} (hn : n ≠ 0) :
    a n ≠ 0 ↔ ∃ k : ℕ, n ∣ f^[k + 1] n := by
  classical
  unfold a
  dsimp only
  split
  next h =>
    exact ⟨fun _ => h, fun _ => (Nat.zero_lt_of_ne_zero hn).trans_le
      (le_iterate_f _ _) |>.ne'⟩
  next h => exact ⟨fun h0 => (h0 rfl).elim, fun he => (h he).elim⟩

theorem f_modEq_double (n : ℕ) : f n ≡ 2 * n [MOD 9] := by
  rw [f, two_mul]
  exact (Nat.ModEq.refl n).add (Nat.modEq_nine_digits_sum n).symm

theorem iterate_f_modEq (k n : ℕ) : f^[k] n ≡ 2 ^ k * n [MOD 9] := by
  induction k with
  | zero => simp [Nat.ModEq.refl]
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    exact (f_modEq_double (f^[k] n)).trans ((Nat.ModEq.refl 2).mul ih)

theorem a_ne_zero_of_dvd_nine {n : ℕ} (hn : n ≠ 0) (hd : n ∣ 9) :
    a n ≠ 0 := by
  apply (a_ne_zero_iff_return hn).2
  refine ⟨0, ?_⟩
  change n ∣ f n
  have h := (f_modEq_double n).of_dvd hd
  exact (Nat.modEq_zero_iff_dvd.mp (h.trans (Nat.modEq_zero_iff_dvd.mpr
    (dvd_mul_left n 2))))

/-- The return condition also holds uniformly for the first nine starting values. -/
theorem a_ne_zero_of_lt_ten {n : ℕ} (hn : 0 < n) (h10 : n < 10) : a n ≠ 0 := by
  apply (a_ne_zero_iff_return hn.ne').2
  refine ⟨0, ?_⟩
  change n ∣ f n
  interval_cases n <;> decide +kernel

def H1 : Prop :=
  ∀ n : ℕ, 10 ≤ n → 3 ∣ n → ∃ k : ℕ, n ∣ f^[k + 1] n

def H2 : Prop :=
  ∀ n : ℕ, 10 ≤ n → ¬ 3 ∣ n → ∃ k : ℕ, n ∣ f^[k + 1] n

theorem main : H1 → H2 → type_of% @OeisA100800.conjecture := by
  intro h1 h2 n hn
  by_cases hsmall : n < 10
  · exact a_ne_zero_of_lt_ten (Nat.pos_of_ne_zero hn) hsmall
  apply (a_ne_zero_iff_return hn).2
  by_cases hdiv : 3 ∣ n
  · exact h1 n (by omega) hdiv
  · exact h2 n (by omega) hdiv

end OMA.R_OeisA100800_conjecture_R1
