import OMAStatements.S_oeis_a007310

def QQ {R : Type*} [CommRing R] (x : R) : R :=
  3 * x ^ 12 + 18 * x ^ 11 + 24 * x ^ 10 - 45 * x ^ 9 - 81 * x ^ 8 + 144 * x ^ 7 + 182 * x ^ 6
    - 345 * x ^ 5 - 217 * x ^ 4 + 498 * x ^ 3 + 44 * x ^ 2 - 315 * x + 105

lemma sum_formula (n : ℕ) :
    (90 : ℤ) * ((∑ k ∈ Finset.Icc 1 n, k ^ 14 : ℕ) : ℤ)
      = (n : ℤ) * ((n + 1) * (2 * n + 1) * QQ (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_add, mul_add, ih]
    unfold QQ
    push_cast
    ring

set_option maxRecDepth 100000 in
lemma table :
    ∀ x : ZMod 90, ((x + 1) * (2 * x + 1) * QQ x = 0 ↔ (x.val % 6 = 1 ∨ x.val % 6 = 5)) := by
  unfold QQ
  decide

theorem OMA.solution : type_of% @OMA.S_oeis_a007310.main := by
  intro n hn
  have h90 := sum_formula n
  rw [← Int.natCast_dvd_natCast]
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← mul_dvd_mul_iff_left (by norm_num : (90 : ℤ) ≠ 0), h90, mul_comm (90 : ℤ) (n : ℤ),
    mul_dvd_mul_iff_left hn0, show (90 : ℤ) = ((90 : ℕ) : ℤ) by norm_num,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hval : ((n : ZMod 90)).val % 6 = n % 6 := by
    rw [ZMod.val_natCast]; omega
  have := table (n : ZMod 90)
  rw [hval] at this
  rw [← this]
  unfold QQ
  push_cast
  rfl
