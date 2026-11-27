import OMAReductions.R_Arxiv_2110_04263_multiplicative_persistence_conjecture_R1

/-! Eliminate even first products having a zero or five digit. -/
open Arxiv.«2110.04263»
namespace OMA.R_Arxiv_2110_04263_multiplicative_persistence_conjecture_R1_H1_R1

private lemma digit_prod_pos {n : ℕ} (hn : 0 < n) :
    digitProduct n = (Nat.digits 10 n).prod := by
  cases n with
  | zero => omega
  | succ n => rfl

private lemma zero_fixed (k : ℕ) : (digitProduct^[k]) 0 = 0 := by
  exact (show Function.IsFixedPt digitProduct 0 from rfl).iterate k

private lemma zero_of_ten_dvd (m : ℕ) (hm : 10 ∣ m) : digitProduct m = 0 := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [digitProduct, Nat.digits_def' (by decide) (Nat.succ_pos _),
      Nat.mod_eq_zero_of_dvd hm, List.prod_cons, zero_mul]

private lemma done_of_digit_zero {n : ℕ} (h : 0 ∈ Nat.digits 10 n) :
    (digitProduct^[10]) n < 10 := by
  have hz : digitProduct n = 0 := by
    by_cases hn : n = 0
    · simp [hn, digitProduct]
    · rw [digit_prod_pos (Nat.pos_of_ne_zero hn)]
      exact List.prod_eq_zero h
  rw [show (10 : ℕ) = Nat.succ 9 from rfl, Function.iterate_succ_apply, hz, zero_fixed]
  decide

private lemma done_of_even_and_five {n : ℕ} (hpos : 0 < n)
    (heven : 2 ∣ n) (hfive : 5 ∈ Nat.digits 10 n) :
    (digitProduct^[10]) n < 10 := by
  have htwo : 2 ∣ digitProduct n := by
    rw [digit_prod_pos hpos, Nat.digits_def' (by decide) hpos, List.prod_cons]
    apply dvd_mul_of_dvd_left
    omega
  have hfive' : 5 ∣ digitProduct n := by
    rw [digit_prod_pos hpos]
    exact List.dvd_prod hfive
  have hten : 10 ∣ digitProduct n := by
    have h := (show Nat.Coprime 2 5 by decide).mul_dvd_of_dvd_of_dvd htwo hfive'
    simpa using h
  have hz : digitProduct (digitProduct n) = 0 := zero_of_ten_dvd _ hten
  rw [show (10 : ℕ) = Nat.succ 9 from rfl, Function.iterate_succ_apply,
    Function.iterate_succ_apply, hz, zero_fixed]
  decide

/-- Odd first products. -/
def H1 : Prop := ∀ b c : ℕ, (digitProduct^[10]) (3^b * 7^c) < 10

/-- Even first products whose decimal expansions contain neither zero nor five. -/
def H2 : Prop := ∀ a b c : ℕ, 0 < a →
  0 ∉ Nat.digits 10 (2^a * 3^b * 7^c) →
  5 ∉ Nat.digits 10 (2^a * 3^b * 7^c) →
  (digitProduct^[10]) (2^a * 3^b * 7^c) < 10

theorem main : H1 → H2 → OMA.R_Arxiv_2110_04263_multiplicative_persistence_conjecture_R1.H1 := by
  intro h1 h2 a b c
  cases a with
  | zero => simpa using h1 b c
  | succ a =>
    let n := 2^(a+1) * 3^b * 7^c
    have hn : 0 < n := by dsimp [n]; positivity
    have heven : 2 ∣ n := by dsimp [n]; exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) _) _
    by_cases hz : 0 ∈ Nat.digits 10 n
    · exact done_of_digit_zero hz
    by_cases hf : 5 ∈ Nat.digits 10 n
    · exact done_of_even_and_five hn heven hf
    · exact h2 (a+1) b c (by omega) hz hf
end OMA.R_Arxiv_2110_04263_multiplicative_persistence_conjecture_R1_H1_R1
