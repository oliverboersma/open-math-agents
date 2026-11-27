import OMAStatements.S_oeis_a068689
import Mathlib

namespace OMA.A068689Proof

open OMA.S_oeis_a068689

def r : ℕ → ℕ
  | 0 => 0
  | k + 1 => 10 * r k + 1

lemma pow_eq (k : ℕ) : 10 ^ k = 9 * r k + 1 := by
  induction k with
  | zero => simp [r]
  | succ k ih => rw [pow_succ, ih]; simp only [r]; ring

lemma rep_eq (k : ℕ) : (10 ^ k - 1) / 9 = r k := by
  rw [pow_eq]; omega

lemma sand_eq (d k : ℕ) : sandwich d k = 9 * 10 ^ (k + 1) + 10 * (d * r k) + 9 := by
  unfold sandwich; rw [rep_eq]

lemma r_six (k : ℕ) : r (k + 6) = 10 ^ 6 * r k + 111111 := by
  simp only [r]; ring

lemma period (p : ℕ) (h1 : (10 : ZMod p) ^ 6 = 1) (h2 : (111111 : ZMod p) = 0)
    (d j q : ℕ) : ((sandwich d (j + 6 * q) : ℕ) : ZMod p) = ((sandwich d j : ℕ) : ZMod p) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [← ih, show j + 6 * (q + 1) = (j + 6 * q) + 6 by ring, sand_eq, sand_eq, r_six]
    push_cast
    linear_combination (9 * (10 : ZMod p) ^ (j + 6 * q + 1) + 10 * (d * (r (j + 6 * q) : ZMod p))) * h1
      + 10 * (d : ZMod p) * h2

lemma transfer (p : ℕ) (h1 : (10 : ZMod p) ^ 6 = 1) (h2 : (111111 : ZMod p) = 0)
    (d j q : ℕ) (h : p ∣ sandwich d j) : p ∣ sandwich d (j + 6 * q) := by
  rw [← ZMod.natCast_eq_zero_iff] at h ⊢
  rw [period p h1 h2, h]

lemma base : ∀ d < 10, ∀ j < 6, ¬ (d = 1 ∨ d = 2 ∨ d = 8) →
    3 ∣ sandwich d j ∨ 7 ∣ sandwich d j ∨ 11 ∣ sandwich d j ∨ 13 ∣ sandwich d j := by
  decide

end OMA.A068689Proof

open OMA.S_oeis_a068689 OMA.A068689Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a068689.main := by
  intro d k hd _ hp
  by_contra hne
  have hk : k = k % 6 + 6 * (k / 6) := (Nat.mod_add_div k 6).symm
  have hbig : 99 ≤ sandwich d k := by
    rw [sand_eq]
    have : 10 ≤ 10 ^ (k + 1) := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have key : ∀ p, p ∣ sandwich d k → 2 ≤ p → p ≤ 13 → False := by
    intro p hdvd hp2 hp13
    rcases hp.eq_one_or_self_of_dvd p hdvd with h | h <;> omega
  rcases base d hd (k % 6) (Nat.mod_lt _ (by norm_num)) hne with h | h | h | h
  · exact key 3 (hk ▸ transfer 3 (by decide) (by decide) d _ _ h) (by norm_num) (by norm_num)
  · exact key 7 (hk ▸ transfer 7 (by decide) (by decide) d _ _ h) (by norm_num) (by norm_num)
  · exact key 11 (hk ▸ transfer 11 (by decide) (by decide) d _ _ h) (by norm_num) (by norm_num)
  · exact key 13 (hk ▸ transfer 13 (by decide) (by decide) d _ _ h) (by norm_num) (by norm_num)
