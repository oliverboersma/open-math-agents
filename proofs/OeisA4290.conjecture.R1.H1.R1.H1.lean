import OMAReductions.R_OeisA4290_conjecture_R1_H1_R1

-- Digit stacking: every divisor n of 10^t - 1 with t at most k has a 0/1 multiple below the repunit with 9k digits.
-- Original proof (no external source). A slice of the open question on OEIS A004290, not the question itself.

namespace OMA.A4290slice
open Finset

lemma digits01 : ∀ (L : ℕ) (f : ℕ → ℕ), (∀ i, f i ≤ 1) →
    ∀ d ∈ Nat.digits 10 (∑ i ∈ range L, f i * 10 ^ i), d = 0 ∨ d = 1 := by
  intro L
  induction L with
  | zero => intro f hf d hd; simp at hd
  | succ L ih =>
    intro f hf d hd
    rw [sum_range_succ'] at hd
    have e : ∑ i ∈ range L, f (i + 1) * 10 ^ (i + 1)
        = 10 * ∑ i ∈ range L, f (i + 1) * 10 ^ i := by
      rw [mul_sum]; apply sum_congr rfl; intro i _; ring
    rw [e, pow_zero, mul_one] at hd
    by_cases h0 : 10 * ∑ i ∈ range L, f (i + 1) * 10 ^ i + f 0 = 0
    · rw [h0] at hd; simp at hd
    · rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero h0)] at hd
      have hf0 := hf 0
      have e1 : (10 * ∑ i ∈ range L, f (i + 1) * 10 ^ i + f 0) % 10 = f 0 := by omega
      have e2 : (10 * ∑ i ∈ range L, f (i + 1) * 10 ^ i + f 0) / 10
          = ∑ i ∈ range L, f (i + 1) * 10 ^ i := by omega
      rw [e1, e2] at hd
      rcases List.mem_cons.mp hd with h | h
      · omega
      · exact ih (fun i => f (i + 1)) (fun i => hf (i + 1)) d h

lemma geom10 (L : ℕ) : ∑ i ∈ range L, 10 ^ i = (10 ^ L - 1) / 9 := by
  have := Nat.geomSum_eq (m := 10) (by norm_num) L
  simpa using this

lemma nine_mul_geom10 (L : ℕ) : 9 * ∑ i ∈ range L, 10 ^ i = 10 ^ L - 1 := by
  rw [geom10]
  exact Nat.mul_div_cancel' (by simpa using Nat.sub_one_dvd_pow_sub_one 10 L)

lemma lt_repunit (L : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i ≤ 1) (i0 : ℕ) (hi0 : i0 < L)
    (h0 : f i0 = 0) : ∑ i ∈ range L, f i * 10 ^ i < (10 ^ L - 1) / 9 := by
  rw [← geom10]
  apply sum_lt_sum
  · intro i _
    calc f i * 10 ^ i ≤ 1 * 10 ^ i := Nat.mul_le_mul_right _ (hf i)
      _ = 10 ^ i := one_mul _
  · exact ⟨i0, mem_range.mpr hi0, by rw [h0, zero_mul]; positivity⟩

lemma digit_expansion (n : ℕ) : ∀ t, ∑ j ∈ range t, (n / 10 ^ j % 10) * 10 ^ j = n % 10 ^ t := by
  intro t
  induction t with
  | zero => simp [Nat.mod_one]
  | succ t ih => rw [sum_range_succ, ih, pow_succ, Nat.mod_mul]; ring

theorem slice1 (k n t : ℕ) (hn : 0 < n) (hlt : n < 10 ^ k - 1) (ht0 : 0 < t) (htk : t ≤ k)
    (hdvd : n ∣ 10 ^ t - 1) :
    ∃ m < (10 ^ (9 * k) - 1) / 9, 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := by
  classical
  set d : ℕ → ℕ := fun j => n / 10 ^ j % 10 with hd
  set f : ℕ → ℕ := fun i => if i / t < d (i % t) then 1 else 0 with hf
  have hd10 : ∀ j, d j < 10 := fun j => Nat.mod_lt _ (by norm_num)
  have hf1 : ∀ i, f i ≤ 1 := by
    intro i; simp only [hf]; split_ifs <;> omega
  have hpow : 10 ≤ 10 ^ t := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ t := Nat.pow_le_pow_right (by norm_num) ht0
  have hnlt : n < 10 ^ t := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hexp : ∑ j ∈ range t, d j * 10 ^ j = n := by
    rw [digit_expansion n t, Nat.mod_eq_of_lt hnlt]
  have hfz : ∀ i, 9 * t ≤ i → f i = 0 := by
    intro i hi
    have h9 : 9 ≤ i / t := (Nat.le_div_iff_mul_le ht0).mpr hi
    have := hd10 (i % t)
    simp only [hf]; rw [if_neg (by omega)]
  have hblock : ∀ R, ∑ i ∈ range (t * R), f i * 10 ^ i
      ≡ ∑ j ∈ range t, min (d j) R * 10 ^ j [MOD 10 ^ t - 1] := by
    intro R
    induction R with
    | zero => simp [Nat.ModEq]
    | succ R ih =>
      have h10 : 10 ^ t ≡ 1 [MOD 10 ^ t - 1] :=
        ((Nat.modEq_iff_dvd' (by omega : 1 ≤ 10 ^ t)).2 (dvd_refl _)).symm
      have hb : ∑ j ∈ range t, f (t * R + j) * 10 ^ (t * R + j)
          = (∑ j ∈ range t, (if R < d j then 1 else 0) * 10 ^ j) * (10 ^ t) ^ R := by
        rw [sum_mul]
        apply sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        have e1 : (t * R + j) / t = R := by
          rw [Nat.mul_add_div ht0, Nat.div_eq_of_lt hj', add_zero]
        have e2 : (t * R + j) % t = j := by
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
        simp only [hf, e1, e2]
        rw [pow_add, pow_mul]; ring
      rw [Nat.mul_succ, sum_range_add, hb]
      have hstep : ∑ j ∈ range t, min (d j) (R + 1) * 10 ^ j
          = ∑ j ∈ range t, min (d j) R * 10 ^ j
            + ∑ j ∈ range t, (if R < d j then 1 else 0) * 10 ^ j := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        rw [← add_mul]
        congr 1
        split_ifs with h <;> omega
      rw [hstep]
      refine Nat.ModEq.add ih ?_
      have := Nat.ModEq.mul_left (∑ j ∈ range t, (if R < d j then 1 else 0) * 10 ^ j) (h10.pow R)
      simpa using this
  have hm9 : ∑ i ∈ range (9 * k), f i * 10 ^ i = ∑ i ∈ range (t * 9), f i * 10 ^ i := by
    symm
    apply sum_subset
    · intro i hi; rw [mem_range] at hi ⊢; omega
    · intro i _ hi
      rw [mem_range, not_lt] at hi
      rw [hfz i (by omega), zero_mul]
  have hT9 : ∑ j ∈ range t, min (d j) 9 * 10 ^ j = n := by
    rw [← hexp]; apply sum_congr rfl; intro j _
    rw [Nat.min_eq_left (by have := hd10 j; omega)]
  refine ⟨∑ i ∈ range (9 * k), f i * 10 ^ i, ?_, ?_, ?_, digits01 _ f hf1⟩
  · by_cases htk' : t < k
    · exact lt_repunit _ f hf1 (9 * t) (by omega) (hfz _ le_rfl)
    · have htk'' : k = t := by omega
      rw [htk''] at hlt
      have : ∃ j, j < t ∧ d j ≤ 8 := by
        by_contra hcon
        push Not at hcon
        have h9 : ∀ j ∈ range t, d j * 10 ^ j = 9 * 10 ^ j := by
          intro j hj
          have h1 := hcon j (mem_range.mp hj)
          have h2 := hd10 j
          rw [show d j = 9 by omega]
        rw [sum_congr rfl h9, ← mul_sum, nine_mul_geom10] at hexp
        omega
      obtain ⟨j, hj, hj8⟩ := this
      refine lt_repunit _ f hf1 (t * 8 + j) (by omega) ?_
      have e1 : (t * 8 + j) / t = 8 := by
        rw [Nat.mul_add_div ht0, Nat.div_eq_of_lt hj]
      have e2 : (t * 8 + j) % t = j := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      simp only [hf, e1, e2]; rw [if_neg (by omega)]
  · have : ∃ j, j < t ∧ 0 < d j := by
      by_contra hcon
      push Not at hcon
      have h0 : ∀ j ∈ range t, d j * 10 ^ j = 0 := by
        intro j hj
        have := hcon j (mem_range.mp hj)
        rw [Nat.le_zero.mp this, zero_mul]
      rw [sum_eq_zero h0] at hexp
      omega
    obtain ⟨j, hj, hjpos⟩ := this
    have hjm : j ∈ range (9 * k) := mem_range.mpr (by omega)
    have hle := single_le_sum (f := fun i => f i * 10 ^ i) (fun i _ => Nat.zero_le _) hjm
    have hfj : f j = 1 := by
      have e1 : j / t = 0 := Nat.div_eq_of_lt hj
      have e2 : j % t = j := Nat.mod_eq_of_lt hj
      simp only [hf, e1, e2]; rw [if_pos hjpos]
    have hpos : 0 < f j * 10 ^ j := by rw [hfj]; positivity
    exact lt_of_lt_of_le hpos hle
  · rw [hm9]
    have h1 := hblock 9
    rw [hT9] at h1
    have h2 := Nat.ModEq.of_dvd hdvd h1
    exact (Nat.modEq_zero_iff_dvd).mp (h2.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))


end OMA.A4290slice

theorem OMA.solution : OMA.R_OeisA4290_conjecture_R1_H1_R1.H1 := by
  intro k n t hn hlt ht0 htk hdvd
  exact OMA.A4290slice.slice1 k n t hn hlt ht0 htk hdvd
