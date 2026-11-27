import FormalConjectures.OEIS.«86766»

/-
For the six-digit block 104040, multiplying each candidate by 999999 gives
(1020 * 1000^r - 201) * (1020 * 1000^r + 201). Both factors exceed 999999.
In 2022, Mersenne Forum contributor sweety439 gave other counterexamples, including
1010 and 101010 (https://archive.ph/zao2Y).
-/

namespace A086766Counterexample

private lemma geometric (r : ℕ) :
    999999 * (∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) + 1 = 1000000 ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [Finset.sum_range_succ, pow_succ]; omega

private lemma not_prime (r : ℕ) (hr : 0 < r) :
    ¬ ((104040 * ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) * 10 + 1).Prime := by
  let t := (1000 : ℕ) ^ r
  let s := ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i
  let c := (104040 * s) * 10 + 1
  let u := 1020 * t - 201
  let v := 1020 * t + 201
  have ht : 1000 ≤ t := (show (1000 : ℕ) ^ 1 ≤ 1000 ^ r from
    Nat.pow_le_pow_right (by decide) hr)
  have hsub : 201 ≤ 1020 * t := by omega
  have hgeom : 999999 * s + 1 = t * t := by
    dsimp [s, t]
    rw [← mul_pow]
    exact geometric r
  have hfac : u * v = 999999 * c := by
    dsimp [u, v, c]
    zify [hsub] at hgeom ⊢
    nlinarith only [hgeom]
  have hu : 999999 < u := by dsimp [u]; omega
  have hv : 999999 < v := by dsimp [v]; omega
  change ¬ c.Prime
  intro hp
  have hd : c ∣ u * v := by rw [hfac]; exact dvd_mul_left c 999999
  rcases hp.dvd_mul.mp hd with h | h
  · have hc := Nat.le_of_dvd (by omega : 0 < u) h
    have hle := Nat.mul_le_mul_left 999999 hc
    have hlt := Nat.mul_lt_mul_of_pos_left hv (by omega : 0 < u)
    rw [hfac, Nat.mul_comm u 999999] at hlt
    omega
  · have hc := Nat.le_of_dvd (by omega : 0 < v) h
    have hle := Nat.mul_le_mul_left 999999 hc
    have hlt := Nat.mul_lt_mul_of_pos_right hu (by omega : 0 < v)
    rw [hfac] at hlt
    omega

private lemma zero_value : OeisA86766.a 104040 = 0 := by
  have hd : (Nat.digits 10 104040).length = 6 := by decide
  simp only [OeisA86766.a, show (104040 : ℕ) ≠ 0 by decide, if_false, hd]
  have he : {r : ℕ | 0 < r ∧ ((104040 * ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) * 10 + 1).Prime} = ∅ := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => not_prime r h.1 h.2
  change sInf {r : ℕ | 0 < r ∧ ((104040 * ∑ i ∈ Finset.range r, (1000000 : ℕ) ^ i) * 10 + 1).Prime} = 0
  rw [he, Nat.sInf_empty]

private lemma nonpower (m : ℕ) : (104040 : ℕ) ≠ 10 ^ m := by
  rcases le_or_gt m 5 with h | h
  · have hb : (10 : ℕ) ^ m ≤ 10 ^ 5 := Nat.pow_le_pow_right (by decide) h
    norm_num at hb
    omega
  · have hb : (10 : ℕ) ^ 6 ≤ 10 ^ m := Nat.pow_le_pow_right (by decide) h
    norm_num at hb
    omega

end A086766Counterexample

theorem OMA.disproof : ¬ (type_of% @OeisA86766.conjecture2) := by
  intro h
  exact h 104040 (by decide) A086766Counterexample.nonpower A086766Counterexample.zero_value
