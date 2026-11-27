import OMAReductions.R_OeisA4290_conjecture_R1_H1_R1_H3_R1

-- Every n below 10^k - 1 dividing 10^(k+1) - 1 has a positive 0/1 multiple below the repunit with 9k digits (k at least 8).
-- Original proof (no external source): stack the digits of a multiple of n whose top nine digits avoid 9; such a
-- multiple exists by a union bound, because multiplying by 10 modulo 10^(k+1) - 1 rotates the digits.
-- A slice of the open question on OEIS A004290, not the question itself.

namespace OMA.A4290next
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

/-- Stacking coefficient: position `i = j + t r` is used when `r` is below digit `j` of `x`. -/
def stk (x t i : ℕ) : ℕ := if i / t < x / 10 ^ (i % t) % 10 then 1 else 0

lemma stk_le (x t i : ℕ) : stk x t i ≤ 1 := by
  unfold stk; split_ifs <;> omega

lemma stk_block (x t : ℕ) (ht0 : 0 < t) (R j : ℕ) (hj : j < t) :
    stk x t (t * R + j) = if R < x / 10 ^ j % 10 then 1 else 0 := by
  have e1 : (t * R + j) / t = R := by
    rw [Nat.mul_add_div ht0, Nat.div_eq_of_lt hj, add_zero]
  have e2 : (t * R + j) % t = j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  unfold stk; rw [e1, e2]

/-- The stacked number is congruent to `x` modulo `10^t - 1`. -/
lemma stk_cong (x t : ℕ) (ht0 : 0 < t) (hx : x < 10 ^ t) :
    ∑ i ∈ range (9 * t), stk x t i * 10 ^ i ≡ x [MOD 10 ^ t - 1] := by
  have hpow : 10 ≤ 10 ^ t := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ t := Nat.pow_le_pow_right (by norm_num) ht0
  have hd10 : ∀ j, x / 10 ^ j % 10 < 10 := fun j => Nat.mod_lt _ (by norm_num)
  have hblock : ∀ R, ∑ i ∈ range (t * R), stk x t i * 10 ^ i
      ≡ ∑ j ∈ range t, min (x / 10 ^ j % 10) R * 10 ^ j [MOD 10 ^ t - 1] := by
    intro R
    induction R with
    | zero => simp [Nat.ModEq]
    | succ R ih =>
      have h10 : 10 ^ t ≡ 1 [MOD 10 ^ t - 1] :=
        ((Nat.modEq_iff_dvd' (by omega : 1 ≤ 10 ^ t)).2 (dvd_refl _)).symm
      have hb : ∑ j ∈ range t, stk x t (t * R + j) * 10 ^ (t * R + j)
          = (∑ j ∈ range t, (if R < x / 10 ^ j % 10 then 1 else 0) * 10 ^ j) * (10 ^ t) ^ R := by
        rw [sum_mul]
        apply sum_congr rfl
        intro j hj
        rw [stk_block x t ht0 R j (mem_range.mp hj), pow_add, pow_mul]; ring
      rw [Nat.mul_succ, sum_range_add, hb]
      have hstep : ∑ j ∈ range t, min (x / 10 ^ j % 10) (R + 1) * 10 ^ j
          = ∑ j ∈ range t, min (x / 10 ^ j % 10) R * 10 ^ j
            + ∑ j ∈ range t, (if R < x / 10 ^ j % 10 then 1 else 0) * 10 ^ j := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro j _
        rw [← add_mul]
        congr 1
        split_ifs with h <;> omega
      rw [hstep]
      refine Nat.ModEq.add ih ?_
      have := Nat.ModEq.mul_left
        (∑ j ∈ range t, (if R < x / 10 ^ j % 10 then 1 else 0) * 10 ^ j) (h10.pow R)
      simpa using this
  have h9 := hblock 9
  have hT9 : ∑ j ∈ range t, min (x / 10 ^ j % 10) 9 * 10 ^ j = x := by
    calc ∑ j ∈ range t, min (x / 10 ^ j % 10) 9 * 10 ^ j
        = ∑ j ∈ range t, (x / 10 ^ j % 10) * 10 ^ j := by
          apply sum_congr rfl; intro j _
          rw [Nat.min_eq_left (by have := hd10 j; omega)]
      _ = x % 10 ^ t := digit_expansion x t
      _ = x := Nat.mod_eq_of_lt hx
  rw [hT9, mul_comm t 9] at h9
  exact h9

/-- Multiplying by 10 modulo `10^t - 1` moves every digit one place up. -/
lemma rot_digit (t x p : ℕ) (hx : x < 10 ^ t - 1) (hp : p + 1 < t) :
    (10 * x % (10 ^ t - 1)) / 10 ^ (p + 1) % 10 = x / 10 ^ p % 10 := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  have hN : 0 < 10 ^ u := by positivity
  have hT : 10 ^ (u + 1) - 1 + 1 = 10 * 10 ^ u := by
    rw [pow_succ]; omega
  have hsplit : 10 ^ u * (x / 10 ^ u) + x % 10 ^ u = x := Nat.div_add_mod x (10 ^ u)
  have hb : x % 10 ^ u < 10 ^ u := Nat.mod_lt _ hN
  have ha : x / 10 ^ u ≤ 9 := by
    have h1 : x < 10 ^ u * 10 := by omega
    have h2 := Nat.div_lt_of_lt_mul h1
    omega
  have key : 10 * x = (10 ^ (u + 1) - 1) * (x / 10 ^ u) + (x / 10 ^ u + 10 * (x % 10 ^ u)) := by
    have e : (10 ^ (u + 1) - 1) * (x / 10 ^ u) + x / 10 ^ u
        = (10 ^ (u + 1) - 1 + 1) * (x / 10 ^ u) := by ring
    rw [← add_assoc, e, hT]
    nlinarith [hsplit]
  have hsmall : x / 10 ^ u + 10 * (x % 10 ^ u) < 10 ^ (u + 1) - 1 := by
    rcases (show x / 10 ^ u ≤ 8 ∨ x / 10 ^ u = 9 by omega) with h | h
    · omega
    · rw [h] at hsplit; omega
  rw [key, Nat.mul_add_mod, Nat.mod_eq_of_lt hsmall]
  have e1 : (x / 10 ^ u + 10 * (x % 10 ^ u)) / 10 ^ (p + 1) = x % 10 ^ u / 10 ^ p := by
    rw [pow_succ, mul_comm (10 ^ p) 10, ← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 10), Nat.div_eq_of_lt (by omega), zero_add]
  rw [e1]
  have hup : u = p + (u - p) := by omega
  have e2 : x % 10 ^ u / 10 ^ p = x / 10 ^ p % 10 ^ (u - p) := by
    conv_lhs => rw [hup, pow_add]
    exact Nat.mod_mul_right_div_self _ _ _
  rw [e2]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self 10 (by omega))

lemma rot_iter (t x : ℕ) (hx : x < 10 ^ t - 1) : ∀ s p, p + s < t →
    (10 ^ s * x % (10 ^ t - 1)) / 10 ^ (p + s) % 10 = x / 10 ^ p % 10 := by
  intro s
  induction s with
  | zero => intro p _; rw [pow_zero, one_mul, Nat.mod_eq_of_lt hx, add_zero]
  | succ s ih =>
    intro p hp
    have hTpos : 0 < 10 ^ t - 1 := by omega
    have e : 10 ^ (s + 1) * x % (10 ^ t - 1) = 10 * (10 ^ s * x % (10 ^ t - 1)) % (10 ^ t - 1) := by
      rw [Nat.mul_mod_mod, pow_succ]; congr 1; ring
    rw [e, ← add_assoc, rot_digit t _ (p + s) (Nat.mod_lt _ hTpos) (by omega)]
    exact ih p (by omega)

/-- A positive multiple of `n` below `10^(k+1) - 1` whose top nine digits avoid 9. -/
lemma good_exists (k n : ℕ) (hk : 8 ≤ k) (hn : 0 < n) (hlt : n < 10 ^ k - 1)
    (hdvd : n ∣ 10 ^ (k + 1) - 1) :
    ∃ x, 0 < x ∧ x < 10 ^ (k + 1) - 1 ∧ n ∣ x ∧
      ∀ p, k - 8 ≤ p → p ≤ k → x / 10 ^ p % 10 ≤ 8 := by
  classical
  have hP : 10 ≤ 10 ^ k := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTeq : 10 ^ (k + 1) - 1 = 10 * 10 ^ k - 1 := by rw [pow_succ]; ring_nf
  have hTpos : 0 < 10 ^ (k + 1) - 1 := by omega
  obtain ⟨D, hD⟩ := hdvd
  have hDpos : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h | h
    · rw [h, mul_zero] at hD; omega
    · exact h
  have hcop10 : Nat.Coprime (10 ^ (k + 1) - 1) 10 := by
    have h1 : Nat.Coprime (10 ^ (k + 1) - 1) (10 ^ (k + 1) - 1 + 1) :=
      (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right _)
    rw [Nat.sub_add_cancel (by omega)] at h1
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self 10 (by omega)) h1
  set T := 10 ^ (k + 1) - 1 with hT
  let M : Finset ℕ := (range T).filter (fun x => 0 < x ∧ n ∣ x)
  let bad : ℕ → Finset ℕ := fun p => M.filter (fun x => x / 10 ^ p % 10 = 9)
  let Top : Finset ℕ := (range T).filter (fun y => n ∣ y ∧ 9 * 10 ^ k ≤ y)
  have hM : D - 1 ≤ M.card := by
    have hsub : (Ico 1 D).image (fun j => j * n) ⊆ M := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
      rw [mem_Ico] at hj
      simp only [M, mem_filter, mem_range]
      refine ⟨?_, Nat.mul_pos (by omega) hn, dvd_mul_left _ _⟩
      rw [hD, mul_comm j n]
      exact Nat.mul_lt_mul_of_pos_left hj.2 hn
    have hc : ((Ico 1 D).image (fun j => j * n)).card = D - 1 := by
      rw [card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hn h), Nat.card_Ico]
    rw [← hc]; exact card_le_card hsub
  have hTop : Top.card ≤ (10 ^ k - 1) / n := by
    have hmaps : ∀ y ∈ Top, (T - y) / n ∈ Icc 1 ((10 ^ k - 1) / n) := by
      intro y hy
      simp only [Top, mem_filter, mem_range] at hy
      obtain ⟨hyT, hny, hy9⟩ := hy
      have hd : n ∣ T - y := Nat.dvd_sub (hD ▸ dvd_mul_right n D) hny
      rw [mem_Icc]
      refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hd) hn, Nat.div_le_div_right ?_⟩
      omega
    have hinj : Set.InjOn (fun y => (T - y) / n) (Top : Set ℕ) := by
      intro y hy y' hy' h
      simp only [Top, coe_filter, mem_range, Set.mem_setOf_eq] at hy hy'
      have hd : n ∣ T - y := Nat.dvd_sub (hD ▸ dvd_mul_right n D) hy.2.1
      have hd' : n ∣ T - y' := Nat.dvd_sub (hD ▸ dvd_mul_right n D) hy'.2.1
      have h1 : T - y = T - y' := by
        have := congrArg (· * n) h
        simpa [Nat.div_mul_cancel hd, Nat.div_mul_cancel hd'] using this
      omega
    have := card_le_card_of_injOn _ hmaps hinj
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
  have hbad : ∀ p, p ≤ k → (bad p).card ≤ (10 ^ k - 1) / n := by
    intro p hp
    have hmaps : ∀ x ∈ bad p, 10 ^ (k - p) * x % T ∈ Top := by
      intro x hx
      have hx' : (x < T ∧ 0 < x ∧ n ∣ x) ∧ x / 10 ^ p % 10 = 9 := by
        simpa only [bad, M, mem_filter, mem_range] using hx
      obtain ⟨⟨hxT, hx0, hnx⟩, hdig⟩ := hx'
      simp only [Top, mem_filter, mem_range]
      refine ⟨Nat.mod_lt _ hTpos, ?_, ?_⟩
      · exact (Nat.dvd_mod_iff (hD ▸ dvd_mul_right n D)).mpr (dvd_mul_of_dvd_right hnx _)
      · have h := rot_iter (k + 1) x hxT (k - p) p (by omega)
        rw [show p + (k - p) = k by omega, hdig, ← hT] at h
        have h9 : 9 ≤ 10 ^ (k - p) * x % T / 10 ^ k := by
          generalize 10 ^ (k - p) * x % T / 10 ^ k = q at h
          omega
        exact (Nat.le_div_iff_mul_le (by positivity)).mp h9
    have hinj : Set.InjOn (fun x => 10 ^ (k - p) * x % T) (bad p : Set ℕ) := by
      intro x hx x' hx' h
      have hxa : (x < T ∧ 0 < x ∧ n ∣ x) ∧ x / 10 ^ p % 10 = 9 := by
        simpa only [bad, M, mem_filter, mem_range, mem_coe] using hx
      have hxb : (x' < T ∧ 0 < x' ∧ n ∣ x') ∧ x' / 10 ^ p % 10 = 9 := by
        simpa only [bad, M, mem_filter, mem_range, mem_coe] using hx'
      have hc : Nat.gcd T (10 ^ (k - p)) = 1 := Nat.Coprime.pow_right _ hcop10
      have h1 : 10 ^ (k - p) * x ≡ 10 ^ (k - p) * x' [MOD T] := h
      have h2 := Nat.ModEq.cancel_left_of_coprime hc h1
      rw [Nat.ModEq, Nat.mod_eq_of_lt hxa.1.1, Nat.mod_eq_of_lt hxb.1.1] at h2
      exact h2
    exact le_trans (card_le_card_of_injOn _ hmaps hinj) hTop
  have hU : ((Icc (k - 8) k).biUnion bad).card ≤ 9 * ((10 ^ k - 1) / n) := by
    refine le_trans card_biUnion_le ?_
    have h9 : (Icc (k - 8) k).card = 9 := by rw [Nat.card_Icc]; omega
    calc ∑ p ∈ Icc (k - 8) k, (bad p).card ≤ ∑ _p ∈ Icc (k - 8) k, (10 ^ k - 1) / n :=
          sum_le_sum (fun p hp => hbad p (mem_Icc.mp hp).2)
      _ = 9 * ((10 ^ k - 1) / n) := by rw [sum_const, h9, smul_eq_mul]
  have hcount : 9 * ((10 ^ k - 1) / n) < D - 1 := by
    by_contra hc
    push Not at hc
    have h1 : (10 ^ k - 1) / n * n ≤ 10 ^ k - 1 := Nat.div_mul_le_self _ _
    have h3 : (D - 1) * n ≤ 9 * ((10 ^ k - 1) / n) * n := Nat.mul_le_mul_right n hc
    rw [Nat.sub_mul, one_mul, mul_assoc] at h3
    have h2 : D * n = 10 * 10 ^ k - 1 := by rw [mul_comm, ← hD]; exact hTeq
    omega
  have hlast : ((Icc (k - 8) k).biUnion bad).card < M.card := by omega
  obtain ⟨x, hxM, hxU⟩ := exists_mem_notMem_of_card_lt_card hlast
  simp only [M, mem_filter, mem_range] at hxM
  refine ⟨x, hxM.2.1, hxM.1, hxM.2.2, ?_⟩
  intro p hp1 hp2
  have hx9 : x / 10 ^ p % 10 ≠ 9 := by
    intro h9
    apply hxU
    rw [mem_biUnion]
    exact ⟨p, mem_Icc.mpr ⟨hp1, hp2⟩, by simp only [bad, M, mem_filter, mem_range]; exact ⟨hxM, h9⟩⟩
  have := Nat.mod_lt (x / 10 ^ p) (show 0 < 10 by norm_num)
  omega

theorem sliceC (k n : ℕ) (hk : 8 ≤ k) (hn : 0 < n) (hlt : n < 10 ^ k - 1)
    (hdvd : n ∣ 10 ^ (k + 1) - 1) :
    ∃ m < (10 ^ (9 * k) - 1) / 9, 0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 := by
  by_cases h9 : n ∣ 111111111
  · have h111 : ∑ i ∈ range 9, 10 ^ i = 111111111 := by norm_num [sum_range_succ]
    refine ⟨∑ i ∈ range 9, 10 ^ i, ?_, ?_, ?_, ?_⟩
    · rw [← geom10]
      exact sum_lt_sum_of_subset (range_mono (by omega)) (i := 9) (mem_range.mpr (by omega))
        (by simp) (by positivity) (fun _ _ _ => Nat.zero_le _)
    · rw [h111]; norm_num
    · rw [h111]; exact h9
    · have := digits01 9 (fun _ => 1) (fun _ => le_rfl)
      simpa using this
  · obtain ⟨x, hx0, hxT, hnx, hgood⟩ := good_exists k n hk hn hlt hdvd
    have ht0 : 0 < k + 1 := by omega
    have hx10 : x < 10 ^ (k + 1) := by omega
    have hvan : ∀ i, 9 * k ≤ i → i < 9 * (k + 1) → stk x (k + 1) i = 0 := by
      intro i h1 h2
      have e1 : i / (k + 1) = 8 := Nat.div_eq_of_lt_le (by omega) (by omega)
      have e2 : i % (k + 1) = i - 8 * (k + 1) := by
        have := Nat.div_add_mod i (k + 1)
        rw [e1] at this
        omega
      have hd := hgood (i % (k + 1)) (by omega) (by omega)
      unfold stk
      rw [e1, if_neg (by omega)]
    have hsum : ∑ i ∈ range (9 * k), stk x (k + 1) i * 10 ^ i
        = ∑ i ∈ range (9 * (k + 1)), stk x (k + 1) i * 10 ^ i := by
      apply sum_subset
      · intro i hi; rw [mem_range] at hi ⊢; omega
      · intro i hi hni
        rw [mem_range] at hi
        rw [mem_range, not_lt] at hni
        rw [hvan i hni hi, zero_mul]
    have hcong := stk_cong x (k + 1) ht0 hx10
    have hxe : ∑ j ∈ range (k + 1), (x / 10 ^ j % 10) * 10 ^ j = x := by
      rw [digit_expansion, Nat.mod_eq_of_lt hx10]
    refine ⟨∑ i ∈ range (9 * k), stk x (k + 1) i * 10 ^ i, ?_, ?_, ?_,
      digits01 _ _ (stk_le x (k + 1))⟩
    · by_contra hnot
      have hall : ∀ i, i < 9 * k → stk x (k + 1) i = 1 := by
        intro i hi
        by_contra h1
        have h0 : stk x (k + 1) i = 0 := by
          have := stk_le x (k + 1) i
          omega
        exact hnot (lt_repunit _ _ (stk_le x (k + 1)) i hi h0)
      have hd9 : ∀ j, j < k - 8 → x / 10 ^ j % 10 = 9 := by
        intro j hj
        have h := hall ((k + 1) * 8 + j) (by omega)
        rw [stk_block x (k + 1) ht0 8 j (by omega)] at h
        have := Nat.mod_lt (x / 10 ^ j) (show 0 < 10 by norm_num)
        (split_ifs at h with hc; omega)
      have hd8 : ∀ j, k - 8 ≤ j → j ≤ k → x / 10 ^ j % 10 = 8 := by
        intro j hj1 hj2
        have h := hall ((k + 1) * 7 + j) (by omega)
        rw [stk_block x (k + 1) ht0 7 j (by omega)] at h
        have := hgood j hj1 hj2
        (split_ifs at h with hc; omega)
      have hk9 : k + 1 = (k - 8) + 9 := by omega
      rw [hk9, sum_range_add] at hxe
      have hs1 : ∑ j ∈ range (k - 8), (x / 10 ^ j % 10) * 10 ^ j = 10 ^ (k - 8) - 1 := by
        rw [← nine_mul_geom10, mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [hd9 j (mem_range.mp hj)]
      have hs2 : ∑ s ∈ range 9, (x / 10 ^ (k - 8 + s) % 10) * 10 ^ (k - 8 + s)
          = 888888888 * 10 ^ (k - 8) := by
        have hterm : ∀ s ∈ range 9, (x / 10 ^ (k - 8 + s) % 10) * 10 ^ (k - 8 + s)
            = 8 * 10 ^ s * 10 ^ (k - 8) := by
          intro s hs
          have hs' := mem_range.mp hs
          rw [hd8 (k - 8 + s) (by omega) (by omega), pow_add]; ring
        rw [sum_congr rfl hterm, ← sum_mul]
        norm_num [sum_range_succ]
      rw [hs1, hs2] at hxe
      have hTe : 10 ^ (k + 1) = 1000000000 * 10 ^ (k - 8) := by
        rw [hk9, pow_add, mul_comm]; norm_num
      have hQ : 1 ≤ 10 ^ (k - 8) := Nat.one_le_pow _ _ (by norm_num)
      have hdiff : 10 ^ (k + 1) - 1 - x = 111111111 * 10 ^ (k - 8) := by omega
      have hd1 : n ∣ 111111111 * 10 ^ (k - 8) := by
        rw [← hdiff]; exact Nat.dvd_sub hdvd hnx
      have hcop10 : Nat.Coprime (10 ^ (k + 1) - 1) 10 := by
        have h1 : Nat.Coprime (10 ^ (k + 1) - 1) (10 ^ (k + 1) - 1 + 1) :=
          (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right _)
        rw [Nat.sub_add_cancel (by omega)] at h1
        exact Nat.Coprime.coprime_dvd_right (dvd_pow_self 10 (by omega)) h1
      have hcop : Nat.Coprime n (10 ^ (k - 8)) :=
        Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_left hdvd hcop10)
      exact h9 (hcop.dvd_of_dvd_mul_right hd1)
    · have hex : ∃ j, j < k + 1 ∧ 0 < x / 10 ^ j % 10 := by
        by_contra hcon
        push Not at hcon
        have h0 : ∀ j ∈ range (k + 1), (x / 10 ^ j % 10) * 10 ^ j = 0 := by
          intro j hj
          have := hcon j (mem_range.mp hj)
          rw [Nat.le_zero.mp this, zero_mul]
        rw [sum_eq_zero h0] at hxe
        omega
      obtain ⟨j, hj, hjpos⟩ := hex
      have hjm : j ∈ range (9 * k) := mem_range.mpr (by omega)
      have hle := single_le_sum (f := fun i => stk x (k + 1) i * 10 ^ i)
        (fun i _ => Nat.zero_le _) hjm
      have hfj : stk x (k + 1) j = 1 := by
        have h := stk_block x (k + 1) ht0 0 j hj
        rw [Nat.mul_zero, zero_add] at h
        rw [h, if_pos hjpos]
      have hpos : 0 < stk x (k + 1) j * 10 ^ j := by rw [hfj]; positivity
      exact lt_of_lt_of_le hpos hle
    · rw [hsum]
      exact (Nat.modEq_zero_iff_dvd).mp
        ((Nat.ModEq.of_dvd hdvd hcong).trans ((Nat.modEq_zero_iff_dvd).mpr hnx))


end OMA.A4290next

theorem OMA.solution : OMA.R_OeisA4290_conjecture_R1_H1_R1_H3_R1.H3 := by
  intro k n hk hn hlt hdvd
  exact OMA.A4290next.sliceC k n hk hn hlt hdvd
