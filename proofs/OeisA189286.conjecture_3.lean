import FormalConjectures.OEIS.«189286»

/-
Copyright 2026 The Formal Conjectures Authors and Yuto Nakahara.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
The exact valuation below follows from Zhi-Hong Sun's convolution recurrence.
The integrality and binary-digit lemmas are adapted, under Apache 2.0, from
Yuto Nakahara's project (with Gemini 4 Neon), PALOMAR-2026-11-22-000013,
commit 10c9f2d2514e13715dfdfea20acf628bbdcd8c78.
Varun Dudipala's November 18, 2026 public proof already gives the exact formula
in A189286.lean (hv_q), commit 3241c0eb195e3a721af082facc886957b41f44f4.
Nakahara independently proved parity. Tom Adamczewski's OEIS Open had previously
proved integrality. The four additional namespaces in this file give another
derivation of the exact formula and use it to prove the catalogue statement.
-/

namespace A189286Published

open OeisA189286

def tNat (k : ℕ) : ℕ := (6 * k).choose (3 * k) * (3 * k).choose k

def sNat (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), tNat k * tNat (n - k)

lemma tNat_pos (k : ℕ) : 0 < tNat k :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))

lemma sNat_pos (n : ℕ) : 0 < sNat n :=
  Finset.sum_pos (fun k _ => Nat.mul_pos (tNat_pos k) (tNat_pos (n - k)))
    ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩

lemma denom_pos {n : ℕ} (hn : 0 < n) : 0 < (2 * n - 1) * (3 * n).choose n :=
  Nat.mul_pos (by omega) (Nat.choose_pos (by omega))

lemma a_eq_div_nat {n : ℕ} (hn : 0 < n) :
    a n = (sNat n : ℚ) / (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) := by
  unfold a sNat tTerm
  have hsub : ((2 * n - 1 : ℕ) : ℚ) = 2 * (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  simp only [tNat, Nat.cast_sum, Nat.cast_mul, hsub]

lemma tNat_mul_factorials (k : ℕ) :
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial = (6 * k).factorial := by
  have h1 : (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial = (6 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 6 * k) (k := 3 * k) (by omega)
    rwa [show 6 * k - 3 * k = 3 * k by omega] at this
  have h2 : (3 * k).choose k * k.factorial * (2 * k).factorial = (3 * k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := 3 * k) (k := k) (by omega)
    rwa [show 3 * k - k = 2 * k by omega] at this
  calc
    tNat k * (3 * k).factorial * (2 * k).factorial * k.factorial
        = (6 * k).choose (3 * k) * (3 * k).factorial *
            ((3 * k).choose k * k.factorial * (2 * k).factorial) := by
            unfold tNat; ring
    _ = (6 * k).choose (3 * k) * (3 * k).factorial * (3 * k).factorial := by rw [h2]
    _ = (6 * k).factorial := h1

lemma choose_3n_mul_factorials (n : ℕ) :
    (3 * n).choose n * n.factorial * (2 * n).factorial = (3 * n).factorial := by
  have := Nat.choose_mul_factorial_mul_factorial (n := 3 * n) (k := n) (by omega)
  rwa [show 3 * n - n = 2 * n by omega] at this

def fStep (q r : ℕ) : ℕ := 6 * r / q - 3 * r / q - 2 * r / q

def gStep (q r : ℕ) : ℕ := 3 * r / q - 2 * r / q

lemma nat_div_eq_of_le_lt {q m j : ℕ} (hq : 0 < q)
    (h1 : j * q ≤ m) (h2 : m < (j + 1) * q) : m / q = j :=
  le_antisymm (Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hq).mpr h2))
    ((Nat.le_div_iff_mul_le hq).mpr h1)

lemma fStep_spec {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    3 * r / q + 2 * r / q ≤ 6 * r / q ∧
    fStep q r = if 6 * r < q then 0 else if 6 * r < 5 * q then 1 else 2 := by
  unfold fStep
  by_cases h1 : 6 * r < q
  · have h6 : 6 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h2 : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    simp [h1, h6, h3, h2]
  · by_cases h2 : 6 * r < 2 * q
    · have h6 : 6 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      rw [if_neg h1, if_pos (by omega)]
      omega
    · by_cases h3 : 6 * r < 3 * q
      · have h6 : 6 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_neg h1, if_pos (by omega)]
        omega
      · by_cases h4 : 6 * r < 4 * q
        · have h6 : 6 * r / q = 3 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
          rw [if_neg h1, if_pos (by omega)]
          omega
        · by_cases h5 : 6 * r < 5 * q
          · have h6 : 6 * r / q = 4 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            rw [if_neg h1, if_pos h5]
            omega
          · have h6 : 6 * r / q = 5 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
            rw [if_neg h1, if_neg h5]
            omega

lemma gStep_spec {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    2 * r / q ≤ 3 * r / q ∧
    gStep q r = if (2 * q ≤ 6 * r ∧ 6 * r < 3 * q) ∨ 4 * q ≤ 6 * r then 1 else 0 := by
  unfold gStep
  by_cases h1 : 6 * r < 2 * q
  · have h3 : 3 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    have h2 : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
    rw [if_neg (by omega)]
    omega
  · by_cases h2 : 6 * r < 3 * q
    · have h3 : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      have h2' : 2 * r / q = 0 := nat_div_eq_of_le_lt hq (by omega) (by omega)
      rw [if_pos (by omega)]
      omega
    · by_cases h3 : 6 * r < 4 * q
      · have h3' : 3 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_neg (by omega)]
        omega
      · have h3' : 3 * r / q = 2 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        have h2' : 2 * r / q = 1 := nat_div_eq_of_le_lt hq (by omega) (by omega)
        rw [if_pos (by omega)]
        omega

lemma div_six_eq {q a : ℕ} (hq : 0 < q) :
    6 * a / q = 3 * a / q + 2 * a / q + a / q + fStep q (a % q) := by
  have hmul : ∀ c : ℕ, c * a / q = c * (a / q) + c * (a % q) / q := by
    intro c
    have hda : q * (a / q) + a % q = a := Nat.div_add_mod a q
    have heq : c * a = c * (a % q) + q * (c * (a / q)) := by
      calc c * a = c * (q * (a / q) + a % q) := by rw [hda]
        _ = c * (a % q) + q * (c * (a / q)) := by ring
    rw [heq, Nat.add_mul_div_left _ _ hq]
    omega
  have hle := (fStep_spec hq (Nat.mod_lt a hq)).1
  have h6 := hmul 6
  have h3 := hmul 3
  have h2 := hmul 2
  unfold fStep
  omega

lemma div_three_eq {q a : ℕ} (hq : 0 < q) :
    3 * a / q = 2 * a / q + a / q + gStep q (a % q) := by
  have hmul : ∀ c : ℕ, c * a / q = c * (a / q) + c * (a % q) / q := by
    intro c
    have hda : q * (a / q) + a % q = a := Nat.div_add_mod a q
    have heq : c * a = c * (a % q) + q * (c * (a / q)) := by
      calc c * a = c * (q * (a / q) + a % q) := by rw [hda]
        _ = c * (a % q) + q * (c * (a / q)) := by ring
    rw [heq, Nat.add_mul_div_left _ _ hq]
    omega
  have hle := (gStep_spec hq (Nat.mod_lt a hq)).1
  have h3 := hmul 3
  have h2 := hmul 2
  unfold gStep
  omega

lemma padicValNat_tNat_eq_sum {p k b : ℕ} [hp : Fact p.Prime]
    (hb : Nat.log p (6 * k) < b) :
    padicValNat p (tNat k) = ∑ i ∈ Finset.Ico 1 b, fStep (p ^ i) (k % p ^ i) := by
  have hfac := congrArg (padicValNat p) (tNat_mul_factorials k)
  rw [padicValNat.mul
        (mul_ne_zero (mul_ne_zero (tNat_pos k).ne' (Nat.factorial_ne_zero _))
          (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (mul_ne_zero (tNat_pos k).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (tNat_pos k).ne' (Nat.factorial_ne_zero _)] at hfac
  rw [padicValNat_factorial hb,
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 b, 6 * k / p ^ i =
      ∑ i ∈ Finset.Ico 1 b, (3 * k / p ^ i + 2 * k / p ^ i + k / p ^ i +
        fStep (p ^ i) (k % p ^ i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_six_eq (pow_pos hp.out.pos i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hfac
  omega

lemma padicValNat_choose_3n_eq_sum {p n b : ℕ} [hp : Fact p.Prime]
    (hb : Nat.log p (3 * n) < b) :
    padicValNat p ((3 * n).choose n) = ∑ i ∈ Finset.Ico 1 b, gStep (p ^ i) (n % p ^ i) := by
  have hfac := congrArg (padicValNat p) (choose_3n_mul_factorials n)
  rw [padicValNat.mul (mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _)] at hfac
  rw [padicValNat_factorial hb,
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb),
      padicValNat_factorial (lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb)] at hfac
  have hsum : ∑ i ∈ Finset.Ico 1 b, 3 * n / p ^ i =
      ∑ i ∈ Finset.Ico 1 b, (2 * n / p ^ i + n / p ^ i + gStep (p ^ i) (n % p ^ i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact div_three_eq (pow_pos hp.out.pos i)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib] at hfac
  omega

lemma padicValNat_eq_sum_ite_dvd {p x b : ℕ} [hp : Fact p.Prime]
    (hx : 0 < x) (hb : Nat.log p x < b) :
    padicValNat p x = ∑ i ∈ Finset.Ico 1 b, if p ^ i ∣ x then 1 else 0 := by
  have hr : padicValNat p x < b := lt_of_le_of_lt (padicValNat_le_nat_log x) hb
  have hfilt : (Finset.Ico 1 b).filter (fun i => p ^ i ∣ x) =
      Finset.Ico 1 (padicValNat p x + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_Ico, padicValNat_dvd_iff_le hx.ne']
    omega
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
      hfilt, Nat.card_Ico]
  omega

lemma gStep_le_fStep_add {q k m : ℕ} (hq : 0 < q) :
    gStep q ((k + m) % q) ≤ fStep q (k % q) + fStep q (m % q) := by
  have hfk := (fStep_spec hq (Nat.mod_lt k hq)).2
  have hfm := (fStep_spec hq (Nat.mod_lt m hq)).2
  have hgn := (gStep_spec hq (Nat.mod_lt (k + m) hq)).2
  have hmod : (k + m) % q = (k % q + m % q) % q := Nat.add_mod k m q
  by_cases hkm : k % q + m % q < q
  · rw [Nat.mod_eq_of_lt hkm] at hmod
    rw [hmod] at hgn ⊢
    split_ifs at hfk hfm hgn <;> omega
  · have hsub : (k + m) % q = k % q + m % q - q := by
      have hklt := Nat.mod_lt k hq
      have hmlt := Nat.mod_lt m hq
      rw [hmod, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hgn ⊢
    have hklt := Nat.mod_lt k hq
    have hmlt := Nat.mod_lt m hq
    split_ifs at hfk hfm hgn <;> omega

lemma two_mul_mod_of_dvd {q n : ℕ} (hn : 0 < n) (hq : 2 ≤ q) (hdiv : q ∣ 2 * n - 1) :
    2 * (n % q) = q + 1 := by
  rcases hdiv with ⟨c, hc⟩
  have hr : n % q < q := Nat.mod_lt n (by omega)
  have hdivmod : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have h2n : 2 * n = q * c + 1 := by omega
  have heq : q * c + 1 = 2 * (q * (n / q)) + 2 * (n % q) := by linarith
  have h1 : c < 2 * (n / q) + 2 := by nlinarith
  have h2 : 2 * (n / q) ≤ c := by
    by_contra hlt
    have hle : c + 1 ≤ 2 * (n / q) := by omega
    have hmul : q * c + q ≤ 2 * (q * (n / q)) := by
      calc q * c + q = q * (c + 1) := by ring
        _ ≤ q * (2 * (n / q)) := Nat.mul_le_mul_left q hle
        _ = 2 * (q * (n / q)) := by ring
    omega
  have hne : c ≠ 2 * (n / q) := by
    intro h
    rw [h] at heq
    have : 2 * (n % q) = 1 := by linarith
    omega
  have hc_eq : c = 2 * (n / q) + 1 := by omega
  rw [hc_eq] at heq
  linarith

lemma dvd_of_two_mul_mod {q n : ℕ} (hn : 0 < n) (hmod : 2 * (n % q) = q + 1) :
    q ∣ 2 * n - 1 := by
  refine ⟨2 * (n / q) + 1, ?_⟩
  have hdivmod : q * (n / q) + n % q = n := Nat.div_add_mod n q
  have : 2 * n = q * (2 * (n / q) + 1) + 1 := by linarith
  omega

lemma gStep_add_one_le_fStep_add {q k m : ℕ} (hq : 5 ≤ q) (hn : 0 < k + m)
    (hdiv : q ∣ 2 * (k + m) - 1) :
    1 + gStep q ((k + m) % q) ≤ fStep q (k % q) + fStep q (m % q) := by
  have hqpos : 0 < q := by omega
  have h2 := two_mul_mod_of_dvd hn (by omega) hdiv
  have hgn := (gStep_spec hqpos (Nat.mod_lt (k + m) hqpos)).2
  have hg0 : gStep q ((k + m) % q) = 0 := by
    rw [hgn, if_neg (by omega)]
  rw [hg0, add_zero]
  have hfk := (fStep_spec hqpos (Nat.mod_lt k hqpos)).2
  have hfm := (fStep_spec hqpos (Nat.mod_lt m hqpos)).2
  by_contra hlt
  have hfk0 : fStep q (k % q) = 0 := by omega
  have hfm0 : fStep q (m % q) = 0 := by omega
  have hksmall : 6 * (k % q) < q := by
    by_contra h
    rw [hfk, if_neg h] at hfk0
    by_cases h5 : 6 * (k % q) < 5 * q
    · rw [if_pos h5] at hfk0; omega
    · rw [if_neg h5] at hfk0; omega
  have hmsmall : 6 * (m % q) < q := by
    by_contra h
    rw [hfm, if_neg h] at hfm0
    by_cases h5 : 6 * (m % q) < 5 * q
    · rw [if_pos h5] at hfm0; omega
    · rw [if_neg h5] at hfm0; omega
  have hmod : (k + m) % q = k % q + m % q := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega)]
  omega

lemma mod_three_mul {q a : ℕ} (hq : 0 < q) :
    a % (3 * q) = ((a / q) % 3) * q + a % q := by
  have h1 : q * (a / q) + a % q = a := Nat.div_add_mod a q
  have h2 : 3 * ((a / q) / 3) + (a / q) % 3 = a / q := Nat.div_add_mod (a / q) 3
  have h3 : (a / q) % 3 < 3 := Nat.mod_lt _ (by omega)
  have h4 : a % q < q := Nat.mod_lt _ hq
  have hlt : ((a / q) % 3) * q + a % q < 3 * q := by nlinarith
  have heq : a = ((a / q) % 3 * q + a % q) + (3 * q) * ((a / q) / 3) := by nlinarith
  conv_lhs => rw [heq]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

lemma exists_surplus_base3_aux {k m : ℕ} (hn : 0 < k + m)
    (hk3 : k % 3 = 0) (hm3 : m % 3 = 2) :
    ∃ j ∈ Finset.Ico 2 (padicValNat 3 (2 * (k + m) - 1) + 2),
      (if 3 ^ j ∣ 2 * (k + m) - 1 then 1 else 0) + gStep (3 ^ j) ((k + m) % 3 ^ j) + 1 ≤
        fStep (3 ^ j) (k % 3 ^ j) + fStep (3 ^ j) (m % 3 ^ j) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set n := k + m
  set r := padicValNat 3 (2 * n - 1)
  have h3dvd : 3 ∣ 2 * n - 1 := by
    refine dvd_of_two_mul_mod hn ?_
    have : n % 3 = (k % 3 + m % 3) % 3 := Nat.add_mod k m 3
    omega
  have hr1 : 1 ≤ r := one_le_padicValNat_of_dvd (by omega) h3dvd
  by_contra hnone
  push Not at hnone
  have hstep : ∀ j, 1 ≤ j → j ≤ r → k % 3 ^ j = 0 ∧ 2 * (m % 3 ^ j) = 3 ^ j + 1 := by
    intro j hj1 hjr
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hj0 : j = 0
      · subst hj0
        simpa using ⟨hk3, by omega⟩
      · have ⟨hkj, hmj⟩ := ih (by omega) (by omega)
        set q := 3 ^ j
        have hqpos : 0 < q := pow_pos (by omega : 0 < 3) j
        have h3q : 3 ^ (j + 1) = 3 * q := by rw [pow_succ']
        have h3q_pos : 0 < 3 ^ (j + 1) := pow_pos (by omega : 0 < 3) (j + 1)
        have h3q_ge : 5 ≤ 3 ^ (j + 1) := by
          have : 3 ^ 2 ≤ 3 ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hdvd_next : 3 ^ (j + 1) ∣ 2 * n - 1 :=
          (padicValNat_dvd_iff_le (p := 3) (by omega)).mpr hjr
        have hgn0 : gStep (3 ^ (j + 1)) (n % 3 ^ (j + 1)) = 0 := by
          have h2n := two_mul_mod_of_dvd hn (by omega) hdvd_next
          have hgs := (gStep_spec h3q_pos (Nat.mod_lt n h3q_pos)).2
          rw [hgs, if_neg (by omega)]
        have hbound := hnone (j + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        rw [if_pos hdvd_next, hgn0, add_zero] at hbound
        have hk_next : k % (3 * q) = ((k / q) % 3) * q := by
          rw [mod_three_mul hqpos, hkj, add_zero]
        have hm_next : m % (3 * q) = ((m / q) % 3) * q + m % q := mod_three_mul hqpos
        have hfm_ge : 1 ≤ fStep (3 ^ (j + 1)) (m % 3 ^ (j + 1)) := by
          have hfs := (fStep_spec h3q_pos (Nat.mod_lt m h3q_pos)).2
          rw [h3q, hm_next] at hfs ⊢
          have h6m : 3 * q ≤ 6 * (((m / q) % 3) * q + m % q) := by
            have : 0 ≤ ((m / q) % 3) * q := Nat.zero_le _
            omega
          rw [hfs, if_neg (by omega)]
          split_ifs <;> omega
        have hfk_eq0 : fStep (3 ^ (j + 1)) (k % 3 ^ (j + 1)) = 0 := by omega
        have hdk0 : (k / q) % 3 = 0 := by
          have hfs := (fStep_spec h3q_pos (Nat.mod_lt k h3q_pos)).2
          rw [h3q, hk_next] at hfs hfk_eq0
          have hlt : 6 * (((k / q) % 3) * q) < 3 * q := by
            by_contra hge
            rw [hfs, if_neg hge] at hfk_eq0
            by_cases h5 : 6 * (((k / q) % 3) * q) < 5 * (3 * q)
            · rw [if_pos h5] at hfk_eq0; omega
            · rw [if_neg h5] at hfk_eq0; omega
          by_contra hne
          have h1 : 1 ≤ (k / q) % 3 := by omega
          have hmul : 1 * q ≤ ((k / q) % 3) * q := Nat.mul_le_mul_right q h1
          omega
        have hk_zero : k % 3 ^ (j + 1) = 0 := by rw [h3q, hk_next, hdk0, zero_mul]
        have hm_eq : m % 3 ^ (j + 1) = n % 3 ^ (j + 1) := by
          have hmod : n % 3 ^ (j + 1) = (k % 3 ^ (j + 1) + m % 3 ^ (j + 1)) % 3 ^ (j + 1) :=
            Nat.add_mod k m _
          rw [hk_zero, zero_add, Nat.mod_mod] at hmod
          exact hmod.symm
        exact ⟨hk_zero, hm_eq.symm ▸ two_mul_mod_of_dvd hn (by omega) hdvd_next⟩
  have ⟨hkr, hmr⟩ := hstep r hr1 le_rfl
  set q := 3 ^ r
  have hq3 : 3 ≤ q := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by omega) hr1
  have hqpos : 0 < q := by omega
  have h3q : 3 ^ (r + 1) = 3 * q := by rw [pow_succ']
  have hndvd : ¬ 3 ^ (r + 1) ∣ 2 * n - 1 := pow_succ_padicValNat_not_dvd (p := 3) (by omega)
  have hbound := hnone (r + 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  rw [if_neg hndvd, zero_add, h3q] at hbound
  set dk := (k / q) % 3
  set dm := (m / q) % 3
  have hdk_lt : dk < 3 := Nat.mod_lt _ (by omega)
  have hdm_lt : dm < 3 := Nat.mod_lt _ (by omega)
  have hk_next : k % (3 * q) = dk * q := by rw [mod_three_mul hqpos, hkr, add_zero]
  have hm_next : m % (3 * q) = dm * q + m % q := mod_three_mul hqpos
  have hn_next : n % (3 * q) = ((dk + dm) % 3) * q + m % q := by
    have hmq_lt : m % q < q := Nat.mod_lt m hqpos
    have h1 : n % (3 * q) = (k % (3 * q) + m % (3 * q)) % (3 * q) := Nat.add_mod k m _
    rw [hk_next, hm_next] at h1
    have h2 : dk * q + (dm * q + m % q) =
        (((dk + dm) % 3) * q + m % q) + (3 * q) * ((dk + dm) / 3) := by
      have := Nat.div_add_mod (dk + dm) 3
      nlinarith
    have h3 : ((dk + dm) % 3) * q + m % q < 3 * q := by
      have : (dk + dm) % 3 < 3 := Nat.mod_lt _ (by omega)
      nlinarith
    rw [h1, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h3]
  have hneq1 : (dk + dm) % 3 ≠ 1 := by
    intro h1
    apply hndvd
    rw [h3q]
    refine dvd_of_two_mul_mod hn ?_
    rw [hn_next, h1]
    omega
  have hfk := (fStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt k (by omega))).2
  have hfm := (fStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt m (by omega))).2
  have hgn := (gStep_spec (by omega : 0 < 3 * q) (Nat.mod_lt n (by omega))).2
  rw [hk_next, hm_next, hn_next] at hbound
  rw [hk_next] at hfk
  rw [hm_next] at hfm
  rw [hn_next] at hgn
  interval_cases dk <;> interval_cases dm <;>
    simp only [Nat.reduceAdd, Nat.reduceMod, zero_mul, one_mul, zero_add] at hneq1 hbound hfk hfm hgn ⊢
  all_goals
    try exact absurd rfl hneq1
  all_goals
    split_ifs at hfk hfm hgn <;> omega

lemma padicValNat_denom_le_tNat_mul {p n k m : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hkm : k + m = n) :
    padicValNat p ((2 * n - 1) * (3 * n).choose n) ≤ padicValNat p (tNat k * tNat m) := by
  have : Fact p.Prime := ⟨hp⟩
  set b := Nat.log p (6 * n) + 1
  have hb6n : Nat.log p (6 * n) < b := Nat.lt_succ_self _
  have hb6k : Nat.log p (6 * k) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb6m : Nat.log p (6 * m) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb3n : Nat.log p (3 * n) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  have hb2n : Nat.log p (2 * n - 1) < b := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hb6n
  rw [padicValNat.mul (by omega) (Nat.choose_pos (by omega)).ne',
      padicValNat.mul (tNat_pos k).ne' (tNat_pos m).ne',
      padicValNat_eq_sum_ite_dvd (by omega) hb2n,
      padicValNat_choose_3n_eq_sum hb3n,
      padicValNat_tNat_eq_sum hb6k,
      padicValNat_tNat_eq_sum hb6m,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  by_cases h3 : p = 3 ∧ 3 ∣ 2 * n - 1
  · rcases h3 with ⟨rfl, h3dvd⟩
    set L : ℕ → ℕ := fun i => (if 3 ^ i ∣ 2 * n - 1 then 1 else 0) + gStep (3 ^ i) (n % 3 ^ i)
    set R : ℕ → ℕ := fun i => fStep (3 ^ i) (k % 3 ^ i) + fStep (3 ^ i) (m % 3 ^ i)
    change ∑ i ∈ Finset.Ico 1 b, L i ≤ ∑ i ∈ Finset.Ico 1 b, R i
    have hge2 : ∀ i ∈ Finset.Ico 2 b, L i ≤ R i := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      dsimp only [L, R]
      by_cases hd : 3 ^ i ∣ 2 * n - 1
      · rw [if_pos hd, ← hkm]
        have h3i_ge : 5 ≤ 3 ^ i := by
          have : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by omega) hi.1
          omega
        exact gStep_add_one_le_fStep_add h3i_ge (by omega) (hkm ▸ hd)
      · rw [if_neg hd, zero_add, ← hkm]
        exact gStep_le_fStep_add (pow_pos (by omega : 0 < 3) i)
    by_cases hL1 : L 1 ≤ R 1
    · refine Finset.sum_le_sum fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      by_cases hi1 : i = 1
      · subst hi1; exact hL1
      · exact hge2 i (Finset.mem_Ico.mpr ⟨by omega, hi.2⟩)
    · have h2n3 : n % 3 = 2 := by
        have := two_mul_mod_of_dvd hn (by omega) h3dvd
        omega
      have hL1_val : L 1 = 2 := by
        dsimp only [L]
        rw [pow_one, if_pos h3dvd, h2n3]
        decide
      have hk3_lt : k % 3 < 3 := Nat.mod_lt k (by omega)
      have hm3_lt : m % 3 < 3 := Nat.mod_lt m (by omega)
      have hkm3 : (k % 3 + m % 3) % 3 = 2 := by
        rw [← Nat.add_mod, hkm, h2n3]
      have hfk1 := (fStep_spec (q := 3) (r := k % 3) (by omega) hk3_lt).2
      have hfm1 := (fStep_spec (q := 3) (r := m % 3) (by omega) hm3_lt).2
      have hcases : (k % 3 = 0 ∧ m % 3 = 2) ∨ (k % 3 = 2 ∧ m % 3 = 0) := by
        have hR1 : R 1 < 2 := by omega
        dsimp only [R] at hR1
        rw [pow_one] at hR1
        split_ifs at hfk1 hfm1 <;> omega
      have hR1_val : R 1 = 1 := by
        dsimp only [R]
        rw [pow_one]
        rcases hcases with ⟨hk0, hm2⟩ | ⟨hk2, hm0⟩
        · rw [hk0, hm2]; decide
        · rw [hk2, hm0]; decide
      have hsurplus : ∃ j ∈ Finset.Ico 2 (padicValNat 3 (2 * n - 1) + 2), L j + 1 ≤ R j := by
        rcases hcases with ⟨hk0, hm2⟩ | ⟨hk2, hm0⟩
        · obtain ⟨j, hj, hle⟩ := exists_surplus_base3_aux (k := k) (m := m) (by omega) hk0 hm2
          exact ⟨j, by rwa [hkm] at hj, by simpa only [L, R, hkm] using hle⟩
        · obtain ⟨j, hj, hle⟩ := exists_surplus_base3_aux (k := m) (m := k) (by omega) hm0 hk2
          refine ⟨j, by rwa [add_comm m k, hkm] at hj, ?_⟩
          dsimp only [L, R]
          rw [add_comm m k, hkm] at hle
          omega
      obtain ⟨j, hj_mem, hj_surp⟩ := hsurplus
      rw [Finset.mem_Ico] at hj_mem
      have hr_pow : 3 ^ (padicValNat 3 (2 * n - 1) + 1) ≤ 6 * n := by
        have hpow_dvd : 3 ^ padicValNat 3 (2 * n - 1) ∣ 2 * n - 1 := pow_padicValNat_dvd
        have hle : 3 ^ padicValNat 3 (2 * n - 1) ≤ 2 * n - 1 := Nat.le_of_dvd (by omega) hpow_dvd
        rw [pow_succ']
        omega
      have hr_lt_b : padicValNat 3 (2 * n - 1) + 1 < b :=
        Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by omega) hr_pow)
      have hj_in : j ∈ Finset.Ico 2 b := Finset.mem_Ico.mpr ⟨hj_mem.1, by omega⟩
      have h1b : 1 < b := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot h1b, Finset.sum_eq_sum_Ico_succ_bot h1b]
      rw [← Finset.add_sum_erase _ _ hj_in, ← Finset.add_sum_erase _ _ hj_in]
      have hrest : ∑ i ∈ (Finset.Ico 2 b).erase j, L i ≤ ∑ i ∈ (Finset.Ico 2 b).erase j, R i :=
        Finset.sum_le_sum fun i hi => hge2 i (Finset.mem_of_mem_erase hi)
      omega
  · refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    by_cases hd : p ^ i ∣ 2 * n - 1
    · rw [if_pos hd, ← hkm]
      have hp_dvd : p ∣ 2 * n - 1 := dvd_trans (dvd_pow_self p (by omega)) hd
      have hp2 : p ≠ 2 := by
        intro h2
        rw [h2] at hp_dvd
        omega
      have hp3 : p ≠ 3 := fun h3' => h3 ⟨h3', h3' ▸ hp_dvd⟩
      have hp5 : 5 ≤ p := by
        have := hp.two_le
        have hne4 : p ≠ 4 := by intro h4; rw [h4] at hp; exact absurd hp (by decide)
        omega
      have hpi5 : 5 ≤ p ^ i :=
        le_trans hp5 (by simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hi.1)
      exact gStep_add_one_le_fStep_add hpi5 (by omega) (hkm ▸ hd)
    · rw [if_neg hd, zero_add, ← hkm]
      exact gStep_le_fStep_add (pow_pos hp.pos i)

lemma denom_dvd_tNat_mul {n k m : ℕ} (hn : 0 < n) (hkm : k + m = n) :
    (2 * n - 1) * (3 * n).choose n ∣ tNat k * tNat m := by
  rw [← Nat.factorization_le_iff_dvd (denom_pos hn).ne'
      (Nat.mul_pos (tNat_pos k) (tNat_pos m)).ne']
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    exact padicValNat_denom_le_tNat_mul hp hn hkm
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

lemma denom_dvd_sNat {n : ℕ} (hn : 0 < n) :
    (2 * n - 1) * (3 * n).choose n ∣ sNat n := by
  unfold sNat
  refine Finset.dvd_sum fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact denom_dvd_tNat_mul hn (Nat.add_sub_of_le hkn)

/--
Conjecture: $a(n)$ is an integer for every $n = 0, 1, 2, \dots$.
- _Zhi-Wei Sun_, Apr 19 2011

Proved in the OEIS Open project, see T. Adamczewski, OEIS Open: How many conjectures can
language models turn into theorems?, [arXiv:2608.11941](https://arxiv.org/abs/2608.11941).
-/
lemma integralTerms (n : ℕ) : (a n).den = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [a_0]; rfl
  · obtain ⟨q, hq⟩ := denom_dvd_sNat hn
    have hd : (((2 * n - 1) * (3 * n).choose n : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (denom_pos hn).ne'
    have han : a n = (q : ℚ) := by
      rw [a_eq_div_nat hn, hq, Nat.cast_mul, mul_div_cancel_left₀ _ hd]
    rw [han]
    exact Rat.den_natCast q


def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

lemma s2_zero : s2 0 = 0 := by simp [s2]

lemma s2_two_mul (n : ℕ) : s2 (2 * n) = s2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [s2]
  · unfold s2
    rw [show 2 * n = 0 + 2 * n by omega,
        Nat.digits_add 2 (by omega) 0 n (by omega) (Or.inr hn)]
    simp

lemma s2_two_mul_add_one (n : ℕ) : s2 (2 * n + 1) = s2 n + 1 := by
  unfold s2
  rw [show 2 * n + 1 = 1 + 2 * n by omega,
      Nat.digits_add 2 (by omega) 1 n (by omega) (Or.inl one_ne_zero)]
  simp [add_comm]

lemma s2_pos {n : ℕ} (hn : 0 < n) : 0 < s2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hmod : n % 2 = 0
    · have hhalf : 0 < n / 2 := by omega
      have heq : n = 2 * (n / 2) := by omega
      rw [heq, s2_two_mul]
      exact ih (n / 2) (by omega) hhalf
    · have heq : n = 2 * (n / 2) + 1 := by omega
      rw [heq, s2_two_mul_add_one]
      omega

lemma s2_eq_one_iff (n : ℕ) : s2 n = 1 ↔ ∃ k : ℕ, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [s2_zero, zero_ne_one, false_iff, not_exists]
      intro k
      exact (pow_pos (by omega : 0 < 2) k).ne
    · by_cases hmod : n % 2 = 0
      · have heq : n = 2 * (n / 2) := by omega
        rw [heq, s2_two_mul, ih (n / 2) (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          exact ⟨k + 1, by rw [hk, pow_succ']⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero => omega
          | succ k =>
            rw [pow_succ'] at hk
            exact ⟨k, by omega⟩
      · have heq : n = 2 * (n / 2) + 1 := by omega
        rw [heq, s2_two_mul_add_one]
        constructor
        · intro h
          have h0 : n / 2 = 0 := by
            by_contra hne
            have := s2_pos (Nat.pos_of_ne_zero hne)
            omega
          exact ⟨0, by omega⟩
        · rintro ⟨k, hk⟩
          cases k with
          | zero =>
            have h0 : n / 2 = 0 := by omega
            simp [h0, s2_zero]
          | succ k =>
            rw [pow_succ'] at hk
            omega

lemma two_le_s2_three_mul {n : ℕ} (hn : 0 < n) : 2 ≤ s2 (3 * n) := by
  have hpos : 0 < s2 (3 * n) := s2_pos (by omega)
  by_contra hlt
  have h1 : s2 (3 * n) = 1 := by omega
  obtain ⟨k, hk⟩ := (s2_eq_one_iff (3 * n)).mp h1
  have h3dvd : 3 ∣ 2 ^ k := ⟨n, hk.symm⟩
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd
  omega

lemma s2_three_mul_two_pow (k : ℕ) : s2 (3 * 2 ^ k) = 2 := by
  induction k with
  | zero =>
    rw [pow_zero, mul_one]
    decide
  | succ k ih =>
    rw [pow_succ', ← mul_assoc, mul_comm 3 2, mul_assoc, s2_two_mul, ih]

end A189286Published

/-
# The exact power of two in OEIS A189286

For the original binomial convolution at every positive index, the exponent
of two is the sum of the binary digit sums of n and 3n. The main statement
is A189286Exact.exactValuation, at the end of this file.

The algebraic certificate for the convolution is from Zhi-Hong Sun,
Legendre polynomials and supercongruences, Acta Arithmetica 159 (2013),
Lemma 3.1, DOI 10.4064/aa159-2-6. Both the summand identity and its
boundary term are proved below. The proof derives the recurrence, verifies
its normalization modulo four, and applies Legendre's factorial formula.
-/


namespace A189286Certificate

def ratio (t : ℚ) : ℚ := 12 * (6 * t + 1) * (6 * t + 5) / (t + 1) ^ 2

def cert (m k : ℚ) : ℚ :=
  12 * k ^ 2 * (36 * m ^ 2 - 36 * k * m + 129 * m - 62 * k + 114) / (m + 2 - k) ^ 2

def b (m : ℚ) : ℚ := 24 * (2 * m + 3) * (18 * m ^ 2 + 54 * m + 41)
def c (m : ℚ) : ℚ := 20736 * (m + 1) * (3 * m + 1) * (3 * m + 5)

theorem telescope (k l : ℚ) (hk : 0 ≤ k) (hl : 0 ≤ l) :
    (k + l + 2) ^ 3 * ratio (l + 1) * ratio l - b (k + l) * ratio l + c (k + l) =
      cert (k + l) (k + 1) * ratio k - cert (k + l) k * ratio l := by
  unfold ratio cert b c
  rw [show k + l + 2 - (k + 1) = l + 1 by ring, show k + l + 2 - k = l + 2 by ring]
  field_simp
  ring

theorem endpoint (m : ℚ) (hm : 0 ≤ m) :
    cert m (m + 1) + (m + 2) ^ 3 * (ratio (m + 1) + 60) - b m = 0 := by
  unfold cert ratio b
  rw [show m + 2 - (m + 1) = 1 by ring]
  field_simp
  ring

def convolution (t : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (m + 1), t k * t (m - k)

def flux (t : ℕ → ℚ) (m k : ℕ) : ℚ :=
  cert (m : ℚ) (k : ℚ) * t k * t (m + 1 - k)

lemma flux_difference (t : ℕ → ℚ)
    (step : ∀ n : ℕ, t (n + 1) = ratio n * t n) {m k : ℕ} (hk : k ≤ m) :
    ((m : ℚ) + 2)^3 * (t k * t (m + 2 - k)) -
      b m * (t k * t (m + 1 - k)) + c m * (t k * t (m-k)) =
    flux t m (k+1) - flux t m k := by
  let l := m - k
  have hm : m = k + l := by dsimp [l]; omega
  have hmq : (m : ℚ) = (k : ℚ) + (l : ℚ) := by exact_mod_cast hm
  have h := congrArg (fun v : ℚ => v * t k * t l)
    (telescope (k : ℚ) (l : ℚ) (by positivity) (by positivity))
  unfold flux
  rw [show m + 2 - k = (l + 1) + 1 by dsimp [l]; omega,
      show m + 1 - k = l + 1 by dsimp [l]; omega,
      show m + 1 - (k+1) = l by dsimp [l]; omega]
  change _ + c m * (t k * t l) = _
  rw [step (l+1), step l, step k, hmq]
  push_cast
  convert h using 1 <;> ring

theorem convolution_recurrence (t : ℕ → ℚ) (t0 : t 0 = 1)
    (step : ∀ n : ℕ, t (n + 1) = ratio n * t n) (m : ℕ) :
    ((m : ℚ)+2)^3 * convolution t (m+2) -
      b m * convolution t (m+1) + c m * convolution t m = 0 := by
  let s := Finset.range (m+1)
  have mid :
      ∑ k ∈ s, (((m : ℚ)+2)^3 * (t k * t (m+2-k)) -
        b m * (t k * t (m+1-k)) + c m * (t k * t (m-k))) =
        flux t m (m+1) := by
    calc
      _ = ∑ k ∈ s, (flux t m (k+1) - flux t m k) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact flux_difference t step (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      _ = _ := by
        dsimp only [s]
        rw [Finset.sum_range_sub (flux t m)]
        simp [flux, cert]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at mid
  have t1 : t 1 = 60 := by
    have h := step 0
    norm_num [ratio, t0] at h
    exact h
  have edge := congrArg (fun v : ℚ => v * t (m+1)) (endpoint (m : ℚ) (by positivity))
  unfold convolution
  rw [Finset.sum_range_succ _ (m+2), Finset.sum_range_succ _ (m+1),
      Finset.sum_range_succ (fun k => t k * t (m+1-k)) (m+1)]
  change _ * ((∑ k ∈ s, t k * t (m+2-k)) + _ + _) -
    _ * ((∑ k ∈ s, t k * t (m+1-k)) + _) + _ * (∑ k ∈ s, t k * t (m-k)) = _
  unfold flux at mid
  have hsub : m+2-(m+1) = 1 := by omega
  simp only [Nat.sub_self, hsub, t0, t1, mul_one, Nat.cast_add, Nat.cast_one] at mid ⊢
  rw [show m+2=(m+1)+1 by rfl, step (m+1)]
  push_cast
  linear_combination mid + edge

end A189286Certificate


namespace A189286Coeff

def t (n : ℕ) : ℚ := ((6*n).factorial : ℚ) /
  (((3*n).factorial : ℚ) * ((2*n).factorial : ℚ) * (n.factorial : ℚ))

lemma positive (n : ℕ) : 0 < t n := by unfold t; positivity

lemma step (n : ℕ) : t (n+1) =
  (12 * (6 * (n : ℚ) + 1) * (6 * (n : ℚ) + 5) / (n+1 : ℚ)^2) * t n := by
  unfold t
  rw [show 6*(n+1) = (6*n).succ.succ.succ.succ.succ.succ by omega,
      show 3*(n+1) = (3*n).succ.succ.succ by omega,
      show 2*(n+1) = (2*n).succ.succ by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring

lemma equals_binomial (n : ℕ) :
    t n = ((6*n).choose (3*n) : ℚ) * ((3*n).choose n : ℚ) := by
  have h6 := Nat.choose_mul_factorial_mul_factorial (n := 6*n) (k := 3*n) (by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (n := 3*n) (k := n) (by omega)
  rw [show 6*n-3*n = 3*n by omega] at h6
  rw [show 3*n-n = 2*n by omega] at h3
  have h6q : ((6*n).choose (3*n) : ℚ) * ((3*n).factorial : ℚ) * ((3*n).factorial : ℚ) = ((6*n).factorial : ℚ) := by exact_mod_cast h6
  have h3q : ((3*n).choose n : ℚ) * (n.factorial : ℚ) * ((2*n).factorial : ℚ) = ((3*n).factorial : ℚ) := by exact_mod_cast h3
  unfold t
  apply (div_eq_iff (by positivity)).mpr
  calc
    _ = ((6*n).choose (3*n) : ℚ) * ((3*n).factorial : ℚ) * ((3*n).factorial : ℚ) := h6q.symm
    _ = ((6*n).choose (3*n) : ℚ) * ((3*n).factorial : ℚ) *
          (((3*n).choose n : ℚ) * (n.factorial : ℚ) * ((2*n).factorial : ℚ)) := by rw [h3q]
    _ = _ := by ring

end A189286Coeff

/-
For the integral recurrence obtained by rescaling Zhi-Hong Sun's equation
(3.2), this file certifies all four residue classes simultaneously. The
identification with the binomial convolution is given in the accompanying
proof of the exact valuation.
-/

namespace A189286Recurrence

def U : ℕ → ℤ
  | 0 => 1
  | 1 => 15
  | n + 2 =>
    let m : ℤ := n
    3 * (2 * m + 3) * (18 * m ^ 2 + 54 * m + 41) * U (n + 1) -
      324 * (m + 1) ^ 4 * (3 * m + 1) * (3 * m + 5) * U n

def signature (r : ZMod 4) : ZMod 4 :=
  if r = 1 ∨ r = 2 then 3 else 1

lemma advance (r : ZMod 4) :
    3 * (2 * r + 3) * (18 * r ^ 2 + 54 * r + 41) * signature (r + 1) -
      324 * (r + 1) ^ 4 * (3 * r + 1) * (3 * r + 5) * signature r =
    signature (r + 2) := by
  fin_cases r <;> decide

theorem residue (n : ℕ) : (U n : ZMod 4) = signature (n : ZMod 4) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 =>
    rw [U]
    push_cast
    rw [h0, h1]
    push_cast
    exact advance _

theorem residue_is_one_or_three (n : ℕ) :
    (U n : ZMod 4) = 1 ∨ (U n : ZMod 4) = 3 := by
  rw [residue]
  unfold signature
  split <;> simp

end A189286Recurrence

namespace A189286Exact

open A189286Certificate A189286Recurrence A189286Coeff

def digitSum (n : ℕ) : ℕ := (Nat.digits 2 n).sum

def term (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (n+1),
    (((6*k).choose (3*k) : ℚ) * ((3*k).choose k : ℚ)) *
    (((6*(n-k)).choose (3*(n-k)) : ℚ) * ((3*(n-k)).choose (n-k) : ℚ))) /
    ((2*(n : ℚ)-1) * ((3*n).choose n : ℚ))

lemma initT : t 0 = 1 := by norm_num [t]

lemma initT1 : t 1 = 60 := by norm_num [t, Nat.factorial]

lemma convpos (n : ℕ) : 0 < convolution t n := by
  unfold convolution
  apply Finset.sum_pos
  · intro k _
    exact mul_pos (A189286Coeff.positive _) (A189286Coeff.positive _)
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

theorem scaled (n : ℕ) :
    (n.factorial : ℚ)^3 * convolution t n = (U n : ℚ) * (8 : ℚ)^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [convolution, initT, U]
  | one => norm_num [convolution, Finset.sum_range_succ, initT, initT1, U]
  | more m h0 h1 =>
    have recn := convolution_recurrence t initT A189286Coeff.step m
    have fac1 : ((m+1).factorial : ℚ) = ((m : ℚ)+1) * (m.factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; rfl
    have fac2 : ((m+2).factorial : ℚ) = ((m : ℚ)+2) * ((m : ℚ)+1) * (m.factorial : ℚ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, fac1]; push_cast; ring
    have u2 : (U (m+2) : ℚ) =
        3*(2*(m : ℚ)+3)*(18*(m : ℚ)^2+54*(m : ℚ)+41)*(U (m+1) : ℚ) -
        324*((m : ℚ)+1)^4*(3*(m : ℚ)+1)*(3*(m : ℚ)+5)*(U m : ℚ) := by
      rw [U]; push_cast; rfl
    rw [fac1, pow_succ (8 : ℚ) m] at h1
    rw [fac2, u2, pow_succ (8 : ℚ) (m+1), pow_succ (8 : ℚ) m]
    linear_combination (norm := (simp only [b, c]; ring))
      ((m.factorial : ℚ)^3 * ((m : ℚ)+1)^3) * recn +
      b (m : ℚ) * h1 - (c (m : ℚ) * ((m : ℚ)+1)^3) * h0


lemma uModTwo (n : ℕ) : (U n : ZMod 2) = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more m _ h1 =>
    rw [U]
    push_cast
    rw [h1]
    have finiteStep (r v : ZMod 2) :
        3*(2*r+3)*(18*r^2+54*r+41)*1 - 324*(r+1)^4*(3*r+1)*(3*r+5)*v = 1 := by
      fin_cases r <;> fin_cases v <;> decide
    exact finiteStep _ _

lemma uNotDiv (n : ℕ) : ¬ (2 : ℤ) ∣ U n := by
  intro h
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (U n) 2).mpr h
  rw [uModTwo] at hz
  exact one_ne_zero hz

lemma factorialVal (n : ℕ) :
    padicValRat 2 (n.factorial : ℚ) = (n : ℤ) - (digitSum n : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValRat.of_nat]
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  have hd := Nat.digit_sum_le 2 n
  unfold digitSum
  simp only [Nat.reduceSub, one_mul] at h
  omega

lemma doubleDigit (n : ℕ) : digitSum (2*n) = digitSum n := by
  cases n with
  | zero => rfl
  | succ k => simp [digitSum]

theorem convolutionVal (n : ℕ) : padicValRat 2 (convolution t n) = 3 * (digitSum n : ℤ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have nz : U n ≠ 0 := fun hz => uNotDiv n (hz ▸ dvd_zero _)
  have unz : (U n : ℚ) ≠ 0 := by exact_mod_cast nz
  have facnz : (n.factorial : ℚ) ≠ 0 := by positivity
  have h := congrArg (padicValRat 2) (scaled n)
  have uval : padicValRat 2 (U n : ℚ) = 0 := by
    rw [padicValRat.of_int]
    simp [padicValInt.eq_zero_of_not_dvd (uNotDiv n)]
  have eight : padicValRat 2 (8 : ℚ) = 3 := by
    change padicValRat 2 ((2 : ℚ)^3) = 3
    have two : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (p := 2) (by decide)
    rw [padicValRat.pow, two]
    norm_num
  rw [padicValRat.mul (pow_ne_zero 3 facnz) (convpos n).ne',
      padicValRat.mul unz (by positivity), padicValRat.pow, padicValRat.pow,
      factorialVal, uval, eight] at h
  omega

lemma term_factorials {n : ℕ} (hn : 0 < n) :
    term n = convolution t n * (n.factorial : ℚ) * ((2*n).factorial : ℚ) /
      (((2*n-1 : ℕ) : ℚ) * ((3*n).factorial : ℚ)) := by
  have h := Nat.choose_mul_factorial_mul_factorial (n := 3*n) (k := n) (by omega)
  rw [show 3*n-n=2*n by omega] at h
  have hq : ((3*n).choose n : ℚ) * (n.factorial : ℚ) * ((2*n).factorial : ℚ) =
      ((3*n).factorial : ℚ) := by exact_mod_cast h
  have hcast : ((2*n-1 : ℕ) : ℚ) = 2*(n : ℚ)-1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; rfl
  have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
  have hodd : 2*(n : ℚ)-1 ≠ 0 := by
    have h1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  have hc : ((3*n).choose n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  unfold term convolution
  simp only [A189286Coeff.equals_binomial]
  rw [hcast, ← hq]
  field_simp

theorem exactValuation (n : ℕ) (hn : 0 < n) :
    padicValRat 2 (term n) = (digitSum n : ℤ) + digitSum (3*n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have oddNZ : ((2*n-1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have oddV : padicValRat 2 ((2*n-1 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    simp [padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ 2*n-1 by omega)]
  rw [term_factorials hn, padicValRat.div (by positivity [convpos n]) (mul_ne_zero oddNZ (by positivity)),
      padicValRat.mul (by positivity [convpos n]) (by positivity),
      padicValRat.mul (convpos n).ne' (by positivity), padicValRat.mul oddNZ (by positivity),
      convolutionVal, factorialVal, factorialVal, factorialVal, oddV, doubleDigit]
  push_cast
  ring

end A189286Exact

theorem OMA.exactValuation (n : ℕ) (hn : 0 < n) :
    padicValRat 2 (OeisA189286.a n) =
      (A189286Exact.digitSum n : ℤ) + A189286Exact.digitSum (3 * n) := by
  have same : OeisA189286.a n = A189286Exact.term n := by
    simp only [OeisA189286.a, OeisA189286.tTerm, A189286Exact.term, Nat.cast_mul]
  rw [same]
  exact A189286Exact.exactValuation n hn

open OeisA189286 A189286Published

theorem OMA.solution : type_of% @OeisA189286.conjecture_3 := by
  intro n hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := (2 * n - 1) * (3*n).choose n
  have hDpos : 0 < D := denom_pos hn
  obtain ⟨q, hq⟩ := denom_dvd_sNat hn
  change sNat n = D * q at hq
  have hqpos : 0 < q := by
    have hs := sNat_pos n
    rw [hq] at hs
    exact Nat.pos_of_mul_pos_left hs
  have han : a n = (q : ℚ) := by
    rw [a_eq_div_nat hn]
    change (sNat n : ℚ) / (D : ℚ) = (q : ℚ)
    rw [hq, Nat.cast_mul, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hDpos.ne')]
  have hval : padicValNat 2 q = s2 n + s2 (3*n) := by
    have h := OMA.exactValuation n hn
    rw [han, padicValRat.of_nat] at h
    change (padicValNat 2 q : ℤ) = (s2 n : ℤ) + (s2 (3*n) : ℤ) at h
    exact_mod_cast h
  have hval_q : (∃ k : ℕ, n = 2 ^ k) → padicValNat 2 q = 3 := by
    rintro ⟨k, rfl⟩
    rw [hval, (s2_eq_one_iff _).mpr ⟨k, rfl⟩, s2_three_mul_two_pow]
  have hval_q_not : (¬ ∃ k : ℕ, n = 2 ^ k) → 4 ≤ padicValNat 2 q := by
    intro hnot
    have hpos := s2_pos hn
    have hne : s2 n ≠ 1 := fun h => hnot ((s2_eq_one_iff n).mp h)
    have hthree := two_le_s2_three_mul hn
    omega
  have hq_ge3 : 3 ≤ padicValNat 2 q := by
    have hn1 := s2_pos hn
    have hn3 := two_le_s2_three_mul hn
    omega
  have h8q : 8 ∣ q := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat_dvd_iff_le hqpos.ne']
    exact hq_ge3
  obtain ⟨m, hm⟩ := h8q
  refine ⟨(m : ℤ), ?_, ?_⟩
  · rw [han, hm]
    push_cast
    ring
  · constructor
    · rintro ⟨t, ht⟩
      by_contra hnot
      have hge4 := hval_q_not hnot
      have h16q : 16 ∣ q := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat_dvd_iff_le hqpos.ne']
        exact hge4
      rw [hm] at h16q
      rcases h16q with ⟨u, hu⟩
      have : m = 2 * u := by omega
      omega
    · intro hpow
      have hv3 := hval_q hpow
      have hnot16 : ¬ 16 ∣ q := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat_dvd_iff_le hqpos.ne']
        omega
      have hnot2m : ¬ 2 ∣ m := by
        intro ⟨u, hu⟩
        apply hnot16
        exact ⟨u, by omega⟩
      exact ⟨(m / 2 : ℕ), by omega⟩
