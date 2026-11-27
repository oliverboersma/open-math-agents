import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R2
import Mathlib

-- Step Arxiv.1601.03081.crystals_components_unique.R2.H1: hypothesis H1 of reduction Arxiv.1601.03081.crystals_components_unique.R2
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

/-! If `n + 1 = 2 ^ A * p ^ B` with `p` an odd prime and `n = a * b` is a crystal, then
`u = a + 1` and `v = b + 1` divide `(n + 1) ^ 2`, so they only involve the primes 2 and `p`.
They cannot share the factor `p`, and only one of them is divisible by 4, so after halving
one of them is a power of 2 and the other a power of `p`. Writing `x + 1 = 2 ^ j`,
`y + 1 = p ^ w` and `M = (n + 1) / 2`, the crystal condition is `(x + 1) * (y + 1)` dividing
`M ^ 2`. Comparing the 2-part and the `p`-part of `M` with `x` and `y` leaves only
`x = 3`, `y = 2`, i.e. `{a, b} = {5, 7}` (the crystal 35). Hence the components are unique. -/


namespace P4Cry

open Arxiv.«1601.03081»

theorem pow_succ_dvd_of_sq {p n k : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : p ^ (2 * k + 1) ∣ n ^ 2) : p ^ (k + 1) ∣ n := by
  rw [hp.pow_dvd_iff_le_factorization (pow_ne_zero 2 hn), Nat.factorization_pow] at h
  rw [hp.pow_dvd_iff_le_factorization hn]
  simp only [Finsupp.smul_apply, smul_eq_mul] at h
  omega

theorem dvd_sq_of_add {X M Z K : ℤ} (h : M + Z = X * K) (hd : X ∣ M ^ 2) : X ∣ Z ^ 2 := by
  have e : Z ^ 2 = M ^ 2 + X * (X * K ^ 2 - 2 * M * K) := by
    have hz : Z = X * K - M := by linarith
    rw [hz]; ring
  rw [e]; exact dvd_add hd (dvd_mul_right _ _)

theorem not_pow_succ_dvd_left {p α β : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ 2 ^ (α + 1) ∣ 2 ^ α * p ^ β := by
  rw [pow_succ]
  intro h
  have h' : 2 ∣ p ^ β := (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ α)).mp h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
    (Nat.prime_two.dvd_of_dvd_pow h')).symm

theorem not_pow_succ_dvd_right {p α β : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ (β + 1) ∣ 2 ^ α * p ^ β := by
  rw [pow_succ, mul_comm (2 ^ α)]
  intro h
  have h' : p ∣ 2 ^ α := (Nat.mul_dvd_mul_iff_left (pow_pos hp.pos β)).mp h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h'))

set_option maxHeartbeats 1000000 in
/-- Core: with `x + 1 = 2 ^ j` and `y + 1 = p ^ w`, the crystal conditions force `x = 3`, `y = 2`. -/
theorem core (p j w α β x y M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j) (hw : 1 ≤ w)
    (hX : x + 1 = 2 ^ j) (hY : y + 1 = p ^ w) (hMs : M = 2 ^ α * p ^ β)
    (hM : M + x + y + 1 = 2 * (x + 1) * (y + 1)) (hdiv : (x + 1) * (y + 1) ∣ M ^ 2) :
    x = 3 ∧ y = 2 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hx1 : 1 ≤ x := by
    have : 2 ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
    omega
  have hy2 : 2 ≤ y := by
    have : p ^ 1 ≤ p ^ w := Nat.pow_le_pow_right hp.pos hw
    rw [pow_one] at this
    omega
  have eY : M + y = (x + 1) * (2 * y + 1) := by
    zify at hM ⊢; linear_combination hM
  have eX : M + x = (y + 1) * (2 * x + 1) := by
    zify at hM ⊢; linear_combination hM
  have hXM2 : x + 1 ∣ M ^ 2 := Dvd.dvd.trans (Dvd.intro _ rfl) hdiv
  have hYM2 : y + 1 ∣ M ^ 2 := Dvd.dvd.trans (Dvd.intro_left _ rfl) hdiv
  have hXy2 : x + 1 ∣ y ^ 2 := by
    have := dvd_sq_of_add (X := ((x + 1 : ℕ) : ℤ)) (M := (M : ℤ)) (Z := (y : ℤ))
      (K := ((2 * y + 1 : ℕ) : ℤ)) (by exact_mod_cast eY) (by exact_mod_cast hXM2)
    exact_mod_cast this
  have hYx2 : y + 1 ∣ x ^ 2 := by
    have := dvd_sq_of_add (X := ((y + 1 : ℕ) : ℤ)) (M := (M : ℤ)) (Z := (x : ℤ))
      (K := ((2 * x + 1 : ℕ) : ℤ)) (by exact_mod_cast eX) (by exact_mod_cast hYM2)
    exact_mod_cast this
  have hnot2 : ¬ 2 ^ (α + 1) ∣ M := by rw [hMs]; exact not_pow_succ_dvd_left hp hp2
  have hnotp : ¬ p ^ (β + 1) ∣ M := by rw [hMs]; exact not_pow_succ_dvd_right hp hp2
  rcases Nat.lt_or_ge j α with hαj | hαj
  · -- x + 1 ∣ M, hence x + 1 ∣ y
    have hXM : x + 1 ∣ M := by
      rw [hX, hMs]; exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 hαj.le) _
    have hXy : x + 1 ∣ y := (Nat.dvd_add_right hXM).mp (by rw [eY]; exact Dvd.intro _ rfl)
    rcases Nat.lt_or_ge w β with hβw | hβw
    · have hYM : y + 1 ∣ M := by
        rw [hY, hMs]; exact Dvd.dvd.mul_left (Nat.pow_dvd_pow p hβw.le) _
      have hYx : y + 1 ∣ x := (Nat.dvd_add_right hYM).mp (by rw [eX]; exact Dvd.intro _ rfl)
      have h1 := Nat.le_of_dvd (by omega) hXy
      have h2 := Nat.le_of_dvd (by omega) hYx
      omega
    · -- case: x + 1 ∣ y and p ^ β ∣ x
      exfalso
      have hpx : p ^ β ∣ x := by
        have h1 : p ^ β ∣ M := by rw [hMs]; exact Dvd.intro_left _ rfl
        have h2 : p ^ β ∣ (y + 1) * (2 * x + 1) := by
          rw [hY]; exact Dvd.dvd.mul_right (Nat.pow_dvd_pow p hβw) _
        rw [← eX] at h2
        exact (Nat.dvd_add_right h1).mp h2
      have hpxle : p ^ β ≤ x := Nat.le_of_dvd (by omega) hpx
      obtain ⟨t, ht⟩ := hXy
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · rw [h0, mul_zero] at ht; omega
        · exact h0
      have hYt2 : y + 1 ∣ (t + 1) ^ 2 := by
        have key : ((t + 1 : ℕ) : ℤ) ^ 2 =
            (t : ℤ) ^ 2 * (x : ℤ) ^ 2 + ((y + 1 : ℕ) : ℤ) * (2 * ((t : ℤ) + 1) - ((y : ℤ) + 1)) := by
          have hy' : (y : ℤ) = ((x : ℤ) + 1) * t := by exact_mod_cast ht
          push_cast; rw [hy']; ring
        have : ((y + 1 : ℕ) : ℤ) ∣ ((t + 1 : ℕ) : ℤ) ^ 2 := by
          rw [key]
          refine dvd_add (Dvd.dvd.mul_left ?_ _) (dvd_mul_right _ _)
          exact_mod_cast hYx2
        exact_mod_cast this
      have eM : M + (x + 1) * (t + 1) = 2 * (x + 1) * (y + 1) := by
        have hy' : (y : ℤ) = ((x : ℤ) + 1) * t := by exact_mod_cast ht
        zify at hM ⊢; rw [hy'] at hM ⊢; linear_combination hM
      have hw2 : w ≤ 2 * β := by
        by_contra hcon
        have h1 : p ^ (2 * β + 1) ∣ (t + 1) ^ 2 :=
          Dvd.dvd.trans (Nat.pow_dvd_pow p (by omega)) (hY ▸ hYt2)
        have h2 : p ^ (β + 1) ∣ t + 1 := pow_succ_dvd_of_sq hp (by omega) h1
        have h3 : p ^ (β + 1) ∣ y + 1 := hY ▸ Nat.pow_dvd_pow p (by omega)
        have h4 : p ^ (β + 1) ∣ M + (x + 1) * (t + 1) := by
          rw [eM]; exact Dvd.dvd.mul_left h3 _
        exact hnotp ((Nat.dvd_add_left (Dvd.dvd.mul_left h2 _)).mp h4)
      have hle1 : y + 1 ≤ x ^ 2 := by
        calc y + 1 = p ^ w := hY
          _ ≤ p ^ (2 * β) := Nat.pow_le_pow_right hp.pos hw2
          _ = (p ^ β) ^ 2 := by ring
          _ ≤ x ^ 2 := Nat.pow_le_pow_left hpxle 2
      have hle2 : y + 1 ≤ (t + 1) ^ 2 := Nat.le_of_dvd (by positivity) hYt2
      rw [ht] at hle1 hle2
      have htx : t < x := by
        by_contra h
        have h := Nat.le_of_not_lt h
        nlinarith [Nat.mul_le_mul_left (x + 1) h]
      have hxt : x ≤ t + 1 := by
        by_contra h
        have h := Nat.lt_of_not_le h
        nlinarith [Nat.mul_le_mul_right t (show t + 3 ≤ x + 1 by omega)]
      have hxe : x = t + 1 := by omega
      subst hxe
      have hpe : p ^ β = t + 1 := by
        by_contra hne
        have hlt : p ^ β < t + 1 := lt_of_le_of_ne hpxle hne
        have : (p ^ β) ^ 2 < (t + 1) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
        have h5 : p ^ w ≤ p ^ (2 * β) := Nat.pow_le_pow_right hp.pos hw2
        rw [← hY, ht] at h5
        have h6 : p ^ (2 * β) = (p ^ β) ^ 2 := by ring
        nlinarith
      have hMe : M = (t + 1) * ((t + 2) * (2 * t + 1)) := by
        have hy' : (y : ℤ) = ((t : ℤ) + 1 + 1) * t := by exact_mod_cast ht
        zify at hM ⊢; rw [hy'] at hM; linear_combination hM
      rw [hMs, ← hpe, mul_comm (2 ^ α)] at hMe
      have h6 : 2 ^ α = (t + 2) * (2 * t + 1) :=
        Nat.eq_of_mul_eq_mul_left (by positivity) hMe
      have h7 : 2 * t + 1 ∣ 2 ^ α := ⟨t + 2, by rw [h6]; ring⟩
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h7
      rcases k with _ | k
      · simp at hk; omega
      · rw [pow_succ] at hk; omega
  · -- 2 ^ α ∣ y
    have h2y : 2 ^ α ∣ y := by
      have h1 : 2 ^ α ∣ M := by rw [hMs]; exact Dvd.intro _ rfl
      have h2 : 2 ^ α ∣ (x + 1) * (2 * y + 1) := by
        rw [hX]; exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 hαj) _
      rw [← eY] at h2
      exact (Nat.dvd_add_right h1).mp h2
    have h2yle : 2 ^ α ≤ y := Nat.le_of_dvd (by omega) h2y
    rcases Nat.lt_or_ge w β with hβw | hβw
    · -- y + 1 ∣ x
      have hYM : y + 1 ∣ M := by
        rw [hY, hMs]; exact Dvd.dvd.mul_left (Nat.pow_dvd_pow p hβw.le) _
      have hYx : y + 1 ∣ x := (Nat.dvd_add_right hYM).mp (by rw [eX]; exact Dvd.intro _ rfl)
      obtain ⟨t, ht⟩ := hYx
      have ht1 : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · rw [h0, mul_zero] at ht; omega
        · exact h0
      have hXt2 : x + 1 ∣ (t + 1) ^ 2 := by
        have key : ((t + 1 : ℕ) : ℤ) ^ 2 =
            (t : ℤ) ^ 2 * (y : ℤ) ^ 2 + ((x + 1 : ℕ) : ℤ) * (2 * ((t : ℤ) + 1) - ((x : ℤ) + 1)) := by
          have hx' : (x : ℤ) = ((y : ℤ) + 1) * t := by exact_mod_cast ht
          push_cast; rw [hx']; ring
        have : ((x + 1 : ℕ) : ℤ) ∣ ((t + 1 : ℕ) : ℤ) ^ 2 := by
          rw [key]
          refine dvd_add (Dvd.dvd.mul_left ?_ _) (dvd_mul_right _ _)
          exact_mod_cast hXy2
        exact_mod_cast this
      have eM : M + (y + 1) * (t + 1) = 2 * (x + 1) * (y + 1) := by
        have hx' : (x : ℤ) = ((y : ℤ) + 1) * t := by exact_mod_cast ht
        zify at hM ⊢; rw [hx'] at hM ⊢; linear_combination hM
      have hj2 : j ≤ 2 * α := by
        by_contra hcon
        have h1 : 2 ^ (2 * α + 1) ∣ (t + 1) ^ 2 :=
          Dvd.dvd.trans (Nat.pow_dvd_pow 2 (by omega)) (hX ▸ hXt2)
        have h2 : 2 ^ (α + 1) ∣ t + 1 := pow_succ_dvd_of_sq Nat.prime_two (by omega) h1
        have h3 : 2 ^ (α + 1) ∣ x + 1 := hX ▸ Nat.pow_dvd_pow 2 (by omega)
        have h4 : 2 ^ (α + 1) ∣ M + (y + 1) * (t + 1) := by
          rw [eM]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h3 _) _
        exact hnot2 ((Nat.dvd_add_left (Dvd.dvd.mul_left h2 _)).mp h4)
      have hle1 : x + 1 ≤ y ^ 2 := by
        calc x + 1 = 2 ^ j := hX
          _ ≤ 2 ^ (2 * α) := Nat.pow_le_pow_right (by norm_num) hj2
          _ = (2 ^ α) ^ 2 := by ring
          _ ≤ y ^ 2 := Nat.pow_le_pow_left h2yle 2
      have hle2 : x + 1 ≤ (t + 1) ^ 2 := Nat.le_of_dvd (by positivity) hXt2
      rw [ht] at hle1 hle2
      have hty : t < y := by
        by_contra h
        have h := Nat.le_of_not_lt h
        nlinarith [Nat.mul_le_mul_left (y + 1) h]
      have hyt : y ≤ t + 1 := by
        by_contra h
        have h := Nat.lt_of_not_le h
        nlinarith [Nat.mul_le_mul_right t (show t + 3 ≤ y + 1 by omega)]
      have hye : y = t + 1 := by omega
      subst hye
      have h2e : 2 ^ α = t + 1 := by
        by_contra hne
        have hlt : 2 ^ α < t + 1 := lt_of_le_of_ne h2yle hne
        have : (2 ^ α) ^ 2 < (t + 1) ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
        have h5 : 2 ^ j ≤ 2 ^ (2 * α) := Nat.pow_le_pow_right (by norm_num) hj2
        rw [← hX, ht] at h5
        have h6 : 2 ^ (2 * α) = (2 ^ α) ^ 2 := by ring
        nlinarith
      have hMe : M = (t + 1) * ((t + 2) * (2 * t + 1)) := by
        have hx' : (x : ℤ) = ((t : ℤ) + 1 + 1) * t := by exact_mod_cast ht
        zify at hM ⊢; rw [hx'] at hM; linear_combination hM
      rw [hMs, ← h2e] at hMe
      have h6 : p ^ β = (t + 2) * (2 * t + 1) :=
        Nat.eq_of_mul_eq_mul_left (by positivity) hMe
      have h7 : 2 * t + 1 ∣ p ^ β := ⟨t + 2, by rw [h6]; ring⟩
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp h7
      rcases k with _ | k
      · simp at hk; omega
      · -- p ∣ 2t+1 and p ∣ t+2, so p ∣ 3
        have hpa : p ∣ 2 * t + 1 := by rw [hk, pow_succ]; exact Dvd.intro_left _ rfl
        have hpb : p ∣ t + 1 + 1 := by
          rw [hY]; exact dvd_pow_self p (by omega)
        have hp3' : p ∣ 3 := by
          have : p ∣ 2 * (t + 1 + 1) := Dvd.dvd.mul_left hpb 2
          have e : 2 * (t + 1 + 1) = (2 * t + 1) + 3 := by ring
          rw [e] at this
          exact (Nat.dvd_add_right hpa).mp this
        have hp3e : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3'
        subst hp3e
        rcases w with _ | w
        · omega
        rcases w with _ | w
        · have ht' : t = 1 := by simp at hY; omega
          subst ht'; omega
        · exfalso
          rw [pow_succ, pow_succ] at hY
          rcases k with _ | k
          · simp at hk; omega
          · rw [pow_succ, pow_succ] at hk; omega
    · -- both small: contradiction by size
      exfalso
      have hpx : p ^ β ∣ x := by
        have h1 : p ^ β ∣ M := by rw [hMs]; exact Dvd.intro_left _ rfl
        have h2 : p ^ β ∣ (y + 1) * (2 * x + 1) := by
          rw [hY]; exact Dvd.dvd.mul_right (Nat.pow_dvd_pow p hβw) _
        rw [← eX] at h2
        exact (Nat.dvd_add_right h1).mp h2
      have hpxle : p ^ β ≤ x := Nat.le_of_dvd (by omega) hpx
      have hle : M ≤ y * x := by rw [hMs]; exact Nat.mul_le_mul h2yle hpxle
      have e : M = 2 * (x * y) + x + y + 1 := by zify at hM ⊢; linear_combination hM
      rw [mul_comm y x] at hle
      omega

theorem decomp {d e f p : ℕ} (hp : p.Prime) (h : d ∣ 2 ^ e * p ^ f) : ∃ i k, d = 2 ^ i * p ^ k := by
  obtain ⟨d1, d2, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  obtain ⟨k, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp h2
  exact ⟨i, k, rfl⟩

theorem crystal_form (n a b A B p : ℕ) (hp : p.Prime) (hpo : Odd p)
    (hN : n + 1 = 2 ^ A * p ^ B) (h : IsCrystalWithComponents n a b) :
    (a = 7 ∧ b = 5) ∨ (a = 5 ∧ b = 7) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hpo) even_two
  rw [isCrystalWithComponents_iff_mul_sq_dvd] at h
  obtain ⟨hn, ha, hb, rfl, hd⟩ := h
  obtain ⟨hao, hbo⟩ := Nat.odd_mul.mp hn
  obtain ⟨x, rfl⟩ := hao
  obtain ⟨y, rfl⟩ := hbo
  have hx0 : 1 ≤ x := by omega
  have hy0 : 1 ≤ y := by omega
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 * x * y + x + y + 1 := ⟨_, rfl⟩
  have hNM : (2 * x + 1) * (2 * y + 1) + 1 = 2 * M := by rw [hMdef]; ring
  have hM : M + x + y + 1 = 2 * (x + 1) * (y + 1) := by rw [hMdef]; ring
  have hdiv : (x + 1) * (y + 1) ∣ M ^ 2 := by
    have e1 : (2 * x + 1 + 1) * (2 * y + 1 + 1) = 4 * ((x + 1) * (y + 1)) := by ring
    have e2 : ((2 * x + 1) * (2 * y + 1) + 1) ^ 2 = 4 * M ^ 2 := by rw [hNM]; ring
    rw [e1, e2] at hd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 4)).mp hd
  rcases A with _ | A'
  · exfalso
    have h2 : 2 * M = p ^ B := by rw [← hNM, hN]; simp
    have : Odd (2 * M) := h2 ▸ hpo.pow
    have := Nat.odd_iff.mp this
    omega
  have hMs : M = 2 ^ A' * p ^ B := by
    have : 2 * M = 2 * (2 ^ A' * p ^ B) := by rw [← hNM, hN]; ring
    omega
  have hM2 : M ^ 2 = 2 ^ (2 * A') * p ^ (2 * B) := by rw [hMs]; ring
  have hx1 : x + 1 ∣ M ^ 2 := Dvd.dvd.trans (Dvd.intro _ rfl) hdiv
  have hy1 : y + 1 ∣ M ^ 2 := Dvd.dvd.trans (Dvd.intro_left _ rfl) hdiv
  obtain ⟨i, k, hik⟩ := decomp hp (hM2 ▸ hx1)
  obtain ⟨l, m, hlm⟩ := decomp hp (hM2 ▸ hy1)
  have hcommon : ∀ q : ℕ, q.Prime → ¬ (q ∣ x + 1 ∧ q ∣ y + 1) := by
    rintro q hq ⟨h1, h2⟩
    have hqM : q ∣ M := hq.dvd_of_dvd_pow (h1.trans hx1)
    have h3 : q ∣ M + (x + 1) + (y + 1) := dvd_add (dvd_add hqM h1) h2
    have e : M + (x + 1) + (y + 1) = 2 * (x + 1) * (y + 1) + 1 := by omega
    rw [e] at h3
    have h4 : q ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left h2 _)).mp h3
    exact hq.one_lt.ne' (Nat.dvd_one.mp h4)
  have hkm : k = 0 ∨ m = 0 := by
    by_contra hc
    rw [not_or] at hc
    apply hcommon p hp
    constructor
    · rw [hik]; exact Dvd.dvd.mul_left (dvd_pow_self p hc.1) _
    · rw [hlm]; exact Dvd.dvd.mul_left (dvd_pow_self p hc.2) _
  have hil : i = 0 ∨ l = 0 := by
    by_contra hc
    rw [not_or] at hc
    apply hcommon 2 Nat.prime_two
    constructor
    · rw [hik]; exact Dvd.dvd.mul_right (dvd_pow_self 2 hc.1) _
    · rw [hlm]; exact Dvd.dvd.mul_right (dvd_pow_self 2 hc.2) _
  rcases hkm with hk0 | hm0 <;> rcases hil with hi0 | hl0
  · rw [hk0, hi0] at hik; simp at hik; omega
  · left
    rw [hk0, pow_zero, mul_one] at hik
    rw [hl0, pow_zero, one_mul] at hlm
    have hi1 : 1 ≤ i := by
      rcases i with _ | i
      · simp at hik; omega
      · omega
    have hm1 : 1 ≤ m := by
      rcases m with _ | m
      · simp at hlm; omega
      · omega
    obtain ⟨h1, h2⟩ := core p i m A' B x y M hp hp2 hi1 hm1 hik hlm hMs hM hdiv
    subst h1; subst h2; norm_num
  · right
    rw [hi0, pow_zero, one_mul] at hik
    rw [hm0, pow_zero, mul_one] at hlm
    have hk1 : 1 ≤ k := by
      rcases k with _ | k
      · simp at hik; omega
      · omega
    have hl1 : 1 ≤ l := by
      rcases l with _ | l
      · simp at hlm; omega
      · omega
    have hM' : M + y + x + 1 = 2 * (y + 1) * (x + 1) := by
      rw [show M + y + x + 1 = M + x + y + 1 by ring, hM]; ring
    have hdiv' : (y + 1) * (x + 1) ∣ M ^ 2 := by rw [mul_comm]; exact hdiv
    obtain ⟨h1, h2⟩ := core p l k A' B y x M hp hp2 hl1 hk1 hlm hik hMs hM' hdiv'
    subst h1; subst h2; norm_num
  · rw [hm0, hl0] at hlm; simp at hlm; omega

end P4Cry

open P4Cry in
theorem OMA.solution : OMA.R_Arxiv_1601_03081_crystals_components_unique_R2.H1 := by
  intro n a b c d hab hcd ⟨p, A, B, hp, hpo, hN⟩
  rcases crystal_form n a b A B p hp hpo hN hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases crystal_form n c d A B p hp hpo hN hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
