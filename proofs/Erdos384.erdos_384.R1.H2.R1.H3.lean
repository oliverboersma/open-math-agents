import OMAReductions.R_Erdos384_erdos_384_R1_H2_R1
import Mathlib.NumberTheory.Chebyshev

/-!
Ecklund's middle range for the small prime divisor theorem (Pacific J. Math. 29,
1969, pp. 267–270). Halving the two arguments gives a binomial coefficient
supported on primes at most `k` if the original coefficient has no small prime
divisor. A primorial bounds the first copy of each prime, and the Chebyshev
functions bound the higher powers.
-/

namespace OMA.EcklundMiddleRange

open Nat Finset

private theorem halfBinomialPrime {n k p : ℕ} (hkn : k ≤ n) (hp : p.Prime)
    (hkp : k < p) (h : p ∣ (n / 2).choose (k / 2)) : p ∣ n.choose k ∧ 2 * p ≤ n := by
  have hhalf : k / 2 ≤ n / 2 := by omega
  have hprod : p ∣ (n / 2).descFactorial (k / 2) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact dvd_mul_of_dvd_right h _
  rw [Nat.descFactorial_eq_prod_range] at hprod
  obtain ⟨i, hi, hd⟩ := (hp.prime.dvd_finsetProd_iff _).mp hprod
  have hil : i < k / 2 := mem_range.mp hi
  have hterm : 2 * (n / 2 - i) ≤ n := by omega
  have hj : n - 2 * (n / 2 - i) < k := by omega
  have hd' : p ∣ n.descFactorial k := by
    rw [Nat.descFactorial_eq_prod_range]
    refine (hp.prime.dvd_finsetProd_iff _).mpr ⟨_, mem_range.mpr hj, ?_⟩
    rw [Nat.sub_sub_self hterm]
    exact dvd_mul_of_dvd_right hd _
  rw [Nat.descFactorial_eq_factorial_mul_choose, hp.dvd_mul] at hd'
  refine ⟨hd'.resolve_left (fun hfac => hkp.not_ge (hp.dvd_factorial.mp hfac)), ?_⟩
  have hle := Nat.le_of_dvd (show 0 < n / 2 - i by omega) hd
  omega

-- A prime power above `s` and at most `y` gives a carry in the binomial.
private theorem lcmStep {y s : ℕ} (hs : 0 < s) (hsy : s ≤ y) (hys : y ≤ 2 * s) :
    lcmUpto y ∣ lcmUpto s * y.choose s := by
  rw [← Nat.factorization_prime_le_iff_dvd (lcmUpto_ne_zero y)
    (mul_ne_zero (lcmUpto_ne_zero s) (choose_ne_zero hsy))]
  intro p hp
  rw [Nat.factorization_mul (lcmUpto_ne_zero s) (choose_ne_zero hsy),
    Finsupp.add_apply, factorization_lcmUpto y hp, factorization_lcmUpto s hp]
  let a := p.log y
  change a ≤ p.log s + (y.choose s).factorization p
  have hpy : p ^ a ≤ y := Nat.pow_log_le_self p (by omega)
  by_cases hsmall : p ^ a ≤ s
  · exact (Nat.le_log_of_pow_le hp.one_lt hsmall).trans (Nat.le_add_right _ _)
  have ha : 0 < a := by
    by_contra! h
    have ha0 : a = 0 := by omega
    simp [ha0, show 1 ≤ s by omega] at hsmall
  have hprev : p ^ (a - 1) ≤ s := by
    have hmul : p ^ (a - 1) * p ≤ y := by
      rwa [← pow_succ, Nat.sub_add_cancel (show 1 ≤ a by omega)]
    have := Nat.mul_le_mul_left (p ^ (a - 1)) hp.two_le
    omega
  have hlog := Nat.le_log_of_pow_le hp.one_lt hprev
  have hcarry : 1 ≤ (y.choose s).factorization p := by
    rw [Nat.factorization_choose hp hsy (Nat.lt_succ_self (p.log y))]
    apply Finset.card_pos.mpr
    refine ⟨a, mem_filter.mpr ⟨mem_Ico.mpr ⟨ha, Nat.lt_succ_self _⟩, ?_⟩⟩
    rw [Nat.mod_eq_of_lt (show s < p ^ a by omega),
      Nat.mod_eq_of_lt (show y - s < p ^ a by omega)]
    omega
  omega

private theorem lcmBound (n : ℕ) : lcmUpto n ≤ 4 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · interval_cases n <;> decide
    let s := (n + 1) / 2
    have hsn : s < n := by dsimp [s]; omega
    have hdiv := lcmStep (y := n) (s := s) (by dsimp [s]; omega) hsn.le (by dsimp [s]; omega)
    have hchoose : n.choose s ≤ 2 ^ (n - 1) := by
      have h := Nat.choose_succ_le_two_pow (n - 1) s
      rwa [Nat.sub_add_cancel (show 1 ≤ n by omega)] at h
    calc
      _ ≤ lcmUpto s * n.choose s := Nat.le_of_dvd
        (Nat.mul_pos (lcmUpto_pos s) (choose_pos hsn.le)) hdiv
      _ ≤ 4 ^ s * 2 ^ (n - 1) := Nat.mul_le_mul (ih s hsn) hchoose
      _ ≤ 4 ^ n := by
        rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, ← pow_add, ← pow_mul]
        apply Nat.pow_le_pow_right (by decide)
        dsimp [s]
        omega

private theorem psiBound {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x ≤ Real.log 4 * x := by
  rw [Chebyshev.psi_eq_psi_coe_floor, Chebyshev.psi_eq_log_lcmUpto]
  calc
    Real.log (lcmUpto ⌊x⌋₊ : ℝ) ≤ Real.log ((4 : ℝ) ^ ⌊x⌋₊) :=
      Real.log_le_log (by exact_mod_cast lcmUpto_pos ⌊x⌋₊)
        (by exact_mod_cast lcmBound ⌊x⌋₊)
    _ = Real.log 4 * (⌊x⌋₊ : ℝ) := by rw [Real.log_pow, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le hx) (Real.log_nonneg (by norm_num))

private theorem primorialVal {p j : ℕ} (hp : p.Prime) (hpj : p ≤ j) :
    (primorial j).factorization p = 1 := by
  apply le_antisymm
  · exact (Nat.squarefree_iff_factorization_le_one (primorial_pos j).ne').mp
      (squarefree_primorial j) p
  · exact (hp.dvd_iff_one_le_factorization (primorial_pos j).ne').mp
      (hp.dvd_primorial_iff.mpr hpj)

private theorem smoothBinomialLog {m l k : ℕ} (hlm : l ≤ m) (hkm : k ≤ m)
    (hsmooth : ∀ p : ℕ, p.Prime → p ∣ m.choose l → p ≤ k) :
    Real.log (m.choose l : ℝ) ≤ Chebyshev.theta k + (Chebyshev.psi m - Chebyshev.theta m) := by
  obtain ⟨q, hq⟩ := primorial_dvd_lcmUpto m
  have hq0 : q ≠ 0 := by rintro rfl; simp [lcmUpto_ne_zero] at hq
  have hd : m.choose l ∣ primorial k * q := by
    rw [← Nat.factorization_prime_le_iff_dvd (choose_ne_zero hlm)
      (mul_ne_zero (primorial_pos k).ne' hq0)]
    intro p hp
    by_cases h : p ∣ m.choose l
    · have hpk := hsmooth p hp h
      have heq := congrArg (fun t : ℕ => t.factorization p) hq
      rw [factorization_lcmUpto m hp, Nat.factorization_mul (primorial_pos m).ne' hq0,
        Finsupp.add_apply, primorialVal hp (hpk.trans hkm)] at heq
      rw [Nat.factorization_mul (primorial_pos k).ne' hq0, Finsupp.add_apply,
        primorialVal hp hpk, ← heq]
      exact Nat.factorization_choose_le_log
    · have hz : (m.choose l).factorization p = 0 := by
        have hn := mt (hp.dvd_iff_one_le_factorization (choose_ne_zero hlm)).mpr h
        omega
      rw [hz]
      exact Nat.zero_le _
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  have hcast : (lcmUpto m : ℝ) = (primorial m : ℝ) * q := by exact_mod_cast hq
  rw [Chebyshev.theta_eq_log_primorial, Chebyshev.psi_eq_log_lcmUpto,
    Chebyshev.theta_eq_log_primorial, Nat.floor_natCast, Nat.floor_natCast, hcast,
    Real.log_mul (by exact_mod_cast (primorial_pos m).ne') hqpos.ne']
  rw [add_sub_cancel_left, ← Real.log_mul (by exact_mod_cast (primorial_pos k).ne') hqpos.ne']
  apply Real.log_le_log (by exact_mod_cast choose_pos hlm)
  exact_mod_cast Nat.le_of_dvd (Nat.mul_pos (primorial_pos k) (Nat.pos_of_ne_zero hq0)) hd

private theorem quadraticBernoulli {u : ℝ} (hu : 0 ≤ u) (t : ℕ) :
    1 + (t : ℝ) * u + (t : ℝ) * ((t : ℝ) - 1) / 2 * u ^ 2 ≤ (1 + u) ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [show (1 + u) ^ (t + 1) = (1 + u) ^ t * (1 + u) from pow_succ _ _, Nat.cast_succ]
    have hm := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1 + u by linarith)
    have ht : 0 ≤ (t : ℝ) * ((t : ℝ) - 1) := by
      cases t with
      | zero => simp
      | succ t => simp only [Nat.cast_succ, add_sub_cancel_right]; positivity
    refine le_trans ?_ hm
    nlinarith only [mul_nonneg ht (pow_nonneg hu 3)]

-- Two steps of the factorial recurrence and a quadratic Bernoulli bound.
private theorem factorialBound (l : ℕ) (hl : 16 ≤ l) :
    (l ! : ℝ) ≤ ((5 : ℝ) * l / 11) ^ l := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    by_cases hsmall : l < 18
    · interval_cases l <;> norm_num [Nat.factorial]
    let t := l - 2
    have ht : 16 ≤ t := by dsimp [t]; omega
    have hlt : t < l := by dsimp [t]; omega
    have hlt' : l = t + 2 := by dsimp [t]; omega
    have htR : (16 : ℝ) ≤ t := by exact_mod_cast ht
    have hpos : 0 < (t : ℝ) := by linarith
    have hgrowth : (121 / 25 : ℝ) ≤ (1 + 2 / t) ^ t := by
      refine le_trans ?_ (quadraticBernoulli (u := 2 / t) (by positivity) t)
      apply (le_of_mul_le_mul_right ?_ (show 0 < (t : ℝ) ^ 2 by positivity))
      field_simp
      nlinarith [mul_nonneg (show 0 ≤ (t : ℝ) - 16 by linarith) hpos.le]
    have hscale : ((t : ℝ) + 2) ^ 2 ≤ (5 * ((t : ℝ) + 2) / 11) ^ 2 * (1 + 2 / t) ^ t := by
      calc
        _ = (5 * ((t : ℝ) + 2) / 11) ^ 2 * (121 / 25) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgrowth (sq_nonneg _)
    have hpow : (1 + 2 / (t : ℝ)) ^ t * (5 * (t : ℝ) / 11) ^ t =
        (5 * ((t : ℝ) + 2) / 11) ^ t := by
      rw [← mul_pow]
      congr 1
      field_simp
    rw [hlt', show t + 2 = t + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    calc
      _ ≤ ((t : ℝ) + 2) ^ 2 * (5 * (t : ℝ) / 11) ^ t := by
        have hi := ih t hlt ht
        have hprod : ((t : ℝ) + 1 + 1) * ((t : ℝ) + 1) ≤ ((t : ℝ) + 2) ^ 2 := by nlinarith
        simpa only [mul_assoc] using mul_le_mul hprod hi (by positivity) (by positivity)
      _ ≤ ((5 * ((t : ℝ) + 2) / 11) ^ 2 * (1 + 2 / t) ^ t) * (5 * (t : ℝ) / 11) ^ t :=
        mul_le_mul_of_nonneg_right hscale (by positivity)
      _ = _ := by
        rw [mul_assoc, hpow, ← pow_add]
        congr 1 <;> ring

private theorem binomialLower {m l : ℕ} (hl : 16 ≤ l) (hm : 16 * l ≤ m) :
    (33 : ℝ) ^ l ≤ m.choose l := by
  refine le_trans ?_ (Nat.pow_le_choose (α := ℝ) l m)
  apply (le_div_iff₀ (show (0 : ℝ) < (l.factorial : ℝ) by exact_mod_cast Nat.factorial_pos l)).2
  calc
    _ ≤ (33 : ℝ) ^ l * (5 * (l : ℝ) / 11) ^ l := by
      gcongr
      exact factorialBound l hl
    _ = (15 * (l : ℝ)) ^ l := by rw [← mul_pow]; ring_nf
    _ ≤ ((m + 1 - l : ℕ) : ℝ) ^ l := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast (show 15 * l ≤ m + 1 - l by omega)

private theorem rootBound {m k : ℝ} (hm : 0 ≤ m) (hk : 256 ≤ k) (hmk : m ^ 2 ≤ k ^ 3 / 4)
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 ≤ c)
    (hconst : 1 / 4 ≤ c ^ (2 * d) * (256 : ℝ) ^ (2 * d - 3)) :
    m ^ ((d : ℝ)⁻¹) ≤ c * k := by
  have hk0 : 0 ≤ k := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  apply (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hc hk0) (show 2 * d ≠ 0 by omega)).mp
  rw [← Real.rpow_natCast, ← Real.rpow_mul hm, show (d : ℝ)⁻¹ * ((2 * d : ℕ) : ℝ) = 2 by
    push_cast
    field_simp, Real.rpow_two]
  have hr : 1 / 4 ≤ c ^ (2 * d) * k ^ (2 * d - 3) := hconst.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hk _) (by positivity))
  calc
    _ ≤ k ^ 3 / 4 := hmk
    _ = k ^ 3 * (1 / 4) := by ring
    _ ≤ k ^ 3 * (c ^ (2 * d) * k ^ (2 * d - 3)) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = (c * k) ^ (2 * d) := by
      rw [mul_left_comm, ← pow_add, show 3 + (2 * d - 3) = 2 * d by omega, mul_pow]

theorem solve (n k : ℕ) (hk : 60 ≤ k) (hk3 : n * n ≤ k * k * k) (h16 : 16 * k ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n.choose k ∧ 2 * p ≤ n := by
  let m := n / 2
  let l := k / 2
  have h16R : 16 * (k : ℝ) ≤ n := by exact_mod_cast h16
  have hk3R : (n : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by
    exact_mod_cast (show n ^ 2 ≤ k ^ 3 by simpa [pow_succ, mul_assoc] using hk3)
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkR : (256 : ℝ) ≤ k := by
    apply le_of_mul_le_mul_right _ (show 0 < (k : ℝ) ^ 2 by positivity)
    have hs := pow_le_pow_left₀ (show 0 ≤ 16 * (k : ℝ) by positivity) h16R 2
    nlinarith only [hs, hk3R]
  have hk256 : 256 ≤ k := by exact_mod_cast hkR
  have hl : 128 ≤ l := by dsimp [l]; omega
  have hml : 16 * l ≤ m := by dsimp [l, m]; omega
  have hlm : l ≤ m := by omega
  have hkm : k ≤ m := by dsimp [m]; omega
  have hmR : 0 ≤ (m : ℝ) := by positivity
  have hm2 : (m : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 / 4 := by
    have hmle : 2 * (m : ℝ) ≤ n := by exact_mod_cast (show 2 * m ≤ n by dsimp [m]; omega)
    have hs := pow_le_pow_left₀ (show 0 ≤ 2 * (m : ℝ) by positivity) hmle 2
    nlinarith only [hs, hk3R]
  by_contra hbad
  have hsmooth (p : ℕ) (hp : p.Prime) (hpd : p ∣ m.choose l) : p ≤ k := by
    by_contra! hpk
    obtain ⟨hd, hpn⟩ := halfBinomialPrime (show k ≤ n by omega) hp hpk hpd
    exact hbad ⟨p, hp, hd, hpn⟩
  have h2 := rootBound hmR hkR hm2 2 (by decide) (9 / 50) (by norm_num) (by norm_num)
  have h3 := rootBound hmR hkR hm2 3 (by decide) (1 / 20) (by norm_num) (by norm_num)
  have h5 := rootBound hmR hkR hm2 5 (by decide) (1 / 50) (by norm_num) (by norm_num)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlogUpper : Real.log (m.choose l : ℝ) ≤ (5 / 2) * k * Real.log 2 := by
    have hextra := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi (m : ℝ)
    have hsum := add_le_add (add_le_add (psiBound (by positivity : 0 ≤ (m : ℝ) ^ ((2 : ℝ)⁻¹)))
      (psiBound (by positivity : 0 ≤ (m : ℝ) ^ ((3 : ℝ)⁻¹))))
      (psiBound (by positivity : 0 ≤ (m : ℝ) ^ ((5 : ℝ)⁻¹)))
    have hr2 := mul_le_mul_of_nonneg_left h2 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    have hr3 := mul_le_mul_of_nonneg_left h3 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    have hr5 := mul_le_mul_of_nonneg_left h5 (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
    have ht := Chebyshev.theta_le_log4_mul_x (show 0 ≤ (k : ℝ) by positivity)
    have hb := smoothBinomialLog hlm hkm hsmooth
    push_cast at hr2 hr3 hr5
    rw [hlog4] at hsum hr2 hr3 hr5 ht
    linarith only [hextra, hsum, hr2, hr3, hr5, ht, hb]
  have h8pow : (8 : ℝ) ≤ (33 / 32 : ℝ) ^ l :=
    (by norm_num : (8 : ℝ) ≤ (33 / 32 : ℝ) ^ (128 : ℕ)).trans
      (pow_le_pow_right₀ (by norm_num) hl)
  have hlow : (8 : ℝ) * 32 ^ l ≤ m.choose l := by
    calc
      _ ≤ (33 / 32 : ℝ) ^ l * 32 ^ l := mul_le_mul_of_nonneg_right h8pow (by positivity)
      _ = (33 : ℝ) ^ l := by rw [← mul_pow]; norm_num
      _ ≤ _ := binomialLower (by omega) hml
  have hlogLower := Real.log_le_log (by positivity : 0 < (8 : ℝ) * 32 ^ l) hlow
  rw [Real.log_mul (by norm_num) (by positivity),
    show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num,
    ← pow_mul, Real.log_pow, Real.log_pow] at hlogLower
  push_cast at hlogLower
  have hkl : (k : ℝ) ≤ 2 * l + 1 := by
    exact_mod_cast (show k ≤ 2 * l + 1 by dsimp [l]; omega)
  have hcomp : (5 / 2 : ℝ) * k < 3 + 5 * l := by linarith
  have hstrict := mul_lt_mul_of_pos_right hcomp (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  nlinarith only [hlogUpper, hlogLower, hstrict]

end OMA.EcklundMiddleRange

theorem OMA.solution : OMA.R_Erdos384_erdos_384_R1_H2_R1.H3 :=
  OMA.EcklundMiddleRange.solve
