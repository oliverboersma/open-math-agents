import OMAReductions.R_Erdos770_erdos_770_parts_iii_R1
import Mathlib

-- Step Erdos770.erdos_770.parts.iii.R1.H2: hypothesis H2 of reduction Erdos770.erdos_770.parts.iii.R1
-- Credit: @ivillar
-- Proof: every prime q < 2^17 has a primitive root g with g <= 21/5 (log q)^2 (the largest needed is
-- 69, at q = 110881). A primitive root generates the whole unit group, so it lies outside every proper
-- subgroup. The roots are found and certified by a kernel computation (decide +kernel) over all
-- q < 2^17, using gcd with 362! as an exact primality test below 2^17 and the Lucas-style criterion
-- (g^((q-1)/p) != 1 for every prime p | q - 1) for the order of g.

namespace OMA.E770H2

/-- Binary modular exponentiation with fuel: `pm m f b e = b ^ e % m` once `e < 2 ^ f`. -/
def pm (m : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1 % m
  | f + 1, b, e =>
    if e = 0 then 1 % m
    else if e % 2 = 1 then pm m f (b * b % m) (e / 2) * b % m
    else pm m f (b * b % m) (e / 2)

/-- `allBelow P n` checks `P k` for every `k < n`. -/
def allBelow (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | k + 1 => P k && allBelow P k

/-- `anyFrom P i f` searches `P i, P (i+1), ..., P (i+f-1)`. -/
def anyFrom (P : ℕ → Bool) : ℕ → ℕ → Bool
  | _, 0 => false
  | i, f + 1 => P i || anyFrom P (i + 1) f

/-- The primes up to `362` (only completeness of this list is used). -/
def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359]

/-- A number divisible by every prime power below `2 ^ 17` whose prime is at most `362`. -/
def F : ℕ := Nat.factorial 362 ^ 17

/-- An exact primality test below `2 ^ 17`. -/
def isPr (f : ℕ) : Bool :=
  2 ≤ f && (if f ≤ 362 then allBelow (fun d => d < 2 || !(d * d ≤ f) || f % d != 0) 20
    else Nat.gcd f (Nat.factorial 362) == 1)

/-- The part of `n` without prime factors up to `362`. -/
def cof (n : ℕ) : ℕ := n / Nat.gcd n F

/-- `g ^ ((q - 1) / p) ≠ 1` modulo `q` for each prime `p ∣ q - 1`. -/
def rootCert (q g : ℕ) : Bool :=
  smallPrimes.all (fun l => (q - 1) % l != 0 || pm q 17 g ((q - 1) / l) != 1) &&
    (cof (q - 1) == 1 || (isPr (cof (q - 1)) && pm q 17 g ((q - 1) / cof (q - 1)) != 1))

def bound (q : ℕ) : ℕ :=
  if q < 4 then 2 else if q < 8 then 6 else if q < 16 then 15 else if q < 32 then 25
  else if q < 64 then 40 else 70

def check (q : ℕ) : Bool :=
  !isPr q || anyFrom (fun g => g < q && rootCert q g) 1 (bound q)

/-! ### Correctness of the checker -/

theorem pm_eq (m : ℕ) : ∀ f b e, e < 2 ^ f → pm m f b e = b ^ e % m := by
  intro f
  induction f with
  | zero =>
    intro b e he
    have : e = 0 := by simpa using he
    subst this
    simp [pm]
  | succ f ih =>
    intro b e he
    have he2 : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
    rw [pm]
    split_ifs with h0 h1
    · subst h0
      simp
    · rw [ih _ _ he2]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k + 1 := ⟨e / 2, by omega⟩
      have hk : (2 * k + 1) / 2 = k := by omega
      rw [hk, ← Nat.pow_mod, Nat.mod_mul_mod, pow_succ, pow_mul, sq]
    · rw [ih _ _ he2]
      obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
      have hk : 2 * k / 2 = k := by omega
      rw [hk, ← Nat.pow_mod, pow_mul, sq]

theorem allBelow_iff (P : ℕ → Bool) (n : ℕ) : allBelow P n = true ↔ ∀ k < n, P k = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact h2 k h
      · subst h
        exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

theorem anyFrom_true (P : ℕ → Bool) : ∀ f i, anyFrom P i f = true →
    ∃ g, i ≤ g ∧ g < i + f ∧ P g = true := by
  intro f
  induction f with
  | zero =>
    intro i h
    simp [anyFrom] at h
  | succ f ih =>
    intro i h
    simp only [anyFrom, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨i, le_rfl, by omega, h⟩
    · obtain ⟨g, h1, h2, h3⟩ := ih (i + 1) h
      exact ⟨g, by omega, by omega, h3⟩

theorem isPr_complete {f : ℕ} (hf : f.Prime) : isPr f = true := by
  have h2 := hf.two_le
  unfold isPr
  split_ifs with hle
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨h2, (allBelow_iff _ _).mpr ?_⟩
    intro k _
    by_contra hc
    have hk2 : 2 ≤ k := by
      by_contra h
      apply hc
      simp [show k < 2 by omega]
    have hkk : k * k ≤ f := by
      by_contra h
      apply hc
      simp [h]
    have hmod : f % k = 0 := by
      by_contra h
      apply hc
      simp [h]
    have hdvd : k ∣ f := Nat.dvd_of_mod_eq_zero hmod
    rcases hf.eq_one_or_self_of_dvd k hdvd with h | h
    · omega
    · subst h
      nlinarith
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨h2, ?_⟩
    exact (Nat.Prime.coprime_iff_not_dvd hf).mpr (fun h => hle ((hf.dvd_factorial).mp h))

theorem isPr_sound {f : ℕ} (hlt : f < 2 ^ 17) (h : isPr f = true) : f.Prime := by
  unfold isPr at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, h⟩ := h
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hmp : (Nat.minFac f).Prime := Nat.minFac_prime (by omega)
  have hm2 := hmp.two_le
  have hmd : Nat.minFac f ∣ f := Nat.minFac_dvd f
  split_ifs at h with hle
  · have hm20 : Nat.minFac f < 20 := by nlinarith
    have := (allBelow_iff _ _).mp h _ hm20
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      bne_iff_ne, ne_eq] at this
    rcases this with (h3 | h3) | h3
    · omega
    · exact h3 (by nlinarith)
    · exact h3 (Nat.mod_eq_zero_of_dvd hmd)
  · simp only [beq_iff_eq] at h
    have hm362 : Nat.minFac f ≤ 362 := by nlinarith
    have hfac : Nat.minFac f ∣ Nat.factorial 362 := Nat.dvd_factorial (by omega) hm362
    have := Nat.dvd_gcd hmd hfac
    rw [h] at this
    have := Nat.le_of_dvd one_pos this
    omega

theorem smallPrimes_complete {p : ℕ} (hp : p.Prime) (hle : p ≤ 362) : p ∈ smallPrimes := by
  have h : allBelow (fun p => !isPr p || smallPrimes.contains p) 363 = true := by decide +kernel
  have := (allBelow_iff _ _).mp h p (by omega)
  rw [isPr_complete hp] at this
  simpa using this

theorem rootCert_sound {q g : ℕ} (hq : q < 2 ^ 17) (h : rootCert q g = true) :
    ∀ p, p.Prime → p ∣ q - 1 → g ^ ((q - 1) / p) % q ≠ 1 := by
  unfold rootCert at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  intro p hp hpd
  have hn : q - 1 < 2 ^ 17 := by omega
  by_cases hle : p ≤ 362
  · have := hA p (smallPrimes_complete hp hle)
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with h1 | h1
    · exact absurd (Nat.mod_eq_zero_of_dvd hpd) h1
    · rwa [pm_eq q 17 g _ (lt_of_le_of_lt (Nat.div_le_self _ _) hn)] at h1
  · have hpF : ¬ p ∣ F := fun hd => hle ((hp.dvd_factorial).mp (hp.dvd_of_dvd_pow hd))
    have hpS : ¬ p ∣ Nat.gcd (q - 1) F := fun hd => hpF (hd.trans (Nat.gcd_dvd_right _ _))
    have hSR : Nat.gcd (q - 1) F * cof (q - 1) = q - 1 :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hpR : p ∣ cof (q - 1) := by
      rw [← hSR] at hpd
      exact ((Nat.Prime.dvd_mul hp).mp hpd).resolve_left hpS
    have hR1 : cof (q - 1) ≠ 1 := by
      intro h1
      rw [h1] at hpR
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpR)
    have hRle : cof (q - 1) ≤ q - 1 := Nat.div_le_self _ _
    simp only [Bool.or_eq_true, beq_iff_eq, hR1, false_or, Bool.and_eq_true, bne_iff_ne,
      ne_eq] at hB
    obtain ⟨hRp, hpm⟩ := hB
    have hRprime := isPr_sound (by omega) hRp
    have hpeq : p = cof (q - 1) := (Nat.prime_dvd_prime_iff_eq hp hRprime).mp hpR
    rw [← hpeq] at hpm
    rwa [pm_eq q 17 g _ (lt_of_le_of_lt (Nat.div_le_self _ _) hn)] at hpm

theorem bound_real {q g : ℕ} (hq2 : 2 ≤ q) (hg : g ≤ bound q) :
    (g : ℝ) ≤ 21 / 5 * Real.log q ^ 2 := by
  have hl2 := Real.log_two_gt_d9
  have key : ∀ k : ℕ, 2 ^ k ≤ q → ((k : ℝ) * 0.6931471803) ^ 2 ≤ Real.log q ^ 2 := by
    intro k hk
    have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log q :=
      Real.log_le_log (by positivity) (by exact_mod_cast hk)
    rw [Real.log_pow] at h1
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : (k : ℝ) * 0.6931471803 ≤ Real.log q := by nlinarith
    exact pow_le_pow_left₀ (by positivity) h3 2
  unfold bound at hg
  split_ifs at hg with h1 h2 h3 h4 h5
  · have := key 1 (by omega)
    have hg' : (g : ℝ) ≤ 2 := by exact_mod_cast hg
    norm_num at this
    nlinarith
  · have := key 2 (by omega)
    have hg' : (g : ℝ) ≤ 6 := by exact_mod_cast hg
    norm_num at this
    nlinarith
  · have := key 3 (by omega)
    have hg' : (g : ℝ) ≤ 15 := by exact_mod_cast hg
    norm_num at this
    nlinarith
  · have := key 4 (by omega)
    have hg' : (g : ℝ) ≤ 25 := by exact_mod_cast hg
    norm_num at this
    nlinarith
  · have := key 5 (by omega)
    have hg' : (g : ℝ) ≤ 40 := by exact_mod_cast hg
    norm_num at this
    nlinarith
  · have := key 6 (by omega)
    have hg' : (g : ℝ) ≤ 70 := by exact_mod_cast hg
    norm_num at this
    nlinarith

/-! ### The computation, in 32 blocks of 4096 -/

set_option maxHeartbeats 0 in
theorem ch0 : allBelow (fun i => check (0 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch1 : allBelow (fun i => check (1 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch2 : allBelow (fun i => check (2 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch3 : allBelow (fun i => check (3 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch4 : allBelow (fun i => check (4 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch5 : allBelow (fun i => check (5 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch6 : allBelow (fun i => check (6 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch7 : allBelow (fun i => check (7 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch8 : allBelow (fun i => check (8 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch9 : allBelow (fun i => check (9 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch10 : allBelow (fun i => check (10 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch11 : allBelow (fun i => check (11 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch12 : allBelow (fun i => check (12 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch13 : allBelow (fun i => check (13 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch14 : allBelow (fun i => check (14 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch15 : allBelow (fun i => check (15 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch16 : allBelow (fun i => check (16 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch17 : allBelow (fun i => check (17 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch18 : allBelow (fun i => check (18 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch19 : allBelow (fun i => check (19 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch20 : allBelow (fun i => check (20 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch21 : allBelow (fun i => check (21 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch22 : allBelow (fun i => check (22 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch23 : allBelow (fun i => check (23 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch24 : allBelow (fun i => check (24 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch25 : allBelow (fun i => check (25 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch26 : allBelow (fun i => check (26 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch27 : allBelow (fun i => check (27 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch28 : allBelow (fun i => check (28 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch29 : allBelow (fun i => check (29 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch30 : allBelow (fun i => check (30 * 4096 + i)) 4096 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ch31 : allBelow (fun i => check (31 * 4096 + i)) 4096 = true := by
  decide +kernel

theorem fromChunk (c : ℕ) (h : allBelow (fun i => check (c * 4096 + i)) 4096 = true) (q : ℕ)
    (hq : q / 4096 = c) : check q = true := by
  have := (allBelow_iff _ _).mp h (q % 4096) (Nat.mod_lt _ (by norm_num))
  have e : c * 4096 + q % 4096 = q := by subst hq; omega
  rwa [e] at this

theorem allCheck (q : ℕ) (hq : q < 2 ^ 17) : check q = true := by
  have hc : q / 4096 < 32 := by omega
  generalize hk : q / 4096 = c at hc
  interval_cases c
  · exact fromChunk 0 ch0 q hk
  · exact fromChunk 1 ch1 q hk
  · exact fromChunk 2 ch2 q hk
  · exact fromChunk 3 ch3 q hk
  · exact fromChunk 4 ch4 q hk
  · exact fromChunk 5 ch5 q hk
  · exact fromChunk 6 ch6 q hk
  · exact fromChunk 7 ch7 q hk
  · exact fromChunk 8 ch8 q hk
  · exact fromChunk 9 ch9 q hk
  · exact fromChunk 10 ch10 q hk
  · exact fromChunk 11 ch11 q hk
  · exact fromChunk 12 ch12 q hk
  · exact fromChunk 13 ch13 q hk
  · exact fromChunk 14 ch14 q hk
  · exact fromChunk 15 ch15 q hk
  · exact fromChunk 16 ch16 q hk
  · exact fromChunk 17 ch17 q hk
  · exact fromChunk 18 ch18 q hk
  · exact fromChunk 19 ch19 q hk
  · exact fromChunk 20 ch20 q hk
  · exact fromChunk 21 ch21 q hk
  · exact fromChunk 22 ch22 q hk
  · exact fromChunk 23 ch23 q hk
  · exact fromChunk 24 ch24 q hk
  · exact fromChunk 25 ch25 q hk
  · exact fromChunk 26 ch26 q hk
  · exact fromChunk 27 ch27 q hk
  · exact fromChunk 28 ch28 q hk
  · exact fromChunk 29 ch29 q hk
  · exact fromChunk 30 ch30 q hk
  · exact fromChunk 31 ch31 q hk

end OMA.E770H2

open OMA.E770H2 in
theorem OMA.solution : OMA.R_Erdos770_erdos_770_parts_iii_R1.H2 := by
  unfold OMA.R_Erdos770_erdos_770_parts_iii_R1.H2
  intro q hq hq17 H hH
  have hq2 := hq.two_le
  have hcheck := allCheck q hq17
  unfold check at hcheck
  rw [isPr_complete hq] at hcheck
  simp only [Bool.not_true, Bool.false_or] at hcheck
  obtain ⟨g, hg1, hg2, hg⟩ := anyFrom_true _ _ _ hcheck
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨hgq, hroot⟩ := hg
  have hfact : Fact q.Prime := ⟨hq⟩
  have hcop : Nat.Coprime g q := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr
      (fun h => absurd (Nat.le_of_dvd (by omega) h) (not_le.mpr hgq))
  have hord : orderOf (ZMod.unitOfCoprime g hcop) = q - 1 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by omega)
      (ZMod.units_pow_card_sub_one_eq_one q _)
    intro p hp hpd heq
    apply rootCert_sound hq17 hroot p hp hpd
    have h1 : (((ZMod.unitOfCoprime g hcop) ^ ((q - 1) / p) : (ZMod q)ˣ) : ZMod q) = 1 := by
      rw [heq]
      simp
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow] at h1
    have h2 := (ZMod.natCast_eq_natCast_iff' (g ^ ((q - 1) / p)) 1 q).mp (by simpa using h1)
    rwa [Nat.mod_eq_of_lt (by omega : 1 < q)] at h2
  refine ⟨ZMod.unitOfCoprime g hcop, ?_, ?_⟩
  · intro hu
    apply hH
    have hz : Subgroup.zpowers (ZMod.unitOfCoprime g hcop) = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord, Nat.card_eq_fintype_card, ZMod.card_units]
    rw [eq_top_iff, ← hz]
    exact Subgroup.zpowers_le.mpr hu
  · rw [ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt hgq]
    exact bound_real hq2 (by omega)
