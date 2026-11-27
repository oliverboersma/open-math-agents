import FormalConjectures.ErdosProblems.«770»

import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Erdős 770(iii) from the large-prime subgroup bound

This adapts the merged R1 reduction by senamakel. Assume Dirichlet GRH and
the conditional subgroup bound for primes at least `2^17`. For large `n`,
the hypothesis `P(n) > n^ε` forces every bad prime `r > P(n)` into
that range, so this reduction needs no finite-range certificate.
-/

namespace OMA.R_Erdos770_erdos_770_parts_iii_R2

open Filter Finset Erdos770

def H1 : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

def H2 : Prop :=
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) →
  ∀ q : ℕ, q.Prime → 2 ^ 17 ≤ q → ∀ H : Subgroup (ZMod q)ˣ, H ≠ ⊤ →
    ∃ a : (ZMod q)ˣ, a ∉ H ∧ ((a : ZMod q).val : ℝ) ≤ 21 / 5 * Real.log q ^ 2

/- ## Elementary facts about `h` and the largest prime `p` with `p - 1 ∣ n` -/

lemma two_mem_P_set (n : ℕ) : 2 ∈ {m : ℕ | m.Prime ∧ m - 1 ∣ n} :=
  ⟨Nat.prime_two, by simp⟩

lemma P_set_bddAbove {n : ℕ} (hn : 1 ≤ n) : BddAbove {m : ℕ | m.Prime ∧ m - 1 ∣ n} :=
  ⟨n + 1, fun m hm => by have := Nat.le_of_dvd hn hm.2; omega⟩

lemma P_mem {n : ℕ} (hn : 1 ≤ n) :
    (sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}).Prime ∧ sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n} - 1 ∣ n :=
  Nat.sSup_mem ⟨2, two_mem_P_set n⟩ (P_set_bddAbove hn)

lemma le_P {n m : ℕ} (hn : 1 ≤ n) (hm : m.Prime) (hd : m - 1 ∣ n) :
    m ≤ sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n} :=
  le_csSup (P_set_bddAbove hn) ⟨hm, hd⟩

/-- `r ∣ aⁿ - 1` (natural subtraction) is `aⁿ = 1` in `ZMod r`, for `a ≥ 1`. -/
lemma dvd_pow_sub_one_iff {r a n : ℕ} (ha : 1 ≤ a) :
    r ∣ a ^ n - 1 ↔ (a : ZMod r) ^ n = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ ha)]
  push_cast
  exact sub_eq_zero

lemma dvd_gcdUpTo_iff {d n M : ℕ} :
    d ∣ ((Finset.Icc 2 M).image fun i => (i ^ n - 1)).gcd id ↔
      ∀ i, 2 ≤ i → i ≤ M → d ∣ i ^ n - 1 := by
  constructor
  · intro hd i hi hiM
    exact hd.trans (Finset.gcd_dvd (Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨hi, hiM⟩)))
  · intro hd
    apply Finset.dvd_gcd
    intro b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hb
    rw [Finset.mem_Icc] at hi
    exact hd i hi.1 hi.2

/-- `P n ≤ h n`: every `i` with `2 ≤ i < P n` has `P n ∣ iⁿ - 1`. -/
theorem P_le_h {n : ℕ} (hn : 1 ≤ n) :
    ((sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n} : ℕ) : ℕ∞) ≤ h n := by
  unfold h
  refine le_sInf ?_
  rintro m ⟨-, hg⟩
  induction m using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    simp only [ENat.toNat_natCast] at hg
    rw [Nat.cast_le]
    by_contra hlt
    push Not at hlt
    obtain ⟨hp, hd⟩ := P_mem hn
    generalize sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n} = p at hp hd hlt ⊢
    have := Fact.mk hp
    have hdiv : p ∣ ((Finset.Icc 2 m).image fun i => (i ^ n - 1)).gcd id := by
      rw [dvd_gcdUpTo_iff]
      intro i hi him
      rw [dvd_pow_sub_one_iff (by omega)]
      have hi0 : (i : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h
        have := Nat.le_of_dvd (by omega) h
        omega
      obtain ⟨t, ht⟩ := hd
      rw [ht, pow_mul, ZMod.pow_card_sub_one_eq_one hi0, one_pow]
    rw [hg] at hdiv
    exact hp.one_lt.ne' (Nat.dvd_one.1 hdiv)

/-- If `gcd(2ⁿ - 1, …, Mⁿ - 1) = 1` with `M > 2`, then `h n ≤ M`. -/
theorem h_le_of_gcd {n M : ℕ} (hM : 2 < M)
    (hg : ((Finset.Icc 2 M).image fun i => (i ^ n - 1)).gcd id = 1) : h n ≤ M :=
  sInf_le ⟨by exact_mod_cast hM, by simpa using hg⟩

/- ## The bad prime and the two bounds on it -/

theorem exists_bad_prime {n M : ℕ} (hn : 1 ≤ n) (hM : 2 ≤ M)
    (hg : ((Finset.Icc 2 M).image fun i => (i ^ n - 1)).gcd id ≠ 1) :
    ∃ r, r.Prime ∧ M < r ∧ r ≤ 2 ^ n - 1 ∧ ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1 := by
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hg
  have hdvd := dvd_gcdUpTo_iff.1 hrd
  refine ⟨r, hr, ?_, ?_, hdvd⟩
  · by_contra hle
    push Not at hle
    have h1 := hdvd r hr.two_le hle
    have h2 : r ∣ r ^ n := dvd_pow_self r (by omega)
    have h3 := Nat.dvd_sub h2 h1
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hr.pos)] at h3
    exact hr.one_lt.ne' (Nat.dvd_one.1 h3)
  · have h1 := hdvd 2 le_rfl hM
    have : 0 < 2 ^ n - 1 := by
      have : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    exact Nat.le_of_dvd this h1

/-- Bach's bound forces `M < (21/5) log² r`. -/
theorem lt_of_bach (h1 : H1) (h2 : H2) {n M r : ℕ} (hn : 1 ≤ n)
    (hMlarge : 2 ^ 17 ≤ M)
    (hr : r.Prime) (hMr : M < r) (hPM : sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n} ≤ M)
    (hdvd : ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1) :
    (M : ℝ) < 21 / 5 * Real.log r ^ 2 := by
  have := Fact.mk hr
  let H : Subgroup (ZMod r)ˣ := (powMonoidHom n : (ZMod r)ˣ →* (ZMod r)ˣ).ker
  have hmem : ∀ x : (ZMod r)ˣ, x ∈ H ↔ x ^ n = 1 := fun x => by
    simp [H, MonoidHom.mem_ker]
  have hH : H ≠ ⊤ := by
    intro htop
    have hall : ∀ x : (ZMod r)ˣ, x ^ n = 1 := fun x => (hmem x).1 (htop ▸ Subgroup.mem_top x)
    have hexp : Monoid.exponent (ZMod r)ˣ ∣ n := Monoid.exponent_dvd_of_forall_pow_eq_one hall
    rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units] at hexp
    have := le_P hn hr hexp
    omega
  obtain ⟨a, haH, hav⟩ := h2 h1 r hr (hMlarge.trans hMr.le) H hH
  refine lt_of_lt_of_le ?_ hav
  by_contra hle
  push Not at hle
  have hle' : (a : ZMod r).val ≤ M := by exact_mod_cast hle
  have hv0 : (a : ZMod r).val ≠ 0 := by
    rw [Ne, ZMod.val_eq_zero]
    exact a.ne_zero
  apply haH
  rw [hmem]
  ext
  push_cast
  rw [← ZMod.natCast_zmod_val (a : ZMod r)]
  rcases Nat.lt_or_ge (a : ZMod r).val 2 with h | h
  · have : (a : ZMod r).val = 1 := by omega
    rw [this]
    simp
  · exact (dvd_pow_sub_one_iff (by omega)).1 (hdvd _ h hle')

/-- The counting bound: `(π K).choose j ≤ n` when `K ≤ M` and `K ^ j < r`. -/
theorem choose_le_of_bad {n M r : ℕ} (hn : 1 ≤ n) (hr : r.Prime)
    (hdvd : ∀ i, 2 ≤ i → i ≤ M → r ∣ i ^ n - 1) (K j : ℕ) (hKM : K ≤ M) (hKj : K ^ j < r) :
    (Nat.primeCounting K).choose j ≤ n := by
  classical
  have := Fact.mk hr
  rw [← Nat.primesLE_card_eq_primeCounting, ← Finset.card_powersetCard]
  set A := (Nat.primesLE K).powersetCard j
  let f : Finset ℕ → ZMod r := fun T => ((∏ p ∈ T, p : ℕ) : ZMod r)
  have hprime : ∀ T ∈ A, ∀ p ∈ T, p.Prime ∧ p ≤ K := fun T hT p hp => by
    rw [Finset.mem_powersetCard] at hT
    exact (Nat.mem_primesLE.1 (hT.1 hp)).symm
  have hlt : ∀ T ∈ A, ∏ p ∈ T, p < r := fun T hT => by
    have hc := (Finset.mem_powersetCard.1 hT).2
    calc ∏ p ∈ T, p ≤ K ^ T.card := Finset.prod_le_pow_card T id K fun p hp => (hprime T hT p hp).2
      _ = K ^ j := by rw [hc]
      _ < r := hKj
  have hmaps : ∀ T ∈ A, f T ∈ (Polynomial.nthRoots n (1 : ZMod r)).toFinset := fun T hT => by
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
    simp only [f, Nat.cast_prod]
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro p hp
    obtain ⟨hpp, hpK⟩ := hprime T hT p hp
    exact (dvd_pow_sub_one_iff hpp.one_lt.le).1 (hdvd p hpp.two_le (hpK.trans hKM))
  have hinj : Set.InjOn f A := fun T hT T' hT' hTT' => by
    have h1 := (ZMod.natCast_eq_natCast_iff' _ _ r).1 hTT'
    rw [Nat.mod_eq_of_lt (hlt T hT), Nat.mod_eq_of_lt (hlt T' hT')] at h1
    have := congrArg Nat.primeFactors h1
    rwa [Nat.primeFactors_prod fun p hp => (hprime T hT p hp).1,
      Nat.primeFactors_prod fun p hp => (hprime T' hT' p hp).1] at this
  calc A.card ≤ (Polynomial.nthRoots n (1 : ZMod r)).toFinset.card :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ Multiset.card (Polynomial.nthRoots n (1 : ZMod r)) := Multiset.toFinset_card_le _
    _ ≤ n := Polynomial.card_nthRoots n 1

/- ## The numerical inequality behind the large-`r` case

For `n ≥ 3` put `u = log n`, `K = ⌈420 u²⌉` and `j = ⌊10 u / log K⌋`. Then `K ^ j ≤ n ^ 10`
and `n < (π K).choose j`, using Chebyshev's bound `π(K) log K ≥ K log 2 - log (K + 1)`.
-/

lemma log_twentyone_lt_four : Real.log 21 < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : (4 : ℝ) = 1 + 1 + 1 + 1 := by norm_num
  rw [this, Real.exp_add, Real.exp_add, Real.exp_add]
  have h0 : (0 : ℝ) < 2.7182818283 := by norm_num
  have h1 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ h0.le h.le 4
  nlinarith [h1]

theorem numeric {n : ℕ} (hn : 3 ≤ n) :
    ∃ j : ℕ, ⌈420 * Real.log n ^ 2⌉₊ ^ j ≤ n ^ 10 ∧
      n < (Nat.primeCounting ⌈420 * Real.log n ^ 2⌉₊).choose j := by
  set u := Real.log n with hu_def
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hu1 : 1 ≤ u := by
    rw [hu_def, Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  set K := ⌈420 * u ^ 2⌉₊ with hK_def
  have hK1 : 420 * u ^ 2 ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) < 420 * u ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hK3 : (K : ℝ) ≤ (21 * u) ^ 2 := by nlinarith
  have hK3' : (K : ℝ) + 1 ≤ (21 * u) ^ 2 := by nlinarith
  have hK7 : 7 ≤ K := by
    have : (7 : ℝ) ≤ K := by nlinarith
    exact_mod_cast this
  have hKpos : (0 : ℝ) < K := by positivity
  set L := Real.log K with hL_def
  have hL0 : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < K))
  set ℓ := Real.log (21 * u) with hℓ_def
  have hℓ0 : 0 < ℓ := Real.log_pos (by linarith)
  have hLℓ : L ≤ 2 * ℓ := by
    have := Real.log_le_log hKpos hK3
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hL1ℓ : Real.log ((K : ℝ) + 1) ≤ 2 * ℓ := by
    have := Real.log_le_log (by positivity) hK3'
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hℓu : ℓ < 4 * u := by
    rw [hℓ_def, Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < u)
    have := log_twentyone_lt_four
    linarith
  -- Chebyshev
  set s := Nat.primeCounting K with hs_def
  have hs : (K : ℝ) * Real.log 2 - Real.log ((K : ℝ) + 1) ≤ s * L :=
    (Chebyshev.psi_ge K).trans (Chebyshev.psi_le_primeCounting_mul_log K)
  have hlog2 := Real.log_two_gt_d9
  set j := ⌊10 * u / L⌋₊ with hj_def
  have hj1 : (j : ℝ) * L ≤ 10 * u := by
    have := Nat.floor_le (by positivity : 0 ≤ 10 * u / L)
    rwa [← hj_def, le_div_iff₀ hL0] at this
  have hj2 : 10 * u < (j + 1) * L := by
    have := Nat.lt_floor_add_one (10 * u / L)
    rwa [← hj_def, div_lt_iff₀ hL0] at this
  refine ⟨j, ?_, ?_⟩
  · -- K ^ j ≤ n ^ 10
    have : ((K : ℝ)) ^ j ≤ (n : ℝ) ^ 10 := by
      rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith
    exact_mod_cast this
  · -- n < choose s j
    have hjℓ : u < j * ℓ := by nlinarith
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h] at hjℓ; simp at hjℓ; linarith
      · exact h
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj0
    -- s ≥ (21 u + 1) j
    have hsj : (21 * u + 1) * j ≤ s := by
      have h0 : (j : ℝ) * L * (22 * u) ≤ 220 * u ^ 2 := by nlinarith
      have h1 : (j : ℝ) * L * (22 * u) ≤ s * L := by nlinarith
      have h2 : (j : ℝ) * (22 * u) ≤ s := le_of_mul_le_mul_right (by linarith) hL0
      nlinarith
    have hjs : j ≤ s + 1 := by
      have : (j : ℝ) ≤ s := by nlinarith
      exact_mod_cast (by linarith : (j : ℝ) ≤ s + 1)
    have hcast : ((s + 1 - j : ℕ) : ℝ) = s + 1 - j := by
      rw [Nat.cast_sub hjs]; push_cast; ring
    have hbase : 21 * u * j ≤ ((s + 1 - j : ℕ) : ℝ) := by rw [hcast]; nlinarith
    have hfac : ((j.factorial : ℕ) : ℝ) ≤ (j : ℝ) ^ j := by exact_mod_cast Nat.factorial_le_pow j
    have hfacpos : (0 : ℝ) < (j.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos j
    have hchoose : (21 * u) ^ j ≤ (s.choose j : ℝ) := by
      refine le_trans ?_ (Nat.pow_le_choose j s)
      rw [le_div_iff₀ hfacpos]
      have h21 : (0 : ℝ) ≤ 21 * u := by linarith
      calc (21 * u) ^ j * (j.factorial : ℕ) ≤ (21 * u) ^ j * (j : ℝ) ^ j :=
            mul_le_mul_of_nonneg_left hfac (pow_nonneg h21 j)
        _ = (21 * u * j) ^ j := by ring
        _ ≤ ((s + 1 - j : ℕ) : ℝ) ^ j :=
            pow_le_pow_left₀ (mul_nonneg h21 hjpos.le) hbase j
    have hpow : (n : ℝ) < (21 * u) ^ j := by
      rw [← Real.log_lt_log_iff hnpos (by positivity), Real.log_pow]
      linarith
    exact_mod_cast hpow.trans_le hchoose

/- ## The explicit bound and part (iii) -/

/-- Bound for `n ≥ 2` once `P n` reaches the analytic cutoff. -/
theorem explicitBound (h1 : H1) (h2 : H2) (n : ℕ) (hn : 2 ≤ n)
    (hP : 2 ^ 17 ≤ sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}) :
    h n ≤ ((max (sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}) ⌈420 * Real.log n ^ 2⌉₊ : ℕ) : ℕ∞) := by
  set K := ⌈420 * Real.log n ^ 2⌉₊ with hK_def
  set M := max (sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n}) K with hM_def
  have hlog2 : (0.69 : ℝ) < Real.log n := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith
  have hK3 : 2 < K := by
    rw [hK_def, Nat.lt_ceil]
    push_cast
    nlinarith
  have hKM : K ≤ M := le_max_right _ _
  apply h_le_of_gcd (by omega)
  by_contra hg
  obtain ⟨r, hr, hMr, hr2, hdvd⟩ := exists_bad_prime (by omega) (by omega) hg
  have hlt := lt_of_bach h1 h2 (by omega) (hP.trans (le_max_left _ _))
    hr hMr (le_max_left _ _) hdvd
  by_cases hsmall : r ≤ n ^ 10
  · have hlogr : Real.log r ≤ 10 * Real.log n := by
      have := Real.log_le_log (by exact_mod_cast hr.pos : (0 : ℝ) < r)
        (by exact_mod_cast hsmall : (r : ℝ) ≤ ((n ^ 10 : ℕ) : ℝ))
      rw [Nat.cast_pow, Real.log_pow] at this
      push_cast at this
      linarith
    have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg (by exact_mod_cast hr.one_lt.le)
    have hh1 : (21 / 5) * Real.log r ^ 2 ≤ 420 * Real.log n ^ 2 := by nlinarith
    have hh2 : 420 * Real.log n ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
    have hh3 : (K : ℝ) ≤ M := by exact_mod_cast hKM
    linarith
  · push Not at hsmall
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · have : n = 2 := by omega
      subst this
      norm_num at hr2 hsmall
      omega
    · obtain ⟨j, hj1, hj2⟩ := numeric hn3
      rw [← hK_def] at hj1 hj2
      have := choose_le_of_bad (by omega) hr hdvd K j hKM (lt_of_le_of_lt hj1 hsmall)
      omega

/-- `C (log x)² + 1 < x^ε` for large `x`. -/
lemma eventually_lt_rpow (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ 2 + 1 < x ^ ε := by
  have hO := isLittleO_log_rpow_rpow_atTop 2 hε
  set c : ℝ := 1 / (2 * (|C| + 1)) with hc_def
  have hc0 : 0 < c := by positivity
  have hCc : |C| * c < 1 / 2 := by
    rw [hc_def]
    rw [show |C| * (1 / (2 * (|C| + 1))) = |C| / (|C| + 1) / 2 by field_simp]
    have : |C| / (|C| + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  filter_upwards [hO.bound hc0, (tendsto_rpow_atTop hε).eventually_ge_atTop 2,
    eventually_gt_atTop 0] with x hx hx2 hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ ε),
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    abs_of_nonneg (by positivity)] at hx
  have e1 : C * Real.log x ^ 2 ≤ |C| * Real.log x ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  have e2 : |C| * Real.log x ^ 2 ≤ |C| * (c * x ^ ε) :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg C)
  have e3 : |C| * (c * x ^ ε) = (|C| * c) * x ^ ε := by ring
  have e4 : (|C| * c) * x ^ ε < 1 / 2 * x ^ ε :=
    mul_lt_mul_of_pos_right hCc (by positivity)
  linarith

theorem main : H1 → H2 → type_of% @Erdos770.erdos_770.parts.iii := by
  intro h1 h2 ε hε
  have hreal := eventually_lt_rpow 420 hε
  have hlarge : ∀ᶠ n : ℕ in atTop, (2 ^ 17 : ℝ) ≤ (n : ℝ) ^ ε :=
    tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hε).eventually_ge_atTop _)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hreal, eventually_ge_atTop 2, hlarge]
    with n hn hn2 hnlarge
  intro p hp
  have hKp : ⌈(420 : ℝ) * Real.log n ^ 2⌉₊ ≤ sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n} := by
    rw [Nat.ceil_le]
    have : (p : ℝ) = ((sSup {m : ℕ | m.Prime ∧ m - 1 ∣ n} : ℕ) : ℝ) := rfl
    linarith
  have hpLarge : 2 ^ 17 ≤ p := by exact_mod_cast hnlarge.trans hp.le
  have hup := explicitBound h1 h2 n hn2 hpLarge
  rw [max_eq_left hKp] at hup
  exact le_antisymm hup (P_le_h (by omega))

end OMA.R_Erdos770_erdos_770_parts_iii_R2
