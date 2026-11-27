import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2

/-!
# Reduction of Agoh-Giuga step R2.H3 (3-free multi-unit k ≥ 2 regime)

Reduction `AgohGiuga.agoh_giuga.variants.giuga.R2.H3.R1` by `@hackoria`.

We prove unconditionally from the hypotheses of `R2.H3` (`3 ∤ n`, `k ≥ 2`):
1. **Gauss Quadratic Reciprocity obstruction:** evaluating `∏_{p ∣ n} J(n / p | p) = 1`
   via `jacobiSym.quadratic_reciprocity` forces `r3 % 4 = 0 ∨ r3 % 4 = 1`, where
   `r3 = #{p ∣ n : p ≡ 3 (mod 4)}`.
2. **Three-way mod-4 Korselt trichotomy + logarithmic-harmonic lower bounds:**
   - **Sub-regime `H1` (mixed mod 4, `∃ p ∣ n, p ≡ 1 (mod 4)`):** forces `n % 4 = 1`,
     `4 ∣ r3`, `r1 % 4 = (k + 1) % 4`, `ω(n) % 4 = (k + 1) % 4`, and `90 ≤ ω(n)` (upgraded from `65`).
   - **Sub-regime `H2` (all `p ≡ 3 (mod 4)`, `4 ∣ ω(n)`):** forces `7 ≤ p` and `p % 12 = 7 ∨ p % 12 = 11`,
     `n % 4 = 1`, `k % 4 = 3`, `3 ≤ k`, and `100000 ≤ ω(n)`.
   - **Sub-regime `H3` (all `p ≡ 3 (mod 4)`, `ω(n) % 4 = 1`):** forces `7 ≤ p` and `p % 12 = 7 ∨ p % 12 = 11`,
     `n % 4 = 3`, `4 ∣ k`, `4 ≤ k`, and `5000000 ≤ ω(n)`.
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H3_R1

open AgohGiuga
open scoped Nat

-- Sub-regime 3A: 3-free multi-unit (k ≥ 2) strong Giuga number with at least one p ≡ 1 (mod 4).
def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) →
    n % 4 = 1 →
    90 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (∀ p ∈ n.primeFactors, 5 ≤ p) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 2 ≤ k ∧
      n.primeFactors.card % 4 = (k + 1) % 4 ∧
      (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 ∧
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

-- Sub-regime 3B: 3-free multi-unit strong Giuga number with all p ≡ 3 (mod 4) and 4 ∣ ω(n).
def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) →
    n % 4 = 1 →
    4 ∣ n.primeFactors.card → 100000 ≤ n.primeFactors.card →
    (∀ p ∈ n.primeFactors, 7 ≤ p ∧ p % 4 = 3) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 3 ≤ k ∧ k % 4 = 3 ∧
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

-- Sub-regime 3C: 3-free multi-unit strong Giuga number with all p ≡ 3 (mod 4) and ω(n) % 4 = 1.
def H3 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) →
    n % 4 = 3 →
    n.primeFactors.card % 4 = 1 → 5000000 ≤ n.primeFactors.card →
    (∀ p ∈ n.primeFactors, 7 ≤ p ∧ p % 4 = 3) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 4 ≤ k ∧ 4 ∣ k ∧
      ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

/- ### Section 1: Basic arithmetic and integer sum identity -/

lemma prod_primeFactors_of_sqf {n : ℕ} (hsqf : Squarefree n) (hn0 : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p = n := by
  conv_rhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hle : n.factorization p ≤ 1 := by
    by_contra hgt
    have h2 : 2 ≤ n.factorization p := by omega
    have hsq : p * p ∣ n := by
      have hpow : p ^ 2 ∣ n := (pow_dvd_pow p h2).trans (Nat.ordProj_dvd n p)
      simpa [sq] using hpow
    exact hp_prime.ne_one (Nat.isUnit_iff.mp (hsqf p hsq))
  have hge : 1 ≤ n.factorization p := (hp_prime.dvd_iff_one_le_factorization hn0).mp hp_dvd
  have heq : n.factorization p = 1 := by omega
  rw [heq, pow_one]

lemma sum_div_eq_mul_add_one {n k : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    ∑ p ∈ n.primeFactors, n / p = k * n + 1 := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hmul : (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ)) * (n : ℚ) = (k : ℚ) * (n : ℚ) :=
    congrArg (· * (n : ℚ)) hsum
  rw [sub_mul, Finset.sum_mul, one_div_mul_cancel hnQ] at hmul
  have hterms : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) * (n : ℚ) =
      ((∑ p ∈ n.primeFactors, n / p : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
    have hcancel : ((n / p : ℕ) : ℚ) * (p : ℚ) = (n : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hp_dvd
    rw [← hcancel, one_div, inv_mul_eq_iff_eq_mul₀ hp0]
    ring
  rw [hterms] at hmul
  have hcast : ((∑ p ∈ n.primeFactors, n / p : ℕ) : ℚ) = ((k * n + 1 : ℕ) : ℚ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    linarith
  exact Nat.cast_injective hcast

/- ### Section 2: Gauss Quadratic Reciprocity obstruction -/

lemma jacobiSym_prod_left (s : Finset ℕ) (b : ℕ) :
    jacobiSym ((∏ y ∈ s, y : ℕ) : ℤ) b = ∏ y ∈ s, jacobiSym (y : ℤ) b := by
  induction s using Finset.cons_induction with
  | empty => simp [jacobiSym.one_left]
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Nat.cast_mul, jacobiSym.mul_left, ih]

lemma prod_jacobiSym_offDiag (s : Finset ℕ)
    (hodd_s : ∀ x ∈ s, Odd x)
    (hcop : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Nat.Coprime x y) :
    ∏ x ∈ s, ∏ y ∈ s.erase x, jacobiSym (y : ℤ) x =
      (-1 : ℤ) ^ ((s.filter (fun p => p % 4 = 3)).card.choose 2) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha_odd : Odd a := hodd_s a (Finset.mem_cons_self a s)
    have hs_odd : ∀ x ∈ s, Odd x := fun x hx => hodd_s x (Finset.mem_cons_of_mem hx)
    have hs_cop : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Nat.Coprime x y :=
      fun x hx y hy hxy => hcop x (Finset.mem_cons_of_mem hx) y (Finset.mem_cons_of_mem hy) hxy
    have hih := ih hs_odd hs_cop
    rw [Finset.prod_cons]
    have herase_a : (Finset.cons a s ha).erase a = s := by
      ext y
      simp only [Finset.mem_erase, Finset.mem_cons]
      constructor
      · rintro ⟨hne, rfl | hy⟩
        · exact absurd rfl hne
        · exact hy
      · intro hy
        exact ⟨fun h => ha (h ▸ hy), Or.inr hy⟩
    rw [herase_a]
    have hinner : ∀ x ∈ s,
        ∏ y ∈ (Finset.cons a s ha).erase x, jacobiSym (y : ℤ) x =
          jacobiSym (a : ℤ) x * ∏ y ∈ s.erase x, jacobiSym (y : ℤ) x := by
      intro x hx
      have hne : a ≠ x := fun h => ha (h ▸ hx)
      have ha_not : a ∉ s.erase x := fun h => ha (Finset.mem_of_mem_erase h)
      have heq : (Finset.cons a s ha).erase x = Finset.cons a (s.erase x) ha_not := by
        ext y
        simp only [Finset.mem_erase, Finset.mem_cons]
        constructor
        · rintro ⟨hyx, rfl | hys⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hyx, hys⟩
        · rintro (rfl | ⟨hyx, hys⟩)
          · exact ⟨hne, Or.inl rfl⟩
          · exact ⟨hyx, Or.inr hys⟩
      rw [heq, Finset.prod_cons]
    rw [Finset.prod_congr rfl hinner, Finset.prod_mul_distrib, ← mul_assoc,
      ← Finset.prod_mul_distrib, hih]
    have hpair : ∀ y ∈ s,
        jacobiSym (y : ℤ) a * jacobiSym (a : ℤ) y = (-1 : ℤ) ^ (y / 2 * (a / 2)) := by
      intro y hy
      have hy_odd : Odd y := hs_odd y hy
      have hne : a ≠ y := fun h => ha (h ▸ hy)
      have hcop_ay : Nat.Coprime a y :=
        hcop a (Finset.mem_cons_self a s) y (Finset.mem_cons_of_mem hy) hne
      have hgcd : (a : ℤ).gcd y = 1 := by
        change Nat.gcd (a : ℤ).natAbs (y : ℤ).natAbs = 1
        simpa using hcop_ay.gcd_eq_one
      rw [jacobiSym.quadratic_reciprocity hy_odd ha_odd, mul_assoc, ← sq,
        jacobiSym.sq_one hgcd, mul_one]
    rw [Finset.prod_congr rfl hpair]
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
    by_cases ha3 : a % 4 = 3
    · have hterm : ∀ y ∈ s,
          (-1 : ℤ) ^ (y / 2 * (a / 2)) = if y % 4 = 3 then (-1 : ℤ) else 1 := by
        intro y hy
        have hy2 : y % 2 = 1 := Nat.odd_iff.mp (hs_odd y hy)
        by_cases hy3 : y % 4 = 3
        · rw [if_pos hy3]
          have hy_div : (y / 2) % 2 = 1 := by omega
          have ha_div : (a / 2) % 2 = 1 := by omega
          have hodd_prod : Odd (y / 2 * (a / 2)) := by
            rw [Nat.odd_iff, Nat.mul_mod, hy_div, ha_div]
          exact hodd_prod.neg_one_pow
        · rw [if_neg hy3]
          have hy_div : (y / 2) % 2 = 0 := by omega
          have heven_prod : Even (y / 2 * (a / 2)) := by
            rw [Nat.even_iff, Nat.mul_mod, hy_div, zero_mul, Nat.zero_mod]
          exact heven_prod.neg_one_pow
      rw [Finset.prod_congr rfl hterm, Finset.prod_ite, Finset.prod_const,
        Finset.prod_const_one, mul_one, ← pow_add]
      have hfilt : ((Finset.cons a s ha).filter (fun p => p % 4 = 3)).card =
          (s.filter (fun p => p % 4 = 3)).card + 1 := by
        rw [Finset.filter_cons, if_pos ha3, Finset.card_cons]
      rw [hfilt, Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    · have hterm : ∀ y ∈ s, (-1 : ℤ) ^ (y / 2 * (a / 2)) = 1 := by
        intro y _
        have ha_div : (a / 2) % 2 = 0 := by omega
        have heven_prod : Even (y / 2 * (a / 2)) := by
          rw [Nat.even_iff, Nat.mul_mod, ha_div, mul_zero, Nat.zero_mod]
        exact heven_prod.neg_one_pow
      rw [Finset.prod_congr rfl hterm, Finset.prod_const_one, one_mul]
      have hfilt : ((Finset.cons a s ha).filter (fun p => p % 4 = 3)).card =
          (s.filter (fun p => p % 4 = 3)).card := by
        rw [Finset.filter_cons, if_neg ha3]
      rw [hfilt]

lemma qr_r3_mod_four {n : ℕ} (hsqf : Squarefree n) (hodd : Odd n)
    (hdvd : ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) :
    (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 ∨
      (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 1 := by
  have hn0 : n ≠ 0 := hsqf.ne_zero
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hodd_pf : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have : (n / p * p) % 2 = 1 := hmul.symm ▸ hn2
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod] at this
      omega
    · exact Nat.odd_iff.mpr h1
  have hcop_pf : ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, p ≠ q → Nat.Coprime p q := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq)).mpr hpq
  have hprod_eq := prod_jacobiSym_offDiag n.primeFactors hodd_pf hcop_pf
  have hprod_n : ∏ p ∈ n.primeFactors, p = n := prod_primeFactors_of_sqf hsqf hn0
  have hlhs : ∏ p ∈ n.primeFactors, ∏ q ∈ n.primeFactors.erase p, jacobiSym (q : ℤ) p = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    rw [← jacobiSym_prod_left]
    have herase_prod : ∏ q ∈ n.primeFactors.erase p, q = n / p := by
      have hpmul : p * ∏ q ∈ n.primeFactors.erase p, q = n := by
        rw [Finset.mul_prod_erase n.primeFactors (fun q => q) hp]
        exact hprod_n
      have hp0 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
      exact Nat.eq_div_of_mul_eq_right hp0.ne' hpmul
    rw [herase_prod]
    have hp_dvd_sub : p ∣ (n / p - 1) := dvd_trans (dvd_mul_right p (p - 1)) (hdvd p hp)
    have hdiv_pos : 1 ≤ n / p := by
      have hp_le : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp)
      exact Nat.div_pos hp_le (Nat.prime_of_mem_primeFactors hp).pos
    have hmod_nat : (n / p) % p = 1 % p := by
      obtain ⟨c, hc⟩ := hp_dvd_sub
      have hnp : n / p = p * c + 1 := by omega
      rw [hnp, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    have hmod_int : ((n / p : ℕ) : ℤ) % (p : ℕ) = (1 : ℤ) % (p : ℕ) := by
      exact_mod_cast hmod_nat
    rw [jacobiSym.mod_left' hmod_int, jacobiSym.one_left]
  rw [hlhs] at hprod_eq
  set r3 := (n.primeFactors.filter (fun p => p % 4 = 3)).card
  have heven_choose : Even (r3.choose 2) := by
    by_contra hnot
    have hodd_c : Odd (r3.choose 2) := Nat.not_even_iff_odd.mp hnot
    rw [hodd_c.neg_one_pow] at hprod_eq
    omega
  rw [Nat.choose_two_right, Nat.even_iff] at heven_choose
  have hcase : r3 % 4 = 0 ∨ r3 % 4 = 1 ∨ r3 % 4 = 2 ∨ r3 % 4 = 3 := by omega
  rcases hcase with h0 | h1 | h2 | h3
  · exact Or.inl h0
  · exact Or.inr h1
  · exfalso
    set q := r3 / 4
    have hq : r3 = 4 * q + 2 := by omega
    have hq1 : r3 - 1 = 4 * q + 1 := by omega
    have hmul : r3 * (r3 - 1) = 2 * ((2 * q + 1) * (4 * q + 1)) := by
      rw [hq1, hq]
      ring
    have hdiv : r3 * (r3 - 1) / 2 = (2 * q + 1) * (4 * q + 1) := by
      rw [hmul, Nat.mul_div_cancel_left _ (by omega)]
    have h1' : (2 * q + 1) % 2 = 1 := by omega
    have h2' : (4 * q + 1) % 2 = 1 := by omega
    rw [hdiv, Nat.mul_mod, h1', h2'] at heven_choose
    omega
  · exfalso
    set q := r3 / 4
    have hq : r3 = 4 * q + 3 := by omega
    have hq1 : r3 - 1 = 4 * q + 2 := by omega
    have hmul : r3 * (r3 - 1) = 2 * ((4 * q + 3) * (2 * q + 1)) := by
      rw [hq1, hq]
      ring
    have hdiv : r3 * (r3 - 1) / 2 = (4 * q + 3) * (2 * q + 1) := by
      rw [hmul, Nat.mul_div_cancel_left _ (by omega)]
    have h1' : (4 * q + 3) % 2 = 1 := by omega
    have h2' : (2 * q + 1) % 2 = 1 := by omega
    rw [hdiv, Nat.mul_mod, h1', h2'] at heven_choose
    omega

/- ### Section 3: Mod-4 product and sum helpers -/

lemma prod_mod_four_of_odd (s : Finset ℕ) (hodd : ∀ p ∈ s, Odd p) :
    (∏ p ∈ s, p) % 4 = if (s.filter (fun p => p % 4 = 3)).card % 2 = 0 then 1 else 3 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha_odd := hodd a (Finset.mem_cons_self a s)
    have hs_odd : ∀ p ∈ s, Odd p := fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    have hih := ih hs_odd
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
    rw [Finset.prod_cons, Nat.mul_mod, hih, Finset.filter_cons]
    by_cases ha3 : a % 4 = 3
    · rw [if_pos ha3, Finset.card_cons, ha3]
      split_ifs <;> omega
    · rw [if_neg ha3]
      have ha1 : a % 4 = 1 := by omega
      rw [ha1]
      split_ifs <;> omega

lemma sum_mod_four_split (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ p ∈ s, (p % 4 = 1 → f p % 4 = 1) ∧ (p % 4 = 3 → f p % 4 = 3))
    (hodd : ∀ p ∈ s, Odd p) :
    (∑ p ∈ s, f p) % 4 =
      ((s.filter (fun p => p % 4 = 1)).card + 3 * (s.filter (fun p => p % 4 = 3)).card) % 4 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha_odd := hodd a (Finset.mem_cons_self a s)
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp ha_odd
    have hs_odd : ∀ p ∈ s, Odd p := fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    have hih := ih (fun p hp => hf p (Finset.mem_cons_of_mem hp)) hs_odd
    have hfa := hf a (Finset.mem_cons_self a s)
    rw [Finset.sum_cons, Finset.filter_cons, Finset.filter_cons]
    by_cases ha1 : a % 4 = 1
    · have ha3 : ¬ (a % 4 = 3) := by omega
      rw [if_pos ha1, if_neg ha3, Finset.card_cons]
      have := hfa.1 ha1
      omega
    · have ha3 : a % 4 = 3 := by omega
      rw [if_neg ha1, if_pos ha3, Finset.card_cons]
      have := hfa.2 ha3
      omega

lemma sum_mod_four_of_one (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ p ∈ s, f p % 4 = 1) :
    (∑ p ∈ s, f p) % 4 = s.card % 4 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.card_cons]
    have ha1 := hf a (Finset.mem_cons_self a s)
    have hih := ih fun p hp => hf p (Finset.mem_cons_of_mem hp)
    omega

lemma sum_mod_four_of_three (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ p ∈ s, f p % 4 = 3) :
    (∑ p ∈ s, f p) % 4 = (3 * s.card) % 4 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.card_cons]
    have ha3 := hf a (Finset.mem_cons_self a s)
    have hih := ih fun p hp => hf p (Finset.mem_cons_of_mem hp)
    omega

lemma card_eq_r1_add_r3 (s : Finset ℕ) (hodd : ∀ p ∈ s, Odd p) :
    s.card = (s.filter (fun p => p % 4 = 1)).card + (s.filter (fun p => p % 4 = 3)).card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have ha2 : a % 2 = 1 := Nat.odd_iff.mp (hodd a (Finset.mem_cons_self a s))
    have hih := ih fun p hp => hodd p (Finset.mem_cons_of_mem hp)
    rw [Finset.card_cons, Finset.filter_cons, Finset.filter_cons]
    by_cases ha1 : a % 4 = 1
    · have ha3 : ¬ (a % 4 = 3) := by omega
      rw [if_pos ha1, if_neg ha3, Finset.card_cons]
      omega
    · have ha3 : a % 4 = 3 := by omega
      rw [if_neg ha1, if_pos ha3, Finset.card_cons]
      omega

/- ### Section 4: Logarithmic-harmonic lower bounds on arithmetic progressions -/

lemma exp_nat_eq_pow (m : ℕ) : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, Real.exp_add, ih, pow_succ]

lemma inv_le_log_diff {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    1 / (a + d) ≤ (1 / d) * (Real.log (a + d) - Real.log a) := by
  have had : 0 < a + d := by linarith
  have hdiv_pos : 0 < a / (a + d) := div_pos ha had
  have hlog := Real.log_le_sub_one_of_pos hdiv_pos
  rw [Real.log_div ha.ne' had.ne'] at hlog
  have hsub : a / (a + d) - 1 = -d / (a + d) := by
    field_simp [had.ne']
    ring
  rw [hsub, neg_div] at hlog
  have hmul : d / (a + d) ≤ Real.log (a + d) - Real.log a := by linarith
  have hstep := mul_le_mul_of_nonneg_left hmul (le_of_lt (one_div_pos.mpr hd))
  have hlhs : 1 / d * (d / (a + d)) = 1 / (a + d) := by
    field_simp [hd.ne', had.ne']
  rwa [hlhs] at hstep

lemma sum_inv_ap_le_log (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) :
    ∑ i ∈ Finset.range (m + 1), (1 / ((a + d * i : ℕ) : ℝ)) ≤
      1 / (a : ℝ) + (1 / (d : ℝ)) * (Real.log ((a + d * m : ℕ) : ℝ) - Real.log (a : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have ham : (0 : ℝ) < ((a + d * m : ℕ) : ℝ) := by positivity
    have hdR : (0 : ℝ) < (d : ℝ) := by positivity
    have hstep := inv_le_log_diff ham hdR
    have hcast : ((a + d * m : ℕ) : ℝ) + (d : ℝ) = ((a + d * (m + 1) : ℕ) : ℝ) := by
      push_cast
      ring
    rw [hcast] at hstep
    linarith

lemma sum_inv_finset_ap_le (s : Finset ℕ) (a d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (hs : ∀ x ∈ s, a ≤ x ∧ x % d = a % d) (hne : 0 < s.card) :
    ∑ x ∈ s, (1 / (x : ℝ)) ≤
      1 / (a : ℝ) + (1 / (d : ℝ)) * (Real.log ((a + d * (s.card - 1) : ℕ) : ℝ) - Real.log (a : ℝ)) := by
  let e : Fin s.card ↪o ℕ := s.orderEmbOfFin rfl
  have himg : Finset.univ.image e = s := by
    refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
    · rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
      exact Finset.orderEmbOfFin_mem s rfl i
    · rw [Finset.card_image_of_injective _ e.injective, Finset.card_fin]
  have hsum_e : ∑ x ∈ s, (1 / (x : ℝ)) = ∑ i : Fin s.card, (1 / (e i : ℝ)) := by
    conv_lhs => rw [← himg]
    rw [Finset.sum_image (fun i _ j _ h => e.injective h)]
  have hbound : ∀ i : ℕ, (hi : i < s.card) → a + d * i ≤ e ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      simpa using (hs (e ⟨0, hi⟩) (Finset.orderEmbOfFin_mem s rfl ⟨0, hi⟩)).1
    | succ i ih =>
      intro hi
      have hi' : i < s.card := by omega
      have hprev := ih hi'
      have hlt : e ⟨i, hi'⟩ < e ⟨i + 1, hi⟩ := e.strictMono (by exact Nat.lt_succ_self i)
      have hmod1 := (hs (e ⟨i, hi'⟩) (Finset.orderEmbOfFin_mem s rfl ⟨i, hi'⟩)).2
      have hmod2 := (hs (e ⟨i + 1, hi⟩) (Finset.orderEmbOfFin_mem s rfl ⟨i + 1, hi⟩)).2
      have hmod_eq : e ⟨i, hi'⟩ % d = e ⟨i + 1, hi⟩ % d := hmod1.trans hmod2.symm
      have hdiv1 := (Nat.div_add_mod (e ⟨i, hi'⟩) d).symm
      have hdiv2 := (Nat.div_add_mod (e ⟨i + 1, hi⟩) d).symm
      have hq_lt : e ⟨i, hi'⟩ / d < e ⟨i + 1, hi⟩ / d := by
        by_contra hle
        have hq_le : e ⟨i + 1, hi⟩ / d ≤ e ⟨i, hi'⟩ / d := Nat.le_of_not_lt hle
        have hmul_le : d * (e ⟨i + 1, hi⟩ / d) ≤ d * (e ⟨i, hi'⟩ / d) :=
          Nat.mul_le_mul_left d hq_le
        omega
      have hmul_step : d * (e ⟨i, hi'⟩ / d) + d ≤ d * (e ⟨i + 1, hi⟩ / d) := by
        have h1 : e ⟨i, hi'⟩ / d + 1 ≤ e ⟨i + 1, hi⟩ / d := hq_lt
        have h2 := Nat.mul_le_mul_left d h1
        linarith
      have hdiff : e ⟨i, hi'⟩ + d ≤ e ⟨i + 1, hi⟩ := by omega
      have hmul_succ : a + d * (i + 1) = a + d * i + d := by ring
      omega
  have hle_sum : ∑ i : Fin s.card, (1 / (e i : ℝ)) ≤
      ∑ i ∈ Finset.range s.card, (1 / ((a + d * i : ℕ) : ℝ)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (1 / ((a + d * i : ℕ) : ℝ))) s.card]
    refine Finset.sum_le_sum fun i _ => ?_
    have hpos : (0 : ℝ) < ((a + d * i.val : ℕ) : ℝ) := by positivity
    have hleR : ((a + d * i.val : ℕ) : ℝ) ≤ (e i : ℝ) := by
      exact_mod_cast hbound i.val i.isLt
    exact one_div_le_one_div_of_le hpos hleR
  have hcard : s.card = (s.card - 1) + 1 := by omega
  calc ∑ x ∈ s, (1 / (x : ℝ))
      = ∑ i : Fin s.card, (1 / (e i : ℝ)) := hsum_e
    _ ≤ ∑ i ∈ Finset.range s.card, (1 / ((a + d * i : ℕ) : ℝ)) := hle_sum
    _ = ∑ i ∈ Finset.range ((s.card - 1) + 1), (1 / ((a + d * i : ℕ) : ℝ)) := by rw [← hcard]
    _ ≤ 1 / (a : ℝ) + (1 / (d : ℝ)) *
          (Real.log ((a + d * (s.card - 1) : ℕ) : ℝ) - Real.log (a : ℝ)) :=
        sum_inv_ap_le_log a d (s.card - 1) ha hd

lemma sum_real_gt_k {n k : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    (k : ℝ) < ∑ p ∈ n.primeFactors, (1 / (p : ℝ)) := by
  have hq : (k : ℚ) < ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) := by
    have hn_pos : (0 : ℚ) < 1 / (n : ℚ) := one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))
    linarith
  have hr : ((k : ℚ) : ℝ) < ((∑ p ∈ n.primeFactors, (1 / (p : ℚ)) : ℚ) : ℝ) := by
    exact_mod_cast hq
  simpa [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hr

lemma card_ge_90_of_ge_five {n k : ℕ} (hn0 : n ≠ 0) (hk2 : 2 ≤ k)
    (hcard65 : 65 ≤ n.primeFactors.card)
    (hodd_pf : ∀ p ∈ n.primeFactors, Odd p)
    (hge5 : ∀ p ∈ n.primeFactors, 5 ≤ p)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    90 ≤ n.primeFactors.card := by
  by_contra hlt
  have hle : n.primeFactors.card - 1 ≤ 88 := by omega
  have hspos : 0 < n.primeFactors.card := by omega
  have hs_ap : ∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 2 = 5 % 2 := fun p hp =>
    ⟨hge5 p hp, Nat.odd_iff.mp (hodd_pf p hp)⟩
  have hsum_real := sum_real_gt_k hn0 hsum
  have hub := sum_inv_finset_ap_le n.primeFactors 5 2 (by omega) (by omega) hs_ap hspos
  have hlog_mono : Real.log ((5 + 2 * (n.primeFactors.card - 1) : ℕ) : ℝ) - Real.log (5 : ℝ) ≤
      Real.log ((5 + 2 * 88 : ℕ) : ℝ) - Real.log (5 : ℝ) := by
    have hle1 : ((5 + 2 * (n.primeFactors.card - 1) : ℕ) : ℝ) ≤ ((5 + 2 * 88 : ℕ) : ℝ) := by
      exact_mod_cast (show 5 + 2 * (n.primeFactors.card - 1) ≤ 5 + 2 * 88 by omega)
    have hpos1 : (0 : ℝ) < ((5 + 2 * (n.primeFactors.card - 1) : ℕ) : ℝ) := by positivity
    linarith [Real.log_le_log hpos1 hle1]
  have hlog_lt : Real.log ((5 + 2 * 88 : ℕ) : ℝ) - Real.log (5 : ℝ) < 18 / 5 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have hpos : (0 : ℝ) < ((5 + 2 * 88 : ℕ) : ℝ) / 5 := by positivity
    suffices h5 : 5 * Real.log (((5 + 2 * 88 : ℕ) : ℝ) / 5) < 18 by linarith
    have hpow_log : Real.log ((((5 + 2 * 88 : ℕ) : ℝ) / 5) ^ 5) =
        5 * Real.log (((5 + 2 * 88 : ℕ) : ℝ) / 5) := by
      simp [Real.log_pow]
    rw [← hpow_log, Real.log_lt_iff_lt_exp (pow_pos hpos 5)]
    have hexp18 : (2718 / 1000 : ℝ) ^ 18 < Real.exp (18 : ℝ) := by
      have hbase : (2718 / 1000 : ℝ) < Real.exp 1 := by
        linarith [Real.exp_one_gt_d9]
      calc (2718 / 1000 : ℝ) ^ 18 < (Real.exp 1) ^ 18 := by gcongr
        _ = Real.exp ((18 : ℕ) : ℝ) := (exp_nat_eq_pow 18).symm
        _ = Real.exp (18 : ℝ) := by norm_num
    have hnum : ((((5 + 2 * 88 : ℕ) : ℝ) / 5) ^ 5) ≤ (2718 / 1000 : ℝ) ^ 18 := by
      norm_num
    linarith
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have h2pos : (0 : ℝ) < 1 / (2 : ℝ) := by positivity
  have hmul_lt := mul_lt_mul_of_pos_left (lt_of_le_of_lt hlog_mono hlog_lt) h2pos
  linarith

lemma card_ge_100000_of_mod_four {n k : ℕ} (hn0 : n ≠ 0) (hk3 : 3 ≤ k)
    (hcard65 : 65 ≤ n.primeFactors.card)
    (hall3 : ∀ p ∈ n.primeFactors, 7 ≤ p ∧ p % 4 = 3)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    100000 ≤ n.primeFactors.card := by
  by_contra hlt
  have hle : n.primeFactors.card - 1 ≤ 99998 := by omega
  have hspos : 0 < n.primeFactors.card := by omega
  have hs_ap : ∀ p ∈ n.primeFactors, 7 ≤ p ∧ p % 4 = 7 % 4 := hall3
  have hsum_real := sum_real_gt_k hn0 hsum
  have hub := sum_inv_finset_ap_le n.primeFactors 7 4 (by omega) (by omega) hs_ap hspos
  have hlog_mono : Real.log ((7 + 4 * (n.primeFactors.card - 1) : ℕ) : ℝ) - Real.log (7 : ℝ) ≤
      Real.log ((7 + 4 * 99998 : ℕ) : ℝ) - Real.log (7 : ℝ) := by
    have hle1 : ((7 + 4 * (n.primeFactors.card - 1) : ℕ) : ℝ) ≤ ((7 + 4 * 99998 : ℕ) : ℝ) := by
      exact_mod_cast (show 7 + 4 * (n.primeFactors.card - 1) ≤ 7 + 4 * 99998 by omega)
    have hpos1 : (0 : ℝ) < ((7 + 4 * (n.primeFactors.card - 1) : ℕ) : ℝ) := by positivity
    linarith [Real.log_le_log hpos1 hle1]
  have hlog_lt : Real.log ((7 + 4 * 99998 : ℕ) : ℝ) - Real.log (7 : ℝ) < 11 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have hpos : (0 : ℝ) < ((7 + 4 * 99998 : ℕ) : ℝ) / 7 := by positivity
    rw [Real.log_lt_iff_lt_exp hpos]
    have hexp11 : (2718 / 1000 : ℝ) ^ 11 < Real.exp (11 : ℝ) := by
      have hbase : (2718 / 1000 : ℝ) < Real.exp 1 := by
        linarith [Real.exp_one_gt_d9]
      calc (2718 / 1000 : ℝ) ^ 11 < (Real.exp 1) ^ 11 := by gcongr
        _ = Real.exp ((11 : ℕ) : ℝ) := (exp_nat_eq_pow 11).symm
        _ = Real.exp (11 : ℝ) := by norm_num
    have hnum : ((7 + 4 * 99998 : ℕ) : ℝ) / 7 ≤ (2718 / 1000 : ℝ) ^ 11 := by
      norm_num
    linarith
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have h4pos : (0 : ℝ) < 1 / (4 : ℝ) := by positivity
  have hmul_lt := mul_lt_mul_of_pos_left (lt_of_le_of_lt hlog_mono hlog_lt) h4pos
  linarith

lemma card_ge_5000000_of_mod_four {n k : ℕ} (hn0 : n ≠ 0) (hk4 : 4 ≤ k)
    (hcard65 : 65 ≤ n.primeFactors.card)
    (hall3 : ∀ p ∈ n.primeFactors, 7 ≤ p ∧ p % 4 = 3)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    5000000 ≤ n.primeFactors.card := by
  by_contra hlt
  have hle : n.primeFactors.card - 1 ≤ 4999998 := by omega
  have hspos : 0 < n.primeFactors.card := by omega
  have hs_ap : ∀ p ∈ n.primeFactors, 7 ≤ p ∧ p % 4 = 7 % 4 := hall3
  have hsum_real := sum_real_gt_k hn0 hsum
  have hub := sum_inv_finset_ap_le n.primeFactors 7 4 (by omega) (by omega) hs_ap hspos
  have hlog_mono : Real.log ((7 + 4 * (n.primeFactors.card - 1) : ℕ) : ℝ) - Real.log (7 : ℝ) ≤
      Real.log ((7 + 4 * 4999998 : ℕ) : ℝ) - Real.log (7 : ℝ) := by
    have hle1 : ((7 + 4 * (n.primeFactors.card - 1) : ℕ) : ℝ) ≤ ((7 + 4 * 4999998 : ℕ) : ℝ) := by
      exact_mod_cast (show 7 + 4 * (n.primeFactors.card - 1) ≤ 7 + 4 * 4999998 by omega)
    have hpos1 : (0 : ℝ) < ((7 + 4 * (n.primeFactors.card - 1) : ℕ) : ℝ) := by positivity
    linarith [Real.log_le_log hpos1 hle1]
  have hlog_lt : Real.log ((7 + 4 * 4999998 : ℕ) : ℝ) - Real.log (7 : ℝ) < 15 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have hpos : (0 : ℝ) < ((7 + 4 * 4999998 : ℕ) : ℝ) / 7 := by positivity
    rw [Real.log_lt_iff_lt_exp hpos]
    have hexp15 : (2718 / 1000 : ℝ) ^ 15 < Real.exp (15 : ℝ) := by
      have hbase : (2718 / 1000 : ℝ) < Real.exp 1 := by
        linarith [Real.exp_one_gt_d9]
      calc (2718 / 1000 : ℝ) ^ 15 < (Real.exp 1) ^ 15 := by gcongr
        _ = Real.exp ((15 : ℕ) : ℝ) := (exp_nat_eq_pow 15).symm
        _ = Real.exp (15 : ℝ) := by norm_num
    have hnum : ((7 + 4 * 4999998 : ℕ) : ℝ) / 7 ≤ (2718 / 1000 : ℝ) ^ 15 := by
      norm_num
    linarith
  have hkR : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk4
  have h4pos : (0 : ℝ) < 1 / (4 : ℝ) := by positivity
  have hmul_lt := mul_lt_mul_of_pos_left (lt_of_le_of_lt hlog_mono hlog_lt) h4pos
  linarith

/- ### Section 5: Main reduction theorem -/

theorem main : H1 → H2 → H3 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2.H3 := by
  intro h1 h2 h3 n hcomp hsqf hodd h3ndvd hcard65 hge5 hdvd hnorm ⟨k, hk2, hsum⟩
  have hn0 : n ≠ 0 := hsqf.ne_zero
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have hodd_pf : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have : (n / p * p) % 2 = 1 := hmul.symm ▸ hn2
    rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
    · rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod] at this
      omega
    · exact Nat.odd_iff.mpr h1
  have hint : ∑ p ∈ n.primeFactors, n / p = k * n + 1 := sum_div_eq_mul_add_one hn0 hsum
  have hqr := qr_r3_mod_four hsqf hodd hdvd
  have hprod_n : ∏ p ∈ n.primeFactors, p = n := prod_primeFactors_of_sqf hsqf hn0
  have hn_mod4 : n % 4 =
      if (n.primeFactors.filter (fun p => p % 4 = 3)).card % 2 = 0 then 1 else 3 := by
    conv_lhs => rw [← hprod_n]
    exact prod_mod_four_of_odd n.primeFactors hodd_pf
  by_cases hex1 : ∃ p ∈ n.primeFactors, p % 4 = 1
  · obtain ⟨p0, hp0, hp0_mod4⟩ := hex1
    have hp0_pred : 4 ∣ (p0 - 1) := by omega
    have hdiv_sub : 4 ∣ (n / p0 - 1) :=
      dvd_trans hp0_pred (dvd_trans (dvd_mul_left (p0 - 1) p0) (hdvd p0 hp0))
    have hdiv_pos : 1 ≤ n / p0 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp0))
        (Nat.prime_of_mem_primeFactors hp0).pos
    have hdiv_mod4 : (n / p0) % 4 = 1 := by
      obtain ⟨c, hc⟩ := hdiv_sub
      omega
    have hn4 : n % 4 = 1 := by
      have hmul : n / p0 * p0 = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp0)
      rw [← hmul, Nat.mul_mod, hdiv_mod4, hp0_mod4]
    have hr3_even : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 2 = 0 := by
      by_contra hne
      rw [if_neg hne] at hn_mod4
      omega
    have hr3_dvd4 : 4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card := by
      rcases hqr with h0 | h1
      · exact Nat.dvd_of_mod_eq_zero h0
      · omega
    have hsum4_terms : ∀ p ∈ n.primeFactors,
        (p % 4 = 1 → (n / p) % 4 = 1) ∧ (p % 4 = 3 → (n / p) % 4 = 3) := by
      intro p hp
      have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
      have hprod4 : (n / p * p) % 4 = 1 := hmul.symm ▸ hn4
      rw [Nat.mul_mod] at hprod4
      constructor
      · intro hp1; rw [hp1] at hprod4; omega
      · intro hp3; rw [hp3] at hprod4; omega
    have hsum4 := sum_mod_four_split n.primeFactors (fun p => n / p) hsum4_terms hodd_pf
    rw [hint] at hsum4
    have hcard_split := card_eq_r1_add_r3 n.primeFactors hodd_pf
    have hrhs4 : (k * n + 1) % 4 = (k + 1) % 4 := by
      rw [Nat.add_mod, Nat.mul_mod, hn4]
      omega
    have hr3_0 : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 :=
      Nat.mod_eq_zero_of_dvd hr3_dvd4
    have hr1_mod4 : (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = (k + 1) % 4 := by
      rw [hrhs4] at hsum4
      omega
    have hcard_mod4 : n.primeFactors.card % 4 = (k + 1) % 4 := by
      omega
    have hcard90 := card_ge_90_of_ge_five hn0 hk2 hcard65 hodd_pf hge5 hsum
    exact h1 n hcomp hsqf hodd h3ndvd hn4 hcard90 ⟨p0, hp0, hp0_mod4⟩ hr3_dvd4
      hge5 hdvd hnorm ⟨k, hk2, hcard_mod4, hr1_mod4, hsum⟩
  · have hall3 : ∀ p ∈ n.primeFactors, 7 ≤ p ∧ p % 4 = 3 := by
      intro p hp
      have hp5 : 5 ≤ p := hge5 p hp
      have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hodd_pf p hp)
      have hp1 : p % 4 ≠ 1 := fun h => hex1 ⟨p, hp, h⟩
      exact ⟨by omega, by omega⟩
    have hfilt_eq : n.primeFactors.filter (fun p => p % 4 = 3) = n.primeFactors :=
      Finset.filter_true_of_mem (fun p hp => (hall3 p hp).2)
    rw [hfilt_eq] at hqr hn_mod4
    rcases hqr with hcard0 | hcard1
    · have hcard_dvd4 : 4 ∣ n.primeFactors.card := Nat.dvd_of_mod_eq_zero hcard0
      have hcard_even : n.primeFactors.card % 2 = 0 := by omega
      have hn4 : n % 4 = 1 := by
        rw [if_pos hcard_even] at hn_mod4
        exact hn_mod4
      have hdiv3 : ∀ p ∈ n.primeFactors, (n / p) % 4 = 3 := by
        intro p hp
        have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
        have hprod4 : (n / p * p) % 4 = 1 := hmul.symm ▸ hn4
        rw [Nat.mul_mod, (hall3 p hp).2] at hprod4
        omega
      have hsum4 := sum_mod_four_of_three n.primeFactors (fun p => n / p) hdiv3
      rw [hint] at hsum4
      have hrhs4 : (k * n + 1) % 4 = (k + 1) % 4 := by
        rw [Nat.add_mod, Nat.mul_mod, hn4]
        omega
      rw [hrhs4] at hsum4
      have hk_mod4 : k % 4 = 3 := by omega
      have hk3 : 3 ≤ k := by omega
      have hcard100k := card_ge_100000_of_mod_four hn0 hk3 hcard65 hall3 hsum
      exact h2 n hcomp hsqf hodd h3ndvd hn4 hcard_dvd4 hcard100k hall3 hdvd hnorm
        ⟨k, hk3, hk_mod4, hsum⟩
    · have hcard_odd : ¬ (n.primeFactors.card % 2 = 0) := by omega
      have hn4 : n % 4 = 3 := by
        rw [if_neg hcard_odd] at hn_mod4
        exact hn_mod4
      have hdiv1 : ∀ p ∈ n.primeFactors, (n / p) % 4 = 1 := by
        intro p hp
        have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
        have hprod4 : (n / p * p) % 4 = 3 := hmul.symm ▸ hn4
        rw [Nat.mul_mod, (hall3 p hp).2] at hprod4
        omega
      have hsum4 := sum_mod_four_of_one n.primeFactors (fun p => n / p) hdiv1
      rw [hint, hcard1] at hsum4
      have hrhs4 : (k * n + 1) % 4 = (3 * k + 1) % 4 := by
        rw [Nat.add_mod, Nat.mul_mod, hn4]
        omega
      rw [hrhs4] at hsum4
      have hk_dvd4 : 4 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
      have hk4 : 4 ≤ k := by
        have : k % 4 = 0 := Nat.mod_eq_zero_of_dvd hk_dvd4
        omega
      have hcard5m := card_ge_5000000_of_mod_four hn0 hk4 hcard65 hall3 hsum
      exact h3 n hcomp hsqf hodd h3ndvd hn4 hcard1 hcard5m hall3 hdvd hnorm
        ⟨k, hk4, hk_dvd4, hsum⟩

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H3_R1
