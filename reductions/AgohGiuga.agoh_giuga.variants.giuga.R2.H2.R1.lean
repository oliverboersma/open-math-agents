import OMAReductions.R_AgohGiuga_agoh_giuga_variants_giuga_R2

/-!
# Reduction of Agoh-Giuga step R2.H2 (3-free primary unit-sum regime)

Reduction `AgohGiuga.agoh_giuga.variants.giuga.R2.H2.R1` by `@hackoria`.

We prove unconditionally from the hypotheses of `R2.H2` (`3 ∤ n`, `∑ 1/p - 1/n = 1`):
1. **Parity:** reducing `∑_{p ∣ n} n / p = n + 1` modulo 2 forces `Even ω(n)`.
2. **Gauss Quadratic Reciprocity obstruction:** evaluating `∏_{p ∣ n} J(n / p | p) = 1`
   via `jacobiSym.quadratic_reciprocity` forces `r3 % 4 = 0 ∨ r3 % 4 = 1`, where
   `r3 = #{p ∣ n : p ≡ 3 (mod 4)}`.
3. **Complete elimination of the all-`3 (mod 4)` case:** if all `p ∣ n` satisfy `p ≡ 3 (mod 4)`,
   then `Even ω(n)` + QR forces `4 ∣ ω(n)`, hence `n ≡ 1 (mod 4)` and `n / p ≡ 3 (mod 4)`,
   giving `∑ n / p ≡ 0 (mod 4)` while `n + 1 ≡ 2 (mod 4)`, contradiction.
4. **Sharp mod-4 structure:** every counterexample must satisfy `∃ p ∣ n, p ≡ 1 (mod 4)`,
   `n % 4 = 1`, `4 ∣ r3`, `r1 % 4 = 2`, `ω(n) % 4 = 2`, and `66 ≤ ω(n)`.
5. **5-divisibility dichotomy:** splits into `H1` (`5 ∣ n`, forbidding `p ≡ 1 (mod 5)`) and
   `H2` (`5 ∤ n`, forcing `7 ≤ p` for all `p ∣ n`).
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1

open AgohGiuga
open scoped Nat

-- Sub-regime 2A: 3-free, 5-divisible primary (k = 1) strong Giuga number.
def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) → 5 ∣ n →
    n % 4 = 1 →
    n.primeFactors.card % 4 = 2 → 66 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    False

-- Sub-regime 2B: 3-free, 5-free primary (k = 1) strong Giuga number (all p ≥ 7).
def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) → ¬ (5 ∣ n) →
    n % 4 = 1 →
    n.primeFactors.card % 4 = 2 → 66 ≤ n.primeFactors.card →
    (∃ p ∈ n.primeFactors, p % 4 = 1) →
    4 ∣ (n.primeFactors.filter (fun p => p % 4 = 3)).card →
    (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 →
    (∀ p ∈ n.primeFactors, 7 ≤ p) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
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

lemma sum_div_eq_add_one {n : ℕ} (hn0 : n ≠ 0)
    (hsum : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) :
    ∑ p ∈ n.primeFactors, n / p = n + 1 := by
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hmul : (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ)) * (n : ℚ) = 1 * (n : ℚ) :=
    congrArg (· * (n : ℚ)) hsum
  rw [sub_mul, Finset.sum_mul, one_div_mul_cancel hnQ, one_mul] at hmul
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
  have hcast : ((∑ p ∈ n.primeFactors, n / p : ℕ) : ℚ) = ((n + 1 : ℕ) : ℚ) := by
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  exact Nat.cast_injective hcast

lemma sum_mod_two_of_odd (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ s, f x % 2 = 1) :
    (∑ x ∈ s, f x) % 2 = s.card % 2 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.card_cons]
    have ha1 := hf a (Finset.mem_cons_self a s)
    have ih1 := ih fun x hx => hf x (Finset.mem_cons_of_mem hx)
    omega

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

/- ### Section 4: Main reduction theorem -/

theorem main : H1 → H2 → OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2.H2 := by
  intro h1 h2 n hcomp hsqf hodd h3 hcard65 hge5 hdvd hnorm hsum
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
  have hint : ∑ p ∈ n.primeFactors, n / p = n + 1 := sum_div_eq_add_one hn0 hsum
  have hdiv2 : ∀ p ∈ n.primeFactors, (n / p) % 2 = 1 := by
    intro p hp
    have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
    have : (n / p * p) % 2 = 1 := hmul.symm ▸ hn2
    rcases Nat.mod_two_eq_zero_or_one (n / p) with h0 | h1
    · rw [Nat.mul_mod, h0, zero_mul, Nat.zero_mod] at this
      omega
    · exact h1
  have hcard_even : n.primeFactors.card % 2 = 0 := by
    have hsum2 := sum_mod_two_of_odd n.primeFactors (fun p => n / p) hdiv2
    rw [hint] at hsum2
    omega
  have hqr := qr_r3_mod_four hsqf hodd hdvd
  have hprod_n : ∏ p ∈ n.primeFactors, p = n := prod_primeFactors_of_sqf hsqf hn0
  have hn_mod4 : n % 4 =
      if (n.primeFactors.filter (fun p => p % 4 = 3)).card % 2 = 0 then 1 else 3 := by
    conv_lhs => rw [← hprod_n]
    exact prod_mod_four_of_odd n.primeFactors hodd_pf
  -- Eliminate the all-3 (mod 4) case completely via Gauss Quadratic Reciprocity + mod 4 sum.
  have hex1 : ∃ p ∈ n.primeFactors, p % 4 = 1 := by
    by_contra hno1
    have hall3 : ∀ p ∈ n.primeFactors, p % 4 = 3 := by
      intro p hp
      have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hodd_pf p hp)
      have hp1 : p % 4 ≠ 1 := fun h => hno1 ⟨p, hp, h⟩
      omega
    have hfilt_eq : n.primeFactors.filter (fun p => p % 4 = 3) = n.primeFactors :=
      Finset.filter_true_of_mem hall3
    rw [hfilt_eq] at hqr hn_mod4
    have hcard_mod4 : n.primeFactors.card % 4 = 0 := by
      rcases hqr with h0 | h1
      · exact h0
      · omega
    have hn4 : n % 4 = 1 := by
      rw [if_pos hcard_even] at hn_mod4
      exact hn_mod4
    have hdiv3 : ∀ p ∈ n.primeFactors, (n / p) % 4 = 3 := by
      intro p hp
      have hmul : n / p * p = n := Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
      have hprod4 : (n / p * p) % 4 = 1 := hmul.symm ▸ hn4
      rw [Nat.mul_mod, hall3 p hp] at hprod4
      omega
    have hsum4 := sum_mod_four_of_three n.primeFactors (fun p => n / p) hdiv3
    rw [hint] at hsum4
    omega
  obtain ⟨p0, hp0, hp0_mod4⟩ := hex1
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
  have hr3_0 : (n.primeFactors.filter (fun p => p % 4 = 3)).card % 4 = 0 :=
    Nat.mod_eq_zero_of_dvd hr3_dvd4
  have hr1_mod4 : (n.primeFactors.filter (fun p => p % 4 = 1)).card % 4 = 2 := by
    omega
  have hcard_mod4 : n.primeFactors.card % 4 = 2 := by
    omega
  have hcard66 : 66 ≤ n.primeFactors.card := by omega
  by_cases h5 : 5 ∣ n
  · have h5mem : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, h5, hn0⟩
    have hmod5 : ∀ p ∈ n.primeFactors, 5 ≤ p ∧ p % 5 ≠ 1 := by
      intro p hp
      refine ⟨hge5 p hp, ?_⟩
      intro hp1
      have h5dvd : 5 ∣ (p - 1) := by omega
      exact hnorm 5 h5mem p hp h5dvd
    exact h1 n hcomp hsqf hodd h3 h5 hn4 hcard_mod4 hcard66 ⟨p0, hp0, hp0_mod4⟩
      hr3_dvd4 hr1_mod4 hmod5 hdvd hnorm hsum
  · have hge7 : ∀ p ∈ n.primeFactors, 7 ≤ p := by
      intro p hp
      have hp5 : 5 ≤ p := hge5 p hp
      have hp_ne5 : p ≠ 5 := fun h => h5 (h ▸ Nat.dvd_of_mem_primeFactors hp)
      have hp2 : p % 2 = 1 := Nat.odd_iff.mp (hodd_pf p hp)
      omega
    exact h2 n hcomp hsqf hodd h3 h5 hn4 hcard_mod4 hcard66 ⟨p0, hp0, hp0_mod4⟩
      hr3_dvd4 hr1_mod4 hge7 hdvd hnorm hsum

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2_H2_R1
