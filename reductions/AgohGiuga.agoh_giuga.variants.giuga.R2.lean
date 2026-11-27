import FormalConjectures.Wikipedia.AgohGiuga

/-!
# Reduction of the Agoh-Giuga conjecture (Giuga's formulation)

Reduction `AgohGiuga.agoh_giuga.variants.giuga.R2`.

We prove unconditionally (using no hypotheses):
1. `prime_dvd_sum_pow`: every prime satisfies Giuga's power-sum congruence.
2. `strongGiuga_korselt_and_giuga`: every strong Giuga number satisfies both Korselt's
   condition `(p - 1) ∣ (n - 1)` and Giuga's condition `p ∣ (n / p - 1)` for all prime
   factors `p ∣ n` (resolving both `R1.H1` and `R1.H2` unconditionally).
3. `strongGiuga_squarefree`, `strongGiuga_div_p_mul_pred`, and `strongGiuga_odd`:
   every strong Giuga number is odd, squarefree, and satisfies `p * (p - 1) ∣ (n / p - 1)`
   for every prime factor `p`.
4. `strongGiuga_normal_set` (Borwein-Borwein-Borwein-Girgensohn, 1996): no prime factor
   `p ∣ n` divides `q - 1` for any prime factor `q ∣ n`.
5. `strongGiuga_reciprocal_sum` (Giuga, 1950): there exists an integer `k ≥ 1` such that
   `∑_{p ∣ n} 1 / p - 1 / n = k`.
6. Sharp normal-set lower bounds on the number of prime factors:
   - If `3 ∣ n`, then every other prime factor satisfies `p ≡ 2 (mod 3)`, `ω(n)` is odd,
     and `37 ≤ ω(n)`.
   - If `3 ∤ n`, then every prime factor is at least `5`, and splitting on `5 ∣ n` via the
     normal-set condition forces `65 ≤ ω(n)`.

This splits the remaining open arithmetic core into three distinct regimes:
- `H1`: 3-divisible Giuga-Carmichael normal sets (`3 ∣ n`, `p ≡ 2 (mod 3)` for `p ≠ 3`,
  `Odd ω(n)`, `37 ≤ ω(n)`).
- `H2`: 3-free primary (unit-sum) Giuga-Carmichael normal sets (`3 ∤ n`, `65 ≤ ω(n)`,
  `∑_{p ∣ n} 1 / p - 1 / n = 1`).
- `H3`: 3-free multi-unit Giuga-Carmichael normal sets (`3 ∤ n`, `65 ≤ ω(n)`,
  `∑_{p ∣ n} 1 / p - 1 / n = k ≥ 2`).
-/

namespace OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2

open AgohGiuga
open scoped Nat

-- Regime 1: No 3-divisible Giuga-Carmichael normal set exists.
def H1 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → 3 ∣ n →
    Odd n.primeFactors.card → 37 ≤ n.primeFactors.card →
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 3 = 2) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 1 ≤ k ∧ ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

-- Regime 2: No 3-free primary (unit-sum) Giuga-Carmichael normal set exists.
def H2 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) →
    65 ≤ n.primeFactors.card →
    (∀ p ∈ n.primeFactors, 5 ≤ p) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = 1) →
    False

-- Regime 3: No 3-free multi-unit (k ≥ 2) Giuga-Carmichael normal set exists.
def H3 : Prop :=
  ∀ n : ℕ, n.Composite → Squarefree n → Odd n → ¬ (3 ∣ n) →
    65 ≤ n.primeFactors.card →
    (∀ p ∈ n.primeFactors, 5 ≤ p) →
    (∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1)) →
    (∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1))) →
    (∃ k : ℕ, 2 ≤ k ∧ ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) →
    False

/- ### Section 1: Prime direction and power sums modulo p -/

lemma prime_dvd_sum_pow (p : ℕ) (hp : p.Prime) :
    p ∣ 1 + ∑ i ∈ Finset.Ioo 0 p, i ^ (p - 1 : ℕ) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  have hsum : ∑ i ∈ Finset.Ioo 0 p, ((i ^ (p - 1 : ℕ) : ℕ) : ZMod p) =
      ∑ _i ∈ Finset.Ioo 0 p, (1 : ZMod p) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Nat.cast_pow]
    rw [Finset.mem_Ioo] at hi
    have hi0 : (i : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd hi.1 h) (not_le_of_gt hi.2)
    exact ZMod.pow_card_sub_one_eq_one hi0
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioo, Nat.sub_zero]
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.add_sub_of_le hp.one_le, ZMod.natCast_self]

lemma sum_pow_zmod_eq_zero_of_not_dvd {p k : ℕ} [Fact p.Prime] (hk : ¬ (p - 1 ∣ k)) :
    ∑ x : ZMod p, x ^ k = 0 := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
    intro h
    have h1 : g ^ k = 1 := by
      ext
      simpa [Units.val_pow_eq_pow_val] using h
    rw [← orderOf_dvd_iff_pow_eq_one, hord] at h1
    exact hk h1
  have hmul : (g : ZMod p) ^ k * ∑ x : ZMod p, x ^ k = ∑ x : ZMod p, x ^ k := by
    rw [Finset.mul_sum]
    have hbij : ∑ x : ZMod p, ((g : ZMod p) * x) ^ k = ∑ x : ZMod p, x ^ k := by
      refine Fintype.sum_bijective (fun x : ZMod p => (g : ZMod p) * x) ?_ _ _ (fun _ => rfl)
      exact (Units.mulLeft g).bijective
    simpa [mul_pow] using hbij
  have hsub : ((g : ZMod p) ^ k - 1) * ∑ x : ZMod p, x ^ k = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hgk_ne)

lemma sum_pow_zmod_eq_neg_one_of_dvd {p k : ℕ} [Fact p.Prime] (hk0 : 0 < k) (hk : p - 1 ∣ k) :
    ∑ x : ZMod p, x ^ k = -1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨m, rfl⟩ := hk
  have hterm : ∀ x : ZMod p, x ^ ((p - 1) * m) = if x = 0 then 0 else 1 := by
    intro x
    split_ifs with hx
    · subst hx
      exact zero_pow (Nat.ne_of_gt hk0)
    · rw [pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow]
  simp_rw [hterm, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  have hcard : (Finset.univ.filter (fun x : ZMod p => ¬ x = 0)).card = p - 1 := by
    have h1 : Finset.univ.filter (fun x : ZMod p => ¬ x = 0) = Finset.univ.erase (0 : ZMod p) := by
      ext x
      simp
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  rw [hcard, Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]

lemma sum_range_pow_zmod_mul (q p k : ℕ) :
    ((∑ i ∈ Finset.range (q * p), i ^ k : ℕ) : ZMod p) =
      (q : ZMod p) * ∑ r ∈ Finset.range p, (r : ZMod p) ^ k := by
  induction q with
  | zero =>
    simp
  | succ q ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, Nat.cast_add, ih]
    have hblock : ((∑ r ∈ Finset.range p, (q * p + r) ^ k : ℕ) : ZMod p) =
        ∑ r ∈ Finset.range p, (r : ZMod p) ^ k := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      push_cast
      rw [ZMod.natCast_self, mul_zero, zero_add]
    rw [hblock]
    push_cast
    ring

lemma sum_range_eq_sum_univ_zmod {p k : ℕ} [Fact p.Prime] :
    ∑ r ∈ Finset.range p, (r : ZMod p) ^ k = ∑ x : ZMod p, x ^ k := by
  refine Finset.sum_bij (fun r _ => (r : ZMod p)) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro a ha b hb hab
    rw [Finset.mem_range] at ha hb
    have ha' : (a : ZMod p).val = a := ZMod.val_natCast_of_lt ha
    have hb' : (b : ZMod p).val = b := ZMod.val_natCast_of_lt hb
    rw [← ha', ← hb', hab]
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
  · intro _ _; rfl

lemma sum_Ioo_eq_sum_range_pow {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ∑ i ∈ Finset.Ioo 0 n, i ^ k = ∑ i ∈ Finset.range n, i ^ k := by
  have hset : Finset.range n = insert 0 (Finset.Ioo 0 n) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hset, Finset.sum_insert (by simp), zero_pow (Nat.ne_of_gt hk), zero_add]

/- ### Section 2: Giuga's characterization, squarefreeness, oddness, normal-set property -/

lemma strongGiuga_korselt_and_giuga {n : ℕ} (hsg : IsStrongGiuga n) :
    ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1) ∧ p ∣ (n / p - 1) := by
  rcases hsg with ⟨hcomp, hdvd_n⟩
  have hn2 : 2 ≤ n := hcomp.1
  have hn0 : 0 < n := by omega
  have hnm1 : 0 < n - 1 := by omega
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have : Fact p.Prime := ⟨hp_prime⟩
  have hp_dvd_sum : p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1 : ℕ) :=
    dvd_trans hp_dvd hdvd_n
  have hz : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1 : ℕ) : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ p).mpr hp_dvd_sum
  rw [Nat.cast_add, Nat.cast_one, sum_Ioo_eq_sum_range_pow hn0 hnm1] at hz
  have hrange : Finset.range n = Finset.range ((n / p) * p) := by
    rw [Nat.div_mul_cancel hp_dvd]
  rw [hrange, sum_range_pow_zmod_mul, sum_range_eq_sum_univ_zmod] at hz
  have hkorselt : (p - 1) ∣ (n - 1) := by
    by_contra hndvd
    rw [sum_pow_zmod_eq_zero_of_not_dvd hndvd, mul_zero, add_zero] at hz
    exact one_ne_zero hz
  have hgiuga : p ∣ (n / p - 1) := by
    rw [sum_pow_zmod_eq_neg_one_of_dvd hnm1 hkorselt, mul_neg_one] at hz
    have hq1 : ((n / p : ℕ) : ZMod p) = 1 := by
      have h1 : (1 : ZMod p) + -((n / p : ℕ) : ZMod p) = 0 := hz
      exact (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h1)).symm
    have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn0 hp_dvd) hp_prime.pos
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hge1, hq1, Nat.cast_one, sub_self]
  exact ⟨hkorselt, hgiuga⟩

lemma strongGiuga_squarefree {n : ℕ} (hsg : IsStrongGiuga n) : Squarefree n := by
  have hn0 : n ≠ 0 := by have := hsg.1.1; omega
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩
  have hdvd1 : p ∣ n / p - 1 := (strongGiuga_korselt_and_giuga hsg p hmem).2
  rcases hpp with ⟨k, hk⟩
  have hdiv : n / p = p * k := by
    rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hdvd2 : p ∣ n / p := ⟨k, hdiv⟩
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn) hp.pos
  have h1 : p ∣ 1 := by
    have hadd : n / p - 1 + 1 = n / p := Nat.sub_add_cancel hge1
    exact (Nat.dvd_add_right hdvd1).mp (hadd.symm ▸ hdvd2)
  exact hp.not_dvd_one h1

lemma strongGiuga_div_p_mul_pred {n : ℕ} (hsg : IsStrongGiuga n) :
    ∀ p ∈ n.primeFactors, p * (p - 1) ∣ (n / p - 1) := by
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hn0 : 0 < n := by have := hsg.1.1; omega
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn0 hp_dvd) hp_prime.pos
  rcases strongGiuga_korselt_and_giuga hsg p hp with ⟨hkorselt, hgiuga⟩
  have hident : n - 1 = p * (n / p - 1) + (p - 1) := by
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hp_dvd
    have hp1 : 1 ≤ p := hp_prime.one_le
    zify [hp1, hge1, show 1 ≤ n by omega]
    have hmulZ : (p : ℤ) * ((n / p : ℕ) : ℤ) = (n : ℤ) := by exact_mod_cast hmul
    linarith
  have hdvd_pmul : (p - 1) ∣ p * (n / p - 1) := by
    rw [hident] at hkorselt
    exact (Nat.dvd_add_left (dvd_refl (p - 1))).mp hkorselt
  have hcop : Nat.Coprime (p - 1) p := by
    have h1 : p - 1 + 1 = p := Nat.sub_add_cancel hp_prime.one_le
    rw [← h1]
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hpred : (p - 1) ∣ (n / p - 1) := hcop.dvd_of_dvd_mul_left hdvd_pmul
  exact hcop.symm.mul_dvd_of_dvd_of_dvd hgiuga hpred

lemma prod_primeFactors_of_squarefree {n : ℕ} (hn0 : n ≠ 0) (hsq : Squarefree n) :
    ∏ p ∈ n.primeFactors, p = n := by
  have h1 : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hge1 : 1 ≤ n.factorization p :=
      (hp_prime.dvd_iff_one_le_factorization hn0).mp (Nat.dvd_of_mem_primeFactors hp)
    have hle1 : n.factorization p ≤ 1 := by
      by_contra hgt
      have h2 : 2 ≤ n.factorization p := by omega
      have hsq_dvd : p * p ∣ n := by
        rw [← sq]
        exact (pow_dvd_pow p h2).trans (n.ordProj_dvd p)
      exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp_prime) hsq_dvd
    omega
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [h1 p hp, pow_one]

lemma dvd_of_squarefree_forall_primeFactors_dvd {n m : ℕ} (hn0 : n ≠ 0) (hsq : Squarefree n)
    (h : ∀ p ∈ n.primeFactors, p ∣ m) : n ∣ m := by
  rw [← prod_primeFactors_of_squarefree hn0 hsq]
  have haux : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ p ∣ m) → ∏ p ∈ s, p ∣ m := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | @insert a s ha ih =>
      intro hs
      rw [Finset.prod_insert ha]
      have ha_p : a.Prime := (hs a (Finset.mem_insert_self a s)).1
      have ha_d : a ∣ m := (hs a (Finset.mem_insert_self a s)).2
      have hs_d : ∏ p ∈ s, p ∣ m := ih fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) := Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_p (hs p (Finset.mem_insert_of_mem hp)).1).mpr
          (fun hEq => ha (hEq ▸ hp))
      exact hcop.mul_dvd_of_dvd_of_dvd ha_d hs_d
  exact haux n.primeFactors fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, h p hp⟩

lemma two_le_primeFactors_card_of_composite_squarefree {n : ℕ} (hcomp : n.Composite)
    (hsq : Squarefree n) : 2 ≤ n.primeFactors.card := by
  have hn0 : n ≠ 0 := by have := hcomp.1; omega
  have hprod := prod_primeFactors_of_squarefree hn0 hsq
  by_contra hlt
  have hle : n.primeFactors.card ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [Finset.card_eq_zero.mp h0, Finset.prod_empty] at hprod
    have := hcomp.1; omega
  · rcases Finset.card_eq_one.mp h1 with ⟨p, hp⟩
    have hmem : p ∈ n.primeFactors := by rw [hp]; simp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hmem
    rw [hp, Finset.prod_singleton] at hprod
    exact hcomp.2 (hprod ▸ hp_prime)

lemma strongGiuga_odd {n : ℕ} (hsg : IsStrongGiuga n) : Odd n := by
  have hsq := strongGiuga_squarefree hsg
  have hcard := two_le_primeFactors_card_of_composite_squarefree hsg.1 hsq
  have hne : (n.primeFactors.erase 2).Nonempty := by
    have hle : n.primeFactors.card - 1 ≤ (n.primeFactors.erase 2).card :=
      Finset.pred_card_le_card_erase
    exact Finset.card_pos.mp (by omega)
  rcases hne with ⟨q, hq⟩
  have hq_ne2 : q ≠ 2 := (Finset.mem_erase.mp hq).1
  have hq_mem : q ∈ n.primeFactors := (Finset.mem_erase.mp hq).2
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_odd : q % 2 = 1 := by
    rcases hq_prime.eq_two_or_odd with rfl | hodd
    · exact absurd rfl hq_ne2
    · exact hodd
  have h2_dvd_q1 : 2 ∣ q - 1 := by omega
  have h2_dvd_n1 : 2 ∣ n - 1 := dvd_trans h2_dvd_q1 (strongGiuga_korselt_and_giuga hsg q hq_mem).1
  have hn2 : 2 ≤ n := hsg.1.1
  rcases h2_dvd_n1 with ⟨k, hk⟩
  exact ⟨k, by omega⟩

lemma strongGiuga_normal_set {n : ℕ} (hsg : IsStrongGiuga n) :
    ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors, ¬ (p ∣ (q - 1)) := by
  intro p hp q hq hdvd
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
  have hq_dvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq
  have hn0 : 0 < n := by have := hsg.1.1; omega
  have hpq_ne : p ≠ q := by
    intro heq
    subst heq
    have hp2 : 2 ≤ p := hp_prime.two_le
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr hpq_ne
  have hpq_dvd : p * q ∣ n := hcop.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd
  have hp_dvd_div : p ∣ n / q := by
    rcases hpq_dvd with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm, mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq_prime.pos]
  have hp_dvd_sub : p ∣ n / q - 1 :=
    dvd_trans hdvd (dvd_trans (dvd_mul_left (q - 1) q) (strongGiuga_div_p_mul_pred hsg q hq))
  have hge1 : 1 ≤ n / q := Nat.div_pos (Nat.le_of_dvd hn0 hq_dvd) hq_prime.pos
  have hp_dvd_one : p ∣ 1 := by
    have hadd : n / q - 1 + 1 = n / q := Nat.sub_add_cancel hge1
    exact (Nat.dvd_add_right hp_dvd_sub).mp (hadd.symm ▸ hp_dvd_div)
  exact hp_prime.not_dvd_one hp_dvd_one

lemma strongGiuga_reciprocal_sum {n : ℕ} (hsg : IsStrongGiuga n) :
    ∃ k : ℕ, 1 ≤ k ∧ ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ) := by
  have hn2 : 2 ≤ n := hsg.1.1
  have hn0 : n ≠ 0 := by omega
  have hsq := strongGiuga_squarefree hsg
  have hcard := two_le_primeFactors_card_of_composite_squarefree hsg.1 hsq
  set S : ℕ := ∑ p ∈ n.primeFactors, n / p
  have hS_ge2 : 2 ≤ S := by
    have h1 : ∀ p ∈ n.primeFactors, 1 ≤ n / p := fun p hp =>
      Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))
        (Nat.prime_of_mem_primeFactors hp).pos
    have hsum_ge : n.primeFactors.card ≤ S := by
      simpa using Finset.sum_le_sum h1
    omega
  have hn_dvd : n ∣ S - 1 := by
    refine dvd_of_squarefree_forall_primeFactors_dvd hn0 hsq fun p hp => ?_
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hsplit : S = n / p + ∑ q ∈ n.primeFactors.erase p, n / q :=
      (Finset.add_sum_erase _ _ hp).symm
    have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hp_dvd) hp_prime.pos
    have hsub_eq : S - 1 = (n / p - 1) + ∑ q ∈ n.primeFactors.erase p, n / q := by omega
    rw [hsub_eq]
    refine dvd_add (strongGiuga_korselt_and_giuga hsg p hp).2 ?_
    refine Finset.dvd_sum fun q hq => ?_
    have hq_ne : q ≠ p := (Finset.mem_erase.mp hq).1
    have hq_mem : q ∈ n.primeFactors := (Finset.mem_erase.mp hq).2
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
    have hq_dvd : q ∣ n := Nat.dvd_of_mem_primeFactors hq_mem
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr (Ne.symm hq_ne)
    rcases hcop.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm, mul_comm p q, mul_assoc, Nat.mul_div_cancel_left _ hq_prime.pos]
  rcases hn_dvd with ⟨k, hk⟩
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk_eq : k = 0 := by omega
    rw [hk_eq, mul_zero] at hk
    omega
  refine ⟨k, hk1, ?_⟩
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  have hS_eq : (S : ℚ) - 1 = (n : ℚ) * (k : ℚ) := by
    have hnat : S = n * k + 1 := by omega
    have hq : (S : ℚ) = (n : ℚ) * (k : ℚ) + 1 := by exact_mod_cast hnat
    linarith
  have hsumQ : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) = (S : ℚ) / (n : ℚ) := by
    dsimp [S]
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
    have hmul : ((n / p : ℕ) : ℚ) * (p : ℚ) = (n : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hp_dvd
    field_simp
    linarith
  rw [hsumQ, ← sub_div, hS_eq, mul_div_cancel_left₀ _ hnQ]

lemma sum_inv_gt_one_of_reciprocal_eq {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (heq : ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) - 1 / (n : ℚ) = (k : ℚ)) :
    (1 : ℚ) < ∑ p ∈ n.primeFactors, (1 / (p : ℚ)) := by
  have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hinv_pos : (0 : ℚ) < 1 / (n : ℚ) := div_pos one_pos hnQ
  have hkQ : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  linarith

/- ### Section 3: Sharp normal-set lower bounds on `n.primeFactors.card` -/

lemma card_gt_of_sum_inv_gt_one {S T : Finset ℕ} {B M : ℕ}
    (hB : 0 < B) (hM : 0 < M)
    (hTpos : ∀ p ∈ T, 0 < p)
    (hTle : ∀ p ∈ T, p ≤ B)
    (hcover : ∀ p ∈ S, p ≤ B → p ∈ T)
    (hsumS : (1 : ℚ) < ∑ p ∈ S, (1 / (p : ℚ)))
    (hsumT : ∑ p ∈ T, (M + p - 1) / p < M) :
    T.card < S.card := by
  have hMQ : (0 : ℚ) < (M : ℚ) := by exact_mod_cast hM
  have hBQ : (0 : ℚ) < (B : ℚ) := by exact_mod_cast hB
  have hT_lt_one : ∑ p ∈ T, (1 / (p : ℚ)) < 1 := by
    have hle_each : ∀ p ∈ T, (1 / (p : ℚ)) ≤ (((M + p - 1) / p : ℕ) : ℚ) / (M : ℚ) := by
      intro p hp
      have hp0 : 0 < p := hTpos p hp
      have hpQ : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hp0
      have hceil : M ≤ p * ((M + p - 1) / p) := by
        have hrem := Nat.mod_lt (M + p - 1) hp0
        have hdiv := Nat.div_add_mod (M + p - 1) p
        omega
      have hceilQ : (M : ℚ) ≤ (p : ℚ) * (((M + p - 1) / p : ℕ) : ℚ) := by exact_mod_cast hceil
      rw [div_le_div_iff₀ hpQ hMQ]
      linarith
    have hsum_le : ∑ p ∈ T, (1 / (p : ℚ)) ≤
        ((∑ p ∈ T, (M + p - 1) / p : ℕ) : ℚ) / (M : ℚ) := by
      rw [Nat.cast_sum, Finset.sum_div]
      exact Finset.sum_le_sum hle_each
    have hlt_M : ((∑ p ∈ T, (M + p - 1) / p : ℕ) : ℚ) / (M : ℚ) < 1 := by
      rw [div_lt_one hMQ]
      exact_mod_cast hsumT
    linarith
  by_contra hnot
  have hcard_le : S.card ≤ T.card := by omega
  have hS_split : S = (S ∩ T) ∪ (S \ T) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hT_split : T = (S ∩ T) ∪ (T \ S) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisjS : Disjoint (S ∩ T) (S \ T) :=
    Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2
  have hdisjT : Disjoint (S ∩ T) (T \ S) :=
    Finset.disjoint_left.mpr fun _ h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).1
  have hcard_sdiff : (S \ T).card ≤ (T \ S).card := by
    have h1 : S.card = (S ∩ T).card + (S \ T).card := by
      conv_lhs => rw [hS_split]
      exact Finset.card_union_of_disjoint hdisjS
    have h2 : T.card = (S ∩ T).card + (T \ S).card := by
      conv_lhs => rw [hT_split]
      exact Finset.card_union_of_disjoint hdisjT
    omega
  have hST_le : ∑ p ∈ S \ T, (1 / (p : ℚ)) ≤ ((S \ T).card : ℚ) * (1 / (B : ℚ)) := by
    calc ∑ p ∈ S \ T, (1 / (p : ℚ))
        ≤ ∑ _p ∈ S \ T, (1 / (B : ℚ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpS : p ∈ S := (Finset.mem_sdiff.mp hp).1
          have hpT : p ∉ T := (Finset.mem_sdiff.mp hp).2
          have hgt : B < p := by
            by_contra hle
            exact hpT (hcover p hpS (by omega))
          have hBle : (B : ℚ) ≤ (p : ℚ) := by exact_mod_cast hgt.le
          exact one_div_le_one_div_of_le hBQ hBle
      _ = ((S \ T).card : ℚ) * (1 / (B : ℚ)) := by simp
  have hTS_ge : ((T \ S).card : ℚ) * (1 / (B : ℚ)) ≤ ∑ p ∈ T \ S, (1 / (p : ℚ)) := by
    calc ((T \ S).card : ℚ) * (1 / (B : ℚ))
        = ∑ _p ∈ T \ S, (1 / (B : ℚ)) := by simp
      _ ≤ ∑ p ∈ T \ S, (1 / (p : ℚ)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hpT : p ∈ T := (Finset.mem_sdiff.mp hp).1
          have hp0 : (0 : ℚ) < (p : ℚ) := by exact_mod_cast hTpos p hpT
          have hpB : (p : ℚ) ≤ (B : ℚ) := by exact_mod_cast hTle p hpT
          exact one_div_le_one_div_of_le hp0 hpB
  have hmid : ((S \ T).card : ℚ) * (1 / (B : ℚ)) ≤ ((T \ S).card : ℚ) * (1 / (B : ℚ)) := by
    refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_sdiff) (by positivity)
  have hsumS_le_T : ∑ p ∈ S, (1 / (p : ℚ)) ≤ ∑ p ∈ T, (1 / (p : ℚ)) := by
    have h1 : ∑ p ∈ S, (1 / (p : ℚ)) =
        ∑ p ∈ S ∩ T, (1 / (p : ℚ)) + ∑ p ∈ S \ T, (1 / (p : ℚ)) := by
      conv_lhs => rw [hS_split]
      exact Finset.sum_union hdisjS
    have h2 : ∑ p ∈ T, (1 / (p : ℚ)) =
        ∑ p ∈ S ∩ T, (1 / (p : ℚ)) + ∑ p ∈ T \ S, (1 / (p : ℚ)) := by
      conv_lhs => rw [hT_split]
      exact Finset.sum_union hdisjT
    linarith
  linarith

lemma prime_sieve19 {p : ℕ} (hp : p.Prime) :
    (p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) ∨
      (2 ≤ p ∧ p % 2 ≠ 0 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧
        p % 11 ≠ 0 ∧ p % 13 ≠ 0 ∧ p % 17 ≠ 0 ∧ p % 19 ≠ 0) := by
  by_cases h : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19
  · exact Or.inl h
  · right
    push Not at h
    have hnot : ∀ q : ℕ, q.Prime → p ≠ q → p % q ≠ 0 := fun q hq hne hmod => by
      have hdvd : q ∣ p := Nat.dvd_of_mod_eq_zero hmod
      rcases hp.eq_one_or_self_of_dvd q hdvd with h1 | h2
      · exact hq.ne_one h1
      · exact hne h2.symm
    exact ⟨hp.two_le, hnot 2 (by decide) h.1, hnot 3 (by decide) h.2.1,
      hnot 5 (by decide) h.2.2.1, hnot 7 (by decide) h.2.2.2.1,
      hnot 11 (by decide) h.2.2.2.2.1, hnot 13 (by decide) h.2.2.2.2.2.1,
      hnot 17 (by decide) h.2.2.2.2.2.2.1, hnot 19 (by decide) h.2.2.2.2.2.2.2⟩

set_option maxRecDepth 8192 in
lemma bound_T3 :
    let T := (Finset.Icc 1 317).filter (fun p =>
      ((p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) ∨
        (2 ≤ p ∧ p % 2 ≠ 0 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧
          p % 11 ≠ 0 ∧ p % 13 ≠ 0 ∧ p % 17 ≠ 0 ∧ p % 19 ≠ 0)) ∧
      3 ≤ p ∧ (p = 3 ∨ p % 3 = 2))
    T.card = 35 ∧ ∑ p ∈ T, (1000000 + p - 1) / p < 1000000 := by
  decide

set_option maxRecDepth 8192 in
lemma bound_Tno3_yes5 :
    let T := (Finset.Icc 1 443).filter (fun p =>
      ((p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) ∨
        (2 ≤ p ∧ p % 2 ≠ 0 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧
          p % 11 ≠ 0 ∧ p % 13 ≠ 0 ∧ p % 17 ≠ 0 ∧ p % 19 ≠ 0)) ∧
      (p = 5 ∨ (7 ≤ p ∧ p % 5 ≠ 1)))
    T.card = 64 ∧ ∑ p ∈ T, (1000000 + p - 1) / p < 1000000 := by
  decide

set_option maxRecDepth 8192 in
lemma bound_Tno3_no5 :
    let T := (Finset.Icc 1 346).filter (fun p =>
      ((p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) ∨
        (2 ≤ p ∧ p % 2 ≠ 0 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧
          p % 11 ≠ 0 ∧ p % 13 ≠ 0 ∧ p % 17 ≠ 0 ∧ p % 19 ≠ 0)) ∧
      7 ≤ p)
    T.card = 65 ∧ ∑ p ∈ T, (1000000 + p - 1) / p < 1000000 := by
  decide

lemma strongGiuga_three_dvd_props {n : ℕ} (hsg : IsStrongGiuga n) (h3 : 3 ∣ n) :
    (∀ p ∈ n.primeFactors, p = 3 ∨ p % 3 = 2) ∧
    Odd n.primeFactors.card ∧
    37 ≤ n.primeFactors.card := by
  have hn0 : n ≠ 0 := by have := hsg.1.1; omega
  have hsq := strongGiuga_squarefree hsg
  have hodd := strongGiuga_odd hsg
  have h3_mem : 3 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h3, hn0⟩
  have hmod3 : ∀ p ∈ n.primeFactors, p = 3 ∨ p % 3 = 2 := by
    intro p hp
    by_cases hp3 : p = 3
    · exact Or.inl hp3
    · right
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hnot_dvd_p : ¬ (3 ∣ p) := by
        intro h3p
        rcases hp_prime.eq_one_or_self_of_dvd 3 h3p with h1 | h2
        · omega
        · exact hp3 h2.symm
      have hnot_dvd_sub : ¬ (3 ∣ p - 1) := strongGiuga_normal_set hsg 3 h3_mem p hp
      have hp2 : 2 ≤ p := hp_prime.two_le
      omega
  have hodd_card : Odd n.primeFactors.card := by
    have hprod := prod_primeFactors_of_squarefree hn0 hsq
    have hdiv3 : n / 3 = ∏ p ∈ n.primeFactors.erase 3, p := by
      have hmul : 3 * (∏ p ∈ n.primeFactors.erase 3, p) = n := by
        have h1 := Finset.mul_prod_erase n.primeFactors id h3_mem
        simpa [id] using h1.trans hprod
      calc n / 3 = (3 * ∏ p ∈ n.primeFactors.erase 3, p) / 3 := by rw [hmul]
        _ = ∏ p ∈ n.primeFactors.erase 3, p := Nat.mul_div_cancel_left _ (by decide)
    have hgiuga3 : 3 ∣ n / 3 - 1 := (strongGiuga_korselt_and_giuga hsg 3 h3_mem).2
    have hge1 : 1 ≤ n / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) h3) (by decide)
    have hmod_one : ((n / 3 : ℕ) : ZMod 3) = 1 := by
      have hz : ((n / 3 - 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ 3).mpr hgiuga3
      rw [Nat.cast_sub hge1, Nat.cast_one, sub_eq_zero] at hz
      exact hz
    have hmod_pow : ((n / 3 : ℕ) : ZMod 3) = (-1 : ZMod 3) ^ (n.primeFactors.erase 3).card := by
      rw [hdiv3, Nat.cast_prod]
      have hcongr : ∀ p ∈ n.primeFactors.erase 3, (p : ZMod 3) = (-1 : ZMod 3) := by
        intro p hp
        have hp_ne : p ≠ 3 := (Finset.mem_erase.mp hp).1
        have hp_mem : p ∈ n.primeFactors := (Finset.mem_erase.mp hp).2
        have hp2 : p % 3 = 2 := (hmod3 p hp_mem).resolve_left hp_ne
        have heq : p = 3 * (p / 3) + 2 := by omega
        rw [heq]
        push_cast
        have h3z : (3 : ZMod 3) = 0 := by decide
        rw [h3z, zero_mul, zero_add]
        decide
      rw [Finset.prod_congr rfl hcongr, Finset.prod_const]
    have hpow_one : (-1 : ZMod 3) ^ (n.primeFactors.erase 3).card = 1 := by
      rw [← hmod_pow, hmod_one]
    have heven_erase : Even (n.primeFactors.erase 3).card := by
      rcases Nat.even_or_odd (n.primeFactors.erase 3).card with hev | ⟨k, hk⟩
      · exact hev
      · rw [hk, pow_add, pow_mul] at hpow_one
        have hbad : (-1 : ZMod 3) = 1 := by simpa using hpow_one
        exact absurd hbad (by decide)
    have hcard_eq : (n.primeFactors.erase 3).card + 1 = n.primeFactors.card := by
      rw [Finset.card_erase_of_mem h3_mem]
      exact Nat.sub_add_cancel (Finset.card_pos.mpr ⟨3, h3_mem⟩)
    rcases heven_erase with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hcard_ge37 : 37 ≤ n.primeFactors.card := by
    rcases strongGiuga_reciprocal_sum hsg with ⟨k, hk, heq⟩
    have hsum_gt := sum_inv_gt_one_of_reciprocal_eq (by omega) hk heq
    set T := (Finset.Icc 1 317).filter (fun p =>
      ((p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) ∨
        (2 ≤ p ∧ p % 2 ≠ 0 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧
          p % 11 ≠ 0 ∧ p % 13 ≠ 0 ∧ p % 17 ≠ 0 ∧ p % 19 ≠ 0)) ∧
      3 ≤ p ∧ (p = 3 ∨ p % 3 = 2))
    have hTcard : T.card = 35 := bound_T3.1
    have hTsum : ∑ p ∈ T, (1000000 + p - 1) / p < 1000000 := bound_T3.2
    have hgt : T.card < n.primeFactors.card :=
      card_gt_of_sum_inv_gt_one (B := 317) (M := 1000000) (by decide) (by decide)
        (fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)
        (fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
        (fun p hp hle => by
          have hp_prime := Nat.prime_of_mem_primeFactors hp
          have hp_dvd := Nat.dvd_of_mem_primeFactors hp
          have hp_ge3 : 3 ≤ p := by
            have hp2 : 2 ≤ p := hp_prime.two_le
            have hp_ne2 : p ≠ 2 := by
              intro h2; subst h2
              rcases hodd with ⟨m, hm⟩
              rcases hp_dvd with ⟨j, hj⟩
              omega
            omega
          exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.pos, hle⟩,
            prime_sieve19 hp_prime, hp_ge3, hmod3 p hp⟩)
        hsum_gt hTsum
    rw [hTcard] at hgt
    rcases hodd_card with ⟨m, hm⟩
    omega
  exact ⟨hmod3, hodd_card, hcard_ge37⟩

lemma strongGiuga_not_three_dvd_props {n : ℕ} (hsg : IsStrongGiuga n) (hn3 : ¬ (3 ∣ n)) :
    (∀ p ∈ n.primeFactors, 5 ≤ p) ∧ 65 ≤ n.primeFactors.card := by
  have hn0 : n ≠ 0 := by have := hsg.1.1; omega
  have hodd := strongGiuga_odd hsg
  have hge5 : ∀ p ∈ n.primeFactors, 5 ≤ p := by
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hp_ne2 : p ≠ 2 := by
      intro h2
      subst h2
      rcases hodd with ⟨k, hk⟩
      rcases hp_dvd with ⟨m, hm⟩
      omega
    have hp_ne3 : p ≠ 3 := fun h3 => hn3 (h3 ▸ hp_dvd)
    have hp_ne4 : p ≠ 4 := fun h4 => (by decide : ¬ Nat.Prime 4) (h4 ▸ hp_prime)
    have hp2 : 2 ≤ p := hp_prime.two_le
    omega
  rcases strongGiuga_reciprocal_sum hsg with ⟨k, hk, heq⟩
  have hsum_gt := sum_inv_gt_one_of_reciprocal_eq (by omega) hk heq
  have hcard_ge65 : 65 ≤ n.primeFactors.card := by
    by_cases h5 : 5 ∣ n
    · have h5_mem : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by decide, h5, hn0⟩
      set T := (Finset.Icc 1 443).filter (fun p =>
        ((p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) ∨
          (2 ≤ p ∧ p % 2 ≠ 0 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧
            p % 11 ≠ 0 ∧ p % 13 ≠ 0 ∧ p % 17 ≠ 0 ∧ p % 19 ≠ 0)) ∧
        (p = 5 ∨ (7 ≤ p ∧ p % 5 ≠ 1)))
      have hTcard : T.card = 64 := bound_Tno3_yes5.1
      have hTsum : ∑ p ∈ T, (1000000 + p - 1) / p < 1000000 := bound_Tno3_yes5.2
      have hgt : T.card < n.primeFactors.card :=
        card_gt_of_sum_inv_gt_one (B := 443) (M := 1000000) (by decide) (by decide)
          (fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)
          (fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
          (fun p hp hle => by
            have hp_prime := Nat.prime_of_mem_primeFactors hp
            have hp5 := hge5 p hp
            refine Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨hp_prime.pos, hle⟩, prime_sieve19 hp_prime, ?_⟩
            by_cases hpeq5 : p = 5
            · exact Or.inl hpeq5
            · right
              have hp_ne6 : p ≠ 6 := fun h6 => (by decide : ¬ Nat.Prime 6) (h6 ▸ hp_prime)
              have hnot5 : ¬ (5 ∣ p - 1) := strongGiuga_normal_set hsg 5 h5_mem p hp
              exact ⟨by omega, by omega⟩)
          hsum_gt hTsum
      omega
    · set T := (Finset.Icc 1 346).filter (fun p =>
        ((p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19) ∨
          (2 ≤ p ∧ p % 2 ≠ 0 ∧ p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0 ∧
            p % 11 ≠ 0 ∧ p % 13 ≠ 0 ∧ p % 17 ≠ 0 ∧ p % 19 ≠ 0)) ∧
        7 ≤ p)
      have hTcard : T.card = 65 := bound_Tno3_no5.1
      have hTsum : ∑ p ∈ T, (1000000 + p - 1) / p < 1000000 := bound_Tno3_no5.2
      have hgt : T.card < n.primeFactors.card :=
        card_gt_of_sum_inv_gt_one (B := 346) (M := 1000000) (by decide) (by decide)
          (fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1)
          (fun p hp => (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2)
          (fun p hp hle => by
            have hp_prime := Nat.prime_of_mem_primeFactors hp
            have hp_dvd := Nat.dvd_of_mem_primeFactors hp
            have hp5 := hge5 p hp
            have hp_ne5 : p ≠ 5 := fun heq => h5 (heq ▸ hp_dvd)
            have hp_ne6 : p ≠ 6 := fun h6 => (by decide : ¬ Nat.Prime 6) (h6 ▸ hp_prime)
            exact Finset.mem_filter.mpr
              ⟨Finset.mem_Icc.mpr ⟨hp_prime.pos, hle⟩, prime_sieve19 hp_prime, by omega⟩)
          hsum_gt hTsum
      omega
  exact ⟨hge5, hcard_ge65⟩

/- ### Section 4: Assembly into `main` -/

theorem main : H1 → H2 → H3 → type_of% @AgohGiuga.agoh_giuga.variants.giuga := by
  intro h1 h2 h3 n hn2
  constructor
  · exact prime_dvd_sum_pow n
  · intro hdvd
    by_contra hnp
    have hcomp : n.Composite := ⟨hn2, hnp⟩
    have hsg : IsStrongGiuga n := ⟨hcomp, hdvd⟩
    have hsq := strongGiuga_squarefree hsg
    have hodd := strongGiuga_odd hsg
    have hdiv := strongGiuga_div_p_mul_pred hsg
    have hnorm := strongGiuga_normal_set hsg
    have hrecip := strongGiuga_reciprocal_sum hsg
    by_cases hdvd3 : 3 ∣ n
    · rcases strongGiuga_three_dvd_props hsg hdvd3 with ⟨hmod3, hodd_card, hcard37⟩
      exact h1 n hcomp hsq hodd hdvd3 hodd_card hcard37 hmod3 hdiv hnorm hrecip
    · rcases strongGiuga_not_three_dvd_props hsg hdvd3 with ⟨hge5, hcard65⟩
      rcases hrecip with ⟨k, hk1, heq⟩
      by_cases hk_eq1 : k = 1
      · rw [hk_eq1, Nat.cast_one] at heq
        exact h2 n hcomp hsq hodd hdvd3 hcard65 hge5 hdiv hnorm heq
      · exact h3 n hcomp hsq hodd hdvd3 hcard65 hge5 hdiv hnorm ⟨k, by omega, heq⟩

end OMA.R_AgohGiuga_agoh_giuga_variants_giuga_R2
