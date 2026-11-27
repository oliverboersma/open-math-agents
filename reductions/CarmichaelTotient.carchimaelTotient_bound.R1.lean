import FormalConjectures.Wikipedia.CarmichaelTotient

-- Reduction CarmichaelTotient.carchimaelTotient_bound.R1 of Carmichael's totient function conjecture — carchimaelTotient bound
-- Credit: @ItsNotTheGabs
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of Kevin Ford's bound for Carmichael's totient conjecture (Theorem 6 in [F1998])

Following Carmichael (1922), Klee (1947), Schlafly–Wagon (1994), and Ford (1998, Section 7,
Theorem 6), we reduce `CarmichaelTotient.carchimaelTotient_bound` completely to two pure
prime-closure growth statements corresponding to the exhaustive dichotomy `3 ^ 2 ∥ n` (Case I)
versus `3 ^ 3 ∣ n` (Case II).

In this file we prove unconditionally:
- `carmichael_klee`: the Carmichael–Klee criterion (Lemma CK of [F1998]);
- `four_dvd_of_not_carmichael` and `nine_dvd_of_not_carmichael`: every positive counterexample
  is divisible by `36 = 2 ^ 2 * 3 ^ 2`;
- `case1_closed_6`, `case1_closed_12`, and `case2_closed_18`: the prime-square closure rules
  in Case I (`3 ^ 2 ∥ n`, rules `6k + 1` and `12k + 1`) and Case II (`3 ^ 3 ∣ n`, rules `6k + 1`
  and `18k + 1`);
- `lucas_primality`: the Lucas–Lehmer–Brillhart–Selfridge primality test (Lemma LLBS of [F1998])
  so downstream solvers of `H1` and `H2` can directly certify primes `c * ∏ q ∈ T, q + 1`.
-/

namespace OMA.R_CarmichaelTotient_carchimaelTotient_bound_R1

open Nat

/-- If every prime factor of `b` divides `a`, then `φ(a * b) = φ(a) * b`. -/
theorem totient_mul_of_prime_dvd {a b : ℕ} (hb : 0 < b)
    (h : ∀ p : ℕ, p.Prime → p ∣ b → p ∣ a) :
    φ (a * b) = φ a * b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    by_cases hb1 : b = 1
    · subst hb1; simp
    · have hb_gt : 1 < b := by omega
      set p := b.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpb : p ∣ b := Nat.minFac_dvd b
      have hpa : p ∣ a := h p hp hpb
      have hbq_pos : 0 < b / p := Nat.div_pos (Nat.le_of_dvd hb hpb) hp.pos
      have hbq_lt : b / p < b := Nat.div_lt_self hb hp.one_lt
      have hbq_mul : b / p * p = b := Nat.div_mul_cancel hpb
      have hsub : ∀ q : ℕ, q.Prime → q ∣ b / p → q ∣ a := fun q hq hq' =>
        h q hq (dvd_trans hq' (Nat.div_dvd_of_dvd hpb))
      have hih := ih (b / p) hbq_lt hbq_pos hsub
      have hmul : a * b = p * (a * (b / p)) := by
        calc
          a * b = a * (b / p * p) := by rw [hbq_mul]
          _ = p * (a * (b / p)) := by ring
      rw [hmul, Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_left hpa (b / p)), hih]
      calc
        p * (φ a * (b / p)) = φ a * (b / p * p) := by ring
        _ = φ a * b := by rw [hbq_mul]

/-- The Carmichael–Klee criterion (Lemma CK in Ford 1998): if `n > 0` is a counterexample
to Carmichael's totient conjecture, `d ∣ n` with `Coprime d (n / d)`, every prime divisor
of `φ(d)` divides `n`, `e > 0` divides `n / d` with every prime factor of `e` dividing
`(n / d) / e`, and `P = 1 + e * φ(d)` is prime, then `P ^ 2 ∣ n`. -/
theorem carmichael_klee {n d e : ℕ} (hn : 0 < n)
    (hnc : ¬ CarmichaelTotient.CarmichaelTotientFor n)
    (hd : d ∣ n) (hcop : d.Coprime (n / d))
    (hφd : ∀ q : ℕ, q.Prime → q ∣ φ d → q ∣ n)
    (hepos : 0 < e) (hed : e ∣ n / d)
    (herad : ∀ q : ℕ, q.Prime → q ∣ e → q ∣ (n / d) / e)
    (hP : (1 + e * φ d).Prime) :
    (1 + e * φ d) ^ 2 ∣ n := by
  set r := n / d
  set P := 1 + e * φ d
  have hdr : d * r = n := Nat.mul_div_cancel' hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
  have hr_dvd : r ∣ n := ⟨d, by rw [mul_comm, hdr]⟩
  have hre : r / e * e = r := Nat.div_mul_cancel hed
  have hφdpos : 0 < φ d := Nat.totient_pos.mpr hdpos
  have hP_dvd : P ∣ n := by
    by_contra hPn
    have hcop_re_P : (r / e).Coprime P := by
      refine (hP.coprime_iff_not_dvd.mpr ?_).symm
      intro hPre
      exact hPn (dvd_trans hPre (dvd_trans (Nat.div_dvd_of_dvd hed) hr_dvd))
    have htot : φ (r / e * P) = φ n := by
      rw [Nat.totient_mul hcop_re_P, Nat.totient_prime hP]
      have hPsub : P - 1 = e * φ d := by omega
      rw [hPsub, ← mul_assoc, ← totient_mul_of_prime_dvd hepos herad, hre,
        mul_comm, ← Nat.totient_mul hcop, hdr]
    have hne : r / e * P ≠ n := by
      intro heq
      exact hPn ⟨r / e, by rw [mul_comm, heq]⟩
    exact hnc ⟨r / e * P, hne, htot⟩
  by_contra hP2
  set u := n / P
  have hPu : P * u = n := Nat.mul_div_cancel' hP_dvd
  have hupos : 0 < u := by
    rcases Nat.eq_zero_or_pos u with hu0 | hup
    · rw [hu0, mul_zero] at hPu; omega
    · exact hup
  have hPnu : ¬ P ∣ u := by
    intro hPu'
    apply hP2
    rcases hPu' with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      n = P * u := hPu.symm
      _ = P * (P * t) := by rw [ht]
      _ = P ^ 2 * t := by ring
  have hPcopu : P.Coprime u := hP.coprime_iff_not_dvd.mpr hPnu
  have heφpos : 0 < e * φ d := Nat.mul_pos hepos hφdpos
  have hprime_u : ∀ q : ℕ, q.Prime → q ∣ e * φ d → q ∣ u := by
    intro q hq hqdvd
    have hqn : q ∣ n := by
      rcases hq.dvd_mul.mp hqdvd with hqe | hqφ
      · exact dvd_trans hqe (dvd_trans hed hr_dvd)
      · exact hφd q hq hqφ
    have hqlt : q < P := lt_of_le_of_lt (Nat.le_of_dvd heφpos hqdvd) (by omega)
    have hqnotP : ¬ q ∣ P := by
      intro hqP
      exact (Nat.ne_of_lt hqlt) ((Nat.prime_dvd_prime_iff_eq hq hP).mp hqP)
    rw [← hPu] at hqn
    rcases hq.dvd_mul.mp hqn with hqP | hqu
    · exact absurd hqP hqnotP
    · exact hqu
  have htot : φ (u * (e * φ d)) = φ n := by
    rw [totient_mul_of_prime_dvd heφpos hprime_u, ← hPu, Nat.totient_mul hPcopu,
      Nat.totient_prime hP]
    have hPsub : P - 1 = e * φ d := by omega
    rw [hPsub, mul_comm]
  have hne : u * (e * φ d) ≠ n := by
    have hlt : u * (e * φ d) < u * P := Nat.mul_lt_mul_of_pos_left (by omega) hupos
    rw [mul_comm u P, hPu] at hlt
    exact Nat.ne_of_lt hlt
  exact hnc ⟨u * (e * φ d), hne, htot⟩

/-- Every positive counterexample to Carmichael's totient conjecture is divisible by `4`. -/
theorem four_dvd_of_not_carmichael {n : ℕ} (hn : 0 < n)
    (hnc : ¬ CarmichaelTotient.CarmichaelTotientFor n) : 4 ∣ n := by
  have h2 : 2 ∣ n := by
    by_contra hodd
    exact hnc (CarmichaelTotient.carmichealTotientFor_odd (Nat.odd_iff.mpr (by omega)))
  by_contra h4
  set u := n / 2
  have h2u : 2 * u = n := Nat.mul_div_cancel' h2
  have huodd : ¬ 2 ∣ u := by
    intro h2u'
    apply h4
    rcases h2u' with ⟨t, ht⟩
    exact ⟨t, by omega⟩
  have hcop : Nat.Coprime 2 u := (Nat.prime_two.coprime_iff_not_dvd).mpr huodd
  have htot : φ u = φ n := by
    rw [← h2u, Nat.totient_mul hcop, Nat.totient_two, one_mul]
  exact hnc ⟨u, Nat.ne_of_lt (by linarith), htot⟩

/-- Every positive counterexample to Carmichael's totient conjecture is divisible by `9`. -/
theorem nine_dvd_of_not_carmichael {n : ℕ} (hn : 0 < n)
    (hnc : ¬ CarmichaelTotient.CarmichaelTotientFor n) : 9 ∣ n := by
  have h4 : 4 ∣ n := four_dvd_of_not_carmichael hn hnc
  have h2 : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) h4
  have h2div : 2 ∣ n / 2 := by
    rcases h4 with ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    omega
  have hck := carmichael_klee (d := 1) (e := 2) hn hnc (one_dvd n)
    (by simp)
    (fun q hq hq1 => by simp at hq1; exact absurd hq1 hq.ne_one)
    (by decide) (by simpa using h2)
    (fun q hq hq2 => by
      have hqeq : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hq2
      subst hqeq
      simpa using h2div)
    (by decide)
  simpa using hck

/-- The product of squares of distinct primes whose squares divide `n` divides `n`. -/
theorem finset_prod_sq_dvd {n : ℕ} {F : Finset ℕ}
    (hF : ∀ p ∈ F, p.Prime ∧ p ^ 2 ∣ n) : (∏ p ∈ F, p ^ 2) ∣ n := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_info := hF a (Finset.mem_insert_self a s)
    have hs_dvd : (∏ p ∈ s, p ^ 2) ∣ n :=
      ih (fun p hp => hF p (Finset.mem_insert_of_mem hp))
    have hcop : (a ^ 2).Coprime (∏ p ∈ s, p ^ 2) := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hp_info := hF p (Finset.mem_insert_of_mem hp)
      have hne : a ≠ p := fun heq => ha (heq ▸ hp)
      exact ((Nat.coprime_primes ha_info.1 hp_info.1).mpr hne).pow 2 2
    exact hcop.mul_dvd_of_dvd_of_dvd ha_info.2 hs_dvd

/-- If `4 ∣ n`, `9 ∣ n`, and every `p ∈ F` is prime `> 3` with `p ^ 2 ∣ n`,
then `36 * ∏ p ∈ F, p ^ 2 ∣ n`. -/
theorem dvd_36_mul_prod_sq {n : ℕ} {F : Finset ℕ} (h4 : 4 ∣ n) (h9 : 9 ∣ n)
    (hF : ∀ p ∈ F, p.Prime ∧ 3 < p ∧ p ^ 2 ∣ n) :
    36 * (∏ p ∈ F, p ^ 2) ∣ n := by
  have h36 : 36 ∣ n :=
    (show Nat.Coprime 4 9 by decide).mul_dvd_of_dvd_of_dvd h4 h9
  have hF_dvd : (∏ p ∈ F, p ^ 2) ∣ n :=
    finset_prod_sq_dvd (fun p hp => ⟨(hF p hp).1, (hF p hp).2.2⟩)
  have hcop : Nat.Coprime 36 (∏ p ∈ F, p ^ 2) := by
    refine Nat.Coprime.prod_right fun p hp => ?_
    have hp_p := (hF p hp).1
    have hp_gt := (hF p hp).2.1
    have hc2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp_p).mpr (by omega)
    have hc3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp_p).mpr (by omega)
    have h36eq : (36 : ℕ) = 2 ^ 2 * 3 ^ 2 := by decide
    rw [h36eq]
    exact ((hc2.pow_left 2).mul_left (hc3.pow_left 2)).pow_right 2
  exact hcop.mul_dvd_of_dvd_of_dvd h36 hF_dvd

/-- If `4 ∣ n`, `27 ∣ n`, and every `p ∈ F` is prime `> 3` with `p ^ 2 ∣ n`,
then `108 * ∏ p ∈ F, p ^ 2 ∣ n`. -/
theorem dvd_108_mul_prod_sq {n : ℕ} {F : Finset ℕ} (h4 : 4 ∣ n) (h27 : 27 ∣ n)
    (hF : ∀ p ∈ F, p.Prime ∧ 3 < p ∧ p ^ 2 ∣ n) :
    108 * (∏ p ∈ F, p ^ 2) ∣ n := by
  have h108 : 108 ∣ n :=
    (show Nat.Coprime 4 27 by decide).mul_dvd_of_dvd_of_dvd h4 h27
  have hF_dvd : (∏ p ∈ F, p ^ 2) ∣ n :=
    finset_prod_sq_dvd (fun p hp => ⟨(hF p hp).1, (hF p hp).2.2⟩)
  have hcop : Nat.Coprime 108 (∏ p ∈ F, p ^ 2) := by
    refine Nat.Coprime.prod_right fun p hp => ?_
    have hp_p := (hF p hp).1
    have hp_gt := (hF p hp).2.1
    have hc2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp_p).mpr (by omega)
    have hc3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp_p).mpr (by omega)
    have h108eq : (108 : ℕ) = 2 ^ 2 * 3 ^ 3 := by decide
    rw [h108eq]
    exact ((hc2.pow_left 2).mul_left (hc3.pow_left 3)).pow_right 2
  exact hcop.mul_dvd_of_dvd_of_dvd h108 hF_dvd

/-- Closure under `6 * ∏ q ∈ T, q + 1` for prime-square divisors `> 3` of a counterexample. -/
theorem closed_6 {n : ℕ} (hn : 0 < n) (hnc : ¬ CarmichaelTotient.CarmichaelTotientFor n)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ 3 < q ∧ q ^ 2 ∣ n)
    (hP : (6 * ∏ q ∈ T, q + 1).Prime) :
    (6 * ∏ q ∈ T, q + 1).Prime ∧ 3 < 6 * ∏ q ∈ T, q + 1 ∧ (6 * ∏ q ∈ T, q + 1) ^ 2 ∣ n := by
  set k := ∏ q ∈ T, q
  have hk_pos : 0 < k := Finset.prod_pos fun q hq => (hT q hq).1.pos
  have h4 := four_dvd_of_not_carmichael hn hnc
  have h9 := nine_dvd_of_not_carmichael hn hnc
  have h36k2 : 36 * k ^ 2 ∣ n := by
    have hsq : ∏ q ∈ T, q ^ 2 = k ^ 2 := Finset.prod_pow T 2 (fun q => q)
    rw [← hsq]
    exact dvd_36_mul_prod_sq h4 h9 hT
  have he2 : (6 * k) * (6 * k) ∣ n := by
    have : (6 * k) * (6 * k) = 36 * k ^ 2 := by ring
    rwa [this]
  have hed : 6 * k ∣ n := dvd_trans (dvd_mul_right (6 * k) (6 * k)) he2
  have hediv : 6 * k ∣ n / (6 * k) := by
    rcases he2 with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hpos : 0 < 6 * k := by omega
    calc
      n / (6 * k) = (6 * k * (6 * k * t)) / (6 * k) := by rw [ht, mul_assoc]
      _ = 6 * k * t := Nat.mul_div_right (6 * k * t) hpos
  have hck := carmichael_klee (d := 1) (e := 6 * k) hn hnc (one_dvd n)
    (by simp)
    (fun q hq hq1 => by simp at hq1; exact absurd hq1 hq.ne_one)
    (by omega) (by simpa using hed)
    (fun q _ hqe => by simpa using dvd_trans hqe hediv)
    (by simpa [add_comm] using hP)
  refine ⟨hP, by omega, ?_⟩
  simpa [add_comm] using hck

/-- Closure under `12 * ∏ q ∈ T, q + 1` in Case I (`3 ^ 2 ∥ n`). -/
theorem case1_closed_12 {n : ℕ} (hn : 0 < n) (hnc : ¬ CarmichaelTotient.CarmichaelTotientFor n)
    (h27 : ¬ 27 ∣ n) (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ 3 < q ∧ q ^ 2 ∣ n)
    (hP : (12 * ∏ q ∈ T, q + 1).Prime) :
    (12 * ∏ q ∈ T, q + 1).Prime ∧ 3 < 12 * ∏ q ∈ T, q + 1 ∧ (12 * ∏ q ∈ T, q + 1) ^ 2 ∣ n := by
  set k := ∏ q ∈ T, q
  have hk_pos : 0 < k := Finset.prod_pos fun q hq => (hT q hq).1.pos
  have h4 := four_dvd_of_not_carmichael hn hnc
  have h9 := nine_dvd_of_not_carmichael hn hnc
  have h3ndiv : ¬ 3 ∣ n / 9 := by
    intro h3
    apply h27
    rcases h3 with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have h9n := Nat.mul_div_cancel' h9
    calc
      n = 9 * (n / 9) := h9n.symm
      _ = 9 * (3 * t) := by rw [ht]
      _ = 27 * t := by ring
  have hcop9 : Nat.Coprime 9 (n / 9) := by
    have hcop3 : Nat.Coprime 3 (n / 9) := Nat.prime_three.coprime_iff_not_dvd.mpr h3ndiv
    simpa [show (9 : ℕ) = 3 ^ 2 by decide] using hcop3.pow_left 2
  have h36k2 : 36 * k ^ 2 ∣ n := by
    have hsq : ∏ q ∈ T, q ^ 2 = k ^ 2 := Finset.prod_pow T 2 (fun q => q)
    rw [← hsq]
    exact dvd_36_mul_prod_sq h4 h9 hT
  have he2 : (2 * k) * (2 * k) ∣ n / 9 := by
    rcases h36k2 with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      n / 9 = (9 * (4 * k ^ 2 * t)) / 9 := by congr 1; linarith
      _ = 4 * k ^ 2 * t := Nat.mul_div_right _ (by decide)
      _ = 2 * k * (2 * k) * t := by ring
  have hed : 2 * k ∣ n / 9 := dvd_trans (dvd_mul_right (2 * k) (2 * k)) he2
  have hediv : 2 * k ∣ (n / 9) / (2 * k) := by
    rcases he2 with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hpos : 0 < 2 * k := by omega
    calc
      (n / 9) / (2 * k) = (2 * k * (2 * k * t)) / (2 * k) := by rw [ht, mul_assoc]
      _ = 2 * k * t := Nat.mul_div_right (2 * k * t) hpos
  have hφ9_val : φ 9 = 6 := by decide
  have hφ9_dvd : ∀ q : ℕ, q.Prime → q ∣ φ 9 → q ∣ n := by
    intro q _ hq
    rw [hφ9_val] at hq
    have h36 : 36 ∣ n := (show Nat.Coprime 4 9 by decide).mul_dvd_of_dvd_of_dvd h4 h9
    exact dvd_trans hq (dvd_trans (by decide : 6 ∣ 36) h36)
  have hPeq : 1 + 2 * k * φ 9 = 12 * k + 1 := by rw [hφ9_val]; ring
  have hck := carmichael_klee (d := 9) (e := 2 * k) hn hnc h9 hcop9 hφ9_dvd
    (by omega) hed (fun q _ hqe => dvd_trans hqe hediv) (by rwa [hPeq])
  refine ⟨hP, by omega, ?_⟩
  rwa [hPeq] at hck

/-- Closure under `18 * ∏ q ∈ T, q + 1` in Case II (`3 ^ 3 ∣ n`). -/
theorem case2_closed_18 {n : ℕ} (hn : 0 < n) (hnc : ¬ CarmichaelTotient.CarmichaelTotientFor n)
    (h27 : 27 ∣ n) (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ 3 < q ∧ q ^ 2 ∣ n)
    (hP : (18 * ∏ q ∈ T, q + 1).Prime) :
    (18 * ∏ q ∈ T, q + 1).Prime ∧ 3 < 18 * ∏ q ∈ T, q + 1 ∧ (18 * ∏ q ∈ T, q + 1) ^ 2 ∣ n := by
  set k := ∏ q ∈ T, q
  have hk_pos : 0 < k := Finset.prod_pos fun q hq => (hT q hq).1.pos
  have h4 := four_dvd_of_not_carmichael hn hnc
  have h108k2 : 108 * k ^ 2 ∣ n := by
    have hsq : ∏ q ∈ T, q ^ 2 = k ^ 2 := Finset.prod_pow T 2 (fun q => q)
    rw [← hsq]
    exact dvd_108_mul_prod_sq h4 h27 hT
  have he_mul : (18 * k) * (6 * k) ∣ n := by
    have : (18 * k) * (6 * k) = 108 * k ^ 2 := by ring
    rwa [this]
  have hed : 18 * k ∣ n := dvd_trans (dvd_mul_right (18 * k) (6 * k)) he_mul
  have h6div : 6 * k ∣ n / (18 * k) := by
    rcases he_mul with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    have hpos : 0 < 18 * k := by omega
    calc
      n / (18 * k) = (18 * k * (6 * k * t)) / (18 * k) := by rw [ht, mul_assoc]
      _ = 6 * k * t := Nat.mul_div_right (6 * k * t) hpos
  have herad : ∀ q : ℕ, q.Prime → q ∣ 18 * k → q ∣ (n / 1) / (18 * k) := by
    intro q hq hq18
    have hq6 : q ∣ 6 * k := by
      have : 18 * k = 3 * (6 * k) := by ring
      rw [this] at hq18
      rcases hq.dvd_mul.mp hq18 with hq3 | hq6k
      · exact dvd_trans hq3 (dvd_trans (by decide : 3 ∣ 6) (dvd_mul_right 6 k))
      · exact hq6k
    simpa using dvd_trans hq6 h6div
  have hck := carmichael_klee (d := 1) (e := 18 * k) hn hnc (one_dvd n)
    (by simp)
    (fun q hq hq1 => by simp at hq1; exact absurd hq1 hq.ne_one)
    (by omega) (by simpa using hed) herad
    (by simpa [add_comm] using hP)
  refine ⟨hP, by omega, ?_⟩
  simpa [add_comm] using hck

/-- The Lucas–Lehmer–Brillhart–Selfridge primality criterion (Lemma LLBS in Ford 1998):
if `1 < p` and for every prime `q ∣ p - 1` there exists `a` with `a ^ (p - 1) ≡ 1 [MOD p]`
and `¬ (a ^ ((p - 1) / q) ≡ 1 [MOD p])`, then `p` is prime. -/
theorem lucas_primality {p : ℕ} (hp : 1 < p)
    (h : ∀ q : ℕ, q.Prime → q ∣ p - 1 →
      ∃ a : ℕ, a ^ (p - 1) ≡ 1 [MOD p] ∧ ¬ (a ^ ((p - 1) / q) ≡ 1 [MOD p])) :
    p.Prime := by
  have : NeZero p := ⟨by omega⟩
  have hp1_ne : p - 1 ≠ 0 := by omega
  have hdvd_tot : p - 1 ∣ φ p := by
    rw [← Nat.factorization_le_iff_dvd hp1_ne (Nat.totient_pos.mpr (by omega)).ne']
    intro q
    by_cases hqdvd : q.Prime ∧ q ∣ p - 1
    · obtain ⟨hq, hqdvd⟩ := hqdvd
      obtain ⟨a, ha1, haq⟩ := h q hq hqdvd
      have hu_pow : (a : ZMod p) ^ (p - 1) = 1 := by
        have := (ZMod.natCast_eq_natCast_iff _ _ p).mpr ha1
        simpa using this
      let u : (ZMod p)ˣ :=
        ⟨(a : ZMod p), (a : ZMod p) ^ (p - 2),
          by rw [mul_comm, ← pow_succ, show p - 2 + 1 = p - 1 by omega]; exact hu_pow,
          by rw [← pow_succ, show p - 2 + 1 = p - 1 by omega]; exact hu_pow⟩
      have hu_eq : u ^ (p - 1) = 1 := by
        apply Units.ext
        simpa [u] using hu_pow
      have hord_dvd_p1 : orderOf u ∣ p - 1 := orderOf_dvd_of_pow_eq_one hu_eq
      have hord_ndvd : ¬ orderOf u ∣ (p - 1) / q := by
        intro hd
        apply haq
        have huq : u ^ ((p - 1) / q) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
        have hzq : ((a ^ ((p - 1) / q) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
          have := congrArg Units.val huq
          simpa [u] using this
        exact (ZMod.natCast_eq_natCast_iff _ _ p).mp hzq
      have hord_pos : 0 < orderOf u := orderOf_pos u
      have hord_le : (p - 1).factorization q ≤ (orderOf u).factorization q := by
        by_contra hlt
        push Not at hlt
        apply hord_ndvd
        have hdiv_ne : (p - 1) / q ≠ 0 :=
          (Nat.div_pos (Nat.le_of_dvd (by omega) hqdvd) hq.pos).ne'
        rw [← Nat.factorization_le_iff_dvd hord_pos.ne' hdiv_ne]
        intro r
        have hord_f := (Nat.factorization_le_iff_dvd hord_pos.ne' hp1_ne).mpr hord_dvd_p1 r
        rw [Nat.factorization_div hqdvd, Finsupp.tsub_apply, hq.factorization]
        by_cases hrq : r = q
        · subst hrq; simp; omega
        · simp [Ne.symm hrq, hord_f]
      have hord_tot : orderOf u ∣ φ p := by
        simpa [ZMod.card_units_eq_totient] using orderOf_dvd_card (x := u)
      have htot_f :=
        (Nat.factorization_le_iff_dvd hord_pos.ne' (Nat.totient_pos.mpr (by omega)).ne').mpr
          hord_tot q
      exact le_trans hord_le htot_f
    · by_cases hqp : q.Prime
      · have hnd : ¬ q ∣ p - 1 := fun hd => hqdvd ⟨hqp, hd⟩
        simp [Nat.factorization_eq_zero_of_not_dvd hnd]
      · simp [Nat.factorization_eq_zero_of_not_prime (p - 1) hqp]
  have hle1 : p - 1 ≤ φ p := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega)) hdvd_tot
  have hle2 : φ p ≤ p - 1 := by
    have := Nat.totient_lt p hp
    omega
  exact (Nat.totient_eq_iff_prime (by omega)).mp (le_antisymm hle2 hle1)

/-- Bootstrap primes for Case I: `7, 13, 43` belong to every Case-I closed set. -/
theorem base_primes_case1 {S : Set ℕ}
    (h6 : ∀ T : Finset ℕ, (∀ q ∈ T, q ∈ S) →
      (6 * ∏ q ∈ T, q + 1).Prime → 6 * ∏ q ∈ T, q + 1 ∈ S)
    (h12 : ∀ T : Finset ℕ, (∀ q ∈ T, q ∈ S) →
      (12 * ∏ q ∈ T, q + 1).Prime → 12 * ∏ q ∈ T, q + 1 ∈ S) :
    7 ∈ S ∧ 13 ∈ S ∧ 43 ∈ S := by
  have h7 : 7 ∈ S := by simpa using h6 ∅ (by simp) (by decide)
  have h13 : 13 ∈ S := by simpa using h12 ∅ (by simp) (by decide)
  have h43 : 43 ∈ S := by
    simpa using h6 {7} (by intro q hq; rw [Finset.mem_singleton] at hq; subst hq; exact h7)
      (by decide)
  exact ⟨h7, h13, h43⟩

/-- Bootstrap primes for Case II: `7, 19, 43, 127` belong to every Case-II closed set. -/
theorem base_primes_case2 {S : Set ℕ}
    (h6 : ∀ T : Finset ℕ, (∀ q ∈ T, q ∈ S) →
      (6 * ∏ q ∈ T, q + 1).Prime → 6 * ∏ q ∈ T, q + 1 ∈ S)
    (h18 : ∀ T : Finset ℕ, (∀ q ∈ T, q ∈ S) →
      (18 * ∏ q ∈ T, q + 1).Prime → 18 * ∏ q ∈ T, q + 1 ∈ S) :
    7 ∈ S ∧ 19 ∈ S ∧ 43 ∈ S ∧ 127 ∈ S := by
  have h7 : 7 ∈ S := by simpa using h6 ∅ (by simp) (by decide)
  have h19 : 19 ∈ S := by simpa using h18 ∅ (by simp) (by decide)
  have h43 : 43 ∈ S := by
    simpa using h6 {7} (by intro q hq; rw [Finset.mem_singleton] at hq; subst hq; exact h7)
      (by decide)
  have h127 : 127 ∈ S := by
    simpa using h18 {7} (by intro q hq; rw [Finset.mem_singleton] at hq; subst hq; exact h7)
      (by decide)
  exact ⟨h7, h19, h43, h127⟩

/-- Case (I) of Ford (1998, Theorem 6) (`3 ^ 2 ∥ n`): every set `S` of natural numbers closed
under adjoining primes of the form `6 * ∏ q ∈ T, q + 1` or `12 * ∏ q ∈ T, q + 1` (for finite
`T ⊆ S`) contains a finite subset `F` with `10 ^ (10 ^ 10) ≤ 36 * ∏ p ∈ F, p ^ 2`. -/
def H1 : Prop :=
  ∀ S : Set ℕ,
    (∀ T : Finset ℕ, (∀ q ∈ T, q ∈ S) →
      (6 * ∏ q ∈ T, q + 1).Prime → 6 * ∏ q ∈ T, q + 1 ∈ S) →
    (∀ T : Finset ℕ, (∀ q ∈ T, q ∈ S) →
      (12 * ∏ q ∈ T, q + 1).Prime → 12 * ∏ q ∈ T, q + 1 ∈ S) →
    ∃ F : Finset ℕ, (∀ p ∈ F, p ∈ S) ∧ 10 ^ (10 ^ 10) ≤ 36 * ∏ p ∈ F, p ^ 2

/-- Case (II) of Ford (1998, Theorem 6) (`3 ^ 3 ∣ n`): every set `S` of natural numbers closed
under adjoining primes of the form `6 * ∏ q ∈ T, q + 1` or `18 * ∏ q ∈ T, q + 1` (for finite
`T ⊆ S`) contains a finite subset `F` with `10 ^ (10 ^ 10) ≤ 108 * ∏ p ∈ F, p ^ 2`. -/
def H2 : Prop :=
  ∀ S : Set ℕ,
    (∀ T : Finset ℕ, (∀ q ∈ T, q ∈ S) →
      (6 * ∏ q ∈ T, q + 1).Prime → 6 * ∏ q ∈ T, q + 1 ∈ S) →
    (∀ T : Finset ℕ, (∀ q ∈ T, q ∈ S) →
      (18 * ∏ q ∈ T, q + 1).Prime → 18 * ∏ q ∈ T, q + 1 ∈ S) →
    ∃ F : Finset ℕ, (∀ p ∈ F, p ∈ S) ∧ 10 ^ (10 ^ 10) ≤ 108 * ∏ p ∈ F, p ^ 2

theorem main : H1 → H2 → type_of% @CarmichaelTotient.carchimaelTotient_bound := by
  intro h1 h2 n hn hn'
  by_contra hnc
  have h4 := four_dvd_of_not_carmichael hn hnc
  have h9 := nine_dvd_of_not_carmichael hn hnc
  set S : Set ℕ := {p : ℕ | p.Prime ∧ 3 < p ∧ p ^ 2 ∣ n}
  by_cases h27 : 27 ∣ n
  · obtain ⟨F, hFS, hbound⟩ := h2 S
      (fun T hT hP => closed_6 hn hnc T hT hP)
      (fun T hT hP => case2_closed_18 hn hnc h27 T hT hP)
    have hdvd : 108 * ∏ p ∈ F, p ^ 2 ∣ n := dvd_108_mul_prod_sq h4 h27 hFS
    have hle : 108 * ∏ p ∈ F, p ^ 2 ≤ n := Nat.le_of_dvd hn hdvd
    exact absurd (lt_of_le_of_lt (le_trans hbound hle) hn') (lt_irrefl _)
  · obtain ⟨F, hFS, hbound⟩ := h1 S
      (fun T hT hP => closed_6 hn hnc T hT hP)
      (fun T hT hP => case1_closed_12 hn hnc h27 T hT hP)
    have hdvd : 36 * ∏ p ∈ F, p ^ 2 ∣ n := dvd_36_mul_prod_sq h4 h9 hFS
    have hle : 36 * ∏ p ∈ F, p ^ 2 ≤ n := Nat.le_of_dvd hn hdvd
    exact absurd (lt_of_le_of_lt (le_trans hbound hle) hn') (lt_irrefl _)

end OMA.R_CarmichaelTotient_carchimaelTotient_bound_R1
