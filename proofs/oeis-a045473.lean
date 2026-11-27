import OMAStatements.S_oeis_a045473
import Mathlib

open OMA.S_oeis_a045473 Polynomial UniqueFactorizationMonoid
theorem a045473_shift_apply {K : Type*} [CommRing K] (t : K) (x : K[X]) :
    algEquivAevalXAddC t x = x.comp (X + C t) := by
  rw [algEquivAevalXAddC_apply, comp_eq_aeval]

theorem a045473_shift_natDegree {K : Type*} [CommRing K] [IsDomain K] (t : K) (x : K[X]) :
    (algEquivAevalXAddC t x).natDegree = x.natDegree := by
  rw [a045473_shift_apply, natDegree_comp, natDegree_X_add_C, mul_one]

theorem a045473_shift_monic {K : Type*} [CommRing K] (t : K) (x : K[X]) (hx : x.Monic) :
    (algEquivAevalXAddC t x).Monic := by
  rw [a045473_shift_apply]; exact hx.comp_X_add_C t

theorem a045473_cyc (p : ℕ) :
    algEquivAevalXAddC (1 : ZMod p) (cyclotomic 7 (ZMod p)) = shiftedQuotient p := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [a045473_shift_apply, cyclotomic_prime]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, add_comp, pow_comp, X_comp,
    map_one, zero_add, pow_zero, one_comp, pow_one, shiftedQuotient]
  have h7 : (C 7 : (ZMod p)[X]) = 7 := rfl
  have h21 : (C 21 : (ZMod p)[X]) = 21 := rfl
  have h35 : (C 35 : (ZMod p)[X]) = 35 := rfl
  rw [h7, h21, h35]
  ring

theorem a045473_mod (p : ℕ) [hp : Fact p.Prime] (hp7 : p ≠ 7) :
    p % 7 = 6 ↔ (p : ZMod 7) ^ 2 = 1 ∧ (p : ZMod 7) ≠ 1 := by
  have h7 : (p : ZMod 7) = ((p % 7 : ℕ) : ZMod 7) := (ZMod.natCast_mod p 7).symm
  have h0 : p % 7 ≠ 0 := by
    intro h
    have hd : 7 ∣ p := Nat.dvd_of_mod_eq_zero h
    exact hp7 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp.out).mp hd).symm
  rw [h7]
  have hlt : p % 7 < 7 := Nat.mod_lt _ (by norm_num)
  generalize p % 7 = r at *
  interval_cases r <;> simp_all <;> decide

theorem a045473_main : ∀ (p : ℕ) [Fact p.Prime],
    p % 7 = 6 ↔
      ∃ f g h : Polynomial (ZMod p),
        f.Monic ∧ g.Monic ∧ h.Monic ∧
        Irreducible f ∧ Irreducible g ∧ Irreducible h ∧
        f.natDegree = 2 ∧ g.natDegree = 2 ∧ h.natDegree = 2 ∧
        f * g * h = shiftedQuotient p := by
  intro p hp
  classical
  have hK : Fintype.card (ZMod p) = p ^ 1 := by simp [ZMod.card]
  by_cases hp7 : p = 7
  · subst hp7
    have hsq : shiftedQuotient 7 = X ^ 6 := by
      have h7 : (C 7 : (ZMod 7)[X]) = 0 := by rw [show (7 : ZMod 7) = 0 from rfl, map_zero]
      have h21 : (C 21 : (ZMod 7)[X]) = 0 := by rw [show (21 : ZMod 7) = 0 from rfl, map_zero]
      have h35 : (C 35 : (ZMod 7)[X]) = 0 := by rw [show (35 : ZMod 7) = 0 from rfl, map_zero]
      simp only [shiftedQuotient, h7, h21, h35, zero_mul, add_zero]
    constructor
    · intro h; norm_num at h
    · rintro ⟨f, g, h, -, -, -, hf, -, -, hfd, -, -, H⟩
      rw [hsq] at H
      have hdvd : f ∣ X ^ 6 := ⟨g * h, by rw [← H]; ring⟩
      have hX : f ∣ X := hf.prime.dvd_of_dvd_pow hdvd
      have := natDegree_le_of_dvd hX X_ne_zero
      rw [natDegree_X, hfd] at this
      norm_num at this
  have hcop : p.Coprime 7 := (Nat.coprime_primes hp.out (by norm_num)).mpr hp7
  have hval : ∀ (u : (ZMod 7)ˣ), u = ZMod.unitOfCoprime (p ^ 1) (hcop.pow_left 1) →
      (orderOf u = 2 ↔ (p : ZMod 7) ^ 2 = 1 ∧ (p : ZMod 7) ≠ 1) := by
    intro u hu
    constructor
    · intro ho
      have h1 : u ^ 2 = 1 := ho ▸ pow_orderOf_eq_one u
      have h2 : u ≠ 1 := by
        intro h; rw [h, orderOf_one] at ho; norm_num at ho
      refine ⟨?_, ?_⟩
      · have := congrArg Units.val h1
        simpa [hu] using this
      · intro h; apply h2; rw [hu]; ext; simpa using h
    · rintro ⟨h1, h2⟩
      apply orderOf_eq_prime
      · rw [hu]; ext; simpa using h1
      · intro h; apply h2; have := congrArg Units.val h; simpa [hu] using this
  rw [a045473_mod p hp7, ← hval _ rfl]
  set u := ZMod.unitOfCoprime (p ^ 1) (hcop.pow_left 1) with hu
  have hcyc := a045473_cyc p
  constructor
  · intro hord
    set S := normalizedFactors (cyclotomic 7 (ZMod p)) with hS
    have hdeg : ∀ P ∈ S, P.natDegree = 2 := fun P hP =>
      (natDegree_of_mem_normalizedFactors_cyclotomic hK hcop hP).trans hord
    have hprod : S.prod = cyclotomic 7 (ZMod p) := by
      have := leadingCoeff_mul_prod_normalizedFactors (cyclotomic 7 (ZMod p))
      rwa [(cyclotomic.monic 7 (ZMod p)).leadingCoeff, map_one, one_mul] at this
    have hmem : ∀ P ∈ S, Irreducible P ∧ P.Monic ∧ P ∣ cyclotomic 7 (ZMod p) := fun P hP =>
      (Polynomial.mem_normalizedFactors_iff (cyclotomic_ne_zero 7 (ZMod p))).mp hP
    have hcard : S.card = 3 := by
      have h1 := congrArg natDegree hprod
      rw [natDegree_multiset_prod_of_monic _ (fun P hP => (hmem P hP).2.1),
        natDegree_cyclotomic, Multiset.map_congr rfl hdeg] at h1
      simp at h1
      norm_num [Nat.totient_prime (show Nat.Prime 7 by norm_num)] at h1
      omega
    obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.mp hcard
    have ha := hmem a (by rw [habc]; simp)
    have hb := hmem b (by rw [habc]; simp)
    have hc := hmem c (by rw [habc]; simp)
    refine ⟨algEquivAevalXAddC (1 : ZMod p) a, algEquivAevalXAddC (1 : ZMod p) b,
      algEquivAevalXAddC (1 : ZMod p) c, a045473_shift_monic _ _ ha.2.1, a045473_shift_monic _ _ hb.2.1,
      a045473_shift_monic _ _ hc.2.1, ha.1.map _, hb.1.map _, hc.1.map _, ?_, ?_, ?_, ?_⟩
    · rw [a045473_shift_natDegree]; exact hdeg a (by rw [habc]; simp)
    · rw [a045473_shift_natDegree]; exact hdeg b (by rw [habc]; simp)
    · rw [a045473_shift_natDegree]; exact hdeg c (by rw [habc]; simp)
    · rw [← hcyc, ← hprod, habc, Multiset.insert_eq_cons, Multiset.insert_eq_cons,
        Multiset.prod_cons, Multiset.prod_cons, Multiset.prod_singleton, map_mul, map_mul,
        mul_assoc]
  · rintro ⟨f, g, h, -, -, -, hf, -, -, hfd, -, -, H⟩
    have hdvd : algEquivAevalXAddC (-1 : ZMod p) f ∣ cyclotomic 7 (ZMod p) := by
      have : algEquivAevalXAddC (-1 : ZMod p) (shiftedQuotient p) = cyclotomic 7 (ZMod p) := by
        rw [← hcyc, ← algEquivAevalXAddC_symm]; exact AlgEquiv.symm_apply_apply _ _
      rw [← this, ← H]
      exact ⟨algEquivAevalXAddC (-1 : ZMod p) (g * h), by rw [← map_mul, ← mul_assoc]⟩
    have hirr : Irreducible (algEquivAevalXAddC (-1 : ZMod p) f) := hf.map _
    have hd := natDegree_of_dvd_cyclotomic_of_irreducible hK hcop hdvd hirr
    rw [a045473_shift_natDegree, hfd] at hd
    exact hd.symm

theorem OMA.solution : type_of% @OMA.S_oeis_a045473.main := a045473_main
