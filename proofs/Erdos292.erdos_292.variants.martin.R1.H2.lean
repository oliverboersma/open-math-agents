import OMAReductions.R_Erdos292_erdos_292_variants_martin_R1
import Mathlib

/-! Martin's lower bound for the complement of the set A of largest denominators of Egyptian
fractions for 1.

If p is a prime with m * m! < p then m * p is not in A: in a representation of 1 with largest
denominator m * p, the terms with denominator divisible by p add up to a / (p * m!) with
0 < a <= m * m! < p, while the other terms add up to a fraction whose denominator is prime to
p, so the total cannot be 1.

With M about (log x) ^ (1 / 4), the products m * p with m <= M and p a prime in
(M * M!, x / m] are distinct, and Chebyshev's bound pi(n) log n >= n log 2 - log (n + 1)
gives at least (log 2 / 8) x log log x / log x of them once x >= 186 ^ 4. -/

open Finset Filter

namespace Martin292

lemma not_mem_A {m p : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (hlt : m * m.factorial < p) :
    m * p ∉ Erdos292.A := by
  rintro ⟨S, hS, hnS, hsum⟩
  classical
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hf0 : ((m.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun k => p ∣ k) (fun k => (1 : ℚ) / k)
  rw [hsum] at hsplit
  have hDpos : 0 < ∏ k ∈ S.filter (fun k => ¬ p ∣ k), k :=
    Finset.prod_pos (fun k hk => (Finset.mem_Icc.mp (hS (Finset.mem_filter.mp hk).1)).1)
  have hpD : ¬ p ∣ ∏ k ∈ S.filter (fun k => ¬ p ∣ k), k := by
    intro h
    obtain ⟨k, hk, hpk⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
    exact (Finset.mem_filter.mp hk).2 hpk
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = ∏ k ∈ S.filter (fun k => ¬ p ∣ k), k := ⟨_, rfl⟩
  rw [← hDdef] at hDpos hpD
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have h0 : ∑ k ∈ S.filter (fun k => ¬ p ∣ k), (1 : ℚ) / k =
      ((∑ k ∈ S.filter (fun k => ¬ p ∣ k), D / k : ℕ) : ℚ) / D := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (hS (Finset.mem_filter.mp hk).1)).1
    have hkD : k ∣ D := by
      rw [hDdef]
      exact Finset.dvd_prod_of_mem _ hk
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [Nat.cast_div hkD hk0]
    field_simp
  have hmem : ∀ k ∈ S.filter (fun k => p ∣ k), ∃ j, k = p * j ∧ 1 ≤ j ∧ j ≤ m := by
    intro k hk
    obtain ⟨hkS, j, rfl⟩ := Finset.mem_filter.mp hk
    have hk' := Finset.mem_Icc.mp (hS hkS)
    refine ⟨j, rfl, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, mul_zero] at hk'
        omega
      · exact h
    · have h2 : p * j ≤ p * m := by
        rw [mul_comm p m]
        exact hk'.2
      exact Nat.le_of_mul_le_mul_left h2 hp.pos
  have h1 : ∑ k ∈ S.filter (fun k => p ∣ k), (1 : ℚ) / k =
      ((∑ k ∈ S.filter (fun k => p ∣ k), m.factorial / (k / p) : ℕ) : ℚ) /
        (p * m.factorial) := by
    rw [Nat.cast_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨j, rfl, hj1, hjm⟩ := hmem k hk
    have hjdvd : j ∣ m.factorial := Nat.dvd_factorial hj1 hjm
    have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    rw [Nat.mul_div_cancel_left j hp.pos, Nat.cast_div hjdvd hj0]
    push_cast
    field_simp
  obtain ⟨a, hadef⟩ : ∃ a : ℕ, a = ∑ k ∈ S.filter (fun k => p ∣ k), m.factorial / (k / p) :=
    ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ, E = ∑ k ∈ S.filter (fun k => ¬ p ∣ k), D / k := ⟨_, rfl⟩
  have hapos : 0 < a := by
    have hn_mem : m * p ∈ S.filter (fun k => p ∣ k) :=
      Finset.mem_filter.mpr ⟨hnS, Dvd.intro_left m rfl⟩
    have hterm : 1 ≤ m.factorial / (m * p / p) := by
      rw [Nat.mul_div_cancel m hp.pos]
      exact Nat.div_pos (Nat.self_le_factorial m) (by omega)
    have hle : m.factorial / (m * p / p) ≤ a := by
      rw [hadef]
      exact Finset.single_le_sum (f := fun k => m.factorial / (k / p))
        (fun k _ => Nat.zero_le _) hn_mem
    omega
  have hale : a ≤ m * m.factorial := by
    have hsub : S.filter (fun k => p ∣ k) ⊆ (Finset.Icc 1 m).image (fun j => p * j) := by
      intro k hk
      obtain ⟨j, rfl, hj1, hjm⟩ := hmem k hk
      exact Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj1, hjm⟩, rfl⟩
    have hcard : (S.filter (fun k => p ∣ k)).card ≤ m := by
      calc (S.filter (fun k => p ∣ k)).card
          ≤ ((Finset.Icc 1 m).image (fun j => p * j)).card := Finset.card_le_card hsub
        _ ≤ (Finset.Icc 1 m).card := Finset.card_image_le
        _ = m := by simp
    calc a ≤ ∑ _k ∈ S.filter (fun k => p ∣ k), m.factorial := by
          rw [hadef]
          exact Finset.sum_le_sum (fun k _ => Nat.div_le_self _ _)
      _ = (S.filter (fun k => p ∣ k)).card * m.factorial := by simp
      _ ≤ m * m.factorial := Nat.mul_le_mul_right _ hcard
  rw [h1, h0, ← hadef, ← hEdef] at hsplit
  have heq : (a : ℚ) * D + E * (p * m.factorial) = p * m.factorial * D := by
    field_simp at hsplit
    linarith
  have heqN : a * D + E * (p * m.factorial) = p * m.factorial * D := by exact_mod_cast heq
  have hdvd : p ∣ a * D := by
    have h2 : p ∣ p * m.factorial * D := Dvd.intro (m.factorial * D) (by ring)
    have h3 : p ∣ E * (p * m.factorial) := Dvd.intro (E * m.factorial) (by ring)
    have h4 : a * D = p * m.factorial * D - E * (p * m.factorial) := by omega
    rw [h4]
    exact Nat.dvd_sub h2 h3
  rcases hp.dvd_mul.mp hdvd with h | h
  · exact absurd (Nat.le_of_dvd hapos h) (by omega)
  · exact hpD h


/-- The integers `m * p` with `m ≤ M` and `p` a prime in `(M * M!, x / m]` are distinct
elements of the complement of `A` in `[1, x]`. -/
lemma sum_le_ncard (x M : ℕ) :
    ∑ m ∈ Finset.Icc 1 M, (Nat.primeCounting (x / m) - M * M.factorial) ≤
      (Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = M * M.factorial := ⟨_, rfl⟩
  rw [← hQ]
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Finset ℕ, ∀ m, T m =
      ((Nat.primesLE (x / m)).filter (fun p => Q < p)).image (fun p => m * p) := ⟨_, fun _ => rfl⟩
  have hMQ : M ≤ Q := by
    rw [hQ]
    exact Nat.le_mul_of_pos_right M (Nat.factorial_pos M)
  have hmemT : ∀ m a, a ∈ T m → ∃ p, p.Prime ∧ p ≤ x / m ∧ Q < p ∧ a = m * p := by
    intro m a ha
    rw [hT, Finset.mem_image] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    rw [Finset.mem_filter, Nat.mem_primesLE] at hp
    exact ⟨p, hp.1.2, hp.1.1, hp.2, rfl⟩
  have hsub : (((Finset.Icc 1 M).biUnion T : Finset ℕ) : Set ℕ) ⊆
      Erdos292.Aᶜ ∩ Set.Icc 1 x := by
    intro a ha
    rw [Finset.mem_coe, Finset.mem_biUnion] at ha
    obtain ⟨m, hm, haT⟩ := ha
    obtain ⟨p, hp, hpx, hQp, rfl⟩ := hmemT m a haT
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    refine ⟨?_, ?_, ?_⟩
    · apply not_mem_A hp hm1
      have h1 : m * m.factorial ≤ M * M.factorial :=
        Nat.mul_le_mul hmM (Nat.factorial_le hmM)
      omega
    · exact Nat.mul_pos hm1 hp.pos
    · exact (Nat.mul_le_mul_left m hpx).trans (Nat.mul_div_le x m)
  have hdisj : ∀ m ∈ Finset.Icc 1 M, ∀ m' ∈ Finset.Icc 1 M, m ≠ m' → Disjoint (T m) (T m') := by
    intro m hm m' hm' hne
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨p, hp, -, hQp, rfl⟩ := hmemT m a ha
    obtain ⟨p', hp', -, hQp', heq⟩ := hmemT m' _ ha'
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hm1', hmM'⟩ := Finset.mem_Icc.mp hm'
    have hdvd : p ∣ m' * p' := Dvd.intro_left m heq
    rcases hp.dvd_mul.mp hdvd with h | h
    · have := Nat.le_of_dvd (by omega) h
      omega
    · have hpp : p = p' := (Nat.prime_dvd_prime_iff_eq hp hp').mp h
      subst hpp
      exact hne (Nat.eq_of_mul_eq_mul_right hp.pos heq)
  have hcardT : ∀ m ∈ Finset.Icc 1 M, Nat.primeCounting (x / m) - Q ≤ (T m).card := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    rw [hT, Finset.card_image_of_injective _ (mul_right_injective₀ (by omega : m ≠ 0))]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := Nat.primesLE (x / m)) (fun p => Q < p)
    have hsmall : ((Nat.primesLE (x / m)).filter (fun p => ¬ Q < p)).card ≤ Q := by
      have hsub2 : (Nat.primesLE (x / m)).filter (fun p => ¬ Q < p) ⊆ Finset.Icc 1 Q := by
        intro p hp
        rw [Finset.mem_filter, Nat.mem_primesLE] at hp
        exact Finset.mem_Icc.mpr ⟨hp.1.2.pos, not_lt.mp hp.2⟩
      simpa using Finset.card_le_card hsub2
    rw [Nat.primesLE_card_eq_primeCounting] at hsplit
    omega
  calc ∑ m ∈ Finset.Icc 1 M, (Nat.primeCounting (x / m) - Q)
      ≤ ∑ m ∈ Finset.Icc 1 M, (T m).card := Finset.sum_le_sum hcardT
    _ = ((Finset.Icc 1 M).biUnion T).card := (Finset.card_biUnion hdisj).symm
    _ = (((Finset.Icc 1 M).biUnion T : Finset ℕ) : Set ℕ).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ (Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard :=
        Set.ncard_le_ncard hsub ((Set.finite_Icc 1 x).inter_of_right _)

/-- Chebyshev's lower bound in the form used below. -/
lemma primeCounting_mul_log_ge {n x : ℕ} (hn : 1 ≤ n) (hnx : n ≤ x) :
    (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) ≤ (Nat.primeCounting n : ℝ) * Real.log x := by
  have h1 := Chebyshev.psi_ge n
  have h2 := Chebyshev.psi_le_primeCounting_mul_log n
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : Real.log (n : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hnx)
  have h4 : (Nat.primeCounting n : ℝ) * Real.log n ≤ (Nat.primeCounting n : ℝ) * Real.log x :=
    mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
  linarith


/-- Summing Chebyshev's bound over `m ≤ M`. -/
lemma sum_primeCounting_ge {x M : ℕ} (hM : M ≤ x) :
    (x : ℝ) * Real.log 2 * Real.log ((M : ℝ) + 1) -
        M * (Real.log 2 + Real.log ((x : ℝ) + 1)) ≤
      (∑ m ∈ Finset.Icc 1 M, (Nat.primeCounting (x / m) : ℝ)) * Real.log x := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      (x : ℝ) * Real.log 2 * (1 / (m : ℝ)) - (Real.log 2 + Real.log ((x : ℝ) + 1)) ≤
        (Nat.primeCounting (x / m) : ℝ) * Real.log x := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    have hmx : m ≤ x := hmM.trans hM
    have hn1 : 1 ≤ x / m := Nat.div_pos hmx (by omega)
    have hnx : x / m ≤ x := Nat.div_le_self x m
    have h := primeCounting_mul_log_ge hn1 hnx
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hdm : m * (x / m) + x % m = x := Nat.div_add_mod x m
    have hmod : x % m < m := Nat.mod_lt x (by omega)
    have hreal : (x : ℝ) < m * ((x / m : ℕ) : ℝ) + m := by
      have h' : x < m * (x / m) + m := by omega
      exact_mod_cast h'
    have hdiv : (x : ℝ) * (1 / (m : ℝ)) - 1 ≤ ((x / m : ℕ) : ℝ) := by
      rw [mul_one_div, sub_le_iff_le_add, div_le_iff₀ hmpos]
      nlinarith
    have hlogle : Real.log (((x / m : ℕ) : ℝ) + 1) ≤ Real.log ((x : ℝ) + 1) := by
      apply Real.log_le_log (by positivity)
      have h' : ((x / m : ℕ) : ℝ) ≤ x := by exact_mod_cast hnx
      linarith
    have hmul : ((x : ℝ) * (1 / (m : ℝ)) - 1) * Real.log 2 ≤ ((x / m : ℕ) : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hdiv hlog2
    have hexp : (x : ℝ) * Real.log 2 * (1 / (m : ℝ)) - Real.log 2 =
        ((x : ℝ) * (1 / (m : ℝ)) - 1) * Real.log 2 := by ring
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, ← Finset.sum_mul,
    Nat.card_Icc, nsmul_eq_mul] at hsum
  have hharm : Real.log ((M : ℝ) + 1) ≤ ∑ m ∈ Finset.Icc 1 M, (1 / (m : ℝ)) := by
    have h := log_add_one_le_harmonic M
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa [one_div] using h
  have hxnn : (0 : ℝ) ≤ (x : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg _) hlog2
  have hmul2 := mul_le_mul_of_nonneg_left hharm hxnn
  have hcast : ((M + 1 - 1 : ℕ) : ℝ) = M := by simp
  rw [hcast] at hsum
  linarith

/-- The choice of the cut-off `M`, about `(log x) ^ (1 / 4)`. -/
lemma nat_facts {x : ℕ} (hx : 2 ≤ x) :
    ∃ M : ℕ, 1 ≤ M ∧ M ≤ x ∧ (M * (M * M.factorial)) ^ 2 ≤ x ∧ x < 2 ^ ((M + 1) ^ 4) := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = Nat.log 2 x := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by
    rw [hL]
    exact Nat.log_pos (by norm_num) hx
  have h2L : 2 ^ L ≤ x := by
    rw [hL]
    exact Nat.pow_log_le_self 2 (by omega)
  have hxL : x < 2 ^ (L + 1) := by
    rw [hL]
    exact Nat.lt_pow_succ_log_self (by norm_num) x
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = Nat.sqrt L := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = Nat.sqrt s := ⟨_, rfl⟩
  have hs1 : s * s ≤ L := by
    rw [hs]
    exact Nat.sqrt_le L
  have hs2 : L < (s + 1) * (s + 1) := by
    rw [hs]
    exact Nat.lt_succ_sqrt L
  have hM1 : M * M ≤ s := by
    rw [hM]
    exact Nat.sqrt_le s
  have hM2 : s < (M + 1) * (M + 1) := by
    rw [hM]
    exact Nat.lt_succ_sqrt s
  have hspos : 1 ≤ s := by
    by_contra h
    have h0 : s = 0 := by omega
    rw [h0] at hs2
    omega
  have hMpos : 1 ≤ M := by
    by_contra h
    have h0 : M = 0 := by omega
    rw [h0] at hM2
    omega
  have hM4 : M ^ 4 ≤ L := by
    calc M ^ 4 = (M * M) * (M * M) := by ring
      _ ≤ s * s := Nat.mul_le_mul hM1 hM1
      _ ≤ L := hs1
  have hL4 : L + 1 ≤ (M + 1) ^ 4 := by
    have h' : s + 1 ≤ (M + 1) * (M + 1) := hM2
    calc L + 1 ≤ (s + 1) * (s + 1) := hs2
      _ ≤ ((M + 1) * (M + 1)) * ((M + 1) * (M + 1)) := Nat.mul_le_mul h' h'
      _ = (M + 1) ^ 4 := by ring
  refine ⟨M, hMpos, ?_, ?_, ?_⟩
  · calc M ≤ M ^ 4 := Nat.le_self_pow (by norm_num) M
      _ ≤ L := hM4
      _ ≤ x := by
        rw [hL]
        exact Nat.log_le_self 2 x
  · have h2M4 : 2 ^ (M ^ 4) ≤ x := (Nat.pow_le_pow_right (by norm_num) hM4).trans h2L
    refine le_trans ?_ h2M4
    rcases Nat.lt_or_ge M 2 with hlt | hge
    · have hM1' : M = 1 := by omega
      rw [hM1']
      norm_num
    · have hfac : M.factorial ≤ M ^ M := Nat.factorial_le_pow M
      have hlt2 : M ≤ 2 ^ M := Nat.lt_two_pow_self.le
      have h1 : 4 ≤ M * M := Nat.mul_le_mul hge hge
      have h2 : 2 * M ≤ M * M := Nat.mul_le_mul_right M hge
      have h3 : 4 * (M * M) ≤ (M * M) * (M * M) := Nat.mul_le_mul_right _ h1
      have hexp : M * (2 * (M + 2)) ≤ M ^ 4 := by
        have e1 : M * (2 * (M + 2)) = 2 * (M * M) + 4 * M := by ring
        have e2 : M ^ 4 = (M * M) * (M * M) := by ring
        rw [e1, e2]
        omega
      calc (M * (M * M.factorial)) ^ 2 ≤ (M * (M * M ^ M)) ^ 2 :=
            Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfac)) 2
        _ = M ^ (2 * (M + 2)) := by ring
        _ ≤ (2 ^ M) ^ (2 * (M + 2)) := Nat.pow_le_pow_left hlt2 _
        _ = 2 ^ (M * (2 * (M + 2))) := by rw [← pow_mul]
        _ ≤ 2 ^ (M ^ 4) := Nat.pow_le_pow_right (by norm_num) hexp
  · exact lt_of_lt_of_le hxL (Nat.pow_le_pow_right (by norm_num) hL4)


/-- Martin's lower bound: the complement of `A` has at least `c x log log x / log x` elements
up to `x`. -/
theorem martin_lower :
    (fun x : ℕ ↦ Real.log (Real.log x) / Real.log x) =O[atTop]
      (fun x : ℕ ↦ ((Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard : ℝ) / x) := by
  apply Asymptotics.IsBigO.of_bound (8 / Real.log 2)
  filter_upwards [Filter.eventually_ge_atTop (186 ^ 4)] with x hx
  have hl2a : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hl2b : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog2 : 0 < Real.log 2 := by linarith
  have hx2 : 2 ≤ x := le_trans (by norm_num) hx
  obtain ⟨M, hM1, hMx, hE, hxM⟩ := nat_facts hx2
  have hxR : (186 : ℝ) ^ 4 ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hxR
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = Real.sqrt (Real.sqrt x) := ⟨_, rfl⟩
  have hsq1 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have hsq2 : y ^ 2 = Real.sqrt x := by
    rw [hydef]
    exact Real.sq_sqrt (Real.sqrt_nonneg _)
  have hy4 : y ^ 4 = (x : ℝ) := by
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (x : ℝ) := by rw [hsq2, hsq1]
  have hy0 : 0 ≤ y := by
    rw [hydef]
    exact Real.sqrt_nonneg _
  have hy186 : 186 ≤ y := by
    by_contra h
    have h' : y < 186 := lt_of_not_ge h
    have h4 : y ^ 4 < 186 ^ 4 := pow_lt_pow_left₀ h' hy0 (by norm_num)
    linarith
  have hypos : 0 < y := by linarith
  have hlogx : Real.log x = 4 * Real.log y := by
    rw [← hy4, Real.log_pow]
    norm_num
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos hypos
  have hlogx_le : Real.log x ≤ 4 * y := by linarith
  have hlogx_ge : 16 ≤ Real.log x := by
    have h1 : Real.log ((2 : ℝ) ^ 28) ≤ Real.log x :=
      Real.log_le_log (by positivity) (le_trans (by norm_num) hxR)
    rw [Real.log_pow] at h1
    norm_num at h1
    linarith
  have hlogxpos : 0 < Real.log x := by linarith
  have hLL1 : 1 ≤ Real.log (Real.log x) := by
    have h1 : Real.log ((2 : ℝ) ^ 4) ≤ Real.log (Real.log x) :=
      Real.log_le_log (by positivity) (by norm_num; linarith)
    rw [Real.log_pow] at h1
    norm_num at h1
    linarith
  have hLLle : Real.log (Real.log x) ≤ 4 * Real.log ((M : ℝ) + 1) := by
    have hxlt : (x : ℝ) < (2 : ℝ) ^ ((M + 1) ^ 4) := by exact_mod_cast hxM
    have h1 : Real.log x < Real.log ((2 : ℝ) ^ ((M + 1) ^ 4)) := Real.log_lt_log hxpos hxlt
    rw [Real.log_pow] at h1
    have h2 : Real.log x ≤ ((M : ℝ) + 1) ^ 4 := by
      have h3 : (((M + 1) ^ 4 : ℕ) : ℝ) * Real.log 2 ≤ (((M + 1) ^ 4 : ℕ) : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      push_cast at h3 h1
      linarith
    have h4 := Real.log_le_log hlogxpos h2
    rw [Real.log_pow] at h4
    norm_num at h4
    exact h4
  have hcnt := sum_le_ncard x M
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = (Erdos292.Aᶜ ∩ Set.Icc 1 x).ncard := ⟨_, rfl⟩
  rw [← hNdef] at hcnt ⊢
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ, Q = M * M.factorial := ⟨_, rfl⟩
  rw [← hQdef] at hcnt hE
  have hQpos : 0 < Q := by
    rw [hQdef]
    exact Nat.mul_pos hM1 (Nat.factorial_pos M)
  have hcntR : (∑ m ∈ Finset.Icc 1 M, (Nat.primeCounting (x / m) : ℝ)) - (M : ℝ) * Q ≤ N := by
    have h1 : (∑ m ∈ Finset.Icc 1 M, ((Nat.primeCounting (x / m) : ℝ) - Q)) ≤
        ((∑ m ∈ Finset.Icc 1 M, (Nat.primeCounting (x / m) - Q) : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_le_sum
      intro m _
      have h' : Nat.primeCounting (x / m) ≤ (Nat.primeCounting (x / m) - Q) + Q := by omega
      have h'' : (Nat.primeCounting (x / m) : ℝ) ≤
          ((Nat.primeCounting (x / m) - Q : ℕ) : ℝ) + Q := by exact_mod_cast h'
      linarith
    have h2 : ((∑ m ∈ Finset.Icc 1 M, (Nat.primeCounting (x / m) - Q) : ℕ) : ℝ) ≤ N := by
      exact_mod_cast hcnt
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at h1
    have hcast : ((M + 1 - 1 : ℕ) : ℝ) = M := by simp
    rw [hcast] at h1
    linarith
  have hsum := sum_primeCounting_ge hMx
  have hER : (M : ℝ) * Q ≤ y ^ 2 := by
    by_contra h
    have h' : y ^ 2 < (M : ℝ) * Q := lt_of_not_ge h
    have h4 : (y ^ 2) ^ 2 < ((M : ℝ) * Q) ^ 2 := pow_lt_pow_left₀ h' (by positivity) (by norm_num)
    have h5 : ((M : ℝ) * Q) ^ 2 ≤ x := by exact_mod_cast hE
    have h6 : (y ^ 2) ^ 2 = (x : ℝ) := by rw [hsq2, hsq1]
    linarith
  have hME : (M : ℝ) ≤ (M : ℝ) * Q := by
    have h' : M ≤ M * Q := Nat.le_mul_of_pos_right M hQpos
    exact_mod_cast h'
  have hlogx1 : Real.log ((x : ℝ) + 1) ≤ 2 * Real.log x := by
    have h1 : (x : ℝ) + 1 ≤ (x : ℝ) ^ 2 := by nlinarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    norm_num at h2
    exact h2
  have hiv1 : (M : ℝ) * (Real.log 2 + Real.log ((x : ℝ) + 1)) ≤
      (M : ℝ) * Q * (1 + 2 * Real.log x) := by
    have h1 : Real.log 2 + Real.log ((x : ℝ) + 1) ≤ 1 + 2 * Real.log x := by linarith
    calc (M : ℝ) * (Real.log 2 + Real.log ((x : ℝ) + 1))
        ≤ (M : ℝ) * (1 + 2 * Real.log x) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
      _ ≤ (M : ℝ) * Q * (1 + 2 * Real.log x) := mul_le_mul_of_nonneg_right hME (by linarith)
  have hiv2 : (M : ℝ) * Q * (1 + 3 * Real.log x) ≤ y ^ 2 * (1 + 12 * y) := by
    calc (M : ℝ) * Q * (1 + 3 * Real.log x) ≤ y ^ 2 * (1 + 3 * Real.log x) :=
          mul_le_mul_of_nonneg_right hER (by linarith)
      _ ≤ y ^ 2 * (1 + 12 * y) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hiv3 : y ^ 2 * (1 + 12 * y) ≤ 13 * y ^ 3 := by
    have h1 : y ^ 2 * 1 ≤ y ^ 2 * y := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  have hv : 13 * y ^ 3 ≤ Real.log 2 / 8 * x * Real.log (Real.log x) := by
    rw [← hy4]
    have h0 : Real.log 2 / 8 * 186 ≤ Real.log 2 / 8 * y :=
      mul_le_mul_of_nonneg_left hy186 (by positivity)
    have h1 : (13 : ℝ) ≤ Real.log 2 / 8 * y := by linarith
    have h2 : 13 * y ^ 3 ≤ (Real.log 2 / 8 * y) * y ^ 3 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : Real.log 2 / 8 * y ^ 4 * 1 ≤ Real.log 2 / 8 * y ^ 4 * Real.log (Real.log (y ^ 4)) := by
      rw [hy4]
      exact mul_le_mul_of_nonneg_left hLL1 (by positivity)
    nlinarith
  have hiii : (x : ℝ) * Real.log 2 * (Real.log (Real.log x) / 4) ≤
      (x : ℝ) * Real.log 2 * Real.log ((M : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hi : ((∑ m ∈ Finset.Icc 1 M, (Nat.primeCounting (x / m) : ℝ)) - (M : ℝ) * Q) *
      Real.log x ≤ (N : ℝ) * Real.log x := mul_le_mul_of_nonneg_right hcntR hlogxpos.le
  have key : Real.log 2 / 8 * x * Real.log (Real.log x) ≤ (N : ℝ) * Real.log x := by
    linarith
  have hLL0 : 0 ≤ Real.log (Real.log x) := by linarith
  rw [Real.norm_of_nonneg (div_nonneg hLL0 hlogxpos.le),
    Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hxpos.le), div_le_iff₀ hlogxpos]
  have hrw : 8 / Real.log 2 * ((N : ℝ) / x) * Real.log x =
      8 * ((N : ℝ) * Real.log x) / (Real.log 2 * x) := by
    field_simp
  rw [hrw, le_div_iff₀ (by positivity)]
  linarith

end Martin292

theorem OMA.solution : OMA.R_Erdos292_erdos_292_variants_martin_R1.H2 := by
  unfold OMA.R_Erdos292_erdos_292_variants_martin_R1.H2
  exact Martin292.martin_lower
