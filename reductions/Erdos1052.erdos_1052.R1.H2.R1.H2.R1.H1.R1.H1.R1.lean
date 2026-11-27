import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H1.R1
-- Splits step H1 (the 223 family) of Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1 in three.  Proving all
-- three H proves the step.
--
-- Notation as in the parent files: n unitary perfect, a = padicValNat 2 n, S = the set of odd primes p
-- with p^2 | n (the kernel), S admissible; a prime of n is SIMPLE if it divides n exactly once.  The 223
-- family is: 16 | a, a not 32 mod 64, 3, 5, 7, 19, 31, 223 | n, no prime of n below 152 other than
-- 2, 3, 5, 7, 19, 31, and the residue clause (some z in S with z = 2 mod 3 divides 2^a + 1).
-- Y = the product over S of (1 + 5/z); Y close to 1 means that the kernel is thin (all z large).
--
-- What is proved here (theorem split223): in the 223 family either a = 0, or a >= 48 and
--   (H1) 607 | n, Y > 5001/5000, and the primes of n below 2100 are 2, 3, 5, 7, 19, 31, 223, 607; or
--   (H2) 607 | n, Y <= 5001/5000, 3967 | n, and the primes of n below 5057 are
--        2, 3, 5, 7, 19, 31, 223, 607, 3967; or
--   (H3) 991 | n and 1783 | n, Y > 2501/2500, and the primes of n below 1899 are
--        2, 3, 5, 7, 19, 31, 223, 991, 1783 (so 607 does not divide n).
-- All other cases are impossible in the family, where a >= 48 (one weight inequality each; node223 needs
-- only a >= 16 and the other five a >= 20):
--   no 607, no 991, no 1783                    node223       (masterT, total 1.99954657)
--   991, no 607, no 1783                       node991       (masterU, total 1.99991507)
--   1783, no 607, no 991                       node1783      (masterU, total 1.99962722)
--   991, 1783, no 607, Y <= 2501/2500, 7927 not simple
--                                              node_pair_out (masterU, smaller leaf constant, 1.99975725)
--   991, 1783, 7927, no 607, Y <= 2501/2500    node_pair_in  (masterU, smaller leaf constant, 1.99998193)
--   607, no 3967, Y <= 5001/5000               node607_thin  (masterU, smaller leaf constant, 1.99997159)
-- Ingredients: the 2-adic count (2^18 divides the product of p + 1 over 3, 5, 7, 19, 31, 223, hence
-- a >= 17 and then a >= 48), the abundancy gaps (S_abund; gap607, gap3967, gap1783), parent tables (T19a,
-- T19y, T223y, T31y, T31c, T607c, T991, T991c, T1783w, T7927w, T8191z, T16381z) and the mod-3 leaf
-- bound of masterU (sumD_one, sumD_two, and sumD_eta, sumD_thin for a thin kernel).
-- The sub-namespaces Erdos1052C7, Erdos1052C9, Erdos1052C11 hold helper theorems taken unchanged from
-- the working files of earlier rounds; Erdos1052C16 holds the new ones.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1

namespace Erdos1052C7

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

-- (1 - sum x) * prod (1 + x) is at most 1 for nonnegative x.
theorem one_sub_sum_mul_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℚ)
    (hx : ∀ i ∈ s, 0 ≤ x i) : (1 - ∑ i ∈ s, x i) * ∏ i ∈ s, (1 + x i) ≤ 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have ih' := ih (fun i hi => hx i (Finset.mem_insert_of_mem hi))
    have hP : 0 ≤ ∏ i ∈ s, (1 + x i) := Finset.prod_nonneg fun i hi => by
      linarith [hx i (Finset.mem_insert_of_mem hi)]
    have hσ : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    nlinarith [mul_nonneg (mul_nonneg hxa (add_nonneg hσ hxa)) hP]

theorem one_le_prod_one_add {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℚ)
    (ha : ∀ i ∈ s, 0 ≤ a i) : 1 ≤ ∏ i ∈ s, (1 + a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb]
    have hab := ha b (Finset.mem_insert_self b s)
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    nlinarith

-- prod (1 + c * a) is at most 1 + c * (prod (1 + a) - 1) for 0 ≤ c ≤ 1 and nonnegative a.
theorem prod_one_add_mul_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℚ) (c : ℚ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + c * a i) ≤ 1 + c * (∏ i ∈ s, (1 + a i) - 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.prod_insert hb]
    have hab := ha b (Finset.mem_insert_self b s)
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have hQ := one_le_prod_one_add s a (fun i hi => ha i (Finset.mem_insert_of_mem hi))
    have h0 : 0 ≤ 1 + c * a b := by nlinarith
    calc (1 + c * a b) * ∏ i ∈ s, (1 + c * a i) ≤ (1 + c * a b) * (1 + c * (∏ i ∈ s, (1 + a i) - 1)) :=
          mul_le_mul_of_nonneg_left ih' h0
      _ ≤ 1 + c * ((1 + a b) * ∏ i ∈ s, (1 + a i) - 1) := by
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hc0 hab) (by linarith : (0 : ℚ) ≤ ∏ i ∈ s, (1 + a i) - 1))
            (by linarith : (0 : ℚ) ≤ 1 - c)]

-- A finite geometric sum with ratio 1/z is at most z/(z-1).
theorem geom_inv_le {z : ℕ} (hz : 2 ≤ z) (J : Finset ℕ) :
    ∑ j ∈ J, (1 / (z : ℚ)) ^ j ≤ (z : ℚ) / ((z : ℚ) - 1) := by
  have hzq : (2 : ℚ) ≤ z := by exact_mod_cast hz
  have hx0 : (0 : ℚ) ≤ 1 / (z : ℚ) := by positivity
  have hx1 : 1 / (z : ℚ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨M, hM⟩ : ∃ M, J ⊆ Finset.range M :=
    ⟨J.sup id + 1, fun j hj => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hj))⟩
  calc ∑ j ∈ J, (1 / (z : ℚ)) ^ j ≤ ∑ j ∈ Finset.range M, (1 / (z : ℚ)) ^ j :=
        Finset.sum_le_sum_of_subset_of_nonneg hM (fun j _ _ => pow_nonneg hx0 j)
    _ ≤ (1 / (z : ℚ)) ^ 0 / (1 - 1 / (z : ℚ)) := by
        rw [Finset.range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one hx0 hx1
    _ = (z : ℚ) / ((z : ℚ) - 1) := by
        have hz0 : (z : ℚ) ≠ 0 := by linarith
        have hz1 : (z : ℚ) - 1 ≠ 0 := by linarith
        field_simp

-- The sum of 1/u over a finite set of positive numbers all of whose primes lie in N.
theorem smooth_recip : ∀ (N : Finset ℕ), (∀ z ∈ N, z.Prime) →
    ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
    ∑ u ∈ U, 1 / (u : ℚ) ≤ ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) := by
  intro N
  induction N using Finset.induction_on with
  | empty =>
    intro _ U hU
    have hsub : U ⊆ {1} := fun u hu => by
      obtain ⟨h0, hr⟩ := hU u hu
      by_contra h1
      have h1' : u ≠ 1 := fun e => h1 (Finset.mem_singleton.mpr e)
      exact absurd (hr _ (Nat.minFac_prime h1') (Nat.minFac_dvd u)) (Finset.notMem_empty _)
    calc ∑ u ∈ U, 1 / (u : ℚ) ≤ ∑ u ∈ ({1} : Finset ℕ), 1 / (u : ℚ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∏ z ∈ (∅ : Finset ℕ), ((z : ℚ) / ((z : ℚ) - 1)) := by simp
  | insert z N0 hzN0 ih =>
    intro hN U hU
    have hzp := hN z (Finset.mem_insert_self z N0)
    have hN0 : ∀ z' ∈ N0, z'.Prime := fun z' h' => hN z' (Finset.mem_insert_of_mem h')
    have hφ : ∀ u ∈ U, u / z ^ u.factorization z ≠ 0 ∧
        ∀ r : ℕ, r.Prime → r ∣ u / z ^ u.factorization z → r ∈ N0 := fun u hu => by
      obtain ⟨h0, hr⟩ := hU u hu
      refine ⟨(Nat.ordCompl_pos z h0).ne', fun r hrp hrd => ?_⟩
      rcases Finset.mem_insert.mp (hr r hrp (hrd.trans (Nat.ordCompl_dvd u z))) with rfl | h
      · exact absurd hrd (Nat.not_dvd_ordCompl hrp h0)
      · exact h
    have hmul : ∀ u : ℕ, z ^ u.factorization z * (u / z ^ u.factorization z) = u := fun u =>
      Nat.ordProj_mul_ordCompl_eq_self u z
    obtain ⟨V, hV⟩ : ∃ V : Finset ℕ, V = U.image (fun u => u / z ^ u.factorization z) := ⟨_, rfl⟩
    have hmaps : ∀ u ∈ U, u / z ^ u.factorization z ∈ V := fun u hu => by
      rw [hV]
      exact Finset.mem_image_of_mem _ hu
    have hz2 : (2 : ℚ) ≤ z := by exact_mod_cast hzp.two_le
    have hzq0 : (0 : ℚ) ≤ (z : ℚ) / ((z : ℚ) - 1) := div_nonneg (by linarith) (by linarith)
    have hfib : ∀ v ∈ V, ∑ u ∈ U.filter (fun u => u / z ^ u.factorization z = v), 1 / (u : ℚ) ≤
        (z : ℚ) / ((z : ℚ) - 1) * (1 / (v : ℚ)) := by
      intro v hv
      have hinj : ∀ u1 ∈ U.filter (fun u => u / z ^ u.factorization z = v),
          ∀ u2 ∈ U.filter (fun u => u / z ^ u.factorization z = v),
          u1.factorization z = u2.factorization z → u1 = u2 := fun u1 h1 u2 h2 he => by
        have e1 := hmul u1
        have e2 := hmul u2
        rw [(Finset.mem_filter.mp h1).2] at e1
        rw [(Finset.mem_filter.mp h2).2, ← he] at e2
        exact e1.symm.trans e2
      have hrew : ∑ u ∈ U.filter (fun u => u / z ^ u.factorization z = v), 1 / (u : ℚ) =
          ∑ j ∈ (U.filter (fun u => u / z ^ u.factorization z = v)).image
              (fun u => u.factorization z), 1 / (v : ℚ) * (1 / (z : ℚ)) ^ j := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun u hu => ?_
        have e1 := hmul u
        rw [(Finset.mem_filter.mp hu).2] at e1
        have e2 : (u : ℚ) = (z : ℚ) ^ u.factorization z * (v : ℚ) := by
          have := congrArg (Nat.cast : ℕ → ℚ) e1
          push_cast at this
          rw [← this]
        rw [e2, one_div_pow, one_div_mul_one_div, mul_comm]
      rw [hrew, ← Finset.mul_sum]
      have hg := geom_inv_le hzp.two_le ((U.filter (fun u => u / z ^ u.factorization z = v)).image
        (fun u => u.factorization z))
      have hv0 : (0 : ℚ) ≤ 1 / (v : ℚ) := by positivity
      calc 1 / (v : ℚ) * ∑ j ∈ (U.filter (fun u => u / z ^ u.factorization z = v)).image
              (fun u => u.factorization z), (1 / (z : ℚ)) ^ j
          ≤ 1 / (v : ℚ) * ((z : ℚ) / ((z : ℚ) - 1)) := mul_le_mul_of_nonneg_left hg hv0
        _ = (z : ℚ) / ((z : ℚ) - 1) * (1 / (v : ℚ)) := by ring
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun u => u / z ^ u.factorization z) (t := V) hmaps]
    refine (Finset.sum_le_sum hfib).trans ?_
    rw [← Finset.mul_sum, Finset.prod_insert hzN0]
    have hV' : ∀ v ∈ V, v ≠ 0 ∧ ∀ r : ℕ, r.Prime → r ∣ v → r ∈ N0 := fun v hv => by
      rw [hV] at hv
      obtain ⟨u0, hu0, rfl⟩ := Finset.mem_image.mp hv
      exact hφ u0 hu0
    exact mul_le_mul_of_nonneg_left (ih hN0 V hV') hzq0

theorem mersenne_small7 {q k : ℕ} (hq : q.Prime) (hk : q + 1 = 2 ^ k) (hlt : q < 131071) :
    q = 3 ∨ q = 7 ∨ q = 31 ∨ q = 127 ∨ q = 8191 := by
  have hk17 : k < 17 := by
    by_contra h
    have : 2 ^ 17 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp at hk <;> subst hk <;> first | omega | (norm_num at hq)

-- The Mersenne leaves: weights at 3, 7, 31, 127, then 8191, then the tail from 131071 on.
theorem mersenne_bound7 (β : ℕ → ℚ) (L : Finset ℕ) (hLp : ∀ q ∈ L, q.Prime)
    (hLm : ∀ q ∈ L, ∃ k, q + 1 = 2 ^ k)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127) :
    ∏ q ∈ L, β q ≤ (β 3 * β 7 * β 31 * β 127) * (4096 / 4095 * (32768 / 32767)) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => q < 8191) β
  have hsmall : ∏ q ∈ L.filter (fun q => q < 8191), β q ≤ β 3 * β 7 * β 31 * β 127 := by
    have hsub : L.filter (fun q => q < 8191) ⊆ ({3, 7, 31, 127} : Finset ℕ) := by
      intro q hq
      obtain ⟨hqL, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨k, hk⟩ := hLm q hqL
      have := mersenne_small (hLp q hqL) hk hlt
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun i hi => (hLβ i (Finset.mem_filter.mp hi).1).1.le) (fun i hi _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact h1.1
      · exact h1.2.1
      · exact h1.2.2.1
      · exact h1.2.2.2)
    have e : ∏ q ∈ ({3, 7, 31, 127} : Finset ℕ), β q = β 3 * β 7 * β 31 * β 127 := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      ring
    rwa [e] at h
  have hmemT : ∀ q ∈ L.filter (fun q => ¬ q < 8191), q ∈ L ∧ 8191 ≤ q := fun q hq => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
    exact ⟨h1, by omega⟩
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not (L.filter (fun q => ¬ q < 8191))
    (fun q => q < 131071) β
  have hmid : ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => q < 131071), β q ≤
      4096 / 4095 := by
    have hsub : (L.filter (fun q => ¬ q < 8191)).filter (fun q => q < 131071) ⊆ {8191} := by
      intro q hq
      obtain ⟨hqL2, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, hge⟩ := hmemT q hqL2
      obtain ⟨k, hk⟩ := hLm q hqL
      have := mersenne_small7 (hLp q hqL) hk hlt
      rw [Finset.mem_singleton]
      omega
    calc ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => q < 131071), β q
        ≤ ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => q < 131071),
            (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
          Finset.prod_le_prod (fun q hq => (hLβ q (hmemT q (Finset.mem_filter.mp hq).1).1).1.le)
            (fun q hq => (hLβ q (hmemT q (Finset.mem_filter.mp hq).1).1).2)
      _ ≤ ∏ q ∈ ({8191} : Finset ℕ), (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
          Finset.prod_le_prod_of_subset_of_one_le hsub
            (fun q hq => by
              have h8 := (hmemT q (Finset.mem_filter.mp hq).1).2
              have h8q : (8191 : ℚ) ≤ q := by exact_mod_cast h8
              exact div_nonneg (by linarith) (by linarith))
            (fun q (hq : q ∈ ({8191} : Finset ℕ)) _ => by
              have := Finset.mem_singleton.mp hq
              subst this
              norm_num)
      _ = 4096 / 4095 := by norm_num
  have htail : ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071), β q ≤
      32768 / 32767 := by
    have hmemT2 : ∀ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071),
        q ∈ L ∧ 131071 ≤ q := fun q hq => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
      exact ⟨(hmemT q h1).1, by omega⟩
    have hle : ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071), β q ≤
        ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071),
          (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod (fun q hq => (hLβ q (hmemT2 q hq).1).1.le)
        (fun q hq => (hLβ q (hmemT2 q hq).1).2)
    have htb := tail_bound _ _ 131071 rfl (by norm_num) (fun q hq => (hmemT2 q hq).2)
      (fun q hq q' hq' hlt => by
        obtain ⟨k, hk⟩ := hLm q (hmemT2 q hq).1
        obtain ⟨k', hk'⟩ := hLm q' (hmemT2 q' hq').1
        have hkk : k < k' := by
          by_contra hcon
          have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega)
    refine hle.trans (htb.trans ?_)
    norm_num
  have hnn1 : (0 : ℚ) ≤ ∏ q ∈ L.filter (fun q => ¬ q < 8191), β q :=
    Finset.prod_nonneg fun q hq => (hLβ q (hmemT q hq).1).1.le
  have hnnA : (0 : ℚ) ≤ ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => q < 131071), β q :=
    Finset.prod_nonneg fun q hq => (hLβ q (hmemT q (Finset.mem_filter.mp hq).1).1).1.le
  have hnnB : (0 : ℚ) ≤ ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071), β q :=
    Finset.prod_nonneg fun q hq => (hLβ q (hmemT q (Finset.mem_filter.mp hq).1).1).1.le
  have hM : (0 : ℚ) ≤ β 3 * β 7 * β 31 * β 127 := by
    obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity
  rw [← hsplit, ← hsplit2]
  exact mul_le_mul hsmall (mul_le_mul hmid htail hnnB (by norm_num))
    (mul_nonneg hnnA hnnB) hM

-- The N-leaves, with the sharper bound 1 / (1 - d), d = (2100/1049) * 2100 / (2099 * 2097).
theorem nleaf_bound7 {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 2100 ≤ z)
    (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097) (L : Finset ℕ)
    (hL : ∀ q ∈ L, 2 ∣ q + 1 ∧ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1 ∧
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) :
    ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      1 / (1 - 2100 / 1049 * (2100 / (2099 * 2097))) := by
  have hu : ∀ q ∈ L, (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 0 ∧
      ¬ 2 ∣ (q + 1) / 2 ^ (q + 1).factorization 2 ∧ 1 ≤ (q + 1).factorization 2 ∧
      q + 1 = 2 ^ (q + 1).factorization 2 * ((q + 1) / 2 ^ (q + 1).factorization 2) :=
    fun q hq => by
      obtain ⟨h2, _, _⟩ := hL q hq
      have hN0 : q + 1 ≠ 0 := by omega
      exact ⟨(Nat.ordCompl_pos 2 hN0).ne', Nat.not_dvd_ordCompl Nat.prime_two hN0,
        Nat.prime_two.factorization_pos_of_dvd hN0 h2,
        (Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2).symm⟩
  rw [← Finset.prod_fiberwise_of_maps_to (g := fun q => (q + 1) / 2 ^ (q + 1).factorization 2)
    (t := L.image (fun q => (q + 1) / 2 ^ (q + 1).factorization 2))
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  have h3 : ∀ u ∈ L.image (fun q => (q + 1) / 2 ^ (q + 1).factorization 2), 3 ≤ u ∧
      (u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) := fun u hu' => by
    obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu'
    obtain ⟨h0, hodd, hk, he⟩ := hu q hq
    obtain ⟨h2, hne1, hc⟩ := hL q hq
    have hdvd : u ∣ q + 1 := hqu ▸ Nat.ordCompl_dvd (q + 1) 2
    rw [hqu] at h0 hodd hne1
    refine ⟨by omega, h0, hne1, fun r hr hrd => ?_⟩
    exact hc r hr (fun h2' => hodd (h2' ▸ hrd)) (hrd.trans hdvd)
  refine (Finset.prod_le_prod (g := fun u : ℕ => (u : ℚ) / ((u : ℚ) - 2))
    (fun u _ => Finset.prod_nonneg fun x hx => ?_) (fun u hu' => ?_)).trans ?_
  · obtain ⟨h2, _, _⟩ := hL x (Finset.mem_filter.mp hx).1
    have hx1 : 1 ≤ x := by omega
    have hx1q : (1 : ℚ) ≤ x := by exact_mod_cast hx1
    exact div_nonneg (by linarith) (by linarith)
  · exact fiber_bound (h3 u hu').1 _ (fun q hq => by
      obtain ⟨hqL, hqu⟩ := Finset.mem_filter.mp hq
      obtain ⟨h0, hodd, hk, he⟩ := hu q hqL
      exact ⟨_, hk, by rw [← hqu]; exact he⟩)
  obtain ⟨U, hU⟩ : ∃ U : Finset ℕ, U = L.image (fun q => (q + 1) / 2 ^ (q + 1).factorization 2) :=
    ⟨_, rfl⟩
  rw [← hU]
  rw [← hU] at h3
  have hUge : ∀ u : ℕ, u ∈ U → (2100 : ℚ) ≤ (u : ℚ) :=
    fun u hu' => by
      obtain ⟨_, h0, h1, hr⟩ := h3 u hu'
      have hmem := hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u)
      have := (hN _ hmem).2
      have := Nat.minFac_le (Nat.pos_of_ne_zero h0)
      exact_mod_cast (by omega : 2100 ≤ u)
  have hstep : ∏ u ∈ U, ((u : ℚ) / ((u : ℚ) - 2)) ≤ ∏ u ∈ U, (1 + 2100 / 1049 * (1 / (u : ℚ))) := by
    refine Finset.prod_le_prod (fun u hu' => ?_) (fun u hu' => ?_)
    · have := hUge u hu'
      exact div_nonneg (by linarith) (by linarith)
    · have h := hUge u hu'
      have hw : (u : ℚ) * (1 / (u : ℚ)) = 1 := by field_simp
      have hw2 : 1 / (u : ℚ) ≤ 1 / 2100 := one_div_le_one_div_of_le (by norm_num) h
      rw [div_le_iff₀ (by linarith)]
      nlinarith
  have hσ : ∑ u ∈ U, 1 / (u : ℚ) ≤ 2100 / (2099 * 2097) := by
    have h1U : 1 ∉ U := fun h => (h3 1 h).2.2.1 rfl
    have hs := smooth_recip N (fun z hz => (hN z hz).1) (insert 1 U) (fun u hu' => by
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
            have := hr.two_le
            omega)⟩
        · obtain ⟨_, h0, _, hr⟩ := h3 u hu'
          exact ⟨h0, hr⟩)
    rw [Finset.sum_insert h1U] at hs
    have hprod : ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) ≤ ∏ z ∈ N, (1 + 525 / 2099 * (4 / (z : ℚ))) := by
      refine Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)
      · have : (2100 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        exact div_nonneg (by linarith) (by linarith)
      · have h : (2100 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        have hw : (z : ℚ) * (1 / (z : ℚ)) = 1 := by field_simp
        have hw2 : 1 / (z : ℚ) ≤ 1 / 2100 := one_div_le_one_div_of_le (by norm_num) h
        have e : (525 : ℚ) / 2099 * (4 / (z : ℚ)) = 2100 / 2099 * (1 / (z : ℚ)) := by ring
        rw [e, div_le_iff₀ (by linarith)]
        nlinarith
    have hL2 := prod_one_add_mul_le N (fun z => 4 / (z : ℚ)) (525 / 2099) (by norm_num) (by norm_num)
      (fun z hz => by
        have : (2100 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        positivity)
    simp only [Nat.cast_one, div_one] at hs
    have hfin := hs.trans (hprod.trans hL2)
    linarith
  have hL1 := one_sub_sum_mul_prod_le U (fun u => 2100 / 1049 * (1 / (u : ℚ))) (fun u _ => by positivity)
  rw [← Finset.mul_sum] at hL1
  have hP0 : (0 : ℚ) ≤ ∏ u ∈ U, (1 + 2100 / 1049 * (1 / (u : ℚ))) := Finset.prod_nonneg fun u hu' => by
    have := hUge u hu'
    positivity
  refine hstep.trans ?_
  rw [le_div_iff₀ (by norm_num)]
  have hcmp : (1 : ℚ) - 2100 / 1049 * (2100 / (2099 * 2097)) ≤
      1 - 2100 / 1049 * ∑ u ∈ U, 1 / (u : ℚ) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hcmp hP0]

-- The kernel factor: a product of 1 + 1/z^2 over a subset of N.
theorem kk_bound {N Z : Finset ℕ} (hZ : Z ⊆ N) (hNb : ∀ z ∈ N, 2100 ≤ z)
    (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097) :
    ∏ z ∈ Z, (1 + 1 / (z : ℚ) ^ 2) ≤ 1 + 1 / (2097 * 2100) := by
  have h1 : ∏ z ∈ Z, (1 + 1 / (z : ℚ) ^ 2) ≤ ∏ z ∈ N, (1 + 1 / 8400 * (4 / (z : ℚ))) := by
    calc ∏ z ∈ Z, (1 + 1 / (z : ℚ) ^ 2) ≤ ∏ z ∈ Z, (1 + 1 / 8400 * (4 / (z : ℚ))) :=
          Finset.prod_le_prod (fun z _ => by positivity) (fun z hz => by
            have hq : (2100 : ℚ) ≤ z := by exact_mod_cast hNb z (hZ hz)
            have hw : 1 / (z : ℚ) ≤ 1 / 2100 := one_div_le_one_div_of_le (by norm_num) hq
            have e1 : 1 / (z : ℚ) ^ 2 = (1 / (z : ℚ)) * (1 / (z : ℚ)) := by ring
            have e2 : (1 : ℚ) / 8400 * (4 / (z : ℚ)) = 1 / 2100 * (1 / (z : ℚ)) := by ring
            rw [e1, e2]
            have := mul_le_mul_of_nonneg_right hw (by positivity : (0 : ℚ) ≤ 1 / (z : ℚ))
            linarith)
      _ ≤ ∏ z ∈ N, (1 + 1 / 8400 * (4 / (z : ℚ))) :=
          Finset.prod_le_prod_of_subset_of_one_le hZ (fun z _ => by positivity)
            (fun z _ _ => by
              have : (0 : ℚ) ≤ 1 / 8400 * (4 / (z : ℚ)) := by positivity
              linarith)
  have h2 := prod_one_add_mul_le N (fun z => 4 / (z : ℚ)) (1 / 8400) (by norm_num) (by norm_num)
    (fun z _ => by positivity)
  have h3 := h1.trans h2
  nlinarith

-- Admissibility gives the product of 1 + 4/z over N.
theorem adm_hY {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hΛ : ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097) :
    ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097 := by
  rcases N.eq_empty_or_nonempty with rfl | hne
  · norm_num
  have hc : (1 : ℚ) ≤ N.card := by exact_mod_cast Finset.card_pos.mpr hne
  refine (Finset.prod_le_prod (fun z _ => by positivity) (fun z hz => ?_)).trans hΛ
  have hq : (N.card : ℚ) + 3 ≤ z := by exact_mod_cast (hN z hz).2.2
  have hz0 : (0 : ℚ) < z := by linarith
  rw [le_div_iff₀ (by linarith)]
  have hw : (z : ℚ) * (1 / (z : ℚ)) = 1 := by field_simp
  have e : (1 + 4 / (z : ℚ)) * ((z : ℚ) - 2 - N.card) =
      (z : ℚ) + 2 - N.card - 4 * (2 + N.card) * (1 / (z : ℚ)) := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ 4 * (2 + (N.card : ℚ)) * (1 / (z : ℚ)) := by positivity
  linarith

-- The balance equation with N = S; the kernel ratio K'/K is at most the product of 1 + 1/z^2.
theorem setup7 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (h2 : 2 ∣ n) :
    ∃ (K K' : ℕ) (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≠ 2) ∧
      (∀ c : ℕ, c.Prime → c ∣ K → c ∈ S) ∧ K ≤ K' ∧
      ((K' : ℚ) / K ≤ ∏ z ∈ S, (1 + 1 / (z : ℚ) ^ 2)) ∧
      ((2 ^ padicValNat 2 n + 1) * K' * ∏ p ∈ P, (p + 1) =
        2 ^ (padicValNat 2 n + 1) * K * ∏ p ∈ P, p) ∧
      (∀ q, q ∈ P ↔ q.Prime ∧ q ≠ 2 ∧ q ∣ n ∧ q ∉ S) := by
  have hn0 : n ≠ 0 := h.2.ne'
  have hfac : n.factorization 2 = padicValNat 2 n := Nat.factorization_def n Nat.prime_two
  have hs : ∀ r ∈ n.primeFactors, r ≠ 2 → r ∉ S → n.factorization r = 1 := by
    intro r hr hr2 hrN
    have hrp := Nat.prime_of_mem_primeFactors hr
    have hpos := hrp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hr)
    have : ¬ 2 ≤ n.factorization r := fun he =>
      hrN ((hS r).mpr ⟨hrp, hr2, (hrp.pow_dvd_iff_le_factorization hn0).mpr he⟩)
    omega
  have E := kernel_balance h h2 hs
  rw [hfac] at E
  have hP : ∀ p ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ S), p.Prime ∧ p ≠ 2 :=
    fun p hp => by
      have h1 := (Finset.mem_filter.mp hp).1
      exact ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase h1), Finset.ne_of_mem_erase h1⟩
  have hMmem : ∀ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S),
      z.Prime ∧ z ∈ S ∧ 2 ≤ n.factorization z := fun z hz => by
    obtain ⟨h1, hzN⟩ := Finset.mem_filter.mp hz
    have hzpf := Finset.mem_of_mem_erase h1
    have hzp := Nat.prime_of_mem_primeFactors hzpf
    exact ⟨hzp, hzN, (hzp.pow_dvd_iff_le_factorization hn0).mp ((hS z).mp hzN).2.2⟩
  have hK : ∀ c : ℕ, c.Prime →
      c ∣ ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S), z ^ n.factorization z →
      c ∈ S := fun c hc hd => by
    obtain ⟨z, hz, hcz⟩ := (Prime.dvd_finsetProd_iff hc.prime _).mp hd
    obtain ⟨hzp, hzN, _⟩ := hMmem z hz
    rw [(Nat.prime_dvd_prime_iff_eq hc hzp).mp (hc.dvd_of_dvd_pow hcz)]
    exact hzN
  have hratio : ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S),
        (1 + z ^ n.factorization z) : ℕ) : ℚ) /
      ((∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S), z ^ n.factorization z : ℕ) : ℚ) ≤
      ∏ z ∈ S, (1 + 1 / (z : ℚ) ^ 2) := by
    push_cast
    rw [← Finset.prod_div_distrib]
    refine (Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)).trans
      (Finset.prod_le_prod_of_subset_of_one_le (fun z hz => (hMmem z hz).2.1)
        (fun z _ => by positivity)
        (fun z _ _ => by
          have : (0 : ℚ) ≤ 1 / (z : ℚ) ^ 2 := by positivity
          linarith))
    · positivity
    · obtain ⟨hzp, hzN, he⟩ := hMmem z hz
      have hz1 : (1 : ℚ) ≤ z := by exact_mod_cast hzp.one_lt.le
      have hpow : (z : ℚ) ^ 2 ≤ (z : ℚ) ^ n.factorization z := pow_le_pow_right₀ hz1 he
      have hz2 : (0 : ℚ) < (z : ℚ) ^ 2 := by positivity
      rw [div_le_iff₀ (by linarith)]
      have h1 : 1 ≤ (z : ℚ) ^ n.factorization z / (z : ℚ) ^ 2 := by
        rw [le_div_iff₀ hz2]
        linarith
      have e : (1 + 1 / (z : ℚ) ^ 2) * (z : ℚ) ^ n.factorization z =
          (z : ℚ) ^ n.factorization z + (z : ℚ) ^ n.factorization z / (z : ℚ) ^ 2 := by ring
      rw [e]
      linarith
  have hK1 : ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S), z ^ n.factorization z ≤
      ∏ z ∈ (n.primeFactors.erase 2).filter (fun r => r ∈ S), (1 + z ^ n.factorization z) :=
    Finset.prod_le_prod' fun z _ => Nat.le_add_left _ _
  refine ⟨_, _, _, hP, hK, hK1, hratio, E, fun q => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_erase, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hq2, hqp, hqn, _⟩, hqN⟩
    exact ⟨hqp, hq2, hqn, hqN⟩
  · rintro ⟨hqp, hq2, hqn, hqN⟩
    exact ⟨⟨hq2, hqp, hqn, hn0⟩, hqN⟩

-- The master inequality for m at least 16 with the sharper constant
-- T = (65537/65536) (4096/4095) (32768/32767) (1 + 1/(2097 * 2100)) / (1 - d).
theorem masterT {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127)
    (hfin : 65537 / 65536 * (β 3 * β 7 * β 31 * β 127) * (4096 / 4095 * (32768 / 32767)) *
      ((1 + 1 / (2097 * 2100)) * (1 / (1 - 2100 / 1049 * (2100 / (2099 * 2097))))) < 2) :
    False := by
  obtain ⟨S1, -, S2, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨g, hg⟩ := exists_child N
  have hK0 : 0 < K := K_pos hN hK
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
    have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2.1 ((hg p).2.2.1 h).2.2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2.1 hc.2.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      by_cases hsp : β (g p) = (((g p : ℕ) : ℚ) + 1) / (((g p : ℕ) : ℚ) - 1)
      · rw [hsp]
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((g p : ℕ) : ℚ) := by positivity
        exact (mul_le_mul_of_nonneg_left (hB p hp).2 h0).trans
          (B_step hc.1.two_le (two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1))
      · exact h4 p hp (g p) h (hg p).1 (hg p).2.2.2 hsp)
  -- a path starts at a prime q such that every odd prime factor of q + 1 lies in N
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P),
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hLP : ∀ q ∈ P.filter (fun q => g q ∉ P), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hsplit := Finset.prod_filter_mul_prod_filter_not (P.filter (fun q => g q ∉ P))
    (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1) β
  have hs0 : (0 : ℚ) ≤ (N.card : ℚ) := Nat.cast_nonneg _
  have hzleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      1 / (1 - 2100 / 1049 * (2100 / (2099 * 2097))) := by
    refine (Finset.prod_le_prod
      (fun q hq => (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le)
      (fun q hq => (hB q (hLP q (Finset.mem_filter.mp hq).1)).2)).trans ?_
    refine nleaf_bound7 (fun z hz => ⟨(hN z hz).1, hNb z hz⟩) hY _ (fun q hq => ?_)
    obtain ⟨hqL, hne⟩ := Finset.mem_filter.mp hq
    have hqP := hP q (hLP q hqL)
    refine ⟨?_, hne, hleaf q hqL⟩
    rcases hqP.1.eq_two_or_odd with h | h
    · exact absurd h hqP.2
    · omega
  have hmleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => ¬ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (4096 / 4095 * (32768 / 32767)) := by
    refine mersenne_bound7 β _ (fun q hq => (hP q (hLP q (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (hLP q (Finset.mem_filter.mp hq).1),
        (hB q (hLP q (Finset.mem_filter.mp hq).1)).2⟩) h1
    obtain ⟨hqL, hzd⟩ := Finset.mem_filter.mp hq
    have h1' : (q + 1) / 2 ^ (q + 1).factorization 2 = 1 := not_not.mp hzd
    have hmul := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2
    rw [h1', mul_one] at hmul
    exact ⟨(q + 1).factorization 2, hmul.symm⟩
  have hM0 : (0 : ℚ) ≤ (β 3 * β 7 * β 31 * β 127) * (4096 / 4095 * (32768 / 32767)) := by
    obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity
  have hNL0 : (0 : ℚ) ≤ 1 / (1 - 2100 / 1049 * (2100 / (2099 * 2097))) := by norm_num
  have hprodL : ∏ q ∈ P.filter (fun q => g q ∉ P), β q ≤
      (1 / (1 - 2100 / 1049 * (2100 / (2099 * 2097)))) *
        ((β 3 * β 7 * β 31 * β 127) * (4096 / 4095 * (32768 / 32767))) := by
    rw [← hsplit]
    refine mul_le_mul hzleaves hmleaves ?_ hNL0
    exact Finset.prod_nonneg fun q hq =>
      (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * K' * ∏ p ∈ P, ((p : ℚ) + 1) =
        2 ^ (m + 1) * K * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 65537 / 65536 := by
    have h2 : (2 : ℚ) ^ 16 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 16 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hKr0 : (0 : ℚ) ≤ (K' : ℚ) / K := div_nonneg (Nat.cast_nonneg _) hKq.le
  have hA : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) ≤ 65537 / 65536 * (1 + 1 / (2097 * 2100)) :=
    mul_le_mul hT hKr hKr0 (by norm_num)
  have hC := mul_le_mul hA (hpath.trans hprodL)
    (Finset.prod_nonneg fun p _ => by positivity) (by norm_num)
  have e2 : 65537 / 65536 * (1 + 1 / (2097 * 2100)) *
      ((1 / (1 - 2100 / 1049 * (2100 / (2099 * 2097)))) *
        ((β 3 * β 7 * β 31 * β 127) * (4096 / 4095 * (32768 / 32767)))) =
      65537 / 65536 * (β 3 * β 7 * β 31 * β 127) * (4096 / 4095 * (32768 / 32767)) *
      ((1 + 1 / (2097 * 2100)) * (1 / (1 - 2100 / 1049 * (2100 / (2099 * 2097))))) := by ring
  rw [hEq, e2] at hC
  linarith

-- A prime p with 991 ∣ p + 1 is at least 7927 (1981, 3963, 5945 are composite).
theorem T991 {p : ℕ} (hp : p.Prime) (hd : 991 ∣ p + 1) : 7927 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  obtain ⟨j, hj⟩ : 2 * 991 ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 hd
  have hjlt : j < 4 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 2 * 991 * j - 1 := by omega
  clear hd h2 hlt hp2 hj
  interval_cases j <;> first | omega | (norm_num at hp)

end Erdos1052C7

namespace Erdos1052C9

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open Erdos1052C7

-- An odd number m > 1 has an odd prime factor r ≤ m.
theorem odd_prime_factor {m : ℕ} (hmo : Odd m) (hm1 : m ≠ 1) :
    ∃ r k : ℕ, r.Prime ∧ r ≠ 2 ∧ m = r * k ∧ 1 ≤ k := by
  have hm0 : 0 < m := hmo.pos
  refine ⟨m.minFac, m / m.minFac, Nat.minFac_prime hm1, fun h => ?_, ?_, ?_⟩
  · have := Nat.minFac_dvd m
    rw [h] at this
    exact (Nat.not_even_iff_odd.mpr hmo) (even_iff_two_dvd.mpr this)
  · exact (Nat.mul_div_cancel' (Nat.minFac_dvd m)).symm
  · exact Nat.div_pos (Nat.minFac_le hm0) (Nat.minFac_pos m)

-- p + 1 = 2 * c * (2^e * m) with m odd, for an odd prime p and an odd c ∣ p + 1.
theorem split_odd {p c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hc : Nat.Coprime 2 c) (hd : c ∣ p + 1) :
    ∃ e m : ℕ, Odd m ∧ p + 1 = 2 * c * (2 ^ e * m) := by
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  obtain ⟨j, hj⟩ : 2 * c ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h2 hd
  have hj0 : j ≠ 0 := by
    rintro rfl
    omega
  obtain ⟨e, m, hmo, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hj0
  exact ⟨e, m, hmo, hj⟩

-- Parent of 31 in the 223 family without 991: at least 3967.
theorem T31y {p : ℕ} (hp : p.Prime) (hd : 31 ∣ p + 1) (hsq : ¬ 31 * 31 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 31 ∨ 64 ≤ r)
    (h61 : p ≠ 61) (h991 : p ≠ 991) : 3967 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 6 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 6 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 31 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h61 h991 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 31 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk
      omega

-- Parent of 223 with every odd prime factor of p + 1 equal to 223 or at least 479: at least
-- 213633 (446 * 2^e - 1 is composite for e ≤ 8 except 1783).
theorem T223y {p : ℕ} (hp : p.Prime) (hd : 223 ∣ p + 1) (hsq : ¬ 223 * 223 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 223 ∨ 479 ≤ r)
    (h1783 : p ≠ 1783) : 213633 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 9 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 9 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 223 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h1783 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 223 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    rcases hgap r hr hr2 hrp with h | h
    · subst h
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · generalize 2 ^ e * (r * k) = t at hj hrk
      omega

-- Parent of 19 in the 223 family without 607: at least 18201.
theorem T19y {p : ℕ} (hp : p.Prime) (hd : 19 ∣ p + 1) (hsq : ¬ 19 * 19 ∣ p + 1)
    (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 19 ≤ r)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 19 ∨ r = 31 ∨ r = 223 ∨ 479 ≤ r)
    (h152 : 152 ≤ p) (h607 : p ≠ 607) : 18201 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  have h3 : ¬ 3 ∣ p + 1 := fun h => by have := hmin 3 (by norm_num) (by norm_num) h; omega
  have h5 : ¬ 5 ∣ p + 1 := fun h => by have := hmin 5 (by norm_num) (by norm_num) h; omega
  have h7 : ¬ 7 ∣ p + 1 := fun h => by have := hmin 7 (by norm_num) (by norm_num) h; omega
  have h11 : ¬ 11 ∣ p + 1 := fun h => by have := hmin 11 (by norm_num) (by norm_num) h; omega
  have h13 : ¬ 13 ∣ p + 1 := fun h => by have := hmin 13 (by norm_num) (by norm_num) h; omega
  have h17 : ¬ 17 ∣ p + 1 := fun h => by have := hmin 17 (by norm_num) (by norm_num) h; omega
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 9 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 9 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 19 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hmin hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h152 h607 h3 h5 h7 h11 h13 h17 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 19 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    have htk : 1 ≤ 2 ^ e * k := Nat.mul_le_mul he0 hk
    rcases hgap r hr hr2 hrp with h | h | h | h
    · subst h
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · subst h
      have hj' : p + 1 = 2 * 19 * 31 * (2 ^ e * k) := by rw [hj]; ring
      generalize 2 ^ e * k = t at hj' htk
      have ht : t < 16 := by omega
      obtain rfl : p = 2 * 19 * 31 * t - 1 := by omega
      clear hj hd hsq hgap hmin hlt hp2 hmo he0 hrk hrp hk hm1 hj' h152 h607
      interval_cases t <;> revert hp h3 h5 h7 h11 h13 h17 <;> norm_num
    · subst h
      have hj' : p + 1 = 2 * 19 * 223 * (2 ^ e * k) := by rw [hj]; ring
      generalize 2 ^ e * k = t at hj' htk
      have ht : t < 3 := by omega
      obtain rfl : p = 2 * 19 * 223 * t - 1 := by omega
      clear hj hd hsq hgap hmin hlt hp2 hmo he0 hrk hrp hk hm1 hj' h152 h607
      interval_cases t <;> revert hp h3 h5 h7 h11 h13 h17 <;> norm_num
    · generalize 2 ^ e * (r * k) = t at hj hrk
      omega

-- The 223 family without 607, 991 and 1783: impossible for m at least 16.
-- Chains 3 ← 5 ← 19 (parent of 19 ≥ 18201), 7 ← 223 (parent of 223 ≥ 213633) and 31 (parent
-- ≥ 3967); total T·β₃·β₇·β₃₁ = 1.99954657 < 2.
theorem node223 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∉ P) (h991 : 991 ∉ P) (h1783 : 1783 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have hA : ({3, 5, 7, 19, 31, 223} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
  have gap : ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → 479 ≤ q := by
    intro q hq e3 e5 e7 e19 e31 e223
    have hqA : q ∉ ({3, 5, 7, 19, 31, 223} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223} : Finset ℕ), (p + 1) = 27525120 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223} : Finset ℕ), p = 13791435 := by decide
    rw [e1, e2] at h
    have h477 : 477 ≤ q := by omega
    have hqp := (hP q hq).1
    have n477 : q ≠ 477 := by
      rintro rfl
      norm_num at hqp
    have n478 : q ≠ 478 := by
      rintro rfl
      norm_num at hqp
    omega
  -- an odd prime factor r of p + 1 (p ∈ P): either r ∈ N (so r ≥ 2100) or r ∈ P
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      2100 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ 479 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hNb r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3
      · exact Or.inl e3
      by_cases e5 : r = 5
      · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7
      · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19
      · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (gap r hrP e3 e5 e7 e19 e31 e223))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (18202 / 18200))) else
      if p = 5 then 6 / 5 * (20 / 19 * (18202 / 18200)) else
      if p = 19 then 20 / 19 * (18202 / 18200) else
      if p = 7 then 8 / 7 * (224 / 223 * (213634 / 213632)) else
      if p = 223 then 224 / 223 * (213634 / 213632) else
      if p = 31 then 32 / 31 * (3968 / 3966) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (18202 / 18200))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (18202 / 18200)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (18202 / 18200) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (213634 / 213632)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (213634 / 213632) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3966) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e223 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e223, if_neg e31, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e223 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  refine masterT hP hN hK hKr hNb hY E hm β hB ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      have hge : 18201 ≤ p := T19y (hP p hp).1 hd
        (S4b 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => if hrN : r ∈ N then by have := hNb r hrN; omega
          else hmin r hr hr2 hrN hrd)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (by
          by_contra hlt
          rcases hs p hp (by omega) with rfl | rfl | rfl | rfl | rfl <;> norm_num at hd)
        (fun h => h607 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 18201) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 223 := T7 p hp hd
      rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 213633 ≤ p := T223y (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => h1783 (h ▸ hp))
      rw [b223]
      exact step_ge (t := 213633) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      have hge : 3967 ≤ p := T31y (hP p hp).1 hd
        (S4b 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => by
          have := hs 61 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h991 (h ▸ hp))
      rw [b31]
      exact step_ge (t := 3967) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e223 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

end Erdos1052C9

namespace Erdos1052C11

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open Erdos1052C7 Erdos1052C9

-- Leaves that at least quadruple (q' + 1 ≥ 4 (q + 1)): the product of (q+1)/(q-1) is at most
-- 3X/(3X - 8), X a lower bound for q + 1.
theorem quad_tail : ∀ (n : ℕ) (Q : Finset ℕ) (X : ℕ), Q.card = n → 4 ≤ X → (∀ q ∈ Q, X ≤ q + 1) →
    (∀ q ∈ Q, ∀ q' ∈ Q, q < q' → 4 * (q + 1) ≤ q' + 1) →
    ∏ q ∈ Q, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 3 * (X : ℚ) / (3 * (X : ℚ) - 8) := by
  intro n
  induction n with
  | zero =>
    intro Q X hQ hX _ _
    have hX' : (4 : ℚ) ≤ X := by exact_mod_cast hX
    rw [Finset.card_eq_zero.mp hQ, Finset.prod_empty, le_div_iff₀ (by linarith)]
    linarith
  | succ n ih =>
    intro Q X hcard hX hge hq4
    have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqQ, hqmin⟩ : ∃ q ∈ Q, ∀ p ∈ Q, q ≤ p :=
      ⟨Q.min' hne, Finset.min'_mem Q hne, fun p hp => Finset.min'_le Q p hp⟩
    have hXq : X ≤ q + 1 := hge q hqQ
    have ih' := ih (Q.erase q) (4 * (q + 1)) (by rw [Finset.card_erase_of_mem hqQ, hcard]; rfl)
      (by omega)
      (fun x hx => hq4 q hqQ x (Finset.mem_of_mem_erase hx)
        (lt_of_le_of_ne (hqmin x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx).symm))
      (fun x hx y hy => hq4 x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy))
    have hX' : (4 : ℚ) ≤ X := by exact_mod_cast hX
    have hXq' : (X : ℚ) ≤ (q : ℚ) + 1 := by exact_mod_cast hXq
    have hB0 : (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := div_nonneg (by linarith) (by linarith)
    rw [← Finset.mul_prod_erase Q _ hqQ]
    calc ((q : ℚ) + 1) / ((q : ℚ) - 1) * ∏ x ∈ Q.erase q, (((x : ℚ) + 1) / ((x : ℚ) - 1))
        ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) *
            (3 * ((4 * (q + 1) : ℕ) : ℚ) / (3 * ((4 * (q + 1) : ℕ) : ℚ) - 8)) :=
          mul_le_mul_of_nonneg_left ih' hB0
      _ ≤ 3 * ((q : ℚ) + 1) / (3 * ((q : ℚ) + 1) - 8) := by
          push_cast
          rw [div_mul_div_comm, div_le_div_iff₀ (by nlinarith) (by linarith)]
          nlinarith
      _ ≤ 3 * (X : ℚ) / (3 * (X : ℚ) - 8) := by
          rw [div_le_div_iff₀ (by linarith) (by linarith)]
          nlinarith

-- One fiber (fixed odd part u, 3 ∤ u) of leaves q = 2^k u - 1 with q + 1 ≡ 2 (mod 3): two leaves
-- of the fiber differ by a factor 2^j with j ≥ 2 (j = 1 would change the residue mod 3), and the
-- least one is ≥ 2u - 1 (u ≡ 1) or ≥ 4u - 1 (u ≡ 2).
theorem fiber3 {u : ℕ} (hu : 3 ≤ u) (hu3 : u % 3 ≠ 0) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, (q + 1) % 3 = 2 ∧ ∃ k, 1 ≤ k ∧ q + 1 = 2 ^ k * u) :
    ∏ q ∈ Q, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 1 + (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) := by
  have hq4 : ∀ q ∈ Q, ∀ q' ∈ Q, q < q' → 4 * (q + 1) ≤ q' + 1 := by
    intro q hq q' hq' hlt
    obtain ⟨h3, k, hk, he⟩ := hQ q hq
    obtain ⟨h3', k', hk', he'⟩ := hQ q' hq'
    have hkk : k < k' := by
      by_contra hcon
      have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ k' * u ≤ 2 ^ k * u := Nat.mul_le_mul_right _ this
      omega
    by_cases h1 : k' = k + 1
    · subst h1
      rw [pow_succ] at he'
      have : q' + 1 = 2 * (q + 1) := by rw [he', he]; ring
      omega
    · have : 2 ^ (k + 2) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : 2 ^ (k + 2) * u ≤ 2 ^ k' * u := Nat.mul_le_mul_right _ this
      have e : 2 ^ (k + 2) * u = 4 * (2 ^ k * u) := by ring
      omega
  have huq : (3 : ℚ) ≤ u := by exact_mod_cast hu
  by_cases h1 : u % 3 = 1
  · have hge : ∀ q ∈ Q, 2 * u ≤ q + 1 := by
      intro q hq
      obtain ⟨_, k, hk, he⟩ := hQ q hq
      have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      have : 2 ^ 1 * u ≤ 2 ^ k * u := Nat.mul_le_mul_right _ this
      omega
    have h := quad_tail Q.card Q (2 * u) rfl (by omega) hge hq4
    rw [if_pos h1]
    refine h.trans (le_of_eq ?_)
    have hA : (3 * (u : ℚ) - 4) ≠ 0 := by linarith
    have hB : (3 * ((2 * u : ℕ) : ℚ) - 8) ≠ 0 := by push_cast; linarith
    have e : 1 + 4 / (3 * (u : ℚ) - 4) = 3 * (u : ℚ) / (3 * (u : ℚ) - 4) := by
      rw [eq_div_iff hA, add_mul, div_mul_cancel₀ _ hA]
      ring
    rw [e, div_eq_div_iff hB hA]
    push_cast
    ring
  · have hge : ∀ q ∈ Q, 4 * u ≤ q + 1 := by
      intro q hq
      obtain ⟨h3, k, hk, he⟩ := hQ q hq
      by_cases hk1 : k = 1
      · subst hk1
        omega
      · have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2 ^ 2 * u ≤ 2 ^ k * u := Nat.mul_le_mul_right _ this
        omega
    have h := quad_tail Q.card Q (4 * u) rfl (by omega) hge hq4
    rw [if_neg h1]
    refine h.trans (le_of_eq ?_)
    have hA : (3 * (u : ℚ) - 2) ≠ 0 := by linarith
    have hB : (3 * ((4 * u : ℕ) : ℚ) - 8) ≠ 0 := by push_cast; linarith
    have e : 1 + 2 / (3 * (u : ℚ) - 2) = 3 * (u : ℚ) / (3 * (u : ℚ) - 2) := by
      rw [eq_div_iff hA, add_mul, div_mul_cancel₀ _ hA]
      ring
    rw [e, div_eq_div_iff hB hA]
    push_cast
    ring

-- The N-leaves q (q + 1 = 2^k u, u > 1 with all primes in N, q + 1 ≡ 2 mod 3): grouped by u,
-- the product is at most ∏ (1 + x(u)) ≤ 1 / (1 - Σ x(u)) ≤ 1 / (1 - D).
theorem nleaf3 {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 2100 ≤ z) (D : ℚ) (hD1 : D < 1)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ D)
    (L : Finset ℕ)
    (hL : ∀ q ∈ L, 2 ∣ q + 1 ∧ (q + 1) % 3 = 2 ∧ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1 ∧
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N) :
    ∏ q ∈ L, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ 1 / (1 - D) := by
  have hu : ∀ q ∈ L, (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 0 ∧
      ¬ 2 ∣ (q + 1) / 2 ^ (q + 1).factorization 2 ∧ 1 ≤ (q + 1).factorization 2 ∧
      q + 1 = 2 ^ (q + 1).factorization 2 * ((q + 1) / 2 ^ (q + 1).factorization 2) :=
    fun q hq => by
      obtain ⟨h2, _, _, _⟩ := hL q hq
      have hN0 : q + 1 ≠ 0 := by omega
      exact ⟨(Nat.ordCompl_pos 2 hN0).ne', Nat.not_dvd_ordCompl Nat.prime_two hN0,
        Nat.prime_two.factorization_pos_of_dvd hN0 h2,
        (Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2).symm⟩
  rw [← Finset.prod_fiberwise_of_maps_to (g := fun q => (q + 1) / 2 ^ (q + 1).factorization 2)
    (t := L.image (fun q => (q + 1) / 2 ^ (q + 1).factorization 2))
    (fun x hx => Finset.mem_image_of_mem _ hx)]
  obtain ⟨U, hU⟩ : ∃ U : Finset ℕ, U = L.image (fun q => (q + 1) / 2 ^ (q + 1).factorization 2) :=
    ⟨_, rfl⟩
  rw [← hU]
  have h3 : ∀ u ∈ U, 3 ≤ u ∧ u % 3 ≠ 0 ∧
      (u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) := fun u hu' => by
    rw [hU] at hu'
    obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu'
    obtain ⟨h0, hodd, hk, he⟩ := hu q hq
    obtain ⟨h2, _, hne1, hc⟩ := hL q hq
    have hdvd : u ∣ q + 1 := hqu ▸ Nat.ordCompl_dvd (q + 1) 2
    rw [hqu] at h0 hodd hne1
    have hr : ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N := fun r hr hrd =>
      hc r hr (fun h2' => hodd (h2' ▸ hrd)) (hrd.trans hdvd)
    refine ⟨by omega, fun h30 => ?_, h0, hne1, hr⟩
    have := (hN 3 (hr 3 (by norm_num) (Nat.dvd_of_mod_eq_zero h30))).2
    omega
  have hx0 : ∀ u ∈ U, (0 : ℚ) ≤ (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) := fun u hu' => by
    have huq : (3 : ℚ) ≤ u := by exact_mod_cast (h3 u hu').1
    split_ifs
    · exact div_nonneg (by norm_num) (by linarith)
    · exact div_nonneg (by norm_num) (by linarith)
  refine (Finset.prod_le_prod (g := fun u : ℕ => 1 + (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)))
    (fun u _ => Finset.prod_nonneg fun x hx => ?_) (fun u hu' => ?_)).trans ?_
  · obtain ⟨h2, _, _, _⟩ := hL x (Finset.mem_filter.mp hx).1
    have hx1 : 1 ≤ x := by omega
    have hx1q : (1 : ℚ) ≤ x := by exact_mod_cast hx1
    exact div_nonneg (by linarith) (by linarith)
  · exact fiber3 (h3 u hu').1 (h3 u hu').2.1 _ (fun q hq => by
      obtain ⟨hqL, hqu⟩ := Finset.mem_filter.mp hq
      obtain ⟨h0, hodd, hk, he⟩ := hu q hqL
      exact ⟨(hL q hqL).2.1, _, hk, by rw [← hqu]; exact he⟩)
  have hσ := hD U (fun u hu' => (h3 u hu').2.2)
  have hL1 := one_sub_sum_mul_prod_le U (fun u : ℕ => (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2))) hx0
  have hP0 : (0 : ℚ) ≤ ∏ u ∈ U, (1 + (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2))) :=
    Finset.prod_nonneg fun u hu' => by linarith [hx0 u hu']
  rw [le_div_iff₀ (by linarith)]
  have hcmp : (1 : ℚ) - D ≤ 1 - ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hcmp hP0]

-- x(u) ≤ (4/3) (3c/(3c - 4)) / u for u ≥ c.
theorem xw_le {u c : ℕ} (hc : 2 ≤ c) (hu : c ≤ u) :
    (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (3 * (c : ℚ) / (3 * (c : ℚ) - 4)) * (1 / (u : ℚ)) := by
  have hcq : (2 : ℚ) ≤ c := by exact_mod_cast hc
  have huq : (c : ℚ) ≤ u := by exact_mod_cast hu
  have h1 : 4 / (3 * (u : ℚ) - 4) ≤ 4 / 3 * (3 * (c : ℚ) / (3 * (c : ℚ) - 4)) * (1 / (u : ℚ)) := by
    have e : 4 / 3 * (3 * (c : ℚ) / (3 * (c : ℚ) - 4)) * (1 / (u : ℚ)) =
        4 * (c : ℚ) / ((3 * (c : ℚ) - 4) * u) := by
      field_simp
    rw [e, div_le_div_iff₀ (by linarith) (by nlinarith)]
    nlinarith
  split_ifs
  · exact h1
  · refine le_trans ?_ h1
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith

-- Σ x(u) over N-smooth u > 1 when every z ∈ N is ≥ 2622 and ∏ (1 + 5/z) ≤ 2101/2097.
theorem sumD_two {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 2622 ≤ z)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 2101 / 2097) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) :
    ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (4 / 2097)) := by
  have hUge : ∀ u ∈ U, 2622 ≤ u := fun u hu' => by
    obtain ⟨h0, h1, hr⟩ := hU u hu'
    have hmem := hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u)
    have := (hN _ hmem).2
    have := Nat.minFac_le (Nat.pos_of_ne_zero h0)
    omega
  have hstep : ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      ∑ u ∈ U, 4 / 3 * (7866 / 7862) * (1 / (u : ℚ)) := by
    refine Finset.sum_le_sum fun u hu' => ?_
    have h := xw_le (c := 2622) (by norm_num) (hUge u hu')
    norm_num at h ⊢
    exact h
  rw [← Finset.mul_sum] at hstep
  have hσ : ∑ u ∈ U, 1 / (u : ℚ) ≤ 1 / 5 * (2622 / 2621) * (4 / 2097) := by
    have h1U : 1 ∉ U := fun h => (hU 1 h).2.1 rfl
    have hs := smooth_recip N (fun z hz => (hN z hz).1) (insert 1 U) (fun u hu' => by
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
            have := hr.two_le
            omega)⟩
        · obtain ⟨h0, _, hr⟩ := hU u hu'
          exact ⟨h0, hr⟩)
    rw [Finset.sum_insert h1U] at hs
    have hprod : ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) ≤
        ∏ z ∈ N, (1 + 1 / 5 * (2622 / 2621) * (5 / (z : ℚ))) := by
      refine Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)
      · have : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        exact div_nonneg (by linarith) (by linarith)
      · have h : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        have e : (1 : ℚ) / 5 * (2622 / 2621) * (5 / (z : ℚ)) = 2622 / (2621 * (z : ℚ)) := by
          field_simp
        rw [e, div_le_iff₀ (by linarith)]
        have : (1 + 2622 / (2621 * (z : ℚ))) * ((z : ℚ) - 1) = (z : ℚ) - 1 + 2622 / 2621 -
            2622 / (2621 * (z : ℚ)) := by
          field_simp
          ring
        rw [this]
        have : 2622 / (2621 * (z : ℚ)) ≤ 1 / 2621 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        linarith
    have hL2 := prod_one_add_mul_le N (fun z => 5 / (z : ℚ)) (1 / 5 * (2622 / 2621))
      (by norm_num) (by norm_num)
      (fun z hz => by
        have : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        positivity)
    simp only [Nat.cast_one, div_one] at hs
    have hfin := hs.trans (hprod.trans hL2)
    have h0 : (0 : ℚ) ≤ 1 / 5 * (2622 / 2621) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left (show ∏ z ∈ N, (1 + 5 / (z : ℚ)) - 1 ≤ 2101 / 2097 - 1 by
      linarith) h0]
  refine hstep.trans ?_
  have h0 : (0 : ℚ) ≤ 4 / 3 * (7866 / 7862) := by norm_num
  have := mul_le_mul_of_nonneg_left hσ h0
  linarith

-- The same sum when N = {z} with z ≡ 2 (mod 3), z ≥ 2100: the term u = z is 2/(3z - 2), and the
-- other u (powers z^j, j ≥ 2) sum to at most 1/(z(z - 1)) in 1/u.
theorem sumD_one {z : ℕ} (hz : z.Prime) (hz2 : 2100 ≤ z) (hz3 : z % 3 = 2) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ ({z} : Finset ℕ)) :
    ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (4 / 2097)) := by
  have hzq : (2100 : ℚ) ≤ z := by exact_mod_cast hz2
  have hUge : ∀ u ∈ U, 2100 ≤ u := fun u hu' => by
    obtain ⟨h0, h1, hr⟩ := hU u hu'
    have hmem := Finset.mem_singleton.mp (hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u))
    have := Nat.minFac_le (Nat.pos_of_ne_zero h0)
    omega
  have hx0 : ∀ u ∈ insert z U, (0 : ℚ) ≤ (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) := fun u hu' => by
    have huq : (2100 : ℚ) ≤ u := by
      rcases Finset.mem_insert.mp hu' with rfl | h
      · exact hzq
      · exact_mod_cast hUge u h
    split_ifs
    · exact div_nonneg (by norm_num) (by linarith)
    · exact div_nonneg (by norm_num) (by linarith)
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert z U)
    (fun u hu' _ => hx0 u hu') (f := fun u : ℕ => (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)))
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self z U), Finset.erase_insert_eq_erase,
    if_neg (by omega)] at hsub
  have hfz : 2 / (3 * (z : ℚ) - 2) ≤ 2 / 6298 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hstep : ∑ u ∈ U.erase z, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      ∑ u ∈ U.erase z, 4 / 3 * (6300 / 6296) * (1 / (u : ℚ)) := by
    refine Finset.sum_le_sum fun u hu' => ?_
    have h := xw_le (c := 2100) (by norm_num) (hUge u (Finset.mem_of_mem_erase hu'))
    norm_num at h ⊢
    exact h
  rw [← Finset.mul_sum] at hstep
  have hσ : ∑ u ∈ U.erase z, 1 / (u : ℚ) ≤ 1 / (2100 * 2099) := by
    have h1 : 1 ∉ insert z (U.erase z) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hz.one_lt.ne h
      · exact (hU 1 (Finset.mem_of_mem_erase h)).2.1 rfl
    have hz' : z ∉ U.erase z := Finset.notMem_erase z U
    have hs := smooth_recip {z} (fun w hw => (Finset.mem_singleton.mp hw) ▸ hz)
      (insert 1 (insert z (U.erase z))) (fun u hu' => by
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
            have := hr.two_le
            omega)⟩
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact ⟨hz.ne_zero, fun r hr hd => by
            rw [(Nat.prime_dvd_prime_iff_eq hr hz).mp hd]
            exact Finset.mem_singleton_self _⟩
        · obtain ⟨h0, _, hr⟩ := hU u (Finset.mem_of_mem_erase hu')
          exact ⟨h0, hr⟩)
    rw [Finset.sum_insert h1, Finset.sum_insert hz', Finset.prod_singleton] at hs
    simp only [Nat.cast_one, div_one] at hs
    have e : (z : ℚ) / ((z : ℚ) - 1) - 1 - 1 / (z : ℚ) = 1 / ((z : ℚ) * ((z : ℚ) - 1)) := by
      have hA : (z : ℚ) - 1 ≠ 0 := by linarith
      have hB : (z : ℚ) ≠ 0 := by linarith
      field_simp
      ring
    have h2 : 1 / ((z : ℚ) * ((z : ℚ) - 1)) ≤ 1 / (2100 * 2099) := by
      rw [div_le_div_iff₀ (by nlinarith) (by norm_num)]
      nlinarith
    linarith
  have h0 : (0 : ℚ) ≤ 4 / 3 * (6300 / 6296) := by norm_num
  have := mul_le_mul_of_nonneg_left hσ h0
  refine hsub.trans ?_
  norm_num at hstep this ⊢
  linarith

-- The Mersenne leaves with an explicit weight at 8191.
theorem mersenne_bound11 (β : ℕ → ℚ) (L : Finset ℕ) (hLp : ∀ q ∈ L, q.Prime)
    (hLm : ∀ q ∈ L, ∃ k, q + 1 = 2 ^ k)
    (hLβ : ∀ q ∈ L, 0 < β q ∧ β q ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1))
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127) (h8 : 1 ≤ β 8191) :
    ∏ q ∈ L, β q ≤ (β 3 * β 7 * β 31 * β 127) * (β 8191 * (32768 / 32767)) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not L (fun q => q < 8191) β
  have hsmall : ∏ q ∈ L.filter (fun q => q < 8191), β q ≤ β 3 * β 7 * β 31 * β 127 := by
    have hsub : L.filter (fun q => q < 8191) ⊆ ({3, 7, 31, 127} : Finset ℕ) := by
      intro q hq
      obtain ⟨hqL, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨k, hk⟩ := hLm q hqL
      have := mersenne_small (hLp q hqL) hk hlt
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun i hi => (hLβ i (Finset.mem_filter.mp hi).1).1.le) (fun i hi _ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact h1.1
      · exact h1.2.1
      · exact h1.2.2.1
      · exact h1.2.2.2)
    have e : ∏ q ∈ ({3, 7, 31, 127} : Finset ℕ), β q = β 3 * β 7 * β 31 * β 127 := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_insert (by decide), Finset.prod_singleton]
      ring
    rwa [e] at h
  have hmemT : ∀ q ∈ L.filter (fun q => ¬ q < 8191), q ∈ L ∧ 8191 ≤ q := fun q hq => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
    exact ⟨h1, by omega⟩
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not (L.filter (fun q => ¬ q < 8191))
    (fun q => q < 131071) β
  have hmid : ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => q < 131071), β q ≤
      β 8191 := by
    have hsub : (L.filter (fun q => ¬ q < 8191)).filter (fun q => q < 131071) ⊆ {8191} := by
      intro q hq
      obtain ⟨hqL2, hlt⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqL, hge⟩ := hmemT q hqL2
      obtain ⟨k, hk⟩ := hLm q hqL
      have := mersenne_small7 (hLp q hqL) hk hlt
      rw [Finset.mem_singleton]
      omega
    have h := Finset.prod_le_prod_of_subset_of_one_le (f := β) hsub
      (fun i hi => (hLβ i (hmemT i (Finset.mem_filter.mp hi).1).1).1.le)
      (fun i hi _ => by rw [Finset.mem_singleton.mp hi]; exact h8)
    rwa [Finset.prod_singleton] at h
  have htail : ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071), β q ≤
      32768 / 32767 := by
    have hmemT2 : ∀ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071),
        q ∈ L ∧ 131071 ≤ q := fun q hq => by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hq
      exact ⟨(hmemT q h1).1, by omega⟩
    have hle : ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071), β q ≤
        ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071),
          (((q : ℚ) + 1) / ((q : ℚ) - 1)) :=
      Finset.prod_le_prod (fun q hq => (hLβ q (hmemT2 q hq).1).1.le)
        (fun q hq => (hLβ q (hmemT2 q hq).1).2)
    have htb := tail_bound _ _ 131071 rfl (by norm_num) (fun q hq => (hmemT2 q hq).2)
      (fun q hq q' hq' hlt => by
        obtain ⟨k, hk⟩ := hLm q (hmemT2 q hq).1
        obtain ⟨k', hk'⟩ := hLm q' (hmemT2 q' hq').1
        have hkk : k < k' := by
          by_contra hcon
          have : 2 ^ k' ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have : 2 ^ (k + 1) ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at this
        omega)
    refine hle.trans (htb.trans ?_)
    norm_num
  have hnn1 : (0 : ℚ) ≤ ∏ q ∈ L.filter (fun q => ¬ q < 8191), β q :=
    Finset.prod_nonneg fun q hq => (hLβ q (hmemT q hq).1).1.le
  have hnnA : (0 : ℚ) ≤ ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => q < 131071), β q :=
    Finset.prod_nonneg fun q hq => (hLβ q (hmemT q (Finset.mem_filter.mp hq).1).1).1.le
  have hnnB : (0 : ℚ) ≤ ∏ q ∈ (L.filter (fun q => ¬ q < 8191)).filter (fun q => ¬ q < 131071), β q :=
    Finset.prod_nonneg fun q hq => (hLβ q (hmemT q (Finset.mem_filter.mp hq).1).1).1.le
  have hM : (0 : ℚ) ≤ β 3 * β 7 * β 31 * β 127 := by
    obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    positivity
  rw [← hsplit, ← hsplit2]
  exact mul_le_mul hsmall (mul_le_mul hmid htail hnnB (by linarith))
    (mul_nonneg hnnA hnnB) hM

-- The master inequality for m at least 20, with an explicit weight β 8191 for the Mersenne leaf
-- 8191 and the mod-3 leaf bound 1 / (1 - D): a leaf q ≠ 5 has 3 ∤ q + 1, so q + 1 ≡ 2 (mod 3).
theorem masterU {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (D : ℚ) (hD1 : D < 1)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ D)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 20 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5)
    (β : ℕ → ℚ)
    (hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1))
    (h4 : ∀ p ∈ P, ∀ c ∈ P, c ∣ p + 1 →
        (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
        β c ≠ ((c : ℚ) + 1) / ((c : ℚ) - 1) → (1 + 1 / (c : ℚ)) * β p ≤ β c)
    (h1 : 1 ≤ β 3 ∧ 1 ≤ β 7 ∧ 1 ≤ β 31 ∧ 1 ≤ β 127) (h8 : 1 ≤ β 8191)
    (hfin : 1048577 / 1048576 * (β 3 * β 7 * β 31 * β 127) * (β 8191 * (32768 / 32767)) *
      ((1 + 1 / (2097 * 2100)) * (1 / (1 - D))) < 2) :
    False := by
  obtain ⟨S1, -, S2, -, -, -, -, -⟩ := facts hP hK E
  obtain ⟨g, hg⟩ := exists_child N
  have hK0 : 0 < K := K_pos hN hK
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).1.pos
  have hβpos : ∀ p ∈ P, 0 < β p := fun p hp => by
    have h0 : (0 : ℚ) ≤ 1 / (p : ℚ) := by positivity
    linarith [(hB p hp).1]
  have hg1 : ∀ p ∈ P, g p ∈ P → g p ≠ 1 := fun p _ h h1 => by
    have := (hP _ h).1
    rw [h1] at this
    exact Nat.not_prime_one this
  have hgP : ∀ p ∈ P, g p ≠ 1 → g p ∈ P := fun p hp h =>
    S1 _ ((hg p).2.2.1 h).1 ((hg p).2.2.1 h).2.1 ((hg p).2.2.1 h).2.2 p hp (hg p).1
  have hpath := path_bound g β P.card P rfl hpos
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      have := two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1
      have := hc.1.two_le
      omega)
    (fun p hp p' hp' h he => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      exact S2 _ hc.1 hc.2.1 hc.2.2 p hp p' hp' (hg p).1 (he ▸ (hg p').1))
    (fun p hp => (hB p hp).1)
    (fun p hp h => by
      have hc := (hg p).2.2.1 (hg1 p hp h)
      by_cases hsp : β (g p) = (((g p : ℕ) : ℚ) + 1) / (((g p : ℕ) : ℚ) - 1)
      · rw [hsp]
        have h0 : (0 : ℚ) ≤ 1 + 1 / ((g p : ℕ) : ℚ) := by positivity
        exact (mul_le_mul_of_nonneg_left (hB p hp).2 h0).trans
          (B_step hc.1.two_le (two_mul_le hc.1 hc.2.1 (hP p hp).1 (hP p hp).2 (hg p).1))
      · exact h4 p hp (g p) h (hg p).1 (hg p).2.2.2 hsp)
  -- a path starts at a prime q such that every odd prime factor of q + 1 lies in N
  have hleaf : ∀ q ∈ P.filter (fun q => g q ∉ P),
      ∀ c : ℕ, c.Prime → c ≠ 2 → c ∣ q + 1 → c ∈ N := fun q hq => by
    obtain ⟨hqP, hgq⟩ := Finset.mem_filter.mp hq
    by_cases h : g q = 1
    · exact (hg q).2.1 h
    · exact absurd (hgP q hqP h) hgq
  have hLP : ∀ q ∈ P.filter (fun q => g q ∉ P), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hsplit := Finset.prod_filter_mul_prod_filter_not (P.filter (fun q => g q ∉ P))
    (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1) β
  have hs0 : (0 : ℚ) ≤ (N.card : ℚ) := Nat.cast_nonneg _
  have hzleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      1 / (1 - D) := by
    refine (Finset.prod_le_prod
      (fun q hq => (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le)
      (fun q hq => (hB q (hLP q (Finset.mem_filter.mp hq).1)).2)).trans ?_
    refine nleaf3 (fun z hz => ⟨(hN z hz).1, hNb z hz⟩) D hD1 hD _ (fun q hq => ?_)
    obtain ⟨hqL, hne⟩ := Finset.mem_filter.mp hq
    have hqP := hP q (hLP q hqL)
    have h2 : 2 ∣ q + 1 := by
      rcases hqP.1.eq_two_or_odd with h | h
      · exact absurd h hqP.2
      · omega
    have hn3 : ¬ 3 ∣ q + 1 := fun h3 => by
      have := T3 q (hLP q hqL) h3
      have h3N := hleaf q hqL 3 (by norm_num) (by norm_num) h3
      have := hNb 3 h3N
      omega
    have hq3 : ¬ 3 ∣ q := fun h3 => by
      have hq3' : q = 3 := ((Nat.prime_dvd_prime_iff_eq (by norm_num) hqP.1).mp h3).symm
      apply hne
      subst hq3'
      have hd : (3 + 1) / 2 ^ (3 + 1).factorization 2 ∣ 4 := Nat.ordCompl_dvd (3 + 1) 2
      have hodd : ¬ 2 ∣ (3 + 1) / 2 ^ (3 + 1).factorization 2 :=
        Nat.not_dvd_ordCompl Nat.prime_two (by norm_num)
      have hle := Nat.le_of_dvd (by norm_num) hd
      generalize (3 + 1) / 2 ^ (3 + 1).factorization 2 = d at hd hodd hle
      interval_cases d <;> omega
    exact ⟨h2, by omega, hne, hleaf q hqL⟩
  have hmleaves : ∏ q ∈ (P.filter (fun q => g q ∉ P)).filter
        (fun q => ¬ (q + 1) / 2 ^ (q + 1).factorization 2 ≠ 1), β q ≤
      (β 3 * β 7 * β 31 * β 127) * (β 8191 * (32768 / 32767)) := by
    refine mersenne_bound11 β _ (fun q hq => (hP q (hLP q (Finset.mem_filter.mp hq).1)).1)
      (fun q hq => ?_)
      (fun q hq => ⟨hβpos q (hLP q (Finset.mem_filter.mp hq).1),
        (hB q (hLP q (Finset.mem_filter.mp hq).1)).2⟩) h1 h8
    obtain ⟨hqL, hzd⟩ := Finset.mem_filter.mp hq
    have h1' : (q + 1) / 2 ^ (q + 1).factorization 2 = 1 := not_not.mp hzd
    have hmul := Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2
    rw [h1', mul_one] at hmul
    exact ⟨(q + 1).factorization 2, hmul.symm⟩
  have hM0 : (0 : ℚ) ≤ (β 3 * β 7 * β 31 * β 127) * (β 8191 * (32768 / 32767)) := by
    obtain ⟨a, b, c, d⟩ := h1
    have h3 : (0 : ℚ) ≤ β 3 := by linarith
    have h7 : (0 : ℚ) ≤ β 7 := by linarith
    have h31 : (0 : ℚ) ≤ β 31 := by linarith
    have h127 : (0 : ℚ) ≤ β 127 := by linarith
    have h8' : (0 : ℚ) ≤ β 8191 := by linarith
    positivity
  have hNL0 : (0 : ℚ) ≤ 1 / (1 - D) := div_nonneg zero_le_one (by linarith)
  have hprodL : ∏ q ∈ P.filter (fun q => g q ∉ P), β q ≤
      (1 / (1 - D)) *
        ((β 3 * β 7 * β 31 * β 127) * (β 8191 * (32768 / 32767))) := by
    rw [← hsplit]
    refine mul_le_mul hzleaves hmleaves ?_ hNL0
    exact Finset.prod_nonneg fun q hq =>
      (hβpos q (hLP q (Finset.mem_filter.mp hq).1)).le
  have hKq : (0 : ℚ) < K := by exact_mod_cast hK0
  have hEq : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
    have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) :=
      Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
    have hcast : ((2 : ℚ) ^ m + 1) * K' * ∏ p ∈ P, ((p : ℚ) + 1) =
        2 ^ (m + 1) * K * ∏ p ∈ P, (p : ℚ) := by
      have h := congrArg (Nat.cast : ℕ → ℚ) E
      push_cast at h
      exact h
    have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
      field_simp
    have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
    rw [e]
    field_simp
    rw [pow_succ] at hcast
    linarith
  have hT : 1 + 1 / (2 : ℚ) ^ m ≤ 1048577 / 1048576 := by
    have h2 : (2 : ℚ) ^ 20 ≤ (2 : ℚ) ^ m := pow_le_pow_right₀ (by norm_num) hm
    have : 1 / (2 : ℚ) ^ m ≤ 1 / (2 : ℚ) ^ 20 := one_div_le_one_div_of_le (by positivity) h2
    norm_num at this ⊢
    linarith
  have hKr0 : (0 : ℚ) ≤ (K' : ℚ) / K := div_nonneg (Nat.cast_nonneg _) hKq.le
  have hA : (1 + 1 / (2 : ℚ) ^ m) * ((K' : ℚ) / K) ≤ 1048577 / 1048576 * (1 + 1 / (2097 * 2100)) :=
    mul_le_mul hT hKr hKr0 (by norm_num)
  have hC := mul_le_mul hA (hpath.trans hprodL)
    (Finset.prod_nonneg fun p _ => by positivity) (by norm_num)
  have e2 : 1048577 / 1048576 * (1 + 1 / (2097 * 2100)) *
      ((1 / (1 - D)) *
        ((β 3 * β 7 * β 31 * β 127) * (β 8191 * (32768 / 32767)))) =
      1048577 / 1048576 * (β 3 * β 7 * β 31 * β 127) * (β 8191 * (32768 / 32767)) *
      ((1 + 1 / (2097 * 2100)) * (1 / (1 - D))) := by ring
  rw [hEq, e2] at hC
  linarith

-- The parent of 8191 (all odd prime factors of p + 1 at least 2100) is 16381, 262111 or ≥ 524223.
theorem T8191z {p : ℕ} (hp : p.Prime) (hd : 8191 ∣ p + 1)
    (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 2100 ≤ r) :
    p = 16381 ∨ p = 262111 ∨ 524223 ≤ p := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨hn1, hn2, hlt⟩ := hcon
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 5 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 5 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 8191 * 2 ^ e - 1 := by omega
    clear hj hd hmin hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp hn1 hn2 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 8191 * 2 ^ e * k, by rw [hj]; ring⟩
    have hr21 := hmin r hr hr2 hrp
    have h1 : 2100 ≤ 2 ^ e * (r * k) :=
      le_trans hr21 (le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0))
    generalize 2 ^ e * (r * k) = t at hj h1
    omega

-- The parent of 16381 (all odd prime factors of p + 1 at least 2100) is at least 1048383
-- (the numbers 32762 * 2^e - 1, e ≤ 4, are composite).
theorem T16381z {p : ℕ} (hp : p.Prime) (hd : 16381 ∣ p + 1)
    (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 2100 ≤ r) : 1048383 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 5 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 5 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 16381 * 2 ^ e - 1 := by omega
    clear hj hd hmin hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 16381 * 2 ^ e * k, by rw [hj]; ring⟩
    have hr21 := hmin r hr hr2 hrp
    have h1 : 2100 ≤ 2 ^ e * (r * k) :=
      le_trans hr21 (le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0))
    generalize 2 ^ e * (r * k) = t at hj h1
    omega

-- Admissibility with at least two primes gives ∏ (1 + 5/z) ≤ 2101/2097.
theorem adm_hY5 {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hc : 2 ≤ N.card)
    (hΛ : ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097) :
    ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 2101 / 2097 := by
  have hc' : (2 : ℚ) ≤ N.card := by exact_mod_cast hc
  refine (Finset.prod_le_prod (fun z _ => by positivity) (fun z hz => ?_)).trans hΛ
  have hq : (N.card : ℚ) + 3 ≤ z := by exact_mod_cast (hN z hz).2.2
  have hz0 : (0 : ℚ) < z := by linarith
  rw [le_div_iff₀ (by linarith)]
  have e : (1 + 5 / (z : ℚ)) * ((z : ℚ) - 2 - N.card) =
      (z : ℚ) + 3 - N.card - 5 * (2 + N.card) * (1 / (z : ℚ)) := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ 5 * (2 + (N.card : ℚ)) * (1 / (z : ℚ)) := by positivity
  linarith

-- From ∏ (1 + 5/z) ≤ 2101/2097 every z is at least 2622.
theorem ge_2622 {N : Finset ℕ} (hN0 : ∀ z ∈ N, z ≠ 0)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 2101 / 2097) : ∀ z ∈ N, 2622 ≤ z := by
  intro z hz
  have h1 : ∏ w ∈ ({z} : Finset ℕ), (1 + 5 / (w : ℚ)) ≤ ∏ w ∈ N, (1 + 5 / (w : ℚ)) :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.singleton_subset_iff.mpr hz)
      (fun w _ => by positivity)
      (fun w _ _ => by
        have : (0 : ℚ) ≤ 5 / (w : ℚ) := by positivity
        linarith)
  rw [Finset.prod_singleton] at h1
  by_contra hlt
  have hz' : (z : ℚ) ≤ 2621 := by exact_mod_cast (by omega : z ≤ 2621)
  have hz0 : z ≠ 0 := hN0 z hz
  have hzpos : (0 : ℚ) < z := by exact_mod_cast Nat.pos_of_ne_zero hz0
  have : (5 : ℚ) / 2621 ≤ 5 / (z : ℚ) := div_le_div_of_nonneg_left (by norm_num) hzpos hz'
  linarith

end Erdos1052C11

namespace Erdos1052C16

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main
open Erdos1052C7 Erdos1052C9 Erdos1052C11

-- 2-adic count, general form: if a subset A of P has 2^k ∣ ∏_A (p + 1) then k ≤ m + 1.
theorem two_pow_le {m K K' : ℕ} {N P A : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hN2 : 2 ∉ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hA : A ⊆ P) {k : ℕ} (hk : 2 ^ k ∣ ∏ p ∈ A, (p + 1)) : k ≤ m + 1 := by
  have hdvdA : ∏ p ∈ A, (p + 1) ∣ ∏ p ∈ P, (p + 1) := Finset.prod_dvd_prod_of_subset _ _ _ hA
  have hk' : 2 ^ k ∣ 2 ^ (m + 1) * (K * ∏ p ∈ P, p) := by
    rw [← mul_assoc, ← E]
    exact (hk.trans hdvdA).mul_left _
  have hK2 : ¬ 2 ∣ K := fun h2 => hN2 (hK 2 Nat.prime_two h2)
  have hP2 : ¬ 2 ∣ ∏ p ∈ P, p := fun h2 => by
    obtain ⟨p, hp, h2p⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp h2
    exact (hP p hp).2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (hP p hp).1).mp h2p).symm
  have hcop : Nat.Coprime 2 (K * ∏ p ∈ P, p) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (fun h2 => by
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
      · exact hK2 h
      · exact hP2 h)
  have h := (Nat.Coprime.pow_left k hcop).dvd_of_dvd_mul_right hk'
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp h


-- 2-adic count in the 223 family: 2^18 ∣ ∏ (p + 1) over 3, 5, 7, 19, 31, 223, so m ≥ 17, and with
-- 16 ∣ m and m not 32 mod 64 this gives m ≥ 48.
theorem m_ge_48_223 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hN2 : 2 ∉ N)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hA : ({3, 5, 7, 19, 31, 223} : Finset ℕ) ⊆ P) (h16 : 16 ∣ m) (h64 : m % 64 ≠ 32) :
    48 ≤ m := by
  have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223} : Finset ℕ), (p + 1) = 2 ^ 18 * 105 := by decide
  have h18 := two_pow_le hP hK hN2 E hA (Dvd.intro _ e1.symm)
  omega

-- Parent of 19 when every odd prime factor of p + 1 is 19, 223 or at least 920: at least 34959
-- (38 * 2^e - 1 is composite for e ≤ 9 except 37, 151, 607; 8474 * t - 1 is composite for t ≤ 4).
theorem T19a {p : ℕ} (hp : p.Prime) (hd : 19 ∣ p + 1) (hsq : ¬ 19 * 19 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 19 ∨ r = 223 ∨ 920 ≤ r)
    (h152 : 152 ≤ p) (h607 : p ≠ 607) : 34959 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 10 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 10 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 19 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h152 h607 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 19 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    have htk : 1 ≤ 2 ^ e * k := Nat.mul_le_mul he0 hk
    rcases hgap r hr hr2 hrp with h | h | h
    · subst h
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · subst h
      have hj' : p + 1 = 2 * 19 * 223 * (2 ^ e * k) := by rw [hj]; ring
      generalize 2 ^ e * k = t at hj' htk
      have ht : t < 5 := by omega
      obtain rfl : p = 2 * 19 * 223 * t - 1 := by omega
      clear hj hd hsq hgap hlt hp2 hmo he0 hrk hrp hk hm1 hj' h152 h607
      interval_cases t <;> revert hp <;> norm_num
    · generalize 2 ^ e * (r * k) = t at hj hrk
      omega

-- Parent of 1783 with every odd prime factor of p + 1 at least 1783: at least 228223
-- (3566 * 2^e - 1 is composite for e ≤ 5).
theorem T1783w {p : ℕ} (hp : p.Prime) (hd : 1783 ∣ p + 1) (hsq : ¬ 1783 * 1783 ∣ p + 1)
    (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 1783 ≤ r) : 228223 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 6 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 6 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 1783 * 2 ^ e - 1 := by omega
    clear hj hd hsq hmin hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 1783 * 2 ^ e * k, by rw [hj]; ring⟩
    have h1783 := hmin r hr hr2 hrp
    have hr1784 : 1784 ≤ r := by
      by_contra hc
      have heq : r = 1783 := by omega
      subst heq
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    have h1 : 1784 ≤ 2 ^ e * (r * k) :=
      le_trans hr1784 (le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0))
    generalize 2 ^ e * (r * k) = t at hj h1
    omega

-- The 223 family with 991 and without 607, 1783: impossible for a ≥ 20 (masterU; chains 3 ← 5 ← 19 with
-- parent of 19 at least 34959, 7 ← 223 with parent of 223 at least 213633, 31 ← 991 with parent of 991
-- at least 7927; every further simple prime is at least 920).
theorem node991 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (4 / 2097)))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 20 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h991 : 991 ∈ P) (h607 : 607 ∉ P) (h1783 : 1783 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 991 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 991 h991 hd (by norm_num)
  have hA : ({3, 5, 7, 19, 31, 223, 991} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h991
  have gap : ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → 920 ≤ q := by
    intro q hq e3 e5 e7 e19 e31 e223
    by_cases e991 : q = 991
    · omega
    have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 991} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 991} : Finset ℕ), (p + 1) = 27304919040 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 991} : Finset ℕ), p = 13667312085 := by decide
    rw [e1, e2] at h
    omega
  -- an odd prime factor r of p + 1 (p ∈ P): either r ∈ N (so r ≥ 2100) or r ∈ P
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      2100 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ 920 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hNb r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3
      · exact Or.inl e3
      by_cases e5 : r = 5
      · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7
      · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19
      · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (gap r hrP e3 e5 e7 e19 e31 e223))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (34960 / 34958))) else
      if p = 5 then 6 / 5 * (20 / 19 * (34960 / 34958)) else
      if p = 19 then 20 / 19 * (34960 / 34958) else
      if p = 7 then 8 / 7 * (224 / 223 * (213634 / 213632)) else
      if p = 223 then 224 / 223 * (213634 / 213632) else
      if p = 31 then 32 / 31 * (992 / 991 * (7928 / 7926)) else
      if p = 991 then 992 / 991 * (7928 / 7926) else
      if p = 8191 then 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) else
      if p = 16381 then 16382 / 16381 * (1048384 / 1048382) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (34960 / 34958))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (34960 / 34958)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (34960 / 34958) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (213634 / 213632)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (213634 / 213632) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (992 / 991 * (7928 / 7926)) := by rw [hβ]; norm_num
  have b991 : β 991 = 992 / 991 * (7928 / 7926) := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) := by rw [hβ]; norm_num
  have b16381 : β 16381 = 16382 / 16381 * (1048384 / 1048382) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 991 → c ≠ 8191 → c ≠ 16381 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e223 e31 e991 e8191 e16381 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e223, if_neg e31, if_neg e991, if_neg e8191, if_neg e16381, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e991 : p = 991
    · subst e991; rw [b991]; norm_num
    by_cases e8191 : p = 8191
    · subst e8191; rw [b8191]; norm_num
    by_cases e16381 : p = 16381
    · subst e16381; rw [b16381]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e223 e31 e991 e8191 e16381 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  -- every odd prime factor of p + 1 that is not in N is at least c, and the ones in N are ≥ 2100
  have hmin2100 : ∀ p ∈ P, ∀ c : ℕ, 2100 ≤ c →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 2100 ≤ r := fun p _ c hc hmin r hr hr2 hrd =>
    if hrN : r ∈ N then hNb r hrN else le_trans hc (hmin r hr hr2 hrN hrd)
  refine masterU hP hN hK hKr hNb (4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (4 / 2097))) (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      have hge : 34959 ≤ p := T19a (hP p hp).1 hd
        (S4b 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have h19r := hmin r hr hr2 hrN hrd
            rcases h with h | h | h | h | h | h | h
            · omega
            · omega
            · omega
            · exact Or.inl h
            · exfalso
              subst h
              have e991 : p = 991 := T31 p hp hrd
              subst e991
              norm_num at hd
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h))
        (by
          by_contra hlt
          rcases hs p hp (by omega) with rfl | rfl | rfl | rfl | rfl <;> norm_num at hd)
        (fun h => h607 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 34959) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 223 := T7 p hp hd
      rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 213633 ≤ p := T223y (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => h1783 (h ▸ hp))
      rw [b223]
      exact step_ge (t := 213633) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 991 := T31 p hp hd
      rw [b31, b991]; norm_num
    by_cases e991 : c = 991
    · subst e991
      have hge : 7927 ≤ p := T991 (hP p hp).1 hd
      rw [b991]
      exact step_ge (t := 7927) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e8191 : c = 8191
    · subst e8191
      rcases T8191z (hP p hp).1 hd (hmin2100 p hp 8191 (by norm_num) hmin) with rfl | rfl | hge
      · rw [b8191, b16381]; norm_num
      · rw [b8191, bd 262111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num
      · rw [b8191]
        exact step_ge (t := 524223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e16381 : c = 16381
    · subst e16381
      have hge : 1048383 ≤ p := T16381z (hP p hp).1 hd (hmin2100 p hp 16381 (by norm_num) hmin)
      rw [b16381]
      exact step_ge (t := 1048383) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e223 e31 e991 e8191 e16381 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b3, b7, b31, b127, b8191]; norm_num

-- The 223 family with 1783 and without 607, 991: impossible for a ≥ 20 (masterU; chains 3 ← 5 ← 19 with
-- parent of 19 at least 18201, 7 ← 223 ← 1783 with parent of 1783 at least 228223, 31 with parent at
-- least 3967; every further simple prime is at least 651).
theorem node1783 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (4 / 2097)))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 20 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h1783 : 1783 ∈ P) (h607 : 607 ∉ P) (h991 : 991 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T223 : ∀ p ∈ P, 223 ∣ p + 1 → p = 1783 := fun p hp hd =>
    S2 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1783 h1783 hd (by norm_num)
  have hA : ({3, 5, 7, 19, 31, 223, 1783} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h1783
  have gap : ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → 651 ≤ q := by
    intro q hq e3 e5 e7 e19 e31 e223
    by_cases e1783 : q = 1783
    · omega
    have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 1783} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 1783} : Finset ℕ), (p + 1) = 49104814080 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 1783} : Finset ℕ), p = 24590128605 := by decide
    rw [e1, e2] at h
    omega
  -- an odd prime factor r of p + 1 (p ∈ P): either r ∈ N (so r ≥ 2100) or r ∈ P
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      2100 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ 651 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hNb r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3
      · exact Or.inl e3
      by_cases e5 : r = 5
      · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7
      · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19
      · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (gap r hrP e3 e5 e7 e19 e31 e223))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (18202 / 18200))) else
      if p = 5 then 6 / 5 * (20 / 19 * (18202 / 18200)) else
      if p = 19 then 20 / 19 * (18202 / 18200) else
      if p = 7 then 8 / 7 * (224 / 223 * (1784 / 1783 * (228224 / 228222))) else
      if p = 223 then 224 / 223 * (1784 / 1783 * (228224 / 228222)) else
      if p = 1783 then 1784 / 1783 * (228224 / 228222) else
      if p = 31 then 32 / 31 * (3968 / 3966) else
      if p = 8191 then 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) else
      if p = 16381 then 16382 / 16381 * (1048384 / 1048382) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (18202 / 18200))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (18202 / 18200)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (18202 / 18200) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (1784 / 1783 * (228224 / 228222))) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (1784 / 1783 * (228224 / 228222)) := by rw [hβ]; norm_num
  have b1783 : β 1783 = 1784 / 1783 * (228224 / 228222) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3966) := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) := by rw [hβ]; norm_num
  have b16381 : β 16381 = 16382 / 16381 * (1048384 / 1048382) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 223 → c ≠ 1783 → c ≠ 31 → c ≠ 8191 → c ≠ 16381 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e223 e1783 e31 e8191 e16381 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e223, if_neg e1783, if_neg e31, if_neg e8191, if_neg e16381, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e1783 : p = 1783
    · subst e1783; rw [b1783]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e8191 : p = 8191
    · subst e8191; rw [b8191]; norm_num
    by_cases e16381 : p = 16381
    · subst e16381; rw [b16381]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e223 e1783 e31 e8191 e16381 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  -- every odd prime factor of p + 1 that is not in N is at least c, and the ones in N are ≥ 2100
  have hmin2100 : ∀ p ∈ P, ∀ c : ℕ, 2100 ≤ c →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 2100 ≤ r := fun p _ c hc hmin r hr hr2 hrd =>
    if hrN : r ∈ N then hNb r hrN else le_trans hc (hmin r hr hr2 hrN hrd)
  refine masterU hP hN hK hKr hNb (4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (4 / 2097))) (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      have hge : 18201 ≤ p := T19y (hP p hp).1 hd
        (S4b 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => if hrN : r ∈ N then by have := hNb r hrN; omega
          else hmin r hr hr2 hrN hrd)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (by
          by_contra hlt
          rcases hs p hp (by omega) with rfl | rfl | rfl | rfl | rfl <;> norm_num at hd)
        (fun h => h607 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 18201) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 223 := T7 p hp hd
      rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      obtain rfl : p = 1783 := T223 p hp hd
      rw [b223, b1783]; norm_num
    by_cases e1783 : c = 1783
    · subst e1783
      have hge : 228223 ≤ p := T1783w (hP p hp).1 hd
        (S4b 1783 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => if hrN : r ∈ N then by have := hNb r hrN; omega
          else hmin r hr hr2 hrN hrd)
      rw [b1783]
      exact step_ge (t := 228223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      have hge : 3967 ≤ p := T31y (hP p hp).1 hd
        (S4b 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => by
          have := hs 61 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h991 (h ▸ hp))
      rw [b31]
      exact step_ge (t := 3967) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e8191 : c = 8191
    · subst e8191
      rcases T8191z (hP p hp).1 hd (hmin2100 p hp 8191 (by norm_num) hmin) with rfl | rfl | hge
      · rw [b8191, b16381]; norm_num
      · rw [b8191, bd 262111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num
      · rw [b8191]
        exact step_ge (t := 524223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e16381 : c = 16381
    · subst e16381
      have hge : 1048383 ≤ p := T16381z (hP p hp).1 hd (hmin2100 p hp 16381 (by norm_num) hmin)
      rw [b16381]
      exact step_ge (t := 1048383) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e223 e1783 e31 e8191 e16381 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b3, b7, b31, b127, b8191]; norm_num

-- Parent of 991 other than 7927, with every odd prime factor of p + 1 at least 991: at least 126847
-- (1982 * 2^e - 1 is composite for e ≤ 5 except 7927).
theorem T991c {p : ℕ} (hp : p.Prime) (hd : 991 ∣ p + 1) (hsq : ¬ 991 * 991 ∣ p + 1)
    (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 991 ≤ r) (h7927 : p ≠ 7927) : 126847 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 6 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 6 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 991 * 2 ^ e - 1 := by omega
    clear hj hd hsq hmin hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h7927 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 991 * 2 ^ e * k, by rw [hj]; ring⟩
    have h991 := hmin r hr hr2 hrp
    have hr992 : 992 ≤ r := by
      by_contra hc
      have heq : r = 991 := by omega
      subst heq
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    have h1 : 992 ≤ 2 ^ e * (r * k) :=
      le_trans hr992 (le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0))
    generalize 2 ^ e * (r * k) = t at hj h1
    omega

-- Parent of 7927 with every odd prime factor of p + 1 at least 7927: at least 1014655
-- (15854 * 2^e - 1 is composite for e ≤ 5).
theorem T7927w {p : ℕ} (hp : p.Prime) (hd : 7927 ∣ p + 1) (hsq : ¬ 7927 * 7927 ∣ p + 1)
    (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 7927 ≤ r) : 1014655 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 6 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 6 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 7927 * 2 ^ e - 1 := by omega
    clear hj hd hsq hmin hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 7927 * 2 ^ e * k, by rw [hj]; ring⟩
    have h7927 := hmin r hr hr2 hrp
    have hr7928 : 7928 ≤ r := by
      by_contra hc
      have heq : r = 7927 := by omega
      subst heq
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    have h1 : 7928 ≤ 2 ^ e * (r * k) :=
      le_trans hr7928 (le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0))
    generalize 2 ^ e * (r * k) = t at hj h1
    omega

-- Parent of 607 other than 1213, with every odd prime factor of p + 1 at least 607: at least 19423
-- (1214 * 2^e - 1 is composite for e ≤ 3 except 1213).
theorem T607c {p : ℕ} (hp : p.Prime) (hd : 607 ∣ p + 1) (hsq : ¬ 607 * 607 ∣ p + 1)
    (hmin : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 607 ≤ r) (h1213 : p ≠ 1213) : 19423 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 4 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 4 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 607 * 2 ^ e - 1 := by omega
    clear hj hd hsq hmin hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h1213 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 607 * 2 ^ e * k, by rw [hj]; ring⟩
    have h607 := hmin r hr hr2 hrp
    have hr608 : 608 ≤ r := by
      by_contra hc
      have heq : r = 607 := by omega
      subst heq
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    have h1 : 608 ≤ 2 ^ e * (r * k) :=
      le_trans hr608 (le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0))
    generalize 2 ^ e * (r * k) = t at hj h1
    omega

-- Parent of 31 other than 61, 991, 3967 when every odd prime factor of p + 1 is 31, 223, 607 or at
-- least 2100: at least 37633 (62 * 2^e - 1 is composite for e ≤ 9 except 61, 991, 3967;
-- 13826 * t - 1 is composite for t ≤ 2; 37633 = 2 * 31 * 607 - 1 is prime).
theorem T31c {p : ℕ} (hp : p.Prime) (hd : 31 ∣ p + 1) (hsq : ¬ 31 * 31 ∣ p + 1)
    (hgap : ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → r = 31 ∨ r = 223 ∨ r = 607 ∨ 2100 ≤ r)
    (h61 : p ≠ 61) (h991 : p ≠ 991) (h3967 : p ≠ 3967) : 37633 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  obtain ⟨e, m, hmo, hj⟩ := split_odd hp hp2 (by norm_num) hd
  have he0 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at hj
    have hlt2 : 2 ^ e < 2 ^ 10 := by
      generalize 2 ^ e = t at hj
      norm_num
      omega
    have he : e < 10 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt2
    obtain rfl : p = 2 * 31 * 2 ^ e - 1 := by omega
    clear hj hd hsq hgap hlt hp2 hmo he0 hlt2
    interval_cases e <;> revert hp h61 h991 h3967 <;> norm_num
  · obtain ⟨r, k, hr, hr2, rfl, hk⟩ := odd_prime_factor hmo hm1
    have hrp : r ∣ p + 1 := ⟨2 * 31 * 2 ^ e * k, by rw [hj]; ring⟩
    have hrk : r ≤ 2 ^ e * (r * k) :=
      le_trans (Nat.le_mul_of_pos_right r hk) (Nat.le_mul_of_pos_left _ he0)
    have htk : 1 ≤ 2 ^ e * k := Nat.mul_le_mul he0 hk
    rcases hgap r hr hr2 hrp with h | h | h | h
    · subst h
      exact hsq ⟨2 * 2 ^ e * k, by rw [hj]; ring⟩
    · subst h
      have hj' : p + 1 = 2 * 31 * 223 * (2 ^ e * k) := by rw [hj]; ring
      generalize 2 ^ e * k = t at hj' htk
      have ht : t < 3 := by omega
      obtain rfl : p = 2 * 31 * 223 * t - 1 := by omega
      clear hj hd hsq hgap hlt hp2 hmo he0 hrk hrp hk hm1 hj' h61 h991 h3967
      interval_cases t <;> revert hp <;> norm_num
    · subst h
      have hj' : p + 1 = 2 * 31 * 607 * (2 ^ e * k) := by rw [hj]; ring
      generalize 2 ^ e * k = t at hj' htk
      omega
    · generalize 2 ^ e * (r * k) = t at hj hrk
      omega

-- Σ x(u) over N-smooth u > 1 when every z ∈ N is ≥ 2622 and ∏ (1 + 5/z) ≤ 2501/2500 (the proof of
-- sumD_two with a smaller constant).
theorem sumD_eta {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 2622 ≤ z)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 2501 / 2500) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) :
    ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 2500)) := by
  have hUge : ∀ u ∈ U, 2622 ≤ u := fun u hu' => by
    obtain ⟨h0, h1, hr⟩ := hU u hu'
    have hmem := hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u)
    have := (hN _ hmem).2
    have := Nat.minFac_le (Nat.pos_of_ne_zero h0)
    omega
  have hstep : ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      ∑ u ∈ U, 4 / 3 * (7866 / 7862) * (1 / (u : ℚ)) := by
    refine Finset.sum_le_sum fun u hu' => ?_
    have h := xw_le (c := 2622) (by norm_num) (hUge u hu')
    norm_num at h ⊢
    exact h
  rw [← Finset.mul_sum] at hstep
  have hσ : ∑ u ∈ U, 1 / (u : ℚ) ≤ 1 / 5 * (2622 / 2621) * (1 / 2500) := by
    have h1U : 1 ∉ U := fun h => (hU 1 h).2.1 rfl
    have hs := smooth_recip N (fun z hz => (hN z hz).1) (insert 1 U) (fun u hu' => by
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
            have := hr.two_le
            omega)⟩
        · obtain ⟨h0, _, hr⟩ := hU u hu'
          exact ⟨h0, hr⟩)
    rw [Finset.sum_insert h1U] at hs
    have hprod : ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) ≤
        ∏ z ∈ N, (1 + 1 / 5 * (2622 / 2621) * (5 / (z : ℚ))) := by
      refine Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)
      · have : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        exact div_nonneg (by linarith) (by linarith)
      · have h : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        have e : (1 : ℚ) / 5 * (2622 / 2621) * (5 / (z : ℚ)) = 2622 / (2621 * (z : ℚ)) := by
          field_simp
        rw [e, div_le_iff₀ (by linarith)]
        have : (1 + 2622 / (2621 * (z : ℚ))) * ((z : ℚ) - 1) = (z : ℚ) - 1 + 2622 / 2621 -
            2622 / (2621 * (z : ℚ)) := by
          field_simp
          ring
        rw [this]
        have : 2622 / (2621 * (z : ℚ)) ≤ 1 / 2621 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        linarith
    have hL2 := prod_one_add_mul_le N (fun z => 5 / (z : ℚ)) (1 / 5 * (2622 / 2621))
      (by norm_num) (by norm_num)
      (fun z hz => by
        have : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        positivity)
    simp only [Nat.cast_one, div_one] at hs
    have hfin := hs.trans (hprod.trans hL2)
    have h0 : (0 : ℚ) ≤ 1 / 5 * (2622 / 2621) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left (show ∏ z ∈ N, (1 + 5 / (z : ℚ)) - 1 ≤ 2501 / 2500 - 1 by
      linarith) h0]
  refine hstep.trans ?_
  have h0 : (0 : ℚ) ≤ 4 / 3 * (7866 / 7862) := by norm_num
  have := mul_le_mul_of_nonneg_left hσ h0
  linarith

-- Σ x(u) over N-smooth u > 1 when every z ∈ N is ≥ 2622 and ∏ (1 + 5/z) ≤ 5001/5000 (the proof of
-- sumD_two with a smaller constant).
theorem sumD_thin {N : Finset ℕ} (hN : ∀ z ∈ N, z.Prime ∧ 2622 ≤ z)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000) (U : Finset ℕ)
    (hU : ∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) :
    ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000)) := by
  have hUge : ∀ u ∈ U, 2622 ≤ u := fun u hu' => by
    obtain ⟨h0, h1, hr⟩ := hU u hu'
    have hmem := hr _ (Nat.minFac_prime h1) (Nat.minFac_dvd u)
    have := (hN _ hmem).2
    have := Nat.minFac_le (Nat.pos_of_ne_zero h0)
    omega
  have hstep : ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤
      ∑ u ∈ U, 4 / 3 * (7866 / 7862) * (1 / (u : ℚ)) := by
    refine Finset.sum_le_sum fun u hu' => ?_
    have h := xw_le (c := 2622) (by norm_num) (hUge u hu')
    norm_num at h ⊢
    exact h
  rw [← Finset.mul_sum] at hstep
  have hσ : ∑ u ∈ U, 1 / (u : ℚ) ≤ 1 / 5 * (2622 / 2621) * (1 / 5000) := by
    have h1U : 1 ∉ U := fun h => (hU 1 h).2.1 rfl
    have hs := smooth_recip N (fun z hz => (hN z hz).1) (insert 1 U) (fun u hu' => by
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact ⟨one_ne_zero, fun r hr hd => absurd (Nat.le_of_dvd one_pos hd) (by
            have := hr.two_le
            omega)⟩
        · obtain ⟨h0, _, hr⟩ := hU u hu'
          exact ⟨h0, hr⟩)
    rw [Finset.sum_insert h1U] at hs
    have hprod : ∏ z ∈ N, ((z : ℚ) / ((z : ℚ) - 1)) ≤
        ∏ z ∈ N, (1 + 1 / 5 * (2622 / 2621) * (5 / (z : ℚ))) := by
      refine Finset.prod_le_prod (fun z hz => ?_) (fun z hz => ?_)
      · have : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        exact div_nonneg (by linarith) (by linarith)
      · have h : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        have e : (1 : ℚ) / 5 * (2622 / 2621) * (5 / (z : ℚ)) = 2622 / (2621 * (z : ℚ)) := by
          field_simp
        rw [e, div_le_iff₀ (by linarith)]
        have : (1 + 2622 / (2621 * (z : ℚ))) * ((z : ℚ) - 1) = (z : ℚ) - 1 + 2622 / 2621 -
            2622 / (2621 * (z : ℚ)) := by
          field_simp
          ring
        rw [this]
        have : 2622 / (2621 * (z : ℚ)) ≤ 1 / 2621 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
        linarith
    have hL2 := prod_one_add_mul_le N (fun z => 5 / (z : ℚ)) (1 / 5 * (2622 / 2621))
      (by norm_num) (by norm_num)
      (fun z hz => by
        have : (2622 : ℚ) ≤ z := by exact_mod_cast (hN z hz).2
        positivity)
    simp only [Nat.cast_one, div_one] at hs
    have hfin := hs.trans (hprod.trans hL2)
    have h0 : (0 : ℚ) ≤ 1 / 5 * (2622 / 2621) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left (show ∏ z ∈ N, (1 + 5 / (z : ℚ)) - 1 ≤ 5001 / 5000 - 1 by
      linarith) h0]
  refine hstep.trans ?_
  have h0 : (0 : ℚ) ≤ 4 / 3 * (7866 / 7862) := by norm_num
  have := mul_le_mul_of_nonneg_left hσ h0
  linarith

-- From ∏ (1 + 5/z) ≤ 2501/2500 every z is at least 12500.
theorem ge_12500 {N : Finset ℕ} (hN0 : ∀ z ∈ N, z ≠ 0)
    (hY5 : ∏ z ∈ N, (1 + 5 / (z : ℚ)) ≤ 2501 / 2500) : ∀ z ∈ N, 12500 ≤ z := by
  intro z hz
  have h1 : ∏ w ∈ ({z} : Finset ℕ), (1 + 5 / (w : ℚ)) ≤ ∏ w ∈ N, (1 + 5 / (w : ℚ)) :=
    Finset.prod_le_prod_of_subset_of_one_le (Finset.singleton_subset_iff.mpr hz)
      (fun w _ => by positivity)
      (fun w _ _ => by
        have : (0 : ℚ) ≤ 5 / (w : ℚ) := by positivity
        linarith)
  rw [Finset.prod_singleton] at h1
  by_contra hlt
  have hz' : (z : ℚ) ≤ 12499 := by exact_mod_cast (by omega : z ≤ 12499)
  have hz0 : z ≠ 0 := hN0 z hz
  have hzpos : (0 : ℚ) < z := by exact_mod_cast Nat.pos_of_ne_zero hz0
  have : (5 : ℚ) / 12499 ≤ 5 / (z : ℚ) := div_le_div_of_nonneg_left (by norm_num) hzpos hz'
  linarith

-- The 223 family with 991 and 1783, without 607, with 7927 not simple, and with a thin kernel
-- (leaf constant D for prod (1 + 5/z) ≤ 2501/2500): impossible for a ≥ 20 (masterU; chains 3 ← 5 ← 19 with
-- parent of 19 at least 34959, 7 ← 223 ← 1783 with parent of 1783 at least 228223, 31 ← 991 with parent
-- of 991 at least 126847; total 1.99975725).
theorem node_pair_out {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 2500)))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 20 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h991 : 991 ∈ P) (h1783 : 1783 ∈ P) (h607 : 607 ∉ P) (h7927 : 7927 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 991 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 991 h991 hd (by norm_num)
  have T223 : ∀ p ∈ P, 223 ∣ p + 1 → p = 1783 := fun p hp hd =>
    S2 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1783 h1783 hd (by norm_num)
  have hA : ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h991
    · exact h1783
  have gap : ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → 920 ≤ q := by
    intro q hq e3 e5 e7 e19 e31 e223
    by_cases e991 : q = 991
    · omega
    by_cases e1783 : q = 1783
    · omega
    have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ), (p + 1) = 48711975567360 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ), p = 24368817447555 := by decide
    rw [e1, e2] at h
    omega
  -- an odd prime factor r of p + 1 (p ∈ P): either r ∈ N (so r ≥ 2100) or r ∈ P
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      2100 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ 920 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hNb r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3
      · exact Or.inl e3
      by_cases e5 : r = 5
      · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7
      · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19
      · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (gap r hrP e3 e5 e7 e19 e31 e223))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (34960 / 34958))) else
      if p = 5 then 6 / 5 * (20 / 19 * (34960 / 34958)) else
      if p = 19 then 20 / 19 * (34960 / 34958) else
      if p = 7 then 8 / 7 * (224 / 223 * (1784 / 1783 * (228224 / 228222))) else
      if p = 223 then 224 / 223 * (1784 / 1783 * (228224 / 228222)) else
      if p = 1783 then 1784 / 1783 * (228224 / 228222) else
      if p = 31 then 32 / 31 * (992 / 991 * (126848 / 126846)) else
      if p = 991 then 992 / 991 * (126848 / 126846) else
      if p = 8191 then 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) else
      if p = 16381 then 16382 / 16381 * (1048384 / 1048382) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (34960 / 34958))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (34960 / 34958)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (34960 / 34958) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (1784 / 1783 * (228224 / 228222))) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (1784 / 1783 * (228224 / 228222)) := by rw [hβ]; norm_num
  have b1783 : β 1783 = 1784 / 1783 * (228224 / 228222) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (992 / 991 * (126848 / 126846)) := by rw [hβ]; norm_num
  have b991 : β 991 = 992 / 991 * (126848 / 126846) := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) := by rw [hβ]; norm_num
  have b16381 : β 16381 = 16382 / 16381 * (1048384 / 1048382) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 223 → c ≠ 1783 → c ≠ 31 → c ≠ 991 → c ≠ 8191 → c ≠ 16381 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e223 e1783 e31 e991 e8191 e16381 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e223, if_neg e1783, if_neg e31, if_neg e991, if_neg e8191, if_neg e16381, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e1783 : p = 1783
    · subst e1783; rw [b1783]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e991 : p = 991
    · subst e991; rw [b991]; norm_num
    by_cases e8191 : p = 8191
    · subst e8191; rw [b8191]; norm_num
    by_cases e16381 : p = 16381
    · subst e16381; rw [b16381]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e223 e1783 e31 e991 e8191 e16381 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  -- every odd prime factor of p + 1 that is not in N is at least c, and the ones in N are ≥ 2100
  have hmin2100 : ∀ p ∈ P, ∀ c : ℕ, 2100 ≤ c →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 2100 ≤ r := fun p _ c hc hmin r hr hr2 hrd =>
    if hrN : r ∈ N then hNb r hrN else le_trans hc (hmin r hr hr2 hrN hrd)
  refine masterU hP hN hK hKr hNb (4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 2500))) (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      have hge : 34959 ≤ p := T19a (hP p hp).1 hd
        (S4b 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have h19r := hmin r hr hr2 hrN hrd
            rcases h with h | h | h | h | h | h | h
            · omega
            · omega
            · omega
            · exact Or.inl h
            · exfalso
              subst h
              have e991 : p = 991 := T31 p hp hrd
              subst e991
              norm_num at hd
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h))
        (by
          by_contra hlt
          rcases hs p hp (by omega) with rfl | rfl | rfl | rfl | rfl <;> norm_num at hd)
        (fun h => h607 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 34959) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 223 := T7 p hp hd
      rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      obtain rfl : p = 1783 := T223 p hp hd
      rw [b223, b1783]; norm_num
    by_cases e1783 : c = 1783
    · subst e1783
      have hge : 228223 ≤ p := T1783w (hP p hp).1 hd
        (S4b 1783 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => if hrN : r ∈ N then by have := hNb r hrN; omega
          else hmin r hr hr2 hrN hrd)
      rw [b1783]
      exact step_ge (t := 228223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 991 := T31 p hp hd
      rw [b31, b991]; norm_num
    by_cases e991 : c = 991
    · subst e991
      have hge : 126847 ≤ p := T991c (hP p hp).1 hd
        (S4b 991 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => if hrN : r ∈ N then by have := hNb r hrN; omega
          else hmin r hr hr2 hrN hrd)
        (fun h => h7927 (h ▸ hp))
      rw [b991]
      exact step_ge (t := 126847) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e8191 : c = 8191
    · subst e8191
      rcases T8191z (hP p hp).1 hd (hmin2100 p hp 8191 (by norm_num) hmin) with rfl | rfl | hge
      · rw [b8191, b16381]; norm_num
      · rw [b8191, bd 262111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num
      · rw [b8191]
        exact step_ge (t := 524223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e16381 : c = 16381
    · subst e16381
      have hge : 1048383 ≤ p := T16381z (hP p hp).1 hd (hmin2100 p hp 16381 (by norm_num) hmin)
      rw [b16381]
      exact step_ge (t := 1048383) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e223 e1783 e31 e991 e8191 e16381 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b3, b7, b31, b127, b8191]; norm_num

-- The 223 family with 991, 1783 and 7927 simple, without 607, with a thin kernel (leaf constant D for
-- prod (1 + 5/z) ≤ 2501/2500): impossible for a ≥ 20 (masterU; chains 3 ← 5 ← 19 with parent of 19 at
-- least 34959, 7 ← 223 ← 1783 with parent of 1783 at least 228223, 31 ← 991 ← 7927 with parent of 7927
-- at least 1014655; total 1.99998193).
theorem node_pair_in {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 2500)))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 20 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h991 : 991 ∈ P) (h1783 : 1783 ∈ P) (h7927 : 7927 ∈ P) (h7927N : 7927 ∉ N)
    (hN7 : ∀ z ∈ N, 7927 ≤ z) (h607 : 607 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 991 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 991 h991 hd (by norm_num)
  have T223 : ∀ p ∈ P, 223 ∣ p + 1 → p = 1783 := fun p hp hd =>
    S2 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1783 h1783 hd (by norm_num)
  have T991p : ∀ p ∈ P, 991 ∣ p + 1 → p = 7927 := fun p hp hd =>
    S2 991 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 7927 h7927 hd (by norm_num)
  have hA : ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h991
    · exact h1783
  have gap : ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → 920 ≤ q := by
    intro q hq e3 e5 e7 e19 e31 e223
    by_cases e991 : q = 991
    · omega
    by_cases e1783 : q = 1783
    · omega
    have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ), (p + 1) = 48711975567360 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ), p = 24368817447555 := by decide
    rw [e1, e2] at h
    omega
  -- an odd prime factor r of p + 1 (p ∈ P): either r ∈ N (so r ≥ 2100) or r ∈ P
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      2100 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ 920 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hNb r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3
      · exact Or.inl e3
      by_cases e5 : r = 5
      · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7
      · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19
      · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (gap r hrP e3 e5 e7 e19 e31 e223))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (34960 / 34958))) else
      if p = 5 then 6 / 5 * (20 / 19 * (34960 / 34958)) else
      if p = 19 then 20 / 19 * (34960 / 34958) else
      if p = 7 then 8 / 7 * (224 / 223 * (1784 / 1783 * (228224 / 228222))) else
      if p = 223 then 224 / 223 * (1784 / 1783 * (228224 / 228222)) else
      if p = 1783 then 1784 / 1783 * (228224 / 228222) else
      if p = 31 then 32 / 31 * (992 / 991 * (7928 / 7927 * (1014656 / 1014654))) else
      if p = 991 then 992 / 991 * (7928 / 7927 * (1014656 / 1014654)) else
      if p = 7927 then 7928 / 7927 * (1014656 / 1014654) else
      if p = 8191 then 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) else
      if p = 16381 then 16382 / 16381 * (1048384 / 1048382) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (34960 / 34958))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (34960 / 34958)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (34960 / 34958) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (1784 / 1783 * (228224 / 228222))) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (1784 / 1783 * (228224 / 228222)) := by rw [hβ]; norm_num
  have b1783 : β 1783 = 1784 / 1783 * (228224 / 228222) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (992 / 991 * (7928 / 7927 * (1014656 / 1014654))) := by rw [hβ]; norm_num
  have b991 : β 991 = 992 / 991 * (7928 / 7927 * (1014656 / 1014654)) := by rw [hβ]; norm_num
  have b7927 : β 7927 = 7928 / 7927 * (1014656 / 1014654) := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) := by rw [hβ]; norm_num
  have b16381 : β 16381 = 16382 / 16381 * (1048384 / 1048382) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 223 → c ≠ 1783 → c ≠ 31 → c ≠ 991 → c ≠ 7927 → c ≠ 8191 → c ≠ 16381 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e223 e1783 e31 e991 e7927 e8191 e16381 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e223, if_neg e1783, if_neg e31, if_neg e991, if_neg e7927, if_neg e8191, if_neg e16381, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e1783 : p = 1783
    · subst e1783; rw [b1783]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e991 : p = 991
    · subst e991; rw [b991]; norm_num
    by_cases e7927 : p = 7927
    · subst e7927; rw [b7927]; norm_num
    by_cases e8191 : p = 8191
    · subst e8191; rw [b8191]; norm_num
    by_cases e16381 : p = 16381
    · subst e16381; rw [b16381]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e223 e1783 e31 e991 e7927 e8191 e16381 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  -- every odd prime factor of p + 1 that is not in N is at least c, and the ones in N are ≥ 2100
  have hmin2100 : ∀ p ∈ P, ∀ c : ℕ, 2100 ≤ c →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 2100 ≤ r := fun p _ c hc hmin r hr hr2 hrd =>
    if hrN : r ∈ N then hNb r hrN else le_trans hc (hmin r hr hr2 hrN hrd)
  refine masterU hP hN hK hKr hNb (4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 2500))) (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      have hge : 34959 ≤ p := T19a (hP p hp).1 hd
        (S4b 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have h19r := hmin r hr hr2 hrN hrd
            rcases h with h | h | h | h | h | h | h
            · omega
            · omega
            · omega
            · exact Or.inl h
            · exfalso
              subst h
              have e991 : p = 991 := T31 p hp hrd
              subst e991
              norm_num at hd
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h))
        (by
          by_contra hlt
          rcases hs p hp (by omega) with rfl | rfl | rfl | rfl | rfl <;> norm_num at hd)
        (fun h => h607 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 34959) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 223 := T7 p hp hd
      rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      obtain rfl : p = 1783 := T223 p hp hd
      rw [b223, b1783]; norm_num
    by_cases e1783 : c = 1783
    · subst e1783
      have hge : 228223 ≤ p := T1783w (hP p hp).1 hd
        (S4b 1783 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => if hrN : r ∈ N then by have := hNb r hrN; omega
          else hmin r hr hr2 hrN hrd)
      rw [b1783]
      exact step_ge (t := 228223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 991 := T31 p hp hd
      rw [b31, b991]; norm_num
    by_cases e991 : c = 991
    · subst e991
      obtain rfl : p = 7927 := T991p p hp hd
      rw [b991, b7927]; norm_num
    by_cases e7927 : c = 7927
    · subst e7927
      have hge : 1014655 ≤ p := T7927w (hP p hp).1 hd
        (S4b 7927 (by norm_num) (by norm_num) h7927N p hp)
        (fun r hr hr2 hrd => if hrN : r ∈ N then hN7 r hrN else hmin r hr hr2 hrN hrd)
      rw [b7927]
      exact step_ge (t := 1014655) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e8191 : c = 8191
    · subst e8191
      rcases T8191z (hP p hp).1 hd (hmin2100 p hp 8191 (by norm_num) hmin) with rfl | rfl | hge
      · rw [b8191, b16381]; norm_num
      · rw [b8191, bd 262111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num
      · rw [b8191]
        exact step_ge (t := 524223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e16381 : c = 16381
    · subst e16381
      have hge : 1048383 ≤ p := T16381z (hP p hp).1 hd (hmin2100 p hp 16381 (by norm_num) hmin)
      rw [b16381]
      exact step_ge (t := 1048383) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e223 e1783 e31 e991 e7927 e8191 e16381 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b3, b7, b31, b127, b8191]; norm_num

-- The 223 family with 607, without 3967, with a thin kernel (leaf constant D for prod (1 + 5/z) ≤
-- 5001/5000): impossible for a ≥ 20 (masterU; chains 3 ← 5 ← 19 ← 607 with parent of 607 at least 19423,
-- 7 ← 223 with parent of 223 at least 213633, 31 with parent at least 37633; every further simple prime
-- is at least 2223; total 1.99997159).
theorem node607_thin {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) (hKK1 : K ≤ K')
    (hNb : ∀ z ∈ N, 2100 ≤ z)
    (hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ N) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000)))
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 20 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (m3 : 3 ∈ P) (m5 : 5 ∈ P) (m7 : 7 ∈ P) (m19 : 19 ∈ P) (m31 : 31 ∈ P)
    (h223 : 223 ∈ P) (h607 : 607 ∈ P) (h3967 : 3967 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 223 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 223 h223 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have hA : ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact h223
    · exact h607
  have gap : ∀ q ∈ P, q ≠ 3 → q ≠ 5 → q ≠ 7 → q ≠ 19 → q ≠ 31 → q ≠ 223 → q ≠ 607 → 2223 ≤ q := by
    intro q hq e3 e5 e7 e19 e31 e223 e607
    have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
    rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
    have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ), (p + 1) = 16735272960 := by decide
    have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ), p = 8371401045 := by decide
    rw [e1, e2] at h
    omega
  -- an odd prime factor r of p + 1 (p ∈ P): either r ∈ N (so r ≥ 2100) or r ∈ P
  have fac : ∀ p ∈ P, ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 →
      2100 ≤ r ∨ (r ∉ N ∧ (r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 19 ∨ r = 31 ∨ r = 223 ∨ r = 607 ∨ 2223 ≤ r)) := by
    intro p hp r hr hr2 hrd
    by_cases hrN : r ∈ N
    · exact Or.inl (hNb r hrN)
    · right
      refine ⟨hrN, ?_⟩
      have hrP := S1 r hr hr2 hrN p hp hrd
      by_cases e3 : r = 3
      · exact Or.inl e3
      by_cases e5 : r = 5
      · exact Or.inr (Or.inl e5)
      by_cases e7 : r = 7
      · exact Or.inr (Or.inr (Or.inl e7))
      by_cases e19 : r = 19
      · exact Or.inr (Or.inr (Or.inr (Or.inl e19)))
      by_cases e31 : r = 31
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e31))))
      by_cases e223 : r = 223
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e223)))))
      by_cases e607 : r = 607
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e607))))))
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (gap r hrP e3 e5 e7 e19 e31 e223 e607)))))))
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (19424 / 19422)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (19424 / 19422))) else
      if p = 19 then 20 / 19 * (608 / 607 * (19424 / 19422)) else
      if p = 607 then 608 / 607 * (19424 / 19422) else
      if p = 7 then 8 / 7 * (224 / 223 * (213634 / 213632)) else
      if p = 223 then 224 / 223 * (213634 / 213632) else
      if p = 31 then 32 / 31 * (37634 / 37632) else
      if p = 8191 then 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) else
      if p = 16381 then 16382 / 16381 * (1048384 / 1048382) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (19424 / 19422)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (19424 / 19422))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (19424 / 19422)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (19424 / 19422) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (224 / 223 * (213634 / 213632)) := by rw [hβ]; norm_num
  have b223 : β 223 = 224 / 223 * (213634 / 213632) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (37634 / 37632) := by rw [hβ]; norm_num
  have b8191 : β 8191 = 8192 / 8191 * (16382 / 16381 * (1048384 / 1048382)) := by rw [hβ]; norm_num
  have b16381 : β 16381 = 16382 / 16381 * (1048384 / 1048382) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 223 → c ≠ 31 → c ≠ 8191 → c ≠ 16381 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e223 e31 e8191 e16381 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e223, if_neg e31, if_neg e8191, if_neg e16381, if_neg e127]
  have hB : ∀ p ∈ P, 1 + 1 / (p : ℚ) ≤ β p ∧ β p ≤ ((p : ℚ) + 1) / ((p : ℚ) - 1) := by
    intro p hp
    by_cases e3 : p = 3
    · subst e3; rw [b3]; norm_num
    by_cases e5 : p = 5
    · subst e5; rw [b5]; norm_num
    by_cases e19 : p = 19
    · subst e19; rw [b19]; norm_num
    by_cases e607 : p = 607
    · subst e607; rw [b607]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e223 : p = 223
    · subst e223; rw [b223]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e8191 : p = 8191
    · subst e8191; rw [b8191]; norm_num
    by_cases e16381 : p = 16381
    · subst e16381; rw [b16381]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e7 e223 e31 e8191 e16381 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
  -- every odd prime factor of p + 1 that is not in N is at least c, and the ones in N are ≥ 2100
  have hmin2100 : ∀ p ∈ P, ∀ c : ℕ, 2100 ≤ c →
      (∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → c ≤ c') →
      ∀ r : ℕ, r.Prime → r ≠ 2 → r ∣ p + 1 → 2100 ≤ r := fun p _ c hc hmin r hr hr2 hrd =>
    if hrN : r ∈ N then hNb r hrN else le_trans hc (hmin r hr hr2 hrN hrd)
  refine masterU hP hN hK hKr hNb (4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000))) (by norm_num) hD E hm T3 β hB ?_ ?_ ?_ ?_
  · intro p hp c hc hd hmin hne
    by_cases e3 : c = 3
    · subst e3
      obtain rfl : p = 5 := T3 p hp hd
      rw [b3, b5]; norm_num
    by_cases e5 : c = 5
    · subst e5
      obtain rfl : p = 19 := T5 p hp hd
      rw [b5, b19]; norm_num
    by_cases e19 : c = 19
    · subst e19
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 19423 ≤ p := T607c (hP p hp).1 hd
        (S4b 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => if hrN : r ∈ N then by have := hNb r hrN; omega
          else hmin r hr hr2 hrN hrd)
        (fun h => by
          have := gap 1213 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          omega)
      rw [b607]
      exact step_ge (t := 19423) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 223 := T7 p hp hd
      rw [b7, b223]; norm_num
    by_cases e223 : c = 223
    · subst e223
      have hge : 213633 ≤ p := T223y (hP p hp).1 hd
        (S4b 223 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => by
          have := gap 1783 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          omega)
      rw [b223]
      exact step_ge (t := 213633) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      have hge : 37633 ≤ p := T31c (hP p hp).1 hd
        (S4b 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun r hr hr2 hrd => by
          rcases fac p hp r hr hr2 hrd with h | ⟨hrN, h⟩
          · omega
          · have := hmin r hr hr2 hrN hrd
            omega)
        (fun h => by
          have := hs 61 (h ▸ hp) (by norm_num)
          omega)
        (fun h => by
          have := gap 991 (h ▸ hp) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          omega)
        (fun h => h3967 (h ▸ hp))
      rw [b31]
      exact step_ge (t := 37633) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e8191 : c = 8191
    · subst e8191
      rcases T8191z (hP p hp).1 hd (hmin2100 p hp 8191 (by norm_num) hmin) with rfl | rfl | hge
      · rw [b8191, b16381]; norm_num
      · rw [b8191, bd 262111 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
        norm_num
      · rw [b8191]
        exact step_ge (t := 524223) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e16381 : c = 16381
    · subst e16381
      have hge : 1048383 ≤ p := T16381z (hP p hp).1 hd (hmin2100 p hp 16381 (by norm_num) hmin)
      rw [b16381]
      exact step_ge (t := 1048383) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e7 e223 e31 e8191 e16381 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b8191]; norm_num
  · rw [b3, b7, b31, b127, b8191]; norm_num

-- With 3, 5, 7, 19, 31, 223, 607 in P the set is nearly abundant: every other simple prime is at least 2223,
-- so the simple primes below 2100 are exactly these seven.
theorem gap607 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hA : ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ) ⊆ P) :
    ∀ q ∈ P, q < 2100 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 := by
  intro q hq hlt
  by_contra hcon
  have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcon
  have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
  rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
  have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ), (p + 1) = 16735272960 := by decide
  have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ), p = 8371401045 := by decide
  rw [e1, e2] at h
  omega

-- With 3, 5, 7, 19, 31, 223, 991, 1783 in P every other simple prime is at least 1899.
theorem gap1783 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hA : ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ) ⊆ P) :
    ∀ q ∈ P, q < 1899 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783 := by
  intro q hq hlt
  by_contra hcon
  have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcon
  have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
  rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
  have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ), (p + 1) = 48711975567360 := by decide
  have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ), p = 24368817447555 := by decide
  rw [e1, e2] at h
  omega

-- With 3, 5, 7, 19, 31, 223, 607, 3967 in P every other simple prime is at least 5057.
theorem gap3967 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N) (hKK1 : K ≤ K')
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hA : ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ) ⊆ P) :
    ∀ q ∈ P, q < 5057 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967 := by
  intro q hq hlt
  by_contra hcon
  have hqA : q ∉ ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hcon
  have h := S_abund hP (K_pos hN hK) hKK1 E (Finset.insert_subset hq hA)
  rw [Finset.prod_insert hqA, Finset.prod_insert hqA] at h
  have e1 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ), (p + 1) = 66405563105280 := by decide
  have e2 : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ), p = 33209347945515 := by decide
  rw [e1, e2] at h
  omega

-- The 223 family (hypotheses of step H1 of R1.H2.R1.H2.R1.H1.R1) splits in three.  Write
-- Y = prod over S of (1 + 5/z) (Y close to 1 means that the kernel S is thin).  Either a = 0, or a ≥ 48 and
--   (i)   607 ∣ n, Y > 5001/5000, and the primes of n below 2100 are 2, 3, 5, 7, 19, 31, 223, 607; or
--   (ii)  607 ∣ n, Y ≤ 5001/5000, 3967 ∣ n, and the primes of n below 5057 are
--         2, 3, 5, 7, 19, 31, 223, 607, 3967; or
--   (iii) 991 ∣ n, 1783 ∣ n, Y > 2501/2500, and the primes of n below 1899 are
--         2, 3, 5, 7, 19, 31, 223, 991, 1783 (in particular 607 does not divide n).
theorem split223 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (hres : ∃ z ∈ S, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h19 : 19 ∣ n) (h16 : 16 ∣ padicValNat 2 n)
    (h64 : padicValNat 2 n % 64 ≠ 32) (h31 : 31 ∣ n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 152 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h223 : 223 ∣ n) :
    padicValNat 2 n = 0 ∨
    (48 ≤ padicValNat 2 n ∧ 607 ∣ n ∧ 5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) ∧
      ∀ q : ℕ, q.Prime → q ∣ n → q < 2100 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607) ∨
    (48 ≤ padicValNat 2 n ∧ 607 ∣ n ∧ ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 ∧ 3967 ∣ n ∧
      ∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967) ∨
    (48 ≤ padicValNat 2 n ∧ 991 ∣ n ∧ 1783 ∣ n ∧ 2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) ∧
      ∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) := by
  by_cases h0 : padicValNat 2 n = 0
  · exact Or.inl h0
  right
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr h0)
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z := fun z hz =>
    ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hNb := adm_ge_2100 hNS hadm2
  have hY := adm_hY hNS hadm2
  obtain ⟨K, K', P, hP, hK, hKK1, hKr0, E, hmem⟩ := setup7 h hS h2
  have hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100) := hKr0.trans (kk_bound subset_rfl hNb hY)
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have mem : ∀ q, q.Prime → q ∣ n → q < 2100 → q ≠ 2 → q ∈ P := fun q hq hqn hlt hq2 =>
    (hmem q).mpr ⟨hq, hq2, hqn, big_notMem hNb hlt⟩
  have m3 := mem 3 (by norm_num) h3 (by norm_num) (by norm_num)
  have m5 := mem 5 (by norm_num) h5 (by norm_num) (by norm_num)
  have m7 := mem 7 (by norm_num) h7 (by norm_num) (by norm_num)
  have m19 := mem 19 (by norm_num) h19 (by norm_num) (by norm_num)
  have m31 := mem 31 (by norm_num) h31 (by norm_num) (by norm_num)
  have m223 := mem 223 (by norm_num) h223 (by norm_num) (by norm_num)
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5 := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 5 m5 hd (by norm_num)
  have T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19 := fun p hp hd =>
    S2 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 19 m19 hd (by norm_num)
  have hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 := fun q hq hlt => by
    obtain ⟨hqp, hq2, hqn, _⟩ := (hmem q).mp hq
    rcases hsmall q hqp hqn hlt with e | e | e | e | e | e
    · exact absurd e hq2
    all_goals (subst e; norm_num)
  have hA : ({3, 5, 7, 19, 31, 223} : Finset ℕ) ⊆ P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact m3
    · exact m5
    · exact m7
    · exact m19
    · exact m31
    · exact m223
  have hm48 : 48 ≤ padicValNat 2 n :=
    m_ge_48_223 hP hK (big_notMem hNb (by norm_num)) E hA h16 h64
  have hm20 : 20 ≤ padicValNat 2 n := le_trans (by norm_num) hm48
  have hm16 : 16 ≤ padicValNat 2 n := le_trans (by norm_num) hm48
  obtain ⟨z, hzS, -, hz3⟩ := hres
  have hD : ∀ U : Finset ℕ, (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ S) →
      ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (4 / 2097)) := by
    by_cases hc : S.card = 1
    · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hc
      have hzw : z = w := by
        rw [hw] at hzS
        exact Finset.mem_singleton.mp hzS
      subst hzw
      intro U hU
      exact sumD_one (hNS z hzS).1 (hNb z hzS) hz3 U (fun u hu => by rw [← hw]; exact hU u hu)
    · have hc2 : 2 ≤ S.card := lt_of_le_of_ne (Finset.card_pos.mpr ⟨z, hzS⟩) (Ne.symm hc)
      have hY5 := adm_hY5 hNS hc2 hadm2
      have hge := ge_2622 (fun w hw => (hNS w hw).1.ne_zero) hY5
      intro U hU
      exact sumD_two (fun w hw => ⟨(hNS w hw).1, hge w hw⟩) hY5 U hU
  by_cases h607 : 607 ∣ n
  · have m607 := mem 607 (by norm_num) h607 (by norm_num) (by norm_num)
    have hA7 : ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact m3
      · exact m5
      · exact m7
      · exact m19
      · exact m31
      · exact m223
      · exact m607
    by_cases hη : ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000
    · have hge := ge_12500 (fun w hw => (hNS w hw).1.ne_zero) (hη.trans (by norm_num))
      by_cases h3967 : 3967 ∈ P
      · have hA8 : ({3, 5, 7, 19, 31, 223, 607, 3967} : Finset ℕ) ⊆ P := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact m3
          · exact m5
          · exact m7
          · exact m19
          · exact m31
          · exact m223
          · exact m607
          · exact h3967
        refine Or.inr (Or.inl ⟨hm48, h607, hη, ((hmem 3967).mp h3967).2.2.1,
          fun q hq hqn hlt => ?_⟩)
        by_cases hq2 : q = 2
        · exact Or.inl hq2
        · have hqS : q ∉ S := fun hx =>
            (not_le.mpr (lt_trans hlt (by norm_num : (5057 : ℕ) < 12500))) (hge q hx)
          exact Or.inr (gap3967 hP hNS hK hKK1 E hA8 q ((hmem q).mpr ⟨hq, hq2, hqn, hqS⟩) hlt)
      · exfalso
        have hDη : ∀ U : Finset ℕ,
            (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ S) →
            ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 5000)) :=
          fun U hU => sumD_thin
            (fun w hw => ⟨(hNS w hw).1, le_trans (by norm_num) (hge w hw)⟩) hη U hU
        exact node607_thin hP hNS hK hKr hKK1 hNb hDη E hm20 T3 T5 hs m3 m5 m7 m19 m31 m223 m607
          h3967
    · refine Or.inl ⟨hm48, h607, not_le.mp hη, fun q hq hqn hlt => ?_⟩
      by_cases hq2 : q = 2
      · exact Or.inl hq2
      · exact Or.inr (gap607 hP hNS hK hKK1 E hA7 q (mem q hq hqn hlt hq2) hlt)
  · have n607 : 607 ∉ P := fun hx => h607 ((hmem 607).mp hx).2.2.1
    by_cases h991 : 991 ∣ n
    · have m991 := mem 991 (by norm_num) h991 (by norm_num) (by norm_num)
      by_cases h1783 : 1783 ∣ n
      · have m1783 := mem 1783 (by norm_num) h1783 (by norm_num) (by norm_num)
        have hA8 : ({3, 5, 7, 19, 31, 223, 991, 1783} : Finset ℕ) ⊆ P := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          · exact m3
          · exact m5
          · exact m7
          · exact m19
          · exact m31
          · exact m223
          · exact m991
          · exact m1783
        by_cases hη : ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 2501 / 2500
        · exfalso
          have hge := ge_12500 (fun w hw => (hNS w hw).1.ne_zero) hη
          have hDη : ∀ U : Finset ℕ,
              (∀ u ∈ U, u ≠ 0 ∧ u ≠ 1 ∧ ∀ r : ℕ, r.Prime → r ∣ u → r ∈ S) →
              ∑ u ∈ U, (if u % 3 = 1 then 4 / (3 * (u : ℚ) - 4) else 2 / (3 * (u : ℚ) - 2)) ≤ 4 / 3 * (7866 / 7862) * (1 / 5 * (2622 / 2621) * (1 / 2500)) :=
            fun U hU => sumD_eta
              (fun w hw => ⟨(hNS w hw).1, le_trans (by norm_num) (hge w hw)⟩) hη U hU
          by_cases h7927 : 7927 ∈ P
          · exact node_pair_in hP hNS hK hKr hKK1 hNb hDη E hm20 T3 T5 hs m3 m5 m7 m19 m31 m223
              m991 m1783 h7927 ((hmem 7927).mp h7927).2.2.2
              (fun w hw => le_trans (by norm_num) (hge w hw)) n607
          · exact node_pair_out hP hNS hK hKr hKK1 hNb hDη E hm20 T3 T5 hs m3 m5 m7 m19 m31 m223
              m991 m1783 n607 h7927
        · refine Or.inr (Or.inr ⟨hm48, h991, h1783, not_le.mp hη, fun q hq hqn hlt => ?_⟩)
          by_cases hq2 : q = 2
          · exact Or.inl hq2
          · exact Or.inr (gap1783 hP hNS hK hKK1 E hA8 q
              (mem q hq hqn (lt_trans hlt (by norm_num)) hq2) hlt)
      · have n1783 : 1783 ∉ P := fun hx => h1783 ((hmem 1783).mp hx).2.2.1
        exact (node991 hP hNS hK hKr hKK1 hNb hD E hm20 T3 T5 hs m3 m5 m7 m19 m31 m223 m991
          n607 n1783).elim
    · have n991 : 991 ∉ P := fun hx => h991 ((hmem 991).mp hx).2.2.1
      by_cases h1783 : 1783 ∣ n
      · have m1783 := mem 1783 (by norm_num) h1783 (by norm_num) (by norm_num)
        exact (node1783 hP hNS hK hKr hKK1 hNb hD E hm20 T3 T5 hs m3 m5 m7 m19 m31 m223 m1783
          n607 n991).elim
      · have n1783 : 1783 ∉ P := fun hx => h1783 ((hmem 1783).mp hx).2.2.1
        exact (node223 hP hNS hK hKr hKK1 hNb hY E hm16 T3 T5 hs m3 m5 m7 m19 m31 m223 n607
          n991 n1783).elim

end Erdos1052C16

-- Y below is the product over S of (1 + 5/z); Y close to 1 means that the kernel S is thin.

-- The 2-adic valuation is bounded over the family of step H1 of R1.H2.R1.H2.R1.H1.R1 (the 223 family)
-- restricted to 607 | n, a at least 48, no prime of n below 2100 other than
-- 2, 3, 5, 7, 19, 31, 223, 607, and a kernel that is not thin: Y > 5001/5000.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 2100 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607) →
    223 ∣ n → 607 ∣ n → 48 ≤ padicValNat 2 n →
    5001 / 5000 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the family of step H1 of R1.H2.R1.H2.R1.H1.R1 (the 223 family)
-- restricted to 607 | n, 3967 | n, a at least 48, no prime of n below 5057 other than
-- 2, 3, 5, 7, 19, 31, 223, 607, 3967, and a thin kernel: Y at most 5001/5000.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 5057 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 607 ∨ q = 3967) →
    223 ∣ n → 607 ∣ n → 3967 ∣ n → 48 ≤ padicValNat 2 n →
    ∏ z ∈ S, (1 + 5 / (z : ℚ)) ≤ 5001 / 5000 →
    padicValNat 2 n ≤ A

-- The 2-adic valuation is bounded over the family of step H1 of R1.H2.R1.H2.R1.H1.R1 (the 223 family)
-- restricted to 991 | n, 1783 | n, a at least 48, no prime of n below 1899 other than
-- 2, 3, 5, 7, 19, 31, 223, 991, 1783 (so 607 does not divide n), and a kernel that is not thin:
-- Y > 2501/2500.
def H3 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n → ¬ Squarefree (n / 2 ^ padicValNat 2 n) →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) →
    (∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) →
    ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097 →
    4 ∣ padicValNat 2 n → 3 ∣ n → 5 ∣ n → 7 ∣ n → 19 ∣ n →
    (∀ N : Finset ℕ, S ⊆ N → (∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z) →
      ∏ z ∈ N, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (N.card : ℚ))) ≤ 2101 / 2097 →
      (∃ z ∈ N, z ∣ 2 ^ padicValNat 2 n + 1 ∧ z % 3 = 2) ∧
      ∀ z ∈ N, z % 3 = 2 → Even (n.factorization z)) →
    16 ∣ padicValNat 2 n → padicValNat 2 n % 64 ≠ 32 →
    31 ∣ n →
    (∀ q : ℕ, q.Prime → q ∣ n → q < 1899 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 ∨ q = 223 ∨ q = 991 ∨ q = 1783) →
    223 ∣ n → 991 ∣ n → 1783 ∣ n → 48 ≤ padicValNat 2 n →
    2501 / 2500 < ∏ z ∈ S, (1 + 5 / (z : ℚ)) →
    padicValNat 2 n ≤ A

theorem main : H1 → H2 → H3 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1.H1 := by
  rintro ⟨A1, hA1⟩ ⟨A2, hA2⟩ ⟨A3, hA3⟩
  refine ⟨max A1 (max A2 A3), fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hsmall
    h223 => ?_⟩
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z := fun z hz =>
    ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hz := (hres S subset_rfl hNS hadm2).1
  rcases Erdos1052C16.split223 h hS hadm1 hadm2 hz h3 h5 h7 h19 h16 h64 h31 hsmall h223 with
    h0 | ⟨h48, h607, hk, hl⟩ | ⟨h48, h607, hk, h3967, hl⟩ | ⟨h48, h991, h1783, hk, hl⟩
  · rw [h0]
    exact Nat.zero_le _
  · exact (hA1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl h223 h607 h48
      hk).trans (le_max_left _ _)
  · exact (hA2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl h223 h607 h3967 h48
      hk).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hA3 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hl h223 h991 h1783 h48
      hk).trans ((le_max_right _ _).trans (le_max_right _ _))

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H1_R1
