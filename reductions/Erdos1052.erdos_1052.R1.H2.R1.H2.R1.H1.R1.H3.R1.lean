import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H3.R1
-- Upstream path: reductions/Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1.H3.R1.lean
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- The weight machinery (masterT, the 433 nodes, setup7, kk_bound, nleaf_bound7, mersenne_bound7,
-- smooth_recip and the bounds T433a, T433b, T607, T1213, T3463) is copied verbatim from
-- @adammcarter's checker-accepted proof of the sibling step H2 (the 433 family, PR 2626); the rest
-- of the machinery is imported from the merged parent reductions by the same author.
--
-- Shrinks step H3 (the 607 family) of Erdos1052.erdos_1052.R1.H2.R1.H2.R1.H1.R1 to its
-- intersection with the 223 family, and splits that intersection in two.
--
-- Notation as in the parent file: n unitary perfect, a = padicValNat 2 n, S admissible, P the
-- simple odd primes of n.  In the 607 family 5 is the parent of 3, 19 of 5 and 607 of 19.
--
-- PROVED BELOW, no hypothesis needed (a = 0 in each case, so the bound 0 works):
--   433 | n: the 433 family of the sibling step (a = 0), by the four weight calls of PR 2626.
--   neither 223 nor 433 divides n: then the parent of 7 is at least 2281 (Q7f) and the parent of
--     31 is 991 or at least 3967 (R31f).  Three weight calls with masterT (constant 1.0012465):
--       1213 does not divide n: parent of 607 at least 3641, of 7 at least 2281, of 31 at least 991;
--       1213 divides n, 991 does not: parent of 1213 at least 20000, of 31 at least 3967;
--       1213 and 991 divide n: 991 is the parent of 31 and its parent is at least 3963.
--     The chain products are below 1.99751 = 2 / 1.0012465 (exact fractions, checked by norm_num).
--   223 | n: none of 991, 1213, 1783 divides n.  The product of 1 + 1/p over 3, 5, 7, 19, 31, 223,
--     607 is 1.999101, and with 991, 1213 or 1783 added it exceeds 2 (abundancy).
--
-- H1 (OPEN): the step restricted to 223 | n, 433, 991, 1213, 1783 not dividing n, 3967 | n
--   (3967 is then the parent of 31).
-- H2 (OPEN): the same with 3967 not dividing n (the parent of 31 is then above 3967).
-- Both lie inside step H1 of the parent file (the 223 family), so a proof of that step proves
-- this one.  The weight inequality cannot close them: the product over 3, 5, 7, 19, 31, 223, 607
-- times the constant 1.0012465 already exceeds 2.  No known unitary perfect number is in either
-- family.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1

-- The 2-adic valuation is bounded over the family of step H3 of the parent file restricted to
-- 223 | n, none of 433, 991, 1213, 1783 dividing n, and 3967 | n.
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
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    607 ∣ n → 223 ∣ n → ¬ 433 ∣ n → ¬ 991 ∣ n → ¬ 1213 ∣ n → ¬ 1783 ∣ n →
    3967 ∣ n →
    padicValNat 2 n ≤ A

-- The same with 3967 not dividing n.
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
    (∀ q : ℕ, q.Prime → q ∣ n → q < 152 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) →
    607 ∣ n → 223 ∣ n → ¬ 433 ∣ n → ¬ 991 ∣ n → ¬ 1213 ∣ n → ¬ 1783 ∣ n →
    ¬ 3967 ∣ n →
    padicValNat 2 n ≤ A

-- ===== Copied from PR 2626 (@adammcarter), unchanged =====

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

end Erdos1052C7

namespace Erdos1052C7

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

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

end Erdos1052C7

namespace Erdos1052C7

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

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

end Erdos1052C7

namespace Erdos1052C7

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

-- A prime p with 433 ∣ p + 1 is at least 3463 (865, 1731, 2597 are composite).
theorem T433a {p : ℕ} (hp : p.Prime) (hd : 433 ∣ p + 1) : 3463 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  obtain ⟨j, hj⟩ : 2 * 433 ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 hd
  have hjlt : j < 4 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 2 * 433 * j - 1 := by omega
  clear hd h2 hlt hp2 hj
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p ≠ 3463 with 433 ∣ p + 1 is at least 6000 (865, 1731, 2597, 4329, 5195 are composite).
theorem T433b {p : ℕ} (hp : p.Prime) (hd : 433 ∣ p + 1) (hne : p ≠ 3463) : 6000 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  obtain ⟨j, hj⟩ : 2 * 433 ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 hd
  have hjlt : j < 7 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 2 * 433 * j - 1 := by omega
  clear hd h2 hlt hp2 hj
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p ≠ 1213 with 607 ∣ p + 1 is at least 3641 (2427 is composite).
theorem T607 {p : ℕ} (hp : p.Prime) (hd : 607 ∣ p + 1) (hne : p ≠ 1213) : 3641 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  obtain ⟨j, hj⟩ : 2 * 607 ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 hd
  have hjlt : j < 3 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 2 * 607 * j - 1 := by omega
  clear hd h2 hlt hp2 hj
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p with 1213 ∣ p + 1 and 7 ∤ p + 1 is at least 20000 (16981 has 7 ∣ 16982; the other
-- candidates 2426 j - 1, j ≤ 8, are composite).
theorem T1213 {p : ℕ} (hp : p.Prime) (hd : 1213 ∣ p + 1) (h7 : ¬ 7 ∣ p + 1) : 20000 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  obtain ⟨j, hj⟩ : 2 * 1213 ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 hd
  have hjlt : j < 9 := by omega
  have hj0 : 0 < j := by omega
  obtain rfl : p = 2 * 1213 * j - 1 := by omega
  clear hd h2 hlt hp2 hj
  interval_cases j <;> first | omega | (norm_num at hp)

-- A prime p with 3463 ∣ p + 1 is at least 20000 (6925 and 13851 are composite).
theorem T3463 {p : ℕ} (hp : p.Prime) (hd : 3463 ∣ p + 1) : 20000 ≤ p := by
  by_contra hlt
  have hp2 : p ≠ 2 := by
    rintro rfl
    norm_num at hd
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  obtain ⟨j, hj⟩ : 2 * 3463 ∣ p + 1 :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 hd
  clear hd h2 hp2
  have hjlt : j < 3 := by
    clear hp
    omega
  have hj0 : 0 < j := by
    clear hp
    omega
  obtain rfl : p = 2 * 3463 * j - 1 := by
    clear hp
    omega
  clear hlt hj
  interval_cases j <;> norm_num at hp

-- Node A of the 433 family: 607 does not divide n.
theorem node433_A {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h433 : 433 ∈ P) (h607 : 607 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 433 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 433 h433 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 433 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 433 h433 hd (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (5776 / 5774))) else
      if p = 5 then 6 / 5 * (20 / 19 * (5776 / 5774)) else
      if p = 19 then 20 / 19 * (5776 / 5774) else
      if p = 7 then 8 / 7 * (434 / 433 * (3464 / 3462)) else
      if p = 433 then 434 / 433 * (3464 / 3462) else
      if p = 31 then 32 / 31 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (5776 / 5774))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (5776 / 5774)) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (5776 / 5774) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (434 / 433 * (3464 / 3462)) := by rw [hβ]; norm_num
  have b433 : β 433 = 434 / 433 * (3464 / 3462) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 7 → c ≠ 433 → c ≠ 31 → c ≠ 127 → 
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e7 e433 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e7, if_neg e433, if_neg e31, if_neg e127]
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
    by_cases e433 : p = 433
    · subst e433; rw [b433]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e7 e433 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
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
      have hge : 5775 ≤ p := Q19f (hP p hp).1 hd
        (S4b 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun h => by have := hmin 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
        (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
          have hle := hmin c' h1 h2 hcN h3
          by_contra hcon
          have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
          omega)
        (fun h => by
          have := hs 37 (h ▸ hp) (by norm_num)
          omega)
        (fun h => by
          have := hs 151 (h ▸ hp) (by norm_num)
          omega)
        (fun h => h607 (h ▸ hp))
      rw [b19]
      exact step_ge (t := 5775) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 433 := T7 p hp hd
      rw [b7, b433]; norm_num
    by_cases e433 : c = 433
    · subst e433
      have hge : 3463 ≤ p := T433a (hP p hp).1 hd
      rw [b433]
      exact step_ge (t := 3463) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 433 := T31 p hp hd
      have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (by norm_num)
      omega
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e7 e433 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Node B: 607 divides n, 1213 does not.
theorem node433_B {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h433 : 433 ∈ P) (h607 : 607 ∈ P) (h1213 : 1213 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 433 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 433 h433 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 433 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 433 h433 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (3642 / 3640)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (3642 / 3640))) else
      if p = 19 then 20 / 19 * (608 / 607 * (3642 / 3640)) else
      if p = 607 then 608 / 607 * (3642 / 3640) else
      if p = 7 then 8 / 7 * (434 / 433 * (3464 / 3462)) else
      if p = 433 then 434 / 433 * (3464 / 3462) else
      if p = 31 then 32 / 31 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (3642 / 3640)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (3642 / 3640))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (3642 / 3640)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (3642 / 3640) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (434 / 433 * (3464 / 3462)) := by rw [hβ]; norm_num
  have b433 : β 433 = 434 / 433 * (3464 / 3462) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 433 → c ≠ 31 → c ≠ 127 → 
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e433 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e433, if_neg e31, if_neg e127]
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
    by_cases e433 : p = 433
    · subst e433; rw [b433]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e7 e433 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
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
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 3641 ≤ p := T607 (hP p hp).1 hd (fun h => h1213 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 3641) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 433 := T7 p hp hd
      rw [b7, b433]; norm_num
    by_cases e433 : c = 433
    · subst e433
      have hge : 3463 ≤ p := T433a (hP p hp).1 hd
      rw [b433]
      exact step_ge (t := 3463) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 433 := T31 p hp hd
      have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (by norm_num)
      omega
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e7 e433 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Node C: 607 and 1213 divide n, 3463 does not.
theorem node433_C {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h433 : 433 ∈ P) (h607 : 607 ∈ P) (h1213 : 1213 ∈ P) (h3463 : 3463 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 433 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 433 h433 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 433 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 433 h433 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T607u : ∀ p ∈ P, 607 ∣ p + 1 → p = 1213 := fun p hp hd =>
    S2 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1213 h1213 hd (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999)))) else
      if p = 19 then 20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))) else
      if p = 607 then 608 / 607 * (1214 / 1213 * (20001 / 19999)) else
      if p = 1213 then 1214 / 1213 * (20001 / 19999) else
      if p = 7 then 8 / 7 * (434 / 433 * (6001 / 5999)) else
      if p = 433 then 434 / 433 * (6001 / 5999) else
      if p = 31 then 32 / 31 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999)))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (1214 / 1213 * (20001 / 19999)) := by rw [hβ]; norm_num
  have b1213 : β 1213 = 1214 / 1213 * (20001 / 19999) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (434 / 433 * (6001 / 5999)) := by rw [hβ]; norm_num
  have b433 : β 433 = 434 / 433 * (6001 / 5999) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 1213 → c ≠ 7 → c ≠ 433 → c ≠ 31 → c ≠ 127 → 
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e1213 e7 e433 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e1213, if_neg e7, if_neg e433, if_neg e31, if_neg e127]
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
    by_cases e1213 : p = 1213
    · subst e1213; rw [b1213]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e433 : p = 433
    · subst e433; rw [b433]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e1213 e7 e433 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
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
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      obtain rfl : p = 1213 := T607u p hp hd
      rw [b607, b1213]; norm_num
    by_cases e1213 : c = 1213
    · subst e1213
      have hge : 20000 ≤ p := T1213 (hP p hp).1 hd (fun h => by
        have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h
        omega)
      rw [b1213]
      exact step_ge (t := 20000) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 433 := T7 p hp hd
      rw [b7, b433]; norm_num
    by_cases e433 : c = 433
    · subst e433
      have hge : 6000 ≤ p := T433b (hP p hp).1 hd (fun h => h3463 (h ▸ hp))
      rw [b433]
      exact step_ge (t := 6000) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 433 := T31 p hp hd
      have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (by norm_num)
      omega
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e1213 e7 e433 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Node D: 607, 1213 and 3463 divide n.
theorem node433_D {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h433 : 433 ∈ P) (h607 : 607 ∈ P) (h1213 : 1213 ∈ P) (h3463 : 3463 ∈ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T7 : ∀ p ∈ P, 7 ∣ p + 1 → p = 433 := fun p hp hd =>
    S2 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 433 h433 hd (by norm_num)
  have T31 : ∀ p ∈ P, 31 ∣ p + 1 → p = 433 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 433 h433 hd (by norm_num)
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T607u : ∀ p ∈ P, 607 ∣ p + 1 → p = 1213 := fun p hp hd =>
    S2 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1213 h1213 hd (by norm_num)
  have T433u : ∀ p ∈ P, 433 ∣ p + 1 → p = 3463 := fun p hp hd =>
    S2 433 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 3463 h3463 hd (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999)))) else
      if p = 19 then 20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))) else
      if p = 607 then 608 / 607 * (1214 / 1213 * (20001 / 19999)) else
      if p = 1213 then 1214 / 1213 * (20001 / 19999) else
      if p = 7 then 8 / 7 * (434 / 433 * (3464 / 3463 * (20001 / 19999))) else
      if p = 433 then 434 / 433 * (3464 / 3463 * (20001 / 19999)) else
      if p = 3463 then 3464 / 3463 * (20001 / 19999) else
      if p = 31 then 32 / 31 else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999)))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (1214 / 1213 * (20001 / 19999)) := by rw [hβ]; norm_num
  have b1213 : β 1213 = 1214 / 1213 * (20001 / 19999) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (434 / 433 * (3464 / 3463 * (20001 / 19999))) := by rw [hβ]; norm_num
  have b433 : β 433 = 434 / 433 * (3464 / 3463 * (20001 / 19999)) := by rw [hβ]; norm_num
  have b3463 : β 3463 = 3464 / 3463 * (20001 / 19999) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 1213 → c ≠ 7 → c ≠ 433 → c ≠ 3463 → c ≠ 31 → c ≠ 127 → 
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e1213 e7 e433 e3463 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e1213, if_neg e7, if_neg e433, if_neg e3463, if_neg e31, if_neg e127]
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
    by_cases e1213 : p = 1213
    · subst e1213; rw [b1213]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e433 : p = 433
    · subst e433; rw [b433]; norm_num
    by_cases e3463 : p = 3463
    · subst e3463; rw [b3463]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e1213 e7 e433 e3463 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
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
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      obtain rfl : p = 1213 := T607u p hp hd
      rw [b607, b1213]; norm_num
    by_cases e1213 : c = 1213
    · subst e1213
      have hge : 20000 ≤ p := T1213 (hP p hp).1 hd (fun h => by
        have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h
        omega)
      rw [b1213]
      exact step_ge (t := 20000) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      obtain rfl : p = 433 := T7 p hp hd
      rw [b7, b433]; norm_num
    by_cases e433 : c = 433
    · subst e433
      obtain rfl : p = 3463 := T433u p hp hd
      rw [b433, b3463]; norm_num
    by_cases e3463 : c = 3463
    · subst e3463
      have hge : 20000 ≤ p := T3463 (hP p hp).1 hd
      rw [b3463]
      exact step_ge (t := 20000) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 433 := T31 p hp hd
      have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) (by norm_num)
      omega
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e1213 e7 e433 e3463 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

end Erdos1052C7

namespace Erdos1052C7

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main


-- The 433 family at the level of the balance equation.
theorem core433P {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h433 : 433 ∈ P) : False := by
  by_cases h607 : 607 ∈ P
  · by_cases h1213 : 1213 ∈ P
    · by_cases h3463 : 3463 ∈ P
      · exact node433_D hP hN hK hKr hNb hY E hm T3 T5 hs h433 h607 h1213 h3463
      · exact node433_C hP hN hK hKr hNb hY E hm T3 T5 hs h433 h607 h1213 h3463
    · exact node433_B hP hN hK hKr hNb hY E hm T3 T5 hs h433 h607 h1213
  · exact node433_A hP hN hK hKr hNb hY E hm T3 T5 hs h433 h607

end Erdos1052C7

-- ===== New: the 607 family without 223 and 433, and the exclusions in the 223 case =====

namespace Erdos1052C7

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 hiding H1 H2 main
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1 hiding H1 H2 H3 main

-- The parent of 7: at least 2281 when none of 13, 223, 433 is in P and 607 is the parent of 19.
theorem par7_607 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hNb : ∀ z ∈ N, 2100 ≤ z)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h223 : 223 ∉ P) (h433 : 433 ∉ P) {p : ℕ} (hp : p ∈ P) (hd : 7 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → 7 ≤ c') : 2281 ≤ p := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  exact Q7f (hP p hp).1 hd
    (fun h => by have := hmin 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
    (fun h => by have := hmin 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h; omega)
    (fun h => by
      have := hs 11 (S1 11 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 13 (S1 13 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 23 (S1 23 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 29 (S1 29 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 43 (S1 43 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 53 (S1 53 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 61 (S1 61 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 67 (S1 67 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 71 (S1 71 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 73 (S1 73 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 127 (S1 127 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (fun h => by
      have := hs 151 (S1 151 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp h) (by norm_num)
      omega)
    (S4b 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
    (fun h => by
      have := hs 13 (h ▸ hp) (by norm_num)
      omega)
    (fun h => h223 (h ▸ hp))
    (fun h => h433 (h ▸ hp))
    (fun h => by
      have := T19 p hp (by rw [h]; norm_num)
      omega)

-- The parent of 31 (when 31 is its least odd child): 991 or at least 3967.
theorem par31_607 {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hNb : ∀ z ∈ N, 2100 ≤ z)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    {p : ℕ} (hp : p ∈ P) (hd : 31 ∣ p + 1)
    (hmin : ∀ c' : ℕ, c'.Prime → c' ≠ 2 → c' ∉ N → c' ∣ p + 1 → 31 ≤ c') :
    p = 991 ∨ 3967 ≤ p := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  by_cases e : p = 991
  · exact Or.inl e
  right
  exact R31f (hP p hp).1 hd
    (S4b 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
    (fun c' h1 h2 hne h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else by
      have hle := hmin c' h1 h2 hcN h3
      by_contra hcon
      have := hs c' (S1 c' h1 h2 hcN p hp h3) (by omega)
      omega)
    (fun h => by
      have := hs 61 (h ▸ hp) (by norm_num)
      omega)
    e

-- Node A of the 607 family (223 and 433 not in P): 1213 is not in P.
theorem node607_A {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h607 : 607 ∈ P) (h223 : 223 ∉ P) (h433 : 433 ∉ P) (h1213 : 1213 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (3642 / 3640)))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (3642 / 3640))) else
      if p = 19 then 20 / 19 * (608 / 607 * (3642 / 3640)) else
      if p = 607 then 608 / 607 * (3642 / 3640) else
      if p = 7 then 8 / 7 * (2282 / 2280) else
      if p = 31 then 32 / 31 * (992 / 990) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (3642 / 3640)))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (3642 / 3640))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (3642 / 3640)) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (3642 / 3640) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (2282 / 2280) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (992 / 990) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 7 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e7 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e7, if_neg e31, if_neg e127]
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
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e7 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
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
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      have hge : 3641 ≤ p := T607 (hP p hp).1 hd (fun h => h1213 (h ▸ hp))
      rw [b607]
      exact step_ge (t := 3641) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      have hge : 2281 ≤ p := par7_607 hP hK hNb E T19 hs h223 h433 hp hd hmin
      rw [b7]
      exact step_ge (t := 2281) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      have hge : 991 ≤ p := by
        rcases par31_607 hP hK hNb E hs hp hd hmin with h | h <;> omega
      rw [b31]
      exact step_ge (t := 991) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e7 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Node B: 1213 in P, 991 not in P.
theorem node607_B {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h607 : 607 ∈ P) (h223 : 223 ∉ P) (h433 : 433 ∉ P) (h1213 : 1213 ∈ P) (h991 : 991 ∉ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T607u : ∀ p ∈ P, 607 ∣ p + 1 → p = 1213 := fun p hp hd =>
    S2 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1213 h1213 hd (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999)))) else
      if p = 19 then 20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))) else
      if p = 607 then 608 / 607 * (1214 / 1213 * (20001 / 19999)) else
      if p = 1213 then 1214 / 1213 * (20001 / 19999) else
      if p = 7 then 8 / 7 * (2282 / 2280) else
      if p = 31 then 32 / 31 * (3968 / 3966) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999)))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (1214 / 1213 * (20001 / 19999)) := by rw [hβ]; norm_num
  have b1213 : β 1213 = 1214 / 1213 * (20001 / 19999) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (2282 / 2280) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (3968 / 3966) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 1213 → c ≠ 7 → c ≠ 31 → c ≠ 127 →
      β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e1213 e7 e31 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e1213, if_neg e7, if_neg e31,
        if_neg e127]
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
    by_cases e1213 : p = 1213
    · subst e1213; rw [b1213]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e1213 e7 e31 e127]; exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
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
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      obtain rfl : p = 1213 := T607u p hp hd
      rw [b607, b1213]; norm_num
    by_cases e1213 : c = 1213
    · subst e1213
      have hge : 20000 ≤ p := T1213 (hP p hp).1 hd (fun h => by
        have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h
        omega)
      rw [b1213]
      exact step_ge (t := 20000) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      have hge : 2281 ≤ p := par7_607 hP hK hNb E T19 hs h223 h433 hp hd hmin
      rw [b7]
      exact step_ge (t := 2281) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      have hge : 3967 ≤ p := by
        rcases par31_607 hP hK hNb E hs hp hd hmin with h | h
        · exact absurd (h ▸ hp) h991
        · exact h
      rw [b31]
      exact step_ge (t := 3967) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e1213 e7 e31 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- Node C: 1213 and 991 in P.
theorem node607_C {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h607 : 607 ∈ P) (h223 : 223 ∉ P) (h433 : 433 ∉ P) (h1213 : 1213 ∈ P) (h991 : 991 ∈ P) :
    False := by
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have h127 : 127 ∉ P := fun h => by
    have := hs 127 h (by norm_num)
    omega
  have T19 : ∀ p ∈ P, 19 ∣ p + 1 → p = 607 := fun p hp hd =>
    S2 19 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 607 h607 hd (by norm_num)
  have T607u : ∀ p ∈ P, 607 ∣ p + 1 → p = 1213 := fun p hp hd =>
    S2 607 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 1213 h1213 hd (by norm_num)
  have T31u : ∀ p ∈ P, 31 ∣ p + 1 → p = 991 := fun p hp hd =>
    S2 31 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 991 h991 hd (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℚ, ∀ p : ℕ, β p =
      if p = 3 then 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))))) else
      if p = 5 then 6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999)))) else
      if p = 19 then 20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))) else
      if p = 607 then 608 / 607 * (1214 / 1213 * (20001 / 19999)) else
      if p = 1213 then 1214 / 1213 * (20001 / 19999) else
      if p = 7 then 8 / 7 * (2282 / 2280) else
      if p = 31 then 32 / 31 * (992 / 991 * (3964 / 3962)) else
      if p = 991 then 992 / 991 * (3964 / 3962) else
      if p = 127 then 1 else
      ((p : ℚ) + 1) / ((p : ℚ) - 1) := ⟨_, fun _ => rfl⟩
  have b3 : β 3 = 4 / 3 * (6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))))) := by rw [hβ]; norm_num
  have b5 : β 5 = 6 / 5 * (20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999)))) := by rw [hβ]; norm_num
  have b19 : β 19 = 20 / 19 * (608 / 607 * (1214 / 1213 * (20001 / 19999))) := by rw [hβ]; norm_num
  have b607 : β 607 = 608 / 607 * (1214 / 1213 * (20001 / 19999)) := by rw [hβ]; norm_num
  have b1213 : β 1213 = 1214 / 1213 * (20001 / 19999) := by rw [hβ]; norm_num
  have b7 : β 7 = 8 / 7 * (2282 / 2280) := by rw [hβ]; norm_num
  have b31 : β 31 = 32 / 31 * (992 / 991 * (3964 / 3962)) := by rw [hβ]; norm_num
  have b991 : β 991 = 992 / 991 * (3964 / 3962) := by rw [hβ]; norm_num
  have b127 : β 127 = 1 := by rw [hβ]; norm_num
  have bd : ∀ c : ℕ, c ≠ 3 → c ≠ 5 → c ≠ 19 → c ≠ 607 → c ≠ 1213 → c ≠ 7 → c ≠ 31 → c ≠ 991 →
      c ≠ 127 → β c = ((c : ℚ) + 1) / ((c : ℚ) - 1) :=
    fun c e3 e5 e19 e607 e1213 e7 e31 e991 e127 => by
      rw [hβ, if_neg e3, if_neg e5, if_neg e19, if_neg e607, if_neg e1213, if_neg e7, if_neg e31,
        if_neg e991, if_neg e127]
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
    by_cases e1213 : p = 1213
    · subst e1213; rw [b1213]; norm_num
    by_cases e7 : p = 7
    · subst e7; rw [b7]; norm_num
    by_cases e31 : p = 31
    · subst e31; rw [b31]; norm_num
    by_cases e991 : p = 991
    · subst e991; rw [b991]; norm_num
    by_cases e127 : p = 127
    · subst e127; exact absurd hp h127
    rw [bd p e3 e5 e19 e607 e1213 e7 e31 e991 e127]
    exact ⟨one_add_le_B (hP p hp).1.two_le, le_refl _⟩
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
      obtain rfl : p = 607 := T19 p hp hd
      rw [b19, b607]; norm_num
    by_cases e607 : c = 607
    · subst e607
      obtain rfl : p = 1213 := T607u p hp hd
      rw [b607, b1213]; norm_num
    by_cases e1213 : c = 1213
    · subst e1213
      have hge : 20000 ≤ p := T1213 (hP p hp).1 hd (fun h => by
        have := hmin 7 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) h
        omega)
      rw [b1213]
      exact step_ge (t := 20000) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e7 : c = 7
    · subst e7
      have hge : 2281 ≤ p := par7_607 hP hK hNb E T19 hs h223 h433 hp hd hmin
      rw [b7]
      exact step_ge (t := 2281) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e31 : c = 31
    · subst e31
      obtain rfl : p = 991 := T31u p hp hd
      rw [b31, b991]; norm_num
    by_cases e991 : c = 991
    · subst e991
      have hge : 3963 ≤ p := R991 (hP p hp).1 hd
        (S4b 991 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp)
        (fun c' h1 h2 _ h3 => if hcN : c' ∈ N then by have := hNb c' hcN; omega else
          hmin c' h1 h2 hcN h3)
      rw [b991]
      exact step_ge (t := 3963) (by norm_num) hge (hB p hp).2 (by norm_num)
    by_cases e127 : c = 127
    · subst e127
      exact absurd hc h127
    exact absurd (bd c e3 e5 e19 e607 e1213 e7 e31 e991 e127) hne
  · rw [b3, b7, b31, b127]; norm_num
  · rw [b3, b7, b31, b127]; norm_num

-- The 607 family without 223 at the level of the balance equation.
theorem core607P {m K K' : ℕ} {N P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2)
    (hN : ∀ z ∈ N, z.Prime ∧ 128 ≤ z ∧ N.card + 3 ≤ z)
    (hK : ∀ c : ℕ, c.Prime → c ∣ K → c ∈ N)
    (hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100))
    (hNb : ∀ z ∈ N, 2100 ≤ z) (hY : ∏ z ∈ N, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097)
    (E : (2 ^ m + 1) * K' * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * K * ∏ p ∈ P, p) (hm : 16 ≤ m)
    (T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5) (T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19)
    (hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h607 : 607 ∈ P) (h223 : 223 ∉ P) : False := by
  by_cases h433 : 433 ∈ P
  · exact core433P hP hN hK hKr hNb hY E hm T3 T5 hs h433
  by_cases h1213 : 1213 ∈ P
  · by_cases h991 : 991 ∈ P
    · exact node607_C hP hN hK hKr hNb hY E hm T3 T5 hs h607 h223 h433 h1213 h991
    · exact node607_B hP hN hK hKr hNb hY E hm T3 T5 hs h607 h223 h433 h1213 h991
  · exact node607_A hP hN hK hKr hNb hY E hm T3 T5 hs h607 h223 h433 h1213

-- The common setup at the level of n: either a = 0, or the balance data with m = a at least 16.
theorem setup607 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h5 : 5 ∣ n) (h19 : 19 ∣ n) (h16 : 16 ∣ padicValNat 2 n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 152 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) :
    padicValNat 2 n = 0 ∨ ∃ (K K' : ℕ) (P : Finset ℕ), (∀ p ∈ P, p.Prime ∧ p ≠ 2) ∧
      (∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      (∀ c : ℕ, c.Prime → c ∣ K → c ∈ S) ∧ K ≤ K' ∧
      ((K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100)) ∧
      (∀ z ∈ S, 2100 ≤ z) ∧ (∏ z ∈ S, (1 + 4 / (z : ℚ)) ≤ 2101 / 2097) ∧
      ((2 ^ padicValNat 2 n + 1) * K' * ∏ p ∈ P, (p + 1) =
        2 ^ (padicValNat 2 n + 1) * K * ∏ p ∈ P, p) ∧ 16 ≤ padicValNat 2 n ∧
      (∀ q, q.Prime → q ∣ n → q < 2100 → q ≠ 2 → q ∈ P) ∧
      (∀ p ∈ P, 3 ∣ p + 1 → p = 5) ∧ (∀ p ∈ P, 5 ∣ p + 1 → p = 19) ∧
      (∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31) ∧
      (∀ q ∈ P, q ∣ n) := by
  by_cases h0 : padicValNat 2 n = 0
  · exact Or.inl h0
  right
  have hm : 16 ≤ padicValNat 2 n := by
    obtain ⟨k, hk⟩ := h16
    omega
  have h2 : 2 ∣ n := dvd_of_one_le_padicValNat (by omega)
  have hNS : ∀ z ∈ S, z.Prime ∧ 128 ≤ z ∧ S.card + 3 ≤ z := fun z hz =>
    ⟨((hS z).mp hz).1, hadm1 z hz⟩
  have hNb := adm_ge_2100 hNS hadm2
  have hY := adm_hY hNS hadm2
  obtain ⟨K, K', P, hP, hK, hKK, hKr0, E, hmem⟩ := setup7 h hS h2
  have hKr : (K' : ℚ) / K ≤ 1 + 1 / (2097 * 2100) := hKr0.trans (kk_bound subset_rfl hNb hY)
  obtain ⟨S1, S5, S2, S3, S4a, S4b, S6, S7⟩ := facts hP hK E
  have mem : ∀ q, q.Prime → q ∣ n → q < 2100 → q ≠ 2 → q ∈ P := fun q hq hqn hlt hq2 =>
    (hmem q).mpr ⟨hq, hq2, hqn, big_notMem hNb hlt⟩
  have m5 := mem 5 (by norm_num) h5 (by norm_num) (by norm_num)
  have m19 := mem 19 (by norm_num) h19 (by norm_num) (by norm_num)
  have T3 : ∀ p ∈ P, 3 ∣ p + 1 → p = 5 := fun p hp hd =>
    S2 3 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 5 m5 hd (by norm_num)
  have T5 : ∀ p ∈ P, 5 ∣ p + 1 → p = 19 := fun p hp hd =>
    S2 5 (by norm_num) (by norm_num) (big_notMem hNb (by norm_num)) p hp 19 m19 hd (by norm_num)
  have hs : ∀ q ∈ P, q < 152 → q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31 := fun q hq hlt => by
    obtain ⟨hqp, hq2, hqn, _⟩ := (hmem q).mp hq
    rcases hsmall q hqp hqn hlt with e | e | e | e | e | e
    · exact absurd e hq2
    all_goals (subst e; norm_num)
  exact ⟨K, K', P, hP, hNS, hK, hKK, hKr, hNb, hY, E, hm, mem, T3, T5, hs,
    fun q hq => ((hmem q).mp hq).2.2.1⟩

-- The 607 family without 223: a = 0.
theorem family607 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h5 : 5 ∣ n) (h19 : 19 ∣ n) (h16 : 16 ∣ padicValNat 2 n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 152 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h607 : 607 ∣ n) (h223 : ¬ 223 ∣ n) : padicValNat 2 n = 0 := by
  rcases setup607 h hS hadm1 hadm2 h5 h19 h16 hsmall with h0 | ⟨K, K', P, hP, hNS, hK, hKK, hKr,
    hNb, hY, E, hm, mem, T3, T5, hs, hdvd⟩
  · exact h0
  exact (core607P hP hNS hK hKr hNb hY E hm T3 T5 hs
    (mem 607 (by norm_num) h607 (by norm_num) (by norm_num))
    (fun h' => h223 (hdvd 223 h'))).elim

theorem prod7_succ : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ), (p + 1) =
    4 * 6 * 8 * 20 * 32 * 224 * 608 := by
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  all_goals norm_num

theorem prod7_self : ∏ p ∈ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ), p =
    3 * 5 * 7 * 19 * 31 * 223 * 607 := by
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  all_goals norm_num

-- The 607 family with 223: a = 0, or none of 433, 991, 1213, 1783 divides n.
theorem excl223 {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n)
    (hadm1 : ∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z)
    (hadm2 : ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097)
    (h3 : 3 ∣ n) (h5 : 5 ∣ n) (h7 : 7 ∣ n) (h19 : 19 ∣ n) (h31 : 31 ∣ n)
    (h16 : 16 ∣ padicValNat 2 n)
    (hsmall : ∀ q : ℕ, q.Prime → q ∣ n → q < 152 →
      q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 19 ∨ q = 31)
    (h607 : 607 ∣ n) (h223 : 223 ∣ n) :
    padicValNat 2 n = 0 ∨ (¬ 433 ∣ n ∧ ¬ 991 ∣ n ∧ ¬ 1213 ∣ n ∧ ¬ 1783 ∣ n) := by
  rcases setup607 h hS hadm1 hadm2 h5 h19 h16 hsmall with h0 | ⟨K, K', P, hP, hNS, hK, hKK, hKr,
    hNb, hY, E, hm, mem, T3, T5, hs, hdvd⟩
  · exact Or.inl h0
  right
  have hK0 : 0 < K := K_pos hNS hK
  have m3 := mem 3 (by norm_num) h3 (by norm_num) (by norm_num)
  have m5 := mem 5 (by norm_num) h5 (by norm_num) (by norm_num)
  have m7 := mem 7 (by norm_num) h7 (by norm_num) (by norm_num)
  have m19 := mem 19 (by norm_num) h19 (by norm_num) (by norm_num)
  have m31 := mem 31 (by norm_num) h31 (by norm_num) (by norm_num)
  have m223 := mem 223 (by norm_num) h223 (by norm_num) (by norm_num)
  have m607 := mem 607 (by norm_num) h607 (by norm_num) (by norm_num)
  -- abundancy: 3, 5, 7, 19, 31, 223, 607 and one more prime x of P
  have hab : ∀ x, x ∈ P → x ≠ 3 → x ≠ 5 → x ≠ 7 → x ≠ 19 → x ≠ 31 → x ≠ 223 → x ≠ 607 →
      (x + 1) * (4 * 6 * 8 * 20 * 32 * 224 * 608) < 2 * (x * (3 * 5 * 7 * 19 * 31 * 223 * 607)) := by
    intro x hx e3 e5 e7 e19 e31 e223 e607
    have hsub : ({x, 3, 5, 7, 19, 31, 223, 607} : Finset ℕ) ⊆ P := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    have hA := S_abund hP hK0 hKK E hsub
    have hx1 : x ∉ ({3, 5, 7, 19, 31, 223, 607} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨e3, e5, e7, e19, e31, e223, e607⟩
    rw [Finset.prod_insert hx1, Finset.prod_insert hx1, prod7_succ, prod7_self] at hA
    exact hA
  refine ⟨fun h433 => ?_, fun h991 => ?_, fun h1213 => ?_, fun h1783 => ?_⟩
  · exact core433P hP hNS hK hKr hNb hY E hm T3 T5 hs
      (mem 433 (by norm_num) h433 (by norm_num) (by norm_num))
  · have := hab 991 (mem 991 (by norm_num) h991 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
  · have := hab 1213 (mem 1213 (by norm_num) h1213 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this
  · have := hab 1783 (mem 1783 (by norm_num) h1783 (by norm_num) (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at this

end Erdos1052C7

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1.H3 := by
  rintro ⟨A1, hA1⟩ ⟨A2, hA2⟩
  refine ⟨max A1 A2, fun n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hsmall h607 =>
    ?_⟩
  by_cases h223 : 223 ∣ n
  · rcases Erdos1052C7.excl223 h hS hadm1 hadm2 h3 h5 h7 h19 h31 h16 hsmall h607 h223 with
      h0 | ⟨n433, n991, n1213, n1783⟩
    · rw [h0]
      exact Nat.zero_le _
    by_cases h3967 : 3967 ∣ n
    · exact (hA1 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hsmall h607 h223 n433
        n991 n1213 n1783 h3967).trans (le_max_left _ _)
    · exact (hA2 n h hsq S hS hadm1 hadm2 h4 h3 h5 h7 h19 hres h16 h64 h31 hsmall h607 h223 n433
        n991 n1213 n1783 h3967).trans (le_max_right _ _)
  · rw [Erdos1052C7.family607 h hS hadm1 hadm2 h5 h19 h16 hsmall h607 h223]
    exact Nat.zero_le _

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H2_R1_H1_R1_H3_R1
