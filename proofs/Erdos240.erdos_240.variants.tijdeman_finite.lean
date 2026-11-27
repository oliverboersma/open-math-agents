import FormalConjectures.ErdosProblems.«240»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.Polynomial.HasseDeriv

/-!
# Tijdeman's gap theorem for `P`-smooth numbers via Baker–Feldman

We prove `Erdos240.erdos_240.variants.tijdeman_finite`: for any finite nonempty set `P` of primes,
there exists `C > 0` such that `a P i / (log (a P i)) ^ C = O(a P (i + 1) - a P i)`.

The proof combines:
1. Smooth-number enumeration and prime-factorization bookkeeping (inlined from reduction R1).
2. A self-contained Baker–Feldman lower bound `c * B ^ (-C) ≤ |∑_{p ∈ S} b_p * log p|` for any
   fixed finite set `S` of rational primes, using Feldman block polynomials, Siegel's lemma over
   `ℤ`, an explicit algebraic Hermite–Schwarz extrapolation lemma via `dslope` and the Maximum
   Modulus Principle (with no contour integrals and no Kummer theory), and a discrete shift-operator
   nonvanishing argument.
-/

namespace BakerFeldman

open Filter Asymptotics Polynomial

/- Section 1: Elementary arithmetic helpers & unique factorization nonvanishing -/

lemma pow_le_two_pow_eventually (d C : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ C * m ^ d ≤ 2 ^ m := by
  have hlim : Tendsto (fun m : ℕ => ((C : ℝ) * (m : ℝ) ^ d) / (2 : ℝ) ^ m) atTop (nhds 0) := by
    have h1 : Tendsto (fun x : ℝ => x ^ d * Real.exp (-(Real.log 2) * x)) atTop (nhds 0) := by
      have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have h2 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d
      have h3 : Tendsto (fun x : ℝ => (Real.log 2 * x) ^ d * Real.exp (-(Real.log 2 * x)))
          atTop (nhds 0) :=
        h2.comp (tendsto_id.const_mul_atTop hpos)
      have h4 := h3.const_mul ((Real.log 2) ^ d)⁻¹
      simp only [mul_zero] at h4
      refine h4.congr (fun x => ?_)
      have hne : Real.log 2 ^ d ≠ 0 := pow_ne_zero d hpos.ne'
      rw [mul_pow, neg_mul]
      field_simp [hne]
    have h5 : Tendsto (fun m : ℕ => (C : ℝ) * ((m : ℝ) ^ d * Real.exp (-(Real.log 2) * (m : ℝ))))
        atTop (nhds 0) := by
      simpa using (h1.comp tendsto_natCast_atTop_atTop).const_mul (C : ℝ)
    refine h5.congr (fun m => ?_)
    have h2pow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [h2pow, div_eq_mul_inv, ← Real.exp_neg, mul_assoc]
    ring_nf
  have hev := (tendsto_order.mp hlim).2 1 zero_lt_one
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  have hlt := hN (max N 1) (le_max_left _ _)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (max N 1) := by positivity
  rw [div_lt_one hpos] at hlt
  exact_mod_cast hlt.le

lemma sum_int_mul_log_ne_zero {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    {b : ℕ → ℤ} (hne : ∃ p ∈ S, b p ≠ 0) :
    ∑ p ∈ S, (b p : ℝ) * Real.log (p : ℝ) ≠ 0 := by
  intro hzero
  set Spos := S.filter (fun p => 0 < b p)
  set Sneg := S.filter (fun p => b p < 0)
  have hdisj : Disjoint Spos Sneg := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter] at hp1 hp2
    omega
  have hsplit : ∑ p ∈ S, (b p : ℝ) * Real.log (p : ℝ) =
      (∑ p ∈ Spos, ((b p).natAbs : ℝ) * Real.log (p : ℝ)) -
      (∑ p ∈ Sneg, ((b p).natAbs : ℝ) * Real.log (p : ℝ)) := by
    have hsub : Spos ∪ Sneg ⊆ S := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [← Finset.sum_subset hsub]
    · rw [Finset.sum_union hdisj, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mem_filter] at hp
        have hnat : ((b p).natAbs : ℤ) = b p := Int.natAbs_of_nonneg hp.2.le
        have hcast : ((b p).natAbs : ℝ) = (b p : ℝ) := by
          rw [← Int.cast_natCast (R := ℝ), hnat]
        rw [hcast]
      · apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mem_filter] at hp
        have hnat : -((b p).natAbs : ℤ) = b p := by
          have := Int.ofNat_natAbs_of_nonpos hp.2.le
          omega
        have hcast : -((b p).natAbs : ℝ) = (b p : ℝ) := by
          rw [← Int.cast_natCast (R := ℝ), ← Int.cast_neg, hnat]
        rw [← neg_mul, hcast]
    · intro p hp hnot
      simp only [Spos, Sneg, Finset.mem_union, Finset.mem_filter, not_or, not_and] at hnot
      have h0 : b p = 0 := by
        have h1 : ¬ (0 < b p) := hnot.1 hp
        have h2 : ¬ (b p < 0) := hnot.2 hp
        omega
      simp [h0]
  rw [hsplit, sub_eq_zero] at hzero
  set Ppos : ℕ := ∏ p ∈ Spos, p ^ (b p).natAbs
  set Pneg : ℕ := ∏ p ∈ Sneg, p ^ (b p).natAbs
  have hPpos_pos : 0 < Ppos :=
    Finset.prod_pos fun p hp => pow_pos (hS p (Finset.mem_filter.mp hp).1).pos _
  have hPneg_pos : 0 < Pneg :=
    Finset.prod_pos fun p hp => pow_pos (hS p (Finset.mem_filter.mp hp).1).pos _
  have hlog_eq : Real.log (Ppos : ℝ) = Real.log (Pneg : ℝ) := by
    have hL : Real.log (Ppos : ℝ) = ∑ p ∈ Spos, ((b p).natAbs : ℝ) * Real.log (p : ℝ) := by
      simp only [Ppos, Nat.cast_prod, Nat.cast_pow]
      rw [Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p _
        rw [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (hS p (Finset.mem_filter.mp hp).1).ne_zero)
    have hR : Real.log (Pneg : ℝ) = ∑ p ∈ Sneg, ((b p).natAbs : ℝ) * Real.log (p : ℝ) := by
      simp only [Pneg, Nat.cast_prod, Nat.cast_pow]
      rw [Real.log_prod]
      · apply Finset.sum_congr rfl
        intro p _
        rw [Real.log_pow]
      · intro p hp
        exact pow_ne_zero _ (by exact_mod_cast (hS p (Finset.mem_filter.mp hp).1).ne_zero)
    rw [hL, hR, hzero]
  have hPeq : Ppos = Pneg := by
    have hR : (Ppos : ℝ) = (Pneg : ℝ) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (by exact_mod_cast hPpos_pos))
        (Set.mem_Ioi.mpr (by exact_mod_cast hPneg_pos)) hlog_eq
    exact_mod_cast hR
  obtain ⟨p₀, hp₀S, hp₀ne⟩ := hne
  have hp₀pr : p₀.Prime := hS p₀ hp₀S
  have hcontra : ∀ (A B : Finset ℕ), Disjoint A B → (∀ q ∈ B, q.Prime) →
      p₀ ∈ A → 0 < (b p₀).natAbs →
      ∏ p ∈ A, p ^ (b p).natAbs = ∏ p ∈ B, p ^ (b p).natAbs → False := by
    intro A B hAB hB hp₀A hexp heq
    have hdvdA : p₀ ∣ ∏ p ∈ A, p ^ (b p).natAbs :=
      dvd_trans (dvd_pow_self p₀ (by omega)) (Finset.dvd_prod_of_mem _ hp₀A)
    rw [heq] at hdvdA
    obtain ⟨q, hqB, hq_dvd⟩ := (Prime.dvd_finsetProd_iff hp₀pr.prime _).mp hdvdA
    have hq_eq : p₀ = q :=
      (Nat.prime_dvd_prime_iff_eq hp₀pr (hB q hqB)).mp (hp₀pr.dvd_of_dvd_pow hq_dvd)
    subst hq_eq
    exact Finset.disjoint_left.mp hAB hp₀A hqB
  rcases lt_or_gt_of_ne hp₀ne with hlt | hgt
  · exact hcontra Sneg Spos hdisj.symm (fun q hq => hS q (Finset.mem_filter.mp hq).1)
      (Finset.mem_filter.mpr ⟨hp₀S, hlt⟩) (Int.natAbs_pos.mpr hp₀ne) hPeq.symm
  · exact hcontra Spos Sneg hdisj (fun q hq => hS q (Finset.mem_filter.mp hq).1)
      (Finset.mem_filter.mpr ⟨hp₀S, hgt⟩) (Int.natAbs_pos.mpr hp₀ne) hPeq

/- Section 2: Siegel's Lemma over `ℤ` -/

lemma siegel_lemma {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : κ → ι → ℤ) (H : ℕ) (hH : ∀ j i, (A j i).natAbs ≤ H)
    (hcard : 0 < Fintype.card ι) (h2 : 2 * Fintype.card κ ≤ Fintype.card ι) :
    ∃ x : ι → ℤ, (∃ i, x i ≠ 0) ∧
      (∀ i, (x i).natAbs ≤ 2 * Fintype.card ι * H + 1) ∧
      (∀ j, ∑ i, A j i * x i = 0) := by
  classical
  set X := Fintype.card ι
  set Y := Fintype.card κ
  set M := 2 * X * H + 1
  have hMpos : 1 ≤ M := by omega
  set R := X * H * M
  let f : (ι → Fin (M + 1)) → (κ → Fin (2 * R + 1)) := fun v j =>
    let s : ℤ := ∑ i : ι, A j i * (v i : ℤ)
    ⟨(s + R).toNat, by
      have habs : |s| ≤ (R : ℤ) := by
        calc |s| = |∑ i : ι, A j i * (v i : ℤ)| := rfl
          _ ≤ ∑ i : ι, |A j i * (v i : ℤ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : ι, ((H : ℤ) * (M : ℤ)) := by
              apply Finset.sum_le_sum
              intro i _
              rw [abs_mul]
              have h1 : |A j i| ≤ (H : ℤ) := by
                rw [← Int.natCast_natAbs]
                exact_mod_cast hH j i
              have h2v : |(v i : ℤ)| ≤ (M : ℤ) := by
                rw [abs_of_nonneg (Nat.cast_nonneg _)]
                exact_mod_cast Nat.lt_succ_iff.mp (v i).isLt
              exact mul_le_mul h1 h2v (abs_nonneg _) (Nat.cast_nonneg _)
          _ = (R : ℤ) := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, X, R]
              push_cast
              ring
      have hlo : -(R : ℤ) ≤ s := (abs_le.mp habs).1
      have hhi : s ≤ (R : ℤ) := (abs_le.mp habs).2
      omega⟩
  have hlt : Fintype.card (κ → Fin (2 * R + 1)) < Fintype.card (ι → Fin (M + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    have hstep : 2 * R + 1 < (M + 1) ^ 2 := by
      have h2R : 2 * R = 2 * X * H * M := by dsimp only [R]; ring
      have hM : 2 * X * H + 1 = M := rfl
      nlinarith
    by_cases hY : Y = 0
    · change (2 * R + 1) ^ Y < (M + 1) ^ X
      rw [hY, pow_zero]
      exact one_lt_pow₀ (by omega : 1 < M + 1) (by omega)
    · calc (2 * R + 1) ^ Y
          < ((M + 1) ^ 2) ^ Y := Nat.pow_lt_pow_left hstep hY
        _ = (M + 1) ^ (2 * Y) := by rw [← pow_mul]
        _ ≤ (M + 1) ^ X := Nat.pow_le_pow_right (by omega) h2
  obtain ⟨v₁, v₂, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  refine ⟨fun i => (v₁ i : ℤ) - (v₂ i : ℤ), ?_, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    apply hne
    funext i
    have hi := hall i
    ext
    omega
  · intro i
    have h1 := (v₁ i).isLt
    have h2i := (v₂ i).isLt
    have habs : |((v₁ i : ℤ) - (v₂ i : ℤ))| ≤ (M : ℤ) := by
      rw [abs_le]; constructor <;> omega
    exact Int.ofNat_le.mp (by rw [Int.natCast_natAbs]; exact habs)
  · intro j
    have hjeq := congr_fun hfeq j
    have hval := congr_arg Fin.val hjeq
    dsimp only [f] at hval
    have hbound : ∀ v : ι → Fin (M + 1), -(R : ℤ) ≤ ∑ i : ι, A j i * (v i : ℤ) := by
      intro v
      have habs : |∑ i : ι, A j i * (v i : ℤ)| ≤ (R : ℤ) := by
        calc |∑ i : ι, A j i * (v i : ℤ)|
            ≤ ∑ i : ι, |A j i * (v i : ℤ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : ι, ((H : ℤ) * (M : ℤ)) := by
              apply Finset.sum_le_sum
              intro i _
              rw [abs_mul]
              have h1 : |A j i| ≤ (H : ℤ) := by
                rw [← Int.natCast_natAbs]; exact_mod_cast hH j i
              have h2v : |(v i : ℤ)| ≤ (M : ℤ) := by
                rw [abs_of_nonneg (Nat.cast_nonneg _)]
                exact_mod_cast Nat.lt_succ_iff.mp (v i).isLt
              exact mul_le_mul h1 h2v (abs_nonneg _) (Nat.cast_nonneg _)
          _ = (R : ℤ) := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, X, R]
              push_cast; ring
      exact (abs_le.mp habs).1
    have h1 := hbound v₁
    have h2v := hbound v₂
    have heqsum : ∑ i : ι, A j i * (v₁ i : ℤ) = ∑ i : ι, A j i * (v₂ i : ℤ) := by omega
    calc ∑ i : ι, A j i * ((v₁ i : ℤ) - (v₂ i : ℤ))
        = (∑ i : ι, A j i * (v₁ i : ℤ)) - (∑ i : ι, A j i * (v₂ i : ℤ)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl; intro i _; ring
      _ = 0 := sub_eq_zero.mpr heqsum

/- Section 3: Feldman Block Polynomials, Denominators, and Algebraic Size Bounds -/

noncomputable def deltaPoly (a : ℕ) : Polynomial ℚ :=
  ((a.factorial : ℚ)⁻¹) • ∏ r ∈ Finset.range a, (X + C ((r + 1 : ℕ) : ℚ))

noncomputable def binomPoly (j : ℕ) : Polynomial ℚ :=
  ((j.factorial : ℚ)⁻¹) • ∏ r ∈ Finset.range j, (X - C (r : ℚ))

noncomputable def feldmanPoly (k l₀ : ℕ) : Polynomial ℚ :=
  (deltaPoly k) ^ (l₀ / k) * deltaPoly (l₀ % k)

lemma deltaPoly_zero : deltaPoly 0 = 1 := by
  simp [deltaPoly]

lemma binomPoly_zero : binomPoly 0 = 1 := by
  simp [binomPoly]

lemma natDegree_deltaPoly (a : ℕ) : (deltaPoly a).natDegree = a := by
  unfold deltaPoly
  have hfac : ((a.factorial : ℚ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero a)
  rw [Polynomial.smul_eq_C_mul, natDegree_C_mul hfac]
  rw [natDegree_prod_of_monic _ _ fun r _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma deltaPoly_ne_zero (a : ℕ) : deltaPoly a ≠ 0 := by
  unfold deltaPoly
  have hfac : ((a.factorial : ℚ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero a)
  have hmon : (∏ r ∈ Finset.range a, (X + C ((r + 1 : ℕ) : ℚ))).Monic :=
    monic_prod_of_monic _ _ fun r _ => monic_X_add_C _
  exact smul_ne_zero hfac hmon.ne_zero

lemma natDegree_feldmanPoly {k : ℕ} (_hk : 0 < k) (l₀ : ℕ) :
    (feldmanPoly k l₀).natDegree = l₀ := by
  unfold feldmanPoly
  rw [natDegree_mul (pow_ne_zero _ (deltaPoly_ne_zero k)) (deltaPoly_ne_zero _),
    natDegree_pow, natDegree_deltaPoly, natDegree_deltaPoly]
  rw [mul_comm]
  exact Nat.div_add_mod l₀ k

lemma feldmanPoly_ne_zero (k l₀ : ℕ) : feldmanPoly k l₀ ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (deltaPoly_ne_zero k)) (deltaPoly_ne_zero _)

lemma sum_feldmanPoly_ne_zero {k L₀ : ℕ} (hk : 0 < k) (c : Fin (L₀ + 1) → ℚ)
    (hne : ∃ i, c i ≠ 0) :
    ∑ i : Fin (L₀ + 1), C (c i) * feldmanPoly k i.val ≠ 0 := by
  classical
  set S := Finset.univ.filter (fun i : Fin (L₀ + 1) => c i ≠ 0)
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  set imax := S.max' hSne
  have himax_mem : imax ∈ S := Finset.max'_mem S hSne
  have himax_ne : c imax ≠ 0 := (Finset.mem_filter.mp himax_mem).2
  have hterm_deg : (C (c imax) * feldmanPoly k imax.val).natDegree = imax.val := by
    rw [natDegree_C_mul himax_ne, natDegree_feldmanPoly hk]
  have hterm_ne : C (c imax) * feldmanPoly k imax.val ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr himax_ne) (feldmanPoly_ne_zero k _)
  have hsum_eq : ∑ i : Fin (L₀ + 1), C (c i) * feldmanPoly k i.val =
      C (c imax) * feldmanPoly k imax.val +
      ∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val := by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · rw [← Finset.add_sum_erase _ _ himax_mem]
    · intro i _ hi
      have h0 : c i = 0 := by
        by_contra hc
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩)
      simp [h0]
  rw [hsum_eq]
  have hrest_deg : (∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val).natDegree < imax.val ∨
      ∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val = 0 := by
    by_cases h0 : ∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val = 0
    · exact Or.inr h0
    · left
      have hlt : ∀ i ∈ S.erase imax, (C (c i) * feldmanPoly k i.val).natDegree < imax.val := by
        intro i hi
        have hiS : i ∈ S := Finset.mem_of_mem_erase hi
        have hine : i ≠ imax := Finset.ne_of_mem_erase hi
        have hle : i ≤ imax := Finset.le_max' S i hiS
        have hlt_i : i < imax := lt_of_le_of_ne hle hine
        have hci : c i ≠ 0 := (Finset.mem_filter.mp hiS).2
        rw [natDegree_C_mul hci, natDegree_feldmanPoly hk]
        exact hlt_i
      have hle_max := natDegree_sum_le (S.erase imax) (fun i => C (c i) * feldmanPoly k i.val)
      have hfold : (S.erase imax).fold max 0 (fun i => (C (c i) * feldmanPoly k i.val).natDegree) <
          imax.val := by
        rw [Finset.fold_max_lt]
        refine ⟨?_, hlt⟩
        have hne_er : (S.erase imax).Nonempty := by
          by_contra hem
          rw [Finset.not_nonempty_iff_eq_empty] at hem
          rw [hem, Finset.sum_empty] at h0
          exact h0 rfl
        obtain ⟨j, hj⟩ := hne_er
        exact lt_of_le_of_lt (Nat.zero_le _) (hlt j hj)
      exact lt_of_le_of_lt hle_max hfold
  rcases hrest_deg with hlt | h0
  · intro heq
    have hneg : C (c imax) * feldmanPoly k imax.val =
        -(∑ i ∈ S.erase imax, C (c i) * feldmanPoly k i.val) := eq_neg_of_add_eq_zero_left heq
    have hdeg := congr_arg Polynomial.natDegree hneg
    rw [natDegree_neg, hterm_deg] at hdeg
    omega
  · rw [h0, add_zero]
    exact hterm_ne

lemma eval_binomPoly_nat (j n : ℕ) : (binomPoly j).eval (n : ℚ) = (n.choose j : ℚ) := by
  unfold binomPoly
  rw [eval_smul, smul_eq_mul, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have hprod : ∏ r ∈ Finset.range j, ((n : ℚ) - (r : ℚ)) = (n.descFactorial j : ℚ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.prod_range_succ, ih, Nat.descFactorial_succ]
      by_cases hjn : j ≤ n
      · rw [Nat.cast_mul, Nat.cast_sub hjn, mul_comm]
      · have hzero : n.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        simp [hzero]
  rw [hprod, inv_mul_eq_div, Nat.choose_eq_descFactorial_div_factorial]
  rw [Nat.cast_div (Nat.factorial_dvd_descFactorial n j) (by exact_mod_cast Nat.factorial_ne_zero j)]

lemma eval_deltaPoly_nat (a n : ℕ) : (deltaPoly a).eval (n : ℚ) = ((n + a).choose a : ℚ) := by
  unfold deltaPoly
  rw [eval_smul, smul_eq_mul, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  have hprod : ∏ r ∈ Finset.range a, ((n : ℚ) + ((r + 1 : ℕ) : ℚ)) =
      ((n + a).descFactorial a : ℚ) := by
    have hnat : ∏ r ∈ Finset.range a, (n + (r + 1)) = (n + a).descFactorial a := by
      induction a with
      | zero => simp
      | succ a ih =>
        rw [Finset.prod_range_succ, ih, ← add_assoc, Nat.succ_descFactorial_succ, mul_comm]
    have hcast : ∏ r ∈ Finset.range a, ((n : ℚ) + ((r + 1 : ℕ) : ℚ)) =
        ((∏ r ∈ Finset.range a, (n + (r + 1)) : ℕ) : ℚ) := by
      push_cast; rfl
    rw [hcast, hnat]
  rw [hprod, inv_mul_eq_div, Nat.choose_eq_descFactorial_div_factorial]
  rw [Nat.cast_div (Nat.factorial_dvd_descFactorial (n + a) a)
    (by exact_mod_cast Nat.factorial_ne_zero a)]

lemma taylor_deltaPoly_eq (a s : ℕ) :
    Polynomial.taylor (s : ℚ) (deltaPoly a) =
      ∑ j ∈ Finset.range (a + 1), C (((s + a).choose (a - j) : ℕ) : ℚ) * binomPoly j := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := Set.range (fun n : ℕ => (n : ℚ))) ?_ ?_
  · intro x hx
    obtain ⟨n, rfl⟩ := hx
    simp only [Set.mem_ofPred_eq, Polynomial.taylor_apply, eval_comp, eval_add, eval_X, eval_C,
      eval_finsetSum, eval_mul]
    rw [show (n : ℚ) + (s : ℚ) = ((n + s : ℕ) : ℚ) by push_cast; ring]
    rw [eval_deltaPoly_nat]
    have hch : ((n + s + a).choose a : ℚ) =
        ∑ j ∈ Finset.range (a + 1), (((s + a).choose (a - j) : ℕ) : ℚ) * (n.choose j : ℚ) := by
      have h1 : n + s + a = (s + a) + n := by omega
      rw [h1, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      push_cast
      rw [← Finset.sum_range_reflect]
      apply Finset.sum_congr rfl
      intro j hj
      have hja : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hsub : a - (a - j) = j := by omega
      simp [hsub]
    rw [hch]
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_binomPoly_nat]
  · exact Set.infinite_range_of_injective Nat.cast_injective

lemma dvd_lcmUpto {r k : ℕ} (hr1 : 1 ≤ r) (hrk : r ≤ k) : r ∣ Nat.lcmUpto k := by
  unfold Nat.lcmUpto
  exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hr1, hrk⟩)

lemma lcmUpto_pow_mul_coeff_binomPoly_int {k j m : ℕ} (hjk : j ≤ k) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (binomPoly j).coeff m := by
  set d := Nat.lcmUpto k
  have hcomp_coeff : ((binomPoly j).comp (C (d : ℚ) * X)).coeff m =
      (d : ℚ) ^ m * (binomPoly j).coeff m := by
    rw [Polynomial.comp_C_mul_X_coeff]
    ring
  rw [← hcomp_coeff]
  suffices hmem : ∃ P : Polynomial ℤ, P.map (Int.castRingHom ℚ) =
      (binomPoly j).comp (C (d : ℚ) * X) by
    obtain ⟨P, hP⟩ := hmem
    refine ⟨P.coeff m, ?_⟩
    rw [← hP, Polynomial.coeff_map, Int.coe_castRingHom]
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · refine ⟨1, ?_⟩
    simp [binomPoly_zero]
  · have hfac : (j.factorial : ℚ) = (j : ℚ) * ∏ r ∈ Finset.Ico 1 j, (r : ℚ) := by
      have hnat : j.factorial = j * ∏ r ∈ Finset.Ico 1 j, r := by
        cases j with
        | zero => omega
        | succ j' =>
          rw [Nat.factorial_succ]
          congr 1
          clear hcomp_coeff hjpos hjk
          induction j' with
          | zero => simp
          | succ t ih =>
            rw [Nat.factorial_succ, ih]
            have hIco : Finset.Ico 1 (t + 2) = insert (t + 1) (Finset.Ico 1 (t + 1)) := by
              ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
            rw [hIco, Finset.prod_insert (by simp)]
      rw [← Nat.cast_prod, ← Nat.cast_mul]
      exact_mod_cast hnat
    have hprod_split : ∏ r ∈ Finset.range j, (X - C (r : ℚ)) =
        X * ∏ r ∈ Finset.Ico 1 j, (X - C (r : ℚ)) := by
      have hrg : Finset.range j = insert 0 (Finset.Ico 1 j) := by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hrg, Finset.prod_insert (by simp), Nat.cast_zero, C_0, sub_zero]
    have hbinom_eq : binomPoly j =
        (C ((j : ℚ)⁻¹) * X) * ∏ r ∈ Finset.Ico 1 j, (C ((r : ℚ)⁻¹) * X - 1) := by
      unfold binomPoly
      rw [hprod_split, hfac, mul_inv, Polynomial.smul_eq_C_mul, C_mul, ← Finset.prod_inv_distrib]
      have h1 : C (∏ r ∈ Finset.Ico 1 j, (r : ℚ)⁻¹) * (∏ r ∈ Finset.Ico 1 j, (X - C (r : ℚ))) =
          ∏ r ∈ Finset.Ico 1 j, (C ((r : ℚ)⁻¹) * X - 1) := by
        rw [map_prod, ← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro r hr
        have hr0 : (r : ℚ) ≠ 0 := by
          have := (Finset.mem_Ico.mp hr).1
          exact_mod_cast (by omega : r ≠ 0)
        rw [mul_sub, ← C_mul, inv_mul_cancel₀ hr0, C_1]
      calc (C (j : ℚ)⁻¹ * C (∏ r ∈ Finset.Ico 1 j, (r : ℚ)⁻¹)) *
            (X * ∏ r ∈ Finset.Ico 1 j, (X - C (r : ℚ)))
          = (C (j : ℚ)⁻¹ * X) *
            (C (∏ r ∈ Finset.Ico 1 j, (r : ℚ)⁻¹) * ∏ r ∈ Finset.Ico 1 j, (X - C (r : ℚ))) := by ring
        _ = (C (j : ℚ)⁻¹ * X) * ∏ r ∈ Finset.Ico 1 j, (C ((r : ℚ)⁻¹) * X - 1) := by rw [h1]
    have hdvd_j : j ∣ d := dvd_lcmUpto hjpos hjk
    refine ⟨(C ((d / j : ℕ) : ℤ) * X) * ∏ r ∈ Finset.Ico 1 j, (C ((d / r : ℕ) : ℤ) * X - 1), ?_⟩
    rw [hbinom_eq, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      Polynomial.prod_comp]
    simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_one, Int.coe_castRingHom, Int.cast_natCast]
    congr 1
    · rw [← mul_assoc, ← C_mul]
      have hj0 : (j : ℚ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
      have hq : ((d / j : ℕ) : ℚ) = (j : ℚ)⁻¹ * (d : ℚ) := by
        rw [Nat.cast_div hdvd_j hj0, div_eq_inv_mul]
      rw [hq]
    · apply Finset.prod_congr rfl
      intro r hr
      rw [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
        Polynomial.one_comp, ← mul_assoc, ← C_mul]
      have hr1 : 1 ≤ r := (Finset.mem_Ico.mp hr).1
      have hrk : r ≤ k := le_trans (le_of_lt (Finset.mem_Ico.mp hr).2) hjk
      have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
      have hq : ((d / r : ℕ) : ℚ) = (r : ℚ)⁻¹ * (d : ℚ) := by
        rw [Nat.cast_div (dvd_lcmUpto hr1 hrk) hr0, div_eq_inv_mul]
      rw [hq]

lemma lcmUpto_pow_mul_hasseDeriv_deltaPoly_int {k a m s : ℕ} (hak : a ≤ k) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m (deltaPoly a)).eval (s : ℚ) := by
  rw [← Polynomial.taylor_coeff, taylor_deltaPoly_eq, Polynomial.finsetSum_coeff, Finset.mul_sum]
  have hterm : ∀ j ∈ Finset.range (a + 1), ∃ z : ℤ,
      (z : ℚ) = (Nat.lcmUpto k : ℚ) ^ m * (C (((s + a).choose (a - j) : ℕ) : ℚ) * binomPoly j).coeff m := by
    intro j hj
    have hjk : j ≤ k := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hak
    obtain ⟨z, hz⟩ := lcmUpto_pow_mul_coeff_binomPoly_int (m := m) hjk
    refine ⟨(((s + a).choose (a - j) : ℕ) : ℤ) * z, ?_⟩
    rw [Polynomial.coeff_C_mul, Int.cast_mul, Int.cast_natCast, hz]
    ring
  choose f hf using hterm
  refine ⟨∑ j ∈ (Finset.range (a + 1)).attach, f j.1 j.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.range (a + 1))]
  apply Finset.sum_congr rfl
  intro j _
  exact hf j.1 j.2

lemma lcmUpto_pow_mul_hasseDeriv_mul_int {k s : ℕ} {P Q : Polynomial ℚ}
    (hP : ∀ m, ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m P).eval (s : ℚ))
    (hQ : ∀ m, ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m Q).eval (s : ℚ))
    (m : ℕ) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m (P * Q)).eval (s : ℚ) := by
  rw [Polynomial.hasseDeriv_mul, Polynomial.eval_finsetSum, Finset.mul_sum]
  have hterm : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ∃ z : ℤ,
      (z : ℚ) = (Nat.lcmUpto k : ℚ) ^ m *
        ((Polynomial.hasseDeriv ij.1 P * Polynomial.hasseDeriv ij.2 Q).eval (s : ℚ)) := by
    intro ij hij
    obtain ⟨z₁, hz₁⟩ := hP ij.1
    obtain ⟨z₂, hz₂⟩ := hQ ij.2
    refine ⟨z₁ * z₂, ?_⟩
    rw [Int.cast_mul, hz₁, hz₂, Polynomial.eval_mul]
    have hsum : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [← hsum, pow_add]
    ring
  choose f hf using hterm
  refine ⟨∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal m).attach, f ij.1 ij.2, ?_⟩
  rw [Int.cast_sum, ← Finset.sum_attach (Finset.HasAntidiagonal.antidiagonal m)]
  apply Finset.sum_congr rfl
  intro ij _
  exact hf ij.1 ij.2

lemma lcmUpto_pow_mul_hasseDeriv_pow_int {k s : ℕ} {P : Polynomial ℚ}
    (hP : ∀ m, ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m P).eval (s : ℚ))
    (q m : ℕ) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) * (Polynomial.hasseDeriv m (P ^ q)).eval (s : ℚ) := by
  induction q generalizing m with
  | zero =>
    rw [pow_zero]
    cases m with
    | zero => exact ⟨1, by simp⟩
    | succ m =>
      refine ⟨0, ?_⟩
      have h0 : Polynomial.hasseDeriv (m + 1) (1 : Polynomial ℚ) = 0 := by
        ext j
        rw [Polynomial.hasseDeriv_coeff, Polynomial.coeff_zero]
        have hlt : 1 ≤ j + (m + 1) := by omega
        rw [Polynomial.coeff_one, if_neg (by omega), mul_zero]
      rw [h0, Polynomial.eval_zero, mul_zero, Int.cast_zero]
  | succ q ih =>
    rw [pow_succ]
    exact lcmUpto_pow_mul_hasseDeriv_mul_int ih hP m

lemma lcmUpto_pow_mul_hasseDeriv_feldmanPoly_int {k : ℕ} (hk : 0 < k) (l₀ m s : ℕ) :
    ∃ z : ℤ, (z : ℚ) = ((Nat.lcmUpto k : ℚ) ^ m) *
      (Polynomial.hasseDeriv m (feldmanPoly k l₀)).eval (s : ℚ) := by
  unfold feldmanPoly
  apply lcmUpto_pow_mul_hasseDeriv_mul_int
  · exact lcmUpto_pow_mul_hasseDeriv_pow_int
      (fun r => lcmUpto_pow_mul_hasseDeriv_deltaPoly_int le_rfl) _
  · exact fun r => lcmUpto_pow_mul_hasseDeriv_deltaPoly_int (le_of_lt (Nat.mod_lt l₀ hk))

lemma log_lcmUpto_le (k : ℕ) : Real.log (Nat.lcmUpto k : ℝ) ≤ 6 * (k : ℝ) := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  have h1 := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg k)
  have hlog4 : Real.log 4 < 2 := by
    have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    have := Real.log_two_lt_d9
    linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

lemma lcmUpto_le_exp (k : ℕ) : (Nat.lcmUpto k : ℝ) ≤ Real.exp (6 * (k : ℝ)) := by
  have hpos : (0 : ℝ) < (Nat.lcmUpto k : ℝ) := by exact_mod_cast Nat.lcmUpto_pos k
  rw [← Real.log_le_iff_le_exp hpos]
  exact log_lcmUpto_le k

/- Purely algebraic coefficient majorant `normSum` for `feldmanPoly` -/

noncomputable def normSum (P : Polynomial ℂ) : ℝ :=
  ∑ m ∈ Finset.range (P.natDegree + 1), ‖P.coeff m‖

lemma normSum_nonneg (P : Polynomial ℂ) : 0 ≤ normSum P :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma normSum_eq_sum_of_natDegree_le {P : Polynomial ℂ} {N : ℕ} (hN : P.natDegree ≤ N) :
    normSum P = ∑ m ∈ Finset.range (N + 1), ‖P.coeff m‖ := by
  unfold normSum
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro m _ hm
  rw [Finset.mem_range] at hm
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]

lemma norm_coeff_le_normSum (P : Polynomial ℂ) (m : ℕ) : ‖P.coeff m‖ ≤ normSum P := by
  by_cases hm : m ≤ P.natDegree
  · exact Finset.single_le_sum (fun _ _ => norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
    exact normSum_nonneg P

lemma normSum_smul (c : ℂ) (P : Polynomial ℂ) : normSum (c • P) = ‖c‖ * normSum P := by
  by_cases hc : c = 0
  · subst hc; simp [normSum]
  · rw [normSum_eq_sum_of_natDegree_le (Polynomial.natDegree_smul_le c P)]
    unfold normSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Polynomial.coeff_smul, smul_eq_mul, norm_mul]

lemma normSum_X_add_C (a : ℂ) : normSum (X + C a) ≤ 1 + ‖a‖ := by
  rw [normSum_eq_sum_of_natDegree_le (show (X + C a).natDegree ≤ 1 by
    exact le_trans (Polynomial.natDegree_add_le _ _) (by simp))]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, Polynomial.coeff_add, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_one, Polynomial.coeff_C_succ, add_zero, norm_one]
  linarith

lemma normSum_mul_le (P Q : Polynomial ℂ) : normSum (P * Q) ≤ normSum P * normSum Q := by
  set N := P.natDegree + Q.natDegree
  rw [normSum_eq_sum_of_natDegree_le (Polynomial.natDegree_mul_le)]
  calc ∑ m ∈ Finset.range (N + 1), ‖(P * Q).coeff m‖
      ≤ ∑ m ∈ Finset.range (N + 1),
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖ := by
        apply Finset.sum_le_sum
        intro m _
        rw [Polynomial.coeff_mul]
        calc ‖∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, P.coeff ij.1 * Q.coeff ij.2‖
            ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1 * Q.coeff ij.2‖ :=
              norm_sum_le _ _
          _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖ := by
              apply Finset.sum_congr rfl; intro ij _; rw [norm_mul]
    _ = (∑ i ∈ Finset.range (P.natDegree + 1), ‖P.coeff i‖) *
        (∑ j ∈ Finset.range (Q.natDegree + 1), ‖Q.coeff j‖) := by
        rw [Finset.sum_mul_sum]
        set S := (Finset.range (P.natDegree + 1)) ×ˢ (Finset.range (Q.natDegree + 1))
        calc ∑ m ∈ Finset.range (N + 1),
              ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖
            = ∑ m ∈ Finset.range (N + 1),
              ∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal m).filter (· ∈ S),
                ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖ := by
              apply Finset.sum_congr rfl
              intro m _
              symm
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro ij hij_mem hij
              have hnotS : ij ∉ S := fun hS => hij (Finset.mem_filter.mpr ⟨hij_mem, hS⟩)
              simp only [S, Finset.mem_product, Finset.mem_range, not_and] at hnotS
              by_cases h1 : ij.1 < P.natDegree + 1
              · have h2 : ¬ (ij.2 < Q.natDegree + 1) := hnotS h1
                rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), norm_zero, mul_zero]
              · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (by omega), norm_zero, zero_mul]
          _ = ∑ ij ∈ S, ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖ := by
              rw [← Finset.sum_biUnion]
              · congr 1
                ext ij
                simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
                  Finset.HasAntidiagonal.mem_antidiagonal, S, Finset.mem_product]
                constructor
                · rintro ⟨_, _, _, hmem⟩; exact hmem
                · intro hmem
                  exact ⟨ij.1 + ij.2, by omega, rfl, hmem⟩
              · intro m₁ _ m₂ _ hne
                change Disjoint _ _
                rw [Finset.disjoint_left]
                intro ij h1 h2
                rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at h1 h2
                exact hne (h1.1.symm.trans h2.1)
          _ = ∑ i ∈ Finset.range (P.natDegree + 1),
              ∑ j ∈ Finset.range (Q.natDegree + 1), ‖P.coeff i‖ * ‖Q.coeff j‖ :=
              Finset.sum_product (Finset.range (P.natDegree + 1)) (Finset.range (Q.natDegree + 1))
                (fun ij => ‖P.coeff ij.1‖ * ‖Q.coeff ij.2‖)

lemma normSum_one : normSum 1 = 1 := by
  simp [normSum]

lemma normSum_prod_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) :
    normSum (∏ i ∈ s, f i) ≤ ∏ i ∈ s, normSum (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normSum_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact le_trans (normSum_mul_le _ _)
      (mul_le_mul_of_nonneg_left ih (normSum_nonneg _))

lemma normSum_pow_le (P : Polynomial ℂ) (q : ℕ) : normSum (P ^ q) ≤ (normSum P) ^ q := by
  induction q with
  | zero => simp [normSum_one]
  | succ q ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (normSum_mul_le _ _) (mul_le_mul_of_nonneg_right ih (normSum_nonneg _))

lemma pow_div_factorial_mono {X : ℝ} (hX : 0 ≤ X) {a k : ℕ} (hak : a ≤ k) :
    (X + (a : ℝ)) ^ a / (a.factorial : ℝ) ≤ (X + (k : ℝ)) ^ k / (k.factorial : ℝ) := by
  induction hak with
  | refl => exact le_rfl
  | @step m hm ih =>
    refine le_trans ih ?_
    have h1 : (1 : ℝ) ≤ (X + ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ) := by
      rw [one_le_div (by positivity)]
      push_cast; linarith
    have h2 : (X + (m : ℝ)) ^ m ≤ (X + ((m + 1 : ℕ) : ℝ)) ^ m := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast; linarith
    have hfac : (((m + 1).factorial : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) * (m.factorial : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    calc (X + (m : ℝ)) ^ m / (m.factorial : ℝ)
        = (X + (m : ℝ)) ^ m / (m.factorial : ℝ) * 1 := (mul_one _).symm
      _ ≤ (X + ((m + 1 : ℕ) : ℝ)) ^ m / (m.factorial : ℝ) *
          ((X + ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ)) := by
          apply mul_le_mul (div_le_div_of_nonneg_right h2 (by positivity)) h1 zero_le_one
            (by positivity)
      _ = (X + ((m + 1 : ℕ) : ℝ)) ^ (m + 1) / (((m + 1).factorial : ℕ) : ℝ) := by
          rw [pow_succ, hfac]; ring

lemma pow_div_factorial_le_exp_pow {X : ℝ} (hX : 0 ≤ X) {k : ℕ} (hk : 0 < k) :
    (X + (k : ℝ)) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1 * (X + (k : ℝ)) / (k : ℝ)) ^ k := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hexp : (k : ℝ) ^ k / (k.factorial : ℝ) ≤ Real.exp (k : ℝ) := by
    have h := Real.sum_le_exp_of_nonneg hkpos.le (k + 1)
    exact le_trans (Finset.single_le_sum
      (f := fun i => (k : ℝ) ^ i / (i.factorial : ℝ))
      (fun i _ => div_nonneg (pow_nonneg hkpos.le _) (Nat.cast_nonneg _))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))) h
  have hfac_inv : ((k.factorial : ℝ))⁻¹ ≤ (Real.exp 1 / (k : ℝ)) ^ k := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
    rw [le_div_iff₀ (pow_pos hkpos k), inv_mul_eq_div]
    exact hexp
  calc (X + (k : ℝ)) ^ k / (k.factorial : ℝ)
      = (X + (k : ℝ)) ^ k * ((k.factorial : ℝ))⁻¹ := div_eq_mul_inv _ _
    _ ≤ (X + (k : ℝ)) ^ k * (Real.exp 1 / (k : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_left hfac_inv (by positivity)
    _ = (Real.exp 1 * (X + (k : ℝ)) / (k : ℝ)) ^ k := by
        rw [← mul_pow]; ring_nf

lemma normSum_taylor_deltaPoly_le {a k : ℕ} (hk : 0 < k) (hak : a ≤ k) (z : ℂ) {R : ℝ}
    (hR : ‖z‖ ≤ R) :
    normSum (Polynomial.taylor z ((deltaPoly a).map (algebraMap ℚ ℂ))) ≤
      (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ k := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) hR
  unfold deltaPoly
  rw [Polynomial.map_smul, Polynomial.map_prod, Polynomial.taylor_apply,
    Polynomial.smul_comp, Polynomial.prod_comp, normSum_smul]
  have hnorm_smul : ‖(algebraMap ℚ ℂ) ((a.factorial : ℚ)⁻¹)‖ = ((a.factorial : ℝ))⁻¹ := by
    simp
  have hprod : normSum (∏ r ∈ Finset.range a,
      (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z)) ≤
      (R + 1 + (a : ℝ)) ^ a := by
    calc normSum (∏ r ∈ Finset.range a,
            (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z))
        ≤ ∏ r ∈ Finset.range a,
            normSum ((Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z)) :=
          normSum_prod_le _ _
      _ ≤ ∏ _r ∈ Finset.range a, (R + 1 + (a : ℝ)) := by
          apply Finset.prod_le_prod (fun _ _ => normSum_nonneg _)
          intro r hr
          have hra : r + 1 ≤ a := Finset.mem_range.mp hr
          have heq : (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z) =
              X + C (z + ((r + 1 : ℕ) : ℂ)) := by
            simp [Polynomial.add_comp, Polynomial.X_comp, add_assoc]
          rw [heq]
          calc normSum (X + C (z + ((r + 1 : ℕ) : ℂ)))
              ≤ 1 + ‖z + ((r + 1 : ℕ) : ℂ)‖ := normSum_X_add_C _
            _ ≤ 1 + (‖z‖ + ‖((r + 1 : ℕ) : ℂ)‖) := by
                linarith [norm_add_le z ((r + 1 : ℕ) : ℂ)]
            _ ≤ R + 1 + (a : ℝ) := by
                rw [Complex.norm_natCast]
                have hle : ((r + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hra
                linarith
      _ = (R + 1 + (a : ℝ)) ^ a := by simp
  have hstep : ‖(algebraMap ℚ ℂ) ((a.factorial : ℚ)⁻¹)‖ *
      normSum (∏ r ∈ Finset.range a,
        (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z)) ≤
      (R + 1 + (a : ℝ)) ^ a / (a.factorial : ℝ) := by
    rw [hnorm_smul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hprod (by positivity)
  calc ‖(algebraMap ℚ ℂ) ((a.factorial : ℚ)⁻¹)‖ *
        normSum (∏ r ∈ Finset.range a,
          (Polynomial.map (algebraMap ℚ ℂ) (X + C ((r + 1 : ℕ) : ℚ))).comp (X + C z))
      ≤ (R + 1 + (a : ℝ)) ^ a / (a.factorial : ℝ) := hstep
    _ ≤ (R + 1 + (k : ℝ)) ^ k / (k.factorial : ℝ) :=
          pow_div_factorial_mono (by linarith) hak
    _ ≤ (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ k :=
          pow_div_factorial_le_exp_pow (by linarith) hk

lemma norm_eval_hasseDeriv_feldmanPoly_le {k L₀ l₀ m : ℕ} (hk : 0 < k) (hl : l₀ ≤ L₀)
    (z : ℂ) {R : ℝ} (hR : ‖z‖ ≤ R) :
    ‖((Polynomial.hasseDeriv m (feldmanPoly k l₀)).map (algebraMap ℚ ℂ)).eval z‖ ≤
      (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) hR
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbase_ge1 : (1 : ℝ) ≤ Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ) := by
    rw [one_le_div hkpos]
    have he1 : (1 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    nlinarith
  rw [← Polynomial.hasseDeriv_map, ← Polynomial.taylor_coeff]
  refine le_trans (norm_coeff_le_normSum _ m) ?_
  unfold feldmanPoly
  rw [Polynomial.map_mul, Polynomial.map_pow, Polynomial.taylor_apply,
    Polynomial.mul_comp, Polynomial.pow_comp]
  have h1 := normSum_taylor_deltaPoly_le hk le_rfl z hR
  have h2 := normSum_taylor_deltaPoly_le hk (le_of_lt (Nat.mod_lt l₀ hk)) z hR
  rw [Polynomial.taylor_apply] at h1 h2
  calc normSum (((deltaPoly k).map (algebraMap ℚ ℂ)).comp (X + C z) ^ (l₀ / k) *
          ((deltaPoly (l₀ % k)).map (algebraMap ℚ ℂ)).comp (X + C z))
      ≤ normSum (((deltaPoly k).map (algebraMap ℚ ℂ)).comp (X + C z) ^ (l₀ / k)) *
        normSum (((deltaPoly (l₀ % k)).map (algebraMap ℚ ℂ)).comp (X + C z)) :=
          normSum_mul_le _ _
    _ ≤ (normSum (((deltaPoly k).map (algebraMap ℚ ℂ)).comp (X + C z))) ^ (l₀ / k) *
        normSum (((deltaPoly (l₀ % k)).map (algebraMap ℚ ℂ)).comp (X + C z)) :=
          mul_le_mul_of_nonneg_right (normSum_pow_le _ _) (normSum_nonneg _)
    _ ≤ ((Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ k) ^ (l₀ / k) *
        (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ k := by
          exact mul_le_mul (pow_le_pow_left₀ (normSum_nonneg _) h1 _) h2 (normSum_nonneg _)
            (by positivity)
    _ = (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (k * (l₀ / k) + k) := by
          rw [← pow_mul, ← pow_add]
    _ ≤ (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) := by
          apply pow_le_pow_right₀ hbase_ge1
          have hdiv : k * (l₀ / k) ≤ l₀ := Nat.mul_div_le l₀ k
          omega

/- Section 4: Zero-Contour-Integral Hermite–Schwarz Extrapolation Lemma -/

noncomputable def normSumHalf (P : Polynomial ℂ) : ℝ :=
  ∑ m ∈ Finset.range (P.natDegree + 1), ‖P.coeff m‖ * ((1 / 2 : ℝ) ^ m)

lemma normSumHalf_nonneg (P : Polynomial ℂ) : 0 ≤ normSumHalf P :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (by positivity)

lemma normSumHalf_eq_sum_of_natDegree_le {P : Polynomial ℂ} {N : ℕ} (hN : P.natDegree ≤ N) :
    normSumHalf P = ∑ m ∈ Finset.range (N + 1), ‖P.coeff m‖ * ((1 / 2 : ℝ) ^ m) := by
  unfold normSumHalf
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro m _ hm
  rw [Finset.mem_range] at hm
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, zero_mul]

lemma norm_coeff_le_two_pow_mul_normSumHalf (P : Polynomial ℂ) (m : ℕ) :
    ‖P.coeff m‖ ≤ (2 : ℝ) ^ m * normSumHalf P := by
  have hterm : ‖P.coeff m‖ * ((1 / 2 : ℝ) ^ m) ≤ normSumHalf P := by
    by_cases hm : m ≤ P.natDegree
    · exact Finset.single_le_sum (fun _ _ => mul_nonneg (norm_nonneg _) (by positivity))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, zero_mul]
      exact normSumHalf_nonneg P
  have hmul := mul_le_mul_of_nonneg_left hterm (show (0 : ℝ) ≤ (2 : ℝ) ^ m by positivity)
  have hcancel : (2 : ℝ) ^ m * (‖P.coeff m‖ * (1 / 2 : ℝ) ^ m) = ‖P.coeff m‖ := by
    rw [mul_left_comm, ← mul_pow]
    norm_num
  linarith

lemma normSumHalf_one : normSumHalf 1 = 1 := by
  simp [normSumHalf]

lemma normSumHalf_mul_le (P Q : Polynomial ℂ) :
    normSumHalf (P * Q) ≤ normSumHalf P * normSumHalf Q := by
  set N := P.natDegree + Q.natDegree
  rw [normSumHalf_eq_sum_of_natDegree_le Polynomial.natDegree_mul_le]
  calc ∑ m ∈ Finset.range (N + 1), ‖(P * Q).coeff m‖ * (1 / 2 : ℝ) ^ m
      ≤ ∑ m ∈ Finset.range (N + 1),
          ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
            (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2) := by
        apply Finset.sum_le_sum
        intro m _
        rw [Polynomial.coeff_mul]
        calc ‖∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, P.coeff ij.1 * Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ m
            ≤ (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m, ‖P.coeff ij.1 * Q.coeff ij.2‖) * (1 / 2 : ℝ) ^ m :=
              mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
          _ = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
                (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro ij hij
              have hsum : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
              rw [norm_mul, ← hsum, pow_add]; ring
    _ = normSumHalf P * normSumHalf Q := by
        unfold normSumHalf
        rw [Finset.sum_mul_sum]
        set S := (Finset.range (P.natDegree + 1)) ×ˢ (Finset.range (Q.natDegree + 1))
        calc ∑ m ∈ Finset.range (N + 1),
              ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal m,
                (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2)
            = ∑ m ∈ Finset.range (N + 1),
              ∑ ij ∈ (Finset.HasAntidiagonal.antidiagonal m).filter (· ∈ S),
                (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2) := by
              apply Finset.sum_congr rfl
              intro m _
              symm
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro ij hij_mem hij
              have hnotS : ij ∉ S := fun hS => hij (Finset.mem_filter.mpr ⟨hij_mem, hS⟩)
              simp only [S, Finset.mem_product, Finset.mem_range, not_and] at hnotS
              by_cases h1 : ij.1 < P.natDegree + 1
              · have h2 : ¬ (ij.2 < Q.natDegree + 1) := hnotS h1
                rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Q) (by omega), norm_zero, zero_mul, mul_zero]
              · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := P) (by omega), norm_zero, zero_mul, zero_mul]
          _ = ∑ ij ∈ S,
                (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2) := by
              rw [← Finset.sum_biUnion]
              · congr 1
                ext ij
                simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter,
                  Finset.HasAntidiagonal.mem_antidiagonal, S, Finset.mem_product]
                constructor
                · rintro ⟨_, _, _, hmem⟩; exact hmem
                · intro hmem; exact ⟨ij.1 + ij.2, by omega, rfl, hmem⟩
              · intro m₁ _ m₂ _ hne
                change Disjoint _ _
                rw [Finset.disjoint_left]
                intro ij h1 h2
                rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at h1 h2
                exact hne (h1.1.symm.trans h2.1)
          _ = ∑ i ∈ Finset.range (P.natDegree + 1),
              ∑ j ∈ Finset.range (Q.natDegree + 1),
                (‖P.coeff i‖ * (1 / 2 : ℝ) ^ i) * (‖Q.coeff j‖ * (1 / 2 : ℝ) ^ j) :=
              Finset.sum_product (Finset.range (P.natDegree + 1)) (Finset.range (Q.natDegree + 1))
                (fun ij => (‖P.coeff ij.1‖ * (1 / 2 : ℝ) ^ ij.1) * (‖Q.coeff ij.2‖ * (1 / 2 : ℝ) ^ ij.2))

lemma normSumHalf_prod_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) :
    normSumHalf (∏ i ∈ s, f i) ≤ ∏ i ∈ s, normSumHalf (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [normSumHalf_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact le_trans (normSumHalf_mul_le _ _)
      (mul_le_mul_of_nonneg_left ih (normSumHalf_nonneg _))

lemma normSumHalf_pow_le (P : Polynomial ℂ) (q : ℕ) :
    normSumHalf (P ^ q) ≤ (normSumHalf P) ^ q := by
  induction q with
  | zero => simp [normSumHalf_one]
  | succ q ih =>
    rw [pow_succ, pow_succ]
    exact le_trans (normSumHalf_mul_le _ _) (mul_le_mul_of_nonneg_right ih (normSumHalf_nonneg _))

noncomputable def truncPoly (S : ℕ) (P : Polynomial ℂ) : Polynomial ℂ :=
  ∑ m ∈ Finset.range S, C (P.coeff m) * X ^ m

lemma coeff_truncPoly (S : ℕ) (P : Polynomial ℂ) (m : ℕ) :
    (truncPoly S P).coeff m = if m < S then P.coeff m else 0 := by
  unfold truncPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hm : m < S
  · rw [if_pos hm, Finset.sum_eq_single m]
    · simp
    · intro b _ hne; exact if_neg (Ne.symm hne)
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr hm))
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro b hb
    have hlt : b < S := Finset.mem_range.mp hb
    exact if_neg (by omega)

lemma natDegree_truncPoly_le (S : ℕ) (P : Polynomial ℂ) :
    (truncPoly S P).natDegree ≤ S := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_truncPoly, if_neg (by omega)]

lemma normSumHalf_truncPoly_le (S : ℕ) (P : Polynomial ℂ) :
    normSumHalf (truncPoly S P) ≤ normSumHalf P := by
  set N := max S P.natDegree
  rw [normSumHalf_eq_sum_of_natDegree_le (le_trans (natDegree_truncPoly_le S P) (le_max_left _ _)),
    normSumHalf_eq_sum_of_natDegree_le (le_max_right S P.natDegree)]
  apply Finset.sum_le_sum
  intro m _
  rw [coeff_truncPoly]
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_mul]
    exact mul_nonneg (norm_nonneg _) (by positivity)

lemma coeff_mul_eq_of_coeff_eq_lt {S : ℕ} {A B B' : Polynomial ℂ}
    (hB : ∀ m < S, B.coeff m = B'.coeff m) {m : ℕ} (hm : m < S) :
    (A * B).coeff m = (A * B').coeff m := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hB ij.2 (by omega)]

lemma coeff_mul_eq_of_coeff_eq_lt_left {S : ℕ} {A A' B : Polynomial ℂ}
    (hA : ∀ m < S, A.coeff m = A'.coeff m) {m : ℕ} (hm : m < S) :
    (A * B).coeff m = (A' * B).coeff m := by
  rw [mul_comm A B, mul_comm A' B]
  exact coeff_mul_eq_of_coeff_eq_lt hA hm

lemma coeff_pow_eq_one_of_coeff_eq_one {S : ℕ} {P : Polynomial ℂ}
    (hP : ∀ m < S, P.coeff m = (1 : Polynomial ℂ).coeff m) (q : ℕ) :
    ∀ m < S, (P ^ q).coeff m = (1 : Polynomial ℂ).coeff m := by
  induction q with
  | zero => intro m _; simp
  | succ q ih =>
    intro m hm
    rw [pow_succ]
    calc (P ^ q * P).coeff m
        = (1 * P).coeff m := coeff_mul_eq_of_coeff_eq_lt_left ih hm
      _ = P.coeff m := by rw [one_mul]
      _ = (1 : Polynomial ℂ).coeff m := hP m hm

lemma coeff_prod_eq_one_of_coeff_eq_one {ι : Type*} (s : Finset ι) (S : ℕ) (f : ι → Polynomial ℂ)
    (hf : ∀ i ∈ s, ∀ m < S, (f i).coeff m = (1 : Polynomial ℂ).coeff m) :
    ∀ m < S, (∏ i ∈ s, f i).coeff m = (1 : Polynomial ℂ).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => intro m _; simp
  | insert a s ha ih =>
    intro m hm
    rw [Finset.prod_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    calc (f a * ∏ i ∈ s, f i).coeff m
        = (1 * ∏ i ∈ s, f i).coeff m := coeff_mul_eq_of_coeff_eq_lt_left h1 hm
      _ = (∏ i ∈ s, f i).coeff m := by rw [one_mul]
      _ = (1 : Polynomial ℂ).coeff m := h2 m hm

noncomputable def invTrunc (S : ℕ) (c : ℂ) : Polynomial ℂ :=
  ∑ a ∈ Finset.range S, C (c⁻¹ * (-c⁻¹) ^ a) * X ^ a

lemma coeff_invTrunc (S : ℕ) (c : ℂ) (m : ℕ) :
    (invTrunc S c).coeff m = if m < S then c⁻¹ * (-c⁻¹) ^ m else 0 := by
  unfold invTrunc
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hm : m < S
  · rw [if_pos hm, Finset.sum_eq_single m]
    · simp
    · intro b _ hne; exact if_neg (Ne.symm hne)
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr hm))
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro b hb
    have hlt : b < S := Finset.mem_range.mp hb
    exact if_neg (by omega)

lemma mul_invTrunc_coeff {S : ℕ} {c : ℂ} (hc : c ≠ 0) {m : ℕ} (hm : m < S) :
    ((C c + X) * invTrunc S c).coeff m = (1 : Polynomial ℂ).coeff m := by
  rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_invTrunc, if_pos hm]
  cases m with
  | zero =>
    simp [mul_inv_cancel₀ hc]
  | succ m =>
    rw [Polynomial.coeff_X_mul, coeff_invTrunc, if_pos (by omega)]
    rw [pow_succ, Polynomial.coeff_one]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    have h1 : c * (c⁻¹ * ((-c⁻¹) ^ m * (-c⁻¹))) = (-c⁻¹) ^ m * (-c⁻¹) := by
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    rw [h1]
    ring

lemma normSumHalf_invTrunc_le {S : ℕ} {c : ℂ} (hc : 1 ≤ ‖c‖) :
    normSumHalf (invTrunc S c) ≤ 2 / ‖c‖ := by
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le zero_lt_one hc
  have hdeg : (invTrunc S c).natDegree ≤ S := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm; rw [coeff_invTrunc, if_neg (by omega)]
  rw [normSumHalf_eq_sum_of_natDegree_le hdeg]
  calc ∑ m ∈ Finset.range (S + 1), ‖(invTrunc S c).coeff m‖ * (1 / 2 : ℝ) ^ m
      ≤ ∑ m ∈ Finset.range (S + 1), ‖c‖⁻¹ * (1 / 2 : ℝ) ^ m := by
        apply Finset.sum_le_sum
        intro m _
        rw [coeff_invTrunc]
        split_ifs
        · rw [norm_mul, norm_inv, norm_pow, norm_neg, norm_inv]
          have hpow : (‖c‖⁻¹) ^ m ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hc)
          have hmul : ‖c‖⁻¹ * (‖c‖⁻¹) ^ m ≤ ‖c‖⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          rw [mul_one] at hmul
          exact mul_le_mul_of_nonneg_right hmul (by positivity)
        · rw [norm_zero, zero_mul]; positivity
    _ = ‖c‖⁻¹ * ∑ m ∈ Finset.range (S + 1), (1 / 2 : ℝ) ^ m := by rw [← Finset.mul_sum]
    _ ≤ ‖c‖⁻¹ * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [geom_sum_eq (by norm_num)]
        have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (S + 1) := by positivity
        have hrew : ((1 / 2 : ℝ) ^ (S + 1) - 1) / ((1 / 2 : ℝ) - 1) =
            2 * (1 - (1 / 2 : ℝ) ^ (S + 1)) := by ring
        rw [hrew]; linarith
    _ = 2 / ‖c‖ := by ring

/- Polynomial derivatives & iteratedDeriv -/

lemma derivative_hasseDeriv_eq (m : ℕ) (P : Polynomial ℂ) :
    Polynomial.derivative (Polynomial.hasseDeriv m P) =
      ((m + 1 : ℕ) : ℂ) • Polynomial.hasseDeriv (m + 1) P := by
  have h := LinearMap.congr_fun (Polynomial.hasseDeriv_comp (R := ℂ) 1 m) P
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, Polynomial.hasseDeriv_one] at h
  rw [h, add_comm 1 m, Nat.choose_one_right, nsmul_eq_mul, Polynomial.smul_eq_C_mul]
  simp

lemma hasDerivAt_eval_poly (P : Polynomial ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => P.eval w) (P.derivative.eval z) z := by
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id] using
    Polynomial.hasDerivAt_aeval P z

lemma iteratedDeriv_eval_poly (s : ℕ) (P : Polynomial ℂ) (z : ℂ) :
    iteratedDeriv s (fun w : ℂ => P.eval w) z =
      (s.factorial : ℂ) * (Polynomial.hasseDeriv s P).eval z := by
  induction s generalizing P z with
  | zero => simp
  | succ s ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun w : ℂ => P.eval w) = fun w : ℂ => P.derivative.eval w := by
      funext w; exact (hasDerivAt_eval_poly P w).deriv
    rw [hd, ih P.derivative z, ← Polynomial.hasseDeriv_one]
    have hcomp := LinearMap.congr_fun (Polynomial.hasseDeriv_comp (R := ℂ) s 1) P
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at hcomp
    rw [hcomp, Polynomial.eval_smul, nsmul_eq_mul, Nat.choose_succ_self_right,
      Nat.factorial_succ]
    push_cast; ring

lemma iteratedDeriv_eval_poly_eq_factorial_mul_taylor_coeff (s : ℕ) (P : Polynomial ℂ) (a : ℂ) :
    iteratedDeriv s (fun w : ℂ => P.eval w) a =
      (s.factorial : ℂ) * (Polynomial.taylor a P).coeff s := by
  rw [iteratedDeriv_eval_poly, Polynomial.taylor_coeff]

/- Entire factorization via `dslope` -/

lemma iteratedDeriv_mul_linear (a : ℂ) {q : ℂ → ℂ} (hq : Differentiable ℂ q) (s : ℕ) :
    iteratedDeriv (s + 1) (fun z => (z - a) * q z) a =
      ((s + 1 : ℕ) : ℂ) * iteratedDeriv s q a := by
  have h1 : ContDiffAt ℂ (s + 1 : ℕ) (fun z : ℂ => z - a) a :=
    (differentiable_id.sub (differentiable_const a)).contDiff.contDiffAt
  have h2 : ContDiffAt ℂ (s + 1 : ℕ) q a := hq.contDiff.contDiffAt
  change iteratedDeriv (s + 1) ((fun z : ℂ => z - a) * q) a = _
  rw [iteratedDeriv_mul h1 h2]
  rw [Finset.sum_eq_single 1]
  · have hd1 : iteratedDeriv 1 (fun z : ℂ => z - a) a = 1 := by
      rw [iteratedDeriv_one]
      exact ((hasDerivAt_id a).sub_const a).deriv
    simp [hd1]
  · intro i hi hne
    have hle : i ≤ s + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rcases i with _ | i'
    · simp
    · rcases i' with _ | i''
      · exact False.elim (hne rfl)
      · have hzero : iteratedDeriv (i'' + 2) (fun z : ℂ => z - a) a = 0 := by
          rw [iteratedDeriv_succ', iteratedDeriv_succ']
          have hd1 : deriv (fun z : ℂ => z - a) = fun _ => (1 : ℂ) := by
            funext w; exact ((hasDerivAt_id w).sub_const a).deriv
          rw [hd1]
          have hd2 : deriv (fun _ : ℂ => (1 : ℂ)) = (0 : ℂ → ℂ) := by
            funext w; exact deriv_const w (1 : ℂ)
          rw [hd2]; simp
        rw [hzero, mul_zero, zero_mul]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

lemma exists_entire_mul_sub_pow_eq (a : ℂ) (S : ℕ) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hvan : ∀ s < S, iteratedDeriv s g a = 0) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, g z = (z - a) ^ S * q z := by
  induction S generalizing g with
  | zero => exact ⟨g, hg, fun z => by simp⟩
  | succ S ih =>
    have hga : g a = 0 := by simpa using hvan 0 (Nat.succ_pos S)
    have hq1_diff : Differentiable ℂ (dslope g a) := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope Filter.univ_mem).mpr hg.differentiableOn
    have hfac : ∀ z, g z = (z - a) * dslope g a z := by
      intro z
      have h := sub_smul_dslope g a z
      rw [smul_eq_mul, hga, sub_zero] at h
      exact h.symm
    have hvan1 : ∀ s < S, iteratedDeriv s (dslope g a) a = 0 := by
      intro s hs
      have h0 : iteratedDeriv (s + 1) g a = 0 := hvan (s + 1) (Nat.succ_lt_succ hs)
      have heq : g = fun z => (z - a) * dslope g a z := funext hfac
      rw [heq, iteratedDeriv_mul_linear a hq1_diff s] at h0
      have hne : ((s + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
      exact (mul_eq_zero.mp h0).resolve_left hne
    obtain ⟨q, hq_diff, hq_eq⟩ := ih hq1_diff hvan1
    refine ⟨q, hq_diff, fun z => ?_⟩
    rw [hfac z, hq_eq z, pow_succ', mul_assoc]

lemma iteratedDeriv_mul_eq_zero_of_left_ne_zero {a : ℂ} {S : ℕ} {u v : ℂ → ℂ}
    (hu : Differentiable ℂ u) (hv : Differentiable ℂ v) (hua : u a ≠ 0)
    (hvan : ∀ s < S, iteratedDeriv s (fun z => u z * v z) a = 0) :
    ∀ s < S, iteratedDeriv s v a = 0 := by
  intro s hs
  induction s using Nat.strong_induction_on with
  | h s ih =>
    have h0 : iteratedDeriv s (u * v) a = 0 := hvan s hs
    rw [iteratedDeriv_mul hu.contDiff.contDiffAt hv.contDiff.contDiffAt] at h0
    rw [Finset.sum_eq_single 0] at h0
    · simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_left hua
    · intro i hi hne
      have hle : i ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hlt : s - i < s := by omega
      rw [ih (s - i) hlt (lt_trans hlt hs), mul_zero]
    · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (Nat.succ_pos s)))

lemma exists_entire_mul_prod_pow_eq (I : Finset ℂ) (S : ℕ) {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hvan : ∀ a ∈ I, ∀ s < S, iteratedDeriv s g a = 0) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, g z = (∏ a ∈ I, (z - a) ^ S) * q z := by
  classical
  induction I using Finset.induction_on generalizing g with
  | empty => exact ⟨g, hg, fun z => by simp⟩
  | insert a I ha ih =>
    obtain ⟨q₁, hq₁_diff, hq₁_eq⟩ := exists_entire_mul_sub_pow_eq a S hg
      (hvan a (Finset.mem_insert_self a I))
    have hvan₁ : ∀ b ∈ I, ∀ s < S, iteratedDeriv s q₁ b = 0 := by
      intro b hb
      have hne : b - a ≠ 0 := sub_ne_zero.mpr (fun hba => ha (hba ▸ hb))
      have hpow_diff : Differentiable ℂ (fun z : ℂ => (z - a) ^ S) :=
        (differentiable_id.sub (differentiable_const a)).pow S
      have hvan_b : ∀ s < S, iteratedDeriv s (fun z => (z - a) ^ S * q₁ z) b = 0 := by
        intro s hs
        have heq : (fun z => (z - a) ^ S * q₁ z) = g := funext fun z => (hq₁_eq z).symm
        rw [heq]
        exact hvan b (Finset.mem_insert_of_mem hb) s hs
      exact iteratedDeriv_mul_eq_zero_of_left_ne_zero hpow_diff hq₁_diff (pow_ne_zero S hne) hvan_b
    obtain ⟨q, hq_diff, hq_eq⟩ := ih hq₁_diff hvan₁
    refine ⟨q, hq_diff, fun z => ?_⟩
    rw [Finset.prod_insert ha, mul_assoc, ← hq_eq z, ← hq₁_eq z]

/- Combinatorial factorial/binomial ratio bound for Hermite interpolation -/

lemma prod_Icc_sub_eq_descFactorial {h l' : ℕ} (hl' : h < l') :
    ∏ u ∈ Finset.Icc 1 h, (l' - u) = (l' - 1).descFactorial h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hIcc : Finset.Icc 1 (h + 1) = insert (h + 1) (Finset.Icc 1 h) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.prod_insert (by simp), ih (by omega), Nat.descFactorial_succ]
    have hsub : l' - 1 - h = l' - (h + 1) := by omega
    rw [hsub]

lemma prod_Icc_erase_abs_sub_eq {h l : ℕ} (hl1 : 1 ≤ l) (hlh : l ≤ h) :
    (∏ u ∈ (Finset.Icc 1 h).erase l, |(l : ℤ) - (u : ℤ)|) =
      (((l - 1).factorial * (h - l).factorial : ℕ) : ℤ) := by
  have hpart : (Finset.Icc 1 h).erase l = Finset.Ico 1 l ∪ Finset.Ioc l h := by
    ext x; simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union,
      Finset.mem_Ico, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Ico 1 l) (Finset.Ioc l h) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_Ico, Finset.mem_Ioc] at h1 h2; omega
  rw [hpart, Finset.prod_union hdisj, Nat.cast_mul]
  congr 1
  · have hleft : ∏ u ∈ Finset.Ico 1 l, |(l : ℤ) - (u : ℤ)| =
        ((∏ u ∈ Finset.Ico 1 l, (l - u) : ℕ) : ℤ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro u hu
      have hul : u < l := (Finset.mem_Ico.mp hu).2
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (l : ℤ) - (u : ℤ)), Int.ofNat_sub hul.le]
    rw [hleft]
    congr 1
    clear hpart hdisj hleft hlh
    induction l with
    | zero => omega
    | succ l' ih =>
      rcases Nat.eq_zero_or_pos l' with rfl | hl'pos
      · simp
      · have hIco : Finset.Ico 1 (l' + 1) = insert 1 (Finset.Ico 2 (l' + 1)) := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        have hbij : ∏ u ∈ Finset.Ico 2 (l' + 1), (l' + 1 - u) =
            ∏ u ∈ Finset.Ico 1 l', (l' - u) := by
          refine Finset.prod_bij (fun u _ => u - 1) ?_ ?_ ?_ ?_
          · intro u hu; simp only [Finset.mem_Ico] at hu ⊢; omega
          · intro u₁ hu₁ u₂ hu₂ heq; simp only [Finset.mem_Ico] at hu₁ hu₂; omega
          · intro b hb; refine ⟨b + 1, ?_, by omega⟩; simp only [Finset.mem_Ico] at hb ⊢; omega
          · intro u hu; simp only [Finset.mem_Ico] at hu; omega
        rw [hIco, Finset.prod_insert (by simp), hbij, ih hl'pos]
        have hsub : l' + 1 - 1 = l' := by omega
        rw [hsub]
        cases l' with
        | zero => omega
        | succ m => rw [Nat.factorial_succ]; simp
  · have hright : ∏ u ∈ Finset.Ioc l h, |(l : ℤ) - (u : ℤ)| =
        ((∏ u ∈ Finset.Ioc l h, (u - l) : ℕ) : ℤ) := by
      rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro u hu
      have hlu : l < u := (Finset.mem_Ioc.mp hu).1
      rw [abs_of_nonpos (by omega : (l : ℤ) - (u : ℤ) ≤ 0), neg_sub, Int.ofNat_sub hlu.le]
    rw [hright]
    congr 1
    have hbij : ∏ u ∈ Finset.Ioc l h, (u - l) = ∏ r ∈ Finset.Icc 1 (h - l), r := by
      refine Finset.prod_bij (fun u _ => u - l) ?_ ?_ ?_ ?_
      · intro u hu; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hu ⊢; omega
      · intro u₁ hu₁ u₂ hu₂ heq; simp only [Finset.mem_Ioc] at hu₁ hu₂; omega
      · intro b hb; refine ⟨b + l, ?_, by omega⟩; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hb ⊢; omega
      · intro u _; rfl
    rw [hbij]
    set m := h - l
    clear hpart hdisj hright hbij hl1 hlh
    induction m with
    | zero => simp
    | succ m ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.prod_insert (by simp), ih, Nat.factorial_succ]

lemma factorial_ratio_le {h l l' : ℕ} (hl1 : 1 ≤ l) (hlh : l ≤ h) (hl'lo : h < l')
    (hl'hi : l' ≤ 2 * h) :
    ((l' - 1).descFactorial h : ℝ) / (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ≤
      (h : ℝ) * (2 : ℝ) ^ (3 * h) := by
  have h1 : (l' - 1).descFactorial h = h.factorial * (l' - 1).choose h := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
  have h2 : h.factorial = h * (h - 1).factorial := by
    cases h with
    | zero => omega
    | succ h' => simp [Nat.factorial_succ]
  have h3 : (h - 1).factorial = (h - 1).choose (l - 1) * ((l - 1).factorial * (h - l).factorial) := by
    have hsub : h - 1 - (l - 1) = h - l := by omega
    have hmul := Nat.choose_mul_factorial_mul_factorial (show l - 1 ≤ h - 1 by omega)
    rw [hsub] at hmul
    rw [← hmul, mul_assoc]
  have hden_pos : (0 : ℝ) < (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) := by positivity
  have hnum_eq : ((l' - 1).descFactorial h : ℝ) =
      ((h * (h - 1).choose (l - 1) * (l' - 1).choose h : ℕ) : ℝ) *
      (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) := by
    have hnat : (l' - 1).descFactorial h =
        h * (h - 1).choose (l - 1) * (l' - 1).choose h * ((l - 1).factorial * (h - l).factorial) := by
      rw [h1, h2, h3]; ring
    rw [← Nat.cast_mul, hnat]
  rw [hnum_eq, mul_div_cancel_right₀ _ hden_pos.ne']
  have hc1 : (h - 1).choose (l - 1) ≤ 2 ^ h :=
    le_trans (Nat.choose_le_two_pow _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hc2 : (l' - 1).choose h ≤ 2 ^ (2 * h) :=
    le_trans (Nat.choose_le_two_pow _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hprod : h * (h - 1).choose (l - 1) * (l' - 1).choose h ≤ h * 2 ^ (3 * h) := by
    calc h * (h - 1).choose (l - 1) * (l' - 1).choose h
        ≤ h * 2 ^ h * 2 ^ (2 * h) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left h hc1) hc2
      _ = h * 2 ^ (3 * h) := by rw [mul_assoc, ← pow_add]; congr 2; omega
  exact_mod_cast hprod

/- Main Hermite–Schwarz Extrapolation Theorem (ZERO contour integrals) -/

theorem hermite_schwarz_bound {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {h S l' : ℕ} (hh : 1 ≤ h) (hS : 1 ≤ S) (hl'lo : h < l') (hl'hi : l' ≤ 2 * h)
    {Mf eps : ℝ} (_hMf : 0 ≤ Mf) (heps : 0 ≤ eps)
    (hcircle : ∀ w : ℂ, ‖w‖ = 32 * (h : ℝ) → ‖f w‖ ≤ Mf)
    (hderiv : ∀ l ∈ Finset.Icc 1 h, ∀ s < S,
      ‖iteratedDeriv s f (l : ℂ) / (s.factorial : ℂ)‖ ≤ eps) :
    ‖f (l' : ℂ)‖ ≤
      ((2 / 31 : ℝ) ^ (h * S)) * Mf +
      4 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
  classical
  set R : ℝ := 32 * (h : ℝ)
  have hRpos : 0 < R := by positivity
  -- Define nodal polynomials E and E_l in ℂ[X]
  let E : Polynomial ℂ := ∏ u ∈ Finset.Icc 1 h, (X - C (u : ℂ)) ^ S
  let El : ℕ → Polynomial ℂ := fun l => ∏ u ∈ (Finset.Icc 1 h).erase l, (X - C (u : ℂ)) ^ S
  have hE_split : ∀ l ∈ Finset.Icc 1 h, E = (X - C (l : ℂ)) ^ S * El l := by
    intro l hl
    dsimp only [E, El]
    exact (Finset.mul_prod_erase (Finset.Icc 1 h) (fun u => (X - C (u : ℂ)) ^ S) hl).symm
  -- Truncated inverse H_l(Y) of E_l(l + Y) mod Y^S
  let Hl : ℕ → Polynomial ℂ := fun l =>
    truncPoly S (∏ u ∈ (Finset.Icc 1 h).erase l, invTrunc S ((l : ℂ) - (u : ℂ)) ^ S)
  -- Taylor polynomial T_l(Y) of f at l
  let Tl : ℕ → Polynomial ℂ := fun l =>
    ∑ s ∈ Finset.range S, C (iteratedDeriv s f (l : ℂ) / (s.factorial : ℂ)) * X ^ s
  -- Gl(Y) = truncPoly S (Tl l * Hl l)
  let Gl : ℕ → Polynomial ℂ := fun l => truncPoly S (Tl l * Hl l)
  -- Hermite interpolating polynomial Q(X) = ∑_{l=1}^h E_l(X) * G_l(X - l)
  let Q : Polynomial ℂ := ∑ l ∈ Finset.Icc 1 h, El l * (Gl l).comp (X - C (l : ℂ))
  -- Step 1: Coefficient bounds on Hl, Tl, Gl
  have hHl_bound : ∀ l ∈ Finset.Icc 1 h,
      normSumHalf (Hl l) ≤
        ((2 : ℝ) ^ ((h - 1) * S)) / ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
    intro l hl
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
    have hlh : l ≤ h := (Finset.mem_Icc.mp hl).2
    refine le_trans (normSumHalf_truncPoly_le S _) ?_
    refine le_trans (normSumHalf_prod_le _ _) ?_
    calc ∏ u ∈ (Finset.Icc 1 h).erase l, normSumHalf (invTrunc S ((l : ℂ) - (u : ℂ)) ^ S)
        ≤ ∏ u ∈ (Finset.Icc 1 h).erase l, (2 / ‖(l : ℂ) - (u : ℂ)‖) ^ S := by
          apply Finset.prod_le_prod (fun _ _ => normSumHalf_nonneg _)
          intro u hu
          have hne : u ≠ l := Finset.ne_of_mem_erase hu
          have hge1 : (1 : ℝ) ≤ ‖(l : ℂ) - (u : ℂ)‖ := by
            have hcast : ((l : ℂ) - (u : ℂ)) = (((l : ℤ) - (u : ℤ) : ℤ) : ℂ) := by push_cast; ring
            rw [hcast, Complex.norm_intCast]
            have h1 : (1 : ℤ) ≤ |(l : ℤ) - (u : ℤ)| := by
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · rw [abs_of_pos (by omega : (0 : ℤ) < (l : ℤ) - (u : ℤ))]; omega
              · rw [abs_of_neg (by omega : (l : ℤ) - (u : ℤ) < 0)]; omega
            exact_mod_cast h1
          exact le_trans (normSumHalf_pow_le _ S)
            (pow_le_pow_left₀ (normSumHalf_nonneg _) (normSumHalf_invTrunc_le hge1) S)
      _ = ((2 : ℝ) ^ ((h - 1) * S)) / ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
          simp only [div_pow, Finset.prod_div_distrib]
          rw [Finset.prod_const, Finset.card_erase_of_mem hl, Nat.card_Icc,
            show h + 1 - 1 = h by omega, ← pow_mul, mul_comm S (h - 1)]
          congr 1
          rw [Finset.prod_pow]
          congr 1
          have hprod := prod_Icc_erase_abs_sub_eq hl1 hlh
          have hcast : ∏ u ∈ (Finset.Icc 1 h).erase l, ‖(l : ℂ) - (u : ℂ)‖ =
              ((∏ u ∈ (Finset.Icc 1 h).erase l, |(l : ℤ) - (u : ℤ)| : ℤ) : ℝ) := by
            rw [Int.cast_prod]
            apply Finset.prod_congr rfl
            intro u _
            have hc : ((l : ℂ) - (u : ℂ)) = (((l : ℤ) - (u : ℤ) : ℤ) : ℂ) := by push_cast; ring
            rw [hc, Complex.norm_intCast, Int.cast_abs]
          rw [hcast, hprod, Int.cast_natCast]
  have hTl_bound : ∀ l ∈ Finset.Icc 1 h, normSumHalf (Tl l) ≤ 2 * eps := by
    intro l hl
    have hcoeff : ∀ m, (Tl l).coeff m =
        if m < S then iteratedDeriv m f (l : ℂ) / (m.factorial : ℂ) else 0 := by
      intro m
      dsimp only [Tl]
      rw [Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      by_cases hm : m < S
      · rw [if_pos hm, Finset.sum_eq_single m]
        · simp
        · intro b _ hne; exact if_neg (Ne.symm hne)
        · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr hm))
      · rw [if_neg hm]
        apply Finset.sum_eq_zero
        intro b hb
        have hlt : b < S := Finset.mem_range.mp hb
        exact if_neg (by omega)
    have hdeg : (Tl l).natDegree ≤ S := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm; rw [hcoeff m, if_neg (by omega)]
    rw [normSumHalf_eq_sum_of_natDegree_le hdeg]
    calc ∑ m ∈ Finset.range (S + 1), ‖(Tl l).coeff m‖ * (1 / 2 : ℝ) ^ m
        ≤ ∑ m ∈ Finset.range (S + 1), eps * (1 / 2 : ℝ) ^ m := by
          apply Finset.sum_le_sum
          intro m _
          rw [hcoeff m]
          split_ifs with hm
          · exact mul_le_mul_of_nonneg_right (hderiv l hl m hm) (by positivity)
          · rw [norm_zero, zero_mul]; positivity
      _ = eps * ∑ m ∈ Finset.range (S + 1), (1 / 2 : ℝ) ^ m := by rw [← Finset.mul_sum]
      _ ≤ eps * 2 := by
          apply mul_le_mul_of_nonneg_left _ heps
          rw [geom_sum_eq (by norm_num)]
          have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (S + 1) := by positivity
          have hrew : ((1 / 2 : ℝ) ^ (S + 1) - 1) / ((1 / 2 : ℝ) - 1) =
              2 * (1 - (1 / 2 : ℝ) ^ (S + 1)) := by ring
          rw [hrew]; linarith
      _ = 2 * eps := by ring
  have hGl_coeff : ∀ l ∈ Finset.Icc 1 h, ∀ k < S,
      ‖(Gl l).coeff k‖ ≤
        ((2 : ℝ) ^ (h * S + 1)) * eps / ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
    intro l hl k hk
    have hnh : normSumHalf (Gl l) ≤
        2 * eps * (((2 : ℝ) ^ ((h - 1) * S)) /
          ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
      refine le_trans (normSumHalf_truncPoly_le S _) ?_
      refine le_trans (normSumHalf_mul_le _ _) ?_
      exact mul_le_mul (hTl_bound l hl) (hHl_bound l hl) (normSumHalf_nonneg _) (by positivity)
    refine le_trans (norm_coeff_le_two_pow_mul_normSumHalf (Gl l) k) ?_
    have h2k : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ S :=
      pow_le_pow_right₀ (by norm_num) (le_of_lt hk)
    calc (2 : ℝ) ^ k * normSumHalf (Gl l)
        ≤ (2 : ℝ) ^ S * (2 * eps * (((2 : ℝ) ^ ((h - 1) * S)) /
            ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S))) :=
          mul_le_mul h2k hnh (normSumHalf_nonneg _) (by positivity)
      _ = ((2 : ℝ) ^ (h * S + 1)) * eps / ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
          have hexp : S + 1 + (h - 1) * S = h * S + 1 := by
            have : (h - 1) * S + S = h * S := by
              cases h with
              | zero => omega
              | succ h' => simp [Nat.add_mul]
            omega
          have hpow : (2 : ℝ) ^ S * 2 * (2 : ℝ) ^ ((h - 1) * S) = (2 : ℝ) ^ (h * S + 1) := by
            rw [← hexp, pow_add, pow_add, pow_one]
          calc (2 : ℝ) ^ S * (2 * eps * ((2 : ℝ) ^ ((h - 1) * S) /
                ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)))
              = ((2 : ℝ) ^ S * 2 * (2 : ℝ) ^ ((h - 1) * S)) * eps /
                  ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by ring
            _ = (2 : ℝ) ^ (h * S + 1) * eps /
                  ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by rw [hpow]
  -- Step 2: Exact vanishing of f - Q to order S at every l ∈ Icc 1 h
  have hQ_van : ∀ l ∈ Finset.Icc 1 h, ∀ s < S,
      iteratedDeriv s (fun z => f z - Q.eval z) (l : ℂ) = 0 := by
    intro l hl s hs
    have hQdiff : Differentiable ℂ (fun z : ℂ => Q.eval z) :=
      fun z => (hasDerivAt_eval_poly Q z).differentiableAt
    have hsub_deriv : iteratedDeriv s (fun z => f z - Q.eval z) (l : ℂ) =
        iteratedDeriv s f (l : ℂ) - iteratedDeriv s (fun z => Q.eval z) (l : ℂ) := by
      have h1 : ContDiffAt ℂ (s : ℕ) f (l : ℂ) := hf.contDiff.contDiffAt
      have h2 : ContDiffAt ℂ (s : ℕ) (fun z : ℂ => Q.eval z) (l : ℂ) := hQdiff.contDiff.contDiffAt
      exact iteratedDeriv_fun_sub h1 h2
    rw [hsub_deriv, sub_eq_zero, iteratedDeriv_eval_poly_eq_factorial_mul_taylor_coeff]
    -- Compute (taylor (l : ℂ) Q).coeff s
    have htaylor_Q : (Polynomial.taylor (l : ℂ) Q).coeff s =
        iteratedDeriv s f (l : ℂ) / (s.factorial : ℂ) := by
      rw [Polynomial.taylor_apply]
      dsimp only [Q]
      rw [Polynomial.sum_comp, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single l]
      · rw [Polynomial.mul_comp, Polynomial.comp_assoc]
        have hcompX : (X - C (l : ℂ)).comp (X + C (l : ℂ)) = X := by
          simp [Polynomial.sub_comp, Polynomial.X_comp]
        rw [hcompX, Polynomial.comp_X]
        -- (El l).comp (X + C l) * Gl l has same s-th coeff as Tl l!
        have hEl_Hl : ∀ m < S,
            (((El l).comp (X + C (l : ℂ))) * Hl l).coeff m = (1 : Polynomial ℂ).coeff m := by
          intro m hm
          have h1 : (((El l).comp (X + C (l : ℂ))) * Hl l).coeff m =
              (((El l).comp (X + C (l : ℂ))) *
                (∏ u ∈ (Finset.Icc 1 h).erase l, invTrunc S ((l : ℂ) - (u : ℂ)) ^ S)).coeff m := by
            apply coeff_mul_eq_of_coeff_eq_lt _ hm
            intro k hk; exact (coeff_truncPoly S _ k).trans (if_pos hk)
          rw [h1]
          dsimp only [El]
          rw [Polynomial.prod_comp, ← Finset.prod_mul_distrib]
          apply coeff_prod_eq_one_of_coeff_eq_one _ S _ _ m hm
          intro u hu k hk
          rw [Polynomial.pow_comp, ← mul_pow]
          apply coeff_pow_eq_one_of_coeff_eq_one _ S k hk
          intro j hj
          have hlin : (X - C (u : ℂ)).comp (X + C (l : ℂ)) = C ((l : ℂ) - (u : ℂ)) + X := by
            simp [Polynomial.sub_comp, Polynomial.X_comp]; ring
          rw [hlin]
          have hne : (l : ℂ) - (u : ℂ) ≠ 0 := by
            have hu_ne : u ≠ l := Finset.ne_of_mem_erase hu
            exact sub_ne_zero.mpr (by exact_mod_cast hu_ne.symm)
          exact mul_invTrunc_coeff hne hj
        have hstep1 : (((El l).comp (X + C (l : ℂ))) * Gl l).coeff s =
            (((El l).comp (X + C (l : ℂ))) * (Tl l * Hl l)).coeff s := by
          apply coeff_mul_eq_of_coeff_eq_lt _ hs
          intro k hk; exact (coeff_truncPoly S _ k).trans (if_pos hk)
        rw [hstep1]
        have hrearr : ((El l).comp (X + C (l : ℂ))) * (Tl l * Hl l) =
            Tl l * (((El l).comp (X + C (l : ℂ))) * Hl l) := by ring
        rw [hrearr]
        calc (Tl l * (((El l).comp (X + C (l : ℂ))) * Hl l)).coeff s
            = (Tl l * 1).coeff s := coeff_mul_eq_of_coeff_eq_lt hEl_Hl hs
          _ = (Tl l).coeff s := by rw [mul_one]
          _ = iteratedDeriv s f (l : ℂ) / (s.factorial : ℂ) := by
              dsimp only [Tl]
              rw [Polynomial.finsetSum_coeff]
              simp only [Polynomial.coeff_C_mul_X_pow]
              rw [Finset.sum_eq_single s]
              · simp
              · intro b _ hne; exact if_neg (Ne.symm hne)
              · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr hs))
      · intro u hu hul
        -- El u contains factor (X - C l)^S, so (El u).comp (X + C l) is divisible by X^S
        have hl_mem : l ∈ (Finset.Icc 1 h).erase u := Finset.mem_erase.mpr ⟨hul.symm, hl⟩
        have hEl_u : El u = (X - C (l : ℂ)) ^ S *
            ∏ v ∈ ((Finset.Icc 1 h).erase u).erase l, (X - C (v : ℂ)) ^ S :=
          (Finset.mul_prod_erase ((Finset.Icc 1 h).erase u)
            (fun v : ℕ => (X - C (v : ℂ)) ^ S) hl_mem).symm
        rw [hEl_u, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.pow_comp]
        have hsub : (X - C (l : ℂ)).comp (X + C (l : ℂ)) = X := by
          simp [Polynomial.sub_comp, Polynomial.X_comp]
        rw [hsub, mul_assoc, Polynomial.coeff_X_pow_mul']
        exact if_neg (by omega)
      · intro hnot; exact False.elim (hnot hl)
    rw [htaylor_Q]
    have hfac_ne : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
    field_simp [hfac_ne]
  -- Step 3: Entire factorization (f - Q) = E * q
  have hdiff_sub : Differentiable ℂ (fun z => f z - Q.eval z) :=
    hf.sub (fun z => (hasDerivAt_eval_poly Q z).differentiableAt)
  let I : Finset ℂ := (Finset.Icc 1 h).image (fun u : ℕ => (u : ℂ))
  have hE_eq_prod : ∀ z : ℂ, E.eval z = ∏ a ∈ I, (z - a) ^ S := by
    intro z
    dsimp only [E, I]
    rw [Polynomial.eval_prod, Finset.prod_image (fun x _ y _ hxy => Nat.cast_injective hxy)]
    simp [Polynomial.eval_pow, Polynomial.eval_sub]
  have hvan_I : ∀ a ∈ I, ∀ s < S, iteratedDeriv s (fun z => f z - Q.eval z) a = 0 := by
    intro a ha s hs
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ha
    exact hQ_van l hl s hs
  obtain ⟨q, hq_diff, hq_eq⟩ := exists_entire_mul_prod_pow_eq I S hdiff_sub hvan_I
  have hq_E : ∀ z, f z - Q.eval z = E.eval z * q z := fun z => by
    rw [hE_eq_prod z]; exact hq_eq z
  -- Step 4: Bounds on E(l'), E(w), Q(l'), Q(w)/E(w)
  have hEl'_norm : ‖E.eval (l' : ℂ)‖ = (((l' - 1).descFactorial h : ℕ) : ℝ) ^ S := by
    dsimp only [E]
    rw [Polynomial.eval_prod, norm_prod]
    have h1 : ∏ u ∈ Finset.Icc 1 h, ‖((X - C (u : ℂ)) ^ S).eval (l' : ℂ)‖ =
        (∏ u ∈ Finset.Icc 1 h, ((l' - u : ℕ) : ℝ)) ^ S := by
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro u hu
      have hul' : u ≤ l' := le_trans (Finset.mem_Icc.mp hu).2 (le_of_lt hl'lo)
      simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        norm_pow]
      congr 1
      rw [← Nat.cast_sub hul', Complex.norm_natCast]
    rw [h1, ← Nat.cast_prod, prod_Icc_sub_eq_descFactorial hl'lo]
  have hEl'_upper : ‖E.eval (l' : ℂ)‖ ≤ (2 * (h : ℝ)) ^ (h * S) := by
    dsimp only [E]
    rw [Polynomial.eval_prod, norm_prod]
    calc ∏ u ∈ Finset.Icc 1 h, ‖((X - C (u : ℂ)) ^ S).eval (l' : ℂ)‖
        ≤ ∏ _u ∈ Finset.Icc 1 h, (2 * (h : ℝ)) ^ S := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro u hu
          have hu1 : 1 ≤ u := (Finset.mem_Icc.mp hu).1
          have hul' : u ≤ l' := le_trans (Finset.mem_Icc.mp hu).2 (le_of_lt hl'lo)
          simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
            norm_pow]
          apply pow_le_pow_left₀ (norm_nonneg _)
          rw [← Nat.cast_sub hul', Complex.norm_natCast]
          have hle : l' - u ≤ 2 * h := by omega
          exact_mod_cast hle
      _ = (2 * (h : ℝ)) ^ (h * S) := by
          rw [Finset.prod_const, Nat.card_Icc, show h + 1 - 1 = h by omega, ← pow_mul, mul_comm S h]
  have hEw_lower : ∀ w : ℂ, ‖w‖ = R → (31 * (h : ℝ)) ^ (h * S) ≤ ‖E.eval w‖ := by
    intro w hw
    dsimp only [E]
    rw [Polynomial.eval_prod, norm_prod]
    have hconst : (31 * (h : ℝ)) ^ (h * S) = ∏ _u ∈ Finset.Icc 1 h, (31 * (h : ℝ)) ^ S := by
      rw [Finset.prod_const, Nat.card_Icc, show h + 1 - 1 = h by omega, ← pow_mul, mul_comm h S]
    rw [hconst]
    apply Finset.prod_le_prod (fun _ _ => by positivity)
    intro u hu
    have huh : u ≤ h := (Finset.mem_Icc.mp hu).2
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      norm_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hrev := norm_sub_norm_le w (u : ℂ)
    rw [hw, Complex.norm_natCast] at hrev
    have huR : (u : ℝ) ≤ (h : ℝ) := by exact_mod_cast huh
    dsimp only [R] at hrev
    linarith
  have hQ_eval_l' : ‖Q.eval (l' : ℂ)‖ ≤
      2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
    dsimp only [Q]
    rw [Polynomial.eval_finsetSum]
    refine le_trans (norm_sum_le _ _) ?_
    calc ∑ l ∈ Finset.Icc 1 h, ‖(El l * (Gl l).comp (X - C (l : ℂ))).eval (l' : ℂ)‖
        ≤ ∑ _l ∈ Finset.Icc 1 h,
            2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
          apply Finset.sum_le_sum
          intro l hl
          have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
          have hlh : l ≤ h := (Finset.mem_Icc.mp hl).2
          rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C, norm_mul]
          -- ‖(El l).eval l'‖ ≤ ‖E.eval l'‖ because |l' - l| ≥ 1
          have hEl_le : ‖(El l).eval (l' : ℂ)‖ ≤ ‖E.eval (l' : ℂ)‖ := by
            rw [hE_split l hl, Polynomial.eval_mul, norm_mul]
            have hge1 : (1 : ℝ) ≤ ‖((X - C (l : ℂ)) ^ S).eval (l' : ℂ)‖ := by
              simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
                Polynomial.eval_C, norm_pow]
              apply one_le_pow₀
              rw [← Nat.cast_sub (le_of_lt (lt_of_le_of_lt hlh hl'lo)), Complex.norm_natCast]
              have : 1 ≤ l' - l := by omega
              exact_mod_cast this
            have h1mul := mul_le_mul_of_nonneg_right hge1 (norm_nonneg ((El l).eval (l' : ℂ)))
            rwa [one_mul] at h1mul
          -- Bound ‖(Gl l).eval (l' - l)‖
          have hGl_val : ‖(Gl l).eval ((l' : ℂ) - (l : ℂ))‖ ≤
              (S : ℝ) * ((2 * (h : ℝ)) ^ S) *
              (((2 : ℝ) ^ (h * S + 1)) * eps /
                ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
            dsimp only [Gl, truncPoly]
            rw [Polynomial.eval_finsetSum]
            refine le_trans (norm_sum_le _ _) ?_
            calc ∑ k ∈ Finset.range S, ‖(C ((Tl l * Hl l).coeff k) * X ^ k).eval ((l' : ℂ) - (l : ℂ))‖
                ≤ ∑ _k ∈ Finset.range S, ((2 * (h : ℝ)) ^ S) *
                    (((2 : ℝ) ^ (h * S + 1)) * eps /
                      ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
                  apply Finset.sum_le_sum
                  intro k hk
                  have hkS : k < S := Finset.mem_range.mp hk
                  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
                    Polynomial.eval_X, norm_mul, norm_pow]
                  have hc : ‖(Tl l * Hl l).coeff k‖ ≤
                      ((2 : ℝ) ^ (h * S + 1)) * eps /
                        ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
                    have heq : (Tl l * Hl l).coeff k = (Gl l).coeff k := by
                      rw [coeff_truncPoly, if_pos hkS]
                    rw [heq]; exact hGl_coeff l hl k hkS
                  have hpow : ‖(l' : ℂ) - (l : ℂ)‖ ^ k ≤ (2 * (h : ℝ)) ^ S := by
                    have hnorm : ‖(l' : ℂ) - (l : ℂ)‖ ≤ 2 * (h : ℝ) := by
                      rw [← Nat.cast_sub (le_of_lt (lt_of_le_of_lt hlh hl'lo)), Complex.norm_natCast]
                      have : l' - l ≤ 2 * h := by omega
                      exact_mod_cast this
                    have h2h1 : (1 : ℝ) ≤ 2 * (h : ℝ) := by
                      have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
                      linarith
                    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hnorm k)
                      (pow_le_pow_right₀ h2h1 (le_of_lt hkS))
                  rw [mul_comm]
                  exact mul_le_mul hpow hc (norm_nonneg _) (by positivity)
              _ = (S : ℝ) * ((2 * (h : ℝ)) ^ S) *
                    (((2 : ℝ) ^ (h * S + 1)) * eps /
                      ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
                  simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
          calc ‖(El l).eval (l' : ℂ)‖ * ‖(Gl l).eval ((l' : ℂ) - (l : ℂ))‖
              ≤ ‖E.eval (l' : ℂ)‖ * ((S : ℝ) * ((2 * (h : ℝ)) ^ S) *
                  (((2 : ℝ) ^ (h * S + 1)) * eps /
                    ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S))) :=
                mul_le_mul hEl_le hGl_val (norm_nonneg _) (norm_nonneg _)
            _ = (S : ℝ) * ((2 * (h : ℝ)) ^ S) * ((2 : ℝ) ^ (h * S + 1)) *
                  (((l' - 1).descFactorial h : ℝ) /
                    (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ)) ^ S * eps := by
                rw [hEl'_norm, div_pow]; ring
            _ ≤ (S : ℝ) * ((2 * (h : ℝ)) ^ S) * ((2 : ℝ) ^ (h * S + 1)) *
                  ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps := by
                have hrat := factorial_ratio_le hl1 hlh hl'lo hl'hi
                have hpow := pow_le_pow_left₀ (by positivity) hrat S
                gcongr
            _ = 2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
                have hsplit : ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S =
                    (h : ℝ) ^ S * (2 : ℝ) ^ (3 * h * S) := by rw [mul_pow, ← pow_mul]
                have h16 : (2 : ℝ) ^ (h * S) * (2 : ℝ) ^ (3 * h * S) = (16 : ℝ) ^ (h * S) := by
                  rw [← pow_add, show h * S + 3 * h * S = 4 * (h * S) by ring, pow_mul]
                  norm_num
                have h2h : (2 * (h : ℝ)) ^ S * (h : ℝ) ^ S = (2 * (h : ℝ) ^ 2) ^ S := by
                  rw [← mul_pow]; congr 1; ring
                rw [hsplit, pow_succ]
                calc (S : ℝ) * (2 * (h : ℝ)) ^ S * ((2 : ℝ) ^ (h * S) * 2) *
                      ((h : ℝ) ^ S * (2 : ℝ) ^ (3 * h * S)) * eps
                    = 2 * (S : ℝ) * ((2 * (h : ℝ)) ^ S * (h : ℝ) ^ S) *
                        ((2 : ℝ) ^ (h * S) * (2 : ℝ) ^ (3 * h * S)) * eps := by ring
                  _ = 2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
                        rw [h2h, h16]
      _ = 2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
          rw [Finset.sum_const, Nat.card_Icc, show h + 1 - 1 = h by omega, nsmul_eq_mul]; ring
  -- Step 5: Bound ‖E(l')‖ * ‖q(w)‖ on the circle ‖w‖ = R
  have hq_circle : ∀ w : ℂ, ‖w‖ = R →
      ‖E.eval (l' : ℂ)‖ * ‖q w‖ ≤
        ((2 / 31 : ℝ) ^ (h * S)) * Mf +
        2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
    intro w hw
    have hEw_pos : 0 < ‖E.eval w‖ := lt_of_lt_of_le (by positivity) (hEw_lower w hw)
    have hEw_ne : E.eval w ≠ 0 := norm_pos_iff.mp hEw_pos
    have hqw : q w = f w / E.eval w - Q.eval w / E.eval w := by
      have h := hq_E w
      rw [← sub_div]
      exact eq_div_of_mul_eq hEw_ne (by rw [mul_comm]; exact h.symm)
    rw [hqw]
    have htri : ‖f w / E.eval w - Q.eval w / E.eval w‖ ≤
        ‖f w‖ / ‖E.eval w‖ + ‖Q.eval w / E.eval w‖ := by
      calc ‖f w / E.eval w - Q.eval w / E.eval w‖
          ≤ ‖f w / E.eval w‖ + ‖Q.eval w / E.eval w‖ := norm_sub_le _ _
        _ = ‖f w‖ / ‖E.eval w‖ + ‖Q.eval w / E.eval w‖ := by rw [norm_div]
    have hterm1 : ‖E.eval (l' : ℂ)‖ * (‖f w‖ / ‖E.eval w‖) ≤ ((2 / 31 : ℝ) ^ (h * S)) * Mf := by
      have hrat : ‖E.eval (l' : ℂ)‖ / ‖E.eval w‖ ≤ (2 / 31 : ℝ) ^ (h * S) := by
        rw [div_le_iff₀ hEw_pos]
        calc ‖E.eval (l' : ℂ)‖
            ≤ (2 * (h : ℝ)) ^ (h * S) := hEl'_upper
          _ = (2 / 31 : ℝ) ^ (h * S) * (31 * (h : ℝ)) ^ (h * S) := by
              rw [← mul_pow]; congr 1; ring
          _ ≤ (2 / 31 : ℝ) ^ (h * S) * ‖E.eval w‖ :=
              mul_le_mul_of_nonneg_left (hEw_lower w hw) (by positivity)
      calc ‖E.eval (l' : ℂ)‖ * (‖f w‖ / ‖E.eval w‖)
          = (‖E.eval (l' : ℂ)‖ / ‖E.eval w‖) * ‖f w‖ := by ring
        _ ≤ ((2 / 31 : ℝ) ^ (h * S)) * Mf :=
            mul_le_mul hrat (hcircle w hw) (norm_nonneg _) (by positivity)
    have hterm2 : ‖E.eval (l' : ℂ)‖ * ‖Q.eval w / E.eval w‖ ≤
        2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
      have hQdiv : Q.eval w / E.eval w =
          ∑ l ∈ Finset.Icc 1 h, (Gl l).eval (w - (l : ℂ)) / (w - (l : ℂ)) ^ S := by
        dsimp only [Q]
        rw [Polynomial.eval_finsetSum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l hl
        rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, hE_split l hl, Polynomial.eval_mul]
        have hEl_ne : (El l).eval w ≠ 0 := by
          intro h0; rw [hE_split l hl, Polynomial.eval_mul, h0, mul_zero] at hEw_ne; exact hEw_ne rfl
        simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        rw [mul_comm ((El l).eval w), mul_div_mul_right _ _ hEl_ne]
      rw [hQdiv]
      refine le_trans (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)) ?_
      rw [Finset.mul_sum]
      calc ∑ l ∈ Finset.Icc 1 h, ‖E.eval (l' : ℂ)‖ * ‖(Gl l).eval (w - (l : ℂ)) / (w - (l : ℂ)) ^ S‖
          ≤ ∑ _l ∈ Finset.Icc 1 h,
              2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
            apply Finset.sum_le_sum
            intro l hl
            have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hl).1
            have hlh : l ≤ h := (Finset.mem_Icc.mp hl).2
            have hwl : (1 : ℝ) ≤ ‖w - (l : ℂ)‖ := by
              have hrev := norm_sub_norm_le w (l : ℂ)
              rw [hw, Complex.norm_natCast] at hrev
              have hlR : (l : ℝ) ≤ (h : ℝ) := by exact_mod_cast hlh
              have hh1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
              dsimp only [R] at hrev; linarith
            have hGl_div : ‖(Gl l).eval (w - (l : ℂ)) / (w - (l : ℂ)) ^ S‖ ≤
                (S : ℝ) * (((2 : ℝ) ^ (h * S + 1)) * eps /
                  ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) := by
              rw [norm_div, norm_pow, div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hwl) S)]
              dsimp only [Gl, truncPoly]
              rw [Polynomial.eval_finsetSum]
              refine le_trans (norm_sum_le _ _) ?_
              calc ∑ k ∈ Finset.range S, ‖(C ((Tl l * Hl l).coeff k) * X ^ k).eval (w - (l : ℂ))‖
                  ≤ ∑ _k ∈ Finset.range S,
                      (((2 : ℝ) ^ (h * S + 1)) * eps /
                        ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) *
                      ‖w - (l : ℂ)‖ ^ S := by
                    apply Finset.sum_le_sum
                    intro k hk
                    have hkS : k < S := Finset.mem_range.mp hk
                    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
                      Polynomial.eval_X, norm_mul, norm_pow]
                    have hc : ‖(Tl l * Hl l).coeff k‖ ≤
                        ((2 : ℝ) ^ (h * S + 1)) * eps /
                          ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S) := by
                      have heq : (Tl l * Hl l).coeff k = (Gl l).coeff k := by
                        rw [coeff_truncPoly, if_pos hkS]
                      rw [heq]; exact hGl_coeff l hl k hkS
                    exact mul_le_mul hc (pow_le_pow_right₀ hwl (le_of_lt hkS))
                      (pow_nonneg (norm_nonneg _) k) (by positivity)
                _ = (S : ℝ) * (((2 : ℝ) ^ (h * S + 1)) * eps /
                      ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S)) *
                    ‖w - (l : ℂ)‖ ^ S := by
                    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
            have h2hS : (1 : ℝ) ≤ (2 * (h : ℝ)) ^ S := by
              apply one_le_pow₀
              have : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
              linarith
            calc ‖E.eval (l' : ℂ)‖ * ‖(Gl l).eval (w - (l : ℂ)) / (w - (l : ℂ)) ^ S‖
                ≤ ‖E.eval (l' : ℂ)‖ * ((S : ℝ) * (((2 : ℝ) ^ (h * S + 1)) * eps /
                    ((((l - 1).factorial * (h - l).factorial : ℕ) : ℝ) ^ S))) :=
                  mul_le_mul_of_nonneg_left hGl_div (norm_nonneg _)
              _ = (S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                    (((l' - 1).descFactorial h : ℝ) /
                      (((l - 1).factorial * (h - l).factorial : ℕ) : ℝ)) ^ S * eps := by
                  rw [hEl'_norm, div_pow]; ring
              _ ≤ (S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                    ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps := by
                  have hrat := factorial_ratio_le hl1 hlh hl'lo hl'hi
                  have hpow := pow_le_pow_left₀ (by positivity) hrat S
                  gcongr
              _ ≤ (S : ℝ) * ((2 * (h : ℝ)) ^ S) * ((2 : ℝ) ^ (h * S + 1)) *
                    ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps := by
                  have hnn : 0 ≤ (S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                      ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps := by positivity
                  calc (S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) * ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps
                      = 1 * ((S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                          ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps) := (one_mul _).symm
                    _ ≤ (2 * (h : ℝ)) ^ S * ((S : ℝ) * ((2 : ℝ) ^ (h * S + 1)) *
                          ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S * eps) :=
                        mul_le_mul_of_nonneg_right h2hS hnn
                    _ = _ := by ring
              _ = 2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
                  have hsplit : ((h : ℝ) * (2 : ℝ) ^ (3 * h)) ^ S =
                      (h : ℝ) ^ S * (2 : ℝ) ^ (3 * h * S) := by rw [mul_pow, ← pow_mul]
                  have h16 : (2 : ℝ) ^ (h * S) * (2 : ℝ) ^ (3 * h * S) = (16 : ℝ) ^ (h * S) := by
                    rw [← pow_add, show h * S + 3 * h * S = 4 * (h * S) by ring, pow_mul]
                    norm_num
                  have h2h : (2 * (h : ℝ)) ^ S * (h : ℝ) ^ S = (2 * (h : ℝ) ^ 2) ^ S := by
                    rw [← mul_pow]; congr 1; ring
                  rw [hsplit, pow_succ]
                  calc (S : ℝ) * (2 * (h : ℝ)) ^ S * ((2 : ℝ) ^ (h * S) * 2) *
                        ((h : ℝ) ^ S * (2 : ℝ) ^ (3 * h * S)) * eps
                      = 2 * (S : ℝ) * ((2 * (h : ℝ)) ^ S * (h : ℝ) ^ S) *
                          ((2 : ℝ) ^ (h * S) * (2 : ℝ) ^ (3 * h * S)) * eps := by ring
                    _ = 2 * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
                          rw [h2h, h16]
        _ = 2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
            rw [Finset.sum_const, Nat.card_Icc, show h + 1 - 1 = h by omega, nsmul_eq_mul]; ring
    calc ‖E.eval (l' : ℂ)‖ * ‖f w / E.eval w - Q.eval w / E.eval w‖
        ≤ ‖E.eval (l' : ℂ)‖ * (‖f w‖ / ‖E.eval w‖ + ‖Q.eval w / E.eval w‖) :=
          mul_le_mul_of_nonneg_left htri (norm_nonneg _)
      _ = ‖E.eval (l' : ℂ)‖ * (‖f w‖ / ‖E.eval w‖) + ‖E.eval (l' : ℂ)‖ * ‖Q.eval w / E.eval w‖ :=
          mul_add _ _ _
      _ ≤ _ := add_le_add hterm1 hterm2
  -- Step 6: Apply Maximum Modulus Principle to `fun w => E.eval l' * q w` on `Metric.ball 0 R`
  set Bnd : ℝ := ((2 / 31 : ℝ) ^ (h * S)) * Mf +
      2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps
  have hmax : ‖E.eval (l' : ℂ) * q (l' : ℂ)‖ ≤ Bnd := by
    have hdiff_mul : DiffContOnCl ℂ (fun w => E.eval (l' : ℂ) * q w) (Metric.ball (0 : ℂ) R) :=
      ((differentiable_const _).mul hq_diff).diffContOnCl
    have hfront : ∀ w ∈ frontier (Metric.ball (0 : ℂ) R), ‖E.eval (l' : ℂ) * q w‖ ≤ Bnd := by
      intro w hw
      rw [frontier_ball (0 : ℂ) hRpos.ne', Metric.mem_sphere, dist_zero_right] at hw
      rw [norm_mul]
      exact hq_circle w hw
    have hmem : (l' : ℂ) ∈ closure (Metric.ball (0 : ℂ) R) := by
      rw [closure_ball (0 : ℂ) hRpos.ne', Metric.mem_closedBall, dist_zero_right,
        Complex.norm_natCast]
      have : (l' : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast hl'hi
      dsimp only [R]; linarith
    exact Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdiff_mul hfront hmem
  have hfl' : f (l' : ℂ) = Q.eval (l' : ℂ) + E.eval (l' : ℂ) * q (l' : ℂ) := by
    have h := hq_E (l' : ℂ); linear_combination h
  rw [hfl']
  calc ‖Q.eval (l' : ℂ) + E.eval (l' : ℂ) * q (l' : ℂ)‖
      ≤ ‖Q.eval (l' : ℂ)‖ + ‖E.eval (l' : ℂ) * q (l' : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps + Bnd :=
        add_le_add hQ_eval_l' hmax
    _ = ((2 / 31 : ℝ) ^ (h * S)) * Mf +
        4 * (h : ℝ) * (S : ℝ) * ((2 * (h : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (h * S)) * eps := by
        dsimp only [Bnd]; ring

/- Section 5: Purely Discrete Shift-Operator Nonvanishing -/

def shiftAction (P : Polynomial ℚ) (u : ℕ → ℚ) (s : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * u (s + j)

lemma shiftAction_eq_sum_of_natDegree_le {P : Polynomial ℚ} {N : ℕ} (hN : P.natDegree ≤ N)
    (u : ℕ → ℚ) (s : ℕ) :
    shiftAction P u s = ∑ j ∈ Finset.range (N + 1), P.coeff j * u (s + j) := by
  unfold shiftAction
  apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hN))
  intro j _ hj
  rw [Finset.mem_range] at hj
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

lemma shiftAction_zero_seq (P : Polynomial ℚ) : shiftAction P (fun _ => 0) = fun _ => 0 := by
  funext s; simp [shiftAction]

lemma shiftAction_sum {ι : Type*} (I : Finset ι) (P : Polynomial ℚ) (f : ι → ℕ → ℚ) (s : ℕ) :
    shiftAction P (fun t => ∑ i ∈ I, f i t) s = ∑ i ∈ I, shiftAction P (f i) s := by
  unfold shiftAction
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

lemma shiftAction_X_sub_C (a : ℚ) (u : ℕ → ℚ) (s : ℕ) :
    shiftAction (X - C a) u s = u (s + 1) - a * u s := by
  rw [shiftAction_eq_sum_of_natDegree_le (show (X - C a).natDegree ≤ 1 by
    rw [Polynomial.natDegree_X_sub_C])]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [zero_add, add_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
    Polynomial.coeff_C_zero, Polynomial.coeff_X_one, Polynomial.coeff_C_succ, sub_zero, one_mul]
  ring

lemma shiftAction_mul_X_sub_C (P : Polynomial ℚ) (a : ℚ) (u : ℕ → ℚ) (s : ℕ) :
    shiftAction (P * (X - C a)) u s = shiftAction P (shiftAction (X - C a) u) s := by
  set N := P.natDegree + 1
  have hdeg : (P * (X - C a)).natDegree ≤ N := by
    exact le_trans Polynomial.natDegree_mul_le (by rw [Polynomial.natDegree_X_sub_C])
  rw [shiftAction_eq_sum_of_natDegree_le hdeg]
  have hmul_sub : P * (X - C a) = P * X - C a * P := by ring
  rw [hmul_sub]
  simp_rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, sub_mul]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ j ∈ Finset.range (N + 1), (P * X).coeff j * u (s + j) =
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * u (s + j + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Polynomial.coeff_mul_X_zero, zero_mul, add_zero, Polynomial.coeff_mul_X]
    apply Finset.sum_congr rfl
    intro j _
    rw [show s + (j + 1) = s + j + 1 by omega]
  have h2 : ∑ j ∈ Finset.range (N + 1), a * P.coeff j * u (s + j) =
      ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * (a * u (s + j)) := by
    rw [Finset.sum_range_succ]
    have htop : P.coeff (P.natDegree + 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [htop, mul_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [h1, h2, ← Finset.sum_sub_distrib]
  change _ = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * shiftAction (X - C a) u (s + j)
  apply Finset.sum_congr rfl
  intro j _
  rw [shiftAction_X_sub_C]; ring

lemma shiftAction_mul (P R : Polynomial ℚ) (u : ℕ → ℚ) :
    shiftAction (P * R) u = shiftAction P (shiftAction R u) := by
  induction R using Polynomial.induction_on' with
  | add R₁ R₂ ih₁ ih₂ =>
    funext s
    have hdeg1 : (P * (R₁ + R₂)).natDegree ≤ P.natDegree + max R₁.natDegree R₂.natDegree :=
      le_trans Polynomial.natDegree_mul_le (Nat.add_le_add_left (Polynomial.natDegree_add_le _ _) _)
    have hadd_act : ∀ v, shiftAction (R₁ + R₂) v = fun t => shiftAction R₁ v t + shiftAction R₂ v t := by
      intro v; funext t
      set M := max R₁.natDegree R₂.natDegree
      rw [shiftAction_eq_sum_of_natDegree_le (le_trans (Polynomial.natDegree_add_le _ _) le_rfl),
        shiftAction_eq_sum_of_natDegree_le (le_max_left R₁.natDegree R₂.natDegree),
        shiftAction_eq_sum_of_natDegree_le (le_max_right R₁.natDegree R₂.natDegree)]
      simp_rw [Polynomial.coeff_add, add_mul]
      exact Finset.sum_add_distrib
    rw [mul_add, hadd_act]
    have hP_add : shiftAction (P * R₁ + P * R₂) u s =
        shiftAction (P * R₁) u s + shiftAction (P * R₂) u s := by
      set M := max (P * R₁).natDegree (P * R₂).natDegree
      rw [shiftAction_eq_sum_of_natDegree_le (le_trans (Polynomial.natDegree_add_le _ _) le_rfl),
        shiftAction_eq_sum_of_natDegree_le (le_max_left _ _),
        shiftAction_eq_sum_of_natDegree_le (le_max_right _ _)]
      simp_rw [Polynomial.coeff_add, add_mul]
      exact Finset.sum_add_distrib
    rw [hP_add, ih₁, ih₂]
    unfold shiftAction
    simp_rw [mul_add]
    exact (Finset.sum_add_distrib).symm
  | monomial n a =>
    funext s
    have hR : shiftAction (Polynomial.monomial n a) u = fun t => a * u (t + n) := by
      funext t
      rw [shiftAction_eq_sum_of_natDegree_le (Polynomial.natDegree_monomial_le a)]
      rw [Finset.sum_eq_single n]
      · simp
      · intro j _ hne
        rw [Polynomial.coeff_monomial, if_neg hne.symm, zero_mul]
      · intro hnot; exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_self n)))
    rw [hR]
    have hdeg : (P * Polynomial.monomial n a).natDegree ≤ P.natDegree + n :=
      le_trans Polynomial.natDegree_mul_le (Nat.add_le_add_left (Polynomial.natDegree_monomial_le a) _)
    rw [shiftAction_eq_sum_of_natDegree_le hdeg]
    have hmul_mon : ∀ j, (P * Polynomial.monomial n a).coeff j =
        if n ≤ j then P.coeff (j - n) * a else 0 := by
      intro j
      rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, mul_comm P (C a), mul_assoc,
        Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow']
      split_ifs <;> ring
    simp_rw [hmul_mon, ite_mul, zero_mul]
    unfold shiftAction
    calc ∑ j ∈ Finset.range (P.natDegree + n + 1), (if n ≤ j then P.coeff (j - n) * a * u (s + j) else 0)
        = ∑ j ∈ Finset.Ico n (P.natDegree + n + 1), P.coeff (j - n) * a * u (s + j) := by
          rw [← Finset.sum_filter]
          have hflt : (Finset.range (P.natDegree + n + 1)).filter (fun j => n ≤ j) =
              Finset.Ico n (P.natDegree + n + 1) := by
            ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
          rw [hflt]
      _ = ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * (a * u (s + j + n)) := by
          refine Finset.sum_bij (fun j _ => j - n) ?_ ?_ ?_ ?_
          · intro j hj; simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢; omega
          · intro j₁ hj₁ j₂ hj₂ heq; simp only [Finset.mem_Ico] at hj₁ hj₂; omega
          · intro b hb; refine ⟨b + n, ?_, by omega⟩
            simp only [Finset.mem_Ico, Finset.mem_range] at hb ⊢; omega
          · intro j hj; simp only [Finset.mem_Ico] at hj
            have hadd : s + j = s + (j - n) + n := by omega
            rw [hadd]; ring

lemma natDegree_comp_X_add_one_sub_lt {Q : Polynomial ℚ} (hQ : 0 < Q.natDegree) :
    (Q.comp (X + 1) - Q).natDegree < Q.natDegree := by
  have hdeg_comp : (Q.comp (X + 1)).natDegree = Q.natDegree := by
    rw [Polynomial.natDegree_comp]
    have : (X + 1 : Polynomial ℚ).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_add_C (1 : ℚ)
    rw [this, mul_one]
  have hlc_comp : (Q.comp (X + 1)).leadingCoeff = Q.leadingCoeff := by
    have hmon : (X + 1 : Polynomial ℚ).Monic := by
      simpa using Polynomial.monic_X_add_C (1 : ℚ)
    rw [Polynomial.leadingCoeff_comp (by
      have : (X + 1 : Polynomial ℚ).natDegree = 1 := by
        simpa using Polynomial.natDegree_X_add_C (1 : ℚ)
      omega)]
    simp [hmon.leadingCoeff]
  have hle : (Q.comp (X + 1) - Q).natDegree ≤ Q.natDegree - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [Polynomial.coeff_sub]
    rcases eq_or_lt_of_le (show Q.natDegree ≤ m by omega) with rfl | hgt
    · have h1 : (Q.comp (X + 1)).coeff Q.natDegree = (Q.comp (X + 1)).leadingCoeff := by
        rw [← hdeg_comp, Polynomial.coeff_natDegree]
      rw [h1, hlc_comp, Polynomial.coeff_natDegree, sub_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (Q.comp (X + 1)).natDegree < m),
        Polynomial.coeff_eq_zero_of_natDegree_lt hgt, sub_self]
  omega

lemma shiftAction_pow_X_sub_C_eval_mul_pow (ω : ℚ) (d : ℕ) :
    ∀ Q : Polynomial ℚ, Q.natDegree ≤ d →
      shiftAction ((X - C ω) ^ (d + 1)) (fun s : ℕ => Q.eval (s : ℚ) * ω ^ s) = fun _ => 0 := by
  induction d with
  | zero =>
    intro Q hQ
    funext s
    rw [pow_one, shiftAction_X_sub_C]
    have hconst : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hQ)
    rw [hconst]
    simp [pow_succ]; ring
  | succ d ih =>
    intro Q hQ
    rw [pow_succ, shiftAction_mul]
    have hstep : shiftAction (X - C ω) (fun s : ℕ => Q.eval (s : ℚ) * ω ^ s) =
        fun s : ℕ => (C ω * (Q.comp (X + 1) - Q)).eval (s : ℚ) * ω ^ s := by
      funext s
      rw [shiftAction_X_sub_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
        Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
        pow_succ, Nat.cast_add, Nat.cast_one]
      ring
    rw [hstep]
    by_cases hQ0 : Q.natDegree = 0
    · have hconst : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQ0
      have hzero : C ω * (Q.comp (X + 1) - Q) = 0 := by rw [hconst]; simp
      rw [hzero]
      simp only [Polynomial.eval_zero, zero_mul]
      exact shiftAction_zero_seq _
    · have hlt : (C ω * (Q.comp (X + 1) - Q)).natDegree ≤ d := by
        refine le_trans (Polynomial.natDegree_C_mul_le ω _) ?_
        have := natDegree_comp_X_add_one_sub_lt (Nat.pos_of_ne_zero hQ0)
        omega
      exact ih _ hlt

lemma exp_poly_zero_of_zero_on_Icc {ι : Type*} [Fintype ι]
    (ω : ι → ℕ) (hω_inj : Function.Injective ω) (hω_pos : ∀ i, 0 < ω i)
    (L₀ : ℕ) (Q : ι → Polynomial ℚ) (hdeg : ∀ i, (Q i).natDegree ≤ L₀)
    (hvan : ∀ s ∈ Finset.Icc 1 ((L₀ + 1) * Fintype.card ι),
      ∑ i : ι, (Q i).eval (s : ℚ) * (ω i : ℚ) ^ s = 0) :
    ∀ i, Q i = 0 := by
  classical
  set u : ℕ → ℚ := fun s => ∑ i : ι, (Q i).eval (s : ℚ) * (ω i : ℚ) ^ s
  set χ : Polynomial ℚ := ∏ i : ι, (X - C (ω i : ℚ)) ^ (L₀ + 1)
  have hχ_monic : χ.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => (Polynomial.monic_X_sub_C _).pow _
  set D := (L₀ + 1) * Fintype.card ι
  have hχ_deg : χ.natDegree = D := by
    dsimp only [χ, D]
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => (Polynomial.monic_X_sub_C _).pow _]
    simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    ring
  have hχ_kill : ∀ s, shiftAction χ u s = 0 := by
    intro s
    dsimp only [u]
    rw [shiftAction_sum]
    apply Finset.sum_eq_zero
    intro i _
    have hsplit : χ = (∏ j ∈ Finset.univ.erase i, (X - C (ω j : ℚ)) ^ (L₀ + 1)) *
        (X - C (ω i : ℚ)) ^ (L₀ + 1) := by
      dsimp only [χ]
      rw [mul_comm]
      exact (Finset.mul_prod_erase Finset.univ (fun j => (X - C (ω j : ℚ)) ^ (L₀ + 1))
        (Finset.mem_univ i)).symm
    rw [hsplit, shiftAction_mul, shiftAction_pow_X_sub_C_eval_mul_pow _ L₀ (Q i) (hdeg i),
      shiftAction_zero_seq]
  -- Strong induction: u s = 0 for ALL s ≥ 1
  have hall_zero : ∀ s, 1 ≤ s → u s = 0 := by
    intro s hs
    induction s using Nat.strong_induction_on with
    | h s ih =>
      by_cases hle : s ≤ D
      · exact hvan s (Finset.mem_Icc.mpr ⟨hs, hle⟩)
      · set t := s - D
        have ht1 : 1 ≤ t := by omega
        have htd : t + D = s := by omega
        have hkill := hχ_kill t
        unfold shiftAction at hkill
        rw [hχ_deg, Finset.sum_range_succ, ← hχ_deg, hχ_monic.coeff_natDegree, one_mul,
          hχ_deg, htd] at hkill
        have hsum0 : ∑ j ∈ Finset.range D, χ.coeff j * u (t + j) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjD : j < D := Finset.mem_range.mp hj
          rw [ih (t + j) (by omega) (by omega), mul_zero]
        rw [hsum0, zero_add] at hkill
        exact hkill
  -- Dominant-term limit contradiction if any Q i ≠ 0
  by_contra hnot
  push Not at hnot
  set S := Finset.univ.filter (fun i : ι => Q i ≠ 0)
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hnot
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨imax, himaxS, himax_ge⟩ := Finset.exists_max_image S ω hSne
  have hQmax_ne : Q imax ≠ 0 := (Finset.mem_filter.mp himaxS).2
  have hωmax_pos : (0 : ℝ) < (ω imax : ℝ) := by exact_mod_cast hω_pos imax
  -- For every s ≥ 1, in ℝ: (Q imax).eval s + ∑_{i ∈ S.erase imax} (Q i).eval s * (ω i / ω imax)^s = 0
  have heval_cast : ∀ (P : Polynomial ℚ) (s : ℕ),
      (P.map (algebraMap ℚ ℝ)).eval (s : ℝ) = Rat.cast (P.eval (s : ℚ)) := by
    intro P s
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Rat.cast_sum]
    have hdeg : (P.map (algebraMap ℚ ℝ)).natDegree = P.natDegree :=
      Polynomial.natDegree_map_eq_of_injective Rat.cast_injective P
    rw [hdeg]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.coeff_map, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
    rfl
  have hreal_eq : ∀ s : ℕ, 1 ≤ s →
      ((Q imax).map (algebraMap ℚ ℝ)).eval (s : ℝ) +
      ∑ i ∈ S.erase imax,
        ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) * ((ω i : ℝ) / (ω imax : ℝ)) ^ s = 0 := by
    intro s hs
    have hu0 : (u s : ℝ) = 0 := by rw [hall_zero s hs, Rat.cast_zero]
    have hdiv0 : (u s : ℝ) / (ω imax : ℝ) ^ s = 0 := by rw [hu0, zero_div]
    rw [← hdiv0]
    dsimp only [u]
    rw [Rat.cast_sum, Finset.sum_div]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · rw [← Finset.add_sum_erase _ _ himaxS]
      congr 1
      · rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
          heval_cast, mul_div_cancel_right₀ _ (pow_ne_zero s hωmax_pos.ne')]
      · apply Finset.sum_congr rfl
        intro i _
        rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
          heval_cast, mul_div_assoc, ← div_pow]
    · intro i _ hi
      have hQ0 : Q i = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      simp [hQ0]
  -- Each term in S.erase imax tends to 0
  have htail_zero : Tendsto (fun s : ℕ =>
      ∑ i ∈ S.erase imax,
        ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) * ((ω i : ℝ) / (ω imax : ℝ)) ^ s)
      atTop (nhds 0) := by
    have hterm : ∀ i ∈ S.erase imax, Tendsto (fun s : ℕ =>
        ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) * ((ω i : ℝ) / (ω imax : ℝ)) ^ s)
        atTop (nhds 0) := by
      intro i hi
      have hiS : i ∈ S := Finset.mem_of_mem_erase hi
      have hine : i ≠ imax := Finset.ne_of_mem_erase hi
      have hlt_nat : ω i < ω imax :=
        lt_of_le_of_ne (himax_ge i hiS) (fun h => hine (hω_inj h))
      set r : ℝ := (ω i : ℝ) / (ω imax : ℝ)
      have hr0 : 0 < r := div_pos (by exact_mod_cast hω_pos i) hωmax_pos
      have hr1 : r < 1 := (div_lt_one hωmax_pos).mpr (by exact_mod_cast hlt_nat)
      have hlogr : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hr1)
      set P : Polynomial ℝ := (Q i).map (algebraMap ℚ ℝ)
      have hpow_lim : ∀ j : ℕ, Tendsto (fun s : ℕ => (s : ℝ) ^ j * r ^ s) atTop (nhds 0) := by
        intro j
        have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
          (tendsto_id.const_mul_atTop hlogr)
        have h2 := (h1.comp tendsto_natCast_atTop_atTop).const_mul ((-Real.log r) ^ j)⁻¹
        simp only [mul_zero] at h2
        refine h2.congr (fun s => ?_)
        dsimp only [Function.comp_apply, id_eq]
        have hr_pow : r ^ s = Real.exp (-((-Real.log r) * (s : ℝ))) := by
          rw [neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hr0]
        rw [hr_pow]
        have hne : (-Real.log r) ^ j ≠ 0 := pow_ne_zero j hlogr.ne'
        rw [mul_pow]; field_simp [hne]
      have hsum_lim : Tendsto (fun s : ℕ =>
          ∑ j ∈ Finset.range (P.natDegree + 1), P.coeff j * ((s : ℝ) ^ j * r ^ s))
          atTop (nhds 0) := by
        have h := tendsto_finsetSum (Finset.range (P.natDegree + 1)) fun j _ =>
          by simpa using (hpow_lim j).const_mul (P.coeff j)
        simpa [Finset.sum_const_zero] using h
      refine hsum_lim.congr (fun s => ?_)
      rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    simpa [Finset.sum_const_zero] using tendsto_finsetSum (S.erase imax) hterm
  -- Meanwhile |((Q imax).map ...).eval s| is eventually ≥ |leadingCoeff| / 2 > 0
  set Pmax : Polynomial ℝ := (Q imax).map (algebraMap ℚ ℝ)
  have hPmax_ne : Pmax ≠ 0 := by
    intro h0
    apply hQmax_ne
    exact Polynomial.map_injective (algebraMap ℚ ℝ) Rat.cast_injective
      (by rw [Polynomial.map_zero]; exact h0)
  have hlc_pos : 0 < |Pmax.leadingCoeff| := abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hPmax_ne)
  have hlead_lim : Tendsto (fun s : ℕ => Pmax.eval (s : ℝ) / (s : ℝ) ^ Pmax.natDegree)
      atTop (nhds Pmax.leadingCoeff) := by
    set d := Pmax.natDegree
    have hrew : ∀ᶠ s : ℕ in atTop,
        Pmax.eval (s : ℝ) / (s : ℝ) ^ d =
          Pmax.leadingCoeff + ∑ j ∈ Finset.range d, Pmax.coeff j * ((s : ℝ) ^ (d - j))⁻¹ := by
      filter_upwards [eventually_ge_atTop 1] with s hs
      have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, add_div, Finset.sum_div]
      rw [mul_div_cancel_right₀ _ (pow_ne_zero d hs0), add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      rw [mul_div_assoc]
      have hpow : (s : ℝ) ^ d = (s : ℝ) ^ j * (s : ℝ) ^ (d - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hjd.le]
      rw [hpow, div_mul_eq_div_div, div_self (pow_ne_zero j hs0), one_div]
    rw [tendsto_congr' hrew]
    have hsum0 : Tendsto (fun s : ℕ =>
        ∑ j ∈ Finset.range d, Pmax.coeff j * ((s : ℝ) ^ (d - j))⁻¹) atTop (nhds 0) := by
      have h := tendsto_finsetSum (Finset.range d) fun j hj => by
        have hjd : 0 < d - j := by have := Finset.mem_range.mp hj; omega
        have h1 : Tendsto (fun s : ℕ => ((s : ℝ) ^ (d - j))⁻¹) atTop (nhds 0) :=
          tendsto_inv_atTop_zero.comp
            ((tendsto_pow_atTop hjd.ne').comp tendsto_natCast_atTop_atTop)
        simpa using h1.const_mul (Pmax.coeff j)
      simpa [Finset.sum_const_zero] using h
    simpa using hsum0.const_add Pmax.leadingCoeff
  have hev_lead : ∀ᶠ s : ℕ in atTop, |Pmax.leadingCoeff| / 2 < |Pmax.eval (s : ℝ)| := by
    have h1 := ((tendsto_order.mp hlead_lim.abs).1 (|Pmax.leadingCoeff| / 2) (by linarith))
    filter_upwards [h1, eventually_ge_atTop 1] with s hs h1s
    have hpow1 : (1 : ℝ) ≤ (s : ℝ) ^ Pmax.natDegree :=
      one_le_pow₀ (by exact_mod_cast h1s)
    rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hpow1), lt_div_iff₀ (lt_of_lt_of_le zero_lt_one hpow1)] at hs
    nlinarith
  have hev_tail : ∀ᶠ s : ℕ in atTop,
      |∑ i ∈ S.erase imax, ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) *
        ((ω i : ℝ) / (ω imax : ℝ)) ^ s| < |Pmax.leadingCoeff| / 2 :=
    (tendsto_order.mp htail_zero.abs).2 (|Pmax.leadingCoeff| / 2) (by linarith)
  have hev_all := hev_lead.and (hev_tail.and (eventually_ge_atTop 1))
  obtain ⟨s, hs_lead, hs_tail, hs1⟩ := hev_all.exists
  have heq := hreal_eq s hs1
  have habs_eq : |Pmax.eval (s : ℝ)| =
      |∑ i ∈ S.erase imax, ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) *
        ((ω i : ℝ) / (ω imax : ℝ)) ^ s| := by
    have hneg : Pmax.eval (s : ℝ) =
        -(∑ i ∈ S.erase imax, ((Q i).map (algebraMap ℚ ℝ)).eval (s : ℝ) *
          ((ω i : ℝ) / (ω imax : ℝ)) ^ s) := eq_neg_of_add_eq_zero_left heq
    rw [hneg, abs_neg]
  linarith

/- Section 6: Auxiliary Functions `Psi` and `G`, Derivative Recurrence, & Approximation Error -/

abbrev Idx (L₀ L m : ℕ) := Fin (L₀ + 1) × (Fin (m + 1) → Fin (L + 1))

def betaRat {m : ℕ} (b : Fin (m + 1) → ℤ) (r : Fin m) : ℚ :=
  -(b (Fin.castSucc r) : ℚ) / (b (Fin.last m) : ℚ)

def gammaRat {L₀ L m : ℕ} (b : Fin (m + 1) → ℤ) (idx : Idx L₀ L m) (r : Fin m) : ℚ :=
  ((idx.2 (Fin.castSucc r)).val : ℚ) + ((idx.2 (Fin.last m)).val : ℚ) * betaRat b r

def gammaInt {L₀ L m : ℕ} (b : Fin (m + 1) → ℤ) (idx : Idx L₀ L m) (r : Fin m) : ℤ :=
  b (Fin.last m) * ((idx.2 (Fin.castSucc r)).val : ℤ) -
    b (Fin.castSucc r) * ((idx.2 (Fin.last m)).val : ℤ)

lemma bn_mul_gammaRat {L₀ L m : ℕ} {b : Fin (m + 1) → ℤ} (hbn : b (Fin.last m) ≠ 0)
    (idx : Idx L₀ L m) (r : Fin m) :
    (b (Fin.last m) : ℚ) * gammaRat b idx r = (gammaInt b idx r : ℚ) := by
  unfold gammaRat betaRat gammaInt
  have hbnQ : (b (Fin.last m) : ℚ) ≠ 0 := by exact_mod_cast hbn
  push_cast
  field_simp [hbnQ]
  ring

lemma abs_betaRat_le_one {m : ℕ} {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m))
    (hble : ∀ i, |b i| ≤ b (Fin.last m)) (r : Fin m) :
    |(betaRat b r : ℝ)| ≤ 1 := by
  unfold betaRat
  push_cast
  have hbnR : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn
  rw [abs_div, abs_neg, abs_of_pos hbnR, div_le_one hbnR]
  have h1 := hble (Fin.castSucc r)
  exact_mod_cast h1

lemma abs_gammaRat_le {L₀ L m : ℕ} {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m))
    (hble : ∀ i, |b i| ≤ b (Fin.last m)) (idx : Idx L₀ L m) (r : Fin m) :
    |(gammaRat b idx r : ℝ)| ≤ 2 * (L : ℝ) := by
  unfold gammaRat
  push_cast
  have h1 : ((idx.2 (Fin.castSucc r)).val : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (idx.2 (Fin.castSucc r)).isLt
  have h2 : ((idx.2 (Fin.last m)).val : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (idx.2 (Fin.last m)).isLt
  have hβ := abs_betaRat_le_one hbn hble r
  calc |((idx.2 (Fin.castSucc r)).val : ℝ) + ((idx.2 (Fin.last m)).val : ℝ) * (betaRat b r : ℝ)|
      ≤ |((idx.2 (Fin.castSucc r)).val : ℝ)| + |((idx.2 (Fin.last m)).val : ℝ) * (betaRat b r : ℝ)| :=
        abs_add_le _ _
    _ = ((idx.2 (Fin.castSucc r)).val : ℝ) + ((idx.2 (Fin.last m)).val : ℝ) * |(betaRat b r : ℝ)| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ (L : ℝ) + (L : ℝ) * 1 := by
        have : ((idx.2 (Fin.last m)).val : ℝ) * |(betaRat b r : ℝ)| ≤ (L : ℝ) * 1 :=
          mul_le_mul h2 hβ (abs_nonneg _) (Nat.cast_nonneg _)
        linarith
    _ = 2 * (L : ℝ) := by ring

lemma abs_gammaInt_le {L₀ L m : ℕ} {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m))
    (hble : ∀ i, |b i| ≤ b (Fin.last m)) (idx : Idx L₀ L m) (r : Fin m) :
    |(gammaInt b idx r : ℝ)| ≤ 2 * (b (Fin.last m) : ℝ) * (L : ℝ) := by
  have hbnR : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn
  have heq : (gammaInt b idx r : ℝ) = (b (Fin.last m) : ℝ) * (gammaRat b idx r : ℝ) := by
    have hq := bn_mul_gammaRat (ne_of_gt hbn) idx r
    have hr := congr_arg (Rat.cast (K := ℝ)) hq
    simpa using hr.symm
  rw [heq, abs_mul, abs_of_pos hbnR]
  have := abs_gammaRat_le hbn hble idx r
  nlinarith

noncomputable def Psi {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (s : ℕ) : ℚ :=
  ∑ idx : Idx L₀ L m, (c idx : ℚ) *
    (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
    (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
    (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s)

noncomputable def G {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (z : ℂ) : ℂ :=
  ∑ idx : Idx L₀ L m, (c idx : ℂ) *
    ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z *
    (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
    Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))

lemma Psi_cleared_int {L₀ L m : ℕ} {k : ℕ} (hk : 0 < k)
    (p : Fin (m + 1) → ℕ) {b : Fin (m + 1) → ℤ} (hbn : b (Fin.last m) ≠ 0)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (s : ℕ) :
    ∃ z : ℤ, (z : ℚ) =
      ((Nat.lcmUpto k : ℚ) ^ (t 0)) *
      ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
      Psi k p b c t s := by
  unfold Psi
  rw [Finset.mul_sum]
  have hterm : ∀ idx : Idx L₀ L m, ∃ z : ℤ,
      (z : ℚ) =
        ((Nat.lcmUpto k : ℚ) ^ (t 0)) *
        ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
        ((c idx : ℚ) *
          (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
          (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
          (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s)) := by
    intro idx
    obtain ⟨zF, hzF⟩ := lcmUpto_pow_mul_hasseDeriv_feldmanPoly_int hk idx.1.val (t 0) s
    refine ⟨c idx * zF * (∏ r : Fin m, (gammaInt b idx r) ^ (t (Fin.succ r))) *
        (∏ i : Fin (m + 1), ((p i : ℤ) ^ (idx.2 i).val) ^ s), ?_⟩
    have hprod_gamma :
        ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
          (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) =
        ∏ r : Fin m, ((gammaInt b idx r : ℚ) ^ (t (Fin.succ r))) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro r _
      rw [← mul_pow, bn_mul_gammaRat hbn idx r]
    push_cast
    rw [hzF, ← hprod_gamma]
    ring
  choose f hf using hterm
  refine ⟨∑ idx : Idx L₀ L m, f idx, ?_⟩
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun idx _ => hf idx

lemma Psi_lower_of_ne_zero {L₀ L m : ℕ} {k : ℕ} (hk : 0 < k)
    (p : Fin (m + 1) → ℕ) {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m))
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (s : ℕ)
    (hne : Psi k p b c t s ≠ 0) :
    (((Nat.lcmUpto k : ℝ) ^ (t 0)) * ((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r))))⁻¹ ≤
      |(Psi k p b c t s : ℝ)| := by
  obtain ⟨z, hz⟩ := Psi_cleared_int hk p (ne_of_gt hbn) c t s
  have hden_pos : (0 : ℝ) < ((Nat.lcmUpto k : ℝ) ^ (t 0)) *
      ((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r))) := by
    have h1 : (0 : ℝ) < (Nat.lcmUpto k : ℝ) := by exact_mod_cast Nat.lcmUpto_pos k
    have h2 : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn
    positivity
  have hz_ne : z ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero] at hz
    have hdenQ : ((Nat.lcmUpto k : ℚ) ^ (t 0)) *
        ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) ≠ 0 := by
      have h1 : (Nat.lcmUpto k : ℚ) ≠ 0 := by exact_mod_cast (Nat.lcmUpto_pos k).ne'
      have h2 : (b (Fin.last m) : ℚ) ≠ 0 := by exact_mod_cast hbn.ne'
      positivity
    exact hne ((mul_eq_zero.mp hz.symm).resolve_left hdenQ)
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz_ne
    exact_mod_cast this
  have hcast : (z : ℝ) =
      (((Nat.lcmUpto k : ℝ) ^ (t 0)) * ((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)))) *
      (Psi k p b c t s : ℝ) := by
    have := congr_arg (Rat.cast (K := ℝ)) hz
    simpa using this
  rw [hcast, abs_mul, abs_of_pos hden_pos] at hz1
  rw [inv_le_iff_one_le_mul₀' hden_pos]
  exact hz1

lemma G_differentiable {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) :
    Differentiable ℂ (G k p b c t) := by
  unfold G
  refine Differentiable.fun_sum fun idx _ => ?_
  have hpoly : Differentiable ℂ (fun z : ℂ =>
      ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z) :=
    fun z => (hasDerivAt_eval_poly _ z).differentiableAt
  have hexp : Differentiable ℂ (fun z : ℂ =>
      Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))) :=
    (differentiable_id.mul_const _).cexp
  exact (((differentiable_const _).mul hpoly).mul (differentiable_const _)).mul hexp

lemma hasDerivAt_G {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ) (b : Fin (m + 1) → ℤ)
    (c : Idx L₀ L m → ℤ) (t : Fin (m + 1) → ℕ) (z : ℂ) :
    HasDerivAt (G k p b c t)
      (((t 0 + 1 : ℕ) : ℂ) * G k p b c (Function.update t 0 (t 0 + 1)) z +
        ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
          G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1)) z) z := by
  have hterm : ∀ idx : Idx L₀ L m,
      HasDerivAt
        (fun w => (c idx : ℂ) *
          ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval w *
          (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
          Complex.exp (w * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)))
        (((t 0 + 1 : ℕ) : ℂ) * ((c idx : ℂ) *
            ((Polynomial.hasseDeriv (t 0 + 1) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z *
            (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
            Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))) +
          ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) * ((c idx : ℂ) *
            ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z *
            (∏ r' : Fin m, ((gammaRat b idx r' : ℚ) : ℂ) ^ (Function.update t (Fin.succ r) (t (Fin.succ r) + 1) (Fin.succ r'))) *
            Complex.exp (z * ∑ r' : Fin m, ((gammaRat b idx r' : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r') : ℝ) : ℂ))))
        z := by
    intro idx
    set P : Polynomial ℂ := (feldmanPoly k idx.1.val).map (algebraMap ℚ ℂ)
    set gam : ℂ := ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)
    set coef : ℂ := (c idx : ℂ) * (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r)))
    have hpoly : HasDerivAt (fun w => (Polynomial.hasseDeriv (t 0) P).eval w)
        (((t 0 + 1 : ℕ) : ℂ) * (Polynomial.hasseDeriv (t 0 + 1) P).eval z) z := by
      have h1 := hasDerivAt_eval_poly (Polynomial.hasseDeriv (t 0) P) z
      rw [derivative_hasseDeriv_eq, Polynomial.eval_smul, smul_eq_mul] at h1
      exact h1
    have hexp : HasDerivAt (fun w => Complex.exp (w * gam)) (gam * Complex.exp (z * gam)) z := by
      have h1 : HasDerivAt (fun w => w * gam) (1 * gam) z := (hasDerivAt_id z).mul_const gam
      rw [one_mul] at h1
      simpa [mul_comm] using h1.cexp
    have hmul := (hpoly.mul hexp).const_mul coef
    simp only [Pi.mul_apply] at hmul
    have hfun_eq : (fun w => coef * ((Polynomial.hasseDeriv (t 0) P).eval w * Complex.exp (w * gam))) =
        (fun w => (c idx : ℂ) *
          ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval w *
          (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
          Complex.exp (w * gam)) := by
      funext w; rw [Polynomial.hasseDeriv_map]; dsimp only [coef, P]; ring
    rw [hfun_eq] at hmul
    refine hmul.congr_deriv ?_
    rw [Polynomial.hasseDeriv_map, Polynomial.hasseDeriv_map]
    have hprod_upd : ∀ r : Fin m,
        (∏ r' : Fin m, ((gammaRat b idx r' : ℚ) : ℂ) ^
          (Function.update t (Fin.succ r) (t (Fin.succ r) + 1) (Fin.succ r'))) =
        ((gammaRat b idx r : ℚ) : ℂ) *
          (∏ r' : Fin m, ((gammaRat b idx r' : ℚ) : ℂ) ^ (t (Fin.succ r'))) := by
      intro r
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r),
        ← Finset.mul_prod_erase Finset.univ (fun r' => ((gammaRat b idx r' : ℚ) : ℂ) ^ (t (Fin.succ r')))
          (Finset.mem_univ r)]
      simp only [Function.update_self, pow_succ']
      rw [mul_assoc]
      congr 2
      apply Finset.prod_congr rfl
      intro r' hr'
      have hne : Fin.succ r' ≠ Fin.succ r := Fin.succ_injective _ |>.ne (Finset.ne_of_mem_erase hr')
      rw [Function.update_of_ne hne]
    simp_rw [hprod_upd]
    dsimp only [coef, gam, P]
    rw [mul_add]
    congr 1
    · ring
    · rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _; ring
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun idx _ => hterm idx)
  refine hsum.congr_deriv ?_
  unfold G
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro idx _
    have hupd0 : Function.update t 0 (t 0 + 1) 0 = t 0 + 1 := Function.update_self 0 _ t
    have hupds : ∀ r : Fin m, Function.update t 0 (t 0 + 1) (Fin.succ r) = t (Fin.succ r) :=
      fun r => Function.update_of_ne (Fin.succ_ne_zero r) _ t
    simp_rw [hupd0, hupds]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro idx _
    have hupd0 : Function.update t (Fin.succ r) (t (Fin.succ r) + 1) 0 = t 0 :=
      Function.update_of_ne (Fin.succ_ne_zero r).symm _ t
    simp_rw [hupd0]

lemma norm_iteratedDeriv_G_le {L₀ L m : ℕ} (k : ℕ) (p : Fin (m + 1) → ℕ)
    (hp : ∀ i, (p i).Prime) (b : Fin (m + 1) → ℤ) (c : Idx L₀ L m → ℤ)
    (s : ℕ) (t : Fin (m + 1) → ℕ) (z : ℂ) {Emax : ℝ} (hEmax : 0 ≤ Emax)
    (hG : ∀ u : Fin (m + 1) → ℕ, (∑ i, u i) = (∑ i, t i) + s → ‖G k p b c u z‖ ≤ Emax) :
    ‖iteratedDeriv s (G k p b c t) z‖ ≤
      (((∑ i, t i) + s + 1 : ℕ) + ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) ^ s * Emax := by
  set αm : ℝ := ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)
  have hαm : 0 ≤ αm := Finset.sum_nonneg fun r _ =>
    Real.log_nonneg (by exact_mod_cast (hp (Fin.castSucc r)).one_lt.le)
  induction s generalizing t with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
    exact hG t (by omega)
  | succ s ih =>
    rw [iteratedDeriv_succ']
    have hderiv_eq : deriv (G k p b c t) =
        fun w => ((t 0 + 1 : ℕ) : ℂ) * G k p b c (Function.update t 0 (t 0 + 1)) w +
          ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
            G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1)) w := by
      funext w; exact (hasDerivAt_G k p b c t w).deriv
    rw [hderiv_eq]
    have hcd0 : ContDiffAt ℂ (s : ℕ) (fun w => ((t 0 + 1 : ℕ) : ℂ) * G k p b c (Function.update t 0 (t 0 + 1)) w) z :=
      ((differentiable_const _).mul (G_differentiable k p b c _)).contDiff.contDiffAt
    have hcd_r : ∀ r : Fin m, ContDiffAt ℂ (s : ℕ)
        (fun w => (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
          G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1)) w) z := fun r =>
      ((differentiable_const _).mul (G_differentiable k p b c _)).contDiff.contDiffAt
    have hcd_sum : ContDiffAt ℂ (s : ℕ)
        (fun w => ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
          G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1)) w) z :=
      ContDiffAt.sum fun r _ => hcd_r r
    rw [iteratedDeriv_fun_add hcd0 hcd_sum, iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_sum (fun r _ => hcd_r r)]
    simp_rw [iteratedDeriv_const_mul_field]
    have hsum_upd : ∀ j : Fin (m + 1), (∑ i, Function.update t j (t j + 1) i) = (∑ i, t i) + 1 := by
      intro j
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j),
        ← Finset.add_sum_erase Finset.univ t (Finset.mem_univ j)]
      simp only [Function.update_self]
      have hrest : ∑ i ∈ Finset.univ.erase j, Function.update t j (t j + 1) i =
          ∑ i ∈ Finset.univ.erase j, t i :=
        Finset.sum_congr rfl fun i hi => Function.update_of_ne (Finset.ne_of_mem_erase hi) _ t
      rw [hrest]; omega
    have hbase_eq : ∀ j : Fin (m + 1),
        (((∑ i, Function.update t j (t j + 1) i) + s + 1 : ℕ) : ℝ) + αm =
        (((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm := by
      intro j; rw [hsum_upd j]; push_cast; ring
    have hih_j : ∀ j : Fin (m + 1),
        ‖iteratedDeriv s (G k p b c (Function.update t j (t j + 1))) z‖ ≤
        ((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax := by
      intro j
      rw [← hbase_eq j]
      exact ih (Function.update t j (t j + 1)) (fun u hu => hG u (by rw [hu, hsum_upd j]; omega))
    have ht0_le : (t 0 : ℝ) ≤ ∑ i : Fin (m + 1), (t i : ℝ) :=
      Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ (0 : Fin (m + 1)))
    calc ‖((t 0 + 1 : ℕ) : ℂ) * iteratedDeriv s (G k p b c (Function.update t 0 (t 0 + 1))) z +
            ∑ r : Fin m, (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
              iteratedDeriv s (G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1))) z‖
        ≤ ‖((t 0 + 1 : ℕ) : ℂ) * iteratedDeriv s (G k p b c (Function.update t 0 (t 0 + 1))) z‖ +
            ∑ r : Fin m, ‖(Real.log (p (Fin.castSucc r) : ℝ) : ℂ) *
              iteratedDeriv s (G k p b c (Function.update t (Fin.succ r) (t (Fin.succ r) + 1))) z‖ :=
          le_trans (norm_add_le _ _) (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ ((t 0 + 1 : ℕ) : ℝ) * (((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax) +
            ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) *
              (((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax) := by
          apply add_le_add
          · rw [norm_mul, Complex.norm_natCast]
            exact mul_le_mul_of_nonneg_left (hih_j 0) (Nat.cast_nonneg _)
          · apply Finset.sum_le_sum
            intro r _
            have hlog0 : 0 ≤ Real.log (p (Fin.castSucc r) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (hp (Fin.castSucc r)).one_lt.le)
            rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hlog0]
            exact mul_le_mul_of_nonneg_left (hih_j (Fin.succ r)) hlog0
      _ = (((t 0 + 1 : ℕ) : ℝ) + αm) * (((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax) := by
          rw [← Finset.sum_mul]; ring
      _ ≤ ((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) *
            (((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ s * Emax) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          push_cast; linarith
      _ = ((((∑ i, t i) + (s + 1) + 1 : ℕ) : ℝ) + αm) ^ (s + 1) * Emax := by
          rw [pow_succ']; ring

lemma norm_G_le {L₀ L m k T₀ : ℕ} (hk : 0 < k)
    (p : Fin (m + 1) → ℕ) (hp : ∀ i, (p i).Prime)
    {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m)) (hble : ∀ i, |b i| ≤ b (Fin.last m))
    (c : Idx L₀ L m → ℤ) {Cmax : ℝ} (hCmax : ∀ idx, |(c idx : ℝ)| ≤ Cmax) (hC0 : 0 ≤ Cmax)
    {t : Fin (m + 1) → ℕ} (ht : ∑ i, t i ≤ T₀)
    {z : ℂ} {R : ℝ} (hR : ‖z‖ ≤ R) :
    ‖G k p b c t z‖ ≤
      (Fintype.card (Idx L₀ L m) : ℝ) * Cmax *
      ((Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
      ((2 * (L : ℝ) + 1) ^ T₀) *
      Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R) := by
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) hR
  unfold G
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ idx : Idx L₀ L m,
        ‖(c idx : ℂ) *
          ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z *
          (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
          Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))‖
      ≤ ∑ _idx : Idx L₀ L m,
          Cmax * ((Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
          ((2 * (L : ℝ) + 1) ^ T₀) *
          Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R) := by
        apply Finset.sum_le_sum
        intro idx _
        rw [norm_mul, norm_mul, norm_mul]
        have h1 : ‖(c idx : ℂ)‖ ≤ Cmax := by
          rw [Complex.norm_intCast]; exact hCmax idx
        have h2 : ‖((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval z‖ ≤
            (Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) :=
          norm_eval_hasseDeriv_feldmanPoly_le hk (Nat.lt_succ_iff.mp idx.1.isLt) z hR
        have h3 : ‖∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))‖ ≤
            (2 * (L : ℝ) + 1) ^ T₀ := by
          rw [norm_prod]
          calc ∏ r : Fin m, ‖((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))‖
              ≤ ∏ r : Fin m, (2 * (L : ℝ) + 1) ^ (t (Fin.succ r)) := by
                apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                intro r _
                rw [norm_pow, Complex.norm_ratCast]
                apply pow_le_pow_left₀ (abs_nonneg _)
                linarith [abs_gammaRat_le hbn hble idx r]
            _ = (2 * (L : ℝ) + 1) ^ (∑ r : Fin m, t (Fin.succ r)) := by
                rw [Finset.prod_pow_eq_pow_sum]
            _ ≤ (2 * (L : ℝ) + 1) ^ T₀ := by
                apply pow_le_pow_right₀ (by have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L; linarith)
                have hsum_split : ∑ i : Fin (m + 1), t i = t 0 + ∑ r : Fin m, t (Fin.succ r) :=
                  Fin.sum_univ_succ t
                omega
        have h4 : ‖Complex.exp (z * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ))‖ ≤
            Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R) := by
          rw [Complex.norm_exp]
          apply Real.exp_le_exp.mpr
          refine le_trans (Complex.re_le_norm _) ?_
          rw [norm_mul]
          have hsum_norm : ‖∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)‖ ≤
              2 * (L : ℝ) * ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) := by
            refine le_trans (norm_sum_le _ _) ?_
            rw [Finset.mul_sum]
            apply Finset.sum_le_sum
            intro r _
            have hlog0 : 0 ≤ Real.log (p (Fin.castSucc r) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast (hp (Fin.castSucc r)).one_lt.le)
            rw [norm_mul, Complex.norm_ratCast, Complex.norm_real, Real.norm_of_nonneg hlog0]
            exact mul_le_mul_of_nonneg_right (abs_gammaRat_le hbn hble idx r) hlog0
          calc ‖z‖ * ‖∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)‖
              ≤ R * (2 * (L : ℝ) * ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) :=
                mul_le_mul hR hsum_norm (norm_nonneg _) hR0
            _ = 2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R := by ring
        have h12 := mul_le_mul h1 h2 (norm_nonneg _) hC0
        have h123 := mul_le_mul h12 h3 (norm_nonneg _) (by positivity)
        exact mul_le_mul h123 h4 (norm_nonneg _) (by positivity)
    _ = (Fintype.card (Idx L₀ L m) : ℝ) * Cmax *
        ((Real.exp 1 * (R + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
        ((2 * (L : ℝ) + 1) ^ T₀) *
        Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * R) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

lemma norm_G_sub_Psi_le {L₀ L m k T₀ : ℕ} (hk : 0 < k)
    (p : Fin (m + 1) → ℕ) (hp : ∀ i, (p i).Prime)
    {b : Fin (m + 1) → ℤ} (hbn : 0 < b (Fin.last m)) (hble : ∀ i, |b i| ≤ b (Fin.last m))
    (c : Idx L₀ L m → ℤ) {Cmax : ℝ} (hCmax : ∀ idx, |(c idx : ℝ)| ≤ Cmax) (hC0 : 0 ≤ Cmax)
    {t : Fin (m + 1) → ℕ} (ht : ∑ i, t i ≤ T₀) (s : ℕ)
    (hsmall : (s : ℝ) * (L : ℝ) *
      (|∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| / (b (Fin.last m) : ℝ)) ≤ 1) :
    ‖G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)‖ ≤
      2 * (s : ℝ) * (L : ℝ) *
      (|∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| / (b (Fin.last m) : ℝ)) *
      (Fintype.card (Idx L₀ L m) : ℝ) * Cmax *
      ((Real.exp 1 * ((s : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
      ((2 * (L : ℝ) + 1) ^ T₀) *
      Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (s : ℝ)) := by
  set Λ : ℝ := ∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)
  set Λ' : ℝ := Λ / (b (Fin.last m) : ℝ)
  have hbnR : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn
  have hΛ'abs : |Λ'| = |Λ| / (b (Fin.last m) : ℝ) := by
    rw [abs_div, abs_of_pos hbnR]
  have hlin : ∑ r : Fin m, (betaRat b r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ) =
      Real.log (p (Fin.last m) : ℝ) - Λ' := by
    have hsplit : Λ = (∑ r : Fin m, (b (Fin.castSucc r) : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) +
        (b (Fin.last m) : ℝ) * Real.log (p (Fin.last m) : ℝ) := Fin.sum_univ_castSucc _
    have h1 : Λ' = (∑ r : Fin m, (b (Fin.castSucc r) : ℝ) / (b (Fin.last m) : ℝ) *
          Real.log (p (Fin.castSucc r) : ℝ)) + Real.log (p (Fin.last m) : ℝ) := by
      dsimp only [Λ']
      rw [hsplit, add_div, Finset.sum_div, mul_div_cancel_left₀ _ hbnR.ne']
      congr 1; apply Finset.sum_congr rfl; intro r _; ring
    have h2 : ∑ r : Fin m, (betaRat b r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ) =
        -(∑ r : Fin m, (b (Fin.castSucc r) : ℝ) / (b (Fin.last m) : ℝ) *
          Real.log (p (Fin.castSucc r) : ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro r _; unfold betaRat; push_cast; ring
    linarith
  have heval_C : ∀ (P : Polynomial ℚ),
      (P.map (algebraMap ℚ ℂ)).eval (s : ℂ) = ((P.eval (s : ℚ) : ℚ) : ℂ) := by
    intro P
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Rat.cast_sum]
    have hdeg : (P.map (algebraMap ℚ ℂ)).natDegree = P.natDegree :=
      Polynomial.natDegree_map_eq_of_injective Rat.cast_injective P
    rw [hdeg]
    apply Finset.sum_congr rfl
    intro j _
    rw [Polynomial.coeff_map, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
    rfl
  unfold G Psi
  rw [Rat.cast_sum, ← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  calc ∑ idx : Idx L₀ L m,
        ‖(c idx : ℂ) *
            ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval (s : ℂ) *
            (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
            Complex.exp ((s : ℂ) * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)) -
          (((c idx : ℚ) *
            (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
            (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
            (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s) : ℚ) : ℂ)‖
      ≤ ∑ _idx : Idx L₀ L m,
          2 * (s : ℝ) * (L : ℝ) * |Λ'| * Cmax *
          ((Real.exp 1 * ((s : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
          ((2 * (L : ℝ) + 1) ^ T₀) *
          Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (s : ℝ)) := by
        apply Finset.sum_le_sum
        intro idx _
        have hcast_term :
            (((c idx : ℚ) *
              (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
              (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
              (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s) : ℚ) : ℂ) =
            (c idx : ℂ) *
              ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval (s : ℂ) *
              (∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))) *
              (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) := by
          rw [heval_C]
          push_cast
          rfl
        rw [hcast_term, ← mul_sub]
        have hexp_split :
            Complex.exp ((s : ℂ) * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ)) =
            (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) *
              Complex.exp (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ)) := by
          have hsum_real :
              (s : ℝ) * (∑ r : Fin m, (gammaRat b idx r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) =
              (∑ i : Fin (m + 1), ((s : ℝ) * ((idx.2 i).val : ℝ) * Real.log (p i : ℝ))) +
                (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ')) := by
            have h1 : ∑ r : Fin m, (gammaRat b idx r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ) =
                (∑ r : Fin m, ((idx.2 (Fin.castSucc r)).val : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) +
                ((idx.2 (Fin.last m)).val : ℝ) * (Real.log (p (Fin.last m) : ℝ) - Λ') := by
              rw [← hlin, Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro r _; unfold gammaRat; push_cast; ring
            rw [h1, Fin.sum_univ_castSucc, mul_add, Finset.mul_sum]
            have h2 : ∑ r : Fin m, (s : ℝ) * (((idx.2 (Fin.castSucc r)).val : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) =
                ∑ r : Fin m, (s : ℝ) * ((idx.2 (Fin.castSucc r)).val : ℝ) * Real.log (p (Fin.castSucc r) : ℝ) :=
              Finset.sum_congr rfl fun r _ => by ring
            rw [h2]; ring
          have hsum_C :
              (s : ℂ) * ∑ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) * (Real.log (p (Fin.castSucc r) : ℝ) : ℂ) =
              ((∑ i : Fin (m + 1), ((s : ℝ) * ((idx.2 i).val : ℝ) * Real.log (p i : ℝ)) : ℝ) : ℂ) +
                ((-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ') : ℝ) : ℂ) := by
            have hcast1 : ((s : ℝ) * (∑ r : Fin m, (gammaRat b idx r : ℝ) * Real.log (p (Fin.castSucc r) : ℝ)) : ℝ) =
                (∑ i : Fin (m + 1), ((s : ℝ) * ((idx.2 i).val : ℝ) * Real.log (p i : ℝ))) +
                  (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ')) := hsum_real
            have hcastC := congr_arg (Complex.ofReal) hcast1
            simpa [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_neg,
              Complex.ofReal_natCast, Complex.ofReal_ratCast] using hcastC
          rw [hsum_C, Complex.exp_add]
          congr 1
          · rw [Complex.ofReal_sum, Complex.exp_sum]
            apply Finset.prod_congr rfl
            intro i _
            have hpi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast (hp i).pos
            have hreal_pow : Real.exp ((s : ℝ) * ((idx.2 i).val : ℝ) * Real.log (p i : ℝ)) =
                ((p i : ℝ) ^ (idx.2 i).val) ^ s := by
              rw [← pow_mul, mul_comm (idx.2 i).val s, ← Nat.cast_mul,
                Real.exp_nat_mul, Real.exp_log hpi]
            have hC := congr_arg Complex.ofReal hreal_pow
            simpa [Complex.ofReal_exp] using hC
          · rw [Complex.ofReal_neg]
        rw [hexp_split, show (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) *
              Complex.exp (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ)) -
              (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) =
            (∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s) *
              (Complex.exp (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ)) - 1) by ring]
        rw [norm_mul, norm_mul, norm_mul, norm_mul]
        have h1 : ‖(c idx : ℂ)‖ ≤ Cmax := by rw [Complex.norm_intCast]; exact hCmax idx
        have h2 : ‖((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).map (algebraMap ℚ ℂ)).eval (s : ℂ)‖ ≤
            (Real.exp 1 * ((s : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) :=
          norm_eval_hasseDeriv_feldmanPoly_le hk (Nat.lt_succ_iff.mp idx.1.isLt) (s : ℂ)
            (by rw [Complex.norm_natCast])
        have h3 : ‖∏ r : Fin m, ((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))‖ ≤
            (2 * (L : ℝ) + 1) ^ T₀ := by
          rw [norm_prod]
          calc ∏ r : Fin m, ‖((gammaRat b idx r : ℚ) : ℂ) ^ (t (Fin.succ r))‖
              ≤ ∏ r : Fin m, (2 * (L : ℝ) + 1) ^ (t (Fin.succ r)) := by
                apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                intro r _
                rw [norm_pow, Complex.norm_ratCast]
                apply pow_le_pow_left₀ (abs_nonneg _)
                linarith [abs_gammaRat_le hbn hble idx r]
            _ = (2 * (L : ℝ) + 1) ^ (∑ r : Fin m, t (Fin.succ r)) := by
                rw [Finset.prod_pow_eq_pow_sum]
            _ ≤ (2 * (L : ℝ) + 1) ^ T₀ := by
                apply pow_le_pow_right₀ (by have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L; linarith)
                have hsum_split : ∑ i : Fin (m + 1), t i = t 0 + ∑ r : Fin m, t (Fin.succ r) :=
                  Fin.sum_univ_succ t
                omega
        have h4 : ‖∏ i : Fin (m + 1), ((p i : ℂ) ^ (idx.2 i).val) ^ s‖ ≤
            Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (s : ℝ)) := by
          rw [norm_prod, Finset.mul_sum, Finset.sum_mul, Real.exp_sum]
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro i _
          have hpi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast (hp i).pos
          have hlog0 : 0 ≤ Real.log (p i : ℝ) := Real.log_nonneg (by exact_mod_cast (hp i).one_lt.le)
          have hli : ((idx.2 i).val : ℝ) ≤ (L : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (idx.2 i).isLt
          rw [norm_pow, norm_pow, Complex.norm_natCast]
          calc ((p i : ℝ) ^ (idx.2 i).val) ^ s
              = Real.exp (((idx.2 i).val : ℝ) * Real.log (p i : ℝ) * (s : ℝ)) := by
                rw [← pow_mul, mul_comm (idx.2 i).val s, mul_comm _ (s : ℝ), ← mul_assoc,
                  ← Nat.cast_mul, Real.exp_nat_mul, Real.exp_log hpi]
            _ ≤ Real.exp ((L : ℝ) * Real.log (p i : ℝ) * (s : ℝ)) := by
                apply Real.exp_le_exp.mpr
                exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hli hlog0) (Nat.cast_nonneg _)
        have h5 : ‖Complex.exp (-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ)) - 1‖ ≤
            2 * (s : ℝ) * (L : ℝ) * |Λ'| := by
          have hln : ((idx.2 (Fin.last m)).val : ℝ) ≤ (L : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (idx.2 (Fin.last m)).isLt
          have hnorm_arg : ‖(-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ) : ℂ)‖ ≤
              (s : ℝ) * (L : ℝ) * |Λ'| := by
            rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
              abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hln (Nat.cast_nonneg _)) (abs_nonneg _)
          have hle1 : ‖(-((s : ℝ) * ((idx.2 (Fin.last m)).val : ℝ) * Λ' : ℝ) : ℂ)‖ ≤ 1 := by
            refine le_trans hnorm_arg ?_
            rw [hΛ'abs]; exact hsmall
          have hexp_err := Complex.norm_exp_sub_one_le hle1
          have h2mul := mul_le_mul_of_nonneg_left hnorm_arg (by norm_num : (0 : ℝ) ≤ 2)
          linarith
        have ha := mul_le_mul h1 h2 (norm_nonneg _) hC0
        have hb := mul_le_mul ha h3 (norm_nonneg _) (by positivity)
        have hc := mul_le_mul hb h4 (norm_nonneg _) (by positivity)
        have hd := mul_le_mul hc h5 (norm_nonneg _) (by positivity)
        linarith
    _ = 2 * (s : ℝ) * (L : ℝ) * (|Λ| / (b (Fin.last m) : ℝ)) *
        (Fintype.card (Idx L₀ L m) : ℝ) * Cmax *
        ((Real.exp 1 * ((s : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)) *
        ((2 * (L : ℝ) + 1) ^ T₀) *
        Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (s : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hΛ'abs]; ring

lemma prime_pow_prod_injective {n L : ℕ} {p : Fin n → ℕ} (hp_pr : ∀ i, (p i).Prime)
    (hp_inj : Function.Injective p) :
    Function.Injective (fun μ : Fin n → Fin (L + 1) => ∏ i : Fin n, p i ^ (μ i).val) := by
  intro μ₁ μ₂ heq
  funext i
  ext
  have h1 := congr_arg (fun x => x.factorization (p i)) heq
  have hfac : ∀ μ : Fin n → Fin (L + 1),
      (∏ j : Fin n, p j ^ (μ j).val).factorization (p i) = (μ i).val := by
    intro μ
    rw [Nat.factorization_prod (fun j _ => pow_ne_zero _ (hp_pr j).ne_zero), Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single i]
    · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        (hp_pr i).factorization_self, mul_one]
    · intro j _ hji
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
      have hne : p i ≠ p j := fun h => hji (hp_inj h).symm
      rw [(hp_pr j).factorization, Finsupp.single_eq_of_ne hne, mul_zero]
    · intro hnot; exact False.elim (hnot (Finset.mem_univ i))
  rw [hfac μ₁, hfac μ₂] at h1
  exact h1

/- Section 7: Core Baker–Feldman Lower Bound for Fixed Ordered Primes -/

lemma real_log_thirty_one_div_two_ge_two : (2 : ℝ) ≤ Real.log (31 / 2 : ℝ) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have hexp1 : Real.exp 1 < 2.72 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  rw [hexp2]
  nlinarith

lemma real_log_le_self_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx
  linarith

lemma real_log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  have hlog : Real.log x = Real.log (Real.sqrt x ^ 2) := by rw [hsq]
  rw [hlog, Real.log_pow]
  push_cast
  linarith [real_log_le_self_of_pos hs_pos]

/- Modular helpers for `baker_feldman_core` -/

lemma baker_matrix_entry_bound {m L₀ L k T₀ c_h c₀ : ℕ}
    (hk_pos : 0 < k) (hL₀_eq : L₀ = c₀ * k)
    (p : Fin (m + 1) → ℕ) (hp_pr : ∀ i, (p i).Prime)
    {b : Fin (m + 1) → ℤ} (hbn_pos : 0 < b (Fin.last m)) (hb_le : ∀ i, |b i| ≤ b (Fin.last m))
    {α : ℝ} (hα_ge : ∑ i : Fin (m + 1), Real.log (p i : ℝ) ≤ α)
    (hlog2L : Real.log (2 * (L : ℝ) + 1) + 1 ≤ (0.5 : ℝ) * (k : ℝ))
    (hD_lt_k1 : Real.log (b (Fin.last m) : ℝ) < (k : ℝ) + 1)
    {s : ℕ} (hs_le : s ≤ c_h * k)
    {t : Fin (m + 1) → ℕ} (ht_sum : ∑ i : Fin (m + 1), t i ≤ T₀)
    (idx : Idx L₀ L m) (z : ℤ)
    (hz : (z : ℚ) =
      ((Nat.lcmUpto k : ℚ) ^ (t 0)) *
      ((b (Fin.last m) : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
      ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
        (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
        (∏ i : Fin (m + 1), ((p i : ℚ) ^ (idx.2 i).val) ^ s))) :
    |(z : ℝ)| ≤ Real.exp ((7.5 * (T₀ : ℝ) +
      ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) +
      α * (L : ℝ) * (c_h : ℝ)) * (k : ℝ)) := by
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hbnR_pos : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn_pos
  have hbnR_ge1 : (1 : ℝ) ≤ (b (Fin.last m) : ℝ) := by exact_mod_cast hbn_pos
  have hcast := congr_arg (Rat.cast (K := ℝ)) hz
  simp only [Rat.cast_intCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_prod] at hcast
  rw [hcast, abs_mul, abs_mul, abs_mul, abs_mul]
  have ht_split : t 0 + ∑ r : Fin m, t (Fin.succ r) ≤ T₀ := by
    rwa [Fin.sum_univ_succ] at ht_sum
  have ht0_le : t 0 ≤ T₀ := by omega
  have htr_le : ∑ r : Fin m, t (Fin.succ r) ≤ T₀ := by omega
  have hb1 : |((Nat.lcmUpto k : ℝ) ^ (t 0))| ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) := by
    rw [abs_of_nonneg (by positivity)]
    calc (Nat.lcmUpto k : ℝ) ^ (t 0)
        ≤ (Real.exp (6 * (k : ℝ))) ^ (t 0) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (lcmUpto_le_exp k) _
      _ = Real.exp ((t 0 : ℝ) * (6 * (k : ℝ))) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have : (t 0 : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast ht0_le
          nlinarith
  have hb2 : |Rat.cast ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ))| ≤
      Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) * (k : ℝ)) := by
    set P := Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)
    have heval_C : (P.map (algebraMap ℚ ℂ)).eval (s : ℂ) = ((P.eval (s : ℚ) : ℚ) : ℂ) := by
      rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, Rat.cast_sum]
      have hdeg : (P.map (algebraMap ℚ ℂ)).natDegree = P.natDegree :=
        Polynomial.natDegree_map_eq_of_injective Rat.cast_injective P
      rw [hdeg]
      apply Finset.sum_congr rfl; intro j _
      rw [Polynomial.coeff_map, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]; rfl
    have hnorm_eq : |Rat.cast (P.eval (s : ℚ))| = ‖(P.map (algebraMap ℚ ℂ)).eval (s : ℂ)‖ := by
      rw [heval_C, Complex.norm_ratCast]
    rw [hnorm_eq]
    have hsR : ‖(s : ℂ)‖ ≤ ((c_h * k : ℕ) : ℝ) := by
      rw [Complex.norm_natCast]; exact_mod_cast hs_le
    refine le_trans (norm_eval_hasseDeriv_feldmanPoly_le hk_pos (Nat.lt_succ_iff.mp idx.1.isLt) _ hsR) ?_
    have hbase_le : Real.exp 1 * (((c_h * k : ℕ) : ℝ) + 1 + (k : ℝ)) / (k : ℝ) ≤
        Real.exp 1 * ((c_h : ℝ) + 2) := by
      rw [div_le_iff₀ hkR_pos]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
      have he0 : 0 < Real.exp 1 := Real.exp_pos 1
      push_cast; nlinarith
    have hpos_b : 0 < Real.exp 1 * ((c_h : ℝ) + 2) := by positivity
    calc (Real.exp 1 * (((c_h * k : ℕ) : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)
        ≤ (Real.exp 1 * ((c_h : ℝ) + 2)) ^ (L₀ + k) :=
          pow_le_pow_left₀ (by positivity) hbase_le _
      _ = Real.exp (((L₀ + k : ℕ) : ℝ) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2))) := by
          rw [Real.exp_nat_mul, Real.exp_log hpos_b]
      _ = Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) * (k : ℝ)) := by
          rw [hL₀_eq]; push_cast; ring_nf
  have hb3 : |((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)))| *
      |∏ r : Fin m, ((gammaRat b idx r : ℝ) ^ (t (Fin.succ r)))| ≤
      Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
    rw [← abs_mul, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, Finset.abs_prod]
    calc ∏ r : Fin m, |(b (Fin.last m) : ℝ) ^ (t (Fin.succ r)) *
            (gammaRat b idx r : ℝ) ^ (t (Fin.succ r))|
        ≤ ∏ r : Fin m, (2 * (b (Fin.last m) : ℝ) * (L : ℝ) + 1) ^ (t (Fin.succ r)) := by
          apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          intro r _
          rw [← mul_pow, abs_pow, abs_mul, abs_of_pos hbnR_pos]
          apply pow_le_pow_left₀ (by positivity)
          have := abs_gammaRat_le hbn_pos hb_le idx r
          nlinarith
      _ = (2 * (b (Fin.last m) : ℝ) * (L : ℝ) + 1) ^ (∑ r : Fin m, t (Fin.succ r)) :=
          Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ (2 * (b (Fin.last m) : ℝ) * (L : ℝ) + 1) ^ T₀ := by
          apply pow_le_pow_right₀ _ htr_le
          have : 0 ≤ 2 * (b (Fin.last m) : ℝ) * (L : ℝ) := by positivity
          linarith
      _ ≤ ((b (Fin.last m) : ℝ) * (2 * (L : ℝ) + 1)) ^ T₀ := by
          apply pow_le_pow_left₀ (by positivity); nlinarith
      _ = Real.exp ((T₀ : ℝ) * (Real.log (b (Fin.last m) : ℝ) + Real.log (2 * (L : ℝ) + 1))) := by
          rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log hbnR_pos,
            Real.exp_log (by positivity : (0 : ℝ) < 2 * (L : ℝ) + 1)]
      _ ≤ Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hsum : Real.log (b (Fin.last m) : ℝ) + Real.log (2 * (L : ℝ) + 1) ≤ (1.5 : ℝ) * (k : ℝ) := by
            linarith
          have := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg T₀)
          linarith
  have hb4 : |∏ i : Fin (m + 1), (((p i : ℝ) ^ (idx.2 i).val) ^ s)| ≤
      Real.exp (α * (L : ℝ) * (c_h : ℝ) * (k : ℝ)) := by
    rw [abs_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
    have hs_leR : (s : ℝ) ≤ (c_h : ℝ) * (k : ℝ) := by exact_mod_cast hs_le
    calc ∏ i : Fin (m + 1), (((p i : ℝ) ^ (idx.2 i).val) ^ s)
        ≤ ∏ i : Fin (m + 1), Real.exp ((L : ℝ) * Real.log (p i : ℝ) * ((c_h : ℝ) * (k : ℝ))) := by
          apply Finset.prod_le_prod (fun _ _ => by positivity)
          intro i _
          have hpi : (0 : ℝ) < (p i : ℝ) := by exact_mod_cast (hp_pr i).pos
          have hlog0 : 0 ≤ Real.log (p i : ℝ) := Real.log_nonneg (by exact_mod_cast (hp_pr i).one_lt.le)
          have hli : ((idx.2 i).val : ℝ) ≤ (L : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (idx.2 i).isLt
          rw [← pow_mul, ← Real.exp_log (pow_pos hpi _), Real.log_pow, Nat.cast_mul]
          apply Real.exp_le_exp.mpr
          have h1 : ((idx.2 i).val : ℝ) * (s : ℝ) ≤ (L : ℝ) * ((c_h : ℝ) * (k : ℝ)) :=
            mul_le_mul hli hs_leR (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          have h2 := mul_le_mul_of_nonneg_right h1 hlog0
          linarith
      _ = Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * ((c_h : ℝ) * (k : ℝ))) := by
          rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_mul]
      _ ≤ Real.exp (α * (L : ℝ) * (c_h : ℝ) * (k : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have hnn : 0 ≤ (L : ℝ) * ((c_h : ℝ) * (k : ℝ)) := by positivity
          nlinarith
  have hrearr :
      |((Nat.lcmUpto k : ℝ) ^ (t 0))| *
        |((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)))| *
        (|Rat.cast ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ))| *
          |∏ r : Fin m, ((gammaRat b idx r : ℝ) ^ (t (Fin.succ r)))| *
          |∏ i : Fin (m + 1), (((p i : ℝ) ^ (idx.2 i).val) ^ s)|) =
      |((Nat.lcmUpto k : ℝ) ^ (t 0))| *
        (|((b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)))| *
          |∏ r : Fin m, ((gammaRat b idx r : ℝ) ^ (t (Fin.succ r)))|) *
        |Rat.cast ((Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ))| *
        |∏ i : Fin (m + 1), (((p i : ℝ) ^ (idx.2 i).val) ^ s)| := by ring
  rw [hrearr]
  have h13 := mul_le_mul hb1 hb3 (by positivity) (by positivity)
  have h132 := mul_le_mul h13 hb2 (abs_nonneg _) (by positivity)
  have h1324 := mul_le_mul h132 hb4 (abs_nonneg _) (by positivity)
  refine le_trans h1324 ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  ring_nf; linarith

set_option maxHeartbeats 800000 in
lemma baker_extrap_step {m L₀ L k K S T₀ c_h c₀ j : ℕ}
    (hk_pos : 0 < k) (hL1 : 1 ≤ L) (hS1 : 1 ≤ S) (hc_h1 : 1 ≤ c_h) (hjK : j + 1 ≤ K)
    (hL₀_eq : L₀ = c₀ * k) (hT₀_eq : T₀ = K * S) (hc_h_eq : c_h = 32 * K)
    (p : Fin (m + 1) → ℕ) (hp_pr : ∀ i, (p i).Prime)
    {b : Fin (m + 1) → ℤ} (hbn_pos : 0 < b (Fin.last m)) (hb_le : ∀ i, |b i| ≤ b (Fin.last m))
    (hD_le_15k : Real.log (b (Fin.last m) : ℝ) ≤ (1.5 : ℝ) * (k : ℝ))
    {α M₀ C_tot Cmax : ℝ} (hα_ge1 : 1 ≤ α)
    (hα_sum : ∑ i : Fin (m + 1), Real.log (p i : ℝ) ≤ α)
    (hαm_le : ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) ≤ α)
    (h65α : 65 * α * (L : ℝ) ≤ (0.55 : ℝ) * (S : ℝ))
    (hM₀_eq : M₀ = 7.5 * (T₀ : ℝ) + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) +
        α * (L : ℝ) * (c_h : ℝ))
    (hC_tot_eq : C_tot = M₀ + 10 * (T₀ : ℝ) +
        2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
        α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ) + 3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) + 20)
    (hCtot_pos : 0 < C_tot)
    (hpoly_S_dom :
      2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) + 10 * (c_h : ℝ) ≤
        (0.8 : ℝ) * (c_h : ℝ) * (S : ℝ))
    (hT0log2L : (T₀ : ℝ) * Real.log (2 * (L : ℝ) + 1) ≤ (0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ))
    (hlogErr :
      Real.log (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
        ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
        (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ))) ≤ 2 * (k : ℝ))
    (hΛ'_lt : |∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| / (b (Fin.last m) : ℝ) <
        Real.exp (-(C_tot + 2) * (k : ℝ)))
    (c : Idx L₀ L m → ℤ) (hCmax_nn : 0 ≤ Cmax) (hc_abs : ∀ idx, |(c idx : ℝ)| ≤ Cmax)
    (hUCmax : (Fintype.card (Idx L₀ L m) : ℝ) * Cmax ≤ Real.exp ((M₀ + 1) * (k : ℝ)))
    (hIH : ∀ s ∈ Finset.Icc 1 (2 ^ j * (c_h * k)), ∀ t : Fin (m + 1) → ℕ,
        (∑ i, t i) ≤ (K - j) * S → Psi k p b c t s = 0) :
    ∀ s ∈ Finset.Icc 1 (2 ^ (j + 1) * (c_h * k)), ∀ t : Fin (m + 1) → ℕ,
      (∑ i, t i) ≤ (K - (j + 1)) * S → Psi k p b c t s = 0 := by
  intro s hs t ht
  have hj_le : j ≤ K := by omega
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hLR_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
  have hbnR_pos : (0 : ℝ) < (b (Fin.last m) : ℝ) := by exact_mod_cast hbn_pos
  set h₀ : ℕ := c_h * k
  have hh₀1 : 1 ≤ h₀ := Nat.mul_pos hc_h1 hk_pos
  set hj : ℕ := 2 ^ j * h₀
  have hhj1 : 1 ≤ hj := Nat.mul_pos (Nat.one_le_pow j 2 (by norm_num)) hh₀1
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  have hs_hi : s ≤ 2 * hj := by
    have hmem : s ≤ 2 ^ (j + 1) * (c_h * k) := (Finset.mem_Icc.mp hs).2
    have hmul : 2 ^ (j + 1) * (c_h * k) = 2 * hj := by
      dsimp only [hj, h₀]; rw [pow_succ']; ring
    exact hmul ▸ hmem
  by_cases hle_hj : s ≤ hj
  · exact hIH s (Finset.mem_Icc.mpr ⟨hs1, hle_hj⟩) t
      (le_trans ht (Nat.mul_le_mul_right S (by omega)))
  · have hs_lo : hj < s := by omega
    by_contra hPsi_ne
    have ht_le_T0 : ∑ i, t i ≤ T₀ := by
      rw [hT₀_eq]; exact le_trans ht (Nat.mul_le_mul_right S (Nat.sub_le K (j + 1)))
    set Λ'abs : ℝ := |∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| / (b (Fin.last m) : ℝ)
    have hΛ'abs_nn : 0 ≤ Λ'abs := div_nonneg (abs_nonneg _) hbnR_pos.le
    -- 1. Liouville lower bound
    have hliouv : Real.exp (-(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) ≤ |(Psi k p b c t s : ℝ)| := by
      refine le_trans ?_ (Psi_lower_of_ne_zero hk_pos p hbn_pos c t s hPsi_ne)
      rw [show -(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ) = -((7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) by ring, Real.exp_neg]
      have hlcm_pos : (0 : ℝ) < (Nat.lcmUpto k : ℝ) := by exact_mod_cast Nat.lcmUpto_pos k
      apply inv_anti₀ (by positivity)
      have ht0_le : t 0 ≤ T₀ := le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)) ht_le_T0
      have htr_le : ∑ r : Fin m, t (Fin.succ r) ≤ T₀ := by
        have := Fin.sum_univ_succ t; omega
      have h1 : (Nat.lcmUpto k : ℝ) ^ (t 0) ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) := by
        calc (Nat.lcmUpto k : ℝ) ^ (t 0)
            ≤ (Real.exp (6 * (k : ℝ))) ^ (t 0) :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) (lcmUpto_le_exp k) _
          _ = Real.exp ((t 0 : ℝ) * (6 * (k : ℝ))) := by rw [← Real.exp_nat_mul]
          _ ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have hle : (t 0 : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast ht0_le
              nlinarith only [hle, hkR_pos]
      have h2 : (b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r)) ≤
          Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
        calc (b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r))
            = Real.exp (((∑ r : Fin m, t (Fin.succ r) : ℕ) : ℝ) * Real.log (b (Fin.last m) : ℝ)) := by
              rw [Real.exp_nat_mul, Real.exp_log hbnR_pos]
          _ ≤ Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
              apply Real.exp_le_exp.mpr
              have htrR : ((∑ r : Fin m, t (Fin.succ r) : ℕ) : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast htr_le
              have hD0 : 0 ≤ Real.log (b (Fin.last m) : ℝ) :=
                Real.log_nonneg (by exact_mod_cast hbn_pos)
              have hT0nn : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
              nlinarith only [htrR, hD0, hD_le_15k, hT0nn, hkR_pos]
      calc (Nat.lcmUpto k : ℝ) ^ (t 0) * (b (Fin.last m) : ℝ) ^ (∑ r : Fin m, t (Fin.succ r))
          ≤ Real.exp (6 * (T₀ : ℝ) * (k : ℝ)) * Real.exp ((1.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = Real.exp ((7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
            rw [← Real.exp_add]; congr 1; ring
    -- 2. Smallness check at any l ≤ 2^K * h₀
    have hsmall_any : ∀ l : ℕ, l ≤ 2 ^ K * h₀ → (l : ℝ) * (L : ℝ) * Λ'abs ≤ 1 := by
      intro l hl
      have hlR : (l : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by
        have : l ≤ 2 ^ K * (c_h * k) := hl
        simpa [mul_assoc] using (show (l : ℝ) ≤ ((2 ^ K * (c_h * k) : ℕ) : ℝ) by exact_mod_cast this)
      have hlog_lL : Real.log ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) ≤ 2 * (k : ℝ) := by
        refine le_trans ?_ hlogErr
        apply Real.log_le_log (by positivity)
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by
          have ha : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
          have hb : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
          have hc : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
          exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) hc
        have h2 : (1 : ℝ) ≤ (2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S := by
          apply one_le_pow₀
          have hsq : (1 : ℝ) ≤ ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2 := one_le_pow₀ h1
          linarith
        have h3 : (1 : ℝ) ≤ ((T₀ : ℝ) + α + 1) ^ S := by
          apply one_le_pow₀
          have : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
          linarith
        have h4 : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
        have hge1 : (1 : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
            ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
            (((T₀ : ℝ) + α + 1) ^ S) * 2 := by
          have ha : (1 : ℝ) ≤ 32 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) := by linarith
          have hb : (1 : ℝ) ≤ 32 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) * (S : ℝ) :=
            one_le_mul_of_one_le_of_one_le ha h4
          have hc : (1 : ℝ) ≤ 32 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) * (S : ℝ) *
              ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) :=
            one_le_mul_of_one_le_of_one_le hb h2
          have hd : (1 : ℝ) ≤ 32 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) * (S : ℝ) *
              ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) :=
            one_le_mul_of_one_le_of_one_le hc h3
          linarith
        have hnn : 0 ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ) := by positivity
        calc (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)
            = 1 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) := (one_mul _).symm
          _ ≤ (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
                ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
                (((T₀ : ℝ) + α + 1) ^ S) * 2) *
              ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) :=
              mul_le_mul_of_nonneg_right hge1 hnn
          _ = _ := by ring
      have hlL_exp : (l : ℝ) * (L : ℝ) ≤ Real.exp (2 * (k : ℝ)) := by
        calc (l : ℝ) * (L : ℝ)
            ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ) :=
              mul_le_mul_of_nonneg_right hlR (Nat.cast_nonneg L)
          _ ≤ Real.exp (2 * (k : ℝ)) := by
              rw [← Real.log_le_iff_le_exp (by positivity)]; exact hlog_lL
      calc (l : ℝ) * (L : ℝ) * Λ'abs
          ≤ Real.exp (2 * (k : ℝ)) * Real.exp (-(C_tot + 2) * (k : ℝ)) :=
            mul_le_mul hlL_exp hΛ'_lt.le hΛ'abs_nn (by positivity)
        _ = Real.exp (-C_tot * (k : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith only [hCtot_pos, hkR_pos])
        _ = 1 := Real.exp_zero
    -- 3. Common upper bound on `‖G u l - Psi u l‖`
    set E_diff : ℝ :=
      2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ) * Λ'abs *
      Real.exp ((M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
        (0.5 : ℝ) * (T₀ : ℝ) + α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ)) * (k : ℝ))
    have hdiff_bound : ∀ l : ℕ, l ≤ 2 ^ K * h₀ → ∀ u : Fin (m + 1) → ℕ, (∑ i, u i) ≤ T₀ →
        ‖G k p b c u (l : ℂ) - ((Psi k p b c u l : ℚ) : ℂ)‖ ≤ E_diff := by
      intro l hl u hu
      refine le_trans (norm_G_sub_Psi_le hk_pos p hp_pr hbn_pos hb_le c hc_abs hCmax_nn hu l (hsmall_any l hl)) ?_
      have hlR : (l : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by
        have : l ≤ 2 ^ K * (c_h * k) := hl
        simpa [mul_assoc] using (show (l : ℝ) ≤ ((2 ^ K * (c_h * k) : ℕ) : ℝ) by exact_mod_cast this)
      have hP_le : (Real.exp 1 * ((l : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) ≤
          Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) * (k : ℝ)) := by
        have hbase : Real.exp 1 * ((l : ℝ) + 1 + (k : ℝ)) / (k : ℝ) ≤
            Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2) := by
          rw [div_le_iff₀ hkR_pos]
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
          have he0 : 0 < Real.exp 1 := Real.exp_pos 1
          have h2Kc : 0 ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by positivity
          nlinarith only [hlR, hk1, he0, h2Kc]
        calc (Real.exp 1 * ((l : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)
            ≤ (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) ^ (L₀ + k) :=
              pow_le_pow_left₀ (by positivity) hbase _
          _ = Real.exp (((L₀ + k : ℕ) : ℝ) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2))) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
          _ = Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) * (k : ℝ)) := by
              rw [hL₀_eq]; push_cast; ring_nf
      have h2L_le : (2 * (L : ℝ) + 1) ^ T₀ ≤ Real.exp ((0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 * (L : ℝ) + 1) ^ T₀), Real.log_pow]
        exact Real.exp_le_exp.mpr hT0log2L
      have hexp_le : Real.exp ((L : ℝ) * (∑ i : Fin (m + 1), Real.log (p i : ℝ)) * (l : ℝ)) ≤
          Real.exp (α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hsum_nn : 0 ≤ ∑ i : Fin (m + 1), Real.log (p i : ℝ) :=
          Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast (hp_pr i).one_lt.le)
        have h1 := mul_le_mul hα_sum hlR (Nat.cast_nonneg l) (by linarith)
        have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg L)
        linarith
      have hfront : 2 * (l : ℝ) * (L : ℝ) * Λ'abs ≤ 2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ) * Λ'abs := by
        have hnn : 0 ≤ 2 * (L : ℝ) * Λ'abs := by positivity
        nlinarith only [hlR, hnn]
      have hprod1 := mul_le_mul hUCmax hP_le (by positivity) (by positivity)
      have hprod2 := mul_le_mul hprod1 h2L_le (by positivity) (by positivity)
      have hprod3 := mul_le_mul hprod2 hexp_le (by positivity) (by positivity)
      have hprod4 := mul_le_mul hfront hprod3 (by positivity) (by positivity)
      refine le_trans ?_ (le_trans hprod4 ?_)
      · apply le_of_eq; ring
      · apply le_of_eq
        dsimp only [E_diff]
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; congr 1; ring
    -- 4. Circle bound Mf on ‖w‖ = 32 * hj
    set Mf : ℝ := Real.exp ((M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
        (0.5 : ℝ) * (T₀ : ℝ) + 64 * α * (L : ℝ) * (2 : ℝ) ^ j * (c_h : ℝ)) * (k : ℝ))
    have hcircle : ∀ w : ℂ, ‖w‖ = 32 * (hj : ℝ) → ‖G k p b c t w‖ ≤ Mf := by
      intro w hw
      refine le_trans (norm_G_le hk_pos p hp_pr hbn_pos hb_le c hc_abs hCmax_nn ht_le_T0 hw.le) ?_
      have h2j_le : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hj_le
      have hP_le : (Real.exp 1 * (32 * (hj : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k) ≤
          Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) * (k : ℝ)) := by
        have hbase : Real.exp 1 * (32 * (hj : ℝ) + 1 + (k : ℝ)) / (k : ℝ) ≤
            Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2) := by
          rw [div_le_iff₀ hkR_pos]
          have hhj_eq : (hj : ℝ) = (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ) := by
            dsimp only [hj, h₀]; push_cast; ring
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
          have he0 : 0 < Real.exp 1 := Real.exp_pos 1
          have hck : 0 ≤ (c_h : ℝ) * (k : ℝ) := by positivity
          have h2j_mul : (2 : ℝ) ^ j * ((c_h : ℝ) * (k : ℝ)) ≤ (2 : ℝ) ^ K * ((c_h : ℝ) * (k : ℝ)) :=
            mul_le_mul_of_nonneg_right h2j_le hck
          rw [hhj_eq]; nlinarith only [h2j_mul, hk1, he0]
        calc (Real.exp 1 * (32 * (hj : ℝ) + 1 + (k : ℝ)) / (k : ℝ)) ^ (L₀ + k)
            ≤ (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) ^ (L₀ + k) :=
              pow_le_pow_left₀ (by positivity) hbase _
          _ = Real.exp (((L₀ + k : ℕ) : ℝ) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2))) := by
              rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
          _ = Real.exp (((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) * (k : ℝ)) := by
              rw [hL₀_eq]; push_cast; ring_nf
      have h2L_le : (2 * (L : ℝ) + 1) ^ T₀ ≤ Real.exp ((0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (2 * (L : ℝ) + 1) ^ T₀), Real.log_pow]
        exact Real.exp_le_exp.mpr hT0log2L
      have hexp_le : Real.exp (2 * (L : ℝ) * (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) * (32 * (hj : ℝ))) ≤
          Real.exp (64 * α * (L : ℝ) * (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have hhj_eq : (hj : ℝ) = (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ) := by
          dsimp only [hj, h₀]; push_cast; ring
        rw [hhj_eq]
        have hnn : 0 ≤ 2 * (L : ℝ) * (32 * ((2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ))) := by positivity
        nlinarith only [hαm_le, hnn]
      have h1 := mul_le_mul hUCmax hP_le (by positivity) (by positivity)
      have h2 := mul_le_mul h1 h2L_le (by positivity) (by positivity)
      have h3 := mul_le_mul h2 hexp_le (by positivity) (by positivity)
      refine le_trans h3 (le_of_eq ?_)
      dsimp only [Mf]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    -- 5. Derivative bound eps at l ∈ Icc 1 hj and s' < S
    set eps : ℝ := (((T₀ : ℝ) + α + 1) ^ S) * E_diff
    have heps_nn : 0 ≤ eps := by positivity
    have hderiv : ∀ l ∈ Finset.Icc 1 hj, ∀ s' < S,
        ‖iteratedDeriv s' (G k p b c t) (l : ℂ) / (s'.factorial : ℂ)‖ ≤ eps := by
      intro l hl s' hs'
      have hl_hi : l ≤ 2 ^ K * h₀ :=
        le_trans (Finset.mem_Icc.mp hl).2 (Nat.mul_le_mul_right h₀ (Nat.pow_le_pow_right (by norm_num) hj_le))
      have hfac1 : (1 : ℝ) ≤ (s'.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos s'
      rw [norm_div, Complex.norm_natCast]
      refine le_trans (div_le_self (norm_nonneg _) hfac1) ?_
      have hG_at_l : ∀ u : Fin (m + 1) → ℕ, (∑ i, u i) = (∑ i, t i) + s' →
          ‖G k p b c u (l : ℂ)‖ ≤ E_diff := by
        intro u hu
        have hu_le : ∑ i, u i ≤ (K - j) * S := by
          have h1 : (K - (j + 1)) * S + S = (K - j) * S := by
            have : K - j = K - (j + 1) + 1 := by omega
            rw [this, Nat.add_mul, one_mul]
          omega
        have hPsi0 : Psi k p b c u l = 0 := hIH l hl u hu_le
        have hsub := hdiff_bound l hl_hi u (by rw [hT₀_eq]; exact le_trans hu_le (Nat.mul_le_mul_right S (Nat.sub_le K j)))
        rwa [hPsi0, Rat.cast_zero, sub_zero] at hsub
      refine le_trans (norm_iteratedDeriv_G_le k p hp_pr b c s' t (l : ℂ) (by positivity) hG_at_l) ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hbase1 : (((∑ i, t i) + s' + 1 : ℕ) : ℝ) + ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) ≤
          (T₀ : ℝ) + α + 1 := by
        have hts : ∑ i, t i + s' ≤ T₀ := by
          rw [hT₀_eq]
          have h1 : (K - (j + 1)) * S + S ≤ K * S := by
            have : K - (j + 1) + 1 ≤ K := by omega
            calc (K - (j + 1)) * S + S = (K - (j + 1) + 1) * S := by ring
              _ ≤ K * S := Nat.mul_le_mul_right S this
          omega
        have htsR : ((∑ i, t i + s' : ℕ) : ℝ) ≤ (T₀ : ℝ) := by exact_mod_cast hts
        push_cast at htsR ⊢; linarith
      have hge1 : (1 : ℝ) ≤ (T₀ : ℝ) + α + 1 := by
        have : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
        linarith
      calc ((((∑ i, t i) + s' + 1 : ℕ) : ℝ) + ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) ^ s'
          ≤ ((T₀ : ℝ) + α + 1) ^ s' := pow_le_pow_left₀ (by positivity) hbase1 s'
        _ ≤ ((T₀ : ℝ) + α + 1) ^ S := pow_le_pow_right₀ hge1 (le_of_lt hs')
    -- 6. Apply Hermite-Schwarz
    have hHS := hermite_schwarz_bound (G_differentiable k p b c t) hhj1 hS1 hs_lo hs_hi
      (by positivity) heps_nn hcircle hderiv
    -- 7. Compare all three terms to Liouville lower bound
    have hterm1_lt : ((2 / 31 : ℝ) ^ (hj * S)) * Mf < (1 / 2 : ℝ) * Real.exp (-(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
      have hpow_le : (2 / 31 : ℝ) ^ (hj * S) ≤ Real.exp (-2 * (hj : ℝ) * (S : ℝ)) := by
        have hpos : (0 : ℝ) < 2 / 31 := by norm_num
        rw [← Real.exp_log (pow_pos hpos _), Real.log_pow]
        apply Real.exp_le_exp.mpr
        have hlog : Real.log (2 / 31 : ℝ) ≤ -2 := by
          have hinv : Real.log (2 / 31 : ℝ) = -Real.log (31 / 2 : ℝ) := by
            rw [← Real.log_inv]; norm_num
          linarith [real_log_thirty_one_div_two_ge_two]
        have hnn : (0 : ℝ) ≤ ((hj * S : ℕ) : ℝ) := Nat.cast_nonneg _
        push_cast at hnn ⊢; nlinarith only [hlog, hnn]
      have h12 : (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      rw [h12, ← Real.exp_add]
      refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hpow_le (by positivity)) ?_
      dsimp only [Mf]
      rw [← Real.exp_add]
      apply Real.exp_lt_exp.mpr
      have h2j1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      have hhj_eq : (hj : ℝ) = (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ) := by
        dsimp only [hj, h₀]; push_cast; ring
      have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      have hlog_mono : Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) ≤
          Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) := by
        apply Real.log_le_log (by positivity)
        have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
        have he0 : 0 < Real.exp 1 := Real.exp_pos 1
        have hch0 : (0 : ℝ) ≤ (c_h : ℝ) := Nat.cast_nonneg _
        have h32 : (c_h : ℝ) + 2 ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by nlinarith only [h2K1, hch0]
        exact mul_le_mul_of_nonneg_left h32 he0.le
      have hT0R : (T₀ : ℝ) = (K : ℝ) * (S : ℝ) := by rw [hT₀_eq]; push_cast; rfl
      have hchR : (c_h : ℝ) = 32 * (K : ℝ) := by rw [hc_h_eq]; push_cast; rfl
      have h16T0 : (15.5 : ℝ) * (T₀ : ℝ) ≤ (0.5 : ℝ) * (c_h : ℝ) * (S : ℝ) := by
        rw [hT0R, hchR]
        have hKS : (0 : ℝ) ≤ (K : ℝ) * (S : ℝ) := by positivity
        linarith
      have hch1R : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
      have hS1R : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
      have hchS_nn : (0 : ℝ) ≤ (c_h : ℝ) * (S : ℝ) := by positivity
      have h2j_mul : (0.5 : ℝ) * (c_h : ℝ) * (S : ℝ) + (0.8 : ℝ) * (c_h : ℝ) * (S : ℝ) ≤
          (1.3 : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ) * (S : ℝ)) := by
        have := mul_le_mul_of_nonneg_right h2j1 hchS_nn
        linarith
      have h65_mul : α * (L : ℝ) * (c_h : ℝ) + 64 * α * (L : ℝ) * (2 : ℝ) ^ j * (c_h : ℝ) ≤
          65 * α * (L : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ)) := by
        have hnn : 0 ≤ α * (L : ℝ) * (c_h : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left h2j1 hnn
        linarith
      have h65_bnd : 65 * α * (L : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ)) ≤
          (0.55 : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ) * (S : ℝ)) := by
        have hnn : 0 ≤ (2 : ℝ) ^ j * (c_h : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_right h65α hnn
        linarith
      have hmain_per_k :
          M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
            (0.5 : ℝ) * (T₀ : ℝ) + 64 * α * (L : ℝ) * (2 : ℝ) ^ j * (c_h : ℝ) +
            (7.5 : ℝ) * (T₀ : ℝ) + 1 <
          2 * ((2 : ℝ) ^ j * (c_h : ℝ) * (S : ℝ)) := by
        rw [hM₀_eq]
        have h2c0 : ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) ≤
            ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hlog_mono (by positivity)
        have h015 : (0.15 : ℝ) * ((2 : ℝ) ^ j * (c_h : ℝ) * (S : ℝ)) > 0 := by positivity
        linarith
      rw [hhj_eq]
      have hmulk := mul_lt_mul_of_pos_right hmain_per_k hkR_pos
      linarith
    have hterm2_lt :
        4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (hj * S)) * eps <
          (1 / 4 : ℝ) * Real.exp (-(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
      have h2j_le : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hj_le
      have hhj_le : (hj : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by
        have : (hj : ℝ) = (2 : ℝ) ^ j * (c_h : ℝ) * (k : ℝ) := by dsimp only [hj, h₀]; push_cast; ring
        rw [this]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2j_le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
      have hpoly_part :
          4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) *
            (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) ≤
          (1 / 4 : ℝ) * Real.exp (2 * (k : ℝ)) := by
        have hle :
            16 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) *
              (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) ≤
            32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
              ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
              (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) := by
          have hsq : (hj : ℝ) ^ 2 ≤ ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hhj_le 2
          have hpow : (2 * (hj : ℝ) ^ 2) ^ S ≤ (2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S :=
            pow_le_pow_left₀ (by positivity) (by linarith) S
          have h16_32 : 16 * (hj : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) := by linarith
          have h1 := mul_le_mul_of_nonneg_right h16_32 (Nat.cast_nonneg S)
          have h2 := mul_le_mul h1 hpow (by positivity) (by positivity)
          have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ (((T₀ : ℝ) + α + 1) ^ S) *
              (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) by positivity)
          linarith
        have hexp := (Real.log_le_iff_le_exp (by positivity)).mp hlogErr
        linarith
      have h16_le : (16 : ℝ) ^ (hj * S) ≤ Real.exp (3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) * (k : ℝ)) := by
        rw [← Real.exp_log (by positivity : (0 : ℝ) < (16 : ℝ) ^ (hj * S)), Real.log_pow]
        apply Real.exp_le_exp.mpr
        have hlog16 : Real.log 16 ≤ 3 := by
          have h16 : (16 : ℝ) = 2 ^ 4 := by norm_num
          rw [h16, Real.log_pow]; push_cast
          linarith [Real.log_two_lt_d9]
        have hprod_le : ((hj * S : ℕ) : ℝ) ≤ (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) * (k : ℝ) := by
          push_cast
          have := mul_le_mul_of_nonneg_right hhj_le (Nat.cast_nonneg S)
          linarith
        have hnn : (0 : ℝ) ≤ ((hj * S : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith only [hlog16, hprod_le, hnn]
      have hrearr :
          4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (hj * S)) * eps =
          (4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) *
            (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ))) *
          ((16 : ℝ) ^ (hj * S)) * Λ'abs *
          Real.exp ((M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
            (0.5 : ℝ) * (T₀ : ℝ) + α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ)) * (k : ℝ)) := by
        dsimp only [eps, E_diff]; ring
      rw [hrearr]
      have h1 := mul_le_mul hpoly_part h16_le (by positivity) (by positivity)
      have h2 : (4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * (((T₀ : ℝ) + α + 1) ^ S) *
            (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ))) * ((16 : ℝ) ^ (hj * S)) * Λ'abs <
          ((1 / 4 : ℝ) * Real.exp (2 * (k : ℝ)) * Real.exp (3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) * (k : ℝ))) *
            Real.exp (-(C_tot + 2) * (k : ℝ)) := by
        have hpos_lhs : 0 < (1 / 4 : ℝ) * Real.exp (2 * (k : ℝ)) *
            Real.exp (3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) * (k : ℝ)) := by positivity
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 hΛ'abs_nn)
          (mul_lt_mul_of_pos_left hΛ'_lt hpos_lhs)
      refine lt_of_lt_of_le (mul_lt_mul_of_pos_right h2 (Real.exp_pos _)) ?_
      rw [mul_assoc, mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hlog0 : 0 ≤ Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) := by
        apply Real.log_nonneg
        have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
        have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
        have hch1 : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
        have h32 : (1 : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by
          have := one_le_mul_of_one_le_of_one_le h2K1 hch1; linarith
        exact one_le_mul_of_one_le_of_one_le he1 h32
      have hT0nn : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
      have hc0nn : (0 : ℝ) ≤ (c₀ : ℝ) + 1 := by positivity
      have hexp_per_k :
          2 + 3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) - (C_tot + 2) +
            (M₀ + 1 + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
              (0.5 : ℝ) * (T₀ : ℝ) + α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ)) ≤
          -(7.5 : ℝ) * (T₀ : ℝ) := by
        rw [hC_tot_eq]
        have hmul_log : 0 ≤ ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) :=
          mul_nonneg hc0nn hlog0
        linarith
      have hmulk := mul_le_mul_of_nonneg_right hexp_per_k hkR_pos.le
      linarith
    have hterm3_lt : ‖G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)‖ <
        (1 / 4 : ℝ) * Real.exp (-(7.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) := by
      have hs_le_max : s ≤ 2 ^ K * h₀ := by
        have h1 : 2 ^ (j + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hjK
        exact le_trans (Finset.mem_Icc.mp hs).2 (Nat.mul_le_mul_right h₀ h1)
      refine lt_of_le_of_lt (hdiff_bound s hs_le_max t ht_le_T0) ?_
      refine lt_of_le_of_lt ?_ hterm2_lt
      have hhjR : (1 : ℝ) ≤ (hj : ℝ) := by exact_mod_cast hhj1
      have hSR : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS1
      have h1 : (1 : ℝ) ≤ (2 * (hj : ℝ) ^ 2) ^ S := by
        apply one_le_pow₀
        have : (1 : ℝ) ≤ (hj : ℝ) ^ 2 := one_le_pow₀ hhjR
        linarith
      have h2 : (1 : ℝ) ≤ (16 : ℝ) ^ (hj * S) := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℝ) ≤ ((T₀ : ℝ) + α + 1) ^ S := by
        apply one_le_pow₀
        have : (0 : ℝ) ≤ (T₀ : ℝ) := Nat.cast_nonneg T₀
        linarith
      have hge1 : (1 : ℝ) ≤ 4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) *
          ((16 : ℝ) ^ (hj * S)) * (((T₀ : ℝ) + α + 1) ^ S) := by
        have ha : (1 : ℝ) ≤ 4 * (hj : ℝ) := by linarith
        have hb := one_le_mul_of_one_le_of_one_le ha hSR
        have hc := one_le_mul_of_one_le_of_one_le hb h1
        have hd := one_le_mul_of_one_le_of_one_le hc h2
        exact one_le_mul_of_one_le_of_one_le hd h3
      have hEd0 : 0 ≤ E_diff := by positivity
      calc E_diff = 1 * E_diff := (one_mul _).symm
        _ ≤ (4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) *
              ((16 : ℝ) ^ (hj * S)) * (((T₀ : ℝ) + α + 1) ^ S)) * E_diff :=
            mul_le_mul_of_nonneg_right hge1 hEd0
        _ = 4 * (hj : ℝ) * (S : ℝ) * ((2 * (hj : ℝ) ^ 2) ^ S) * ((16 : ℝ) ^ (hj * S)) * eps := by
            dsimp only [eps]; ring
    have hPsi_norm : |(Psi k p b c t s : ℝ)| = ‖((Psi k p b c t s : ℚ) : ℂ)‖ := by
      rw [Complex.norm_ratCast]
    have htri : ‖((Psi k p b c t s : ℚ) : ℂ)‖ ≤
        ‖G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)‖ + ‖G k p b c t (s : ℂ)‖ := by
      have heq : ((Psi k p b c t s : ℚ) : ℂ) =
          G k p b c t (s : ℂ) - (G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)) := by ring
      calc ‖((Psi k p b c t s : ℚ) : ℂ)‖
          = ‖G k p b c t (s : ℂ) - (G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ))‖ := by
              congr 1
        _ ≤ ‖G k p b c t (s : ℂ)‖ + ‖G k p b c t (s : ℂ) - ((Psi k p b c t s : ℚ) : ℂ)‖ :=
            norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith

set_option maxHeartbeats 800000 in
theorem baker_feldman_core {m : ℕ} (hm : 1 ≤ m)
    (p : Fin (m + 1) → ℕ) (hp_pr : ∀ i, (p i).Prime) (hp_inj : Function.Injective p) :
    ∃ C B₀ : ℝ, 0 < C ∧ 2 ≤ B₀ ∧
      ∀ b : Fin (m + 1) → ℤ,
        B₀ ≤ (b (Fin.last m) : ℝ) →
        (∀ i, |b i| ≤ b (Fin.last m)) →
        ((b (Fin.last m) : ℝ)) ^ (-C) ≤ |∑ i : Fin (m + 1), (b i : ℝ) * Real.log (p i : ℝ)| := by
  classical
  let n : ℕ := m + 1
  have hn2 : 2 ≤ n := by dsimp only [n]; omega
  set α : ℝ := (∑ i : Fin (m + 1), Real.log (p i : ℝ)) + 1
  have hα_ge1 : 1 ≤ α := by
    have hsum : 0 ≤ ∑ i : Fin (m + 1), Real.log (p i : ℝ) :=
      Finset.sum_nonneg fun i _ => Real.log_nonneg (by exact_mod_cast (hp_pr i).one_lt.le)
    linarith
  have hαm_le : ∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ) ≤ α := by
    have hsplit : ∑ i : Fin (m + 1), Real.log (p i : ℝ) =
        (∑ r : Fin m, Real.log (p (Fin.castSucc r) : ℝ)) + Real.log (p (Fin.last m) : ℝ) :=
      Fin.sum_univ_castSucc _
    have hlast : 0 ≤ Real.log (p (Fin.last m) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (hp_pr (Fin.last m)).one_lt.le)
    linarith
  set s_ratio : ℕ := Nat.ceil (128 * α) + 1
  have hs_ratio_pos : 1 ≤ s_ratio := by omega
  have hs_ratio_ge : 128 * α ≤ (s_ratio : ℝ) := by
    have h1 := Nat.le_ceil (128 * α)
    push_cast [s_ratio]; linarith
  -- Choose single parameter `u ≥ 1` beating both polynomial bounds via `pow_le_two_pow_eventually`
  set C_poly : ℕ :=
    max (8 * 2 ^ n * (2 * n * s_ratio + 1) ^ n)
        (200000 * n * (2 * n * s_ratio + 1) ^ n) + 100
  obtain ⟨u, hu1, hu_dom⟩ := pow_le_two_pow_eventually (n + 1) C_poly
  set L : ℕ := 2 ^ u
  have hL1 : 1 ≤ L := Nat.one_le_pow u 2 (by norm_num)
  set K : ℕ := 2 * n * u
  have hK1 : 1 ≤ K := by dsimp only [K]; nlinarith
  set S : ℕ := s_ratio * L
  have hS1 : 1 ≤ S := Nat.mul_pos hs_ratio_pos hL1
  set T₀ : ℕ := K * S
  have hT₀1 : 1 ≤ T₀ := Nat.mul_pos hK1 hS1
  set c_h : ℕ := 32 * K
  have hc_h1 : 1 ≤ c_h := by omega
  set c₀ : ℕ := 4 * c_h * (K * s_ratio + 1) ^ n
  have hc₀1 : 1 ≤ c₀ := by
    dsimp only [c₀]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) hc_h1) (pow_pos (Nat.succ_pos _) _)
  -- Verify key parameter inequalities from `hu_dom`
  have hK_dom : 8 * (K * s_ratio + 1) ^ n * (L + 1) ^ n ≤ 2 ^ K := by
    have hL_le : L + 1 ≤ 2 * 2 ^ u := by dsimp only [L]; omega
    have hKsr : K * s_ratio + 1 ≤ (2 * n * s_ratio + 1) * u := by
      dsimp only [K]; nlinarith
    have hu_n : u ^ n ≤ u ^ (n + 1) := Nat.pow_le_pow_right hu1 (Nat.le_succ n)
    have h1 : 8 * 2 ^ n * (2 * n * s_ratio + 1) ^ n * u ^ n ≤ 2 ^ u := by
      calc 8 * 2 ^ n * (2 * n * s_ratio + 1) ^ n * u ^ n
          ≤ C_poly * u ^ (n + 1) := by
            apply Nat.mul_le_mul _ hu_n
            dsimp only [C_poly]; omega
        _ ≤ 2 ^ u := hu_dom
    have h2 : (2 ^ u) * (2 ^ (n * u)) ≤ 2 ^ K := by
      rw [← pow_add]
      apply Nat.pow_le_pow_right (by norm_num)
      dsimp only [K]; nlinarith
    calc 8 * (K * s_ratio + 1) ^ n * (L + 1) ^ n
        ≤ 8 * ((2 * n * s_ratio + 1) * u) ^ n * (2 * 2 ^ u) ^ n := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hKsr n))
            (Nat.pow_le_pow_left hL_le n)
      _ = (8 * 2 ^ n * (2 * n * s_ratio + 1) ^ n * u ^ n) * 2 ^ (n * u) := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm u n]; ring
      _ ≤ 2 ^ u * 2 ^ (n * u) := Nat.mul_le_mul_right _ h1
      _ ≤ 2 ^ K := h2
  have hpoly_S_dom :
      2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) + 10 * (c_h : ℝ) ≤
        (0.8 : ℝ) * (c_h : ℝ) * (S : ℝ) := by
    have hlog_bnd : Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) ≤ 14000 * (n : ℝ) * (u : ℝ) := by
      have harg_le : Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2) ≤
          (192 * (c_h : ℝ)) * (2 : ℝ) ^ K := by
        have he3 : Real.exp 1 ≤ 3 := le_trans Real.exp_one_lt_d9.le (by norm_num)
        have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
        have hch1 : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
        have h1 : 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 ≤ 64 * (c_h : ℝ) * (2 : ℝ) ^ K := by nlinarith
        nlinarith
      have hpos : 0 < Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2) := by positivity
      calc Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2))
          ≤ Real.log ((192 * (c_h : ℝ)) * (2 : ℝ) ^ K) := Real.log_le_log hpos harg_le
        _ = Real.log (192 * (c_h : ℝ)) + (K : ℝ) * Real.log 2 := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        _ ≤ 192 * (c_h : ℝ) + (K : ℝ) * 1 := by
            have h1 := real_log_le_self_of_pos (show (0 : ℝ) < 192 * (c_h : ℝ) by positivity)
            have h2 : Real.log 2 ≤ 1 := le_trans Real.log_two_lt_d9.le (by norm_num)
            have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
            nlinarith
        _ ≤ 14000 * (n : ℝ) * (u : ℝ) := by
            have hch_eq : (c_h : ℝ) = 64 * (n : ℝ) * (u : ℝ) := by
              dsimp only [c_h, K]; push_cast; ring
            have hK_eq : (K : ℝ) = 2 * (n : ℝ) * (u : ℝ) := by
              dsimp only [K]; push_cast; ring
            rw [hch_eq, hK_eq]
            have hnu : (0 : ℝ) ≤ (n : ℝ) * (u : ℝ) := by positivity
            nlinarith
    have hc0_le : ((c₀ : ℝ) + 1) ≤ 5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n := by
      have hKsr : (K : ℝ) * (s_ratio : ℝ) + 1 ≤ (2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ) := by
        have hKeq : (K : ℝ) = 2 * (n : ℝ) * (u : ℝ) := by dsimp only [K]; push_cast; ring
        have hu1R : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
        rw [hKeq]; nlinarith
      have hpow : ((K : ℝ) * (s_ratio : ℝ) + 1) ^ n ≤
          ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n :=
        pow_le_pow_left₀ (by positivity) hKsr n
      have hc0_eq : (c₀ : ℝ) = 4 * (c_h : ℝ) * ((K : ℝ) * (s_ratio : ℝ) + 1) ^ n := by
        dsimp only [c₀]; push_cast; rfl
      have hch1 : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
      have hpow1 : (1 : ℝ) ≤ ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n := by
        apply one_le_pow₀
        have hu1R : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
        have hns : (0 : ℝ) ≤ 2 * (n : ℝ) * (s_ratio : ℝ) := by positivity
        nlinarith
      rw [hc0_eq]; nlinarith
    have hlog_pos : 0 ≤ Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) := by
      apply Real.log_nonneg
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
      have hch1 : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
      have h32 : (1 : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by nlinarith
      nlinarith
    have hu_domR : (C_poly : ℝ) * (u : ℝ) ^ (n + 1) ≤ (L : ℝ) := by
      have : (C_poly * u ^ (n + 1) : ℕ) ≤ 2 ^ u := hu_dom
      dsimp only [L]
      exact_mod_cast this
    have hCpoly_ge : (200000 * (n : ℝ) * (2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n + 100 : ℝ) ≤ (C_poly : ℝ) := by
      have hnat : 200000 * n * (2 * n * s_ratio + 1) ^ n + 100 ≤ C_poly := by
        dsimp only [C_poly]; omega
      exact_mod_cast hnat
    have hu1R : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu1
    have hch1R : (0 : ℝ) ≤ (c_h : ℝ) := Nat.cast_nonneg _
    have hs1R : (1 : ℝ) ≤ (s_ratio : ℝ) := by exact_mod_cast hs_ratio_pos
    have hS_eq : (S : ℝ) = (s_ratio : ℝ) * (L : ℝ) := by dsimp only [S]; push_cast; rfl
    have hprod_bound :
        2 * (5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n) *
          (14000 * (n : ℝ) * (u : ℝ)) + 10 * (c_h : ℝ) ≤
        (0.8 : ℝ) * (c_h : ℝ) * (S : ℝ) := by
      rw [mul_pow, hS_eq]
      have h1 : 140000 * (n : ℝ) * (2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n * (u : ℝ) ^ (n + 1) + 10 ≤
          (0.8 : ℝ) * (C_poly : ℝ) * (u : ℝ) ^ (n + 1) := by
        have hup : (1 : ℝ) ≤ (u : ℝ) ^ (n + 1) := one_le_pow₀ hu1R
        have hpos_t : 0 ≤ (n : ℝ) * (2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n * (u : ℝ) ^ (n + 1) := by positivity
        nlinarith
      have h2 : (0.8 : ℝ) * (C_poly : ℝ) * (u : ℝ) ^ (n + 1) ≤ (0.8 : ℝ) * (s_ratio : ℝ) * (L : ℝ) := by
        have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
        nlinarith
      calc 2 * (5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n * (u : ℝ) ^ n)) *
              (14000 * (n : ℝ) * (u : ℝ)) + 10 * (c_h : ℝ)
          = (c_h : ℝ) * (140000 * (n : ℝ) * (2 * (n : ℝ) * (s_ratio : ℝ) + 1) ^ n *
              (u : ℝ) ^ (n + 1) + 10) := by rw [pow_succ]; ring
        _ ≤ (c_h : ℝ) * ((0.8 : ℝ) * (s_ratio : ℝ) * (L : ℝ)) :=
            mul_le_mul_of_nonneg_left (le_trans h1 h2) hch1R
        _ = (0.8 : ℝ) * (c_h : ℝ) * ((s_ratio : ℝ) * (L : ℝ)) := by ring
    have hmul_le : 2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) ≤
        2 * (5 * (c_h : ℝ) * ((2 * (n : ℝ) * (s_ratio : ℝ) + 1) * (u : ℝ)) ^ n) *
          (14000 * (n : ℝ) * (u : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hc0_le (by norm_num : (0 : ℝ) ≤ 2)
      exact mul_le_mul h1 hlog_bnd hlog_pos (by positivity)
    linarith
  -- Choose fixed exponent `C_tot` and threshold `k₀` (depending ONLY on `n, α, u`)
  set M₀ : ℝ :=
    7.5 * (T₀ : ℝ) + ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) + α * (L : ℝ) * (c_h : ℝ)
  have hM₀_nn : 0 ≤ M₀ := by
    have hlog0 : 0 ≤ Real.log (Real.exp 1 * ((c_h : ℝ) + 2)) := by
      apply Real.log_nonneg
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      have hch0 : (0 : ℝ) ≤ (c_h : ℝ) := Nat.cast_nonneg c_h
      nlinarith only [he1, hch0]
    positivity
  set C_tot : ℝ :=
    M₀ + 10 * (T₀ : ℝ) + 2 * ((c₀ : ℝ) + 1) * Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) +
      α * (L : ℝ) * (2 : ℝ) ^ K * (c_h : ℝ) + 3 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) + 20
  have hCtot_pos : 0 < C_tot := by
    have hlog0 : 0 ≤ Real.log (Real.exp 1 * (32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2)) := by
      apply Real.log_nonneg
      have he1 : (1 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      have h2K1 : (1 : ℝ) ≤ (2 : ℝ) ^ K := one_le_pow₀ (by norm_num)
      have hch1 : (1 : ℝ) ≤ (c_h : ℝ) := by exact_mod_cast hc_h1
      have h32 : (1 : ℝ) ≤ 32 * (2 : ℝ) ^ K * (c_h : ℝ) + 2 := by nlinarith only [h2K1, hch1]
      nlinarith only [he1, h32]
    positivity
  -- Pick `k₀ ≥ 10` large enough so all small-order log(poly(k)) terms are absorbed by `k`
  have hk₀_exists : ∃ k₀ : ℕ, 10 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      (Real.log (2 * (L : ℝ) + 1) + 1 ≤ (0.5 : ℝ) * (k : ℝ)) ∧
      (Real.log (20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) ≤ (k : ℝ)) ∧
      ((T₀ : ℝ) * Real.log (2 * (L : ℝ) + 1) ≤ (0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ)) ∧
      (Real.log (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
        ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
        (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ))) ≤ 2 * (k : ℝ)) := by
    set A1 : ℝ := Real.log (2 * (L : ℝ) + 1) + 1
    set A2 : ℝ := Real.log (20 * ((c₀ : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n))
    set A3 : ℝ := Real.log (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) *
        ((2 * ((2 : ℝ) ^ K * (c_h : ℝ)) ^ 2) ^ S) *
        (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (L : ℝ)))
    set D_deg : ℕ := 2 * S + 4
    set N₁ : ℕ := (4 * D_deg + 1) ^ 2
    set k₀ : ℕ := max 10 (max N₁ (Nat.ceil (2 * max 0 A1 + 2 * max 0 A2 + 2 * max 0 A3 + 10)))
    refine ⟨k₀, le_max_left _ _, fun k hk => ?_⟩
    have hk10 : 10 ≤ k := le_trans (le_max_left _ _) hk
    have hkN₁ : N₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    have hkA : 2 * max 0 A1 + 2 * max 0 A2 + 2 * max 0 A3 + 10 ≤ (k : ℝ) := by
      have h1 : Nat.ceil (2 * max 0 A1 + 2 * max 0 A2 + 2 * max 0 A3 + 10) ≤ k :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hlogk : (D_deg : ℝ) * Real.log (k : ℝ) ≤ (0.5 : ℝ) * (k : ℝ) := by
      have hsq : 4 * (D_deg : ℝ) ≤ Real.sqrt (k : ℝ) := by
        have h1 : ((4 * D_deg + 1 : ℕ) : ℝ) ^ 2 ≤ (k : ℝ) := by
          have : (4 * D_deg + 1) ^ 2 ≤ k := hkN₁
          exact_mod_cast this
        have h2 : ((4 * D_deg + 1 : ℕ) : ℝ) ≤ Real.sqrt (k : ℝ) := by
          rw [← Real.sqrt_sq (Nat.cast_nonneg _)]
          exact Real.sqrt_le_sqrt h1
        push_cast at h2; linarith
      have hlog_sq := real_log_le_two_sqrt hk_pos
      have hsqrt_sq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := Real.mul_self_sqrt hk_pos.le
      have hsqrt_nn : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      have hDnn : (0 : ℝ) ≤ (D_deg : ℝ) := Nat.cast_nonneg D_deg
      nlinarith only [hsq, hlog_sq, hsqrt_sq, hsqrt_nn, hDnn]
    have hA1 : A1 ≤ (0.5 : ℝ) * (k : ℝ) := by
      have h1 := le_max_right (0 : ℝ) A1
      have h2 := le_max_left (0 : ℝ) A2
      have h3 := le_max_left (0 : ℝ) A3
      linarith only [hkA, h1, h2, h3]
    have hA2 : A2 ≤ (0.5 : ℝ) * (k : ℝ) := by
      have h1 := le_max_left (0 : ℝ) A1
      have h2 := le_max_right (0 : ℝ) A2
      have h3 := le_max_left (0 : ℝ) A3
      linarith only [hkA, h1, h2, h3]
    have hA3 : A3 ≤ (0.5 : ℝ) * (k : ℝ) := by
      have h1 := le_max_left (0 : ℝ) A1
      have h2 := le_max_left (0 : ℝ) A2
      have h3 := le_max_right (0 : ℝ) A3
      linarith only [hkA, h1, h2, h3]
    have hlogk_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
    refine ⟨hA1, ?_, ?_, ?_⟩
    · have hle : 20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) ≤
          (20 * ((c₀ : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) * (k : ℝ) ^ 2 := by
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
        have h1 : (c₀ : ℝ) * (k : ℝ) + 1 ≤ ((c₀ : ℝ) + 1) * (k : ℝ) := by
          have : (0 : ℝ) ≤ (c₀ : ℝ) := Nat.cast_nonneg c₀
          nlinarith only [hk1, this]
        have h2 := pow_le_pow_left₀ (by positivity) h1 2
        rw [mul_pow] at h2
        have h3 : 0 ≤ 20 * ((L : ℝ) + 1) ^ (2 * n) := by positivity
        nlinarith only [h2, h3]
      calc Real.log (20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n))
          ≤ Real.log ((20 * ((c₀ : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) * (k : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) hle
        _ = A2 + 2 * Real.log (k : ℝ) := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; rfl
        _ ≤ (0.5 : ℝ) * (k : ℝ) + (D_deg : ℝ) * Real.log (k : ℝ) := by
            have h2D : (2 : ℝ) ≤ (D_deg : ℝ) := by dsimp only [D_deg]; exact_mod_cast (by omega : 2 ≤ 2 * S + 4)
            nlinarith only [hA2, h2D, hlogk_nn]
        _ ≤ (k : ℝ) := by linarith only [hlogk]
    · rw [show (0.5 : ℝ) * (T₀ : ℝ) * (k : ℝ) = (T₀ : ℝ) * ((0.5 : ℝ) * (k : ℝ)) by ring]
      exact mul_le_mul_of_nonneg_left (by dsimp only [A1] at hA1; linarith only [hA1]) (Nat.cast_nonneg T₀)
    · have hfact :
          32 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (S : ℝ) *
            ((2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S) *
            (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ) * (L : ℝ)) =
          (32 * (2 : ℝ) ^ K * (c_h : ℝ) * (S : ℝ) *
            ((2 * ((2 : ℝ) ^ K * (c_h : ℝ)) ^ 2) ^ S) *
            (((T₀ : ℝ) + α + 1) ^ S) * (2 * (2 : ℝ) ^ K * (c_h : ℝ) * (L : ℝ))) *
            (k : ℝ) ^ (2 * S + 2) := by
        have h1 : (2 * ((2 : ℝ) ^ K * (c_h : ℝ) * (k : ℝ)) ^ 2) ^ S =
            (2 * ((2 : ℝ) ^ K * (c_h : ℝ)) ^ 2) ^ S * (k : ℝ) ^ (2 * S) := by
          rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul]
          ring
        rw [h1, show 2 * S + 2 = 2 * S + 1 + 1 by omega, pow_succ, pow_succ]
        ring
      rw [hfact, Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hdeg_le : ((2 * S + 2 : ℕ) : ℝ) ≤ (D_deg : ℝ) := by
        dsimp only [D_deg]; exact_mod_cast (by omega : 2 * S + 2 ≤ 2 * S + 4)
      have hmul := mul_le_mul_of_nonneg_right hdeg_le hlogk_nn
      dsimp only [A3] at hA3
      linarith only [hA3, hmul, hlogk]
  obtain ⟨k₀, hk₀10, hk₀_prop⟩ := hk₀_exists
  -- Return `C := C_tot + 2` and `B₀ := max 2 (Real.exp ((k₀ : ℝ) + 1))`
  refine ⟨C_tot + 2, max 2 (Real.exp ((k₀ : ℝ) + 1)), by linarith only [hCtot_pos], le_max_left _ _, ?_⟩
  intro b hbn_ge hb_le
  set b_n : ℤ := b (Fin.last m)
  have hbnR_ge2 : (2 : ℝ) ≤ (b_n : ℝ) := le_trans (le_max_left _ _) hbn_ge
  have hbn_pos : 0 < b_n := by
    have : (0 : ℝ) < (b_n : ℝ) := by linarith only [hbnR_ge2]
    exact_mod_cast this
  have hbnR_pos : (0 : ℝ) < (b_n : ℝ) := by exact_mod_cast hbn_pos
  set D : ℝ := Real.log (b_n : ℝ)
  have hD_ge : (k₀ : ℝ) + 1 ≤ D := by
    rw [Real.le_log_iff_exp_le hbnR_pos]
    exact le_trans (le_max_right _ _) hbn_ge
  set k : ℕ := Nat.floor D
  have hk_ge : k₀ ≤ k := by
    have h1 : (k₀ : ℝ) ≤ D := by linarith only [hD_ge]
    exact Nat.le_floor h1
  have hk10 : 10 ≤ k := le_trans hk₀10 hk_ge
  have hk_pos : 0 < k := by omega
  have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
  have hk_le_D : (k : ℝ) ≤ D := Nat.floor_le (by have := Nat.cast_nonneg (α := ℝ) k₀; linarith only [hD_ge, this])
  have hD_lt_k1 : D < (k : ℝ) + 1 := Nat.lt_floor_add_one D
  have hD_le_15k : D ≤ (1.5 : ℝ) * (k : ℝ) := by
    have : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk10
    linarith only [hD_lt_k1, this]
  obtain ⟨hlog2L, hlogU2, hT0log2L, hlogErr⟩ := hk₀_prop k hk_ge
  set Λ : ℝ := ∑ i : Fin n, (b i : ℝ) * Real.log (p i : ℝ)
  set Λ' : ℝ := Λ / (b_n : ℝ)
  have hΛ'abs : |Λ'| = |Λ| / (b_n : ℝ) := by rw [abs_div, abs_of_pos hbnR_pos]
  -- Proof by contradiction: assume |Λ| < b_n ^ (-(C_tot + 2))
  by_contra hlt_contra
  push Not at hlt_contra
  have hΛ_lt_exp : |Λ| < Real.exp (-(C_tot + 2) * D) := by
    rwa [Real.rpow_def_of_pos hbnR_pos, mul_comm D] at hlt_contra
  have hΛ'_lt : |Λ'| < Real.exp (-(C_tot + 2) * (k : ℝ)) := by
    have h1 : |Λ'| ≤ |Λ| := by
      rw [hΛ'abs]; exact div_le_self (abs_nonneg _) (by linarith only [hbnR_ge2])
    have h2 : Real.exp (-(C_tot + 2) * D) ≤ Real.exp (-(C_tot + 2) * (k : ℝ)) := by
      apply Real.exp_le_exp.mpr; nlinarith only [hCtot_pos, hk_le_D]
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hΛ_lt_exp h2)
  -- Define `h₀`, `L₀` and construct coefficients `c : Idx L₀ L m → ℤ` via Siegel's Lemma
  set h₀ : ℕ := c_h * k
  have hh₀1 : 1 ≤ h₀ := Nat.mul_pos hc_h1 hk_pos
  set L₀ : ℕ := c₀ * k
  have hL₀1 : 1 ≤ L₀ := Nat.mul_pos hc₀1 hk_pos
  -- Equation index type: `(s_idx : Fin h₀)` representing `s = s_idx.val + 1 ∈ 1..h₀`,
  -- and `t : {t : Fin n → Fin (T₀ + 1) // ∑ i, (t i).val ≤ T₀}`
  let EqIdx := Fin h₀ × {t : Fin n → Fin (T₀ + 1) // ∑ i : Fin n, (t i).val ≤ T₀}
  have hcard_Eq : Fintype.card EqIdx ≤ h₀ * (T₀ + 1) ^ n := by
    dsimp only [EqIdx]
    rw [Fintype.card_prod, Fintype.card_fin]
    apply Nat.mul_le_mul_left h₀
    have hsub := Fintype.card_subtype_le (fun t : Fin n → Fin (T₀ + 1) => ∑ i : Fin n, (t i).val ≤ T₀)
    simpa [Fintype.card_fun, Fintype.card_fin] using hsub
  have hcard_Idx : Fintype.card (Idx L₀ L m) = (L₀ + 1) * (L + 1) ^ n := by
    simp [Idx, Fintype.card_prod, Fintype.card_fin, n]
  have hcard_pos : 0 < Fintype.card (Idx L₀ L m) := by rw [hcard_Idx]; positivity
  have h2card : 2 * Fintype.card EqIdx ≤ Fintype.card (Idx L₀ L m) := by
    have hT0L : T₀ + 1 ≤ (K * s_ratio + 1) * L := by
      have : T₀ = K * s_ratio * L := by dsimp only [T₀, S]; ring
      rw [this, add_mul, one_mul]
      exact Nat.add_le_add_left hL1 _
    have hc0_ge : 2 * c_h * (K * s_ratio + 1) ^ n ≤ c₀ := by
      dsimp only [c₀]
      exact Nat.mul_le_mul_right ((K * s_ratio + 1) ^ n) (Nat.mul_le_mul_right c_h (by norm_num : 2 ≤ 4))
    calc 2 * Fintype.card EqIdx
        ≤ 2 * (h₀ * (T₀ + 1) ^ n) := Nat.mul_le_mul_left 2 hcard_Eq
      _ ≤ 2 * (h₀ * ((K * s_ratio + 1) * L) ^ n) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left h₀ (Nat.pow_le_pow_left hT0L n))
      _ = (2 * c_h * (K * s_ratio + 1) ^ n) * (k * L ^ n) := by
          dsimp only [h₀]; rw [mul_pow]; ring
      _ ≤ c₀ * (k * L ^ n) := Nat.mul_le_mul_right _ hc0_ge
      _ = L₀ * L ^ n := by dsimp only [L₀]; ring
      _ ≤ (L₀ + 1) * (L + 1) ^ n :=
          Nat.mul_le_mul (Nat.le_succ _) (Nat.pow_le_pow_left (Nat.le_succ L) n)
      _ = Fintype.card (Idx L₀ L m) := hcard_Idx.symm
  -- Build integer matrix A : EqIdx → Idx L₀ L m → ℤ
  have hmat_exists : ∀ (eq : EqIdx) (idx : Idx L₀ L m), ∃ z : ℤ,
      (z : ℚ) =
        ((Nat.lcmUpto k : ℚ) ^ (eq.2.1 0).val) *
        ((b_n : ℚ) ^ (∑ r : Fin m, (eq.2.1 (Fin.succ r)).val)) *
        ((Polynomial.hasseDeriv (eq.2.1 0).val (feldmanPoly k idx.1.val)).eval ((eq.1.val + 1 : ℕ) : ℚ) *
          (∏ r : Fin m, (gammaRat b idx r) ^ (eq.2.1 (Fin.succ r)).val) *
          (∏ i : Fin n, ((p i : ℚ) ^ (idx.2 i).val) ^ (eq.1.val + 1))) := by
    intro eq idx
    obtain ⟨zF, hzF⟩ := lcmUpto_pow_mul_hasseDeriv_feldmanPoly_int hk_pos idx.1.val (eq.2.1 0).val (eq.1.val + 1)
    refine ⟨zF * (∏ r : Fin m, (gammaInt b idx r) ^ (eq.2.1 (Fin.succ r)).val) *
        (∏ i : Fin n, ((p i : ℤ) ^ (idx.2 i).val) ^ (eq.1.val + 1)), ?_⟩
    have hpg : ((b_n : ℚ) ^ (∑ r : Fin m, (eq.2.1 (Fin.succ r)).val)) *
        (∏ r : Fin m, (gammaRat b idx r) ^ (eq.2.1 (Fin.succ r)).val) =
        ∏ r : Fin m, ((gammaInt b idx r : ℚ) ^ (eq.2.1 (Fin.succ r)).val) := by
      rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl; intro r _
      rw [← mul_pow, bn_mul_gammaRat (ne_of_gt hbn_pos) idx r]
    simp only [Int.cast_mul, Int.cast_prod, Int.cast_pow, Int.cast_natCast]
    rw [hzF, ← hpg]
    ring
  choose Amat hAmat using hmat_exists
  -- Bound |Amat eq idx| ≤ Hmat using `baker_matrix_entry_bound`
  set Hmat : ℕ := Nat.ceil (Real.exp (M₀ * (k : ℝ)))
  have hAmat_bound : ∀ eq idx, (Amat eq idx).natAbs ≤ Hmat := by
    intro eq idx
    have hreal : |(Amat eq idx : ℝ)| ≤ Real.exp (M₀ * (k : ℝ)) := by
      have hα_sum : ∑ i : Fin (m + 1), Real.log (p i : ℝ) ≤ α := by dsimp only [α]; linarith
      exact baker_matrix_entry_bound hk_pos rfl p hp_pr hbn_pos hb_le hα_sum hlog2L hD_lt_k1
        (show eq.1.val + 1 ≤ c_h * k from eq.1.isLt) eq.2.2 idx (Amat eq idx) (hAmat eq idx)
    have hnatR : ((Amat eq idx).natAbs : ℝ) ≤ (Hmat : ℝ) := by
      rw [← Int.cast_natCast (R := ℝ), Int.natCast_natAbs, Int.cast_abs]
      exact le_trans hreal (Nat.le_ceil _)
    exact_mod_cast hnatR
  -- Apply Siegel's Lemma!
  obtain ⟨c, hc_ne, hc_bound, hc_zero⟩ := siegel_lemma Amat Hmat hAmat_bound hcard_pos h2card
  set Cmax : ℝ := ((2 * Fintype.card (Idx L₀ L m) * Hmat + 1 : ℕ) : ℝ)
  have hCmax_nn : 0 ≤ Cmax := Nat.cast_nonneg _
  have hc_abs : ∀ idx, |(c idx : ℝ)| ≤ Cmax := by
    intro idx
    have hnat : ((c idx).natAbs : ℝ) ≤ Cmax := by
      dsimp only [Cmax]; exact_mod_cast hc_bound idx
    rwa [← Int.cast_natCast (R := ℝ), Int.natCast_natAbs, Int.cast_abs] at hnat
  have hUCmax : (Fintype.card (Idx L₀ L m) : ℝ) * Cmax ≤ Real.exp ((M₀ + 1) * (k : ℝ)) := by
    have hHmat_le : (Hmat : ℝ) ≤ 2 * Real.exp (M₀ * (k : ℝ)) := by
      have h1 : (Hmat : ℝ) < Real.exp (M₀ * (k : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
      have h2 : (1 : ℝ) ≤ Real.exp (M₀ * (k : ℝ)) := Real.one_le_exp (by positivity)
      linarith only [h1, h2]
    have hcardR : (Fintype.card (Idx L₀ L m) : ℝ) = ((c₀ : ℝ) * (k : ℝ) + 1) * ((L : ℝ) + 1) ^ n := by
      rw [hcard_Idx]; dsimp only [L₀]; push_cast; rfl
    have hcard_ge1 : (1 : ℝ) ≤ (Fintype.card (Idx L₀ L m) : ℝ) := by exact_mod_cast hcard_pos
    have hpoly_le : (Fintype.card (Idx L₀ L m) : ℝ) * Cmax ≤
        (20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) * Real.exp (M₀ * (k : ℝ)) := by
      have hexp1 : (1 : ℝ) ≤ Real.exp (M₀ * (k : ℝ)) := Real.one_le_exp (by positivity)
      have hC : Cmax ≤ 5 * (Fintype.card (Idx L₀ L m) : ℝ) * Real.exp (M₀ * (k : ℝ)) := by
        dsimp only [Cmax]; push_cast
        have h1 : (1 : ℝ) ≤ (Fintype.card (Idx L₀ L m) : ℝ) * Real.exp (M₀ * (k : ℝ)) :=
          one_le_mul_of_one_le_of_one_le hcard_ge1 hexp1
        have h2 := mul_le_mul_of_nonneg_left hHmat_le (show (0 : ℝ) ≤ 2 * (Fintype.card (Idx L₀ L m) : ℝ) by positivity)
        linarith only [h1, h2]
      have hsq : (Fintype.card (Idx L₀ L m) : ℝ) * (Fintype.card (Idx L₀ L m) : ℝ) =
          ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) := by
        rw [hcardR, two_mul, pow_add]; ring
      calc (Fintype.card (Idx L₀ L m) : ℝ) * Cmax
          ≤ (Fintype.card (Idx L₀ L m) : ℝ) * (5 * (Fintype.card (Idx L₀ L m) : ℝ) * Real.exp (M₀ * (k : ℝ))) :=
            mul_le_mul_of_nonneg_left hC (by positivity)
        _ = 5 * (((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n)) * Real.exp (M₀ * (k : ℝ)) := by
            rw [← hsq]; ring
        _ ≤ 20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) * Real.exp (M₀ * (k : ℝ)) := by
            have hnn : 0 ≤ ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) * Real.exp (M₀ * (k : ℝ)) := by
              positivity
            linarith only [hnn]
    have h20 : 20 * ((c₀ : ℝ) * (k : ℝ) + 1) ^ 2 * ((L : ℝ) + 1) ^ (2 * n) ≤ Real.exp (k : ℝ) := by
      rw [← Real.log_le_iff_le_exp (by positivity)]; exact hlogU2
    calc (Fintype.card (Idx L₀ L m) : ℝ) * Cmax
        ≤ Real.exp (k : ℝ) * Real.exp (M₀ * (k : ℝ)) :=
          le_trans hpoly_le (mul_le_mul_of_nonneg_right h20 (by positivity))
      _ = Real.exp ((M₀ + 1) * (k : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
  -- Base case j = 0: Psi c t s = 0 for all 1 ≤ s ≤ h₀ and ∑ i, t i ≤ T₀
  have hbase : ∀ s ∈ Finset.Icc 1 h₀, ∀ t : Fin n → ℕ, (∑ i, t i) ≤ T₀ →
      Psi k p b c t s = 0 := by
    intro s hs t ht
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsh : s ≤ h₀ := (Finset.mem_Icc.mp hs).2
    let eq : EqIdx :=
      (⟨s - 1, by omega⟩,
       ⟨fun i => ⟨t i, by
          have := Finset.single_le_sum (f := t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega⟩,
        by simpa using ht⟩)
    have hz : ∑ idx : Idx L₀ L m, Amat eq idx * c idx = 0 := hc_zero eq
    have hq : ((Nat.lcmUpto k : ℚ) ^ (t 0)) * ((b_n : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
        Psi k p b c t s = 0 := by
      unfold Psi
      rw [Finset.mul_sum]
      have hsum_eq : ∑ idx : Idx L₀ L m,
            ((Nat.lcmUpto k : ℚ) ^ (t 0)) * ((b_n : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) *
            ((c idx : ℚ) *
              (Polynomial.hasseDeriv (t 0) (feldmanPoly k idx.1.val)).eval (s : ℚ) *
              (∏ r : Fin m, (gammaRat b idx r) ^ (t (Fin.succ r))) *
              (∏ i : Fin n, ((p i : ℚ) ^ (idx.2 i).val) ^ s)) =
          ∑ idx : Idx L₀ L m, (Amat eq idx : ℚ) * (c idx : ℚ) := by
        apply Finset.sum_congr rfl
        intro idx _
        have hA := hAmat eq idx
        have hs_eq : eq.1.val + 1 = s := by dsimp only [eq]; omega
        have ht_eq : ∀ i, (eq.2.1 i).val = t i := fun _ => rfl
        simp only [hs_eq, ht_eq] at hA
        rw [hA]; ring
      rw [hsum_eq]
      have hzQ : (∑ idx : Idx L₀ L m, (Amat eq idx : ℚ) * (c idx : ℚ)) =
          ((∑ idx : Idx L₀ L m, Amat eq idx * c idx : ℤ) : ℚ) := by push_cast; rfl
      rw [hzQ, hz, Int.cast_zero]
    have hdenQ : ((Nat.lcmUpto k : ℚ) ^ (t 0)) * ((b_n : ℚ) ^ (∑ r : Fin m, t (Fin.succ r))) ≠ 0 := by
      have h1 : (Nat.lcmUpto k : ℚ) ≠ 0 := by exact_mod_cast (Nat.lcmUpto_pos k).ne'
      have h2 : (b_n : ℚ) ≠ 0 := by exact_mod_cast hbn_pos.ne'
      positivity
    exact (mul_eq_zero.mp hq).resolve_left hdenQ
  -- Extrapolation induction over j = 0..K using `baker_extrap_step`!
  have h65α : 65 * α * (L : ℝ) ≤ (0.55 : ℝ) * (S : ℝ) := by
    have hS_eq : (S : ℝ) = (s_ratio : ℝ) * (L : ℝ) := by dsimp only [S]; push_cast; rfl
    rw [hS_eq]
    have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
    nlinarith only [hs_ratio_ge, hL0, hα_ge1]
  have hα_sum : ∑ i : Fin (m + 1), Real.log (p i : ℝ) ≤ α := by dsimp only [α]; linarith only []
  have hextrap : ∀ j : ℕ, j ≤ K →
      ∀ s ∈ Finset.Icc 1 (2 ^ j * h₀), ∀ t : Fin n → ℕ, (∑ i, t i) ≤ (K - j) * S →
      Psi k p b c t s = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ s hs t ht
      simp only [pow_zero, one_mul, Nat.sub_zero] at hs ht
      exact hbase s hs t ht
    | succ j ih =>
      intro hjK
      exact baker_extrap_step hk_pos hL1 hS1 hc_h1 hjK rfl rfl rfl p hp_pr hbn_pos hb_le hD_le_15k
        hα_ge1 hα_sum hαm_le h65α rfl rfl hCtot_pos hpoly_S_dom hT0log2L hlogErr
        (by rw [← hΛ'abs]; exact hΛ'_lt) c hCmax_nn hc_abs hUCmax (ih (by omega))
  -- Step K: Psi c 0 s = 0 for all 1 ≤ s ≤ 2^K * h₀ ≥ (L₀ + 1) * (L + 1)^n
  have hvan_K : ∀ s ∈ Finset.Icc 1 ((L₀ + 1) * Fintype.card (Fin n → Fin (L + 1))),
      Psi k p b c (fun _ => 0) s = 0 := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hs_hi : s ≤ 2 ^ K * h₀ := by
      have h1 := (Finset.mem_Icc.mp hs).2
      simp only [Fintype.card_fun, Fintype.card_fin] at h1
      have hL0_le : L₀ + 1 ≤ 2 * c₀ * k := by
        have h2L : L₀ + 1 ≤ 2 * L₀ := by omega
        calc L₀ + 1 ≤ 2 * L₀ := h2L
          _ = 2 * c₀ * k := by dsimp only [L₀]; ring
      have hdom : (L₀ + 1) * (L + 1) ^ n ≤ 2 ^ K * h₀ := by
        calc (L₀ + 1) * (L + 1) ^ n
            ≤ (2 * c₀ * k) * (L + 1) ^ n := Nat.mul_le_mul_right _ hL0_le
          _ = (8 * (K * s_ratio + 1) ^ n * (L + 1) ^ n) * h₀ := by
              dsimp only [c₀, h₀]; ring
          _ ≤ 2 ^ K * h₀ := Nat.mul_le_mul_right h₀ hK_dom
      exact le_trans h1 hdom
    exact hextrap K le_rfl s (Finset.mem_Icc.mpr ⟨hs1, hs_hi⟩) (fun _ => 0) (by simp)
  -- Apply discrete shift-operator nonvanishing (Section 5)!
  let ω : (Fin n → Fin (L + 1)) → ℕ := fun μ => ∏ i : Fin n, p i ^ (μ i).val
  have hω_inj : Function.Injective ω := prime_pow_prod_injective hp_pr hp_inj
  have hω_pos : ∀ μ, 0 < ω μ := fun μ => Finset.prod_pos fun i _ => pow_pos (hp_pr i).pos _
  let Q : (Fin n → Fin (L + 1)) → Polynomial ℚ :=
    fun μ => ∑ l₀ : Fin (L₀ + 1), C (c (l₀, μ) : ℚ) * feldmanPoly k l₀.val
  have hQ_deg : ∀ μ, (Q μ).natDegree ≤ L₀ := by
    intro μ
    refine le_trans (Polynomial.natDegree_sum_le Finset.univ _) ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le L₀, fun l₀ _ => ?_⟩
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [natDegree_feldmanPoly hk_pos]
    exact Nat.lt_succ_iff.mp l₀.isLt
  have hvan_Q : ∀ s ∈ Finset.Icc 1 ((L₀ + 1) * Fintype.card (Fin n → Fin (L + 1))),
      ∑ μ : Fin n → Fin (L + 1), (Q μ).eval (s : ℚ) * (ω μ : ℚ) ^ s = 0 := by
    intro s hs
    have hPsi0 := hvan_K s hs
    rw [← hPsi0]
    unfold Psi
    simp only [Polynomial.hasseDeriv_zero, LinearMap.id_apply, pow_zero, Finset.prod_const_one, mul_one]
    rw [Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl
    intro μ _
    dsimp only [Q, ω]
    rw [Polynomial.eval_finsetSum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l₀ _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Nat.cast_prod, Finset.prod_pow]
    simp only [Nat.cast_pow]; rfl
  have hQ_all_zero := exp_poly_zero_of_zero_on_Icc ω hω_inj hω_pos L₀ Q hQ_deg hvan_Q
  obtain ⟨⟨l₀_ne, μ_ne⟩, hne⟩ := hc_ne
  have hQne : Q μ_ne ≠ 0 :=
    sum_feldmanPoly_ne_zero hk_pos (fun l₀ => (c (l₀, μ_ne) : ℚ)) ⟨l₀_ne, by exact_mod_cast hne⟩
  exact hQne (hQ_all_zero μ_ne)

/- Section 8: Reduction from `H1` + Inlined `R1.H2`, `R1.H3`, `R1.main` -/

theorem baker_feldman_H1 :
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (b : ℕ → ℤ) (B : ℝ), 2 ≤ B → (∀ p ∈ S, |(b p : ℝ)| ≤ B) → (∃ p ∈ S, b p ≠ 0) →
        c * B ^ (-C) ≤ |∑ p ∈ S, (b p : ℝ) * Real.log (p : ℝ)| := by
  classical
  intro S hS
  by_cases hcard : S.card ≤ 1
  · refine ⟨1, Real.log 2, zero_lt_one, Real.log_pos (by norm_num), ?_⟩
    intro b B hB _ hne
    obtain ⟨p₀, hp₀S, hp₀ne⟩ := hne
    have hSeq : S = {p₀} := by
      rw [Finset.card_le_one_iff_subset_singleton] at hcard
      obtain ⟨a, ha⟩ := hcard
      have hp0a : p₀ = a := Finset.mem_singleton.mp (ha hp₀S)
      subst hp0a
      exact Finset.Subset.antisymm ha (Finset.singleton_subset_iff.mpr hp₀S)
    rw [hSeq, Finset.sum_singleton, abs_mul]
    have hb1 : (1 : ℝ) ≤ |(b p₀ : ℝ)| := by
      have : (1 : ℤ) ≤ |b p₀| := Int.one_le_abs hp₀ne
      exact_mod_cast this
    have hlp : Real.log 2 ≤ |Real.log (p₀ : ℝ)| := by
      have hp2 : (2 : ℝ) ≤ (p₀ : ℝ) := by exact_mod_cast (hS p₀ hp₀S).two_le
      have h1 : Real.log 2 ≤ Real.log (p₀ : ℝ) := Real.log_le_log (by norm_num) hp2
      rw [abs_of_nonneg (le_trans (Real.log_pos (by norm_num)).le h1)]
      exact h1
    have hB1 : B ^ (-(1 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg (by linarith), Real.rpow_one]
      exact inv_le_one_of_one_le₀ (by linarith)
    calc Real.log 2 * B ^ (-(1 : ℝ))
        ≤ Real.log 2 * 1 := mul_le_mul_of_nonneg_left hB1 (Real.log_pos (by norm_num)).le
      _ = 1 * Real.log 2 := by ring
      _ ≤ |(b p₀ : ℝ)| * |Real.log (p₀ : ℝ)| :=
          mul_le_mul hb1 hlp (Real.log_pos (by norm_num)).le (abs_nonneg _)
  · have hn2 : 2 ≤ S.card := by omega
    set n := S.card
    set m := n - 1
    have hmn : m + 1 = n := by omega
    have hm1 : 1 ≤ m := by omega
    let e : Fin (m + 1) ≃ S := (Fintype.equivFinOfCardEq (by simp [hmn, n])).symm
    -- For each `pivot : Fin (m + 1)`, permute `pivot` to `Fin.last m` and apply `baker_feldman_core`
    have hpivot_bound : ∀ pivot : Fin (m + 1), ∃ C B₀ : ℝ, 0 < C ∧ 2 ≤ B₀ ∧
        ∀ b : Fin (m + 1) → ℤ, B₀ ≤ (b pivot : ℝ) → (∀ i, |b i| ≤ b pivot) →
          ((b pivot : ℝ)) ^ (-C) ≤ |∑ i : Fin (m + 1), (b i : ℝ) * Real.log ((e i : ℕ) : ℝ)| := by
      intro pivot
      let σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap pivot (Fin.last m)
      let p' : Fin (m + 1) → ℕ := fun i => (e (σ i) : ℕ)
      have hp'_pr : ∀ i, (p' i).Prime := fun i => hS (e (σ i)) (e (σ i)).2
      have hp'_inj : Function.Injective p' := fun i j hij =>
        σ.injective (e.injective (Subtype.ext hij))
      obtain ⟨C, B₀, hC, hB₀, hcore⟩ := baker_feldman_core hm1 p' hp'_pr hp'_inj
      refine ⟨C, B₀, hC, hB₀, fun b hge hle => ?_⟩
      let b' : Fin (m + 1) → ℤ := fun i => b (σ i)
      have hlast : b' (Fin.last m) = b pivot := by
        dsimp only [b', σ]; rw [Equiv.swap_apply_right]
      have h1 := hcore b' (by rwa [hlast]) (fun i => by rw [hlast]; exact hle (σ i))
      rw [hlast] at h1
      have hsum_eq : ∑ i : Fin (m + 1), (b' i : ℝ) * Real.log (p' i : ℝ) =
          ∑ i : Fin (m + 1), (b i : ℝ) * Real.log ((e i : ℕ) : ℝ) :=
        Equiv.sum_comp σ (fun i => (b i : ℝ) * Real.log ((e i : ℕ) : ℝ))
      rwa [hsum_eq] at h1
    choose C_piv B₀_piv hC_piv hB₀_piv hcore_piv using hpivot_bound
    have huniv_ne : (Finset.univ : Finset (Fin (m + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
    set C : ℝ := (Finset.univ.image C_piv).max' (huniv_ne.image _)
    set B₀ : ℝ := (Finset.univ.image B₀_piv).max' (huniv_ne.image _)
    have hC_ge : ∀ pivot, C_piv pivot ≤ C := fun pivot =>
      Finset.le_max' _ _ (Finset.mem_image_of_mem C_piv (Finset.mem_univ pivot))
    have hB₀_ge : ∀ pivot, B₀_piv pivot ≤ B₀ := fun pivot =>
      Finset.le_max' _ _ (Finset.mem_image_of_mem B₀_piv (Finset.mem_univ pivot))
    have hC_pos : 0 < C := lt_of_lt_of_le (hC_piv 0) (hC_ge 0)
    have hB₀_ge2 : 2 ≤ B₀ := le_trans (hB₀_piv 0) (hB₀_ge 0)
    -- Handle small bounded integer vectors `|b_i| ≤ ⌈B₀⌉` via finiteness + `sum_int_mul_log_ne_zero`
    set K_fin : ℕ := Nat.ceil B₀
    let SmallSet : Finset (Fin (m + 1) → ℤ) :=
      (Fintype.piFinset fun _ : Fin (m + 1) => Finset.Icc (-(K_fin : ℤ)) (K_fin : ℤ)).filter
        (fun v => ∃ i, v i ≠ 0)
    have hSmall_ne : SmallSet.Nonempty := by
      refine ⟨fun _ => 1, Finset.mem_filter.mpr ⟨?_, ⟨0, one_ne_zero⟩⟩⟩
      rw [Fintype.mem_piFinset]
      intro _; rw [Finset.mem_Icc]
      have hK1 : 1 ≤ K_fin := by
        have : (1 : ℝ) ≤ (K_fin : ℝ) := le_trans (by linarith) (Nat.le_ceil B₀)
        exact_mod_cast this
      omega
    let valFn : (Fin (m + 1) → ℤ) → ℝ :=
      fun v => |∑ i : Fin (m + 1), (v i : ℝ) * Real.log ((e i : ℕ) : ℝ)|
    obtain ⟨vmin, hvmin_mem, hvmin_le⟩ := Finset.exists_min_image SmallSet valFn hSmall_ne
    have hvmin_pos : 0 < valFn vmin := by
      dsimp only [valFn]
      rw [abs_pos]
      have hne_v : ∃ i, vmin i ≠ 0 := (Finset.mem_filter.mp hvmin_mem).2
      let b_nat : ℕ → ℤ := fun q => if hq : q ∈ S then vmin (e.symm ⟨q, hq⟩) else 0
      have hsum_eq : ∑ i : Fin (m + 1), (vmin i : ℝ) * Real.log ((e i : ℕ) : ℝ) =
          ∑ q ∈ S, (b_nat q : ℝ) * Real.log (q : ℝ) := by
        rw [← Finset.sum_attach S]
        refine Fintype.sum_equiv e _ _ fun i => ?_
        dsimp only [b_nat]
        rw [dif_pos (e i).2, Equiv.symm_apply_apply]
      rw [hsum_eq]
      apply sum_int_mul_log_ne_zero hS
      obtain ⟨i₀, hi₀⟩ := hne_v
      refine ⟨(e i₀ : ℕ), (e i₀).2, ?_⟩
      dsimp only [b_nat]
      rw [dif_pos (e i₀).2, Equiv.symm_apply_apply]
      exact hi₀
    set c_const : ℝ := min 1 (valFn vmin)
    have hc_pos : 0 < c_const := lt_min zero_lt_one hvmin_pos
    refine ⟨C, c_const, hC_pos, hc_pos, ?_⟩
    intro b B hB hbB hne
    let v : Fin (m + 1) → ℤ := fun i => b (e i : ℕ)
    have hsum_v : ∑ p ∈ S, (b p : ℝ) * Real.log (p : ℝ) =
        ∑ i : Fin (m + 1), (v i : ℝ) * Real.log ((e i : ℕ) : ℝ) := by
      rw [← Finset.sum_attach S]
      exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
    rw [hsum_v]
    have hne_v : ∃ i, v i ≠ 0 := by
      obtain ⟨q, hqS, hqne⟩ := hne
      refine ⟨e.symm ⟨q, hqS⟩, ?_⟩
      dsimp only [v]; simpa using hqne
    -- Pick pivot maximizing `|v i|`
    obtain ⟨pivot, _, hpivot_max⟩ := Finset.exists_max_image Finset.univ (fun i => |v i|) huniv_ne
    have hpivot_ne : v pivot ≠ 0 := by
      obtain ⟨i₀, hi₀⟩ := hne_v
      have h1 : 0 < |v i₀| := abs_pos.mpr hi₀
      have h2 := hpivot_max i₀ (Finset.mem_univ i₀)
      exact abs_pos.mp (lt_of_lt_of_le h1 h2)
    -- Replace `v` by `w := if 0 < v pivot then v else -v` so `0 < w pivot` and `|∑ w| = |∑ v|`
    let w : Fin (m + 1) → ℤ := fun i => if 0 < v pivot then v i else -v i
    have hw_sum : |∑ i : Fin (m + 1), (w i : ℝ) * Real.log ((e i : ℕ) : ℝ)| =
        |∑ i : Fin (m + 1), (v i : ℝ) * Real.log ((e i : ℕ) : ℝ)| := by
      dsimp only [w]
      split_ifs with hpos
      · rfl
      · have hneg : ∑ i : Fin (m + 1), ((-v i : ℤ) : ℝ) * Real.log ((e i : ℕ) : ℝ) =
            -(∑ i : Fin (m + 1), (v i : ℝ) * Real.log ((e i : ℕ) : ℝ)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro i _; push_cast; ring
        rw [hneg, abs_neg]
    rw [← hw_sum]
    have hw_piv_eq : w pivot = |v pivot| := by
      dsimp only [w]
      split_ifs with hpos
      · exact (abs_of_pos hpos).symm
      · have hlt : v pivot < 0 := lt_of_le_of_ne (not_lt.mp hpos) hpivot_ne
        exact (abs_of_neg hlt).symm
    have hw_max : ∀ i, |w i| ≤ w pivot := by
      intro i
      rw [hw_piv_eq]
      dsimp only [w]
      split_ifs
      · exact hpivot_max i (Finset.mem_univ i)
      · rw [abs_neg]; exact hpivot_max i (Finset.mem_univ i)
    have hw_piv_le_B : (w pivot : ℝ) ≤ B := by
      rw [hw_piv_eq, Int.cast_abs]
      exact hbB (e pivot : ℕ) (e pivot).2
    by_cases hbig : B₀ ≤ (w pivot : ℝ)
    · have h1 := hcore_piv pivot w (le_trans (hB₀_ge pivot) hbig) hw_max
      have hwp_pos : (0 : ℝ) < (w pivot : ℝ) := by linarith
      have hB_pos : (0 : ℝ) < B := by linarith
      have hpow1 : B ^ (-C) ≤ (w pivot : ℝ) ^ (-C) :=
        Real.rpow_le_rpow_of_nonpos hwp_pos hw_piv_le_B (by linarith)
      have hpow2 : (w pivot : ℝ) ^ (-C) ≤ (w pivot : ℝ) ^ (-C_piv pivot) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg (hC_ge pivot))
      have hc1 : c_const ≤ 1 := min_le_left _ _
      calc c_const * B ^ (-C)
          ≤ 1 * B ^ (-C) := mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hB_pos.le _)
        _ = B ^ (-C) := one_mul _
        _ ≤ (w pivot : ℝ) ^ (-C_piv pivot) := le_trans hpow1 hpow2
        _ ≤ |∑ i : Fin (m + 1), (w i : ℝ) * Real.log ((e i : ℕ) : ℝ)| := h1
    · push Not at hbig
      have hw_mem : w ∈ SmallSet := by
        rw [Finset.mem_filter]
        refine ⟨?_, ⟨pivot, by rw [hw_piv_eq]; exact abs_ne_zero.mpr hpivot_ne⟩⟩
        rw [Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_Icc]
        have hi_le : |(w i : ℝ)| ≤ (K_fin : ℝ) := by
          have h1 : |(w i : ℝ)| ≤ (w pivot : ℝ) := by exact_mod_cast hw_max i
          exact le_trans h1 (le_trans hbig.le (Nat.le_ceil B₀))
        have hiZ : |w i| ≤ (K_fin : ℤ) := by exact_mod_cast hi_le
        exact abs_le.mp hiZ
      have hmin := hvmin_le w hw_mem
      have hBpow : B ^ (-C) ≤ 1 := by
        rw [Real.rpow_neg (by linarith)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by linarith) hC_pos.le)
      calc c_const * B ^ (-C)
          ≤ valFn vmin * 1 := mul_le_mul (min_le_right _ _) hBpow (Real.rpow_nonneg (by linarith) _) hvmin_pos.le
        _ = valFn vmin := mul_one _
        _ ≤ valFn w := hmin

/- Inlined R1.H2, R1.H3, and R1.main -/

lemma smooth_pow_mem {P : Set ℕ} {p : ℕ} (hp : p ∈ P) (hpp : p.Prime) (k : ℕ) :
    p ^ k ∈ Erdos675.composedOf P := by
  refine ⟨pow_pos hpp.pos k, fun q hq hqd => ?_⟩
  have := (Nat.prime_dvd_prime_iff_eq hq hpp).1 (hq.dvd_of_dvd_pow hqd)
  rw [this]; exact hp

lemma smooth_mul_mem {P : Set ℕ} {p m : ℕ} (hp : p ∈ P) (hpp : p.Prime)
    (hm : m ∈ Erdos675.composedOf P) : p * m ∈ Erdos675.composedOf P := by
  refine ⟨Nat.mul_pos hpp.pos hm.1, fun q hq hqd => ?_⟩
  rcases (Nat.Prime.dvd_mul hq).1 hqd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hq hpp).1 h]; exact hp
  · exact hm.2 q hq h

lemma smooth_infinite {P : Set ℕ} {p : ℕ} (hp : p ∈ P) (hpp : p.Prime) :
    (Set.ofPred (· ∈ Erdos675.composedOf P)).Infinite := by
  have hinj : Function.Injective (fun k : ℕ => p ^ k) := Nat.pow_right_injective hpp.two_le
  exact Set.infinite_of_injective_forall_mem hinj fun k => smooth_pow_mem hp hpp k

lemma smooth_H2 :
    ∀ P : Set ℕ, P.Finite → P.Nonempty → P ⊆ {p : ℕ | p.Prime} →
      StrictMono (Erdos240.a P) ∧ (∀ i, Erdos240.a P i ∈ Erdos675.composedOf P) ∧
        ∀ p ∈ P, ∀ i, Erdos240.a P (i + 1) ≤ p * Erdos240.a P i := by
  classical
  intro P _ hne hsub
  obtain ⟨p₀, hp₀⟩ := hne
  have hinf := smooth_infinite hp₀ (hsub hp₀)
  have hmem : ∀ i, Erdos240.a P i ∈ Erdos675.composedOf P := fun i =>
    Nat.nth_mem_of_infinite hinf i
  refine ⟨Nat.nth_strictMono hinf, hmem, fun p hp i => ?_⟩
  have hpp : p.Prime := hsub hp
  have hpm := smooth_mul_mem hp hpp (hmem i)
  have hpos := (hmem i).1
  obtain ⟨k, hk⟩ : ∃ k, Nat.nth (· ∈ Erdos675.composedOf P) k = p * Erdos240.a P i :=
    ⟨_, Nat.nth_count hpm⟩
  have hlt : Erdos240.a P i < Nat.nth (· ∈ Erdos675.composedOf P) k := by
    rw [hk]
    have := hpp.two_le
    nlinarith
  have hik : i < k := (Nat.nth_lt_nth hinf).1 hlt
  have : Erdos240.a P (i + 1) ≤ Nat.nth (· ∈ Erdos675.composedOf P) k :=
    (Nat.nth_le_nth hinf).2 hik
  rwa [hk] at this

lemma smooth_logsum (S : Finset ℕ) (n : ℕ) (hS : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ S) :
    Real.log (n : ℝ) = ∑ p ∈ S, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum]
  apply Finset.sum_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    exact hS p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  · intro p _ hp
    rw [Finsupp.notMem_support_iff] at hp
    rw [hp]; simp

lemma smooth_fact_le (n p : ℕ) (hn : 0 < n) :
    (n.factorization p : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  by_cases hp : p.Prime
  · have h1 : p ^ n.factorization p ≤ n := Nat.le_of_dvd hn (Nat.ordProj_dvd n p)
    have h2 : 2 ^ n.factorization p ≤ p ^ n.factorization p := Nat.pow_le_pow_left hp.two_le _
    have h3 : ((2 : ℝ)) ^ n.factorization p ≤ (n : ℝ) := by exact_mod_cast le_trans h2 h1
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow] at h4
    rwa [le_div_iff₀ hl2]
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]
    simp only [Nat.cast_zero]
    exact div_nonneg (Real.log_nonneg hn1) hl2.le

lemma smooth_H3 :
    ∀ (S : Finset ℕ) (x y : ℕ), 0 < x → 0 < y →
      (∀ p : ℕ, p.Prime → p ∣ x → p ∈ S) → (∀ p : ℕ, p.Prime → p ∣ y → p ∈ S) →
      ∃ b : ℕ → ℤ, Real.log (y : ℝ) - Real.log (x : ℝ) = ∑ p ∈ S, (b p : ℝ) * Real.log p ∧
        ∀ p ∈ S, |(b p : ℝ)| ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2 := by
  intro S x y hx hy hSx hSy
  refine ⟨fun p => (y.factorization p : ℤ) - (x.factorization p : ℤ), ?_, ?_⟩
  · rw [smooth_logsum S y hSy, smooth_logsum S x hSx, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _; push_cast; ring
  · intro p _
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hx1 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have hy1 : (0 : ℝ) < (y : ℝ) := by exact_mod_cast hy
    have hxm : (x : ℝ) ≤ ((max x y : ℕ) : ℝ) := by exact_mod_cast le_max_left x y
    have hym : (y : ℝ) ≤ ((max x y : ℕ) : ℝ) := by exact_mod_cast le_max_right x y
    have a1 := smooth_fact_le x p hx
    have a2 := smooth_fact_le y p hy
    have b1 : Real.log (x : ℝ) / Real.log 2 ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_right (Real.log_le_log hx1 hxm) hl2.le
    have b2 : Real.log (y : ℝ) / Real.log 2 ≤ Real.log ((max x y : ℕ) : ℝ) / Real.log 2 :=
      div_le_div_of_nonneg_right (Real.log_le_log hy1 hym) hl2.le
    have c1 : (0 : ℝ) ≤ (x.factorization p : ℝ) := Nat.cast_nonneg _
    have c2 : (0 : ℝ) ≤ (y.factorization p : ℝ) := Nat.cast_nonneg _
    simp only [Int.cast_sub, Int.cast_natCast]
    rw [abs_le]; constructor <;> linarith

end BakerFeldman

theorem OMA.solution : type_of% @Erdos240.erdos_240.variants.tijdeman_finite := by
  open Filter Asymptotics BakerFeldman in
  intro P hP hne hpr
  obtain ⟨hmono, hmem, hstep⟩ := smooth_H2 P hP hne hpr
  obtain ⟨p0, hp0⟩ := hne
  have hp0prime : p0.Prime := hpr hp0
  set S := hP.toFinset with hS
  have hSP : ∀ p, p ∈ S ↔ p ∈ P := fun p => Set.Finite.mem_toFinset hP
  obtain ⟨C, c, hC, hc, hbaker⟩ := baker_feldman_H1 S (fun p hp => hpr ((hSP p).1 hp))
  refine ⟨C, hC, ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlp0 : 0 ≤ Real.log (p0 : ℝ) := Real.log_nonneg (by exact_mod_cast hp0prime.one_lt.le)
  set K0 : ℝ := (Real.log (p0 : ℝ) + 1) / Real.log 2 + 2 with hK0
  have hK0pos : 0 < K0 := by positivity
  set κ : ℝ := c * K0 ^ (-C) with hκ
  have hκpos : 0 < κ := by positivity
  refine IsBigO.of_bound κ⁻¹ ?_
  have hev : ∀ᶠ i in atTop, 3 ≤ Erdos240.a P i :=
    hmono.tendsto_atTop.eventually (eventually_ge_atTop 3)
  filter_upwards [hev] with i hi
  set x := Erdos240.a P i with hx
  set y := Erdos240.a P (i + 1) with hy
  have hxy : x < y := hmono (Nat.lt_succ_self i)
  have hyx : y ≤ p0 * x := hstep p0 hp0 i
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  have hxyR : (x : ℝ) < y := by exact_mod_cast hxy
  have hmx := hmem i
  have hmy := hmem (i + 1)
  obtain ⟨b, hlog, hb⟩ := smooth_H3 S x y (by omega) (by omega)
    (fun p hp hd => (hSP p).2 (hmx.2 p hp hd)) (fun p hp hd => (hSP p).2 (hmy.2 p hp hd))
  rw [max_eq_right hxy.le] at hb
  have hΛpos : 0 < Real.log (y : ℝ) - Real.log (x : ℝ) := by
    have := Real.log_lt_log hxpos hxyR
    linarith
  have hlogy : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  set B : ℝ := Real.log (y : ℝ) / Real.log 2 + 2 with hB
  have hB2 : 2 ≤ B := by
    have : 0 ≤ Real.log (y : ℝ) / Real.log 2 := div_nonneg hlogy hl2.le
    linarith
  have hbB : ∀ p ∈ S, |(b p : ℝ)| ≤ B := by
    intro p hp
    have := hb p hp
    linarith
  have hnz : ∃ p ∈ S, b p ≠ 0 := by
    by_contra hall
    push Not at hall
    have : ∑ p ∈ S, (b p : ℝ) * Real.log p = 0 :=
      Finset.sum_eq_zero fun p hp => by rw [hall p hp]; simp
    linarith
  have hbak := hbaker b B hB2 hbB hnz
  rw [← hlog, abs_of_pos hΛpos] at hbak
  have hlogx1 : 1 ≤ Real.log (x : ℝ) := by
    rw [Real.le_log_iff_exp_le hxpos]
    have h3x : (3 : ℝ) ≤ x := by exact_mod_cast hi
    have := Real.exp_one_lt_d9
    linarith
  have hlogyx : Real.log (y : ℝ) ≤ Real.log (p0 : ℝ) + Real.log (x : ℝ) := by
    rw [← Real.log_mul (by exact_mod_cast hp0prime.ne_zero) hxpos.ne']
    exact Real.log_le_log hypos (by exact_mod_cast hyx)
  have hBK : B ≤ K0 * Real.log (x : ℝ) := by
    have e1 : Real.log (y : ℝ) / Real.log 2 ≤
        (Real.log (p0 : ℝ) + 1) / Real.log 2 * Real.log (x : ℝ) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hl2]
      nlinarith
    rw [hB, hK0]
    nlinarith
  have hBpos : 0 < B := by linarith
  have hpow : (K0 * Real.log (x : ℝ)) ^ (-C) ≤ B ^ (-C) :=
    Real.rpow_le_rpow_of_nonpos hBpos hBK (by linarith)
  rw [Real.mul_rpow hK0pos.le (by linarith)] at hpow
  have hgap : (x : ℝ) * (Real.log (y : ℝ) - Real.log (x : ℝ)) ≤ (y : ℝ) - x := by
    rw [← Real.log_div hypos.ne' hxpos.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hypos hxpos)
    have e : (x : ℝ) * ((y : ℝ) / x - 1) = y - x := by field_simp
    nlinarith
  have hlx : 0 < Real.log (x : ℝ) := by linarith
  have hfx : (x : ℝ) / Real.log (x : ℝ) ^ C = (x : ℝ) * Real.log (x : ℝ) ^ (-C) := by
    rw [Real.rpow_neg hlx.le, div_eq_mul_inv]
  have hrp : 0 < Real.log (x : ℝ) ^ (-C) := Real.rpow_pos_of_pos hlx _
  have hcast : (((y - x : ℕ)) : ℝ) = (y : ℝ) - x := by rw [Nat.cast_sub hxy.le]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hcast, hfx,
    abs_of_pos (mul_pos hxpos hrp), abs_of_pos (by linarith)]
  rw [inv_mul_eq_div, le_div_iff₀ hκpos]
  calc (x : ℝ) * Real.log (x : ℝ) ^ (-C) * κ
      = (x : ℝ) * (c * (K0 ^ (-C) * Real.log (x : ℝ) ^ (-C))) := by rw [hκ]; ring
    _ ≤ (x : ℝ) * (c * B ^ (-C)) := by gcongr
    _ ≤ (x : ℝ) * (Real.log (y : ℝ) - Real.log (x : ℝ)) := by gcongr
    _ ≤ (y : ℝ) - x := hgap
