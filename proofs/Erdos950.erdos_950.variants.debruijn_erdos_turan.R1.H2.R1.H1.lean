import OMAReductions.R_Erdos950_erdos_950_variants_debruijn_erdos_turan_R1_H2_R1
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.RingTheory.Radical.NatInt

/-! The interval bound adapts @marcusbuffett’s proof in PR 2609. A dyadic shell
is contained in an interval of four times its lower endpoint. Its harmonic
weight cancels the logarithm from the sieve.

Count primes above the sieve cutoff by the Selberg upper bound on a single
interval, and bound the primes below the cutoff by counting all integers there.
The cutoff is the integer part of the fourth root of the interval length.

The Selberg sieve estimates are adapted from Arend Mellendijk's formalization
in PrimeNumberTheoremAnd, commit 55270df80721 (Apache 2.0), as ported for the
finite sieve bound in Erdős 1204. -/
/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
section
noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem inv_sub_antitoneOn_Icc
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_pos {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] :
    AntitoneOn (fun x:R ↦ x⁻¹) (Set.Ioi 0) := by
  convert inv_sub_antitoneOn_gt (R:=R) 0; ring

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

end Aux
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
section
noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)

abbrev selbergTerms := BoundingSieve.selbergTerms (s := s)

theorem selbergTerms_apply (d : ℕ) :
    (SelbergSieve.selbergTerms s) d = s.nu d * ∏ p ∈ d.primeFactors, 1/(1 - s.nu p) := by
  simpa only [selbergTerms, one_div] using BoundingSieve.selbergTerms_apply (s := s) d
section UpperBoundSieve

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

end UpperBoundSieve

section SieveLemmas

theorem selbergTerms_pos (l : ℕ) (hl : l ∣ s.prodPrimes) : 0 < (SelbergSieve.selbergTerms s) l := by
  exact BoundingSieve.selbergTerms_pos hl
theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative (SelbergSieve.selbergTerms s) := by
  exact BoundingSieve.selbergTerms_isMultiplicative
theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then (SelbergSieve.selbergTerms s) l else 0) = (SelbergSieve.selbergTerms s) d * (s.nu d)⁻¹ := by
  exact BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd
theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ s.totalMass * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

section LambdaSquared

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms s) l * (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 :=
  by simpa only [selbergTerms, one_div] using BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq (s := s) w
end LambdaSquared

end SelbergSieve
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
section
noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve

variable (s : SelbergSieve)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.prodPrimes, if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0

theorem selbergBoundingSum_pos :
    0 < (SelbergSieve.selbergBoundingSum s) := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : (SelbergSieve.selbergBoundingSum s) ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ (SelbergSieve.selbergBoundingSum s) := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * μ d * (SelbergSieve.selbergBoundingSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
  else 0

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ s.level) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ (SelbergSieve.selbergWeights s) d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * (SelbergSieve.selbergBoundingSum s)⁻¹ * ∑ m ∈ divisors s.prodPrimes,
          if (d * m) ^ 2 ≤ s.level ∧ Coprime m d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * (SelbergSieve.selbergWeights s) d =
      (SelbergSieve.selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes, if d ∣ l ∧ l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0 := by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  
  apply symm
  rw [sum_mul_subst d s.prodPrimes]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((s.nu d)⁻¹ * (s.nu d) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * μ d / (SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
      if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
        ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors s.prodPrimes, if k ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * (SelbergSieve.selbergBoundingSum s)⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors s.prodPrimes) l (fun _ => if l^2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared (SelbergSieve.selbergWeights s)

theorem weight_one_of_selberg : (SelbergSieve.selbergWeights s) 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd s.prodPrimes), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ s.level) : (SelbergSieve.selbergMuPlus s) d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ s.level _ d hd
  apply s.selbergWeights_eq_zero

def selbergUbSieve : UpperBoundSieve :=
  ⟨(SelbergSieve.selbergMuPlus s), BoundingSieve.upperMoebius_lambdaSquared (SelbergSieve.selbergWeights s) (s.weight_one_of_selberg)⟩

theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms (s.toBoundingSieve)) l *
          (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) = (SelbergSieve.selbergBoundingSum s)⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors s.prodPrimes, (if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/(SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (μ l:ℝ)^2  * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private theorem _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors s.prodPrimes) (hm : m ∈ divisors s.prodPrimes) :
    k * m ∣ s.prodPrimes ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ s.level ↔
    (k * m) ^ 2 ≤ s.level ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    (SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
  calc
  _ = (∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes, if k = d.gcd l ∧ l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * ∑ m ∈ divisors s.prodPrimes, if (k * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k s.prodPrimes, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors s.prodPrimes, if k ∣ d
          then (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans ((SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * (∑ m ∈ divisors s.prodPrimes, if (d*m) ^ 2 ≤ s.level ∧
      Coprime m d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |(SelbergSieve.selbergWeights s) d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*(SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : (SelbergSieve.selbergWeights s) d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]

end SelbergSieve
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
section
open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section
namespace Sieve

theorem prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

theorem primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    obtain ⟨q, hq⟩ : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      hp.prime.exists_mem_finset_dvd h
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

theorem siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1) (z : ℝ)
    (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    siftedSum (s := s.toBoundingSieve) =
    (s.support.filter (fun d => ∀ p:ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d; constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [←Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [prime_dvd_primorial_iff _ _ hpp]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [prime_dvd_primorial_iff _ _ hp]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  simp_rw [Nat.cast_one]
  intro x hx
  simp only [Finset.mem_filter] at hx
  apply hw x hx.1
end Sieve
end
end

/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/
section
open Sieve SelbergSieve BoundingSieve
open Filter Asymptotics
open scoped Nat ArithmeticFunction BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega

noncomputable section
namespace BrunTitchmarsh

def primeInterSieve (x y z : ℝ) (hz : 1 ≤ z) : SelbergSieve where
  support := Finset.Icc (Nat.ceil x) (Nat.floor (x+y))
  prodPrimes := primorial (Nat.floor z)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ ↦ 1
  weights_nonneg := fun _ ↦ zero_le_one
  totalMass := y
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ ↦ by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ ↦ by
    simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.zeta_apply, hp.ne_zero, ↓reduceIte, Nat.cast_one,
      ArithmeticFunction.id_apply, one_div]
    apply inv_lt_one_of_one_lt₀
    exact_mod_cast hp.one_lt
  level := z
  one_le_level := hz
theorem Ioc_filter_dvd_eq (d a b : ℕ) (hd : d ≠ 0) :
  Finset.filter (fun x ↦ d ∣ x) (Finset.Ioc a b) =
    Finset.image (fun x ↦ x * d) (Finset.Ioc (a / d) (b / d)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
  constructor
  · intro hn
    rcases hn with ⟨⟨han, hnb⟩, hd⟩
    refine ⟨n/d, ⟨Nat.div_lt_div_of_lt_of_dvd hd han,
      Nat.div_le_div_right (Nat.le_floor hnb)⟩, Nat.div_mul_cancel hd⟩
  · rintro ⟨r, ⟨ha, ha'⟩, rfl⟩
    refine ⟨⟨(Nat.div_lt_iff_lt_mul (by omega)).mp ha, Nat.mul_le_of_le_div d r b ha'⟩,
      Nat.dvd_mul_left d r⟩

theorem card_Ioc_filter_dvd (d a b : ℕ) (hd : d ≠ 0) :
    (Finset.filter (fun x ↦ d ∣ x) (Finset.Ioc a b)).card =
      b / d - a / d := by
  rw [Ioc_filter_dvd_eq _ _ _ hd, Finset.card_image_of_injective _ <| mul_left_injective₀ hd,
    Nat.card_Ioc]
end BrunTitchmarsh
end
end
open Finset Nat BoundingSieve
open scoped BigOperators ArithmeticFunction
noncomputable section
namespace OMA.IntervalSieve

private lemma sum_lambda_abs (P : ℕ) (w : ℕ → ℝ) :
    (∑ d ∈ P.divisors, |BoundingSieve.lambdaSquared w d|) ≤
      (∑ d ∈ P.divisors, |w d|)^2 := by
  classical
  let term (a b d : ℕ) := if d = a.lcm b then |w a| * |w b| else 0
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ a ∈ d.divisors, ∑ b ∈ d.divisors, term a b d := by
      apply sum_le_sum
      intro d _
      unfold BoundingSieve.lambdaSquared
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro a _
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro b _
      by_cases he : d = a.lcm b <;> simp [term,he,abs_mul]
    _ = ∑ d ∈ P.divisors, ∑ a ∈ P.divisors, ∑ b ∈ P.divisors, term a b d := by
      apply sum_congr rfl
      intro d hd
      have h := mem_divisors.mp hd
      have hiff (a b : ℕ) : (a ∣ d ∧ b ∣ d ∧ d = a.lcm b) ↔ d = a.lcm b := by
        constructor
        · tauto
        · rintro rfl
          exact ⟨Nat.dvd_lcm_left .., Nat.dvd_lcm_right ..,rfl⟩
      simp_rw [← Nat.divisors_filter_dvd_of_dvd h.2 h.1, sum_filter,term,ite_sum_zero,← ite_and,hiff]
    _ = _ := by
      rw [sum_comm,sq,mul_sum]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm,sum_mul]
      apply sum_congr rfl
      intro b hb
      have hl : a.lcm b ∈ P.divisors := mem_divisors.mpr ⟨Nat.lcm_dvd (dvd_of_mem_divisors ha) (dvd_of_mem_divisors hb),(mem_divisors.mp hb).2⟩
      simp [term,hl,mul_comm]

private lemma sharp_error (s : SelbergSieve) (z : ℕ) (hl : s.level = (z:ℝ)^2)
    (hr : ∀ d ∈ s.prodPrimes.divisors, |s.toBoundingSieve.rem d| ≤ 1) :
    s.toBoundingSieve.errSum s.selbergMuPlus ≤ (z:ℝ)^2 := by
  classical
  have hw : (∑ d ∈ s.prodPrimes.divisors, |s.selbergWeights d|) ≤ z := by
    let D := s.prodPrimes.divisors
    have he : (∑ d ∈ D, |s.selbergWeights d|) = ∑ d ∈ D.filter (· ≤ z), |s.selbergWeights d| := by
      apply (sum_subset (filter_subset _ _) ?_).symm
      intro d hd hnot
      have hdz : z < d := by simpa [hd] using hnot
      rw [s.selbergWeights_eq_zero d (by rw [hl,sq_le_sq₀ (by positivity) (by positivity),Nat.cast_le]; omega),abs_zero]
    change (∑ d ∈ D, |s.selbergWeights d|) ≤ _
    rw [he]
    calc
      _ ≤ ∑ _ ∈ D.filter (· ≤ z), (1:ℝ) := sum_le_sum (fun d _ => s.selberg_bound_weights d)
      _ ≤ ∑ _ ∈ Icc 1 z, (1:ℝ) := sum_le_sum_of_subset_of_nonneg (by
        intro d hd
        obtain ⟨hd,hle⟩ := mem_filter.mp hd
        exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,hle⟩) (by intros; norm_num)
      _ = _ := by simp
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors, |s.selbergMuPlus d| := by
      unfold BoundingSieve.errSum
      exact sum_le_sum (fun d hd => mul_le_of_le_one_right (abs_nonneg _) (hr d hd))
    _ ≤ (∑ d ∈ s.prodPrimes.divisors, |s.selbergWeights d|)^2 := sum_lambda_abs _ _
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg (fun _ _ => abs_nonneg _)) hw _

private def inter (u N z : ℕ) (hz : 1 ≤ z) : SelbergSieve :=
  { BrunTitchmarsh.primeInterSieve 1 N z (by exact_mod_cast hz) with
    support := Ioc u (u+N)
    level := (z:ℝ)^2
    one_le_level := one_le_pow₀ (by exact_mod_cast hz) }

private lemma nu_eq {u N z : ℕ} (hz : 1 ≤ z) {d : ℕ} (hd : d ≠ 0) :
    (inter u N z hz).nu d = (d:ℝ)⁻¹ := by
  simp [inter,BrunTitchmarsh.primeInterSieve,ArithmeticFunction.pdiv_apply,hd,one_div]

private lemma sharp_rem {u N z : ℕ} (hz : 1 ≤ z) {d : ℕ} (hd : d ≠ 0) :
    |(inter u N z hz).toBoundingSieve.rem d| ≤ 1 := by
  rw [BoundingSieve.rem,nu_eq hz hd]
  have hc : (inter u N z hz).toBoundingSieve.multSum d =
      (((u+N)/d - u/d : ℕ):ℝ) := by
    simp [BoundingSieve.multSum,inter,BrunTitchmarsh.primeInterSieve,
      BrunTitchmarsh.card_Ioc_filter_dvd,hd]
  rw [hc,Nat.cast_sub (Nat.div_le_div_right (by omega))]
  change |(↑((u+N)/d):ℝ) - ↑(u/d) - (d:ℝ)⁻¹ * N| ≤ 1
  have hf (a : ℕ) : ((a/d:ℕ):ℝ) ≤ (a:ℝ)/d ∧ (a:ℝ)/d < ((a/d:ℕ):ℝ)+1 := by
    rw [← Nat.floor_div_eq_div (K:=ℝ)]
    exact ⟨Nat.floor_le (by positivity),Nat.lt_floor_add_one _⟩
  obtain ⟨h1,h2⟩ := hf (u+N)
  obtain ⟨h3,h4⟩ := hf u
  rw [Nat.cast_add,add_div] at h1 h2
  rw [inv_mul_eq_div,abs_le]
  constructor <;> linarith

private lemma den_eq {u N z : ℕ} (hz : 1 ≤ z) :
    (inter u N z hz).selbergBoundingSum = ∑ d ∈ (Icc 1 z).filter Squarefree, (1:ℝ)/d.totient := by
  classical
  let s := inter u N z hz
  have hP : s.prodPrimes = primorial z := by simp [s,inter,BrunTitchmarsh.primeInterSieve]
  have hset : (s.prodPrimes.divisors.filter fun (d : ℕ) => (d:ℝ)^2 ≤ s.level) = (Icc 1 z).filter Squarefree := by
    ext d
    simp only [mem_filter,mem_divisors,mem_Icc,hP]
    change (_ ∧ _) ∧ (d:ℝ)^2 ≤ (z:ℝ)^2 ↔ _
    rw [sq_le_sq₀ (by positivity) (by positivity),Nat.cast_le]
    constructor
    · rintro ⟨⟨hd,hn⟩,hle⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (primorial_pos _),hle⟩,(hP ▸ s.prodPrimes_squarefree).squarefree_of_dvd hd⟩
    · rintro ⟨⟨hpos,hle⟩,hsq⟩
      refine ⟨⟨?_,primorial_ne_zero _⟩,hle⟩
      rw [← Nat.prod_primeFactors_of_squarefree hsq,primorial_eq_prod_primesLE]
      apply Finset.prod_dvd_prod_of_subset
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primeFactors hp).trans hle, Nat.prime_of_mem_primeFactors hp⟩
  change s.selbergBoundingSum = _
  rw [SelbergSieve.selbergBoundingSum,← sum_filter,hset]
  apply sum_congr rfl
  intro d hd
  have hpos := (mem_Icc.mp (mem_filter.mp hd).1).1
  rw [SelbergSieve.selbergTerms_apply,nu_eq hz (by omega)]
  have he (p) (hp : p ∈ d.primeFactors) : s.nu p = (p:ℝ)⁻¹ := nu_eq hz (Nat.pos_of_mem_primeFactors hp).ne'
  have hφ : (d.totient:ℝ) = (d:ℝ) * ∏ p ∈ d.primeFactors, (1-(p:ℝ)⁻¹) := by
    have h := congrArg (fun a : ℚ => (a:ℝ)) (Nat.totient_eq_mul_prod_factors d)
    push_cast at h
    exact h
  rw [hφ,one_div,mul_inv]
  congr 1
  rw [← Finset.prod_inv_distrib]
  apply prod_congr rfl
  intro p hp
  rw [he p hp,one_div]


end OMA.IntervalSieve
end

namespace OMA.SieveDenominator
open Finset UniqueFactorizationMonoid

lemma fiber (z d : ℕ) (hz : 1 ≤ z) (hd : Squarefree d) :
    ∑ n ∈ (Icc 1 z).filter (fun n => radical n = d), (n : ℝ)⁻¹ ≤ (d.totient : ℝ)⁻¹ := by
  classical
  let D := d ^ z
  let S := (Icc 1 z).filter fun n => radical n = d
  let b := fun n => D / n * d
  have hD : D ≠ 0 := pow_ne_zero _ hd.ne_zero
  have hf : 0 < d.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd.ne_zero)
  have facts (n : ℕ) (hn : n ∈ S) :
      b n ∈ D.divisors ∧ (b n).totient * n = D * d.totient := by
    obtain ⟨hI,hr⟩ := mem_filter.mp hn
    have hLo := (mem_Icc.mp hI).1
    have hHi := (mem_Icc.mp hI).2
    have hnd : n ∣ D := by
      calc n ∣ radical n ^ n := Nat.dvd_radical_pow_self (by omega)
           _ ∣ D := by rw [hr]; exact pow_dvd_pow d hHi
    have hmul := Nat.div_mul_cancel hnd
    have hdn : d ∣ n := hr ▸ radical_dvd_self
    have hb : b n ∣ D := by
      rw [← hmul]
      exact Nat.mul_dvd_mul_left _ hdn
    have hbp : (b n).primeFactors = d.primeFactors := by
      apply Subset.antisymm
      · simpa only [D, Nat.primeFactors_pow d (show z ≠ 0 by omega)] using Nat.primeFactors_mono hb hD
      · exact Nat.primeFactors_mono (dvd_mul_left d (D/n)) (fun e => hD (by simpa [e] using hb))
    have ht : (b n).totient = D / n * d.totient := by
      rw [Nat.totient_eq_div_primeFactors_mul (b n), hbp, Nat.prod_primeFactors_of_squarefree hd,
        Nat.totient_eq_div_primeFactors_mul d, Nat.prod_primeFactors_of_squarefree hd,
        Nat.div_self (Nat.pos_of_ne_zero hd.ne_zero), one_mul]
      simp only [b, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hd.ne_zero)]
    exact ⟨Nat.mem_divisors.mpr ⟨hb,hD⟩, by rw [ht, Nat.mul_right_comm,hmul]⟩
  have inj : Set.InjOn b (S : Set ℕ) := by
    intro i hi j hj he
    have hi' := (facts i hi).2
    have hj' := (facts j hj).2
    rw [he] at hi'
    have hp := (Nat.totient_pos.mpr (Nat.pos_of_mem_divisors (facts j hj).1))
    exact Nat.eq_of_mul_eq_mul_left hp (hi'.trans hj'.symm)
  have sub : S.image b ⊆ D.divisors := by
    rintro _ hx
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
    exact (facts n hn).1
  have bound : ∑ n ∈ S, (b n).totient ≤ D := calc
    _ = ∑ m ∈ S.image b, m.totient := (sum_image inj).symm
    _ ≤ ∑ m ∈ D.divisors, m.totient := sum_le_sum_of_subset sub
    _ = D := Nat.sum_totient D
  have hDR : 0 < (D : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hFR : 0 < (d.totient : ℝ) := by exact_mod_cast hf
  change ∑ n ∈ S, (n : ℝ)⁻¹ ≤ _
  calc
    _ = ∑ n ∈ S, ((b n).totient : ℝ) / ((D : ℝ) * d.totient) := by
      apply sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp (mem_filter.mp hn).1).1; omega)
      have ht : ((b n).totient : ℝ) * n = D * (d.totient : ℝ) := by exact_mod_cast (facts n hn).2
      field_simp
      linarith
    _ = (↑(∑ n ∈ S, (b n).totient) : ℝ) / ((D : ℝ) * d.totient) := by simp [sum_div]
    _ ≤ (D : ℝ) / ((D : ℝ) * d.totient) := by gcongr
    _ = _ := by field_simp

end OMA.SieveDenominator

open Finset UniqueFactorizationMonoid in
lemma OMA.SieveDenominator.log_bound (z : ℕ) (hz : 1 ≤ z) : Real.log ((z : ℝ) + 1) ≤ ∑ d ∈ (Icc 1 z).filter Squarefree, (1 : ℝ)/d.totient := by
  classical
  have maps (n : ℕ) (hn : n ∈ Icc 1 z) : radical n ∈ (Icc 1 z).filter Squarefree := by
    obtain ⟨hn,hnz⟩ := mem_Icc.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.radical_pos n,
      (Nat.radical_le_self_iff.mpr (by omega)).trans hnz⟩, squarefree_radical⟩
  calc
    _ ≤ (harmonic z : ℝ) := by simpa using log_add_one_le_harmonic z
    _ = ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ := by simp [harmonic_eq_sum_Icc]
    _ = ∑ d ∈ (Icc 1 z).filter Squarefree, ∑ n ∈ (Icc 1 z).filter (fun n => radical n = d),
        (n : ℝ)⁻¹ := (sum_fiberwise_of_maps_to maps _).symm
    _ ≤ _ := by
      apply sum_le_sum
      intro d hd
      simpa only [one_div] using OMA.SieveDenominator.fiber z d hz (mem_filter.mp hd).2
namespace OMA.IntervalSieve
open Finset Nat BoundingSieve
open scoped Classical Nat.Prime

private lemma short_count (x t z : ℕ) (hz : 1 ≤ z) :
    (π x : ℝ) - (π (x-t) : ℝ) ≤
      (z : ℝ) + ((t : ℝ) / Real.log ((z : ℝ)+1) + (z : ℝ)^2) := by
  classical
  let u := x-t
  let s := inter u t z hz
  let S := s.support.filter fun n => ∀ p : ℕ, p.Prime → (p : ℝ) ≤ z → ¬ p ∣ n
  have hS : (S.card : ℝ) = s.toBoundingSieve.siftedSum := by
    rw [Sieve.siftedSum_eq s (fun _ _ => rfl) (z:ℝ) (by exact_mod_cast hz)
      (show s.prodPrimes = primorial ⌊(z:ℝ)⌋₊ from rfl)]
  have hsub : primesLE x \ primesLE u ⊆ Icc 1 z ∪ S := by
    intro n hn
    obtain ⟨hxn,hun⟩ := mem_sdiff.mp hn
    obtain ⟨hle,hp⟩ := mem_primesLE.mp hxn
    have hlo : u < n := by
      by_contra! h
      exact hun (mem_primesLE.mpr ⟨h,hp⟩)
    by_cases hsmall : n ≤ z
    · exact mem_union_left _ (mem_Icc.mpr ⟨hp.pos,hsmall⟩)
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨(show n ∈ Ioc u (u+t) from mem_Ioc.mpr ⟨hlo,by dsimp [u]; omega⟩),?_⟩
      intro p hprime hpz hd
      have h := (Nat.prime_dvd_prime_iff_eq hprime hp).mp hd
      have hpn : p ≤ z := by exact_mod_cast hpz
      omega
  have hle : primesLE u ⊆ primesLE x := by
    intro n hn
    obtain ⟨hu,hn'⟩ := mem_primesLE.mp hn
    exact mem_primesLE.mpr ⟨hu.trans (Nat.sub_le ..),hn'⟩
  have hcard := (card_le_card hsub).trans (card_union_le (Icc 1 z) S)
  rw [card_sdiff_of_subset hle,primesLE_card_eq_primeCounting,primesLE_card_eq_primeCounting] at hcard
  have hdiff : (π x : ℝ) - (π u : ℝ) ≤ (z : ℝ) + S.card := by
    have hmono := card_le_card hle
    simp only [primesLE_card_eq_primeCounting] at hmono
    have hc : π x - π u ≤ z + S.card := by simpa using hcard
    apply sub_le_iff_le_add.mpr
    exact_mod_cast (show π x ≤ z + S.card + π u by omega)
  have hh := SelbergSieve.siftedSum_le_mainSum_errSum_of_UpperBoundSieve s.toBoundingSieve s.selbergUbSieve
  change _ ≤ s.totalMass * s.toBoundingSieve.mainSum s.selbergMuPlus + s.toBoundingSieve.errSum s.selbergMuPlus at hh
  rw [s.selberg_bound_simple_mainSum,← div_eq_mul_inv] at hh
  rw [hS] at hdiff
  apply hdiff.trans
  apply add_le_add_right
  apply hh.trans
  rw [show s.totalMass = (t:ℝ) from rfl,show s.selbergBoundingSum = _ from den_eq (u:=u) (N:=t) hz]
  apply _root_.add_le_add
  · gcongr
    · exact Real.log_pos (by exact_mod_cast (by omega : 1 < z+1))
    · exact OMA.SieveDenominator.log_bound z hz
  · exact sharp_error s z rfl (fun d hd => sharp_rem hz (Nat.pos_of_mem_divisors hd).ne')

end OMA.IntervalSieve

open scoped Nat.Prime in
theorem OMA.shell_window : ∀ x t : ℕ, 2 ≤ t → (π x : ℝ) - π (x-t) ≤ 8*t/Real.log t := by
  intro x t ht
  have ht1 : 1 < (t:ℝ) := by exact_mod_cast (show 1 < t by omega)
  let s := Real.sqrt (t:ℝ)
  let y := Real.sqrt s
  let z := ⌊y⌋₊
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hy : 0 < y := Real.sqrt_pos.mpr hs
  have hs2 : s^2 = t := Real.sq_sqrt (by linarith)
  have hy2 : y^2 = s := Real.sq_sqrt hs.le
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr ht1.le)
  have hz : 1 ≤ z := Nat.le_floor (by simpa using hy1)
  have hzle : (z:ℝ) ≤ y := Nat.floor_le hy.le
  have hzlt : y < (z:ℝ)+1 := Nat.lt_floor_add_one y
  have hL := Real.log_pos ht1
  have hZ : 0 < Real.log ((z:ℝ)+1) := Real.log_pos (by
    have h : (1:ℝ) ≤ z := by exact_mod_cast hz
    linarith)
  have hlog : Real.log (t:ℝ) = 2 * Real.log s := by rw [← hs2,Real.log_pow]; norm_num
  have hlog' : Real.log s = 2 * Real.log y := by rw [← hy2,Real.log_pow]; norm_num
  have hratio : Real.log (t:ℝ) ≤ 4*Real.log ((z:ℝ)+1) := by
    linarith [Real.log_le_log hy hzlt.le]
  have hmain : (t:ℝ) / Real.log ((z:ℝ)+1) ≤ 4*t / Real.log t := by
    rw [div_le_div_iff₀ hZ hL]
    nlinarith [mul_le_mul_of_nonneg_left hratio (show 0 ≤ (t:ℝ) by positivity)]
  have hz2 : (z:ℝ)^2 ≤ s := hy2 ▸ (pow_le_pow_left₀ (by positivity) hzle 2)
  have hzs : (z:ℝ) ≤ s := by
    have h : 1 ≤ (z:ℝ) := by exact_mod_cast hz
    nlinarith [mul_nonneg (show 0 ≤ (z:ℝ) by positivity) (show 0 ≤ (z:ℝ)-1 by linarith)]
  have hLs : Real.log (t:ℝ) ≤ 2*s := by linarith [Real.log_le_sub_one_of_pos hs]
  have herr : (z:ℝ) + (z:ℝ)^2 ≤ 4 * t / Real.log t := by
    rw [le_div_iff₀ hL]
    calc
      _ ≤ (2*s) * (2*s) := mul_le_mul (by linarith) hLs hL.le (by positivity)
      _ = _ := by nlinarith
  have hc := OMA.IntervalSieve.short_count x t z hz
  linarith [show 8*(t:ℝ)/Real.log t = 4*t/Real.log t + 4*t/Real.log t by ring]

open Finset Real
open scoped Nat.Prime

theorem OMA.solution : OMA.R_Erdos950_erdos_950_variants_debruijn_erdos_turan_R1_H2_R1.H1 := by
  classical
  refine ⟨64,by norm_num,?_⟩
  intro N p j
  let t := 2^j
  let x := p+2*t
  let P := (range N).filter Nat.Prime
  let S := (P.erase p).filter (fun q => Nat.log 2 (Nat.dist p q) = j)
  change ∑ q ∈ S, (harmonic (Nat.dist p q) : ℝ) / Nat.dist p q ≤ 64
  have ht : 0 < t := by dsimp [t]; positivity
  have htR : 0 < (t:ℝ) := by exact_mod_cast ht
  have hscale (q : ℕ) (hq : q ∈ S) : t ≤ Nat.dist p q ∧ Nat.dist p q < 2*t := by
    obtain ⟨hqp,hj⟩ := mem_filter.mp hq
    have hne := (mem_erase.mp hqp).1
    have hd : Nat.dist p q ≠ 0 := (Nat.dist_pos_of_ne hne.symm).ne'
    have hlow := Nat.pow_log_le_self 2 hd
    have hhigh := Nat.lt_pow_succ_log_self (b:=2) (by decide) (Nat.dist p q)
    rw [hj] at hlow hhigh
    exact ⟨hlow,by simpa [t,pow_succ,Nat.mul_comm] using hhigh⟩
  have hsub : S ⊆ x.primesLE \ (x-4*t).primesLE := by
    intro q hq
    have hprime := (mem_filter.mp (mem_erase.mp (mem_filter.mp hq).1).2).2
    have hqpos := hprime.pos
    have hh := (hscale q hq).2
    unfold Nat.dist at hh
    refine mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨by dsimp [x]; omega,hprime⟩,?_⟩
    intro h
    have hqx := (Nat.mem_primesLE.mp h).1
    dsimp [x] at hqx
    omega
  have hcard := card_le_card hsub
  rw [card_sdiff_of_subset (Nat.primesLE_mono (Nat.sub_le _ _)),
    Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting] at hcard
  have hc : (S.card : ℝ) ≤ 8*(4*(t:ℝ))/log (4*(t:ℝ)) := by
    have hh : (S.card:ℝ) ≤ (π x:ℝ)-π (x-4*t) := by
      rw [← Nat.cast_sub (Nat.monotone_primeCounting (Nat.sub_le _ _))]
      exact_mod_cast hcard
    exact hh.trans (by simpa using OMA.shell_window x (4*t) (by omega))
  have hlog4 : 1 ≤ log (4*(t:ℝ)) := by
    have h' : log ((2:ℝ)^2) ≤ log (4*(t:ℝ)) := log_le_log (by norm_num)
      (by
        have ht1 : (1:ℝ) ≤ t := by exact_mod_cast ht
        linarith)
    rw [Real.log_pow] at h'
    norm_num only [Nat.cast_ofNat] at h'
    linarith [Real.log_two_gt_d9]
  have hlog : 0 < log (4*(t:ℝ)) := by linarith
  let W := 2 * log (4*(t:ℝ)) / t
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    _ ≤ ∑ _ ∈ S, W := sum_le_sum fun q hq => by
      obtain ⟨hlo,hhi⟩ := hscale q hq
      have hd : (0:ℝ) < Nat.dist p q := lt_of_lt_of_le htR (by exact_mod_cast hlo)
      have hcomp : (Nat.dist p q : ℝ) ≤ 4*(t:ℝ) := by exact_mod_cast (show Nat.dist p q ≤ 4*t by omega)
      have hh := (harmonic_le_one_add_log (Nat.dist p q)).trans (add_le_add_right (log_le_log hd hcomp) 1)
      dsimp [W]
      apply div_le_div₀ (by positivity) (by linarith : (harmonic (Nat.dist p q):ℝ) ≤ 2*log (4*(t:ℝ))) htR
      exact_mod_cast hlo
    _ = (S.card : ℝ)*W := by simp
    _ ≤ (8*(4*(t:ℝ))/log (4*(t:ℝ)))*W := mul_le_mul_of_nonneg_right hc hW
    _ = 64 := by dsimp [W]; field_simp; ring
