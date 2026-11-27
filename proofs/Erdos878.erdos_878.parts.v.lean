import FormalConjectures.ErdosProblems.«878»
import Mathlib

/-!
# Solution to Erdos Problem 878, part (v)

Single-file Lean 4.33.1 port of the solution to Erdos Problem 878, part (v).

Attribution and Licensing (Apache License, Version 2.0):
1. Main proof adapted from rivkalipko/erdos-878-asymptotics
   (commit 4c47e6de8732037482450e83c71869aad107c1f4, PALOMAR-2026-11-19-000034),
   directed and maintained by Rivka Lipkovitz (with OpenAI Codex),
   licensed under the Apache License, Version 2.0.
2. Selberg sieve bounds and Brun-Titchmarsh prime interval estimates adapted from
   AlexKontorovich/PrimeNumberTheoremAnd
   (commit 2c476fa6441c607096d93c8fc7ac0a227a655dae),
   files BrunTitchmarsh.lean, Sieve/AuxResults.lean, Sieve/Basic.lean,
   Sieve/Selberg.lean, Sieve/SelbergBounds.lean,
   Copyright (c) 2023-2024 Arend Mellendijk,
   licensed under the Apache License, Version 2.0.
3. Problem definitions from google-deepmind/formal-conjectures
   (FormalConjectures/ErdosProblems/878.lean),
   Copyright 2026 The Formal Conjectures Authors,
   licensed under the Apache License, Version 2.0.

Modifications: flattened into a single self-contained Lean 4.33.1 file,
reused Mathlib.NumberTheory.SelbergSieve directly, expanded local notations,
removed module headers, adapted Lean 4.35 lemma names to Lean 4.33.1,
and bridged to FormalConjectures.ErdosProblems.878 via OMA.answer and OMA.solution.

License URL: https://www.apache.org/licenses/LICENSE-2.0
-/

noncomputable section

section Erdos878PartVSieveAux

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega
open Nat ArithmeticFunction Finset

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem ite_sum_zero {p : Prop} [Decidable p] (s : Finset ℕ) (f : ℕ → ℝ) :
    (if p then (∑ x ∈ s, f x) else 0) = ∑ x ∈ s, if p then f x else 0 := by
  split_ifs <;> simp

theorem conv_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors,
        ∑ d1 ∈ d.divisors,
          ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
      ∑ d ∈ n.divisors,
        ∑ d1 ∈ n.divisors,
          ∑ d2 ∈ n.divisors, if d = Nat.lcm d1 d2 then f d1 d2 d else 0 := by
  apply sum_congr rfl; intro d hd
  rw [mem_divisors] at hd
  simp_rw [←Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ←ite_and, ite_sum_zero,
    ←ite_and]
  congr with d1
  congr with d2
  congr
  rw [eq_iff_iff]
  refine ⟨fun ⟨_, _, h⟩ ↦ h, ?_⟩
  rintro rfl
  exact ⟨Nat.dvd_lcm_left d1 d2, Nat.dvd_lcm_right d1 d2, rfl⟩

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]--
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

theorem multiplicative_zero_of_zero_dvd (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    {m n : ℕ} (h_sq : Squarefree n) (hmn : m ∣ n) (h_zero : f m = 0) : f n = 0 := by
  rcases hmn with ⟨k, rfl⟩
  simp only [MulZeroClass.zero_mul,
    h_mult.map_mul_of_coprime (coprime_of_squarefree_mul h_sq), h_zero]

theorem div_mult_of_dvd_squarefree (f : ArithmeticFunction ℝ) (h_mult : IsMultiplicative f)
    (l d : ℕ) (hdl : d ∣ l) (hl : Squarefree l) (hd : f d ≠ 0) : f l / f d = f (l / d) := by
  apply div_eq_of_eq_mul hd
  rw [← h_mult.right, Nat.div_mul_cancel hdl]
  apply coprime_of_squarefree_mul
  convert hl
  exact Nat.div_mul_cancel hdl

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

theorem log_add_one_le_sum_inv (n : ℕ) :
    Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) :
    Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) :
    ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

-- Lemma 3.1 in Heath-Brown's notes
theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_ -- do we need this one?
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_

  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [← sum_filter, Finset.sum_const, ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      · intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d; rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]; exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤
      x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP


end Aux

end Erdos878PartVSieveAux

section Erdos878PartVAsymp

open Filter Asymptotics

private theorem isBigO_natCast {E : Type*} [Norm E] {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop

end Erdos878PartVAsymp

section Erdos878PartVSelberg

open scoped BigOperators Classical ArithmeticFunction.Moebius ArithmeticFunction.omega
open Finset Real Nat ArithmeticFunction BoundingSieve

namespace BoundingSieve

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

end BoundingSieve

namespace SelbergSieve

variable (s : SelbergSieve)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.prodPrimes, if l ^ 2 ≤ s.level then s.selbergTerms l else 0


theorem selbergBoundingSum_pos :
    0 < s.selbergBoundingSum := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply BoundingSieve.selbergTerms_pos (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : s.selbergBoundingSum ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ s.selbergBoundingSum := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * s.selbergTerms d * μ d * s.selbergBoundingSum⁻¹ *
      ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
  else 0

-- This notation traditionally uses λ, which is unavailable in lean

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    s.selbergWeights d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ s.level) :
    s.selbergWeights d = 0 := by
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
    0 ≤ s.selbergWeights d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (s.nu d)⁻¹ * s.selbergTerms d * s.selbergBoundingSum⁻¹ * ∑ m ∈ divisors s.prodPrimes,
          if (d * m) ^ 2 ≤ s.level ∧ Coprime m d then s.selbergTerms m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| BoundingSieve.selbergTerms_pos hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| BoundingSieve.selbergTerms_pos (dvd_of_mem_divisors hm)
  · rfl

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
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

--Important facts about the selberg weights
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * s.selbergWeights d =
      s.selbergBoundingSum⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes, if d ∣ l ∧ l ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
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
  -- change of variables l=m*d
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
      trans ((s.nu d)⁻¹ * (s.nu d) * s.selbergTerms d * μ d / s.selbergBoundingSum * s.selbergTerms m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * s.selbergWeights d else 0) =
      if l ^ 2 ≤ s.level then s.selbergTerms l * μ l * s.selbergBoundingSum⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * s.selbergWeights d else 0) =
        ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ s.level then s.selbergTerms k * s.selbergBoundingSum⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors s.prodPrimes, if k ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * s.selbergTerms k * s.selbergBoundingSum⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ s.level then s.selbergTerms l * μ l * s.selbergBoundingSum⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors s.prodPrimes) l (fun _ => if l^2 ≤ s.level then s.selbergTerms l * μ l * s.selbergBoundingSum⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ :=
  BoundingSieve.lambdaSquared s.selbergWeights


theorem weight_one_of_selberg : s.selbergWeights 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd s.prodPrimes), s.nu_mult.left, BoundingSieve.selbergTerms_isMultiplicative.map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ s.level) : s.selbergMuPlus d = 0 := by
  apply BoundingSieve.lambdaSquared_eq_zero_of_support _ s.level _ d hd
  apply s.selbergWeights_eq_zero

theorem selbergMuPlus_isUpperMoebius : BoundingSieve.IsUpperMoebius s.selbergMuPlus :=
  BoundingSieve.upperMoebius_lambdaSquared s.selbergWeights s.weight_one_of_selberg

-- proved for general lambda squared sieves
theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) s.selbergMuPlus =
      ∑ l ∈ divisors s.prodPrimes,
        (s.selbergTerms l)⁻¹ *
          (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * s.selbergWeights d else 0) ^ 2 :=
  by apply BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) s.selbergMuPlus = s.selbergBoundingSum⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors s.prodPrimes, (if l ^ 2 ≤ s.level then s.selbergTerms l * (s.selbergBoundingSum⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans ((s.selbergTerms l)⁻¹ * s.selbergTerms l * s.selbergTerms l * (μ l:ℝ)^2  * (s.selbergBoundingSum⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [inv_mul_cancel₀ <| _root_.ne_of_gt <| BoundingSieve.selbergTerms_pos <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors s.prodPrimes) (hm : m ∈ divisors s.prodPrimes) :
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
    s.selbergBoundingSum ≥ s.selbergWeights d * ↑(μ d) * s.selbergBoundingSum := by
  calc
  _ = (∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes, if k = d.gcd l ∧ l ^ 2 ≤ s.level then s.selbergTerms l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            s.selbergTerms k * ∑ m ∈ divisors s.prodPrimes, if (k * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
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
        apply BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime
        rw [Nat.gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors s.prodPrimes, if k ∣ d
          then s.selbergTerms k * ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| BoundingSieve.selbergTerms_pos <| hkd.trans hdP)
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
      · refine le_of_lt <| BoundingSieve.selbergTerms_pos <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| BoundingSieve.selbergTerms_pos <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
    trans (s.selbergBoundingSum * s.selbergBoundingSum⁻¹ * (μ d:ℝ)^2 * (s.nu d)⁻¹ * s.selbergTerms d * (∑ m ∈ divisors s.prodPrimes, if (d*m) ^ 2 ≤ s.level ∧
      Coprime m d then s.selbergTerms m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |s.selbergWeights d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*s.selbergBoundingSum ≥ s.selbergWeights d * ↑(μ d) * s.selbergBoundingSum := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : s.selbergWeights d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]


theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors s.prodPrimes) :
    |s.selbergMuPlus n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, BoundingSieve.lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then s.selbergWeights d1 * s.selbergWeights d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then s.selbergWeights d1 * s.selbergWeights d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then s.selbergWeights d1 * s.selbergWeights d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      exact (mul_le_of_le_one_left (abs_nonneg <| s.selbergWeights d2) (s.selberg_bound_weights d1)).trans
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum :
    errSum (s := s.toBoundingSieve) s.selbergMuPlus ≤
      ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |s.rem d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| s.rem d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple :
    siftedSum (s := s.toBoundingSieve) ≤
      s.totalMass / s.selbergBoundingSum +
        ∑ d ∈ divisors s.prodPrimes, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |s.rem d| else 0 := by
  calc
    siftedSum ≤ s.totalMass * mainSum s.selbergMuPlus + errSum s.selbergMuPlus :=
      BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius s.selbergMuPlus s.selbergMuPlus_isUpperMoebius
    _ ≤ _ := ?_
  gcongr
  · rw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve

end Erdos878PartVSelberg

section Erdos878PartVSelbergBounds

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

namespace Sieve

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
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

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2

theorem zeta_pos_of_prime : ∀ (p : ℕ), Nat.Prime p → (0:ℝ) < (↑ζ:ArithmeticFunction ℝ) p := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime : ∀ (p : ℕ), Nat.Prime p → (↑ζ:ArithmeticFunction ℝ) p < (p:ℝ) := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num;
  exact Nat.succ_le_iff.mp (Nat.Prime.two_le hp)

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

def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, one_ne_zero, ite_false,
    mul_eq_zero, Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_zero, mul_one,
    true_and, ← ite_or, or_comm, implies_true]

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
    constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simp_rw [pow_zero, hf.1]
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ) (hd : Squarefree d)
    (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, (1 - f p)⁻¹
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p ∈ d.primeFactors, (1 - f p)⁻¹
    = ∏ p ∈ d.primeFactors, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
        rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw [div_eq_mul_inv]
  _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p)^n  := by
    gcongr with p hp
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
    rw [← Finset.Ico_add_one_right_eq_Icc, geom_sum_Ico,
      ← mul_div_mul_left (c := (-1 : ℝ)) (f p ^ (M + 1) - f p ^ 1)]
    · gcongr
      · apply hf_nonneg
      · linarith [hf_size p hp.1 hp.2]
      · rw [pow_one]
        have : 0 ≤ f p ^ (M + 1) := by
          apply pow_nonneg
          apply hf_nonneg
        linarith only [this]
      · linarith only
    · norm_num
    · apply ne_of_lt <| hf_size p hp.1 hp.2
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)

  _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)
    = ∑ m ∈ (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]
        · push Not
          exact fun _ => hq
        · exact Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp q.2
        · exact (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_one
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
          (List.mem_toFinset.mp q.2)))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      refine ⟨?_, hd.ne_zero⟩
      trans q
      · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      · apply Nat.dvd_of_mem_primeFactorsList <| List.mem_toFinset.mp hq

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
      (List.mem_toFinset.mp p.property)))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d^M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero
      (hi_ne_zero a ha),← Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp <| Nat.prime_of_mem_primeFactorsList
      (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.ext hc)

  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp

  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => b.factorization p) ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push Not
        exact ⟨hpp.dvd_of_dvd_pow (h.trans hb.1.1), hd.ne_zero⟩
      · left; exact hpp

  exact Finset.sum_bij i hi i_inj i_surj h

theorem prod_primes_dvd_of_dvd (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  refine le_self_pow₀ hx ?right.h
  norm_num

lemma Nat.squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [Squarefree.dvd_pow_iff_dvd ha hN] at hab
  exact hab

/-
Proposed generalisation :

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1):
    s.selbergBoundingSum ≥ ∑ m in
      (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes),
      s.nu m
-/

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)
  (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1):
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m := by
  unfold selbergBoundingSum
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then BoundingSieve.selbergTerms l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [BoundingSieve.selbergTerms_apply]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg

  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hm
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos;
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    · have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor; constructor; constructor
      · apply prod_primes_dvd_of_dvd <;> intro p hp
        · apply hP p <| Nat.prime_of_mem_primeFactors hp
          trans (m:ℝ)
          · exact_mod_cast Nat.le_of_mem_primeFactors hp
          trans (Real.sqrt s.level)
          · exact hm.2
          apply sqrt_le_self s.level s.one_le_level
        exact Nat.prime_of_mem_primeFactors hp
      · exact prodPrimes_ne_zero
      · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
        · trans (m:ℝ)
          · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
            exact Nat.prod_primeFactors_dvd m
          exact hm.2
        apply le_of_lt; norm_cast
      constructor; constructor
      · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
        · intro p
          have hy_mul_prod_nonneg : 0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
            apply mul_nonneg
            · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
            · norm_num
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          rw [Finsupp.smul_apply, smul_eq_mul]
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · apply le_of_lt <| Nat.factorization_lt _ _
              apply hm_ne_zero
            apply Nat.le_floor
            refine le_trans hm.2 ?_
            apply sqrt_le_self _ s.one_le_level
          · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos, pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
        exact hm_ne_zero
      · exact hprod_ne_zero
      · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ) := by
  trans ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), (ζ : ArithmeticFunction ℝ).pdiv .id m
  · rw[←hnu]
    apply selbergBoundingSum_ge_sum_div
    · intro p hpp hple
      apply hP p hpp hple
    · rw[hnu]
      exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
    · intro n
      rw[hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp[h]
      simp
    · intro p hpp _
      rw[hnu]
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
        ArithmeticFunction.id_apply]
      rw [if_neg, one_div]
      · apply inv_lt_one_of_one_lt₀; norm_cast
        exact hpp.one_lt
      exact hpp.ne_zero
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
    ArithmeticFunction.id_apply];

theorem boundingSum_ge_log (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)  :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log <| Real.sqrt s.level)
  · rw [ge_iff_le]; simp_rw[one_div]
    apply Aux.log_le_sum_inv (Real.sqrt s.level)
    rw [Real.le_sqrt] <;> linarith[s.one_le_level]
  · apply ge_of_eq
    refine Real.log_sqrt ?h.hx
    linarith[s.one_le_level]

open ArithmeticFunction

theorem rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (by norm_num)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree

end Sieve

end Erdos878PartVSelbergBounds

section Erdos878PartVBrunTitchmarsh

open Sieve SelbergSieve BoundingSieve
open Filter Asymptotics
open scoped Nat ArithmeticFunction BigOperators ArithmeticFunction.zeta ArithmeticFunction.omega

namespace BrunTitchmarsh

/-- Sifting primes ≤ z from the interval [x, x+y] -/
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

/-- The number of primes in the interval [a, b] -/
def primesBetween (a b : ℝ) : ℕ :=
  (Finset.Icc (Nat.ceil a) (Nat.floor b)).filter Nat.Prime |>.card

variable (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 1 ≤ z)

open Classical in
theorem siftedSum_eq_card :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) =
      ((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
        (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  apply Sieve.siftedSum_eq
  · exact fun _ _ ↦ rfl
  · exact hz
  · rfl

open Classical in
theorem primesBetween_subset :
  (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter Nat.Prime ⊆
    (Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
      (Finset.Icc 1 (Nat.floor z)) := by
  intro p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Finset.mem_union, and_imp]
  intro hx hxy hp
  by_cases hpz : p ≤ z
  · right
    rw [Nat.le_floor_iff (by linarith)]
    have := hp.ne_zero
    exact ⟨by omega, hpz⟩
  · refine Or.inl ⟨⟨hx, hxy⟩, fun q hq hqz ↦ ?_⟩
    rw [hp.dvd_iff_eq (hq.ne_one)]
    rintro rfl
    exact hpz hqz

theorem primesBetween_le_siftedSum_add :
    primesBetween x (x+y) ≤
      siftedSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) + z := by
  classical
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d) ∪
      (Finset.Icc 1 (Nat.floor z))).card
  · rw [primesBetween]
    exact_mod_cast Finset.card_le_card (primesBetween_subset _ _ _)
  trans ↑((Finset.Icc (Nat.ceil x) (Nat.floor (x+y))).filter
      (fun d ↦ ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card +
      ↑(Finset.Icc 1 (Nat.floor z)).card
  · exact_mod_cast Finset.card_union_le _ _
  rw [siftedSum_eq_card]
  gcongr
  rw [Nat.card_Icc]
  simp only [add_tsub_cancel_right]
  apply Nat.floor_le
  linarith

section Remainder

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

include hx in
theorem multSum_eq (d : ℕ) (hd : d ≠ 0) :
    multSum (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) := by
  unfold multSum
  rw [primeInterSieve]
  simp only [Finset.sum_boole, Nat.cast_inj]
  trans ↑(Finset.Ioc (Nat.ceil x - 1) (Nat.floor (x+y)) |>.filter (d ∣ ·) |>.card)
  · rw [← Finset.Icc_add_one_left_eq_Ioc, Nat.sub_add_cancel (Nat.one_le_ceil_iff.mpr hx)]
  · rw [BrunTitchmarsh.card_Ioc_filter_dvd _ _ _ hd]

include hx in
theorem rem_eq (d : ℕ) (hd : d ≠ 0) :
    rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d =
      ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) - (↑d)⁻¹ * y := by
  unfold rem
  rw [multSum_eq x y z hx hz d hd]
  simp [primeInterSieve, if_neg hd]

theorem Nat.ceil_le_self_add_one (x : ℝ) (hx : 0 ≤ x) : Nat.ceil x ≤ x + 1 := by
  trans Nat.floor x + 1
  · exact_mod_cast Nat.ceil_le_floor_add_one x
  · gcongr
    exact Nat.floor_le hx

theorem floor_approx (x : ℝ) (hx : 0 ≤ x) :
    ∃ C, |C| ≤ 1 ∧ ↑((Nat.floor x)) = x + C := by
  use ↑(Nat.floor x) - x
  simp only [add_sub_cancel, and_true]
  rw [abs_le]
  refine ⟨by linarith [Nat.lt_floor_add_one x], by linarith [Nat.floor_le hx]⟩

theorem ceil_approx (x : ℝ) (hx : 0 ≤ x) : ∃ C, |C| ≤ 1 ∧ ↑((Nat.ceil x)) = x + C := by
  use ↑(Nat.ceil x) - x
  simp only [add_sub_cancel, and_true, abs_le]
  refine ⟨by linarith [Nat.le_ceil x], ?_⟩
  rw [tsub_le_iff_right, add_comm]
  exact Nat.ceil_le_self_add_one x hx

theorem nat_div_approx (a b : ℕ) : ∃ C, |C| ≤ 1 ∧ ↑(a/b) = (a/b : ℝ) + C := by
  rw [← Nat.floor_div_eq_div (K := ℝ)]
  exact floor_approx (a/b:ℝ) (by positivity)

theorem floor_div_approx (x : ℝ) (hx : 0 ≤ x) (d : ℕ) :
    ∃ C, |C| ≤ 2 ∧ ↑((Nat.floor x)/d) = x / d + C := by
  by_cases hd : d = 0
  · simp [hd]
  · obtain ⟨C₁, hC₁_le, hC₁⟩ := nat_div_approx (Nat.floor x) d
    obtain ⟨C₂, hC₂_le, hC₂⟩ := floor_approx x hx
    rw [hC₁, hC₂]
    refine ⟨C₁ + C₂/d, ?_, by ring⟩
    have : |C₁ + C₂/d| ≤ |C₁| + |C₂/d| := abs_add_le C₁ (C₂ / ↑d)
    have : |C₂/d| ≤ |C₂| := by
      rw [abs_div]
      refine div_le_self (abs_nonneg C₂) ?_
      simp only [Nat.abs_cast, Nat.one_le_cast]
      omega
    linarith

include hx hy in
theorem abs_rem_le {d : ℕ} (hd : d ≠ 0) :
    |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| ≤ 5 := by
  rw [rem_eq _ _ _ hx hz _ hd]
  have hpush : ↑(⌊x + y⌋₊ / d - (⌈x⌉₊ - 1) / d) =
      (↑(⌊x + y⌋₊ / d) - ↑((⌈x⌉₊ - 1) / d) : ℝ) := by
    rw [Nat.cast_sub]
    gcongr
    rw [Nat.le_floor_iff, ← add_le_add_iff_right 1]
    · rw_mod_cast [Nat.sub_add_cancel (by simp [hx])]
      linarith [Nat.ceil_le_self_add_one x (le_of_lt hx)]
    linarith
  rw [hpush]
  obtain ⟨C₁, hC₁_le, hC₁⟩ := floor_div_approx (x + y) (by linarith) d
  obtain ⟨C₂, hC₂_le, hC₂⟩ := nat_div_approx (Nat.ceil x - 1) d
  obtain ⟨C₃, hC₃_le, hC₃⟩ := ceil_approx (x) (by linarith)
  rw [hC₁, hC₂, Nat.cast_sub, hC₃]
  · ring_nf
    rw [(by ring_nf : |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + C₁ - C₂| = |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)|)]
    have : |(↑d)⁻¹ - (↑d)⁻¹ * C₃ + (C₁ - C₂)| ≤
        |(↑d)⁻¹ - (↑d)⁻¹ * C₃| + |C₁ - C₂| := abs_add_le _ _
    have : |(↑d)⁻¹ - (↑d)⁻¹ * C₃| ≤
        |(↑d)⁻¹| + |(↑d)⁻¹ * C₃| := abs_sub _ _
    have : |C₁ - C₂| ≤ |C₁| + |C₂| := abs_sub _ _
    have : |(d:ℝ)⁻¹| ≤ 1 := by
      rw [abs_inv, Nat.abs_cast]
      exact Nat.cast_inv_le_one _
    have : |(↑d)⁻¹ * C₃| ≤ |C₃| := by
      rw [inv_mul_eq_div, abs_div]
      refine div_le_self (abs_nonneg _) ?_
      rw [Nat.abs_cast, Nat.one_le_cast]
      omega
    linarith
  · simp [hx]

end Remainder

theorem boudingSum_ge : (primeInterSieve x y z hz).selbergBoundingSum ≥ Real.log z / 2 := by
  apply boundingSum_ge_log
  · exact rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff]
    · exact Nat.le_floor hp
    · exact hpp

include hx hy in
theorem primeSieve_rem_sum_le :
    ∑ d ∈ (primeInterSieve x y z hz).prodPrimes.divisors,
        (if (d : ℝ) ≤ z then (3:ℝ) ^ ω d *
          |rem (s := toBoundingSieve (self := primeInterSieve x y z hz)) d| else 0)
      ≤ 5 * z * (1 + Real.log z) ^ 3 := by
  refine rem_sum_le_of_const (primeInterSieve x y z hz) 5 (fun d hd ↦ ?_)
  apply abs_rem_le _ _ _ <;> linarith

include hx hy in
theorem siftedSum_le (hz : 1 < z) :
    siftedSum (s := toBoundingSieve (self := primeInterSieve x y z (le_of_lt hz)))
      ≤ 2 * y / Real.log z + 5 * z * (1 + Real.log z) ^ 3 := by
  apply le_trans (SelbergSieve.selberg_bound_simple ..)
  calc _ ≤ y / (Real.log z / 2) + 5 * z * (1 + Real.log z) ^ 3 := ?_
       _ = _ := by ring
  gcongr
  · linarith [Real.log_pos hz]
  · rfl
  · exact boudingSum_ge _ _ _ _
  · exact primeSieve_rem_sum_le x y z hx hy _

include hx hy in
theorem primesBetween_le (hz : 1 < z) :
    primesBetween x (x+y) ≤ 2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3 := by
  have : z ≤ z * (1 + Real.log z) ^ 3 := by
    apply le_mul_of_one_le_right
    · linarith
    · apply one_le_pow₀
      linarith [Real.log_nonneg (by linarith)]
  linarith [siftedSum_le _ _ _ hx hy hz, primesBetween_le_siftedSum_add x y z hz.le]

theorem primesBetween_one (n : ℕ) :
    primesBetween 1 n = ((Finset.range (n+1)).filter Nat.Prime).card := by
  rw [primesBetween]
  congr 1
  ext p
  simp only [Nat.ceil_one, Nat.floor_natCast, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
    and_congr_left_iff]
  exact fun hp ↦ ⟨fun h ↦ by omega,
    fun h ↦ ⟨by have := hp.pos; omega, by omega⟩⟩

theorem primesBetween_mono_right (a b c : ℝ) (hbc : b ≤ c) :
    primesBetween a b ≤ primesBetween a c := by
  dsimp only [primesBetween]
  refine Finset.card_le_card fun p ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, and_imp]
  exact fun ha hb hp ↦ ⟨⟨ha, hb.trans (Nat.floor_mono hbc)⟩, hp⟩

theorem tmp (N : ℕ) :
    ((Finset.range N).filter Nat.Prime).card ≤
      4 * (N / Real.log N) + 6 * (N ^ (1/2 : ℝ) * (1 + 1/2 * Real.log N) ^ 3) := by
  trans ↑((Finset.range (N+1)).filter Nat.Prime).card
  · norm_cast
    refine Finset.card_le_card fun n ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_range, and_imp]
    exact fun hnN hp ↦ ⟨by omega, hp⟩
  rw [← primesBetween_one]
  by_cases hN : N = 0
  · simp [hN, primesBetween]
  by_cases hN : N = 1
  · simp [hN, primesBetween]; rw [Finset.filter_singleton]; simp [Nat.not_prime_one]
  have h : primesBetween 1 (1 + N) ≤
      2 * (N / Real.log (N ^ (1/2 : ℝ))) +
        6 * (N ^ (1 / 2 : ℝ) * (1 + Real.log (N ^ (1/2 : ℝ))) ^ 3) := by
    convert (primesBetween_le 1 N (N ^ (1/2 : ℝ)) (by norm_num) (by norm_cast; omega)
      (Real.one_lt_rpow (by norm_cast; omega) (by norm_num))) using 1
    ring
  calc
    _ ≤ (primesBetween 1 (1+N):ℝ) := by
      norm_cast
      apply primesBetween_mono_right
      norm_cast
      omega
    _ ≤ _ := by
      rw [Real.log_rpow (by norm_num; omega)] at h
      convert h using 2
      ring

theorem rpow_mul_rpow_log_isBigO_id_div_log (k : ℝ) {r : ℝ} (hr : r < 1) :
    (fun x ↦ (x : ℝ) ^ (r : ℝ) * (Real.log x) ^ k) =O[atTop]
      (fun x ↦ x / Real.log x) := calc
  (fun x ↦ (x : ℝ) ^ (r : ℝ) * (Real.log x) ^ k) =O[atTop]
      (fun x ↦ (x : ℝ) ^ (r : ℝ) * x ^ ((1-r)/2 : ℝ)) := by
    apply IsBigO.mul (isBigO_refl ..)
    apply (isLittleO_log_rpow_rpow_atTop k (by linarith) ..).isBigO
  _ =ᶠ[atTop] (fun N ↦ (N : ℝ) * (N ^ ((1-r)/2 : ℝ))⁻¹) := by
    filter_upwards [Filter.eventually_gt_atTop 0]
    intro N hN
    trans (N ^ (1 : ℝ) * (N ^ ((1-r)/2 : ℝ))⁻¹)
    · rw [← Real.rpow_add hN, ← Real.rpow_neg hN.le, ← Real.rpow_add hN]
      ring_nf
    · rw [← Nat.cast_one, Real.rpow_natCast, pow_one]
  _ =O[atTop] (fun N ↦ (N : ℝ) * (Real.log N)⁻¹) := by
    apply IsBigO.mul (isBigO_refl ..)
    apply IsBigO.inv_rev
    · apply (isLittleO_log_rpow_atTop (by linarith) ..).isBigO
    · filter_upwards [Filter.eventually_gt_atTop 1]
      intro N hN hcontra
      linarith [Real.log_pos hN]
  _ = (fun N ↦ (N : ℝ)/(Real.log N)) := by
    simp_rw [div_eq_mul_inv]

theorem err_isBigO :
    (fun x ↦ (x ^ (1 / 2 : ℝ) * (1 + 1 / 2 * Real.log x) ^ 3)) =O[atTop]
      fun x ↦ (x / Real.log x) := by
  calc
    _ =O[atTop] (fun x ↦ x ^ (1/2:ℝ) * (Real.log x) ^ 3) := by
      apply IsBigO.mul (isBigO_refl ..)
        (Real.isLittleO_const_log_atTop.isBigO.add
          ((isBigO_refl ..).const_mul_left ..) |>.pow _)
    _ =O[atTop] _ := by
      convert rpow_mul_rpow_log_isBigO_id_div_log 3 (?_) <;> norm_num

theorem card_range_filter_prime_isBigO :
    (fun N ↦ ((Finset.range N).filter Nat.Prime).card : ℕ → ℝ) =O[atTop]
      (fun N ↦ N / Real.log N) := calc
  _ =O[atTop]
      (fun N ↦ 4 * (N / Real.log N) +
        6 * (N ^ (1/2 : ℝ) * (1 + 1/2 * Real.log N) ^ 3) : ℕ→ℝ) := by
    apply isBigO_of_le
    intro N
    simp only [RCLike.norm_natCast, one_div, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    convert tmp N using 4 <;> norm_num
    positivity
  _ =O[atTop] _ :=
    ((isBigO_refl ..).const_mul_left ..).add ((isBigO_natCast err_isBigO).const_mul_left _)

theorem prime_or_pow (N n : ℕ) (hnN : n < N) (hnprime : IsPrimePow n) :
    Nat.Prime n ∨ (∃ (m : ℕ), m < Real.sqrt N ∧ ∃ k ≤ Nat.log 2 N, n = m ^ k) := by
  rw [isPrimePow_nat_iff_bounded n] at hnprime
  obtain ⟨p, -, k, -, hp, hk_pos, hpkn⟩ := hnprime
  by_cases hk : k = 1
  · left
    rw [← hpkn, hk, pow_one]
    exact hp
  right
  refine ⟨p, ?_, k, ?_, ?_⟩
  · rw [Real.lt_sqrt]
    · norm_cast
      calc
        p ^ 2 ≤ p ^ k := by gcongr <;> [exact hp.one_le; omega]
      _ = n := hpkn
      _ < N := hnN
    · positivity
  · calc
      _ ≤ Nat.log p n := Nat.le_log_of_pow_le hp.one_lt hpkn.le
      _ ≤ Nat.log 2 n := Nat.log_anti_left (by norm_num) hp.two_le
      _ ≤ Nat.log 2 N := Nat.log_mono_right hnN.le
  · exact_mod_cast hpkn.symm

theorem range_filter_isPrimePow_subset_union (N : ℕ) :
    ((Finset.range N).filter IsPrimePow) ⊆ (Finset.range N).filter Nat.Prime ∪
      ((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image
        (fun p ↦ p.1 ^ p.2) := by
  intro n
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, Finset.mem_union,
    Finset.mem_image, Finset.mem_product, Prod.exists, and_imp]
  intro hnN hnprime
  rcases prime_or_pow N n hnN hnprime with hp | ⟨m, hm, k, hk, h⟩
  · left
    exact ⟨hnN, hp⟩
  · right
    refine ⟨m, k, ?_⟩
    by_cases hm : m = 0
    · rw [hm, zero_pow] at h
      · exact False.elim (hnprime.ne_zero h)
      · rintro rfl
        simp only [pow_zero] at h
        exact False.elim (hnprime.ne_one h)
    rw [Nat.lt_ceil, Nat.lt_succ_iff]
    have : 1 ≤ m := by omega
    aesop

theorem IsBigO.nat_Top_of_atTop (f g : ℕ → ℝ) (h : f =O[Filter.atTop] g)
    (h0 : ∀ n, g n = 0 → f n = 0) : f =O[⊤] g := by
  simp only [Asymptotics.isBigO_top, Real.norm_eq_abs]
  rw [Asymptotics.isBigO_atTop_iff_eventually_exists] at h
  simp only [ge_iff_le, Real.norm_eq_abs, Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  specialize hN N le_rfl
  obtain ⟨c, hc⟩ := hN
  let C := Finset.max' (insert c ((Finset.range N).image (fun n ↦ |f n| * |g n|⁻¹))) (by simp)
  refine ⟨C, fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · calc |f n| ≤ c * |g n| := hc n hn
      _ ≤ C * |g n| := by
        gcongr
        apply Finset.le_max'
        simp
  · by_cases hg : g n = 0
    · simp [hg, h0]
    rw [← mul_inv_le_iff₀]
    · apply Finset.le_max'
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_range]
      exact .inr ⟨n, by omega, rfl⟩
    · simp [hg]

theorem pows_small_primes_le (N : ℕ) :
    (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ Finset.range (Nat.log 2 N + 1)).image
      (fun p ↦ p.1 ^ p.2)).card ≤
        (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2) := calc
  _ ≤ (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
      Finset.range (Nat.log 2 N + 1)).card : ℝ) := by
    norm_cast
    exact Finset.card_image_le
  _ ≤ _ := by
    simp only [Finset.card_product, Nat.card_Ico, Finset.card_range, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one]
    by_cases hN : N = 0
    · simp [hN]
    have : 1 ≤ Nat.ceil (Real.sqrt N) := by
      simp only [Nat.one_le_ceil_iff, Real.sqrt_pos, Nat.cast_pos]
      omega
    gcongr ?_ * ?_
    · rw [← Real.sqrt_eq_rpow, Nat.cast_sub this, Nat.cast_one]
      have := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt N by positivity)
      linarith
    rw [← Real.natFloor_logb_natCast, Real.log_div_log, Nat.cast_two, add_comm,
      add_le_add_iff_left]
    apply Nat.floor_le
    apply Real.logb_nonneg one_lt_two
    norm_cast; omega

theorem one_add_log_div_log_two_isBigO :
    (fun N ↦ (1 + Real.log N / Real.log 2)) =O[atTop] (fun N ↦ Real.log N) := by
  refine IsBigO.add ?h₁ ?h₂
  · convert Real.isLittleO_const_log_atTop.isBigO
  simp_rw [div_eq_inv_mul]
  apply IsBigO.const_mul_left (isBigO_refl _ _)

theorem pow_half_mul_one_add_log_div_isBigO :
    (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2)) =O[Filter.atTop]
      (fun N ↦ N / Real.log N) := calc
  (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * (1 + Real.log N / Real.log 2)) =O[atTop]
      (fun N ↦ (N : ℝ) ^ (1/2 : ℝ) * Real.log N) := by
    apply IsBigO.mul
    · apply isBigO_refl
    apply one_add_log_div_log_two_isBigO
  _ =O[atTop] (fun N ↦ (N : ℝ)/(Real.log N)) := by
    convert rpow_mul_rpow_log_isBigO_id_div_log 1 (show 1/2 < (1:ℝ) by norm_num) using 1
    simp

theorem card_pows_aux :
    (fun N ↦ (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
      Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card : ℕ → ℝ) =O[atTop]
        fun N ↦ N / Real.log N := by
  apply IsBigO.trans ?_ (isBigO_natCast pow_half_mul_one_add_log_div_isBigO)
  apply isBigO_of_le
  intro N
  simp only [RCLike.norm_natCast, one_div, norm_mul, Real.norm_eq_abs]
  rw [Real.abs_rpow_of_nonneg (by positivity), Nat.abs_cast, abs_of_nonneg]
  · convert pows_small_primes_le N using 3
    norm_num
  by_cases hN : N = 0
  · simp [hN]
  rw [Real.log_div_log]
  linarith [Real.logb_nonneg (show 1 < (2:ℝ) by norm_num)
    (show (1 : ℝ) ≤ N by norm_num; omega)]

theorem card_isPrimePow_isBigO :
    (fun N ↦ (((Finset.range N).filter IsPrimePow).card:ℝ)) =O[atTop]
      (fun N ↦ N / Real.log N) := calc
  (fun N ↦ (((Finset.range N).filter IsPrimePow).card:ℝ)) =O[atTop]
      (fun N ↦ (((Finset.range N).filter Nat.Prime ∪
        ((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
          Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card:ℝ)) := by
    apply isBigO_of_le
    simp only [RCLike.norm_natCast, Nat.cast_le]
    exact fun N ↦ Finset.card_le_card (range_filter_isPrimePow_subset_union _)
  _ =O[atTop] fun N ↦ (((Finset.range N).filter Nat.Prime).card +
      (((Finset.Ico 1 (Nat.ceil (Real.sqrt N))) ×ˢ
        Finset.range (Nat.log 2 N + 1)).image (fun p ↦ p.1 ^ p.2)).card : ℝ) := by
    apply isBigO_of_le
    simp only [RCLike.norm_natCast, Real.norm_eq_abs]
    intro N
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast Finset.card_union_le _ _
  _ =O[atTop] fun N ↦ N / Real.log N :=
    IsBigO.add (card_range_filter_prime_isBigO) card_pows_aux

theorem card_range_filter_isPrimePow_le :
    ∃ C, ∀ N, ((Finset.range N).filter IsPrimePow).card ≤ C * (N / Real.log N) := by
  convert_to (fun N ↦ ((Finset.range N).filter IsPrimePow).card : ℕ → ℝ) =O[⊤]
      (fun N ↦ (N / Real.log N))
  · simp only [isBigO_top, RCLike.norm_natCast, norm_div, Real.norm_eq_abs]
    congr! 3 with C N
    by_cases hN : N = 0
    · simp [hN]
    rw [abs_of_nonneg]
    apply Real.log_nonneg
    norm_cast; omega
  apply IsBigO.nat_Top_of_atTop _ _ card_isPrimePow_isBigO
  have (a : ℕ) : (a : ℝ) ≠ -1 := by linarith [show 0 ≤ (a : ℝ) by positivity]
  simp [this, not_isPrimePow_zero]

end BrunTitchmarsh

end Erdos878PartVBrunTitchmarsh

section Erdos878PartVMain

open scoped BigOperators


namespace Erdos878PartV

noncomputable def residue (x p : ℕ) : ℝ :=
  Real.log x - (Nat.log p x : ℝ) * Real.log p

noncomputable def weight (x p : ℕ) : ℝ :=
  Real.exp (-residue x p) / p * (residue x p + Real.log p / ((p : ℝ) - 1))

noncomputable def primeCutoff (x : ℕ) : ℕ :=
  ⌊(Real.log (x : ℝ)) ^ 2⌋₊

def primeBases (x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter Nat.Prime

noncomputable def harmonicAnswer (x : ℕ) : ℝ :=
  (x : ℝ) * ∑ p ∈ primeBases (primeCutoff x), weight x p

end Erdos878PartV

namespace Erdos878PartV

private noncomputable def primeContribution (x p : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico 1 ⌈(x : ℝ) / p⌉₊, (p : ℝ) ^ Nat.log p m / m

private lemma one_div_succ_le_log_sub_le_one_div (m : ℕ) (hm : 0 < m) :
    1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log m ∧
      Real.log ((m : ℝ) + 1) - Real.log m ≤ 1 / (m : ℝ) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1' : 0 < (m : ℝ) + 1 := by positivity
  have h₁ := Real.log_le_sub_one_of_pos (div_pos hm' hm1')
  have h₂ := Real.log_le_sub_one_of_pos (div_pos hm1' hm')
  rw [Real.log_div hm'.ne' hm1'.ne'] at h₁
  rw [Real.log_div hm1'.ne' hm'.ne'] at h₂
  constructor
  · have he : (m : ℝ) / ((m : ℝ) + 1) - 1 = -(1 / ((m : ℝ) + 1)) := by
      field_simp
      ring
    linarith
  · have he : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
      field_simp
      ring
    linarith

private lemma harmonic_Ico_error {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ (∑ i ∈ Finset.Ico a b, 1 / (i : ℝ)) - (Real.log b - Real.log a) ∧
    (∑ i ∈ Finset.Ico a b, 1 / (i : ℝ)) - (Real.log b - Real.log a) ≤ 1 / (a : ℝ) := by
  have hl := Finset.sum_Ico_sub (fun i ↦ Real.log (i : ℝ)) hab
  have hi := Finset.sum_Ico_sub (fun i ↦ -(1 / (i : ℝ))) hab
  rw [← hl, ← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro i hi
    have hpos := ha.trans_le (Finset.mem_Ico.mp hi).1
    simpa only [Nat.cast_add, Nat.cast_one, sub_nonneg] using
      (one_div_succ_le_log_sub_le_one_div i hpos).2
  · calc
      _ ≤ ∑ i ∈ Finset.Ico a b, (-(1 / ((i + 1 : ℕ) : ℝ)) - -(1 / (i : ℝ))) := by
        apply Finset.sum_le_sum
        intro i hi
        have hpos := ha.trans_le (Finset.mem_Ico.mp hi).1
        have := (one_div_succ_le_log_sub_le_one_div i hpos).1
        push_cast
        linarith
      _ ≤ _ := by
        rw [hi]
        have : 0 ≤ 1 / (b : ℝ) := by positivity
        linarith

private lemma scaled_harmonic_error {a : ℕ} {y : ℝ} (ha : 0 < a) (hay : (a : ℝ) ≤ y) :
    |(a : ℝ) * (∑ i ∈ Finset.Ico a ⌈y⌉₊, 1 / (i : ℝ)) -
      (a : ℝ) * (Real.log y - Real.log a)| ≤ 2 := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have hy : 0 < y := ha'.trans_le hay
  have hceil := Nat.le_ceil y
  have hceil' : y ≤ (⌈y⌉₊ : ℝ) := hceil
  have hceilpos : 0 < (⌈y⌉₊ : ℝ) := hy.trans_le hceil'
  have hca : a ≤ ⌈y⌉₊ := by exact_mod_cast hay.trans hceil'
  have hl₁ : 0 ≤ Real.log (⌈y⌉₊ : ℝ) - Real.log y :=
    sub_nonneg.mpr (Real.log_le_log hy hceil')
  have hl₂ : Real.log (⌈y⌉₊ : ℝ) - Real.log y ≤ 1 / (a : ℝ) := by
    have hl := Real.log_le_sub_one_of_pos (div_pos hceilpos hy)
    rw [Real.log_div hceilpos.ne' hy.ne'] at hl
    refine hl.trans ?_
    calc
      (⌈y⌉₊ : ℝ) / y - 1 = ((⌈y⌉₊ : ℝ) - y) / y := by rw [sub_div, div_self hy.ne']
      _ ≤ 1 / y := by gcongr; linarith [Nat.ceil_lt_add_one hy.le]
      _ ≤ 1 / (a : ℝ) := one_div_le_one_div_of_le ha' hay
  rcases harmonic_Ico_error ha hca with ⟨h₁, h₂⟩
  have h₃ : 0 ≤ (∑ i ∈ Finset.Ico a ⌈y⌉₊, 1 / (i : ℝ)) -
      (Real.log y - Real.log a) := by linarith
  have h₄ : (∑ i ∈ Finset.Ico a ⌈y⌉₊, 1 / (i : ℝ)) -
      (Real.log y - Real.log a) ≤ 2 / (a : ℝ) := by
    rw [show (2 : ℝ) / a = 1 / a + 1 / a by ring]
    linarith
  rw [← mul_sub, abs_of_nonneg (mul_nonneg ha'.le h₃)]
  simpa [mul_div_cancel₀ _ ha'.ne'] using mul_le_mul_of_nonneg_left h₄ ha'.le

private lemma H_eq_sum_primeContribution (x : ℕ) :
    Erdos878.H x = ∑ p ∈ primeBases x, primeContribution x p := by
  classical
  unfold Erdos878.H
  calc
    _ = ∑ n ∈ Finset.Ico 1 x, ∑ p ∈ primeBases x with p ∣ n,
        (p : ℝ) ^ Nat.log p n / n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnr := Finset.mem_Ico.mp hn
      have hn0 : n ≠ 0 := by omega
      have hset : n.primeFactors = (primeBases x).filter (· ∣ n) := by
        ext p
        simp only [Nat.mem_primeFactors, Finset.mem_filter, primeBases, Finset.mem_range]
        constructor
        · rintro ⟨hp, hpn, _⟩
          exact ⟨⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn).trans_lt
            (hnr.2.trans (Nat.lt_succ_self x)), hp⟩, hpn⟩
        · rintro ⟨⟨_, hp⟩, hpn⟩
          exact ⟨hp, hpn, hn0⟩
      simp only [Erdos878.f, Nat.cast_sum, Nat.cast_pow, Finset.sum_div, hset]
    _ = ∑ p ∈ primeBases x, ∑ n ∈ Finset.Ico 1 x with p ∣ n,
        (p : ℝ) ^ Nat.log p n / n := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hprime : p.Prime := (Finset.mem_filter.mp hp).2
      have hp' : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
      have hlt (m : ℕ) : m < ⌈(x : ℝ) / p⌉₊ ↔ m * p < x := by
        rw [Nat.lt_ceil, lt_div_iff₀ hp']
        exact_mod_cast Iff.rfl
      unfold primeContribution
      symm
      refine Finset.sum_bij (fun m _ ↦ m * p) ?_ ?_ ?_ ?_
      · intro m hm
        have hmr := Finset.mem_Ico.mp hm
        refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, (hlt m).mp hmr.2⟩, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_le_iff.mp hmr.1) hprime.pos)
        · exact ⟨m, Nat.mul_comm m p⟩
      · intro m _ n _ heq
        exact Nat.eq_of_mul_eq_mul_right hprime.pos heq
      · intro n hn
        rcases Finset.mem_filter.mp hn with ⟨hn, m, rfl⟩
        have hnr := Finset.mem_Ico.mp hn
        refine ⟨m, Finset.mem_Ico.mpr ⟨?_, (hlt m).mpr (by simpa [Nat.mul_comm] using hnr.2)⟩,
          Nat.mul_comm m p⟩
        by_contra! hneg
        have hm : m = 0 := by omega
        simp [hm] at hnr
      · intro m hm
        have hmpos : 0 < m := Nat.succ_le_iff.mp (Finset.mem_Ico.mp hm).1
        have hm' : 0 < (m : ℝ) := by exact_mod_cast hmpos
        rw [Nat.log_mul_base hprime.one_lt hmpos.ne', Nat.cast_mul, pow_succ]
        field_simp

private noncomputable def harmonicBlock (p j b : ℕ) : ℝ :=
  (p : ℝ) ^ j * (∑ m ∈ Finset.Ico (p ^ j) b, 1 / (m : ℝ))

private lemma sum_power_block {p j b : ℕ} (hb : b ≤ p ^ (j + 1)) :
    (∑ m ∈ Finset.Ico (p ^ j) b, (p : ℝ) ^ Nat.log p m / m) =
      harmonicBlock p j b := by
  rw [harmonicBlock, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rcases Finset.mem_Ico.mp hm with ⟨hlo, hhi⟩
  rw [Nat.log_eq_of_pow_le_of_lt_pow hlo (hhi.trans_le hb)]
  ring

private lemma sum_full_blocks (p : ℕ) (hp : 1 < p) (k : ℕ) :
    (∑ m ∈ Finset.Ico 1 (p ^ k), (p : ℝ) ^ Nat.log p m / m) =
      ∑ j ∈ Finset.range k, harmonicBlock p j (p ^ (j + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp0 : 0 < p := by omega
    have hmono : p ^ k ≤ p ^ (k + 1) :=
      Nat.pow_le_pow_right hp0 (Nat.le_succ k)
    rw [← Finset.sum_Ico_consecutive _ (Nat.one_le_pow k p hp0) hmono,
      Finset.sum_range_succ, ih, sum_power_block le_rfl]

private lemma full_block_error {p : ℕ} (hp : 1 < p) (j : ℕ) :
    |harmonicBlock p j (p ^ (j + 1)) - (p : ℝ) ^ j * Real.log p| ≤ 1 := by
  have hpos : 0 < p := by omega
  have hpow : p ^ j ≤ p ^ (j + 1) := Nat.pow_le_pow_right hpos (Nat.le_succ j)
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hpos
  have hpj : 0 < (p : ℝ) ^ j := pow_pos hp' _
  have hl : Real.log (↑(p ^ (j + 1)) : ℝ) - Real.log (↑(p ^ j) : ℝ) = Real.log p := by
    simp only [Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
    ring
  obtain ⟨hlow, hupp⟩ := harmonic_Ico_error (pow_pos hpos j) hpow
  rw [hl] at hlow hupp
  push_cast at hupp
  rw [harmonicBlock, ← mul_sub, abs_of_nonneg (mul_nonneg hpj.le hlow)]
  simpa [hpj.ne'] using mul_le_mul_of_nonneg_left hupp hpj.le

private lemma primeContribution_error {x p : ℕ} (hp : 1 < p) (hpx : p ≤ x) :
    |primeContribution x p - (x : ℝ) * weight x p| ≤ (Nat.log p x : ℝ) + 2 := by
  let k : ℕ := Nat.log p x - 1
  let y : ℝ := (x : ℝ) / p
  have hp' : 1 < (p : ℝ) := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := zero_lt_one.trans hp'
  have hx0 : 0 < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hK : 0 < Nat.log p x := Nat.log_pos hp hpx
  have hk : k + 1 = Nat.log p x := by dsimp [k]; omega
  have hylo : (↑(p ^ k) : ℝ) ≤ y := by
    apply (le_div_iff₀ hp0).2
    have hn : p ^ (k + 1) ≤ x := by
      rw [hk]
      exact Nat.pow_log_le_self p (by omega)
    rw [pow_succ] at hn
    exact_mod_cast hn
  have hyhi : y ≤ (↑(p ^ (k + 1)) : ℝ) := by
    apply (div_le_iff₀ hp0).2
    have hn : x < p ^ ((k + 1) + 1) := by
      rw [hk]
      exact Nat.lt_pow_succ_log_self hp _
    rw [pow_succ] at hn
    exact_mod_cast hn.le
  have hs : primeContribution x p =
      (∑ j ∈ Finset.range k, harmonicBlock p j (p ^ (j + 1))) +
        harmonicBlock p k ⌈y⌉₊ := by
    unfold primeContribution
    change (∑ m ∈ Finset.Ico 1 ⌈y⌉₊, (p : ℝ) ^ Nat.log p m / m) = _
    rw [← Finset.sum_Ico_consecutive _ (Nat.one_le_pow k p (by omega))
      (show p ^ k ≤ ⌈y⌉₊ by exact_mod_cast hylo.trans (Nat.le_ceil y)),
      sum_full_blocks p hp k, sum_power_block (Nat.ceil_le.mpr hyhi)]
  have hr : Real.log y - Real.log (↑(p ^ k) : ℝ) = residue x p := by
    rw [residue, ← hk, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
    rw [show y = (x : ℝ) / p from rfl, Real.log_div hx0.ne' hp0.ne']
    ring
  have hpartial : |harmonicBlock p k ⌈y⌉₊ - (p : ℝ) ^ k * residue x p| ≤ 2 := by
    have h := scaled_harmonic_error (a := p ^ k) (pow_pos (by omega) k) hylo
    rw [hr, Nat.cast_pow] at h
    exact h
  have hfull : |(∑ j ∈ Finset.range k, harmonicBlock p j (p ^ (j + 1))) -
      ∑ j ∈ Finset.range k, (p : ℝ) ^ j * Real.log p| ≤ (k : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _j ∈ Finset.range k, (1 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ full_block_error hp j
      _ = _ := by simp
  have hphase : (∑ j ∈ Finset.range k, (p : ℝ) ^ j * Real.log p) +
      (p : ℝ) ^ k * residue x p = (x : ℝ) * weight x p - Real.log p / ((p : ℝ) - 1) := by
    have hexp : Real.exp (-residue x p) = (p : ℝ) ^ (k + 1) / x := by
      have hlog : -residue x p = Real.log ((p : ℝ) ^ (k + 1) / x) := by
        rw [residue, ← hk, Real.log_div (pow_ne_zero _ hp0.ne') hx0.ne', Real.log_pow]
        ring
      rw [hlog, Real.exp_log (by positivity)]
    rw [← Finset.sum_mul, geom_sum_eq hp'.ne' k, weight, hexp, pow_succ]
    field_simp
    ring
  have hshift : |Real.log p / ((p : ℝ) - 1)| ≤ 1 := by
    have hpos : 0 < (p : ℝ) - 1 := sub_pos.mpr hp'
    rw [abs_of_nonneg (div_nonneg (Real.log_nonneg hp'.le) hpos.le), div_le_iff₀ hpos]
    simpa using Real.log_le_sub_one_of_pos hp0
  have htotal : |primeContribution x p - ((x : ℝ) * weight x p -
      Real.log p / ((p : ℝ) - 1))| ≤ (k : ℝ) + 2 := by
    rw [hs, ← hphase, add_sub_add_comm]
    exact (abs_add_le _ _).trans (add_le_add hfull hpartial)
  calc
    _ ≤ |primeContribution x p - ((x : ℝ) * weight x p -
        Real.log p / ((p : ℝ) - 1))| + |Real.log p / ((p : ℝ) - 1)| := by
      rw [show primeContribution x p - (x : ℝ) * weight x p =
        (primeContribution x p - ((x : ℝ) * weight x p - Real.log p / ((p : ℝ) - 1))) -
          Real.log p / ((p : ℝ) - 1) by ring]
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (primeContribution x p - ((x : ℝ) * weight x p -
          Real.log p / ((p : ℝ) - 1))) (-(Real.log p / ((p : ℝ) - 1)))
    _ ≤ (k : ℝ) + 2 + 1 := add_le_add htotal hshift
    _ = _ := by rw [← hk, Nat.cast_add, Nat.cast_one]; ring

/-- Expanding the harmonic sum into its full prime-range phase sum costs at most
    the number of prime-power blocks plus two terms per prime. -/
theorem abs_H_sub_weight_le (x : ℕ) :
    |Erdos878.H x - (x : ℝ) * ∑ p ∈ primeBases x, weight x p| ≤
      ∑ p ∈ primeBases x, ((Nat.log p x : ℝ) + 2) := by
  rw [H_eq_sum_primeContribution, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp ↦ ?_)
  have hmem := Finset.mem_filter.mp hp
  exact primeContribution_error hmem.2.one_lt
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem.1))

end Erdos878PartV
open scoped BigOperators
open Filter Asymptotics
open Real Finset


namespace Erdos878PartV.Tail

/-- Exponent of the largest prime power in a logarithmic interval. -/
def exponent (L : ℝ) (p : ℕ) : ℕ := ⌊L / log p⌋₊

/-- Logarithm of the ratio between the endpoint and the largest prime power. -/
def phase (L : ℝ) (p : ℕ) : ℝ := L - (exponent L p : ℝ) * log p

private theorem phase_nonneg {L : ℝ} (hL : 0 ≤ L) {p : ℕ} (hp : 1 < p) :
    0 ≤ phase L p := by
  have hp' : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h := Nat.floor_le (div_nonneg hL hp'.le : 0 ≤ L / log (p : ℝ))
  exact sub_nonneg.mpr ((le_div_iff₀ hp').mp h)

private theorem phase_le {L : ℝ} {p : ℕ} (hp : 1 < p) : phase L p ≤ L := by
  have hp' : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.le)
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) hp')

private theorem exponent_pos {L : ℝ} {p : ℕ} (hp : 1 < p) (hpL : (p : ℝ) ≤ exp L) :
    0 < exponent L p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast (zero_lt_one.trans hp)
  have hlog : 0 < log (p : ℝ) := log_pos (by exact_mod_cast hp)
  have h : log (p : ℝ) ≤ L := by
    rw [← log_exp L]
    exact strictMonoOn_log.monotoneOn hp' (exp_pos _) hpL
  change 1 ≤ ⌊L / log (p : ℝ)⌋₊
  exact (Nat.le_floor_iff (div_nonneg (hlog.le.trans h) hlog.le)).mpr (by simpa using (le_div_iff₀ hlog).mpr (by simpa))

private theorem log_twice_le_log_prime {L : ℝ} (hL : 0 < L) {p : ℕ} (hp : L ^ 2 < p) :
    2 * log L < log (p : ℝ) := by
  have h := strictMonoOn_log (show 0 < L ^ 2 by positivity)
    (lt_trans (by positivity : 0 < L ^ 2) hp) hp
  simpa [log_pow] using h

private theorem exponent_le {L : ℝ} (hL : 1 < L) {p : ℕ} (hp : L ^ 2 < p) :
    exponent L p ≤ ⌊L / (2 * log L)⌋₊ := by
  have hh := log_twice_le_log_prime (zero_lt_one.trans hL) hp
  unfold exponent
  exact Nat.floor_mono (div_le_div_of_nonneg_left (zero_lt_one.trans hL).le (mul_pos (by norm_num) (log_pos hL)) hh.le)

/-- A uniform upper bound for the number of primes in a real interval. -/
theorem primeIntervalUpper :
    ∃ C > 0, ∃ A > 1, ∀ a h : ℝ, 0 < a → A ≤ h →
      (BrunTitchmarsh.primesBetween a (a + h) : ℝ) ≤ C * (h / log h) := by
  have hO := BrunTitchmarsh.err_isBigO
  obtain ⟨C, hCpos, hC⟩ := hO.exists_pos
  obtain ⟨A, hA⟩ := eventually_atTop.1 hC.bound
  refine ⟨4 + 6 * C, by positivity, max A 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro a h ha hah
  have hh : 1 < h := (lt_of_lt_of_le (by norm_num) (le_max_right A 2)).trans_le hah
  have hr : log (h ^ (1 / 2 : ℝ)) = 1 / 2 * log h := log_rpow (by positivity) _
  have hz : 1 < h ^ (1 / 2 : ℝ) := one_lt_rpow hh (by norm_num)
  have hB := BrunTitchmarsh.primesBetween_le a h (h ^ (1 / 2 : ℝ)) ha (by positivity) hz
  have hE := hA h ((le_max_left A 2).trans hah)
  have hhpos := zero_lt_one.trans hh
  have hlog := log_pos hh
  have hleft : 0 ≤ h ^ (1 / 2 : ℝ) * (1 + 1 / 2 * log h) ^ 3 := by positivity
  have hright : 0 ≤ h / log h := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] at hE
  rw [hr] at hB
  rw [show 2 * h / (1 / 2 * log h) = 4 * (h / log h) by ring] at hB
  calc
    _ ≤ 4 * (h / log h) + 6 * (h ^ (1 / 2 : ℝ) * (1 + 1 / 2 * log h) ^ 3) := by
      simpa only [mul_assoc] using hB
    _ ≤ _ := by linarith

private theorem window_geometry {L j k : ℝ} (hL : exp 1 ≤ L)
    (hj : j ≤ L / 2) (hk : 1 ≤ k) (hkL : k ≤ L / (2 * log L))
    {p : ℝ} (hp : L ^ 2 < p) (hpu : p ≤ exp ((L - j) / k)) :
    let t := (L - j) / k
    let h := exp t - exp (t - 1 / k)
    L ≤ h ∧ h ≤ exp t / k ∧ t / 2 ≤ log h ∧ 0 < t := by
  dsimp only
  have hLpos := (exp_pos 1).trans_le hL
  have hL1 : 1 < L := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hL
  have hlog : 1 ≤ log L := by
    rw [← log_exp 1]
    exact strictMonoOn_log.monotoneOn (exp_pos _) hLpos hL
  have ht : 0 < (L - j) / k := div_pos (by linarith) (lt_of_lt_of_le zero_lt_one hk)
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hw : 0 < 1 / k := by positivity
  have hw1 : 1 / k ≤ 1 := (div_le_iff₀ hkpos).mpr (by simpa)
  have hkw : 2 * k ≤ L := by
    have h1 := (le_div_iff₀ (by positivity : 0 < 2 * log L)).mp hkL
    nlinarith [mul_nonneg hkpos.le (sub_nonneg.mpr hlog)]
  let t := (L - j) / k
  let w := 1 / k
  have hlower : w / 2 ≤ 1 - exp (-w) := by
    have hE := add_one_le_exp w
    have hE' : exp (-w) * (w + 1) ≤ 1 := by
      rw [exp_neg]
      exact (inv_mul_le_iff₀ (exp_pos _)).mpr (by simpa using hE)
    have hpoly : 0 ≤ w * (1 - w) := mul_nonneg hw.le (sub_nonneg.mpr hw1)
    by_contra! hcontra
    have hmul := mul_lt_mul_of_pos_right hcontra (show 0 < w + 1 by positivity)
    nlinarith
  have hupper : 1 - exp (-w) ≤ w := by linarith [add_one_le_exp (-w)]
  have hh_eq : exp t - exp (t - w) = exp t * (1 - exp (-w)) := by
    rw [sub_eq_add_neg t w, exp_add]
    ring
  change L ≤ exp t - exp (t - w) ∧ exp t - exp (t - w) ≤ exp t / k ∧
    t / 2 ≤ log (exp t - exp (t - w)) ∧ 0 < t
  have hhlo : exp t / (2 * k) ≤ exp t - exp (t - w) := by
    rw [hh_eq, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
    have hw_eq : (2 * k)⁻¹ = w / 2 := by
      dsimp [w]
      field_simp
    rw [hw_eq]
    exact hlower
  have hpU : L ^ 2 < exp t := hp.trans_le hpu
  have hLL : L ≤ exp t / (2 * k) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hkw hLpos.le]
  have htlog : 2 * log L ≤ t := by
    have h := strictMonoOn_log (show 0 < L ^ 2 by positivity) (exp_pos t) hpU
    simpa [log_pow] using h.le
  have hUL : exp t / L ≤ exp t - exp (t - w) :=
    (div_le_div_of_nonneg_left (exp_nonneg _) (by positivity) hkw).trans hhlo
  refine ⟨hLL.trans hhlo, ?_, ?_, ht⟩
  · rw [hh_eq, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hupper (exp_nonneg _)
  · have hcomp := strictMonoOn_log.monotoneOn (show 0 < exp t / L by positivity)
      (hLpos.trans_le (hLL.trans hhlo)) hUL
    rw [log_div (exp_pos _).ne' hLpos.ne', log_exp] at hcomp
    linarith

private theorem window_mem {L : ℝ} {j k p : ℕ} (hk : 0 < k)
    (hL : 0 ≤ L) (hp : 1 < p)
    (hej : ⌊phase L p⌋₊ = j) (hek : exponent L p = k) :
    let t := (L - j) / k
    exp (t - 1 / k) < (p : ℝ) ∧ (p : ℝ) ≤ exp t := by
  dsimp only
  have hp' : (0 : ℝ) < p := by exact_mod_cast (zero_lt_one.trans hp)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 := Nat.floor_le (phase_nonneg hL hp)
  have h2 := Nat.lt_floor_add_one (phase L p)
  rw [hej, phase, hek] at h1 h2
  have h1' : log (p : ℝ) ≤ (L - j) / k := by
    apply (le_div_iff₀ hkr).mpr
    linarith
  have h2' : (L - j) / k - 1 / k < log (p : ℝ) := by
    rw [← sub_div]
    apply (div_lt_iff₀ hkr).mpr
    linarith
  exact ⟨by simpa [exp_log hp'] using exp_lt_exp.mpr h2',
    by simpa [exp_log hp'] using exp_le_exp.mpr h1'⟩

private theorem window_sum {C A : ℝ} (hC : 0 < C) (hA : 1 < A)
    (hB : ∀ a h : ℝ, 0 < a → A ≤ h →
      (BrunTitchmarsh.primesBetween a (a + h) : ℝ) ≤ C * (h / log h))
    {L : ℝ} (hL : exp 1 ≤ L) (hAL : A ≤ L)
    {j k : ℕ} (hj : (j : ℝ) ≤ L / 2)
    (hk : 0 < k) (hkL : (k : ℝ) ≤ L / (2 * log L))
    (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ L ^ 2 < (p : ℝ) ∧
      ⌊phase L p⌋₊ = j ∧ exponent L p = k) :
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ (4 * C * exp 1) / L := by
  have hLpos := (exp_pos 1).trans_le hL
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  let t := (L - j) / k
  let U := exp t
  let V := exp (t - 1 / k)
  let h := U - V
  have hinterval (p : ℕ) (hp : p ∈ s) : V < (p : ℝ) ∧ (p : ℝ) ≤ U := by
    obtain ⟨hpp, _, hpj, hpk⟩ := hs p hp
    exact window_mem hk hLpos.le hpp.one_lt hpj hpk
  by_cases hempty : s = ∅
  · simp [hempty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨hhL, hhU, hlog, ht⟩ := window_geometry hL hj (by exact_mod_cast hk) hkL
    (hs p hp).2.1 (hinterval p hp).2
  change L ≤ h at hhL
  change h ≤ U / k at hhU
  change t / 2 ≤ log h at hlog
  change 0 < t at ht
  have hhpos : 0 < h := hLpos.trans_le hhL
  have hlogpos : 0 < log h := (by positivity : 0 < t / 2).trans_le hlog
  have hp_bound : ∀ p ∈ s, (p : ℝ)⁻¹ ≤ exp 1 / U := by
    intro p hp
    have hw1 : (1 : ℝ) / k ≤ 1 := (div_le_iff₀ hkr).mpr (by simpa using (show (1 : ℝ) ≤ k by exact_mod_cast hk))
    have hlow : exp (t - 1) ≤ (p : ℝ) :=
      (exp_le_exp.mpr (by linarith)).trans (hinterval p hp).1.le
    rw [show exp 1 / U = (exp (t - 1))⁻¹ by
      dsimp [U]
      rw [exp_sub, inv_div]]
    simp only [← one_div]
    exact one_div_le_one_div_of_le (exp_pos _) hlow
  have hscard : s.card ≤ BrunTitchmarsh.primesBetween V U := by
    unfold BrunTitchmarsh.primesBetween
    refine card_le_card (fun p hp ↦ ?_)
    rw [mem_filter, mem_Icc, Nat.ceil_le, Nat.le_floor_iff (exp_nonneg _)]
    exact ⟨⟨(hinterval p hp).1.le, (hinterval p hp).2⟩, (hs p hp).1⟩
  have hcard := hB V h (exp_pos _) (hAL.trans hhL)
  rw [show V + h = U by dsimp [h]; ring] at hcard
  have hratio : h / log h ≤ (U / k) / (t / 2) := by
    exact (div_le_div_of_nonneg_right hhU hlogpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hlog)
  have hlast : (C * ((U / k) / (t / 2))) * (exp 1 / U) ≤ (4 * C * exp 1) / L := by
    have hstep : (C * ((U / k) / (t / 2))) * (exp 1 / U) =
        (2 * C * exp 1) / (L - j) := by
      have hUpos : 0 < U := exp_pos _
      have hLj : 0 < L - j := by linarith
      dsimp [t]
      field_simp
    rw [hstep, show (4 * C * exp 1) / L = (2 * C * exp 1) / (L / 2) by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  calc
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ ∑ _ ∈ s, exp 1 / U := Finset.sum_le_sum hp_bound
    _ = (s.card : ℝ) * (exp 1 / U) := by simp
    _ ≤ C * (h / log h) * (exp 1 / U) := by
      exact mul_le_mul_of_nonneg_right
        ((show (s.card : ℝ) ≤ BrunTitchmarsh.primesBetween V U by exact_mod_cast hscard).trans hcard)
        (by positivity)
    _ ≤ _ := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hC.le) (by positivity)).trans hlast

private theorem harmonic_bound {L : ℝ} (hL : 0 ≤ L) (s : Finset ℕ)
    (hs : ∀ p ∈ s, 0 < p ∧ (p : ℝ) ≤ exp L) :
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ 1 + L := by
  have hsubset : s ⊆ Icc 1 ⌊exp L⌋₊ := by
    intro p hp
    rw [mem_Icc, Nat.le_floor_iff (exp_nonneg _)]
    exact hs p hp
  calc
    ∑ p ∈ s, (p : ℝ)⁻¹ ≤ ∑ p ∈ Icc 1 ⌊exp L⌋₊, (p : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsubset (fun p _ _ ↦ by positivity)
    _ = (harmonic ⌊exp L⌋₊ : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + L := by
      simpa using harmonic_floor_le_one_add_log (exp L) (one_le_exp_iff.mpr hL)

private theorem weight_summable :
    Summable (fun j : ℕ ↦ (j + 1 : ℝ) * exp (-(j : ℝ))) := by
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 (by norm_num : (0 : ℝ) < 1)
  have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 1)
  simpa only [add_mul, pow_one, pow_zero, one_mul, neg_one_mul] using h1.add h0

private theorem phase_sum_low {C A : ℝ} (hC : 0 < C) (hA : 1 < A)
    (hB : ∀ a h : ℝ, 0 < a → A ≤ h →
      (BrunTitchmarsh.primesBetween a (a + h) : ℝ) ≤ C * (h / log h))
    {L : ℝ} (hL : exp 1 ≤ L) (hAL : A ≤ L) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ L ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ exp L ∧
      (⌊phase L p⌋₊ : ℝ) ≤ L / 2) :
    ∑ p ∈ s, exp (-phase L p) * phase L p / p ≤
      (2 * C * exp 1 * (∑' j : ℕ, (j + 1 : ℝ) * exp (-(j : ℝ)))) / log L := by
  have hLpos := (exp_pos 1).trans_le hL
  have hL1 : 1 < L := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hL
  have hlog : 0 < log L := log_pos hL1
  let K := ⌊L / (2 * log L)⌋₊
  let J := ⌊L / 2⌋₊
  let a (j : ℕ) := (j + 1 : ℝ) * exp (-(j : ℝ))
  let g (p : ℕ) := exp (-phase L p) * phase L p / p
  have ha (j : ℕ) : 0 ≤ a j := by dsimp [a]; positivity
  have hsum : 0 ≤ ∑' j, a j := tsum_nonneg ha
  have hk_mem (p : ℕ) (hp : p ∈ s) : exponent L p ∈ Icc 1 K := by
    obtain ⟨hpp, hp', hpL, _⟩ := hs p hp
    exact mem_Icc.mpr ⟨exponent_pos hpp.one_lt hpL, exponent_le hL1 hp'⟩
  have hbound_k (k : ℕ) (hk : k ∈ Icc 1 K) :
      ∑ p ∈ s with exponent L p = k, g p ≤
        (4 * C * exp 1) / L * (∑' j, a j) := by
    have hk1 : 0 < k := (mem_Icc.mp hk).1
    have hkL : (k : ℝ) ≤ L / (2 * log L) :=
      (Nat.le_floor_iff (by positivity)).mp (mem_Icc.mp hk).2
    let S := s.filter (fun p ↦ exponent L p = k)
    change ∑ p ∈ S, g p ≤ _
    have hj_mem (p : ℕ) (hp : p ∈ S) : ⌊phase L p⌋₊ ∈ range (J + 1) := by
      rw [mem_range, Nat.lt_succ_iff, Nat.le_floor_iff (by positivity)]
      exact (hs p (mem_filter.mp hp).1).2.2.2
    rw [← sum_fiberwise_of_maps_to hj_mem g]
    calc
      _ ≤ ∑ j ∈ range (J + 1), a j * ((4 * C * exp 1) / L) := by
        refine sum_le_sum (fun j hj ↦ ?_)
        let T := S.filter (fun p ↦ ⌊phase L p⌋₊ = j)
        change ∑ p ∈ T, g p ≤ _
        have hjL : (j : ℝ) ≤ L / 2 :=
          (Nat.le_floor_iff (show 0 ≤ L / 2 by positivity)).mp
            (Nat.lt_succ_iff.mp (mem_range.mp hj))
        have ht (p : ℕ) (hp : p ∈ T) :
            p.Prime ∧ L ^ 2 < (p : ℝ) ∧ ⌊phase L p⌋₊ = j ∧ exponent L p = k := by
          obtain ⟨hpS, hpj⟩ := mem_filter.mp hp
          obtain ⟨hps, hpk⟩ := mem_filter.mp hpS
          exact ⟨(hs p hps).1, (hs p hps).2.1, hpj, hpk⟩
        calc
          ∑ p ∈ T, g p ≤ ∑ p ∈ T, a j * (p : ℝ)⁻¹ := by
            refine sum_le_sum (fun p hp ↦ ?_)
            have h := ht p hp
            have hp0 : 0 ≤ phase L p := phase_nonneg hLpos.le h.1.one_lt
            have hjr : (j : ℝ) ≤ phase L p := by
              simpa only [h.2.2.1] using Nat.floor_le hp0
            have hrj : phase L p ≤ (j : ℝ) + 1 := by
              simpa only [h.2.2.1] using (Nat.lt_floor_add_one (phase L p)).le
            dsimp [g, a]
            rw [div_eq_mul_inv, mul_comm ((j : ℝ) + 1)]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul (exp_le_exp.mpr (by linarith)) hrj hp0 (by positivity))
              (by positivity)
          _ = a j * (∑ p ∈ T, (p : ℝ)⁻¹) := by rw [mul_sum]
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (window_sum hC hA hB hL hAL hjL hk1 hkL T ht) (ha _)
      _ = ((4 * C * exp 1) / L) * ∑ j ∈ range (J + 1), a j := by
        rw [mul_sum]
        exact sum_congr rfl (fun _ _ ↦ mul_comm _ _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (weight_summable.sum_le_tsum _ (fun j _ ↦ ha j)) (by positivity)
  have hK : (K : ℝ) ≤ L / (2 * log L) := Nat.floor_le (by positivity)
  change ∑ p ∈ s, g p ≤ _
  rw [← sum_fiberwise_of_maps_to hk_mem g]
  calc
    _ ≤ ∑ _ ∈ Icc 1 K, ((4 * C * exp 1) / L * (∑' j, a j)) := sum_le_sum hbound_k
    _ = (K : ℝ) * ((4 * C * exp 1) / L * (∑' j, a j)) := by simp [Nat.card_Icc]
    _ ≤ L / (2 * log L) * ((4 * C * exp 1) / L * (∑' j, a j)) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    _ = _ := by dsimp [a]; field_simp; ring

private theorem phase_sum_high {L : ℝ} (hL : 1 < L) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ exp L ∧ L / 2 ≤ phase L p) :
    ∑ p ∈ s, exp (-phase L p) * phase L p / p ≤ 96 / log L := by
  have hLpos := zero_lt_one.trans hL
  have hlog := log_pos hL
  have hstep : exp (-(L / 2)) * L * (1 + L) ≤ 96 / log L := by
    have hE := Real.pow_div_factorial_le_exp (L / 2) (by positivity) 3
    norm_num at hE
    have hp : L ^ 3 ≤ 48 * exp (L / 2) := by linarith
    have hlogL : log L ≤ L := Real.log_le_self hLpos.le
    rw [exp_neg]
    apply (le_div_iff₀ hlog).mpr
    have hpoly : L * (1 + L) * log L ≤ 2 * L ^ 3 := by
      calc
        _ ≤ L * (2 * L) * L := by gcongr; linarith
        _ = _ := by ring
    calc
      _ = (exp (L / 2))⁻¹ * (L * (1 + L) * log L) := by ring
      _ ≤ (exp (L / 2))⁻¹ * (96 * exp (L / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ p ∈ s, (exp (-(L / 2)) * L) * (p : ℝ)⁻¹ := by
      refine sum_le_sum (fun p hp ↦ ?_)
      have h := hs p hp
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (exp_le_exp.mpr (by linarith [h.2.2]))
          (phase_le h.1.one_lt) (phase_nonneg hLpos.le h.1.one_lt) (by positivity))
        (by positivity)
    _ = (exp (-(L / 2)) * L) * (∑ p ∈ s, (p : ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ exp (-(L / 2)) * L * (1 + L) :=
      mul_le_mul_of_nonneg_left
        (harmonic_bound hLpos.le s (fun p hp ↦ ⟨(hs p hp).1.pos, (hs p hp).2.1⟩))
        (by positivity)
    _ ≤ _ := hstep

private theorem correction_sum {L : ℝ} (hL : 1 < L) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ L ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ exp L) :
    ∑ p ∈ s, exp (-phase L p) / p * (log (p : ℝ) / ((p : ℝ) - 1)) ≤
      32 / log L := by
  have hLpos := zero_lt_one.trans hL
  have hlog := log_pos hL
  have hLlog : 0 < L * log L := by positivity
  have hterm (p : ℕ) (hp : p ∈ s) :
      log (p : ℝ) / ((p : ℝ) - 1) ≤ 16 / (L * log L) := by
    obtain ⟨hpp, hpL, _⟩ := hs p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hplog : 0 < log (p : ℝ) := log_pos (by linarith)
    have hlog2 := log_twice_le_log_prime hLpos hpL
    let q := exp (log (p : ℝ) / 2)
    have hq : L ≤ q := by
      rw [← exp_log hLpos]
      exact exp_le_exp.mpr (by linarith)
    have hqpos : 0 < q := exp_pos _
    have hq2 : q * q = p := by
      dsimp [q]
      rw [← exp_add, show log (p : ℝ) / 2 + log (p : ℝ) / 2 = log (p : ℝ) by ring]
      exact exp_log (by linarith)
    have hE := Real.pow_div_factorial_le_exp (log (p : ℝ) / 2) (by positivity) 2
    change (log (p : ℝ) / 2) ^ 2 / (Nat.factorial 2 : ℝ) ≤ q at hE
    norm_num at hE
    have hpoly : log (p : ℝ) * (L * log L) ≤ 8 * (p : ℝ) := by
      calc
        _ = log (p : ℝ) * log L * L := by ring
        _ ≤ log (p : ℝ) * log (p : ℝ) * L :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hplog.le) hLpos.le
        _ ≤ 8 * q * L :=
          mul_le_mul_of_nonneg_right (by nlinarith) hLpos.le
        _ ≤ 8 * q * q :=
          mul_le_mul_of_nonneg_left hq (by positivity)
        _ = _ := by rw [mul_assoc, hq2]
    exact (div_le_div_iff₀ (by linarith) hLlog).mpr (by linarith)
  calc
    _ ≤ ∑ p ∈ s, (16 / (L * log L)) * (p : ℝ)⁻¹ := by
      refine sum_le_sum (fun p hp ↦ ?_)
      have hpp := (hs p hp).1
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      have hphase := phase_nonneg hLpos.le hpp.one_lt
      have hexp : exp (-phase L p) ≤ 1 := exp_le_one_iff.mpr (by linarith)
      rw [div_eq_mul_inv, mul_right_comm]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa using mul_le_mul hexp (hterm p hp)
        (by positivity : 0 ≤ log (p : ℝ) / ((p : ℝ) - 1)) (by positivity)
    _ = (16 / (L * log L)) * (∑ p ∈ s, (p : ℝ)⁻¹) := by rw [mul_sum]
    _ ≤ (16 / (L * log L)) * (1 + L) :=
      mul_le_mul_of_nonneg_left
        (harmonic_bound hLpos.le s (fun p hp ↦ ⟨(hs p hp).1.pos, (hs p hp).2.2⟩))
        (by positivity)
    _ ≤ (16 / (L * log L)) * (2 * L) := by gcongr; linarith
    _ = _ := by field_simp; ring

private theorem all_tail_bound :
    ∃ C > 0, ∃ A : ℝ, ∀ L ≥ A, ∀ (s : Finset ℕ),
      (∀ p ∈ s, p.Prime ∧ L ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ exp L) →
      ∑ p ∈ s, exp (-phase L p) / p * (phase L p + log (p : ℝ) / ((p : ℝ) - 1)) ≤
        C / log L := by
  obtain ⟨C, hC, A, hA, hB⟩ := primeIntervalUpper
  let B := 2 * C * exp 1 * (∑' j : ℕ, (j + 1 : ℝ) * exp (-(j : ℝ)))
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑' j : ℕ, (j + 1 : ℝ) * exp (-(j : ℝ)) := tsum_nonneg (fun j ↦ by positivity)
    dsimp [B]
    positivity
  refine ⟨B + 128, by positivity, max A (exp 1), ?_⟩
  intro L hL s hs
  have hAL := (le_max_left A (exp 1)).trans hL
  have hL1 := (le_max_right A (exp 1)).trans hL
  have hLgt : 1 < L := (one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le hL1
  have hLpos := zero_lt_one.trans hLgt
  let P (p : ℕ) := (⌊phase L p⌋₊ : ℝ) ≤ L / 2
  let g (p : ℕ) := exp (-phase L p) * phase L p / p
  have hlo : ∀ p ∈ s.filter P, p.Prime ∧ L ^ 2 < (p : ℝ) ∧
      (p : ℝ) ≤ exp L ∧ (⌊phase L p⌋₊ : ℝ) ≤ L / 2 := by
    intro p hp
    obtain ⟨hps, hpP⟩ := mem_filter.mp hp
    obtain ⟨ha, hb, hc⟩ := hs p hps
    exact ⟨ha, hb, hc, hpP⟩
  have hhi : ∀ p ∈ s.filter (fun p ↦ ¬ P p),
      p.Prime ∧ (p : ℝ) ≤ exp L ∧ L / 2 ≤ phase L p := by
    intro p hp
    obtain ⟨hps, hpP⟩ := mem_filter.mp hp
    obtain ⟨ha, _, hc⟩ := hs p hps
    exact ⟨ha, hc, (lt_of_not_ge hpP).le.trans (Nat.floor_le (phase_nonneg hLpos.le ha.one_lt))⟩
  have hsplit : ∑ p ∈ s, g p ≤ (B + 96) / log L := by
    rw [← sum_filter_add_sum_filter_not s P g, add_div]
    exact add_le_add (phase_sum_low hC hA hB hL1 hAL _ hlo) (phase_sum_high hLgt _ hhi)
  calc
    ∑ p ∈ s, exp (-phase L p) / p * (phase L p + log (p : ℝ) / ((p : ℝ) - 1)) =
        ∑ p ∈ s, g p + ∑ p ∈ s, exp (-phase L p) / p * (log (p : ℝ) / ((p : ℝ) - 1)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun _ _ ↦ by dsimp [g]; ring)
    _ ≤ (B + 96) / log L + 32 / log L := add_le_add hsplit (correction_sum hLgt s hs)
    _ = _ := by ring

private theorem phase_eq_residue (x p : ℕ) : phase (log (x : ℝ)) p = Erdos878PartV.residue x p := by
  unfold phase Erdos878PartV.residue exponent
  rw [← Real.logb, Real.natFloor_logb_natCast]

end Erdos878PartV.Tail

namespace Erdos878PartV

/-- The normalized contribution from primes above the square-logarithm cutoff. -/
theorem primeTail_isBigO :
    (fun x : ℕ ↦ ∑ p ∈ (primeBases x).filter (primeCutoff x < ·), weight x p)
      =O[atTop] (fun x : ℕ ↦ (Real.log (Real.log (x : ℝ)))⁻¹) := by
  obtain ⟨C, hC, A, hA⟩ := Tail.all_tail_bound
  refine Asymptotics.IsBigO.of_bound C ?_
  have hlog : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlog.eventually_ge_atTop (max A 2)
  filter_upwards [hlarge, Filter.eventually_ge_atTop 1] with x hx hx1
  let L := Real.log (x : ℝ)
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x from hx1)
  have hL : 1 < L := (by norm_num : (1 : ℝ) < 2).trans_le ((le_max_right A 2).trans hx)
  let s := (primeBases x).filter (primeCutoff x < ·)
  have hs (p : ℕ) (hp : p ∈ s) : p.Prime ∧ L ^ 2 < (p : ℝ) ∧ (p : ℝ) ≤ exp L := by
    obtain ⟨hp', hpC⟩ := mem_filter.mp hp
    have hpx : p ≤ x := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp').1)
    obtain ⟨_, hpp⟩ := mem_filter.mp hp'
    refine ⟨hpp, (Nat.floor_lt (sq_nonneg L)).mp hpC, ?_⟩
    rw [show exp L = (x : ℝ) from Real.exp_log hxpos]
    exact_mod_cast hpx
  have h := hA L ((le_max_left A 2).trans hx) s hs
  dsimp only [L] at h
  simp_rw [Tail.phase_eq_residue] at h
  change ‖∑ p ∈ s, weight x p‖ ≤ C * ‖(Real.log L)⁻¹‖
  have hnonneg : 0 ≤ ∑ p ∈ s, weight x p := by
    refine sum_nonneg (fun p hp ↦ ?_)
    have hpp := (hs p hp).1.one_lt
    have hpp' : (1 : ℝ) < p := by exact_mod_cast hpp
    have hr : 0 ≤ residue x p := by
      rw [← Tail.phase_eq_residue]
      exact Tail.phase_nonneg (zero_lt_one.trans hL).le hpp
    unfold weight
    positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (inv_nonneg.mpr (log_pos hL).le), ← div_eq_mul_inv]
  exact h


end Erdos878PartV
open Filter Asymptotics
open scoped Topology

namespace Erdos878PartV

private lemma mem_primeBases {x p : ℕ} : p ∈ primeBases x ↔ p.Prime ∧ p ≤ x := by
  unfold primeBases
  simp [and_comm]

private lemma sum_log_le_card_primePowers (x : ℕ) :
    ∑ p ∈ primeBases x, Nat.log p x ≤ ((Finset.range (x + 1)).filter IsPrimePow).card := by
  classical
  let pairs : Finset (Σ _ : ℕ, ℕ) :=
    (primeBases x).sigma (fun p ↦ Finset.Icc 1 (Nat.log p x))
  have hc : pairs.card = ∑ p ∈ primeBases x, Nat.log p x := by
    simp [pairs, Finset.card_sigma, Nat.card_Icc]
  rw [← hc]
  apply Finset.card_le_card_of_injOn (fun z : Σ _ : ℕ, ℕ ↦ z.1 ^ z.2)
  · rintro ⟨p, k⟩ hz
    simp only [pairs, Finset.mem_coe, Finset.mem_sigma, mem_primeBases, Finset.mem_Icc] at hz
    have hpow : p ^ k ≤ x := Nat.pow_le_of_le_log (hz.1.1.pos.trans_le hz.1.2).ne' hz.2.2
    change p ^ k ∈ (Finset.range (x + 1)).filter IsPrimePow
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), (isPrimePow_nat_iff _).2 ⟨p, k, hz.1.1, hz.2.1, rfl⟩⟩
  · rintro ⟨p, j⟩ h₁ ⟨q, k⟩ h₂ he
    simp only [pairs, Finset.mem_coe, Finset.mem_sigma, mem_primeBases, Finset.mem_Icc] at h₁ h₂
    change p ^ j = q ^ k at he
    have hd : p ∣ q ^ k := he ▸ dvd_pow_self _ (by omega)
    have hpq : p = q := (Nat.dvd_prime h₂.1.1).mp (h₁.1.1.dvd_of_dvd_pow hd) |>.resolve_left h₁.1.1.ne_one
    subst q
    have hjk : j = k := (pow_right_strictMono₀ h₁.1.1.one_lt).injective he
    subst k
    rfl

private lemma regroup_error_isLittleO :
    (fun x : ℕ ↦ ∑ p ∈ primeBases x, ((Nat.log p x : ℝ) + 2)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := by
  have hsucc : Tendsto (fun x : ℕ ↦ x + 1) atTop atTop :=
    tendsto_atTop_mono (fun x ↦ Nat.le_succ x) tendsto_id
  have hp := BrunTitchmarsh.card_isPrimePow_isBigO.comp_tendsto hsucc
  have hl : (fun x : ℕ ↦ ((x + 1 : ℕ) : ℝ) / Real.log ((x + 1 : ℕ) : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := by
    have hcast : Tendsto (fun x : ℕ ↦ ((x + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hsucc
    have hinv : (fun x : ℕ ↦ (Real.log ((x + 1 : ℕ) : ℝ))⁻¹) =o[atTop] (fun _ ↦ (1 : ℝ)) := by
      have ht := (tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hcast))
      exact (isLittleO_one_iff ℝ).2 (by simpa [Function.comp_def] using ht)
    have hlin : (fun x : ℕ ↦ ((x + 1 : ℕ) : ℝ)) =O[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
      apply Asymptotics.IsBigO.of_bound 2
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with x hx
      simp only [Real.norm_natCast, Nat.cast_add, Nat.cast_one]
      rw [Real.norm_of_nonneg (by positivity)]
      have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
      linarith
    simpa [div_eq_mul_inv] using hlin.mul_isLittleO hinv
  have hsum : (fun x : ℕ ↦ ∑ p ∈ primeBases x, ((Nat.log p x : ℝ) + 2)) =O[atTop]
      (fun x : ℕ ↦ (((Finset.range (x + 1)).filter IsPrimePow).card : ℝ)) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity), Real.norm_natCast]
    calc
      _ ≤ ∑ p ∈ primeBases x, 3 * (Nat.log p x : ℝ) := by
        apply Finset.sum_le_sum
        intro p hmem
        obtain ⟨hp', hpx⟩ := mem_primeBases.mp hmem
        have hle : 1 ≤ Nat.log p x := Nat.log_pos_iff.mpr ⟨hpx, hp'.one_lt⟩
        have : (1 : ℝ) ≤ Nat.log p x := by exact_mod_cast hle
        linarith
      _ ≤ _ := by
        rw [← Finset.mul_sum, ← Nat.cast_sum]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast sum_log_le_card_primePowers x) (by norm_num)
  exact hsum.trans_isLittleO (hp.trans_isLittleO hl)

private lemma residue_bounds {x p : ℕ} (hp : p.Prime) (hpx : p ≤ x) :
    0 ≤ residue x p ∧ residue x p < Real.log p := by
  have hx : 0 < x := hp.pos.trans_le hpx
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hl := Nat.pow_log_le_self p hx.ne'
  have hu := Nat.lt_pow_succ_log_self hp.one_lt x
  have hl' : (p : ℝ) ^ Nat.log p x ≤ x := by exact_mod_cast hl
  have hu' : (x : ℝ) < (p : ℝ) ^ (Nat.log p x + 1) := by exact_mod_cast hu
  have ha := Real.log_le_log (by positivity) hl'
  have hb := Real.log_lt_log (by exact_mod_cast hx) hu'
  rw [Real.log_pow] at ha hb
  push_cast at ha hb
  unfold residue
  constructor <;> linarith

private lemma eventually_cutoff_bounds : ∀ᶠ x : ℕ in atTop, 2 ≤ primeCutoff x ∧ primeCutoff x ≤ x := by
  have ht := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog := (isLittleO_log_rpow_atTop (show 0 < (1 / 2 : ℝ) by norm_num)).comp_tendsto
    (show Tendsto (fun x : ℕ ↦ (x : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)
  filter_upwards [ht.eventually (eventually_ge_atTop (2 : ℝ)), hlog.bound (by norm_num : (0 : ℝ) < 1)] with x hx h
  change 2 ≤ Real.log (x : ℝ) at hx
  have hpos : 0 ≤ Real.log (x : ℝ) := by linarith
  simp only [Function.comp_apply, Real.norm_eq_abs, one_mul, ← Real.sqrt_eq_rpow,
    abs_of_nonneg hpos, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  unfold primeCutoff
  constructor
  · apply (Nat.le_floor_iff (by positivity)).2
    norm_num
    nlinarith
  · exact_mod_cast (Nat.floor_le (sq_nonneg (Real.log (x : ℝ)))).trans
      (calc Real.log (x : ℝ) ^ 2 ≤ Real.sqrt x ^ 2 := by gcongr
            _ = (x : ℝ) := Real.sq_sqrt (by positivity))

private lemma id_isBigO_harmonicAnswer :
    (fun x : ℕ ↦ (x : ℝ)) =O[atTop] harmonicAnswer := by
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Asymptotics.IsBigO.of_bound (4 / Real.log 2)
  filter_upwards [eventually_cutoff_bounds] with x hx
  have ht : 2 ∈ primeBases (primeCutoff x) := mem_primeBases.mpr ⟨Nat.prime_two, hx.1⟩
  have hn : ∀ p ∈ primeBases (primeCutoff x), 0 ≤ weight x p := by
    intro p hp
    obtain ⟨hpp, hpx⟩ := mem_primeBases.mp hp
    have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
    have hp₁ : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have hr := (residue_bounds hpp (hpx.trans hx.2)).1
    unfold weight
    positivity
  have hr := residue_bounds Nat.prime_two (hx.1.trans hx.2)
  have hres : residue x 2 < Real.log 2 := by exact_mod_cast hr.2
  have hexp : (1 / 2 : ℝ) ≤ Real.exp (-residue x 2) := by
    have hl := Real.exp_le_exp.mpr (show -Real.log 2 ≤ -residue x 2 by linarith)
    rwa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), inv_eq_one_div] at hl
  have htwo : Real.log 2 / 4 ≤ weight x 2 := by
    unfold weight
    norm_num
    calc
      Real.log 2 / 4 = ((1 / 2 : ℝ) / 2) * Real.log 2 := by ring
      _ ≤ _ := by gcongr; linarith [hr.1]
  have hsum : (x : ℝ) * (Real.log 2 / 4) ≤ harmonicAnswer x := by
    unfold harmonicAnswer
    exact mul_le_mul_of_nonneg_left (htwo.trans (Finset.single_le_sum hn ht)) (by positivity)
  have hnonneg : 0 ≤ harmonicAnswer x := le_trans (by positivity) hsum
  rw [Real.norm_natCast, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog₂]
  linarith

/-- The truncated prime sum is an asymptotic equivalent for the average in part (v). -/
theorem part_v : Erdos878.H ~[atTop] harmonicAnswer := by
  change (Erdos878.H - harmonicAnswer) =o[atTop] harmonicAnswer
  apply IsLittleO.trans_isBigO _ id_isBigO_harmonicAnswer
  let full (x : ℕ) : ℝ := (x : ℝ) * ∑ p ∈ primeBases x, weight x p
  have hregroup : (Erdos878.H - full) =o[atTop] (fun x : ℕ ↦ (x : ℝ)) := by
    apply IsBigO.trans_isLittleO _ regroup_error_isLittleO
    apply isBigO_of_le
    intro x
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    exact (abs_H_sub_weight_le x).trans (le_abs_self _)
  have hinv : (fun x : ℕ ↦ (Real.log (Real.log (x : ℝ)))⁻¹) =o[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)) := by
    have ht := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact (isLittleO_one_iff ℝ).2 (by simpa [Function.comp_def] using tendsto_inv_atTop_zero.comp ht)
  have htail := (isBigO_refl (fun x : ℕ ↦ (x : ℝ)) atTop).mul_isLittleO
    (primeTail_isBigO.trans_isLittleO hinv)
  have heq : (full - harmonicAnswer) =ᶠ[atTop]
      (fun x : ℕ ↦ (x : ℝ) * ∑ p ∈ (primeBases x).filter (primeCutoff x < ·), weight x p) := by
    classical
    filter_upwards [eventually_cutoff_bounds] with x hx
    have hfilter : (primeBases x).filter (fun p ↦ ¬primeCutoff x < p) = primeBases (primeCutoff x) := by
      ext p
      simp only [Finset.mem_filter, mem_primeBases, not_lt]
      exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, h.2.trans hx.2⟩, h.2⟩⟩
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := primeBases x)
      (p := (primeCutoff x < ·)) (f := weight x)
    rw [hfilter] at hsplit
    simp only [Pi.sub_apply, full, harmonicAnswer]
    rw [← hsplit]
    ring
  have hadd : (fun x ↦ (Erdos878.H - full) x + (full - harmonicAnswer) x) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ)) := by
    apply hregroup.add
    simpa using (htail.congr' heq.symm EventuallyEq.rfl)
  change (fun x ↦ Erdos878.H x - harmonicAnswer x) =o[atTop] (fun x : ℕ ↦ (x : ℝ))
  simpa [sub_add_sub_cancel] using hadd

end Erdos878PartV

end Erdos878PartVMain

end

noncomputable def OMA.answer : ℕ → ℝ := fun x ↦
  (x : ℝ) * ∑ p ∈ (Finset.range (⌊(Real.log (x : ℝ)) ^ 2⌋₊ + 1)).filter Nat.Prime,
    Real.exp (-(Real.log (x : ℝ) - (Nat.log p x : ℝ) * Real.log (p : ℝ))) / (p : ℝ) *
      (Real.log (x : ℝ) - (Nat.log p x : ℝ) * Real.log (p : ℝ) +
        Real.log (p : ℝ) / ((p : ℝ) - 1))

theorem OMA.solution : Erdos878.erdos_878.parts.v.answer = OMA.answer → type_of% @Erdos878.erdos_878.parts.v := by
  intro h
  rw [h]
  exact Erdos878PartV.part_v
